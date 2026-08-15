# -*- coding: utf-8 -*-
"""gatelock.py — hold a write-lock on the files a review gate is reading.

WHY THIS EXISTS (Tim, 2026-08-01). Reviews are READ-ONLY on the tree, but the CALLER is not.
Twice in one arc the caller wrote "the tree is stable and will not be touched" into a gate brief
and then edited the reviewed files while the gates were still running. Both times a gate reported
the drift; once it invalidated a signal that had been computed against a working tree that then
moved. Discipline demonstrably does not hold here, so this is a lock instead.

HOW IT ENFORCES — and why the first design did not (measured 2026-08-01, judged by file hash).

  v1 relied ONLY on a PreToolUse hook returning {continue:false}. That is a stop-the-agent-loop
  signal, not a deny-this-tool signal. Measured: the hook fired, printed its block, the harness
  reported "stopped continuation" — AND THE EDIT LANDED ON DISK ANYWAY. The Edit tool reported
  "updated successfully". A lock that reports success while the write goes through is worse than
  no lock, because it is trusted.

  v2 (this version) sets the READ-ONLY ATTRIBUTE on each locked path. The Edit tool writes a temp
  file and renames it over the target; Windows refuses that rename, so the tool returns a hard
  error:  EPERM: operation not permitted, rename '...Snap.lean.tmp...' -> '...Snap.lean'
  The block happens at the syscall, so it does not depend on any tool cooperating. Measured on the
  same file that v1 failed on: hash unchanged, no stray temp file, git diff empty.

  The hook (.claude-local/hooks/gate_lock.ps1) is KEPT as a second layer. It cannot prevent a
  write, but the raw EPERM says nothing about gate rounds, and the hook message explains why.

FAIL CLOSED. Every freeze is VERIFIED after it is applied (os.access W_OK). If any path cannot be
frozen, acquire rolls back the ones it already froze and exits non-zero holding no lock. There is
no path through this script that reports a lock it did not actually take — that is the whole bug
v1 had, in both the hook's catch block and the mechanism itself.

WHAT THIS IS NOT, so the blast radius is not guessed at. It sets the FAT-style READ-ONLY ATTRIBUTE
(one bit in the directory entry, via os.chmod), NOT an ACL. `icacls /deny` writes a DACL entry that
inherits and can leave a tree an ordinary user cannot repair; this cannot. Git does not track the
read-only bit either — it is not in the index, cannot be committed, and cannot be pushed. The blast
radius is exactly this working tree.

Known limits, stated rather than discovered later:
  - The read-only attribute is advisory against a DETERMINED process: anything may clear it and
    rewrite. It stops accidental and tool-mediated writes, not deliberate ones. ACL-level deny
    (icacls /deny) survives that and is materially harder to unwind; not used here by decision.
  - GIT IS A HOLE IN THIS LOCK, measured 2026-08-01 in a throwaway repo rather than assumed.
    `git checkout HEAD~1 -- <frozen file>` REWROTE the file and exited 0; so did `git reset
    --hard`. Git unlinks and recreates rather than opening for write, and unlinking a read-only
    file in a writable directory is permitted on Windows. Worse, the recreated file comes back
    WITHOUT the read-only bit, so a git operation silently un-freezes a locked path.
    Consequences, both directions:
      * The lock does NOT stop git from overwriting a file a gate is reading. It stops tool-
        mediated edits (Edit/Write), which is the failure mode it was built for and the one that
        actually occurred twice.
      * `status` already catches the silent thaw — it measures the attribute rather than trusting
        gate.lock, and prints '[WRITABLE] ** NOT ACTUALLY LOCKED **' with exit 1. Check status
        after any git operation during a round.
    An earlier draft of this docstring claimed the opposite (that the freeze BLOCKS checkout/
    merge/pull/rebase and that a merge could fail partway). That was never measured and is false;
    it is deleted rather than annotated, per the correction rule in CLAUDE.md.
  - Because git writes through it, the freeze cannot wedge a merge or leave git unable to operate.
    There is no repair scenario in which a frozen file blocks recovery.
  - `lake build` is unaffected: it writes under `.lake/`, never to locked sources.

RECOVERY does not depend on the lock file. `sweep` enumerates tracked files from git and reports
every one whose read-only bit is set, whether or not gate.lock still exists — so a deleted or
corrupted lock file, or a session that died mid-round, leaves a recoverable state rather than an
invisible one. `sweep --clear` thaws them.

    python gatelock.py sweep [--clear]
    python gatelock.py guard          # hooks call this; exit 1 => refuse

Scope note: only the REVIEWED paths are locked. Gates write their findings notes under
`.claude-local/notes/` and their signals to `.claude-local/*_cleared.txt`; those are never locked,
so a gate is never blocked by this.

Usage:
    python gatelock.py acquire --round 3 <path> [<path> ...]
    python gatelock.py status
    python gatelock.py release
"""
import argparse
import datetime
import io
import json
import os
import stat
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SELF = os.path.relpath(os.path.abspath(__file__), ROOT).replace("\\", "/")
LOCK = os.path.join(ROOT, '.claude-local', 'gate.lock')


def norm(p):
    """Repo-relative, forward slashes, lowercased — the hook normalizes the same way."""
    p = os.path.abspath(os.path.join(ROOT, p)) if not os.path.isabs(p) else os.path.abspath(p)
    try:
        p = os.path.relpath(p, ROOT)
    except ValueError:
        pass
    return p.replace('\\', '/').lower()


def full(rel):
    """Absolute path for a repo-relative locked path."""
    return os.path.join(ROOT, rel.replace('/', os.sep))


def is_frozen(rel):
    """MEASURED, not inferred: is this path actually unwritable right now?"""
    f = full(rel)
    if not os.path.exists(f):
        return None
    return not os.access(f, os.W_OK)


def freeze(rel):
    """Set read-only, then VERIFY it took. Returns True only if the file is now unwritable."""
    f = full(rel)
    os.chmod(f, stat.S_IREAD)
    return is_frozen(rel) is True


def thaw(rel):
    """Clear read-only, then VERIFY it took. Returns True only if the file is now writable."""
    f = full(rel)
    os.chmod(f, stat.S_IWRITE)
    return is_frozen(rel) is False


def tracked_files():
    """Every tracked path, from git. Returns None if git could not be asked — which is NOT the
    same as 'nothing is frozen', and callers must not conflate the two."""
    try:
        out = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT,
                                      stderr=subprocess.PIPE)
    except Exception:
        return None
    return [p.decode('utf-8', 'surrogateescape').replace('\\', '/')
            for p in out.split(b'\0') if p]


def frozen_tracked():
    """Every tracked file whose read-only bit is set, measured directly.

    Deliberately does NOT consult gate.lock: this is the orphan-recovery path, and an orphan is
    precisely the case where the lock file is gone, corrupt, or lying. Returns None if git failed.
    """
    files = tracked_files()
    if files is None:
        return None
    out = []
    for rel in files:
        f = os.path.join(ROOT, rel.replace('/', os.sep))
        if os.path.exists(f) and not os.access(f, os.W_OK):
            out.append(rel)
    return out


def read():
    if not os.path.exists(LOCK):
        return None
    try:
        return json.load(io.open(LOCK, encoding='utf-8'))
    except Exception:
        return None


def cmd_acquire(args):
    if not args.paths:
        print('refusing: acquire needs at least one path')
        return 2
    existing = read()
    if existing:
        print('ALREADY LOCKED (round %s, acquired %s). Release it first.'
              % (existing.get('round'), existing.get('acquired')))
        return 1

    paths = sorted({norm(p) for p in args.paths})

    # Fail closed on a path that does not exist: a lock naming a phantom file is a lock the
    # caller believes covers something it does not.
    missing = [p for p in paths if not os.path.exists(full(p))]
    if missing:
        print('refusing: %d path(s) do not exist — nothing was locked:' % len(missing))
        for p in missing:
            print('   ' + p)
        return 2

    frozen = []
    for p in paths:
        try:
            ok = freeze(p)
        except Exception as e:
            ok = False
            print('   ! %s — %s' % (p, e))
        if not ok:
            print('refusing: could not freeze %s (verified still writable). Rolling back.' % p)
            for q in frozen:
                try:
                    thaw(q)
                except Exception:
                    print('   ! rollback FAILED on %s — clear it by hand' % q)
            return 2
        frozen.append(p)

    data = {
        'round': args.round,
        'acquired': datetime.datetime.now().isoformat(timespec='seconds'),
        'reason': args.reason,
        'paths': paths,
    }
    io.open(LOCK, 'w', encoding='utf-8', newline='\n').write(
        json.dumps(data, indent=2, ensure_ascii=False) + '\n')
    print('LOCKED %d path(s) for gate round %s — read-only VERIFIED on each:' % (len(paths), args.round))
    for p in paths:
        print('   [frozen] ' + p)
    print('\nWrites now fail at the syscall (EPERM on rename), not merely at the hook.')
    print('Release with:  python %s release' % SELF)
    return 0


def cmd_status(_args):
    d = read()
    if not d:
        print('UNLOCKED — no gate review in progress.')
        return 0
    age = ''
    try:
        t = datetime.datetime.fromisoformat(d['acquired'])
        mins = (datetime.datetime.now() - t).total_seconds() / 60.0
        age = '  (%.0f min old)' % mins
        if mins > 90:
            age += '  ** STALE? gates rarely run this long — check for a dead agent **'
    except Exception:
        pass
    print('LOCKED  round %s  acquired %s%s' % (d.get('round'), d.get('acquired'), age))
    if d.get('reason'):
        print('reason: %s' % d['reason'])

    # Report the MEASURED attribute state, never the lock file's say-so. A path listed here but
    # writable means the freeze was cleared behind the lock's back — the lock is not holding.
    drift = 0
    for p in d.get('paths', []):
        st = is_frozen(p)
        if st is True:
            print('   [frozen]  ' + p)
        elif st is None:
            print('   [MISSING] ' + p + '   ** path no longer exists **')
            drift += 1
        else:
            print('   [WRITABLE]' + p + '   ** NOT ACTUALLY LOCKED **')
            drift += 1
    if drift:
        print('\n** %d path(s) are listed in the lock but not frozen. The lock is NOT holding.' % drift)
        print('   Re-acquire, or release and investigate. Do not trust the lock file alone.')
        return 1
    return 0


def cmd_release(_args):
    d = read()
    if not d:
        print('already unlocked.')
        return 0
    failed = []
    for p in d.get('paths', []):
        if not os.path.exists(full(p)):
            print('   [gone]   %s (skipped)' % p)
            continue
        try:
            ok = thaw(p)
        except Exception as e:
            ok = False
            print('   ! %s — %s' % (p, e))
        if ok:
            print('   [thawed] ' + p)
        else:
            failed.append(p)
            print('   [STUCK]  %s  ** still read-only — clear by hand: attrib -R %s **'
                  % (p, p.replace('/', os.sep)))
    os.remove(LOCK)
    print('RELEASED (was round %s, %d path(s)).' % (d.get('round'), len(d.get('paths', []))))
    if failed:
        print('** %d path(s) could not be thawed. They are STILL UNWRITABLE. **' % len(failed))
        return 1
    return 0


def cmd_sweep(args):
    """Orphan recovery. Answers 'is anything frozen right now?' without trusting the lock file."""
    found = frozen_tracked()
    if found is None:
        print('sweep: could not enumerate tracked files (git failed). NOTHING was changed,')
        print('and this is NOT a clean result — the question is unanswered, not answered no.')
        return 2
    if not found:
        print('SWEEP CLEAN — no tracked file is read-only.')
        return 0

    print('%d tracked file(s) are READ-ONLY:' % len(found))
    for p in found:
        print('   ' + p)

    d = read()
    if d:
        print('\ngate.lock IS present (round %s, acquired %s).' % (d.get('round'), d.get('acquired')))
        print('This looks like a LIVE lock, not an orphan. Refusing to clear it here —')
        print('clearing a live lock would silently unfreeze files a gate is still reading.')
        print('Use:  python %s release' % SELF)
        return 1

    print('\nNo gate.lock present — these are ORPHANS (lock file lost, or a session died mid-round).')
    if not args.clear:
        print('Clear them with:  python %s sweep --clear' % SELF)
        return 1

    failed = []
    for p in found:
        try:
            ok = thaw(p)
        except Exception as e:
            ok = False
            print('   ! %s — %s' % (p, e))
        print('   [%s] %s' % ('thawed' if ok else 'STUCK', p))
        if not ok:
            failed.append(p)
    if failed:
        print('\n** %d path(s) could not be thawed. STILL UNWRITABLE. **' % len(failed))
        return 1
    print('\nCleared %d orphan(s).' % len(found))
    return 0


def cmd_guard(_args):
    """Called by the pre-commit (warn) and pre-push (block) hooks.

    Exit 1 means: do not proceed. Two independent reasons, checked separately so the message says
    which one fired — a held lock means a review round is still open, while a frozen file with no
    lock means an orphan left by a lost lock file or a dead session.
    """
    d = read()
    found = frozen_tracked()

    if found is None:
        print('gate lock guard: could not enumerate tracked files (git failed).')
        print('Treating as UNKNOWN, not clear.')
        return 1

    if not d and not found:
        print('gate lock: clear (no lock held, no tracked file frozen).')
        return 0

    print('')
    print('=== GATE LOCK GUARD ===')
    if d:
        print('A gate lock is HELD — round %s, acquired %s, %d path(s).'
              % (d.get('round'), d.get('acquired'), len(d.get('paths', []))))
        if d.get('reason'):
            print('reason: %s' % d['reason'])
        print('A review round is still open. Wait for every gate to return, then:')
        print('    python %s release' % SELF)
    if found:
        print('%d tracked file(s) are still READ-ONLY (left frozen by an unreleased lock):' % len(found))
        for p in found[:20]:
            print('   ' + p)
        if len(found) > 20:
            print('   ... and %d more' % (len(found) - 20))
        if not d:
            print('No lock file is present, so these are ORPHANS. Clear them with:')
            print('    python %s sweep --clear' % SELF)
    print('')
    return 1


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest='cmd')
    a = sub.add_parser('acquire'); a.add_argument('paths', nargs='*')
    a.add_argument('--round', default='?'); a.add_argument('--reason', default='')
    sub.add_parser('status')
    sub.add_parser('release')
    s = sub.add_parser('sweep'); s.add_argument('--clear', action='store_true')
    sub.add_parser('guard')
    args = ap.parse_args()
    fn = {'acquire': cmd_acquire, 'status': cmd_status, 'release': cmd_release,
          'sweep': cmd_sweep, 'guard': cmd_guard}.get(args.cmd)
    if not fn:
        ap.print_help()
        return 2
    return fn(args)


if __name__ == '__main__':
    sys.exit(main())
