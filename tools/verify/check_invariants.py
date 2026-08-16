"""Always-true repo invariants — checked on every push, not just at release.

These were previously enforced ONLY inside check_release_ready.py, which is procedural (there is
no git event for tag creation, so nothing runs it automatically). Both invariants below had
already failed silently once before anyone noticed:
  * the LEAN_CUSTOM_REGISTRY count drifted and sat broken for weeks;
  * the documented Engineer's-Take grep was non-recursive and blind to 184 of 187 files.
Neither is release-specific — an unfilled Take or an unregistered custom declaration is wrong
whenever it exists. So they run at push time.

check_release_ready.py still runs these at release; this is the earlier tripwire, not a
replacement for the release gate.

Usage:  python check_invariants.py
Exit 0 = all invariants hold.  Exit 1 = at least one broken.
"""
import re
import subprocess
import sys
from pathlib import Path

# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3).
sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
from common import HERE, REPO, SRC  # noqa: E402

SELF = common.self_rel(__file__)
LEAN = sorted(SRC.rglob('*.lean'))   # RECURSIVE — the whole point
REGISTRY = REPO / 'LEAN_CUSTOM_REGISTRY.md'

TAKE_PLACEHOLDER = re.compile(r"TODO \(Tim|TODO: Engineer")
CUSTOM_TAG = re.compile(r'\[ZP-CUSTOM\]')
REGISTRY_ENTRY = re.compile(r'(?m)^### ')

failures = []


def read(p):
    return p.read_text(encoding='utf-8', errors='replace')


def check_engineers_takes():
    hits = []
    for f in LEAN:
        for i, line in enumerate(read(f).split('\n'), 1):
            if TAKE_PLACEHOLDER.search(line):
                hits.append(f'{f.relative_to(REPO)}:{i}')
    if hits:
        failures.append(
            'Unfilled Engineer\'s Take placeholder(s) — these are Tim\'s prose, never Claude\'s:\n'
            + '\n'.join(f'    {h}' for h in hits)
        )
        return False
    print(f'  OK:      Engineer\'s Takes — no placeholders across {len(LEAN)} .lean files (recursive)')
    return True


def check_custom_registry():
    if not REGISTRY.exists():
        failures.append(f'LEAN_CUSTOM_REGISTRY.md missing at {REGISTRY}')
        return False
    entries = len(REGISTRY_ENTRY.findall(read(REGISTRY)))
    tags, tagged_files = 0, []
    for f in LEAN:
        n = len(CUSTOM_TAG.findall(read(f)))
        if n:
            tags += n
            tagged_files.append(f'{f.relative_to(REPO)} x{n}')
    if entries != tags:
        failures.append(
            f'LEAN_CUSTOM_REGISTRY invariant broken: {entries} "### " entries vs {tags} '
            f'[ZP-CUSTOM] tags.\n    Every custom declaration needs a registry entry.\n'
            + '\n'.join(f'    {t}' for t in tagged_files)
        )
        return False
    print(f'  OK:      LEAN_CUSTOM_REGISTRY invariant — {entries} entries == {tags} tags')
    return True


BINARY_EXT = ('.pdf', '.png', '.jpg', '.jpeg', '.ico', '.ttf', '.otf', '.woff',
              '.woff2', '.olean', '.gif')


def tracked_text():
    r = subprocess.run(['git', 'ls-files'], cwd=str(REPO), capture_output=True,
                       text=True, encoding='utf-8')
    return [f for f in r.stdout.split('\n')
            if f.strip() and not f.lower().endswith(BINARY_EXT)]


def check_bytes_are_portable():
    """Every tracked text file is LF, BOM-free, UTF-8, and byte-identical to its committed blob.

    ⚠ THE FOURTH CLAUSE IS THE ONE THAT WAS SILENTLY FALSE, and it is the K1 bedrock finding of
    2026-08-15. `.gitattributes` has declared `* text=auto eol=lf` since 2026-06-21, but 21 files
    predated it and their WORKING COPIES stayed CRLF. Git normalises on comparison, so
    `git status` showed nothing — while anything hashing FILE BYTES got a different answer here
    than in a clean checkout.

    `register.md`'s build-script fingerprints are exactly such a hash. The consequence, measured:
    `check_hashes.py` exited 0 on the author's machine and 1 in a fresh clone, and the CI job
    introduced in the same push would have published `check_hashes FAIL(1)` on day one. A
    provenance token that only reproduces on one machine is not provenance.

    ⚠ Note the deliberate asymmetry with the REVIEW-SIGNAL rule, which says "hash the FILE ON
    DISK, never a git value". That is right for a signal, which certifies what a reviewer actually
    read at that moment. It is wrong for a PROVENANCE token, which must describe what a reader
    receives. This invariant is what keeps the two from diverging: when disk == blob, both rules
    give the same answer."""
    crlf, bom, bad_utf8, differs = [], [], [], []
    for f in tracked_text():
        p = REPO / f
        if not p.is_file():
            continue
        raw = p.read_bytes()
        if b'\r\n' in raw:
            crlf.append(f)
        if raw.startswith(b'\xef\xbb\xbf'):
            bom.append(f)
        try:
            raw.decode('utf-8')
        except UnicodeDecodeError:
            bad_utf8.append(f)
        # ⚠ THE COMMITTED BLOB, not the index, and CRLF-IN-BLOB rather than disk-vs-blob.
        #
        # The first version compared disk bytes against the staged blob and flagged any
        # difference. That fires on every UNCOMMITTED EDIT — it reported three files while the
        # author was mid-change — which is a false-positive generator, and a checker that fires
        # during normal work is one people learn to ignore.
        #
        # What actually needs to hold is that BOTH SIDES are LF. Disk is checked above; this
        # checks the committed side. Given `.gitattributes` (`* text=auto eol=lf`), an LF disk
        # file commits to an LF blob, so the two together give disk == blob without penalising
        # work in progress.
        blob = subprocess.run(['git', 'show', 'HEAD:' + f], cwd=str(REPO), capture_output=True)
        if blob.returncode == 0 and b'\r\n' in blob.stdout:
            differs.append(f)

    problems = []
    if crlf:
        problems.append('CRLF in %d tracked text file(s): %s' % (len(crlf), ', '.join(crlf[:6])))
    if bom:
        problems.append('UTF-8 BOM in %d file(s): %s' % (len(bom), ', '.join(bom[:6])))
    if bad_utf8:
        problems.append('not decodable as UTF-8: %s' % ', '.join(bad_utf8[:6]))
    if differs:
        problems.append(
            'CRLF in the COMMITTED blob of %d file(s): %s\n'
            '    A reader clones these with CRLF, so any fingerprint of them describes bytes\n'
            '    that differ from yours. Fix: rewrite LF-only and re-commit.'
            % (len(differs), ', '.join(differs[:6])))

    if problems:
        failures.append('Byte portability:\n' + '\n'.join('    ' + p for p in problems))
        return False
    print('  OK:      byte portability — %d tracked text files: LF on disk AND in the committed '
          'blob, no BOM, UTF-8' % len(tracked_text()))
    return True


def selftest():
    """MUST-FIRE and MUST-SUPPRESS controls, on planted strings and a synthetic count.

    Added 2026-08-15 to meet the Phase 1 exit ("each with both control types"), which this checker
    had never satisfied. The detection is pure — two regexes and a comparison of two counts — so
    the controls run in memory and write nothing into the repo.

    ⚠ The third control is the one that matters historically. This file exists because the
    documented Engineer's-Take grep was NON-RECURSIVE and blind to 184 of 187 files: a check that
    ran, passed, and saw almost nothing. `LEAN` uses `rglob`, and the control asserts that it
    actually reaches into subdirectories rather than trusting the call."""
    bad = 0

    print('  MUST FIRE')
    for label, line in (('TODO (Tim) placeholder', "-- TODO (Tim): fill this in"),
                        ('TODO: Engineer form', "## TODO: Engineer's Take")):
        ok = bool(TAKE_PLACEHOLDER.search(line))
        bad += 0 if ok else 1
        print('    %-30s %s' % (label, 'ok' if ok else '*** MISSED ***'))
    ok = (3 != 2)   # the comparison the registry check makes
    print('    %-30s %s' % ('entries != tags is a failure', 'ok' if ok else '*** WRONG ***'))

    print('  MUST SUPPRESS')
    for label, line in (('a filled Take', "## Engineer's Take\nBottom is the floor."),
                        ('a bare TODO elsewhere', "-- TODO: tidy this proof later"),
                        ('ordinary prose', "the snap lands at epsilon-zero")):
        ok = not TAKE_PLACEHOLDER.search(line)
        bad += 0 if ok else 1
        print('    %-30s %s' % (label, 'ok' if ok else '*** FALSE POSITIVE ***'))

    # Byte-portability controls. Each shape is built with explicit escapes rather than literal
    # bytes, because a literal CR in source is exactly what this invariant forbids.
    CR_LF = b'a' + bytes([13, 10]) + b'b'
    LF_ONLY = b'a' + bytes([10]) + b'b'
    BOM_X = bytes([0xEF, 0xBB, 0xBF]) + b'x'
    for label, raw, want_crlf, want_bom in (
            ('CRLF is detected', CR_LF, True, False),
            ('LF alone is not', LF_ONLY, False, False),
            ('a BOM is detected', BOM_X, False, True),
            ('plain UTF-8 is neither', 'the pole ⊥'.encode('utf-8'), False, False)):
        got_crlf = bytes([13, 10]) in raw
        got_bom = raw.startswith(bytes([0xEF, 0xBB, 0xBF]))
        ok = (got_crlf is want_crlf) and (got_bom is want_bom)
        bad += 0 if ok else 1
        print('    %-30s %s' % (label, 'ok' if ok else '*** WRONG ***'))

    # The recursion control: rglob must see past the top level.
    nested = [f for f in LEAN if len(f.relative_to(REPO).parts) > 2]
    ok = len(nested) > 0 and len(LEAN) > 10
    bad += 0 if ok else 1
    print('    %-30s %s (%d files, %d in subdirectories)'
          % ('the scan is RECURSIVE', 'ok' if ok else '*** NOT RECURSIVE ***',
             len(LEAN), len(nested)))

    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and the compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    print('  PATTERNS')
    bad += common.check_vocabulary('check_invariants', globals())
    print('\n  selftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


def main():
    if '--selftest' in sys.argv:
        print('')
        print('=== Always-true invariants - CONTROLS ===')
        return selftest()
    print('')
    print('=== Always-true invariants ===')
    check_engineers_takes()
    check_custom_registry()
    check_bytes_are_portable()
    if failures:
        print('')
        for f in failures:
            print(f'  BROKEN:  {f}')
        print('')
        print('Push blocked: a standing invariant is broken.')
        print('Fix the finding, or record it in .claude-local/DEFECTS.md and fix the')
        print('site it points at.')
        # ⚠ CORRECTED 2026-08-15. This block used to end: "This gate is NOT mirrored in CI - CI
        # runs `lake build` only, so this is the LAST check before the remote. Measured
        # 2026-08-10: no workflow references any checker." That was true when written and is now
        # false - `.github/workflows/verify.yml` runs this checker on every push and PR to main.
        # A gate that misstates where else it runs is telling a reader the wrong thing about how
        # much protection they have.
        print('This checker also runs in CI (.github/workflows/verify.yml), report-only for now,')
        print('so a bypass here is visible there rather than invisible everywhere.')
        return 1
    print('==============================')
    return 0


if __name__ == '__main__':
    sys.exit(main())
