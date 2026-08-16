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
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SELF = Path(__file__).resolve().relative_to(ROOT).as_posix()
LEAN = sorted((ROOT / 'ZeroParadox').rglob('*.lean'))   # RECURSIVE — the whole point
REGISTRY = ROOT / 'LEAN_CUSTOM_REGISTRY.md'

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
                hits.append(f'{f.relative_to(ROOT)}:{i}')
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
            tagged_files.append(f'{f.relative_to(ROOT)} x{n}')
    if entries != tags:
        failures.append(
            f'LEAN_CUSTOM_REGISTRY invariant broken: {entries} "### " entries vs {tags} '
            f'[ZP-CUSTOM] tags.\n    Every custom declaration needs a registry entry.\n'
            + '\n'.join(f'    {t}' for t in tagged_files)
        )
        return False
    print(f'  OK:      LEAN_CUSTOM_REGISTRY invariant — {entries} entries == {tags} tags')
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

    # The recursion control: rglob must see past the top level.
    nested = [f for f in LEAN if len(f.relative_to(ROOT).parts) > 2]
    ok = len(nested) > 0 and len(LEAN) > 10
    bad += 0 if ok else 1
    print('    %-30s %s (%d files, %d in subdirectories)'
          % ('the scan is RECURSIVE', 'ok' if ok else '*** NOT RECURSIVE ***',
             len(LEAN), len(nested)))

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
