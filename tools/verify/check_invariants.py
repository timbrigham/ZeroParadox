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


def main():
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
        print('site it points at. This gate is NOT mirrored in CI - CI runs `lake build`')
        print('only, so this is the LAST check before the remote. Measured 2026-08-10:')
        print('no workflow references any checker. Bypassing it ships the change unchecked.')
        return 1
    print('==============================')
    return 0


if __name__ == '__main__':
    sys.exit(main())
