"""The one definition of everything more than one checker needs.

**WHY THIS FILE EXISTS — `DEFECTS.md` MIG-3, and it is this bundle's own argument turned on
itself.** The migration that created `tools/verify/` retired three FILE-level mirrors and **two of
the three had silently drifted**: `scan_pdfs.py` by three months, and 4 of 8 gate briefs. The
standing rule that came out of it is *"if something must exist in two places, that is the signal to
change the layout — NOT to add a copy step and a rule asking someone to remember it."*

Then the bundle built to enforce that rule accumulated **constant-level mirrors inside itself** — the
path preamble, `selftest`, `load_baseline`, `SKIP_DIRS`/`SKIP_NAMES`, `targets` and the stdout guard
each copied across many modules (surveyed 2026-08-16; the tally is in `DEFECTS.md` MIG-3 and is a
measurement of a state this file removes, so it is not restated here). Same defect, one level down.

**⚠ EVERY DIVERGENCE FOUND WAS LATENT, AND THAT IS THE POINT — MEASURED, NOT ASSUMED.**
Each was verified inert against the real tree before unifying, so this file changes no behaviour:

* **`SKIP_DIRS`** — `check_modal` carried 8 entries, `check_negatives` 10, `check_figures` 11. The
  three extra names (`__pycache__`, `deepseek`, `fonts`) cannot match anything the globs produce:
  `__pycache__` holds `.pyc`, `deepseek` lives under the gitignored private folder the globs never
  reach, `fonts` holds `.ttf`. Diffing the three scan sets returns **exactly the self-skip each way**.
* **`load_baseline`** — four genuinely different readings (utf-8 vs utf-8-sig; the `#` test applied
  to the raw line vs the stripped one; `check_pov`'s tab-field-0 split). Run over all eight real
  baseline files, **all four produce identical key sets**. The unified reading below is the superset
  of all four, so it can only ever skip a comment the old ones kept.
* **the stdout guard** — some copies passed `line_buffering=True`, some did not. `report.py:34`
  records what the missing flag costs: Python block-buffers while child processes write straight to
  the terminal fd, so the manifest prints *after* what it announced and section headers land under
  the wrong section.

**⚠ WHAT THIS FILE DELIBERATELY DOES NOT OWN.** `check_poles` walks the whole repo over three
extensions with a directory-NAME skip set and an anchored `SKIP_RELDIRS`; the `targets()` family
globs three patterns plus tracked markdown with a path-SUBSTRING skip. Those are two different
questions that happen to share a variable name. **Folding them together would be a silent scope
change in every checker at once** — the one failure mode MIG-3's control exists to catch. `SKIP_DIRS`
here is the `targets()` family's only.

**⚠ AND THIS MODULE IMPORTS NOTHING LOCAL, BY CONSTRUCTION.** It sits at layer 0 beside
`vendored.py` and `report.py`, so every other module can import it and no cycle is reachable.
Verified over the whole bundle by AST before this file was written: the local import graph is a DAG,
and the one edge that made a checker a library — `check_figures`/`check_negatives` importing
`check_modal` for `tracked_md`, `normalize_separators` and `strip_module_docstring` — is what moving
those three functions here removes. **Do not add a local import to this file.**
"""
import io
import os
import re
import subprocess
import sys
from pathlib import Path

# --------------------------------------------------------------------------- roots
#
# ⚠ THE ONE DERIVATION. Every other module coerces these; none re-computes them. `SELF` is derived
# from `__file__` per module rather than written down, because a hardcoded `python <dir>/tool.py` in
# a docstring is a COPY of the path and drifts exactly like a mirrored file.
#
# ⚠ ONE NAME FOR ONE DIRECTORY. The repo root was spelled `REPO` in some modules and `ROOT` in
# others — the same directory under two names, in one bundle (surveyed 2026-08-16). `REPO` won on
# count; `ROOT` is gone, and a stale reference now fails loud instead of resolving to something
# plausible.
HERE = Path(__file__).resolve().parent           # this bundle: tools/verify
REPO = HERE.parent.parent                        # the repository root
PRIV = REPO / '.claude-local'                    # private state; ABSENT in a public clone
SRC = REPO / 'ZeroParadox'                       # the Lean corpus


def self_rel(file):
    """This module's repo-relative path, for a checker to name itself in its own output.

    Never hardcode the answer — see the header. `os.path.relpath` rather than
    `Path.relative_to` so a checker invoked through a symlinked path still resolves."""
    return os.path.relpath(os.path.abspath(file), str(REPO)).replace('\\', '/')


def utf8_stdout():
    """UTF-8 + line buffering on stdout. Call it at every entry point.

    Two separate failures, both measured, both of which shipped looking correct:

    **Encoding.** The corpus is full of `⊥ ∞ ℤ₂`; the Windows console defaults to cp1252 and
    *raises* on them. `check_prose.py:44` records the shape — the crash is indistinguishable from a
    real violation and blocks a clean commit, or lands mid-run and truncates the findings list into
    something that reads like a completed pass.

    **Buffering.** `report.py:34`: Python block-buffers its own stdout while child processes write
    straight to the terminal fd, so a manifest printed before its children arrives after them and
    section headers land under the wrong section. `line_buffering=True` is not cosmetic, and two of
    the eight copies of this guard omitted it."""
    try:
        sys.stdout.reconfigure(encoding='utf-8', line_buffering=True)
    except Exception:
        pass


# --------------------------------------------------------------------------- scan scope
#
# ⚠ THIS IS THE `targets()` FAMILY'S SCOPE AND NOTHING ELSE'S. See the header: `check_poles` asks a
# different question with a different walk, and its same-named constant stays where it is.
#
# The three extra names below (`__pycache__`, `deepseek`, `fonts`) were present in some copies and
# not others. They are kept because they are correct as *intent* and cost nothing as *filter* — the
# globs cannot produce a `.pyc`, cannot reach the gitignored private folder, and cannot yield a
# `.ttf`. Keeping the union rather than the intersection is the conservative direction: it can only
# narrow scope for file kinds that are already impossible.
SKIP_DIRS = ('.lake', '.git', 'notes', 'papers', 'archive', 'feedback', 'outreach',
             'autobiography', '__pycache__', 'deepseek', 'fonts')

# Files no checker in this family should scan, whatever it is looking for. A checker additionally
# skips ITSELF and its OWN baseline — those two are per-checker and passed in, not listed here,
# because a shared list of every checker's name would exempt all of them from all of each other.
SKIP_NAMES = frozenset({'CLAUDE.md', 'register.md', 'RELEASES.md'})

# The glob patterns. `.claude-local/build_*.py` was a fourth until the build scripts stopped being
# mirrored: `scripts/` is now their only home, so the third pattern already covers them and a fourth
# would have been a second copy of the same coverage claim.
GLOBS = ('ZeroParadox/**/*.lean', 'scripts/*.py', 'tools/**/*.py')

# The reviewed scan scope, pinned. `selftest()` asserts the live set is a SUPERSET of it, so any
# narrowing of GLOBS, SKIP_DIRS, SKIP_NAMES or a per-checker skip fires — see SCOPE-1 there.
#
# ⚠⚠ **SECTIONED, BECAUSE PINNING `targets()` ALONE PINNED THREE CHECKERS OUT OF SEVEN** (SCOPE-3,
# `/rely` round 3). Only `check_modal`, `check_negatives` and `check_figures` use the shared
# enumerator. `check_pov`, `check_prose`, `check_classes` and `check_poles` each walk the tree
# privately — `check_pov`'s source says so deliberately, and the others predate `common.py`. So the
# output pin was correct and **not connected to four of the gating checkers**: narrowing any private
# enumerator took a planted violation from detected to undetected with the whole suite green, and
# `common.py --selftest` kept reporting the shared scan set intact, correctly, because it was.
#
# ⚠ The one thing that noticed was `guards.py` — reporting *itself* `DETECTOR BROKEN`, and the
# narrowing silenced that too. **Fixing the shared thing and leaving the private ones is the same
# one-route-not-the-property error, one level out.**
SCOPE_BASELINE = HERE / 'scope_baseline.txt'


def load_scope(section):
    """The recorded scan set for one enumerator. Sections are `[name]` headed."""
    if not SCOPE_BASELINE.exists():
        return set()
    out, cur = set(), None
    for line in io.open(str(SCOPE_BASELINE), encoding='utf-8-sig').read().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        if line.startswith('[') and line.endswith(']'):
            cur = line[1:-1]
            continue
        if cur == section:
            out.add(line)
    return out


PATTERN_BASELINE = HERE / 'pattern_baseline.txt'


def load_pinned(path, section):
    """Sectioned `[name]` reader, shared by the scope and pattern pins."""
    if not path.exists():
        return set()
    out, cur = set(), None
    for line in io.open(str(path), encoding='utf-8-sig').read().split('\n'):
        s = line.strip()
        if not s or s.startswith('#'):
            continue
        if s.startswith('[') and s.endswith(']'):
            cur = s[1:-1]
            continue
        if cur == section:
            # ⚠ THE RECORDED VALUE IS NOT STRIPPED, and stripping it was a fidelity bug the pin
            # caught in itself on its first full run. `check_invariants.REGISTRY_ENTRY` is
            # `(?m)^### ` — **with a trailing space** — so a `.strip()` here stored something the
            # live pattern could never equal, and the checker reported its own regex as REMOVED.
            # A pin that mangles the value it stores cannot detect a change to it. Blank and
            # comment lines are still recognised from the stripped form; only the VALUE is verbatim.
            out.add(line)
    return out


# Names that are NOT detection vocabulary: accumulators, scan scope (pinned separately by
# `scope_baseline.txt`), rosters, and the controls themselves.
#
# ⚠⚠ **QUALIFIED `module.NAME`, NEVER BARE — A BARE DENYLIST IS KEYED BY A NAME COLLISION** (`PAT-2`,
# `/rely` round 4). `SKIP_NAMES` means *files not to scan* in the `targets()` family, where it is
# correctly excluded because `scope_baseline.txt` pins it. In `check_classes` the identical name
# means *declarations exempt from the degeneracy gauge* — detection surface, and it was silently
# exempted from pinning by the other module's entry. Adding one line to it took that checker from
# exit 1 to exit 0 with every gate green. **One correct exemption granting an unrelated one is the
# self-exemption shape this bundle exists to close, arriving through a namespace.**
# ⚠⚠ **EVERY ENTRY CARRIES ITS REASON, AND THE REASON IS CHECKED** (`SKIP-3`, `/rely` round 5). This
# was a flat set under one blanket comment — *"scan scope, pinned by `scope_baseline.txt` instead"* —
# and that claim was **FALSE FOR THREE OF TWELVE ROWS**. `check_modal`, `check_negatives` and
# `check_figures` have no `scope_baseline.txt` section: they feed their own `SKIP_NAMES` into the
# SHARED walk, so `[common.targets]` pins that walk under the DEFAULT skips, not each checker's
# effective scan set. Measured per checker with its own `MUST_FIRE[0]` planted live on disk — adding
# one filename to any of the three took it from exit 1 to exit 0 with the violation still present
# and both pins, all selftests, `guards --block` and `check_checkers --block` reporting green. One
# further row was simply **DEAD**: `check_moved.SKIP_DIRS` named an attribute that does not exist,
# drifted in the same edit meant to harden this list.
#
# **A blanket justification over a list nobody re-checks is the shape this bundle exists to close.**
# So: `module.NAME -> (reason, detail)`, and `selftest()` asserts every row is LIVE (the attribute
# exists) and COVERED (its stated reason actually holds). That is `guards.py` doctrine — the
# registry is the deliverable — applied to the one exemption registry here that had no
# registry-level check.
_SCOPE, _ROSTER, _CONTROL, _DERIVED, _COMPUTED = 'scope', 'roster', 'control', 'derived', 'computed'

_NOT_VOCAB_REASONS = {
    # scan scope — genuinely pinned by the named `scope_baseline.txt` section
    'common.SKIP_DIRS': (_SCOPE, 'common.targets'),
    'common.SKIP_NAMES': (_SCOPE, 'common.targets'),
    'common.GLOBS': (_SCOPE, 'common.targets'),
    'check_poles.SKIP_DIRS': (_SCOPE, 'check_poles'),
    'check_poles.SKIP_RELDIRS': (_SCOPE, 'check_poles'),
    'check_poles.SCAN_EXT': (_SCOPE, 'check_poles'),
    'check_moved.SCAN_EXT': (_SCOPE, 'check_moved'),
    'check_invariants.BINARY_EXT': (_SCOPE, 'check_invariants'),
    # ⚠ `check_modal.SKIP_NAMES`, `check_negatives.SKIP_NAMES` and `check_figures.SKIP_NAMES` are
    # DELIBERATELY ABSENT — they were here, the claim did not hold, and they are now pinned as
    # ordinary vocabulary. Each is a set of two strings; pinning costs nothing and closes SKIP-3.
    # `check_moved.SKIP_DIRS` is absent because it never existed.

    # rosters — reconciled by `check_checkers.roster_agrees()` instead
    'check_checkers.CALLERS': (_ROSTER, None),
    'check_checkers.ALSO_AUDITED': (_ROSTER, None),
    'ci_report.SELFTESTS': (_ROSTER, None),
    'batch.CHECKERS': (_ROSTER, None),
    'batch.GATING_CHECKERS': (_ROSTER, None),

    # the controls themselves: pinning them would pin the test, not the thing tested
    'check_modal.MUST_FIRE': (_CONTROL, None), 'check_modal.MUST_SUPPRESS': (_CONTROL, None),
    'check_negatives.MUST_FIRE': (_CONTROL, None),
    'check_negatives.MUST_SUPPRESS': (_CONTROL, None),
    'check_figures.MUST_FIRE': (_CONTROL, None), 'check_figures.MUST_SUPPRESS': (_CONTROL, None),
    'check_pov.MUST_FIRE': (_CONTROL, None), 'check_pov.MUST_SUPPRESS': (_CONTROL, None),
    'check_pov.MUST_DENY': (_CONTROL, None),
    'check_classes.MUST_FIRE': (_CONTROL, None), 'check_classes.MUST_SUPPRESS': (_CONTROL, None),
    'check_poles.MUST_FIRE': (_CONTROL, None), 'check_poles.MUST_SUPPRESS': (_CONTROL, None),
    'vendored.MUST_FIRE': (_CONTROL, None), 'vendored.MUST_SUPPRESS': (_CONTROL, None),
    'guards.TOUCHED': (_CONTROL, None), 'guards.PROPERTIES': (_CONTROL, None),

    # derived from a pinned source, so pinning it twice adds nothing
    'check_moved.RULES': (_DERIVED, 'check_moved.MOVED'),

    # ⚠ COMPUTED STATE, NOT AN AUTHORED KNOB — the whole rule for scalars. `MATHLIB_PRESENT` is True
    # where `.lake/packages/` exists and False in a worktree, in CI, and in any fresh clone. Pinning
    # it made `check_paths --selftest` fail everywhere Mathlib is absent: a control that only passes
    # on the author's machine, which is the `check_hashes` failure already on record here. Caught by
    # running the PAT-2 control in a worktree rather than in place.
    # **Pin what someone TUNES; never pin what the environment answers.**
    'check_paths.MATHLIB_PRESENT': (_COMPUTED, None),
}
_NOT_VOCAB = frozenset(_NOT_VOCAB_REASONS)


def vocabulary(mod_globals, module=None):
    """Every detection pattern a module advertises, as `NAME<TAB>value` lines.

    ⚠ **DISCOVERED AT RUNTIME BY TYPE, NOT LISTED.** A hand-maintained roster of which constants
    matter is the `DEB-2` hazard, and this suite has already paid for it three times. Anything that
    IS a compiled regex, a threshold, or a collection of strings not explicitly denylisted is
    vocabulary — so a knob added tomorrow is pinned the day it is written.

    ⚠⚠ **`int` IS COLLECTED, AND LEAVING IT OUT WAS A BEDROCK HOLE** (`PAT-2`). A detector is tuned
    by NUMBERS as much as by phrases: `check_modal.SENTENCE` is the window in which *weak* evidence
    counts, so ENLARGING it monotonically suppresses hits. Measured on the real corpus with no file
    edited at all — `SENTENCE` 260 → 10000 takes `check_modal.scan()` from three sites to **zero**,
    with `--selftest` PASS, both pins `ok`, and `check_checkers --block` exit 0. That is the
    "addition silently clears more hits" direction this module's own header names as the danger,
    with the knob for it outside the pin. ⚠ And it has an INNOCENT PATH — *"widen the window, we keep
    getting false positives on wrapped prose"* is a plausible well-meaning edit that zeroes a gate.

    ⚠ **PINNED EXACTLY, IN BOTH DIRECTIONS.** For a DETECTION pattern removal is the danger; for an
    EVIDENCE or suppression pattern, or a window, it is ADDITION. A superset test is right for a list
    of things to catch and wrong for a list of excuses."""
    out = set()
    for name, val in sorted(mod_globals.items()):
        if name.lstrip('_').upper() != name.lstrip('_'):
            continue                                        # not a CONSTANT-cased name
        if '%s.%s' % (module, name) in _NOT_VOCAB:
            continue
        if isinstance(val, re.Pattern):
            out.add('%s\t%s' % (name, val.pattern))
        elif isinstance(val, bool):
            out.add('%s\t%r' % (name, val))                 # before int: bool IS an int in Python
        elif isinstance(val, int):
            out.add('%s\t%d' % (name, val))
        elif isinstance(val, (list, tuple, set, frozenset)) and val:
            for item in val:
                if isinstance(item, str):
                    out.add('%s\t%s' % (name, item))
                elif isinstance(item, (tuple, list)) and all(isinstance(x, str) for x in item):
                    # ⚠ `check_moved.MOVED` is a list of (pattern, destination) PAIRS — its own
                    # docstring calls the table "this checker's whole content", and it was invisible
                    # twice over: denylisted AND tuple-shaped. Deleting one entry took
                    # `relocations tracked` from 74 to 73 with the pin still reporting ok.
                    out.add('%s\t%s' % (name, '\t'.join(item)))
    return out


def check_exemption_registry():
    """Every `_NOT_VOCAB` row must be LIVE and its stated reason must actually HOLD.

    ⚠ **THIS IS THE PART THAT TERMINATES THE REGRESS** (`SKIP-3`). Removing three wrong rows fixes
    three rows; checking the registry fixes the class. A blanket justification over a list nobody
    re-checks is how `SKIP-3` happened — twelve entries under one comment, three of them false and
    one naming an attribute that had ceased to exist.

    Two assertions per row:
      * **LIVE** — the module has that attribute. A dead row is a rule about nothing, and it drifts
        silently because nothing dereferences it.
      * **COVERED** — a `scope` row names a `scope_baseline.txt` section that exists and is
        populated. The other reasons (`roster`, `control`, `derived`, `computed`) are structural
        claims checked elsewhere or by construction, and are recorded so the reason is at least
        legible rather than blanket.

    Returns the failure count."""
    import importlib
    bad = 0
    print('EXEMPTION REGISTRY (every _NOT_VOCAB row live and covered)')
    dead, uncovered = [], []
    for key, (reason, detail) in sorted(_NOT_VOCAB_REASONS.items()):
        mod_name, attr = key.rsplit('.', 1)
        try:
            mod = importlib.import_module(mod_name)
        except Exception:
            dead.append('%s (module will not import)' % key)
            continue
        if not hasattr(mod, attr):
            dead.append(key)
            continue
        if reason == _SCOPE and not load_pinned(SCOPE_BASELINE, detail):
            uncovered.append('%s -> [%s] absent or empty' % (key, detail))
    for label, rows in (('every row names a live attribute', dead),
                        ('every scope row is really scope-pinned', uncovered)):
        ok = not rows
        print('  %-40s %s' % (label, 'ok (%d rows)' % len(_NOT_VOCAB_REASONS) if ok
                              else '*** %d BAD: %s ***' % (len(rows), '; '.join(rows[:3]))))
        bad += 0 if ok else 1
    return bad


def render_pattern_delta(dropped, added, width=38):
    """The CHANGED line for a pattern edit, windowed on the first character that differs.

    ⚠ RENDER FROM THE FIRST DIFFERENCE, NOT FROM OFFSET 0 (`RLY16-8`, /rely). Both sides used to be
    truncated at `[:38]` from the start, so editing a pattern whose first 38 characters are constant
    — the common case, since a pattern's NAME and the opening of its regex rarely move — printed two
    BYTE-IDENTICAL strings either side of the arrow. The gate fired correctly and said nothing a
    reader could act on, which leaves re-pinning blind as the only available response: a message
    that cannot distinguish the two versions turns a precise control into a rubber stamp.

    Extracted from `check_vocabulary` so it can be controlled at all. It printed inline before, so
    the only way to test the rendering was to read it.
    """
    a, b = dropped[0], added[0]
    i = next((n for n, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    start = max(0, i - 8)
    lead = '' if start == 0 else '…'
    # ⚠⚠ THE NAME IS PRINTED SEPARATELY, AND THE FIRST FIX DROPPED IT — creating the mirror of the
    # defect it closed. Windowing on the first difference moves the window PAST the `NAME\t` prefix
    # whenever only the regex changed, so on this very commit's `_ARROW_MOVE` edit the message
    # contained no `_ARROW_MOVE` at all: with 92 pinned patterns, legible-but-anonymous is no more
    # actionable than identical-but-named. Entries are `NAME\tPATTERN`, so the name is recoverable.
    _name = a.split('\t', 1)[0]
    _also = b.split('\t', 1)[0]
    _label = _name if _name == _also else '%s -> %s' % (_name, _also)
    return ('*** %d CHANGED [%s]: %s%s -> %s%s *** (an edit is one removal and one addition)'
            % (max(len(dropped), len(added)), _label,
               lead, a[start:start + width], lead, b[start:start + width]))


def check_vocabulary(section, mod_globals, label=None):
    """Pin every detection pattern a module advertises. See `vocabulary`.

    ⚠⚠ **SCOPE ANSWERS "DID IT LOOK AT EVERYTHING". THIS ANSWERS "WOULD IT RECOGNISE ANYTHING",
    AND ONLY THE FIRST WAS GUARDED** (`PAT-1`, 2026-08-16). Measured by mutation - replacing each
    advertised pattern with a string that cannot match, one at a time, and re-running that checker's
    own `--selftest`: **30 of 34 patterns were SILENT**. Delete `artifact` from `check_modal`'s
    phrase list and it stops catching the defect class it was built for, with `--selftest` green,
    `--block` exit 0, and `check_checkers` reporting all four properties satisfied. A must-fire
    control only ever proves the patterns it happens to exercise.

    ⚠ **THE CONTROLS CANNOT BE GENERATED FROM THE PATTERN LIST — that is the trap.** A control
    derived from the live list disappears with the pattern it was meant to guard, so deletion stays
    silent and the design defeats itself. The pin has to be an INDEPENDENT record, which is what
    `pattern_baseline.txt` is.

    ⚠ **EXACT, NOT SUPERSET, AND A DEAD FUNCTION USED TO SAY OTHERWISE.** `check_patterns()` carried
    this argument with the closing bargain *"adding a pattern is free and only a REMOVAL fires"* -
    which is the scope pin's bargain, not this one. It had no callers, and the live behaviour is the
    opposite: an unrecorded ADDITION fires too, exit 1, so strengthening a detector must be recorded
    rather than merely permitted. Deleted 2026-08-18 (`/rely`); the argument kept, the false
    semantics dropped."""
    live = vocabulary(mod_globals, section)
    recorded = load_pinned(PATTERN_BASELINE, section)
    dropped = sorted(recorded - live)
    added = sorted(live - recorded)
    bad = 0
    ok = not dropped and not added
    # ⚠ BOTH SIDES ARE REPORTED, AND THE FIRST VERSION DESCRIBED THE WRONG EVENT (`PIN-MSG`,
    # `/rely` round 4). It printed `dropped` first, so EDITING a pattern — which is one removal and
    # one addition — was announced as `1 REMOVED` showing the OLD value. It fired correctly and
    # named the wrong thing, which for a gate is its own defect: the reader is sent to look for a
    # deletion that did not happen.
    detail = 'ok (%d patterns)' % len(live)
    if dropped and added:
        detail = render_pattern_delta(dropped, added)
    elif dropped:
        detail = '*** %d REMOVED: %s ***' % (len(dropped), '; '.join(d[:44] for d in dropped[:2]))
    elif added:
        detail = ('*** %d ADDED and unrecorded: %s *** (strengthening is fine — record it)'
                  % (len(added), '; '.join(a[:44] for a in added[:2])))
    print('  %-40s %s' % ('%s: vocabulary unchanged' % (label or section), detail))
    bad += 0 if ok else 1
    # ⚠ THE VACUITY GUARD IS ON `live`, NOT ON `recorded`, and the difference is the whole point.
    # Under EXACT match an empty section already fires — as "N ADDED and unrecorded" — so a
    # threshold on the recorded side is redundant AND wrong: it failed `check_figures`, which
    # legitimately advertises two regexes. What cannot be caught that way is a module whose
    # vocabulary went to ZERO, because then recorded and live agree at nothing. That is the real
    # vacuous state and it is what this asserts.
    alive = len(live) > 0
    print('  %-40s %s' % ('%s: the module still has vocabulary' % (label or section),
                          'ok' if alive else '*** NO PATTERNS AT ALL — check is vacuous ***'))
    bad += 0 if alive else 1
    return bad


def check_scope(section, live, label=None):
    """Print and score one enumerator's scope pin. Returns the number of failures (0, 1 or 2).

    SUPERSET, so adding files never fires; only a NARROWING does. The vacuity guard is not
    decoration — an absent section makes the superset test trivially true, which is the
    `decl_baseline.txt` failure mode `batch.py` records, where "added declarations" computed against
    nothing returned nothing and both purity and SSOT passed blind.

    ⚠ **A RECORDED PATH THAT NO LONGER EXISTS IS NOT A NARROWING — it is a different tree**, and
    filtering by existence is what makes this pin survive a clone. The first version compared against
    the raw recorded set and failed in a fresh worktree, because the baseline had been generated in a
    working tree that carried untracked files. A control that only passes on the author's machine is
    the `check_hashes` failure this project already has on record: exit 0 here, exit 1 in a clean
    checkout. Caught by running the control in a worktree rather than trusting it in place.

    What the check therefore asserts is the property that matters: **every file that EXISTS and was
    in scope is still in scope.**"""
    recorded = load_scope(section)
    present = {r for r in recorded if (REPO / r).exists()}
    dropped = sorted(present - set(live))
    bad = 0
    ok = not dropped
    print('  %-40s %s'
          % ('%s: no recorded path dropped' % (label or section),
             'ok (%d recorded, %d present, %d live)'
             % (len(recorded), len(present), len(list(live))) if ok
             else '*** %d DROPPED: %s ***' % (len(dropped), ', '.join(dropped[:4]))))
    bad += 0 if ok else 1
    # ⚠ Vacuity is measured on what is PRESENT, not on what is recorded: a section full of paths
    # that no longer exist would pass the superset test trivially while pinning nothing.
    populated = len(present) > 20
    print('  %-40s %s' % ('%s: the pin is populated' % (label or section),
                          'ok' if populated else '*** EMPTY SECTION — check is vacuous ***'))
    bad += 0 if populated else 1
    return bad


def tracked_md():
    """Every TRACKED `.md`, at any depth. **The single definition — import it, never re-glob.**

    ⚠ `REPO.glob('*.md')` is ROOT-ONLY, and this class had THREE members: `check_modal`,
    `check_negatives`, `check_figures`. A round-3 fix closed two and left the third — the
    fix-the-site-not-the-class defect this project names, committed while fixing an instance of it.
    18 tracked markdown files were unscanned, including all 11 published gate briefs.

    `git ls-files` is what `check_paths` already used. Tracked-only is the load-bearing half: the
    gitignored private folder stays out **by construction** rather than by remembering SKIP_DIRS."""
    out = subprocess.run(['git', 'ls-files', '*.md'], cwd=str(REPO),
                         capture_output=True, text=True, check=True).stdout.split()
    return [REPO / rel for rel in out]


# ═══ SUBJECT IDENTITY FOR THE LEDGER ══════════════════════════════════════════════════════════
#
# ⚠⚠ A SUBJECT IS IDENTIFIED BY ITS GIT BLOB ID, NOT BY A CONTENT HASH (`gitRobot.md` §12-0-quater).
# The blob id is the identifier git already maintains, so `inventory(ref)` answers "does this commit
# have the keys" with a tree walk instead of reading and hashing every subject — which is the whole
# point of moving the cross-check server-side (§12-0-alpha).
#
# ⚠ IT IS NOT `sha1(file_bytes)`. A blob id is `sha1("blob " + bytelength + "\0" + content)`; no
# standard hash tool produces one, which is exactly why it is read from git rather than computed.
#
# ⚠⚠ AND IT NAMES THE STAGED OBJECT, NOT WHAT A CHECKER READ OFF DISK. That is the trap: a checker
# scanning the working tree while recording a blob id would attest to bytes nobody examined. Until
# the checkers read from the index, `unstaged_modified()` below is the fence — a file whose worktree
# differs from its index is EXCLUDED from the record rather than recorded on the wrong bytes.


INDEX = 'INDEX'   # the staged content — see `ledger_subjects`


def index_blobs():
    """`{path: blob id}` from the INDEX. One git call, whatever the subject count."""
    out = subprocess.run(['git', 'ls-files', '-s'], cwd=str(REPO), capture_output=True,
                         text=True, encoding='utf-8', errors='replace').stdout
    blobs = {}
    for line in out.splitlines():
        meta, _, path = line.partition('\t')          # `<mode> <blob> <stage>\t<path>`
        bits = meta.split()
        if path and len(bits) >= 2 and len(bits[1]) == 40:
            blobs[path.strip().replace('\\', '/')] = bits[1]
    return blobs


def worktree_modified():
    """Paths whose WORKING TREE differs from the index — not safe to record against a staged blob."""
    out = subprocess.run(['git', 'ls-files', '-m'], cwd=str(REPO), capture_output=True,
                         text=True, encoding='utf-8', errors='replace').stdout
    return {p.strip().replace('\\', '/') for p in out.splitlines() if p.strip()}


def ref_blobs(ref='HEAD'):
    """`{repo-relative path: blob id}` at `ref`. ONE git call, whatever the subject count.

    ⚠ This is the cheap half of the design. `inventory(ref)` answers "does this commit have the
    keys" from a tree the caller already has, instead of reading and hashing every subject."""
    out = subprocess.run(['git', 'ls-tree', '-r', ref], cwd=str(REPO), capture_output=True,
                         text=True, encoding='utf-8', errors='replace').stdout
    blobs = {}
    for line in out.splitlines():
        # `<mode> blob <id>\t<path>`
        meta, _, path = line.partition('\t')
        bits = meta.split()
        if path and len(bits) >= 3 and bits[1] == 'blob':
            blobs[path.strip().replace('\\', '/')] = bits[2]
    return blobs


def differs_from(ref='HEAD'):
    """Paths whose worktree OR index differs from `ref` — never safe to record against its blobs."""
    out = subprocess.run(['git', 'diff', '--name-only', 'HEAD'], cwd=str(REPO),
                         capture_output=True, text=True, encoding='utf-8',
                         errors='replace').stdout if ref == 'HEAD' else ''
    return {p.strip().replace('\\', '/') for p in out.splitlines() if p.strip()}


def ledger_basis(ref='HEAD'):
    """The `basis` block for a record: a resolved ref, never a symbolic name.

    ⚠ `kind` is one of ('range', 'ref', 'scope', 'tree') — the ledger rejects anything else, which
    is how `'index'` was caught on the first wiring attempt.

    ⚠ INDEX MODE RESOLVES TO THE TREE THE COMMIT WILL CARRY. `write-tree` turns the index into a
    real tree object, which is exactly what the pending commit will point at — so the basis names
    the content being committed rather than the parent it is being committed onto. It writes an
    object and changes no ref, so it is safe to run before a commit."""
    if ref == INDEX:
        tree = subprocess.run(['git', 'write-tree'], cwd=str(REPO), capture_output=True,
                              text=True, encoding='utf-8', errors='replace').stdout.strip()
        # `resolved_from` is V1's enum ('explicit' | 'upstream' | 'FALLBACK'), not free text — it
        # records HOW the basis was determined, and this one was asked for by name.
        return {'kind': 'tree', 'resolved_from': 'explicit', 'value': tree}
    sha = subprocess.run(['git', 'rev-parse', ref], cwd=str(REPO), capture_output=True,
                         text=True, encoding='utf-8', errors='replace').stdout.strip()
    return {'kind': 'ref', 'resolved_from': 'explicit', 'value': sha}


def ledger_subjects(rels, ref='HEAD'):
    """`([{path, blob}], skipped)` — subjects safe to record, and the paths deliberately left out.

    ⚠⚠ FAIL CLOSED, AND REPORT THE SKIPS. A path absent from `ref`, or differing from it in the
    worktree or the index, is DROPPED rather than recorded — because recording it would attest to
    bytes the checker did not read, which is the one thing this identity scheme exists to prevent
    (`gitRobot.md` §12-0-quater). The caller MUST print what was dropped: a record covering fewer
    subjects than the checker examined is a coverage gap, and a silent one is the defect this whole
    layer exists to end."""
    rels = [r.replace('\\', '/') for r in rels]
    # ⚠⚠ INDEX MODE IS WHAT MAKES PRE-COMMIT RECORDING POSSIBLE, and the reason is not obvious.
    # At pre-commit time HEAD is the PARENT — the commit being made does not exist yet — so a record
    # keyed to HEAD would cover the wrong content entirely. But the staged blobs ARE the new
    # commit's blobs, and coverage is content-addressed, so recording the INDEX covers a commit that
    # has not happened yet. That is the whole reason a blob id beats a commit id here.
    if ref == INDEX:
        blobs = index_blobs()
        moved = worktree_modified()
        why_moved = 'modified in the worktree since it was staged'
    elif ref == 'HEAD':
        blobs = ref_blobs(ref)
        moved = differs_from(ref)
        why_moved = 'differs from HEAD in the worktree or index'
    else:
        # ⚠⚠ FAIL CLOSED ON A REF WE CANNOT FENCE. `differs_from` diffs against HEAD and returns an
        # EMPTY set for any other ref, so an arbitrary basis silently disabled the fence: every path
        # recorded cleanly against that ref's blobs while the checker had read today's disk.
        # Measured 2026-08-23 by a reliability trial: `ZPLEDGER_BASIS=<older sha> check_encoding
        # --record` printed `recorded PASS 425 subject(s)`, exit 0, keyed to an older commit's
        # blobs, with no warning. The record is internally consistent, so the server cannot detect
        # it — this is the mechanism for manufacturing keys for content nobody opened, and
        # `can_push` gates every commit in a range.
        # A checker reads the WORKING TREE. Only HEAD (clean) or the INDEX can correspond to what it
        # read, so any other basis is refused rather than fenced.
        blobs, moved = {}, set(rels)
        why_moved = ('basis %r cannot be fenced — a checker reads the worktree, so only HEAD or '
                     'INDEX can correspond to what it read' % ref)
    subjects, skipped = [], []
    for rel in sorted(set(rels)):
        if rel in moved:
            skipped.append((rel, why_moved))
        elif rel not in blobs:
            skipped.append((rel, 'not staged' if ref == INDEX else 'not present at %s' % ref))
        else:
            subjects.append({'path': rel, 'git_blob_id': blobs[rel]})
    return subjects, skipped


def record_if_asked(step, scanned, bad, reason, argv=None, tier='M', ref='HEAD', withheld=None,
                    switches=()):
    """⭐ THE ONE CALL EVERY CHECKER MAKES. Identical shape everywhere, by design.

        rc = common.record_if_asked('check_x', scanned, bad, 'why it failed', argv)
        if rc:
            return rc

    `scanned` is the file set THIS checker's verdict was computed over — its own scope, never a
    shared roster, or the record claims coverage the checker never had. `bad` is the subset that
    failed. Returns 0 when there is nothing to do, or 2 when a verdict could not be RECORDED.

    ⚠⚠ `withheld` IS THE HONEST ESCAPE, AND IT IS NOT A FAILURE. Pass a reason string when the run
    was PARTIAL — a skipped class, an unavailable dependency — and NOTHING is recorded, so the key
    stays MISSING and the action BLOCKS. `check_paths` returns EXIT_SKIPPED with Mathlib absent, and
    `ci_report.py`'s own header records that scoring that as a pass would publish *"a GREEN REQUIRED
    CHECK covering a gate that was skipped"*. **"It could not decide" and "it decided yes" are the
    two facts this whole layer exists to keep apart**; a checker that cannot tell them apart is the
    defect, not the outage.

    ⚠ COVERAGE CARRIES FORWARD BY CONTENT, NOT BY COMMIT (measured 2026-08-23). A record satisfies
    any later commit whose subject blobs are unchanged — `can_push` gates EVERY commit in a range,
    and a record made once covers all of them until the files it named actually move. That is what
    makes per-commit recording cheap rather than quadratic, and it is why the identifier is a blob
    id rather than a commit."""
    argv = sys.argv[1:] if argv is None else argv
    if '--record' not in argv:
        return 0
    # ⚠ THE BASIS COMES FROM THE ENVIRONMENT, NOT FROM TEN CALL SITES. `precommit` sets
    # `ZPLEDGER_BASIS=INDEX` so every checker records the STAGED content in one place; a manual run
    # defaults to HEAD. Threading it through each checker's signature would be ten chances to
    # disagree about what a verdict is about.
    ref = os.environ.get('ZPLEDGER_BASIS') or ref
    if withheld:
        print('  not recorded: %s — %s' % (step, withheld))
        print('                a partial run must not record a PASS; the key stays MISSING.')
        return 0
    # ⚠⚠ AN EXEMPTION SWITCH IS PART OF THE SUBJECT SET, AND LEAVING IT OUT IS A BYPASS.
    # Measured 2026-08-23: `check_pov`'s subjects were its 291 scanned files and NOTHING from
    # `tools/verify/` — so `pov_baseline.txt` was not a subject. Grandfather a new violation into
    # that baseline and the record still reads SATISFIED, because the files it names did not move.
    # The verdict changed; the record could not tell. That is the exemption-switch fail-open
    # `gitRobot.md` §12-0-ter names, arriving through the subject list.
    #
    # ⚠ IT MATTERS TWICE OVER once anything SKIPS work on the strength of a fresh record: the
    # checker would never re-run, so the suppression would land unverified and unexamined. A
    # baseline is exactly the file whose edit MUST re-arm its checker.
    #
    # THE RULE: a subject set is everything the verdict DEPENDS ON, not merely everything it read.
    scanned = list(scanned) + [s for s in switches if s not in set(scanned)]
    bad = set(bad)
    return emit_verdict(step, ok_rels=[r for r in scanned if r not in bad],
                        bad_rels=sorted(bad), reason=reason, tier=tier, ref=ref)


def emit_verdict(step, ok_rels=(), bad_rels=(), reason=None, tier='M', ref='HEAD'):
    """Record one step's verdict in the ledger. Returns 0, or 2 if it could NOT be recorded.

    ⚠⚠ ONE DEFINITION, CALLED BY EVERY CHECKER. Fifteen copies of this block is the mirror defect
    this bundle exists to stop — and the worst place for it, because a checker whose emit drifted
    would report a verdict nobody can act on while every control stayed green.

    ⚠⚠ ONE RECORD PER (step, basis) — V11, AND IT OVERRIDES `record.emit`'s DOCSTRING. That
    docstring says a step failing on one of forty files emits a PASS over thirty-nine and a FAIL
    over one. **The ledger refuses the second**: `(step, basis, revision)` is unique, so branching is
    unrepresentable rather than merely detected. Measured 2026-08-23 by running it — the PASS landed
    and the FAIL came back `V11`.
    ⚠ AND `revision` IS NOT THE ESCAPE. It is the supersede ordinal (a regrade); using it to carry a
    second simultaneous verdict would make a split look like a chain and corrupt tip resolution.
    So: ONE verdict for the step — FAIL if anything failed — over ALL the subjects it examined.
    Coverage stays exact because every examined file is still named; what is given up is a per-file
    verdict, which the admission gate never consumed. It asks whether the STEP passed.

    ⚠⚠ **A VERDICT IS ALWAYS A PROPERTY VERIFIED AGAINST A FILE SET** (Tim, 2026-08-23). There is no
    second kind of checker. A scanner's subjects are the files it scanned; a PROPERTY checker's
    subjects are the files its property was computed OVER — its inputs, the ones whose change could
    falsify it. `guards` holds over the checkers and exemption switches it exercises; `check_frozen`
    over the frozen baselines; `check_hashes` over the build scripts and `register.md`. Same shape,
    same staleness: change an input and the verdict must be re-earned.

    ⚠ THIS IS WHY THE SUBJECT SET IS NOT A JUDGEMENT CALL. Each checker already knows what it read;
    it must SAY so rather than let a caller guess. A property recorded against the wrong file set is
    worse than one not recorded at all — it claims the property still holds when its inputs moved,
    which is the exact fail-open shape (`RLY25-1`) this layer exists to end.

    ⚠⚠ EXIT 2, NEVER 1. "the check failed" and "the check could not be RECORDED" are different
    facts and only one is about the corpus. Collapsing them lets an outage read as a finding, or a
    finding read as an outage and get retried away."""
    import record
    bad = sorted(set(bad_rels))
    verdict = 'FAIL' if bad else 'PASS'
    subjects, skipped = ledger_subjects(sorted(set(ok_rels) | set(bad)), ref)
    for rel, why in skipped:
        print('  not recorded: %-52s %s' % (rel, why))
    if not subjects:
        # ⚠⚠ 2, NOT 0, WHEN THE CHECKER ACTUALLY EXAMINED SOMETHING. "I read the whole corpus and
        # could record none of it" is a RECORDING FAILURE — the step ends up MISSING and the
        # operator has just watched a green run. Returning 0 made that read as success, in the one
        # branch reached when every path was fenced out. `record.py`'s CLI already returned 2 here
        # and this shared path returned 0, so the two disagreed about the same condition.
        # ⚠ An EMPTY scan is different and stays 0: a checker whose scope matched nothing has
        # nothing to attest and is not failing. The discriminator is whether anything was examined.
        examined = len(set(ok_rels) | set(bad))
        if examined:
            print('  UNDECIDED: %s examined %d path(s) and could record NONE of them'
                  % (step, examined))
            return 2
        print('  nothing recordable for %s at this ref (nothing examined)' % step)
        return 0
    why = None
    if bad:
        why = '%s — %d failing subject(s): %s' % (reason or 'see the run output', len(bad),
                                                  ', '.join(bad[:5]) + ('…' if len(bad) > 5 else ''))
    rid = record.emit(step=step, tier=tier, verdict=verdict, subjects=subjects,
                      basis=ledger_basis(ref), reason=why)
    if rid is None:
        print('UNDECIDED: %s ran but its %s verdict was not recorded' % (step, verdict))
        return 2
    print('  recorded %-4s %4d subject(s)  %s' % (verdict, len(subjects), rid))
    return 0


def targets(skip_names=(), is_vendored=None):
    """Yield `(path, rel)` for every file in the `.lean` + `.py` + tracked-`.md` scan scope.

    `skip_names` is the CALLER's own additions — its own source file and its own baseline. Passing
    them rather than listing them here is deliberate: a shared roster of every checker's filename
    would exempt every checker from every other checker, which is the self-exemption hole
    `vendored.py` records being reached twice.

    `is_vendored` is passed in rather than imported so this module keeps zero local imports (see the
    header). Callers hand it `vendored.is_vendored`. Vendored backports are exempt STRUCTURALLY:
    upstream's prose is not a claim of ours to measure."""
    skip = set(SKIP_NAMES) | set(skip_names)
    globbed = [p for pat in GLOBS for p in REPO.glob(pat)]
    for p in globbed + tracked_md():
        rel = p.relative_to(REPO).as_posix()
        if p.name in skip or any(('/' + d + '/') in ('/' + rel) for d in SKIP_DIRS):
            continue
        if is_vendored is not None and is_vendored(p, rel):
            continue
        yield p, rel


# --------------------------------------------------------------------------- baselines
# ⚠⚠ THE ACCEPTED-DEFECT BASELINES ARE FROZEN AS OF 2026-08-22. NOTHING IS EVER ADDED AGAIN.
#
# Tim: *"We should never be adding anything to the baseline at this point, period… all we need to do
# is work through the backlog. Step one is to stop the bleeding — no new additions. **You don't have
# to guard a backlog that's impossible to be written.**"*
#
# That last sentence is the whole design. An earlier draft built a retired-entry list, a check that
# no retired entry could reappear, and a git-history check guarding THAT — three mechanisms, all of
# them there to catch an entry coming back. **If the file can never be written, nothing can come
# back**, and all three collapse into one property: the set may only SHRINK.
#
# ⚠ THIS SET IS ONLY THE ACCEPTED-DEFECT BACKLOG. It is NOT every data file near it, and the
# distinction is load-bearing — freezing the wrong one breaks the pipeline:
#   * `decl_baseline.txt` is a high-water mark of KNOWN DECLARATIONS used to detect new ones. It MUST
#     grow with the corpus; frozen, every future declaration looks new forever.
#   * `encoding_whitelist.txt` holds VERIFIED exclusions with stated reasons, for text the round-trip
#     test provably cannot decide (`3 × 10²` encodes to valid UTF-8). A permanent correct carve-out,
#     not deferred work.
#   * `scope_baseline.txt` / `pattern_baseline.txt` pin what the checkers scan and look for.
#     Configuration, not debt — a separate question, deliberately not answered here.
#   * `shared_build_baseline.txt` records the hash `zp_utils.py` last carried, so a change to
#     the one module every build script imports forces a look at every document. Same KIND as
#     `decl_baseline.txt` - a high-water mark, not accepted defect. Frozen, `zp_utils` could
#     never legitimately change.
FROZEN_BASELINES = frozenset([
    'prose_baseline.txt', 'pov_baseline.txt', 'figures_baseline.txt',
    'modal_baseline.txt', 'negatives_baseline.txt', 'class_baseline.txt',
])


def refuse_baseline_write(name, tool=None):
    """Refuse a `--baseline` regenerate on a frozen accepted-defect baseline. NEVER RETURNS.

    ⚠ THE FLAG IS KEPT AND MADE TO REFUSE, RATHER THAN DELETED (Tim, 2026-08-22). Deleting it yields
    `unknown option`, which teaches nothing and sends the reader looking for a way around — a
    hand-edit, or their own regeneration loop. **A flag that exists and explains itself is a lesson
    delivered at the exact moment of temptation**, and it keeps every docstring and usage line that
    mentions `--baseline` pointing at something true instead of turning them into dead pointers.
    """
    import sys as _sys
    bar = '=' * 72
    _sys.stderr.write(
        '\n%s\n  REFUSED — %s is FROZEN. Nothing is ever added to it again.\n%s\n\n'
        '  This file is a BACKLOG OF ACCEPTED DEFECTS being drained to zero, not a place to\n'
        '  put new work. Regenerating it would absorb whatever currently violates — which is\n'
        '  a measured fail-open here, not a hypothetical: `batch.py decls --baseline`, the\n'
        '  command the hook itself printed as the remedy, swallowed a live purity obligation\n'
        '  and took the run from exit 1 to exit 0 with the checker hashes byte-identical.\n\n'
        '  WHAT TO DO INSTEAD, and it depends on what you are actually looking at:\n\n'
        '    The finding is REAL      -> fix the site. That is the whole job now; the backlog\n'
        '                                only shrinks. Run the checker again and it goes green.\n\n'
        '    The finding is a FALSE   -> then the CHECKER is wrong, and suppressing the symptom\n'
        '    POSITIVE                    hides a defect in the verification layer. Route it:\n'
        '                                open a row in DEFECTS.md and fix the check, or take it\n'
        '                                through /rely. Do not launder a checker bug into the\n'
        '                                accepted-defect list.\n\n'
        '    You need to see the      -> `python tools/verify/debaseline.py --bucket <name>`\n'
        '    remaining work              lists it, bucketed, MECHANICAL vs SEMANTIC.\n\n'
        '  Removing an entry is always allowed. Adding one is not.\n%s\n\n'
        % (bar, name, bar, bar))
    _sys.exit(2)


def load_baseline(path, field0=False):
    """Grandfathered sites. A baseline is DEBT, not a decision — it blocks on NEW sites only.

    **The superset of the four readings this replaced**, each of which was verified to produce an
    identical key set on all eight real baseline files before unification:

    * `utf-8-sig` decodes a BOM away instead of welding it onto the first key. Identical to `utf-8`
      on a file without one, which all eight currently are.
    * The `#` test runs on the STRIPPED line, so an indented comment is a comment. Four of the six
      copies tested the raw line and would have loaded `  # note` as a key.

    `field0=True` takes the tab-delimited first field — `check_pov`'s baseline format, where the
    remainder of the line is the per-site reading note.

    ⚠ **ADD ENTRIES BY HAND.** `--baseline` regeneration discards every comment: it once took
    `modal_baseline.txt` from 26 lines to 5, destroying the per-site notes that file's own header
    requires. Regeneration also grandfathers sites nobody read, which falsifies the one property
    that makes a baseline worth anything."""
    path = Path(path)
    if not path.exists():
        return set()
    out = set()
    for line in io.open(str(path), encoding='utf-8-sig').read().splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        out.add(line.split('\t')[0].strip() if field0 else line)
    return out


def write_text_lf(path, text):
    """Write a TRACKED file. LF, UTF-8, no BOM. **Never use a bare `write_text` for one.**

    ⚠ **THIS IS A LIVE DEFECT CLASS, NOT A STYLE PREFERENCE.** `check_invariants` blocks on CRLF in
    any tracked text file on disk, and `Path.write_text` / `open(..., 'w')` without `newline=''`
    translates `\\n` to `\\r\\n` on Windows. So a `--baseline` regeneration wrote a file that
    immediately failed the suite's own byte-portability gate.

    The class was closed among the BUILD SCRIPTS on 2026-08-16 — `build_snap_map` was the third of
    three — and was still open in five places inside this bundle: the `check_modal` and `check_pov`
    baseline writers and `check_hashes`'s three `register.md` writers. Fixing those five as sites
    would have been the fourth occurrence of fix-the-site-not-the-class in a row, so the writer is
    shared instead and there is one place left to get it wrong.

    Why it matters beyond the gate: `register.md` carries build-script fingerprints, and
    `check_invariants` records what a byte difference costs there — `check_hashes` exiting 0 on the
    author's machine and 1 in a fresh clone. A provenance token that reproduces on one machine only
    is not provenance.

    ⚠ **THE PARENT DIRECTORY IS CREATED IF ABSENT, and that is not a convenience — it is the fix for
    three crashes in a PUBLIC CLONE.** `.claude-local/` is gitignored, so it does not exist in any
    clone that is not the author's, and every piece of per-push state lives there. Measured
    2026-08-16 in a worktree with the private folder absent: `gate_round.py bump`, `gate_round.py
    reset` and `batch.py start` each died with a raw `FileNotFoundError` traceback rather than a
    verdict — **the three commands a remediation cycle needs FIRST.** `gate_round.py show` succeeds
    (it reports round 0 when state is missing), so the failure arrives mid-flow rather than at the
    door. Pre-existing at `ab2a693`, so not introduced by the dedup.

    `guards.py`'s `_rewrite` had already learned this the same way and fixed it locally, for itself,
    in August — which is the copy-instead-of-share pattern this module exists to end. One writer, one
    place, and the lesson applies everywhere it is used."""
    p = Path(path)
    if p.parent and not p.parent.is_dir():
        p.parent.mkdir(parents=True, exist_ok=True)
    with io.open(str(p), 'w', encoding='utf-8', newline='\n') as fh:
        fh.write(text)


# --------------------------------------------------------------------------- text normalization
#
# These three lived in `check_modal` and were imported from it by `check_negatives` and
# `check_figures`, which made a CHECKER into a LIBRARY. That was the cheap move, not the right one:
# a peer then depends on another peer's internals, and the dependency is invisible from either end.
_SEP = re.compile(
    r"(?m)^[ \t]*(?:--+|//+|\*)[ \t]*"       # Lean/C line-comment continuation
    r"|'[ \t]*\r?\n[ \t]*'"                   # Python adjacent-string-literal join
    r'|"[ \t]*\r?\n[ \t]*"')


def normalize_separators(text):
    """Blank the separators that sit inside a WRAPPED phrase, preserving character offsets.

    ⚠ `\\s+` between words is not enough, and the first fix stopped there. In real sources the gap
    between wrapped words is not whitespace:

        Lean:   "-- ... is a library\\n--     artifact, not a\\n--     necessity."
        Python: "'... is a library '\\n            'artifact, not a necessity'"

    A `--` or a quote-comma-quote sits in the middle, so the phrase stays invisible. Measured by
    planting a wrapped probe in a real file after the first fix: it did not fire.

    ⚠ Substituting spaces of EQUAL LENGTH preserves every character OFFSET — but **not** line
    numbers, and an earlier docstring wrongly claimed it did. The Python adjacent-string-literal
    alternative CONSUMES the newline, so a phrase on line 78 reported as line 40 after 38 joins.
    Count line numbers against the ORIGINAL text, never the normalized copy."""
    return _SEP.sub(lambda m: ' ' * len(m.group(0)), text)


def strip_module_docstring(text, path):
    """Blank a build script's leading docstring so its changelog is not scanned.

    Line count is preserved so reported line numbers stay correct."""
    if not str(path).endswith('.py'):
        return text
    m = re.match(r'\s*(?:"""|\'\'\')', text)
    if not m:
        return text
    q = text[m.end() - 3: m.end()]
    end = text.find(q, m.end())
    if end < 0:
        return text
    head = text[:end]
    return '\n' * head.count('\n') + text[end:]


# --------------------------------------------------------------------------- the control harness
def run_controls(groups, width=34):
    """Run MUST-FIRE / MUST-SUPPRESS control groups. Returns 1 on any failure, else 0.

    `groups` is a list of `(title, items, predicate, expect, failure_label)` — or a 6-tuple with a
    trailing `detail(text) -> str` rendered after a failure, for checkers that report WHICH pattern
    matched. `items` is a list of `(label, text)`; `predicate(text)` returns whether the checker
    FIRED; `expect` is what firing should be for that group — `True` for a must-fire, `False` for a
    must-suppress.

    ⚠ **THE INVERSION IS WHY THIS IS SHARED AND NOT COPIED.** The comment inside
    `check_modal.py`'s `selftest()` records the bug verbatim: the first version reused the must-fire
    loop's `bad += 0 if got else 1` for the suppression group, and reported `FAIL (5)` while printing
    `ok` on all five. The summary contradicted the detail, which is the only reason it was caught.
    Fifteen hand-written copies of this loop is fifteen chances to write that line the wrong way
    round; one `expect` parameter is none.

    ⚠ Cited by DECLARATION, not by line. This sentence said `check_modal.py:302` and the record had
    moved to `:230` — because collapsing that very selftest into this harness shortened the file.
    A line number is a copy of a location and drifts exactly like any other copy; a function name
    does not.

    ⚠ **AND THE CONTROL TEXT MUST BE THE CHECKER'S OWN.** Three separate agents independently ran a
    must-fire probe using a hand-written violation the checker does not detect, got a pass, and
    nearly drew the opposite conclusion. Pass the module's real `MUST_FIRE` strings, verbatim."""
    bad = 0
    for group in groups:
        title, items, predicate, expect, fail_label = group[:5]
        detail = group[5] if len(group) > 5 else None
        print(title)
        for label, text in items:
            got = bool(predicate(text))
            ok = (got == expect)
            suffix = '' if (ok or detail is None) else detail(text)
            print('  %-*s %s%s' % (width, label,
                                   'ok' if ok else '*** %s ***' % fail_label, suffix))
            bad += 0 if ok else 1
    print('\nselftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


def fire_suppress(must_fire, must_suppress, predicate, what, width=34):
    """The two-group shape 13 of the 15 selftests use. `what` names the thing being detected."""
    return run_controls([
        ('MUST FIRE (%s)' % what, must_fire, predicate, True, 'MISSED'),
        ('MUST SUPPRESS', must_suppress, predicate, False, 'FALSE POSITIVE'),
    ], width=width)


# --------------------------------------------------------------------------- self-check
SELF = self_rel(__file__)

_MUST_FIRE = [
    ('an unindented comment is skipped', '# a comment'),
    ('an indented comment is skipped', '   # a comment'),
]
_MUST_SUPPRESS = [
    ('an ordinary key survives', 'ZeroParadox/Foo.lean|some claim'),
    ('a key containing # survives', 'scripts/build_x.py|the # sign'),
]


def selftest():
    """Controls for this module itself — it is now load-bearing for thirteen checkers.

    ⚠ A shared module with no controls is a single point of silent failure, which is strictly worse
    than the duplication it replaced: one wrong `SKIP_DIRS` entry here is a false zero in every
    checker at once, where before it was a false zero in one."""
    import tempfile
    bad = 0
    print('MUST FIRE (load_baseline drops it)')
    for label, line in _MUST_FIRE:
        with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False,
                                         encoding='utf-8', newline='\n') as fh:
            fh.write(line + '\n')
            tmp = fh.name
        got = not load_baseline(tmp)
        os.unlink(tmp)
        print('  %-40s %s' % (label, 'ok' if got else '*** KEPT ***'))
        bad += 0 if got else 1
    print('MUST SUPPRESS (load_baseline keeps it)')
    for label, line in _MUST_SUPPRESS:
        with tempfile.NamedTemporaryFile('w', suffix='.txt', delete=False,
                                         encoding='utf-8', newline='\n') as fh:
            fh.write(line + '\n')
            tmp = fh.name
        got = load_baseline(tmp) == {line}
        os.unlink(tmp)
        print('  %-40s %s' % (label, 'ok' if got else '*** DROPPED ***'))
        bad += 0 if got else 1

    # A BOM must not weld itself onto the first key — the utf-8 vs utf-8-sig divergence, tested
    # rather than asserted.
    with tempfile.NamedTemporaryFile('wb', suffix='.txt', delete=False) as fh:
        fh.write(b'\xef\xbb\xbfZeroParadox/Foo.lean|claim\n')
        tmp = fh.name
    ok = load_baseline(tmp) == {'ZeroParadox/Foo.lean|claim'}
    os.unlink(tmp)
    print('BOM')
    print('  %-40s %s' % ('a BOM is decoded away', 'ok' if ok else '*** BOM IN KEY ***'))
    bad += 0 if ok else 1

    # The roots must resolve to real directories, or every checker built on them scans nothing.
    print('ROOTS')
    for name, p, must_exist in (('REPO', REPO, True), ('HERE', HERE, True), ('SRC', SRC, True)):
        ok = p.is_dir() if must_exist else True
        print('  %-40s %s' % ('%s resolves (%s)' % (name, p.name), 'ok' if ok else '*** MISSING ***'))
        bad += 0 if ok else 1

    # ⚠ SHAPE ASSERTIONS. These say the enumerator returns the right KINDS of file. They are NOT a
    # scope control and must not be described as one — see the block below for why that distinction
    # cost a bedrock finding.
    print('SHAPE')
    rels = [rel for _p, rel in targets()]
    for label, test in (
            ('scan set is populated', len(rels) > 100),
            ('reaches nested .lean', any(r.startswith('ZeroParadox/') and r.endswith('.lean')
                                         and r.count('/') > 1 for r in rels)),
            ('reaches nested tracked .md', any(r.endswith('.md') and '/' in r for r in rels)),
            ('reaches scripts/*.py', any(r.startswith('scripts/') and r.endswith('.py')
                                         for r in rels)),
            ('excludes the private folder', not any(r.startswith('.claude-local/') for r in rels)),
    ):
        print('  %-40s %s' % (label, 'ok' if test else '*** FAILED ***'))
        bad += 0 if test else 1

    # ═══ THE SCOPE CONTROL ═══════════════════════════════════════════════════════════════════
    #
    # ⚠⚠ **TWO EARLIER VERSIONS OF THIS CONTROL EACH CLOSED ONE ROUTE AND LEFT THE PROPERTY OPEN.**
    # The first asserted the scan set was non-empty and reached each file KIND — defeated by adding
    # `'Order'` to `SKIP_DIRS`, which left nested `.lean` files elsewhere so nothing fired. The
    # second asserted every `ZeroParadox/` subdirectory contributed a file — defeated three more
    # ways, each a one-word edit, each with a live violation on disk and every gate green including
    # the PUSH gate: `SKIP_DIRS += 'commands'` took out every published gate brief, `SKIP_NAMES +=
    # 'BottomCannotBe.lean'` took out a keystone index, and dropping `tools/**/*.py` from `GLOBS`
    # took out the verification layer itself. Roughly a THIRD of the scan set was pinned by nothing
    # at all (measured 2026-08-16; the four routes below are now controls, so measure rather than
    # trust this sentence).
    #
    # **The error was enumerating INPUT routes inside a fix for a routes-class defect.** Pinning the
    # OUTPUT makes every route fail at once, including the ones nobody has enumerated — which is the
    # only form that survives a reviewer smarter than the author. SUPERSET, so adding files is free
    # and only a NARROWING fires; deleting a source file needs its line removed here, a reviewable
    # act, on the same bargain every other baseline in this suite makes.
    print('SCOPE (the recorded scan set is still covered)')
    recorded = load_scope('common.targets')
    bad += check_scope('common.targets', rels)

    # The registry that decides what is EXEMPT from pinning is itself checked here — it is the one
    # exemption surface in this bundle that had no registry-level control, which is exactly how
    # SKIP-3 got in.
    bad += check_exemption_registry()

    # ⚠ MUST-FIRE, IN PROCESS. Each is a route `/rely` used to defeat the previous control. They
    # mutate module constants and restore them, so nothing touches disk and no probe can be left
    # behind by a killed run — unlike `guards.py`, whose file-planting probe was found stranded in a
    # real source file today after an interrupted run.
    print('SCOPE CONTROLS (each route must be caught)')
    import contextlib

    @contextlib.contextmanager
    def _swapped(name, value):
        old = globals()[name]
        globals()[name] = value
        try:
            yield
        finally:
            globals()[name] = old

    for label, name, value in (
            ('SKIP_DIRS gains a ZeroParadox subdir', 'SKIP_DIRS', SKIP_DIRS + ('Order',)),
            ('SKIP_DIRS gains a non-corpus dir', 'SKIP_DIRS', SKIP_DIRS + ('commands',)),
            ('SKIP_NAMES gains a basename', 'SKIP_NAMES',
             frozenset(SKIP_NAMES | {'BottomCannotBe.lean'})),
            ('GLOBS drops a pattern', 'GLOBS', tuple(g for g in GLOBS if g != 'tools/**/*.py')),
    ):
        with _swapped(name, value):
            caught = bool(recorded - {r for _p, r in targets()})
        print('  %-40s %s' % (label, 'ok' if caught else '*** NOT CAUGHT ***'))
        bad += 0 if caught else 1

    # ⚠ THE PIN'S MESSAGE IS PART OF THE PIN (`RLY16-8`). A control that fires and cannot say WHAT
    # changed leaves re-pinning blind as the only response, which converts a precise gate into a
    # rubber stamp. The failing shape is a long shared prefix — a pattern's name plus the opening of
    # its regex — which the old fixed `[:38]` window rendered identically on both sides.
    # ⚠ TWO PROPERTIES, NOT ONE. The first version asserted only that the two sides RENDER
    # DIFFERENTLY, and was therefore green on the mirror defect /rely found: windowing on the first
    # difference walks past the `NAME\t` prefix, so a regex-only edit produced a legible diff of an
    # ANONYMOUS pattern. With 92 pinned patterns that is as unactionable as the identical-sides bug
    # it replaced. A message is legible only if it says WHICH pattern and HOW it changed.
    print('MUST DISTINGUISH (a pattern edit names the pattern AND shows the change)')
    _shared = '_SOME_LONG_PATTERN_NAME\t(?:alpha|beta|gamma|delta)+\\s*'
    for _label, _a, _b, _want in (
        ('long shared prefix', _shared + 'AAA', _shared + 'BBB', '_SOME_LONG_PATTERN_NAME'),
        ('differs at char 0', 'aaa\tone', 'bbb\ttwo', 'aaa'),
        ('one is a prefix of the other', _shared, _shared + 'XYZ', '_SOME_LONG_PATTERN_NAME'),
        ('regex-only edit, long name', '_N\tzzzz' + 'q' * 60 + 'A', '_N\tzzzz' + 'q' * 60 + 'B', '_N'),
    ):
        _msg = render_pattern_delta([_a], [_b])
        _named = _want in _msg
        _rest = _msg.split(']: ', 1)[-1]
        _l, _, _r = _rest.partition(' -> ')
        _r = _r.split(' ***', 1)[0]
        _shown = _l != _r
        _ok = _named and _shown
        bad += 0 if _ok else 1
        _why = '' if _ok else ('  NAME MISSING' if not _named else '  both sides render %r' % _l)
        print('  %-40s %s%s' % (_label, 'ok' if _ok else '*** ILLEGIBLE ***', _why))

    print('\nselftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


if __name__ == '__main__':
    utf8_stdout()
    if '--selftest' in sys.argv:
        sys.exit(selftest())
    print('%s — shared definitions for the verification bundle. Nothing to run.' % SELF)
    print('  REPO %s' % REPO)
    print('  HERE %s' % HERE)
    print('  PRIV %s%s' % (PRIV, '' if PRIV.is_dir() else '   (absent — public clone)'))
    print('  scan scope: %d files' % len(list(targets())))
    print('\n  --selftest   run this module\'s own controls')
