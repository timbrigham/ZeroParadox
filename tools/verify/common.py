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
    # ⚠⚠ **THE ASSERTIONS ABOVE WERE LABELLED "THE SCOPE CONTROL" AND COULD NOT SEE A SCOPE
    # COLLAPSE. That is DC-18 — a proxy for the property, in the control written against exactly the
    # risk this module creates.** Measured by `/rely` 2026-08-16, and the probe is the one to keep:
    # plant `check_negatives`' own MUST_FIRE string (confirmed exit 1), then add ONE WORD — `'Order'`
    # — to `SKIP_DIRS`. `check_negatives`, `check_modal` and `check_figures` all went to **exit 0
    # with the violation still live**, the scan set fell 330 → 317, and every assertion above still
    # printed `ok`. They test NON-EMPTINESS: drop one directory and there are still nested `.lean`
    # files elsewhere, so nothing fires.
    #
    # **The fix is to derive what MUST be covered from the tree rather than asserting a shape.**
    # Every immediate subdirectory of `ZeroParadox/` holding a `.lean` file must contribute at least
    # one file to the scan set. That is self-maintaining — a new subsystem is covered the day it is
    # created, with nothing to remember — and it fails loud on precisely the edit that defeated the
    # old version, because excluding `Order` removes `ZeroParadox/Order/` from the set entirely.
    #
    # ⚠ `Vendored/` is the one legitimate absence: backports are exempt STRUCTURALLY (`vendored.py`),
    # so requiring coverage of it would assert the opposite of the rule.
    print('SCOPE (every ZeroParadox/ subsystem is reached)')
    covered = {r.split('/')[1] for r in rels
               if r.startswith('ZeroParadox/') and r.count('/') > 1}
    expected = {d.name for d in SRC.iterdir()
                if d.is_dir() and d.name != 'Vendored' and any(d.rglob('*.lean'))}
    missing = sorted(expected - covered)
    ok = not missing
    print('  %-40s %s (%d/%d subsystems)'
          % ('no subsystem has fallen out of scope',
             'ok' if ok else '*** %d MISSING: %s ***' % (len(missing), ', '.join(missing[:5])),
             len(covered & expected), len(expected)))
    bad += 0 if ok else 1

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
