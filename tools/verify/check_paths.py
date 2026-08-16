"""Verify every repo-relative file reference resolves — tracked markdown AND the private layer.

The File-Reference Citation Convention (CLAUDE.md, 2026-07-08) requires full repo paths in
checkable surfaces, so that a move/rename fails LOUD rather than silently pointing nowhere.
This is the resolver that convention names as its enforcement.

Scope note (2026-07-19): the tracked layer was already clean when this was first run
(465/465 resolved). Every dangling reference found by the rule audit lived in the UNTRACKED
layer — memory files and .claude-local notes — which no gate covers. That is the decay this
tool exists to stop, so it checks both.

Usage (the exact invocation path is printed in this tool's own output):
    check_paths.py            # tracked markdown only (exit 1 if dangling)
    check_paths.py --all      # + memory and .claude-local notes
    check_paths.py --all --warn-private
                              # private-layer hits do not fail the build
    check_paths.py --selftest # must-fire AND must-suppress controls

Exit 0 = clean.  Exit 1 = at least one dangling reference in a failing scope.
"""
import re
import subprocess
import sys
from pathlib import Path

from vendored import is_vendored

# ⚠ RLY15-1 — IMPORTED FOR ITS SIDE EFFECT, DELIBERATELY. `report.py` reconfigures stdout to UTF-8
# with line buffering at import, and states that every entry point should inherit it by importing
# the formatter "so it cannot drift between them". This file prints non-ASCII (a warning glyph), and
# Windows selects cp1252 for a PIPE OR REDIRECT while picking UTF-8 only for a real console — so
# without this the tool exits 1 on an unhandled UnicodeEncodeError in exactly the redirected shape
# CLAUDE.md mandates for pushes, while looking green when run by hand.
# ⚠ It went unnoticed here only because this shell happens to export
# `PYTHONIOENCODING=utf-8:surrogateescape`; that variable is NOT version-controlled, so CI, a fresh
# clone and a spawned agent all lack it. A checker whose exit code depends on the caller's terminal
# is not an instrument. Measured by a `/rely` pass whose environment did not carry the variable.
import report  # noqa: F401  (side effect only)

# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3).
import common  # noqa: E402
from common import HERE, REPO  # noqa: E402

SELF = common.self_rel(__file__)
MEMORY = Path.home() / '.claude' / 'projects' / 'C--Workspace-ZeroParadox' / 'memory'
# The private layer this tool scans for dangling references. Unlike the baselines, this genuinely
# IS `.claude-local` — it is the thing being checked, not state belonging to the checker.
NOTES = REPO / '.claude-local'

# Repo-relative references to real project files. Deliberately narrow: only paths that
# start at a known top-level directory, so prose like "see Foo/Bar" is not misread.
PATTERN = re.compile(
    r'(?<![\w/.-])((?:ZeroParadox|scripts|\.github)/[A-Za-z0-9_./-]+\.(?:lean|py|md|json|yml|yaml))'
)

# Bare Lean basenames (pre-reorg style, e.g. ZPJ_APG.lean). These are the silent-failure class
# the citation convention was written to prevent — flagged separately, resolved by search.
BARE_LEAN = re.compile(r'(?<![\w/.-])((?:ZP[A-Z]?[A-Za-z0-9_]*)\.lean)')

# === PRIVATE-LAYER DEPENDENCIES (PATH-3) =====================================================
# A tracked file must be self-sufficient for a reader who has only the repo. It may cite public
# sources; it may not depend on files that are not in the repo for its meaning. `.claude-local/`
# is gitignored and unreachable to an external reader, so every reference to it from a tracked
# file is exactly such a dependency.
#
# ⚠ TWO FORMS, AND THE SECOND IS WHY THIS EXISTS. Grepping for the private folder's NAME finds
# only the path-qualified form. A citation written as a BARE note basename carries no path and is
# INVISIBLE to that grep — `(`thread_obstruction_table_2026-06-29.md` §7)` resolves to nothing in
# a public clone and no name-grep can see it. Found by the editorial gate 2026-08-12, which
# measured 22 bare-basename sites across 21 tracked `.lean` files against the 26 path-qualified
# ones the ledger had counted: the population was roughly DOUBLE the recorded figure, and the row
# being sized from it was the note-pointer burn-down itself.
#
# This is the project's own rule that a search is a PROJECTION and loses whatever is orthogonal
# to it — so the detector carries BOTH polarities rather than the one that was natural to write.
PRIVATE_REF = re.compile(r'(?<![\w/.-])(\.claude-local/[A-Za-z0-9_./-]+)')

# A dated-note citation in one of the three note-filename shapes this project actually uses (the
# same three `DATED` below recognises: hyphenated, compact, month-name), **with or without a path
# prefix**. A dateless `.md` basename is NOT matched — `README.md` and friends are ordinary public
# files, not private notes.
#
# ⚠ RLY14-2: the optional `(?:…/)*` prefix is the fix. The two original patterns had a gap BETWEEN
# them — `PRIVATE_REF` requires the literal `.claude-local/`, and a bare-basename pattern's
# lookbehind is defeated by any `/`, so a dated note cited under any OTHER relative prefix
# (`notes/foo_2026-05-31.md`) was invisible to both, and to the blocking `PATTERN` above, which
# anchors only `ZeroParadox|scripts|.github`. One live instance existed in tracked Lean.
# Matches starting `.claude-local/` are dropped by the scanner, since `PRIVATE_REF` already has
# them — that keeps the two counts disjoint.
NOTE_REF = re.compile(
    r'(?<![\w/.-])((?:[A-Za-z0-9_.-]+/)*'
    r'[A-Za-z0-9][A-Za-z0-9_-]*'
    r'(?:\d{4}-\d{2}-\d{2}|\d{8}|(?:jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\d{4})'
    r'\.md)',
    re.IGNORECASE,
)

# Substrings that mark a reference as deliberately non-resolving (a note ABOUT a dead path).
SKIP_MARKERS = (
    'retired', 'no longer exist', 'does not exist', 'pre-reorg', 'post-reorg', 'formerly',
    'was at', 'old path', 'renamed', 'dead', 'stale', 'moved to', 'now at', 'corrected',
    'do not recreate', 'synced to', '->', '→', 'superseded', 'historical',
)

# ⚠ The arrow markers above are PROSE markers ("Foo.lean -> Bar.lean" = a note about a move).
# In LEAN SOURCE `→` and `->` are the function arrow and appear on a large fraction of lines,
# so reusing this tuple for .lean files would silently skip most of the file and report a clean
# scan — the exact fail-open shape this resolver exists to prevent. Lean gets its own set.
SKIP_MARKERS_LEAN = tuple(m for m in SKIP_MARKERS if m not in ('->', '→'))

# Mathlib citations resolve under the pinned checkout, not the repo root. They are a real and
# frequently-cited class in this corpus (CLAUDE.md: "verify an API exists before naming it"),
# and a dead one fails silently exactly like a dead repo path.
MATHLIB_PATTERN = re.compile(
    r'(?<![\w/.-])((?:Mathlib|Std|Batteries)/[A-Za-z0-9_./-]+\.lean)'
)
MATHLIB_ROOTS = (
    REPO / '.lake' / 'packages' / 'mathlib',
    REPO / '.lake' / 'packages' / 'batteries',
    REPO / '.lake' / 'packages' / 'std4',
    REPO / '.lake' / 'packages',
)


# ⚠ IS THE PINNED CHECKOUT EVEN HERE? `.lake/packages/` is a BUILD ARTIFACT — gitignored, absent
# from every fresh clone, absent from a git worktree, and absent in CI, which runs this suite with
# `actions/setup-python` and no Lean toolchain at all.
#
# Without this guard the checker reported "63 of 63 DANGLING MATHLIB CITATIONS" anywhere Mathlib
# was not built, and exited 1. Measured 2026-08-15 in a clean worktree; the new CI job would have
# published that on every single run. Sixty-three correct citations reported as broken is the
# cry-wolf shape, and it would have taught everyone to ignore a red `check_paths`.
#
# Unavailable is not wrong. The same distinction the AR tracker needed in `check_hashes.py`: a
# check that cannot run must SAY SO, not fail.
MATHLIB_PRESENT = any(base.is_dir() for base in MATHLIB_ROOTS)


def mathlib_resolves(ref):
    """True if a Mathlib/Std/Batteries path exists under any pinned package root.

    ⚠ Returns True unconditionally when the checkout is ABSENT. That is a skip, not a pass, and the
    caller says so in its output — `scan()` returns a different arity depending on `check_mathlib`,
    so branching at the call site raised `ValueError: expected 5, got 3` the moment it was tried."""
    if not MATHLIB_PRESENT:
        return True
    return any((base / ref).exists() for base in MATHLIB_ROOTS)


# ZeroParadox/Vendored/ records the UPSTREAM PROVENANCE of files Mathlib has removed — naming a
# path that no longer exists is the entire point of the header (NaturalOps.lean:5 cites the
# v4.28.0 source, removed upstream 2026-02-20, which is WHY it is vendored). Resolving those
# would be wrong, so the directory is exempt from the Mathlib check. Measured as a false
# positive on the resolver's first run, 2026-08-01.
MATHLIB_EXEMPT_DIRS = ('Vendored',)


def mathlib_exempt(path):
    return any(part in MATHLIB_EXEMPT_DIRS for part in path.parts)


def tracked_markdown():
    out = subprocess.run(
        ['git', 'ls-files', '*.md'], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.split('\n')
    return [REPO / p for p in out if p.strip()]


# A filename carrying a date is a DATED RECORD (a review verdict, a session note). Its file
# references describe the tree as it stood then; "fixing" them would falsify the record.
# Live rules and standing references have no date in the name — those must resolve.
# Match the date formats actually used in this project's filenames. The hyphenated form is the
# convention, but two other shapes exist and were initially misclassified as LIVE:
#   foo_2026-06-30.md   (convention)
#   foo_20260531.md     (compact)
#   foo_may2026.md      (month-name)
DATED = re.compile(
    r'\d{4}-\d{2}-\d{2}'
    r'|(?<!\d)\d{8}(?!\d)'
    r'|(?:jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\d{4}',
    re.IGNORECASE,
)

# Release history is never rewritten (CLAUDE.md); it names files as they were at each release.
RECORD_FILES = {'RELEASES.md'}


def private_markdown():
    files = []
    if MEMORY.is_dir():
        files += sorted(MEMORY.glob('*.md'))
    if NOTES.is_dir():
        files += sorted(NOTES.rglob('*.md'))
    # archived material is history; do not police it
    return [f for f in files if 'archive' not in f.parts and 'autobiography' not in f.parts]


def split_live_records(files):
    live = [f for f in files if not DATED.search(f.name) and f.name not in RECORD_FILES]
    records = [f for f in files if DATED.search(f.name) or f.name in RECORD_FILES]
    return live, records


def tracked_lean():
    """Tracked Lean sources. Never .lake/ — that is thousands of Mathlib files, not ours."""
    out = subprocess.run(
        ['git', 'ls-files', '*.lean'], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.split('\n')
    return [REPO / p for p in out if p.strip()]


UNREADABLE = []          # tracked files the scanner could not decode; each is a FAILURE, not a skip


def scan(files, find_bare, lean_mode=False, check_mathlib=False):
    dangling, bare, checked = [], [], 0
    mathlib_bad, mathlib_checked = [], 0
    markers = SKIP_MARKERS_LEAN if lean_mode else SKIP_MARKERS
    for md in files:
        try:
            text = md.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError) as exc:
            # ⚠ FAIL CLOSED. This used to `continue` with only a printed SKIP, so a file the
            # checker could not read was silently treated as a file with nothing wrong in it.
            # Measured /rely pass 7: one 0xff byte inserted into a tracked markdown hid a real
            # dangling reference and took the run from exit 1 to exit 0. An unreadable TRACKED
            # markdown is a defect in its own right — `.gitattributes` declares text LF — so
            # there is no case where skipping it is the right answer.
            print(f'UNREADABLE (counts as a failure): {md} — {exc}')
            UNREADABLE.append(md)
            continue
        for lineno, line in enumerate(text.split('\n'), 1):
            if any(m in line.lower() for m in markers):
                continue  # the line is discussing a dead path on purpose
            for ref in PATTERN.findall(line):
                checked += 1
                if not (REPO / ref).exists():
                    dangling.append((md, lineno, ref))
            if check_mathlib and not mathlib_exempt(md):
                for ref in MATHLIB_PATTERN.findall(line):
                    mathlib_checked += 1
                    if not mathlib_resolves(ref):
                        mathlib_bad.append((md, lineno, ref))
            if find_bare:
                for ref in BARE_LEAN.findall(line):
                    hits = list((REPO / 'ZeroParadox').rglob(ref))
                    bare.append((md, lineno, ref, hits[0].relative_to(REPO) if hits else None))
    if check_mathlib:
        return dangling, bare, checked, mathlib_bad, mathlib_checked
    return dangling, bare, checked


def scan_private_deps(files):
    """Tracked files depending on the gitignored private layer. Returns (qualified, bare).

    Vendored files are exempt STRUCTURALLY, via the one definition in `vendored.py` — never a
    restatement of it, per CLAUDE.md. Editing a backport's prose destroys the diff against
    upstream, which is the reason for vendoring it.
    """
    qualified, bare = [], []
    for f in files:
        # ⚠ RLY14-1: `vendored.py` normalises and tests a REPO-RELATIVE path. This call site used to
        # pass the absolute `Path`, so the exemption NEVER FIRED here — measured `is_vendored(rel)`
        # True, `is_vendored(abs)` False, and all three planted violations (Vendored/, allowlisted,
        # ordinary) were counted where one should have been. Importing the single shared definition
        # is necessary and was done; it is not sufficient, because the CALL can still be wrong.
        if is_vendored(f.relative_to(REPO).as_posix()):
            continue
        try:
            text = f.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError):
            continue  # already reported and failed-closed by scan()
        for lineno, line in enumerate(text.split('\n'), 1):
            for ref in PRIVATE_REF.findall(line):
                qualified.append((f, lineno, ref))
            for ref in NOTE_REF.findall(line):
                # already counted as path-qualified; keep the two buckets disjoint
                if ref.startswith('.claude-local/'):
                    continue
                bare.append((f, lineno, ref))
    return qualified, bare


def report_private_deps(qualified, bare):
    """INFORMATIONAL ONLY — deliberately does not set `failed`.

    This measures a KNOWN open item (PATH-3) with a large existing population, and CLAUDE.md is
    explicit that a gate which blocks everything on day one gets muted. It is also the wrong
    enforcement shape: the fix for most of these is folded into the header burn-down (PRS-3),
    because the sites sit inside grandfathered over-cap prose blocks that re-fire `check_prose`
    the moment they are touched. Measure now; baseline and block when the population is sized.
    """
    print('\n== private-layer dependencies in tracked files (PATH-3) ==')

    # ⚠ A RAW TOTAL HERE WOULD BE A READING LIST, NOT A FINDING LIST. The kinds have different
    # verdicts and must never be summed into one alarming number:
    #   translation_matrix/  the Meta tooling READS these. Functional paths, not citations. LEAVE.
    #   papers/              source pointers. Fix by citing the PUBLIC identifier (arXiv/DOI).
    #   notes/               the real item — a tracked file depending on an untracked one.
    #   CLAUDE.md            the operating manual, explicitly gate-exempt. Not a citation defect.
    def kind(ref):
        if 'translation_matrix' in ref:
            return 'translation_matrix (functional — tooling reads these; LEAVE)'
        if '/papers/' in ref:
            return 'papers (cite the public identifier instead)'
        if '/notes/' in ref:
            return 'notes (READ EACH — forbidden vs acceptable is not decidable here)'
        return 'other'

    lean_q = [t for t in qualified if t[0].suffix == '.lean']
    md_q = [t for t in qualified if t[0].suffix != '.lean' and t[0].name != 'CLAUDE.md']
    exempt_q = [t for t in qualified if t[0].name == 'CLAUDE.md']

    print(f'  tracked .lean, path-qualified : {len(lean_q)}')
    buckets = {}
    for t in lean_q:
        buckets.setdefault(kind(t[2]), []).append(t)
    for k in sorted(buckets):
        print(f'      {len(buckets[k]):3d}  {k}')
    print(f'  tracked .md (excl. CLAUDE.md) : {len(md_q)}')
    print(f'  CLAUDE.md (gate-exempt, N/A)  : {len(exempt_q)}')

    lean_bare = [t for t in bare if t[0].suffix == '.lean']
    # UNIT LABELS: every figure above is a count of REFERENCES, not of FILES. The ledger recorded
    # "43 tracked .lean files" when 43 was references and the distinct-file count was 28 (RLY14).
    print(f'  (all figures above are REFERENCES, not files — distinct .lean files: '
          f'{len({t[0] for t in qualified if t[0].suffix == ".lean"})})')
    print(f'\n  ⚠ NOT path-qualified — the shapes a grep for the folder name CANNOT see:')
    print(f'      {len(lean_bare)} reference(s) in tracked .lean, '
          f'{len(bare) - len(lean_bare)} elsewhere; '
          f'distinct .lean files: {len({t[0] for t in lean_bare})}')
    for path, lineno, ref in lean_bare:
        # a `/` means it carried SOME prefix, just not `.claude-local/` — the RLY14-2 shape, which
        # was invisible to all three patterns until this run
        shape = 'other-prefix' if '/' in ref else 'bare'
        print(f'      {path.relative_to(REPO)}:{lineno}  [{shape}]  ->  {ref}')
    # ⚠⚠ THIS OUTPUT IS A READING LIST, NOT A FINDING LIST — do not size a burn-down from it.
    # The ratified rule (`vocabulary_reference.md` § 1b, 2026-07-19) splits by FUNCTION, not by
    # destination:
    #   FORBIDDEN   provenance for a public claim — the reader is asked to TRUST an untracked file.
    #   ACCEPTABLE  an internal pointer where the CLAIM IS STATED INLINE; the pointer only adds
    #               background, and removing it costs the reader nothing.
    # A regex sees the path, never the function, so **every `notes/` hit needs a human read**. This
    # classifier splits by DESTINATION because that is all it can see — which is the weaker axis.
    # Caught 2026-08-13 by an editorial gate that declined to report a site of the acceptable kind
    # and cited § 1b; it also recorded the dated corpus figure of 43 tracked `.lean` files carrying
    # such a citation. Labelling all of them "the real item" would have manufactured a burn-down
    # against sites that are correct as written.
    print('\n  ⚠ READING LIST, NOT A FINDING LIST. `vocabulary_reference.md` § 1b splits these by')
    print('    FUNCTION, which no regex can see: provenance-for-a-claim is FORBIDDEN, an internal')
    print('    pointer whose claim is STATED INLINE is ACCEPTABLE. Read each before counting it debt.')
    print('  INFORMATIONAL: does not fail the run. Fold into the header burn-down, as-touched.')


def report(label, dangling, bare, checked):
    print(f'\n== {label} ==')
    print(f'checked {checked} repo-relative reference(s)')
    if dangling:
        print(f'DANGLING ({len(dangling)}):')
        for path, lineno, ref in dangling:
            print(f'  {path}:{lineno}  ->  {ref}')
    else:
        print('all repo-relative references resolve')
    if bare:
        print(f'\nBARE PRE-REORG BASENAMES ({len(bare)}) — cite the full path instead:')
        for path, lineno, ref, actual in bare:
            where = f'now {actual}' if actual else 'NO SUCH FILE ANYWHERE'
            print(f'  {path}:{lineno}  ->  {ref}   ({where})')


def selftest():
    """MUST-FIRE and MUST-SUPPRESS controls on the reference detector.

    Added 2026-08-15 for the Phase 1 exit ("each with both control types"), which this checker had
    never met. Everything below runs against planted strings and the REAL filesystem, so it writes
    nothing into the repo.

    ⚠ The SKIP_MARKERS control is the one with teeth. This checker deliberately ignores a path in a
    sentence that says the path is dead ("no longer exists", "moved to", "renamed"), because a
    historical record naming an old location is not a broken link. That exemption is also the
    obvious way to silence a real finding by accident, so both halves are pinned here: a marker
    suppresses, and a bare dangling path does not."""
    bad = 0

    def fires(text):
        return bool(PATTERN.search(text))

    print('  MUST FIRE')
    cases = [
        ('a repo-relative .lean path', 'see ZeroParadox/Order/Snap.lean for the theorem'),
        ('a scripts/ path', 'built by scripts/build_zpa.py'),
        ('a workflow path', 'defined in .github/workflows/verify.yml'),
    ]
    for label, text in cases:
        ok = fires(text)
        bad += 0 if ok else 1
        print('    %-32s %s' % (label, 'ok' if ok else '*** MISSED ***'))

    # A path that does NOT resolve must be reported by the resolver, not merely matched.
    ghost = 'ZeroParadox/Order/NoSuchFile.lean'
    ok = not (REPO / ghost).exists() and fires('see %s' % ghost)
    bad += 0 if ok else 1
    print('    %-32s %s' % ('a dangling path is detectable', 'ok' if ok else '*** WRONG ***'))

    print('  MUST SUPPRESS')
    # A real file must resolve.
    real = 'ZeroParadox/Order/Snap.lean'
    ok = (REPO / real).exists()
    bad += 0 if ok else 1
    print('    %-32s %s' % ('a real path resolves', 'ok' if ok else '*** WRONG ***'))

    for label, text in (
        ('prose with no path at all', 'the bottom is the diagonal fixed point'),
        ('a bare identifier', 'see t_snap_derived for the statement'),
        ('a Mathlib path (own class)', 'Mathlib/Order/RelClasses.lean:225'),
    ):
        ok = not fires(text)
        bad += 0 if ok else 1
        print('    %-32s %s' % (label, 'ok' if ok else '*** FALSE POSITIVE ***'))

    # SKIP_MARKERS: a dead path in a sentence that SAYS it is dead must be tolerated.
    marked = 'ZeroParadox/ZZTestOrd.lean no longer exists'
    has_marker = any(m in marked.lower() for m in SKIP_MARKERS)
    bad += 0 if has_marker else 1
    print('    %-32s %s' % ('a "no longer exists" marker', 'ok' if has_marker else '*** WRONG ***'))
    unmarked = 'see ZeroParadox/ZZTestOrd.lean for the probe'
    no_marker = not any(m in unmarked.lower() for m in SKIP_MARKERS)
    bad += 0 if no_marker else 1
    print('    %-32s %s' % ('...but a bare mention is NOT', 'ok' if no_marker else '*** OVER-WIDE ***'))

    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and the compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    # ⚠ THE SCOPE PIN (PAT-2). This checker BLOCKS at push and walks privately, and had no
    # scope section at all: its controls run in memory and never touch its enumerator, so
    # nothing exercised what it covers. Verified rather than inferred by /rely round 4.
    print('  SCOPE')
    bad += common.check_scope('check_paths',
                              [str(p.relative_to(REPO)).replace('\\', '/')
                               for p in list(tracked_markdown()) + list(tracked_lean())])
    print('  PATTERNS')
    bad += common.check_vocabulary('check_paths', globals())
    print('\n  selftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


# ⚠ EXIT 3 MEANS 'PASSED WHAT I COULD RUN, AND SKIPPED PART OF MY SCOPE'.
#
# This checker skips Mathlib citations when `.lake/packages/` is absent, which is always the
# case in CI. It said so honestly in its own output — and `ci_report.py` reads the EXIT CODE
# and discards stdout, so the published summary said `pass` while 0 of 63 citations had been
# verified. Measured by both gates independently; /rely planted two genuinely dangling
# citations in a tracked .lean file and got exit 0 with `**all checks pass**`.
#
# The honesty has to live in the exit code, because that is the only channel the reporter
# consumes — and it must NOT be parsed out of the text, which is the fail-open the buildout
# records three times. Callers that only care about pass/fail treat 3 as success.
EXIT_SKIPPED = 3


def main():
    # ⚠ LOCAL, initialised HERE. The first version declared this at module level and assigned to
    # it inside `main`, which makes it a LOCAL by Python's scoping rule — so reading it raised
    # UnboundLocalError on exactly the path where the skip does NOT happen, i.e. wherever Mathlib
    # IS present. It worked in the clean worktree and crashed locally: a bug visible only in the
    # environment the change was not aimed at.
    skipped_a_class = False
    args = sys.argv[1:]
    if '--selftest' in args:
        print('== file-reference resolver - CONTROLS ==')
        return selftest()
    do_all = '--all' in args
    warn_private = '--warn-private' in args

    warn_lean = '--warn-lean' in args

    tracked_live, tracked_rec = split_live_records(tracked_markdown())

    d1, b1, c1 = scan(tracked_live, find_bare=True)
    report('tracked markdown (live)', d1, b1, c1)
    failed = bool(d1)

    # === Lean sources ========================================================================
    # Added 2026-08-01. Why: the resolver covered tracked MARKDOWN only, so eight dead
    # `ZPJ_WheelFrac.lean` citations sat inside ZeroParadox/Algebra/Wheel.lean while every push
    # gate reported "all repo-relative references resolve". Dead citations in Lean docstrings
    # fail exactly as silently as in markdown, and there are far more of them.
    dl, bl, cl, ml, cm = scan(tracked_lean(), find_bare=True, lean_mode=True, check_mathlib=True)
    report('tracked Lean sources (live)', dl, bl, cl)
    if not MATHLIB_PRESENT:
        skipped_a_class = True
        print('  (Mathlib/Std citations NOT CHECKED — no pinned checkout at .lake/packages/.')
        print('   That is a build artifact: absent in a fresh clone, a worktree, and CI.')
        print('   A SKIP, not a pass — these citations were not verified here.)')
    elif ml:
        print(f'\nDANGLING MATHLIB/STD CITATIONS ({len(ml)} of {cm} checked) — '
              f'not in the pinned checkout:')
        for path, lineno, ref in ml:
            print(f'  {path}:{lineno}  ->  {ref}')
    else:
        print(f'  (+ {cm} Mathlib/Std citation(s) checked against the pinned checkout, all resolve)')
    # A bare basename that resolves NOWHERE is a genuinely dead citation, not a style nit — it is
    # the silent-failure class the convention exists to stop, so it FAILS. A bare basename that
    # does resolve is merely un-converted style and stays a warning.
    lean_dead_bare = [b for b in bl if b[3] is None]
    if lean_dead_bare:
        print(f'\n** {len(lean_dead_bare)} of those resolve NOWHERE — dead citations, not style. **')
    if (dl or ml or lean_dead_bare) and not warn_lean:
        failed = True

    # PATH-3 population, both polarities. Tracked Lean + tracked markdown, informational only.
    pq, pb = scan_private_deps(tracked_lean() + tracked_live + tracked_rec)
    report_private_deps(pq, pb)

    dr, br, cr = scan(tracked_rec, find_bare=False)
    if dr:
        report('tracked markdown (DATED RECORDS - informational, do not "fix")', dr, [], cr)

    if do_all:
        priv_live, priv_rec = split_live_records(private_markdown())

        d2, b2, c2 = scan(priv_live, find_bare=True)
        report('private LIVE rules (memory + undated notes) - these must resolve', d2, b2, c2)
        if d2 and not warn_private:
            failed = True

        d3, _, c3 = scan(priv_rec, find_bare=False)
        print(f'\n== private DATED RECORDS ==')
        print(f'checked {c3} reference(s); {len(d3)} dangling')
        print('  NOT a defect: dated review verdicts and session notes cite the tree as it stood')
        print('  at the time. Rewriting them would falsify the record. Informational only.')

    print()
    if UNREADABLE:
        print('\n%d file(s) could not be decoded and were NOT scanned — failing closed:' %
              len(UNREADABLE))
        for p in UNREADABLE:
            print('  %s' % p)
        failed = True
    if failed:
        return 1
    return EXIT_SKIPPED if skipped_a_class else 0


if __name__ == '__main__':
    sys.exit(main())
