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


# === RIDE-ALONG CROSS-REFERENCES (2026-08-17) ================================================
# The ride-along convention moves a module-level ESSAY out of `Foo.lean` into `Foo.md` beside it.
# The declarations stay; the argument, prior art and fences move.
#
# ⚠⚠ THE FAILURE THIS CATCHES IS INVISIBLE TO EVERY OTHER CHECK IN THIS FILE, BECAUSE THE PATH
# STILL RESOLVES. `Foo.lean` exists, so the resolver is happy; what moved is the TARGET INSIDE it.
# A reference reading "`Wall.lean`'s NO-GO table" or "`Wall.lean:74-75` says 'Now adopted'" now
# points at a file that no longer contains either. Measured on the FIRST conversion, 2026-08-17:
# one file produced 13+ live tracked breaks, none of which any gate reported.
#
# Two shapes, and both are the project's own recorded defect classes arriving here:
#   * a LINE NUMBER into a `.lean` that has a ride-along — a line number is a copy of a location
#     and drifts (the `COM-4` rule), and relocation is the extreme case of that drift;
#   * a PROSE NOUN attached to the `.lean` — table, section, paragraph, citation, fence — naming
#     content that by construction is now next door.
#
# ⚠ A DECLARATION citation is NOT a hit and must never become one: `wf_no_selfloop` really does
# live in the `.lean`, and firing on those would be the cry-wolf shape that gets a gate muted.
# ⚠ THE CLOSING DELIMITER IS PART OF THE GAP AND THE FIRST DRAFT MISSED IT. References are written
# `` `Settheory/Wall.lean`'s reframe paragraph `` — a BACKTICK sits between the name and the `'s`,
# so an anchored match on `'s` returned a clean ZERO against 13 known-live breaks. Allow the
# closing delimiter. (Verified the detector against a known-bad line rather than believing the zero.)
PROSE_NOUN = re.compile(
    r"[`'\"\)\]]*\s*(?:'s|’s|s')\s+"
    r"(?:[A-Za-z][\w-]*\s+){0,3}"      # intervening modifiers: "failure-mode taxonomy", "one-root reframe"
    r"(paragraph|section|§|table|note|docstring|header|reframe|taxonomy|fence|fenced|"
    r"citation|cites|cited|overview|gloss|discussion|argument|prior art|hypothesis|"
    r"classification|module doc)",
    re.I)
# The same reference also appears as "cited in `Wall.lean`" / "fenced conjecture of `Wall.lean`",
# where the prose noun PRECEDES the name. One-sided matching is a blind half (the Two-Pole rule
# applied to a detector), so look behind as well as ahead.
# ⚠ THE LEADING `\b` IS LOad-BEARING AND WAS MISSING. Without it the `note` alternative matched the
# TAIL of an identifier: `SynONote` — a `def` that never left its `.lean` — reported as a pointer at
# relocated prose. Found 2026-08-17 by the SECOND conversion, i.e. by using the rule rather than by
# reading it, which is the only way a word-boundary bug of this shape surfaces.
PROSE_NOUN_BEFORE = re.compile(
    r"\b(cited|cites|citation|fenced|fence|table|taxonomy|paragraph|section|reframe|note|"
    r"docstring|gloss|argument|hypothesis|discussion|overview)\b[^`]{0,40}$",
    re.I)
# ⚠ THE THIRD BLIND FORM: THE APPOSITIVE — a prose noun after the name with NO possessive, as in
# "`Wall.lean` - a failure-mode taxonomy" or "`Wall.lean` § V". Found 2026-08-17 by a `/rely` pass
# told to assume a third form existed, after two had already been found and fixed.
#
# ⚠⚠ IT IS STILL BLIND, AND THIS SECTION CLAIMED OTHERWISE FOR ONE COMMIT. Only the SECTION-MARKER
# subcase below is detected. The general appositive is NOT, and a second `/rely` pass constructed
# seven stale references that all walk past: a paraphrased appositive, an em-dash appositive, an
# inflected noun (`taxonomies` vs `taxonomy`), a noun outside the vocabulary (`roster`), and a
# possessive beyond the modifier cap. **A hole described as closed is worse than one described as
# open**, and that is the same defect this file's own limits paragraph exists to prevent — made
# twice in one day, in the paragraph documenting it.
#
# The `MANIFEST.md` case that motivated it is handled UPSTREAM instead, by
# `scan_title_duplication` below: the manifest is GENERATED from the `.lean` H1, so keeping that
# title about the declarations keeps every generated row correct at the source.
# ⚠ TWO SHAPES, AND THE FIRST DRAFT GUESSED GRAMMAR AND MISSED BOTH CONTROLS. An appositive puts
# arbitrary prose between the name and the noun ("`Wall.lean` - Zero as a Wall, a failure-mode
# taxonomy"), so no fixed-width regex catches it without firing on everything. Derive it from
# CONTENT instead of sentence shape:
#   (a) a section marker after the name — the section is in the `.md` now;
#   (b) the line repeats the ride-along's OWN TITLE while citing the `.lean`, which is exactly
#       what a `MANIFEST.md` row does after a conversion.
# (b) is the robust one precisely because it compares against the artifact rather than guessing.
SECTION_AFTER = re.compile(r"^[`'\"\)\]]*\s*(?:§|section\b|\bch(?:apter)?\b)\s*[IVXLC0-9]", re.I)
_STOP = {'the', 'a', 'an', 'of', 'as', 'and', 'to', 'in', 'is', 'for', 'on', 'at', 'by', 'it',
         'its', 'that', 'this', 'with', 'from', 'formal', 'object'}


def _title_words(md_path):
    """Distinctive words of a ride-along's H1 — the phrase a stale index row will repeat."""
    try:
        for line in md_path.read_text(encoding='utf-8', errors='replace').split('\n'):
            if line.startswith('# '):
                ws = re.findall(r"[A-Za-z][\w-]{2,}", line[2:].lower())
                return {w for w in ws if w not in _STOP}
    except OSError:
        pass
    return set()
LINE_REF = re.compile(r'\.lean:\d+')


# === LINE-NUMBER CITATIONS (Tim, 2026-08-17) =================================================
# "line numbers for comments on other files need to go. the block/ paragraph"
#
# A line number is a COPY OF A LOCATION and drifts exactly like any other copy — the failure this
# project has paid for repeatedly (`COM-4`: `common.py` cited `check_modal.py:302` when the record
# had moved to `:230`, moved by the very edit that made the citation). Relocation is the extreme
# case, and the ride-along conversion demonstrated it at full scale in a single commit.
#
# THE STABLE ANCHOR IS A NAME, NOT A NUMBER: a declaration (globally unique, self-locating,
# `#check`-able) or a section heading. Both survive edits above them; a line number does not.
#
# ⚠ REPORTED, NOT BLOCKING, and deliberately so. There are ~100 pre-existing sites; a gate that
# blocks everything on day one gets bypassed and then ignored, which this project has recorded.
# The count is printed so a RISING number is visible — the same bargain as the measurement-gap
# line in `check_prose`. It should become blocking, with a baseline, once the burn-down starts.
LINE_CITATION = re.compile(
    r'(?<![\w/.-])([A-Za-z0-9_./-]+\.(?:lean|py|md))[:∶](\d+)(?:\s*[-–]\s*\d+)?')


def scan_line_citations(files):
    """File references carrying a line number, in tracked prose."""
    hits = []
    for path in files:
        try:
            text = path.read_text(encoding='utf-8', errors='replace')
        except OSError:
            continue
        rel = str(path.relative_to(REPO)).replace('\\', '/')
        if DATED.search(rel.rsplit('/', 1)[-1]):
            continue                    # a dated record describes the tree as it stood
        for lineno, line in enumerate(text.split('\n'), 1):
            # A checker printing its OWN findings emits `file:line` as tool output, not as prose.
            if 'print(' in line or "print (" in line or line.lstrip().startswith(('>>>', '$')):
                continue
            for m in LINE_CITATION.finditer(line):
                hits.append((rel, lineno, m.group(0)))
    return hits


def ride_along_pairs():
    """`Foo.lean` files that have a `Foo.md` beside them."""
    out = {}
    for p in (REPO / 'ZeroParadox').rglob('*.md'):
        lean = p.with_suffix('.lean')
        if lean.exists():
            out[lean.name] = str(p.relative_to(REPO)).replace('\\', '/')
    return out


def scan_ride_along(files, pairs):
    """References to a ride-along `.lean` that actually target its RELOCATED PROSE."""
    hits = []
    if not pairs:
        return hits
    for _n, md in pairs.items():
        _titles.setdefault(md, _title_words(REPO / md))
    # ⚠ NO `/` IN THE LOOKBEHIND. The convention REQUIRES the full repo path, so almost every real
    # citation reads `ZeroParadox/Settheory/Wall.lean` — and excluding a preceding `/` made the
    # detector blind to exactly the form the project mandates. It returned 0 against 13 known breaks.
    names = re.compile(r'(?<![\w.-])(' + '|'.join(re.escape(n) for n in pairs) + r')')
    for path in files:
        try:
            text = path.read_text(encoding='utf-8', errors='replace')
        except OSError:
            continue
        rel = str(path.relative_to(REPO)).replace('\\', '/')
        for lineno, line in enumerate(text.split('\n'), 1):
            # ⚠ BLANK THE DELIMITERS, LENGTH-PRESERVING, so offsets stay exact. Every real citation
            # is written `` `Foo.lean` ``, so the backtick sits between the name and the prose noun
            # on BOTH sides — matching the raw line found 5 of 13 known breaks. Same fix, same
            # reason, as `common.normalize_separators`; the bug it prevents is the one this
            # project keeps paying for, a detector blind to the form the convention mandates.
            for why in _ride_along_line_hits(line, pairs):
                name = next(n for n in pairs if n in line)
                hits.append((rel, lineno, name, pairs[name], why))
    return hits


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


def selftest_ride_along():
    """Controls for the ride-along cross-reference rule.

    ⚠ WRITTEN AFTER THE DETECTOR RETURNED A FALSE ZERO TWICE, which is why they are in the shapes
    the corpus actually uses rather than the shapes that were convenient to invent. First draft:
    the lookbehind excluded a preceding `/`, so it could not see `ZeroParadox/Settheory/Wall.lean`
    — the very form the file-reference convention MANDATES. Second: the closing backtick sits
    between the name and the prose noun, so an anchored match found 5 of 13 known-live breaks.
    Both were caught by checking a known-bad line instead of believing the zero.

    ⚠ DECLARED LIMITS — TWO, not one, and the second was mis-stated as CLOSED for one commit:

    1. A reference whose prose noun WRAPS to the next line is not caught — this scans line by line.
       One such site exists today (`WheelFrac.lean`). Same root cause as `check_pov`'s wrap gap.
    2. The general APPOSITIVE is not caught — a prose noun after the name with no possessive and no
       section marker. Only the section-marker subcase fires. A `/rely` pass constructed seven stale
       references that walk past: paraphrased and em-dash appositives, an inflected noun
       (`taxonomies` vs `taxonomy`), a noun outside the vocabulary (`roster`), and a possessive
       beyond the modifier cap. Three are pinned as MUST-MISS controls below, so the gap is a listed
       fact — and widening the rule without updating that list fails loudly.

    ⚠ Limit 2 was briefly claimed CLOSED here by a title-overlap heuristic, which was then measured
    to have ZERO live yield and a false-positive surface that GREW with every conversion. It was
    removed; `scan_title_duplication` handles the case that motivated it, upstream and precisely.
    **A hole described as closed is worse than one described as open** — and getting that wrong in
    the paragraph whose whole job is honest limits is exactly what this paragraph exists to stop."""
    pairs = {'Wall.lean': 'ZeroParadox/Settheory/Wall.md'}
    _titles.setdefault(pairs['Wall.lean'], _title_words(REPO / pairs['Wall.lean']))
    must_fire = [
        ("full path + closing backtick, the mandated form",
         "the wall/floor carving; and `ZeroParadox/Settheory/Wall.lean`'s reframe paragraph."),
        ("intervening modifier", "`Wall.lean`'s failure-mode taxonomy singles out the row"),
        ("prose noun BEFORE the name", "the diagonal framing is Lawvere (cited in `Wall.lean`)."),
        ("line number into relocated prose", "recorded at `ZeroParadox/Settheory/Wall.lean:67`."),
        ("appositive with a section marker", "see `Wall.lean` § V for the carving."),
    ]
    # ⚠ MUST-MISS, RECORDED AS SUCH. These are stale references the rule does NOT catch. They are
    # here so the gap is a listed fact rather than a discovery: a control that asserts a known
    # blind form stays blind is the honest way to keep it visible, and it fails loudly the day
    # someone widens the rule without updating this list.
    must_miss = [
        ("general appositive (no possessive, no section marker)",
         "- `ZeroParadox/Settheory/Wall.lean` - Zero as a Wall, a failure-mode taxonomy"),
        ("em-dash appositive", "`Wall.lean` — the failure-mode taxonomy — lists the rows."),
        ("inflected noun", "the `Wall.lean` taxonomies cover each condition-set."),
    ]
    must_suppress = [
        ("a DECLARATION citation — the prose moved, the theorem did not",
         "`wf_no_selfloop` (`ZeroParadox/Settheory/Wall.lean`) is axiom-free."),
        ("a bare file pointer with no prose noun",
         "See `ZeroParadox/Settheory/Wall.lean` for the engine."),
        ("an unrelated file", "`ZeroParadox/Order/Snap.lean`'s NO-GO gauge section."),
        # ⚠ IN THE LIVE SHAPE that produced the false positive, not an invented one: an identifier
        # ending in a vocabulary word, beside a citation of a ride-along `.lean`. `SynONote` is a
        # `def` that never moved.
        ("identifier ending in a vocabulary word (SynONote / 'note')",
         "The `SynONote` bridge is defined in `ZeroParadox/Settheory/Wall.lean` for the carrier."),
    ]
    import tempfile
    bad = 0
    tmp = Path(tempfile.mkdtemp())
    print('\n== ride-along cross-references - CONTROLS ==')
    for label, group, want in (('MUST FIRE', must_fire, True),
                               ('MUST SUPPRESS', must_suppress, False),
                               ('MUST MISS (known blind forms, kept visible)', must_miss, False)):
        print(f'{label}')
        for why, line in group:
            f = tmp / 'Probe.md'
            f.write_text(line, encoding='utf-8')
            # scan_ride_along resolves paths against REPO; probe via the pure matchers instead by
            # pointing it at a file inside the repo tree is not possible read-only, so call the
            # matcher on the constructed line directly through a shim file in the repo-relative tmp.
            got = bool(_ride_along_line_hits(line, pairs))
            ok = (got == want)
            bad += 0 if ok else 1
            print('  %-52s %s' % (why[:52], 'ok' if ok else ('MISSED' if want else 'FALSE POSITIVE')))
    return bad


def _ride_along_line_hits(line, pairs):
    """The per-line decision, EXTRACTED so the controls exercise the real path rather than a copy.

    A replica drifts from the thing it certifies — the mirror problem this project keeps paying for.
    `scan_ride_along` calls this, so the controls test what actually runs."""
    names = re.compile(r'(?<![\w.-])(' + '|'.join(re.escape(n) for n in pairs) + r')')
    out = []
    soft = line.replace('`', ' ')
    for m in names.finditer(line):
        tail = soft[m.end():m.end() + 90]
        before = soft[:m.start()]
        if LINE_REF.search(line[m.start():m.end() + 8]):
            out.append('line number into relocated prose')
        elif PROSE_NOUN.match(tail):
            out.append('names prose that moved: ' + PROSE_NOUN.match(tail).group(1))
        elif PROSE_NOUN_BEFORE.search(before):
            out.append('names prose that moved: ' + PROSE_NOUN_BEFORE.search(before).group(1))
        elif SECTION_AFTER.match(tail):
            out.append('names a SECTION that moved to the ride-along')
    return out
# ⚠⚠ A TITLE-OVERLAP HEURISTIC LIVED HERE FOR ONE COMMIT AND WAS REMOVED. Recorded because the
# measurement is the useful part, not the code. It flagged a line sharing >=3 distinctive words with
# the ride-along's H1 while citing the `.lean`, aimed at the `MANIFEST.md` row shape.
#
#   * LIVE YIELD: ZERO. The only corpus line meeting the threshold already fired on `PROSE_NOUN`.
#   * The threshold was nominally 3 and effectively 2 — a ride-along is named after its `.lean`, so
#     the subject noun sits in the title AND in every citation path. One word is always free.
#   * FALSE POSITIVES GREW WITH EVERY CONVERSION, which is fatal for a convention meant to scale.
#     Measured: retitling `Wall.md`'s H1 took the run 9 -> 19 hits, 10 on real corpus lines nobody
#     wrote for the test — including a BARE DECLARATION CITATION, the canonical must-suppress class,
#     plus `BOTTOMELEMENT.md` x4, `CLAIMS.md`, `register.md`, and `MANIFEST.md` *while correct*.
#     Simulating the next conversion (`Snap.lean`) fired on `register.md` and `CLAIMS.md` because the
#     shared words are the name of a PDF; simulating `DiagonalFixedPoint.lean` fired on a
#     gate-exempt file; and the ride-along fired on ITSELF.
#   * A gate that cries wolf gets muted, and a muted gate protects nothing.
#
# WHAT REPLACED IT is below and is precise: compare the PAIR'S OWN TWO TITLES to each other. That is
# two strings this project controls, not arbitrary corpus prose, so it has no false-positive surface
# — and it catches the ROOT CAUSE (a `.lean` whose title describes the essay rather than its own
# declarations) instead of the symptom (index rows echoing that title).


def scan_title_duplication(pairs):
    """A ride-along's `.md` title must not duplicate its `.lean` title.

    The `.lean` says what the FILE PROVES; the `.md` says what the ARGUMENT is. When both carry the
    essay's title, every generated index row describes the `.lean` using words that now belong to
    the `.md` — which is how `MANIFEST.md` (template `path - description`) went stale on the first
    conversion, one row per conversion thereafter."""
    out = []
    for lean_name, md_rel in sorted(pairs.items()):
        md_words = _title_words(REPO / md_rel)
        lean_rel = md_rel[:-3] + '.lean'
        lean_words = _title_words_lean(REPO / lean_rel)
        if not md_words or not lean_words:
            continue
        shared = md_words & lean_words
        if len(shared) >= 3:
            out.append((lean_rel, md_rel, sorted(shared)))
    return out


def _title_words_lean(path):
    """Distinctive words of a `.lean` module docstring's H1."""
    try:
        for line in path.read_text(encoding='utf-8', errors='replace').split('\n'):
            if line.startswith('# '):
                ws = re.findall(r"[A-Za-z][\w-]{2,}", line[2:].lower())
                return {w for w in ws if w not in _STOP}
    except OSError:
        pass
    return set()


# Title words per ride-along, computed once. Populated by `scan_ride_along`.
_titles = {}


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
        return selftest() + selftest_ride_along()
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
    # === Line-number citations ===============================================================
    lc = scan_line_citations(tracked_markdown() + tracked_lean())
    by_file = {}
    for rel, _ln, ref in lc:
        by_file[rel] = by_file.get(rel, 0) + 1
    print(f'\n== line-number citations into other files ({len(lc)} in {len(by_file)} file(s)) ==')
    print('  A line number is a COPY OF A LOCATION and drifts. Cite the DECLARATION (unique,')
    print('  self-locating, #check-able) or the section heading — the block, not the number.')
    if by_file:
        for rel, n in sorted(by_file.items(), key=lambda kv: -kv[1])[:8]:
            print(f'      {n:4d}  {rel}')
        if len(by_file) > 8:
            print(f'      ... and {len(by_file) - 8} more file(s)')
    print('  INFORMATIONAL: does not fail the run. A RISING number means the class is growing.')

    # === Ride-along cross-references =========================================================
    pairs = ride_along_pairs()
    if pairs:
        # ⚠ BUILD SCRIPTS ARE IN SCOPE, AND LEAVING THEM OUT WAS A FAIL-OPEN. Measured 2026-08-17
        # by a `/rely` plant: the SAME sentence was reported in `Tarski.lean` and silent in
        # `scripts/build_zpr_addendum.py`, because this set was `{.md, .lean}` only. So a stale
        # pointer in a Lean docstring blocked a push while the identical one in a build script —
        # the surface a Zenodo DOI freezes PERMANENTLY — went through. That is the wrong way round.
        build_scripts = sorted((REPO / 'scripts').glob('build_*.py'))
        ra = scan_ride_along(tracked_live + tracked_rec + tracked_lean() + build_scripts, pairs)
        # Dated records describe the tree as it stood then; "fixing" them would falsify the record.
        ra = [h for h in ra if not DATED.search(h[0].rsplit('/', 1)[-1])]
        print(f'\n== ride-along cross-references ({len(pairs)} pair(s)) ==')
        for name, md in sorted(pairs.items()):
            print(f'  {name}  ->  {md}')
        dup = scan_title_duplication(pairs)
        if dup:
            print('\n** TITLE DUPLICATION — the .lean and its ride-along carry the same title: **')
            for lean_rel, md_rel, shared in dup:
                print(f'  {lean_rel}\n      and {md_rel}\n      share: {", ".join(shared[:6])}')
            print('  The .lean title says what the FILE PROVES; the .md title says what the ARGUMENT')
            print('  is. MANIFEST.md is GENERATED from the .lean H1, so a .lean titled after the')
            print('  essay makes every generated index row describe it with words that moved out.')
            failed = True
        if ra:
            print(f'\n** {len(ra)} REFERENCE(S) POINT AT PROSE, NOT AT CODE — the path still '
                  f'resolves, the target no longer lives there: **')
            for rel, lineno, name, md, why in ra:
                print(f'  {rel}:{lineno}  cites {name} but {why}')
            # ⚠⚠ THE REMEDY IS *NOT* "RETARGET IT AT THE .md", AND SAYING SO WAS THIS RULE'S OWN
            # FIRST DEFECT (Tim, 2026-08-17: "I don't think we should ever have prose blocks that
            # point at each other. that sounds exactly the opposite of how the damn things are
            # supposed to work"). Repointing prose at prose one directory over just relocates the
            # coupling — it is the mirror problem this project has already paid for three times,
            # and a paragraph is not a stable target the way a declaration is.
            #
            # PROSE HANGS OFF CODE. A `.lean` pairs with its OWN `.md`, one structural hop, and
            # everything else cites a DECLARATION (globally unique, self-locating via
            # `#print axioms`) or states the one line it needs inline. That is `CLAUDE.md`'s
            # existing rule — "keep declaration names bare" — and its one-line-plus-pointer rule,
            # where the canonical home of a MATHEMATICAL fact is a theorem, never a paragraph.
            print('\n  FIX BY DE-REFERENCING, NOT BY REPOINTING:')
            print('    * naming a source ("cited in X") -> cite the SOURCE itself; a pointer at a')
            print('      file that quotes Lawvere 1969 is strictly worse than citing Lawvere 1969')
            print('    * naming an argument ("X\'s taxonomy/table/fence") -> name the DECLARATION it')
            print('      turns on, or state the one line this site needs and stop')
            print('    * a line number -> delete it; a line number is a copy of a location')
            print('  Repointing at the .md is NOT a fix — it keeps prose pointing at prose.')
            failed = True
        else:
            print('  all references to ride-along .lean files target declarations, not moved prose')

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
