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

Exit 0 = no dangling reference in a failing scope. Exit 1 = at least one.
Exit 3 (EXIT_SKIPPED) = the scope could not be determined.
⚠ EXIT 0 IS NOT "CLEAN". Several classes here are INFORMATIONAL and do not affect the code:
the ride-along cross-reference rule, the private-layer dependency list, and the line-citation
reading list. A caller that reads only the exit status sees none of them - and CI does exactly
that, discarding stdout, so those findings reach the push terminal only.
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


# ⭐⭐ THE DIVIDING LINE (Tim, 2026-08-17): "keep the mechanical as basic as getting a line count so
# we know where the dividing line is."
#
# **THE MECHANICAL LAYER MEASURES AND LOCATES. AGENTS JUDGE.** A checker's job is to answer WHERE and
# HOW MANY — cheaply, on every run, without anyone remembering. Deciding whether a claim is TRUE is
# not a checker's job and every attempt here to make it one has produced its own defect:
#
#   * `check_pov` is a tag-PRESENCE test read as a truth test — a `/rely` plant plus one honest tag
#     two lines away certified the retracted arrow verbatim, and the tagged-claims counter ROSE.
#   * `check_prose`'s block metric counts blank lines and delimiters, so 29 of the 47 smallest sites
#     come under cap by deleting whitespace — zero liability removed (`PRS-10`).
#   * A title-overlap heuristic added here to judge relevance had ZERO live yield and a
#     false-positive surface that grew with every conversion. Deleted the same day.
#
# Measured across this session: **every BEDROCK finding came from an AGENT executing something —
# `#check`, `lake env lean`, a planted defect. None came from a checker firing.** What the checkers
# did contribute was the thing agents cannot: enumeration that fires every time and forgets nothing
# (83 line-citations, 293 over-cap blocks, which checker hashes moved since `/rely` signed them).
#
# SO: report the count, name the sites, and STOP. Where this file blocks, it blocks on facts that are
# decidable without judgement — does a path resolve, is a hash current. Everything interpretive here
# is INFORMATIONAL by design, not by timidity.
#
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
SECTION_AFTER = re.compile(
    r"^[`'\"\)\]]*\s*(?:§|section\b|\bch(?:apter)?\b)\s*([IVXLC0-9][IVXLC0-9a-z-]*)", re.I)
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
# ⚠ REPORTED, NOT BLOCKING, and deliberately so. The checker measures the live count on every
# run — do not quote one here, it goes stale the first time anyone acts on it. A gate that
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
        _owner[_n] = md[:-3] + '.lean'
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
        # ⚠ A RIDE-ALONG NAMING ITS OWN `.lean` IS THE REQUIRED CROSS-REFERENCE, NOT A DEFECT.
        # The convention's whole point is that the pair name each other; firing on the `.md`'s
        # opening line would make every correctly-written ride-along a finding, and the rule would
        # be self-defeating. Suppress the SELF pair ONLY — a ride-along citing a DIFFERENT file's
        # relocated prose is still a hit, which is how `Wall.md` was caught.
        for lineno, line in enumerate(text.split('\n'), 1):
            # ⚠ BLANK THE DELIMITERS, LENGTH-PRESERVING, so offsets stay exact. Every real citation
            # is written `` `Foo.lean` ``, so the backtick sits between the name and the prose noun
            # on BOTH sides — matching the raw line found 5 of 13 known breaks. Same fix, same
            # reason, as `common.normalize_separators`; the bug it prevents is the one this
            # project keeps paying for, a detector blind to the form the convention mandates.
            # ⚠ THE NAME COMES FROM THE MATCH. This used to re-derive it as
            # `next(n for n in pairs if n in line)` - the first basename in dict order - so on a
            # line naming its own partner AND another ride-along, the self-pair test was applied
            # to the wrong name and the other file's hit was silently dropped. Measured: the
            # identical stale sentence reported 1 hit alone and 0 hits beside its own partner,
            # which is precisely what the convention requires a ride-along to write.
            for name, why in _ride_along_line_hits(line, pairs):
                if pairs[name] == rel:
                    continue
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
    # Two ride-alongs on purpose: `Wall.lean` kept NO section headings (its whole essay moved), and
    # `Occurrence.lean` kept several while their bodies moved. The section rule must behave
    # differently on the two, and one fixture cannot show that.
    pairs = {'Wall.lean': 'ZeroParadox/Settheory/Wall.md',
             'Occurrence.lean': 'ZeroParadox/Computability/Occurrence.md'}
    for _n, _md in pairs.items():
        _owner[_n] = _md[:-3] + '.lean'
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
    # ⚠ THE SECTION RULE HAS TWO BRANCHES AND ONE CONTROL WOULD PASS ON EITHER. A heading that
    # is STILL in the `.lean` must downgrade; one that LEFT must say it moved. Without both, the
    # `§ III` false positive that prompted the fix would have gone on passing its own control.
    section_branches = [
        ('heading still present in the .lean -> downgraded, not "moved"',
         'See `ZeroParadox/Computability/Occurrence.lean` § III for the obstruction.',
         'heading is still'),
        ('heading absent from the .lean -> reported as moved',
         'See `ZeroParadox/Computability/Occurrence.lean` § XCIX for the obstruction.',
         'moved to the ride-along'),
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
    # \u26a0 THE FILE-LEVEL SELF-PAIR SUPPRESSION HAD NO CONTROL AND WAS BROKEN. It lives in
    # `scan_ride_along`, not in `_ride_along_line_hits`, so every control above passed while the
    # suppression was applied to the WRONG name - dropping a real hit on any line naming its own
    # partner alongside another ride-along, which is what the convention requires a ride-along to
    # do. Found independently by two gates on the same day.
    # \u26a0 THIS GROUP MUST EXERCISE `scan_ride_along`, NOT THE MATCHER. The previous version called
    # `_ride_along_line_hits` - the half that was already correct - so it reported green while the
    # caller silently dropped hits, and --selftest was byte-identical either way. The defect lives
    # in the CALLER; a control that never calls it cannot see it.
    # \u26a0\u26a0 THIS GROUP MUST GO THROUGH `scan_ride_along`, THE CALLER. A previous version was
    # HEADED "through the caller" and called the matcher instead, re-implementing the self-pair
    # filter inline - so it could not see a defect in the caller, which is the only thing it was
    # added to catch. Measured: reinstating that defect left `--selftest` byte-identical, exit 0,
    # every control `ok`. A control named after what it does not do is worse than no control.
    print('SELF-PAIR THROUGH scan_ride_along (the caller, where the drop happened)')
    import tempfile as _tf
    _probe_root = Path(_tf.mkdtemp())
    _md = _probe_root / 'Probe.md'
    _stale = ("Argument for `ZeroParadox/Settheory/Wall.lean`. It restates "
              "`ZeroParadox/Computability/Occurrence.lean`'s taxonomy.")
    try:
        _md.write_text(_stale, encoding='utf-8')
        # scan_ride_along keys the self-pair test on the file being scanned, so scan the probe
        # AS IF it were Wall's ride-along: the Wall hit must drop, the Occurrence hit must not.
        _saved = globals().get('REPO')
        globals()['REPO'] = _probe_root
        _pairs = {'Wall.lean': 'Probe.md',
                  'Occurrence.lean': 'ZeroParadox/Computability/Occurrence.md'}
        for _n, _m in _pairs.items():
            _owner[_n] = _m[:-3] + '.lean'
        _hits = scan_ride_along([_md], _pairs)
        _names = sorted({h[2] for h in _hits})
        globals()['REPO'] = _saved
        for _why, _ok in (('the foreign hit survives the self-pair drop',
                           _names == ['Occurrence.lean']),
                          ('the reason is a plain string, not a tuple',
                           all(isinstance(h[4], str) for h in _hits))):
            bad += 0 if _ok else 1
            print('  %-52s %s' % (_why[:52], 'ok' if _ok else 'BROKEN: %s' % (_hits or 'no hit')))
    finally:
        globals()['REPO'] = _saved
        try:
            _md.unlink()
            _probe_root.rmdir()
        except OSError:
            pass

    print('SELF-PAIR ATTRIBUTION (the name must come from the match, not a re-scan)')
    mixed = ("Argument for `ZeroParadox/Settheory/Wall.lean`, whose reframe paragraph restates "
             "`ZeroParadox/Computability/Occurrence.lean`'s taxonomy.")
    hits = _ride_along_line_hits(mixed, pairs)
    names = {n for n, _w in hits}
    for why, ok in (('both names produce their own hit',
                     names == {'Wall.lean', 'Occurrence.lean'}),
                    ('dropping the SELF pair leaves the foreign one',
                     {n for n, _w in hits
                      if pairs[n] != 'ZeroParadox/Settheory/Wall.md'} == {'Occurrence.lean'})):
        bad += 0 if ok else 1
        print('  %-52s %s' % (why[:52], 'ok' if ok else 'BROKEN: %s' % (hits or 'no hit')))

    # \u26a0 EVERY SPELLING, because the rule was spelling-sensitive AND the marker capture was one
    # character wide - so all four canonicalised to `I`, `\u00a7 IV` "matched" the `\u00a7 I` heading, and the
    # two controls below passed on a test that distinguished nothing.
    print('SECTION SPELLING + WIDTH (heading present -> downgrade; absent -> moved)')
    # \u26a0 `IX` IS THE LOAD-BEARING CASE. `III` and `XCIX` both give the right verdict even with the
    # one-character capture reinstated, so a group built from those two passes green with the bug
    # back in. `\u00a7 IX` against the `\u00a7 I` heading is the discrimination that actually fails.
    spell_cases = [('\u00a7 III', True), ('\u00a7III', True), ('section III', True), ('\u00a7 III.', True),
                   ('\u00a7 IX', False), ('\u00a7 XCIX', False)]
    for spell, want_present in spell_cases:
        line = ('See `ZeroParadox/Computability/Occurrence.lean` %s for the obstruction.' % spell)
        hits = _ride_along_line_hits(line, pairs)
        got_present = any('heading is still' in why for _n, why in hits)
        ok = bool(hits) and got_present == want_present
        bad += 0 if ok else 1
        print('  %-52s %s' % ('%r -> %s' % (spell, 'downgrade' if want_present else 'moved'),
                              'ok' if ok else 'WRONG: %s' % (hits or 'no hit')))
    print('SECTION BRANCH (both, or the rule is untested on one side)')
    for why, line, want_sub in section_branches:
        hits = _ride_along_line_hits(line, pairs)
        ok = any(want_sub in why for _n, why in hits)
        bad += 0 if ok else 1
        print('  %-52s %s' % (why[:52], 'ok' if ok else 'WRONG BRANCH: %s' % (hits or 'no hit')))
    return bad


# Words that can sit before "docstring" while still meaning the MODULE's docstring. Anything
# else in that slot names a declaration, and a declaration docstring never relocates.
_DOC_GENERIC = {"the", "its", "this", "a", "module", "own", "file", "header", "and", "or",
                "that", "whose", "same", "s"}


def _names_a_declaration_docstring(line, lo=0, hi=None):
    """Is the `docstring` on this line a DECLARATION's rather than the module's?

    A DECLARATION DOCSTRING NEVER MOVES under the ride-along convention - only module-doc blocks
    relocate, and a declaration's docstring travels with its declaration. Reporting "`l_inf`'s
    docstring" as prose that moved is false on its face, and it was: measured 2026-08-17 across CLAUDE.md,
    ZeroParadox/README.md, Gentzen.lean and five build scripts, every one naming prose that is
    still exactly where it says it is.

    The discriminator is the QUALIFIER in the slot before the word: a name with no file extension
    owns a declaration docstring; a bare file name, or a generic word, owns the module one.

    BOTH SPELLINGS ARE COVERED ON PURPOSE. The corpus writes it backticked and bare, and a first
    fix that handled only the backticked form left 7 of the 10 standing - a probe written in a
    shape the corpus does not actually use.
    """
    window = line[lo:hi if hi is not None else len(line)]
    for m in re.finditer(r"([`\w.'/\\-]+)\s+docstring", window, re.I):
        tok = m.group(1).strip("`'\u2019")
        if not tok or tok.lower() in _DOC_GENERIC:
            continue
        if re.search(r"\.(lean|md|py)$", tok, re.I):
            continue                                    # the FILE's docstring - it can move
        if re.match(r"^[A-Za-z_][\w.']*$", tok):
            return True                                 # a declaration name
    return False


def _trim_punct(s):
    """Strip the delimiters a citation is wrapped in, leaving the bare section marker."""
    return s.strip(" 	`)]" + chr(39) + chr(34))


def pairs_owner(basename):
    """Repo-relative `.lean` path for a matched ride-along basename, or None."""
    return _owner.get(basename)


_owner = {}


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
            out.append((m.group(1), 'line number into relocated prose'))
        elif PROSE_NOUN.match(tail) and not (
                PROSE_NOUN.match(tail).group(1).lower() == 'docstring'
                and _names_a_declaration_docstring(soft, m.end(), m.end() + 90)):
            out.append((m.group(1), 'names prose that moved: '
                        + PROSE_NOUN.match(tail).group(1)))
        elif PROSE_NOUN_BEFORE.search(before) and not (
                PROSE_NOUN_BEFORE.search(before).group(1).lower() == 'docstring'
                and _names_a_declaration_docstring(soft, max(0, m.start() - 90), m.start())):
            out.append((m.group(1), 'names prose that moved: '
                        + PROSE_NOUN_BEFORE.search(before).group(1)))
        elif SECTION_AFTER.match(tail):
            # ⚠ ONLY IF THE HEADING ACTUALLY LEFT. Firing on every `§` after a ride-along name
            # asserts a move that did not happen: `Occurrence.lean` kept `§ III` and `§ VI` as
            # headings while their BODIES moved, and the check reported both as relocated. That is
            # a false positive whose surface GROWS with every conversion — the same shape as the
            # title-overlap heuristic deleted below, and the reason it was deleted.
            mark = SECTION_AFTER.match(tail).group(1)
            if _section_heading_present(pairs_owner(m.group(1)), mark):
                out.append((m.group(1),
                            'names a SECTION of a file that has a ride-along — heading is still '
                            'in the .lean; confirm the CONTENT it names did not move'))
            else:
                out.append((m.group(1), 'names a SECTION that moved to the ride-along'))
    return out


_headings = {}


def _canon_section(s):
    """`§ III` / `§III` / `section III` / `§ III.` -> `III`.

    All four spellings occur here. Comparing raw markers made the rule spelling-sensitive, and the
    two controls that existed happened to use the one spelling that worked.
    """
    s = re.sub(r"^\s*(?:§|section\b|ch(?:apter)?\b)\s*", "", s.strip(), flags=re.I)
    return re.sub(r"\s+", " ", s).strip().rstrip(".").upper()


def _section_heading_present(lean_rel, mark):
    """Does `mark` still open a heading in the cited `.lean`?

    Existence of the heading is NOT proof the cited content stayed - a subsection can move out from
    under a heading that remains. So a present heading DOWNGRADES the message rather than
    suppressing the hit: the checker locates, the reader judges.

    ⚠ MATCH THE WHOLE MARKER. `SECTION_AFTER` used to capture one character, so every marker
    canonicalised to `I` and `§ IV` "matched" the `§ I` heading - the test distinguished nothing,
    and passed its controls for that reason.
    """
    if lean_rel is None:
        return False
    if lean_rel not in _headings:
        try:
            body = (REPO / lean_rel).read_text(encoding="utf-8", errors="replace")
        except OSError:
            body = ""
        _headings[lean_rel] = [_canon_section(h)
                               for h in re.findall(r"^\s*/-!\s*#+\s*(.+?)\s*$", body, re.M)]
    want = _canon_section(mark)
    if not want:
        return False
    return any(h == want or h.startswith(want + ".") or h.startswith(want + " ")
               for h in _headings[lean_rel])


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
        # ⚠ EVERY `.py` UNDER `scripts/`, RECURSIVELY, NOT JUST `build_*`. The glob was
        # non-recursive while this comment claimed otherwise, so `scripts/archive/` was
        # invisible (measured by plant). The glob walked past
        # `zp_utils.py` — the shared library those build scripts IMPORT — so a stale pointer
        # there reached every rendered PDF while being invisible here. Measured by a plant:
        # the same sentence fired in `build_zpa.py` and was silent in `zp_utils.py`.
        build_scripts = sorted(p for p in (REPO / 'scripts').rglob('*.py') if p.is_file())
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
            print('  INFORMATIONAL: does not fail the run.')
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
            print('  INFORMATIONAL: does not fail the run. A RISING number means the class is growing.')
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
