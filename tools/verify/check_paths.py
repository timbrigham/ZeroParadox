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
import io
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

# Repo-relative references to real project files. Narrow on purpose — only paths starting at a
# TRACKED top-level directory, so prose like "see Foo/Bar" is not misread.
#
# ⚠⚠ THE ROOTS ARE DERIVED FROM `git ls-files`, NOT LISTED. They were `ZeroParadox|scripts|.github`
# — three someone thought of in a session predating the layout — and `tools/` went public on
# 2026-08-15 without the pattern following. Measured (`RLY16-1`): **54 references into `tools/` across
# 26 distinct targets, one of them DANGLING**, while this file printed *"all repo-relative references
# resolve"*, exit 0. That is this checker's own stated purpose inverted, and the dangling one sits in
# a PUBLISHED gate brief. `.claude/` and `_layouts/` were missing too.
#
# **The property is decidable, so decide it**: a directory that is tracked is a directory whose
# references must resolve. Adding a top-level directory now extends coverage by itself — which is the
# difference between a guard and the hole-list this was.
def _tracked_roots():
    out = subprocess.run(['git', 'ls-files'], cwd=REPO,
                         capture_output=True, text=True, check=True).stdout.split('\n')
    roots = {p.split('/')[0] for p in out if '/' in p}
    # ⚠ TOTALLY ORDERED, NOT JUST LONGEST-FIRST. `roots` is a SET, and sorting by length alone leaves
    # equal-length roots in set-iteration order — `scripts`, `.github` and `.claude` are all seven
    # characters, so the compiled pattern differed BETWEEN RUNS. Caught by the vocabulary pin, which
    # is exactly what a pin is for: it does not care what the pattern is, only that it stopped being
    # the same one. Length descending prevents prefix shadowing; the name breaks ties.
    return sorted(roots, key=lambda r: (-len(r), r))


PATTERN = re.compile(
    r'(?<![\w/.-])((?:' + '|'.join(re.escape(r) for r in _tracked_roots()) +
    r')/[A-Za-z0-9_./-]+\.(?:lean|py|md|json|yml|yaml))'
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

# ⚠⚠ AND THE SAME TRAP EXISTS IN MARKDOWN, ONE STEP OVER — carving Lean out was not enough.
# An arrow marks a MOVE only when it joins two PATHS. In a workflow chain it means "then", and a
# whole line was suppressed on that basis: `tag-review.md` reads *"exit 0 → re-pin the new hash →
# finalize the log → optionally refresh `tools/registry/registry_export.json`"* — a genuinely
# DANGLING reference in a PUBLISHED gate brief, invisible because a sentence used arrows to sequence
# steps. Found by `/rely` hand-resolving what the tool would not (`RLY16-1`).
# So the arrow suppresses only when it actually connects two path-like tokens.
#
# ⚠⚠ AND THE FIRST VERSION OF THIS RULE DISCRIMINATED ON **DELIMITERS**, NOT ON MOVE-VS-CHAIN
# (`ARROW-1`, /rely). `\s*` cannot cross a backtick, so `` `A.lean` → `B.lean` `` — the way this
# corpus actually writes a move — did NOT match, and the rule suppressed nothing there. It caught
# its own motivating case only because a backtick happened to sit between `.py` and the arrow:
# right answer, accidental reason. Measured 2 of 9 fixtures correct.
#
# Two changes take it to 9 of 9. Blank the delimiters first, EQUAL-LENGTH so nothing shifts, so the
# arrow can see the paths either side of them. And require the TARGET to look like a path — contain
# a `/` or a `.` — because that is what separates *"Old.lean → New.lean"* (a move) from
# *"`foo.py` → re-pin the hash"* (a chain whose next step is prose).
# ⚠ `_` IS NOT IN THIS CLASS AND MUST NOT BE. It is a markdown emphasis marker, but it is also a
# character inside almost every filename here — blanking it split `old_name.py` into `old name.py`
# and the move stopped being recognised. Caught by the `bare basenames` control on first run.
# An italicised path is rare; an underscored one is the norm.
_ARROW_DELIM = re.compile(r'[`*"\']')
#
# ⚠ THE TARGET NEEDS A SEPARATOR OR A KNOWN EXTENSION, NOT MERELY A DOT. "contains `/` or `.`" was
# the first cut and /rely measured what it swallows: `v1.5`, `2.`, `0.5s`, `done.` and `...` all
# contain a dot, so `` `build_zpa.py` → v1.5, then rebuild `` was classed a MOVE and silenced its
# whole line. Live impact was nil, which is exactly how the original arrow defect stayed invisible
# for months — a suppression rule is judged by what it COULD hide, not by today's count.
_ARROW_MOVE = re.compile(
    r'[\w./-]+\.(?:lean|py|md|json|yml|yaml)\s*(?:->|→)\s*'
    r'(?:[\w.-]*/[\w./-]*|[\w.-]+\.(?:lean|py|md|json|yml|yaml)\b)'
)


def _arrow_is_a_move(line):
    """True when an arrow on this line joins two paths, i.e. genuinely notates a rename/move.

    Delimiters are blanked equal-length before matching: the question is whether the arrow connects
    two paths, and a backtick between them does not change the answer.
    """
    return bool(_ARROW_MOVE.search(_ARROW_DELIM.sub(' ', line)))

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


def tracked_scripts():
    """Tracked Python — the surface a claim RENDERS from, plus the layer that ASSERTS about itself.

    ⚠ Not optional. The 2026-08-01 sweep that recorded a false universal negative as removed grepped
    `.lean` and missed a Python build script, so the claim survived in RENDERED PUBLIC PROSE and was
    still there three months later.

    ⚠⚠ **`tools/verify/**` WAS ABSENT, AND `--claim`'s FIRST REAL USE PROVED IT** (2026-08-19). An
    adversary pass located the same false claim at three sites in `check_hashes.py`; the sweep built
    to catch exactly that — DC-24, one claim living at several sites — returned **0 hits across 328
    surfaces**, because its surface set was `scripts/*.py` and nothing else. A zero from a detector
    that cannot see the file is a COVERAGE GAP, never an absence, and this is the same `tools/`
    blindness fixed in the path resolver two commits earlier and not carried here: one lesson, two
    consumers, one updated. The checkers assert about themselves constantly — every ⚠ block in this
    directory is a claim — so they are exactly the surface where a stale one hides.

    ⚠⚠ **`tools/*.py`, NOT `tools/**/*.py`, AND THE `**` FORM SILENTLY LOSES DEPTH 1** (`RLY21-1`).
    Git's default pathspec is **non-pathname wildmatch, where a bare `*` ALREADY CROSSES `/`** — so
    `scripts/*.py` was recursive all along, and adding `**` widened nothing while inserting a
    mandatory separator. Measured at three depths: `tools/**/*.py` returns depth 2 and 3 and **drops
    depth 1**; `tools/*.py` returns all three. Planting one sentence in three tracked files at three
    depths, the `**` form reported `365 surfaces` (+2 for 3 files) and found 2 of 3 — a confident
    count over a silent miss, i.e. this function's own defect class committed inside its own fix.

    **The `**` came from `common.py:116`, where the identical string is CORRECT**, because
    `pathlib.glob` gives `**` a zero-or-more-directories meaning git's wildmatch does not. A glob
    STRING carried from a pathlib enumerator to a git enumerator means less at the destination —
    the mirror-drift failure at the level of an idiom rather than a file. Use `:(glob)` if the
    pathname semantics are ever actually wanted.
    """
    out = subprocess.run(
        ['git', 'ls-files', 'scripts/*.py', 'tools/*.py'],
        cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.split('\n')
    return [REPO / p for p in out if p.strip()]


def _universe_gap(paths, pat):
    """(what the enumerator returned, what git tracks matching `pat`) — as repo-relative sets.

    Extracted so the UNIVERSE check and its MUST-FIRE control run the SAME comparison. A control that
    reaches the property by a different path cannot see production's wiring removed — the `RLY18-5`
    lesson, applied at birth rather than after a round.
    """
    live = {str(p.relative_to(REPO)).replace('\\', '/') for p in paths}
    uni = {x.strip() for x in subprocess.run(
        ['git', 'ls-files', pat], cwd=REPO, capture_output=True, text=True,
        encoding='utf-8', errors='replace').stdout.split('\n') if x.strip()}
    return live, uni


def _rel(path):
    """Repo-relative display path, falling back to the absolute one.

    ⚠ `relative_to` RAISES on anything outside the tree, so the bare form turned `sweep_claim` — a
    pure function whose whole point is that a caller can hand it any file list — into one that
    exploded on a path from a temp directory. Degrading is correct here: an out-of-tree file still
    has a name worth printing.
    """
    try:
        return str(path.relative_to(REPO)).replace('\\', '/')
    except ValueError:
        return str(path).replace('\\', '/')


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
            # ⚠ An arrow alone no longer suppresses: it must actually JOIN TWO PATHS. Otherwise a
            # workflow sentence ("do X → then Y → then refresh `some/path.json`") silences the whole
            # line, which is how a dangling reference sat in a published gate brief (`RLY16-1`).
            _hit = [m for m in markers if m in line.lower()]
            _arrows = {'->', '→'}
            if _hit and set(_hit) <= _arrows and not _arrow_is_a_move(line):
                _hit = []
            if _hit:
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

    # ⚠⚠ THE ARROW RULE HAD NO CONTROL AT ALL, which is how it shipped answering 2 of these 9
    # (`ARROW-1`). Both polarities matter and they fail in opposite directions: a move that is NOT
    # recognised turns a rename note into false positives, and a chain that IS recognised silences
    # a whole line — which is how a dangling reference sat in a published gate brief. The delimiter
    # forms are the point: this corpus writes moves in backticks and bold, so a rule that only works
    # on bare text works almost nowhere.
    print('  MUST FIRE  (arrow notates a MOVE — suppression is correct)')
    for label, line in (
        ('bare',            'ZeroParadox/A.lean -> ZeroParadox/B.lean'),
        ('unicode arrow',   'ZeroParadox/A.lean → ZeroParadox/B.lean'),
        ('backticked',      'moved `ZeroParadox/A.lean` → `ZeroParadox/B.lean` last week'),
        ('bold',            '**scripts/old.py** -> **scripts/new.py**'),
        ('quoted',          '"tools/a.json" → "tools/b.json"'),
        ('bare basenames',  'old_name.py → new_name.py'),
    ):
        ok = _arrow_is_a_move(line)
        bad += 0 if ok else 1
        print('    %-32s %s' % ('move: %s' % label, 'ok' if ok else '*** NOT RECOGNISED ***'))

    print('  MUST SUPPRESS  (arrow sequences STEPS — suppression would hide a dead path)')
    for label, line in (
        ('workflow chain',  'run `ssot_l1_acceptance.py` exit 0 -> re-pin the hash -> finalize'),
        ('chain to prose',  '`build_zpa.py` → then rebuild the companion'),
        ('prose both ends', 'the log → the ledger'),
        # /rely's four: a dot is not a path. Each of these was classed a MOVE by the first cut.
        ('arrow to a version',  '`build_zpa.py` → v1.5, then rebuild'),
        ('arrow to a list item', '`build_zpa.py` → 2. rebuild the companion'),
        ('arrow to a duration',  '`build_zpa.py` → 0.5s on this machine'),
        ('arrow to a sentence',  '`build_zpa.py` → done. Next step follows'),
    ):
        ok = not _arrow_is_a_move(line)
        bad += 0 if ok else 1
        print('    %-32s %s' % ('chain: %s' % label, 'ok' if ok else '*** OVER-WIDE ***'))

    # ⚠ THE VOCABULARY PIN (PAT-1). The controls above prove the patterns they exercise;
    # this proves the rest are still there. Measured before it was written: 30 of 34
    # list-shaped patterns could be deleted with every control green, and the compiled
    # regexes carrying the rest of the vocabulary were pinned by nothing at all.
    # ⚠ THE SCOPE PIN (PAT-2). This checker BLOCKS at push and walks privately, and had no
    # scope section at all: its controls run in memory and never touch its enumerator, so
    # nothing exercised what it covers. Verified rather than inferred by /rely round 4.
    # ⚠⚠ **A SNAPSHOT PIN CAN SEE A RECORDED FILE LEAVE. IT CAN NEVER SEE A NEW FILE FAIL TO ARRIVE**
    # (`RLY22-2`). That is not a gap in the seeding, it is the SHAPE of a superset-over-recorded test:
    # the files a bad glob drops are, by construction, the ones never recorded. Measured — the
    # `tools/**/*.py` regression that shipped in `a34429c` passes the pin at exit 0 forever, because
    # `**` and `*` return identical sets under `tools/` today and diverge only on files added later.
    #
    # So the pin is paired with an INVARIANT, which is a different kind of claim: each enumerator must
    # cover its ENTIRE tracked universe, computed now rather than recorded. Measured 2026-08-19 —
    # python 84/84, markdown 60/60, lean 219/219, all three exactly equal.
    #
    # ⚠⚠ **WHAT IT CATCHES IS A FILE THE ENUMERATOR CANNOT REACH — NOT, BY ITSELF, THE `RLY21-1`
    # GLOB.** An earlier version of this comment claimed the shipped `**` regression "reads 36 against
    # a universe of 84 and fires immediately". Measured FALSE (`RLY23-1`): planting the byte-exact
    # `a34429c` enumerator into this tree gives `84 of 84`, PASS, exit 0, because `tools/**/*.py` and
    # `tools/*.py` both return 35 while nothing sits at depth 1. The 36 came from a BOTH-ARMS form
    # (`scripts/**` too) that never shipped — and on that form the SCOPE pin fires anyway, so on the
    # example cited this control added nothing.
    #
    # **The honest statement, and the control below is exactly it:** the invariant is the SOLE
    # detector when a bad enumerator meets a file that is genuinely new. Shipped `**` regression plus
    # one new depth-1 `tools/*.py`: invariant `*** INCOMPLETE *** (84 of 85)`, SCOPE pin `ok
    # (363/363/363)` — blind, as `RLY22-2` predicts. That is the pairing: the pin covers removals of
    # what was recorded, the invariant covers arrivals it can never have recorded.
    #
    # ⚠ A DELIBERATE exclusion (vendored code, generated files) trips this, and **there is no
    # exclusion list to record it in** — this is a strict set equality by design. An earlier line here
    # said such an exclusion would be "stated and recorded", which named a surface that does not
    # exist. If one is ever needed, add it explicitly rather than widening the universe query, which
    # would silence the control instead of narrowing it.
    print('  UNIVERSE')
    for _name, _paths, _pat in (('python', tracked_scripts(), '*.py'),
                                ('markdown', tracked_markdown(), '*.md'),
                                ('lean', tracked_lean(), '*.lean')):
        _live, _uni = _universe_gap(_paths, _pat)
        _ok = _live == _uni
        bad += 0 if _ok else 1
        _why = '' if _ok else '  MISSED %s' % (sorted(_uni - _live)[:3] or sorted(_live - _uni)[:3],)
        print('    %-32s %s (%d of %d tracked)%s'
              % ('%s enumerator is complete' % _name,
                 'ok' if _ok else '*** INCOMPLETE ***', len(_live), len(_uni), _why))

    # ⚠⚠ AND IT HAD **NO MUST-FIRE CONTROL**, WHICH `check_checkers` COULD NOT SEE (`RLY23-2`). Its
    # "both halves" property is a PROXY: it greps this selftest's output for `MUST FIRE` headings, and
    # the arrow and claim-sweep sections already supply them — so it reported `violations: 0` over a
    # section asserted in the passing direction only. Exactly the shape that shipped the arrow rule at
    # 2 of 9. In memory, no git writes: narrow each enumerator by one real file and require divergence.
    print('  MUST FIRE  (a narrowed enumerator is INCOMPLETE)')
    for _name, _paths, _pat in (('python', tracked_scripts(), '*.py'),
                                ('markdown', tracked_markdown(), '*.md'),
                                ('lean', tracked_lean(), '*.lean')):
        _dropped = sorted(_paths)[:-1]
        _l, _u = _universe_gap(_dropped, _pat)
        _fires = _l != _u
        bad += 0 if _fires else 1
        print('    %-32s %s (%d of %d)' % ('%s: drop one, gap appears' % _name,
                                           'ok' if _fires else '*** SILENT ***', len(_l), len(_u)))

    print('  SCOPE')
    # ⚠⚠ `tracked_scripts()` IS IN THE PIN, AND ITS ABSENCE IS WHY `RLY21-1` SHIPPED. The pin was fed
    # markdown + lean only, so the 84 Python surfaces were pinned by nothing: `--selftest` printed
    # IDENTICAL numbers (252 recorded / 252 present / 279 live) at both revisions while the claim
    # surface moved 328 → 363 and then silently lost every depth-1 file under a bad glob. A pin that
    # cannot see an enumerator cannot notice it changing — and `selftest_claim` passes `files=[p]` at
    # every call site, so no control touched it either. This is the one control that would have fired.
    bad += common.check_scope('check_paths',
                              [str(p.relative_to(REPO)).replace('\\', '/')
                               for p in (list(tracked_markdown()) + list(tracked_lean())
                                         + list(tracked_scripts()))])
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


# ---------------------------------------------------------------------------------------------
# `--claim` — sweep ONE CLAIM across every rendering surface. The mechanical half of DC-24, owed
# since that class was opened and named by both prose gates in round 5.
#
# ⚠ IT IS A READING LIST, AND IT DOES NOT REPLACE THE GATES — an earlier version of this header said
# it "would have printed every finding they made", and that was measured FALSE (`RLY21-3`). Over the
# three sites of the 2026-08-19 defect: `"never existed"` returns **2 of 3**, `"nonexistent"` returns
# **1 of 3**, and no single phrase returns all three — the third reads *"not merely stale but
# nonexistent"*, which is the same claim in words this sweep cannot reach from either. That is the
# tool working as designed: it takes a phrase, so it finds a phrasing. Run BOTH POLARITIES and more
# than one wording, and treat a zero as evidence about the query until proven otherwise.
#
# ⚠ THREE DESIGN POINTS, EACH PAID FOR BY A MEASURED FAILURE:
#   1. WRAP-TOLERANT, WITH LINE NUMBERS SURVIVING IT. `check_modal` shipped with literal spaces in
#      its patterns, so a claim wrapped across a line was invisible — and Lean docstrings and Python
#      string concatenation wrap constantly. Markers are blanked to EQUAL-LENGTH spaces so a match
#      offset still maps to the right line.
#   2. ALL THREE SURFACES IN ONE RUN — `.md` + `.lean` + tracked Python, which since 2026-08-19 means
#      `tools/**` as well as `scripts/`. See `tracked_scripts`, and the measurement in its docstring:
#      omitting the verification layer is what made this sweep's first real use return a false zero.
#   3. SEVERAL PHRASES, BECAUSE POLARITY IS THE POINT. Rounds 1–4 of the choice arc keyed on a
#      universal negative; the sites that survived asserted the POSITIVE form. Neither search could
#      reach the other. Pass the claim AND the form the corpus would use if it disagreed with you.
#
# ⚠⚠ ADVISORY. It never blocks and never classifies: whether a hit is a defect, a correct denial, or
# a changelog entry recording the fix is judgement, and a checker that guessed would manufacture the
# false-positive work this project has already measured twice.
#
# ⚠⚠⚠ **THIS CHECK HAS ALREADY FAILED THREE TIMES, WHICH IS RUNG 5 OF `CLAUDE.md`'s ESCALATION
# LADDER: STOP WIDENING IT.** Emphasis, then entities and escaped quotes, then line-start markers —
# each fix closed the holes its author thought of, and a `/rely` pass watching the second land
# reported both its routes still blind. The failure is ENUMERATION (the space of formatting shapes is
# open-ended), not GROUND TRUTH, so by the ladder's discriminator the next layer is an **LLM screen**
# — `.claude-local/deepseek/fragment_screen.py` is the built precedent, and its docstring records the
# same lesson from a whitespace rule that corrupted 61 files (measured 2026-08-02) while its damage
# checker shared the bug.
# **Keep this checker**: it is free, it runs anywhere, and it catches the shapes it knows. Do not
# mistake it for coverage.

# ⚠⚠ A PROPERTY, NOT A HOLE-LIST. This was `(--|//|#)` — three markers someone thought of — and a
# `/rely` pass enumerated the routes instead of testing the list: of ten line-start markers in this
# corpus FIVE were blind (`>`, `-`, `+`, `1.`, `|`), and `*` was covered only by accident because it
# doubles as an emphasis character. A published gate brief's sentence returned zero sites purely
# because its lines begin with `>`. Widening the list again would repeat the shape; the property is
# **a line-start structural marker must not break a phrase**, so match the CLASS: any short run of
# punctuation, or an ordered-list number, at the head of a line.
_CLAIM_MARKER = re.compile(r'(?m)^([ \t]*)([-*+>|#/]{1,3}|\d{1,3}\.)(?=\s)')
# Adjacent Python string literals across a line break — BOTH quote styles. The single-quote-only
# form was blind in four tracked build scripts, and `scripts/*.py` is the surface DC-24's own row
# names as the one that keeps being missed and the one a DOI freezes.
_CLAIM_JOIN = re.compile("'\\s*\\n\\s*'" + '|"\\s*\\n\\s*"')
# ⚠⚠ FORMATTING IS A SEARCH FILTER, AND THIS IS THE LONGEST LIST IN THE FILE FOR A REASON. Every
# entry below was SILENT on a version of this tool, and two were live in prose written the same hour:
#   *emphasis*          README's `*essential* rather than inherited` — the site an editorial gate had
#                       by hand while this reported the file clean. The first blind spot found.
#   &#8212; &#8217;      HTML entities mid-phrase, live in `build_zp_choice_free_core.py`
#   framework\'s        an ESCAPED APOSTROPHE in a Python literal — and this arc's claim is
#                       literally "the framework's own", so the sweep was blind to its own subject
#   [text](href)        a markdown link injected mid-phrase, live at the README site itself
#   curly ’ “ ”         against a phrase typed with ASCII punctuation
#   | <sub> <br/>       table-cell pipes and inline tags
# Blanking is always EQUAL-LENGTH; the curly folds are 1:1, so line numbers survive all of it.
_CLAIM_EMPH = re.compile(
    r'\*\*|\*|__|_|`'            # markdown emphasis / code spans
    r'|</?[A-Za-z][^>]{0,20}>'   # any short inline HTML tag: <i> <b> <sub> <br/> <em> ...
    r'|&[#A-Za-z0-9]{1,8};'      # HTML entities: &#8212; &#8217; &amp; ...
    r'|\\(?=[\'"])'              # the BACKSLASH of an escaped quote, leaving the quote itself
    r'|\]\([^)]{0,120}\)'        # the trailing half of a markdown link, keeping its text
    r'|\['                       # ...and its opening bracket
    r'|\|')                      # markdown table-cell separators
# 1:1 punctuation folds — same character count, so offsets are untouched.
_CLAIM_FOLD = str.maketrans({'’': "'", '‘': "'", '“': '"', '”': '"',
                             '–': '-', '—': '-', ' ': ' '})


def _soften(text):
    """Blank structural markers so they cannot break a phrase — PRESERVING EVERY NEWLINE.

    ⚠⚠ **NEWLINE preservation is the invariant, NOT length preservation, and the first version of
    this docstring guarded the wrong one.** `line_at` is built by walking `soft` and counting `\\n`,
    so an equal-length substitution that ATE a newline still shifted every subsequent line. That is
    exactly what happened: `_CLAIM_JOIN` matches across a line break and replaced it with spaces, so
    each hit was reported one line low per join above it — measured at up to **347 lines** of skew in
    `build_zpe.py`. The certifying control passed throughout, because its fixture had zero joins
    above the hit.

    A length-destroying `_soften` survives every control here; a newline-destroying one is the bug.
    Guard the invariant that matters: every substitution below re-emits the newlines it consumed.
    """
    def blank_keeping_newlines(m):
        s = m.group(0)
        return ''.join('\n' if ch == '\n' else ' ' for ch in s)

    out = text.translate(_CLAIM_FOLD)
    out = _CLAIM_MARKER.sub(lambda m: m.group(1) + ' ' * len(m.group(2)), out)
    out = _CLAIM_JOIN.sub(blank_keeping_newlines, out)
    return _CLAIM_EMPH.sub(blank_keeping_newlines, out)


def _claim_pattern(phrase):
    """A phrase as a wrap-tolerant, case-insensitive regex: any whitespace run matches any other.

    ⚠ THE FOLD APPLIES TO THE PHRASE TOO, or it only works in one direction. Folding the corpus
    alone lets an ASCII-typed phrase reach curly text — but a phrase copied FROM rendered prose,
    carrying an em dash or a smart apostrophe, still could not reach source written with a hyphen.
    Normalising both sides means the direction the caller happens to type in stops mattering.
    Measured as a live gap: "em dash vs hyphen, either direction".
    """
    folded = phrase.translate(_CLAIM_FOLD)
    return re.compile(r'\s+'.join(re.escape(w) for w in folded.split()), re.I)


def tracked_pdfs():
    out = subprocess.run(
        ['git', 'ls-files', '*.pdf'], cwd=REPO, capture_output=True, text=True, check=True
    ).stdout.split('\n')
    return [REPO / p for p in out if p.strip()]


def _pdf_text(path):
    """Extracted text of a rendered PDF, or None if it cannot be read."""
    try:
        try:
            from pypdf import PdfReader
        except ImportError:
            from PyPDF2 import PdfReader
        return ' '.join((pg.extract_text() or '') for pg in PdfReader(str(path)).pages)
    except Exception:                                             # noqa: BLE001
        return None


def _claim_targets():
    seen, out = set(), []
    for group in (tracked_markdown(), tracked_lean(), tracked_scripts()):
        for p in group:
            if str(p) not in seen:
                seen.add(str(p))
                out.append(p)
    return out


def sweep_claim(phrases, files=None, pdfs=False):
    """[(rel, line, phrase, context)], [(rel, why)] — pure, prints nothing.

    ⚠⚠ `pdfs=True` ADDS THE RENDERED TEXT, AND IT IS THE AUTHORITATIVE SURFACE, NOT AN EXTRA.
    `vocabulary_reference.md`'s Update Log records the rule, paid for by a claim that survived FOUR
    sweeps: *verify prose claims against the extracted PDF text, not the build script — that is the
    only surface where concatenation and entity-escaping are already resolved.* Every formatting
    shape `_soften` has to defend against upstream (`&#8212;`, `framework\\'s`, literals split across
    adjacent strings) is a SOURCE artifact the PDF has already resolved. Sweeping source alone means
    defending against the whole list; sweeping the render means the question was already answered.
    Line numbers are meaningless there, so a PDF hit reports page-less line 0 and names the file.
    """
    hits, unreadable = [], []
    targets = list(files if files is not None else _claim_targets())
    if pdfs and files is None:
        targets += tracked_pdfs()
    for path in targets:
        if str(path).lower().endswith('.pdf'):
            raw = _pdf_text(path)
            if raw is None:
                unreadable.append((_rel(path), 'PDF text could not be extracted'))
                continue
            flat_pdf = re.sub(r'\s+', ' ', raw)
            for phrase in phrases:
                for m in _claim_pattern(phrase).finditer(flat_pdf):
                    lo, hi = max(0, m.start() - 90), min(len(flat_pdf), m.end() + 90)
                    hits.append((_rel(path) + '  [RENDERED]', 0, phrase, flat_pdf[lo:hi].strip()))
            continue
        try:
            raw = path.read_text(encoding='utf-8')
        except (OSError, UnicodeDecodeError) as exc:
            unreadable.append((_rel(path), str(exc)))
            continue
        soft = _soften(raw)
        line_at, n = [], 1
        for ch in soft:
            line_at.append(n)
            if ch == '\n':
                n += 1
        flat = soft.replace('\n', ' ')
        for phrase in phrases:
            for m in _claim_pattern(phrase).finditer(flat):
                lo, hi = max(0, m.start() - 90), min(len(flat), m.end() + 90)
                # ⚠ SHOW THE LINE BREAKS IN THE CONTEXT. Blanking a line-start marker lets a phrase
                # WELD across two list items that never contained it:
                #     * choice here is the framework's own
                #     * rather than inherited from Mathlib
                # matches "own rather than inherited", which is in neither bullet. That is the price
                # of matching the marker CLASS rather than an enumeration — five markers were blind
                # before and so could not weld; all ten can now. It is a real trade, not a bug to
                # argue away, and the reader is the one who adjudicates: a run of spaces hides the
                # boundary, a sentinel makes the weld self-evident. Line numbers are untouched.
                # ⚠ ONLY INSIDE THE MATCHED SPAN. The first version marked every break in the ±90
                # window, so an ordinary correct single-line hit showed three sentinels: measured
                # **511 hits, 418 (82%) sentinel-marked, 0 of them welds** — the cry-wolf shape this
                # project elsewhere says to narrow rather than tolerate, and the comment claiming it
                # "makes the weld self-evident" was describing something the code did not do. A break
                # OUTSIDE the match is just neighbouring text; a break INSIDE it is the weld.
                # ⚠⚠ TWO SENTINELS, BECAUSE ONE DOES NOT DISCRIMINATE. `⏎` alone renders a WELD
                # (a phrase spanning two list items, present in neither) identically to an honest
                # wrapped line — both read `own⏎ rather` — since a blanked marker collapses to a
                # space and so does continuation indentation, which is this repo's dominant wrap
                # style. `_soften` is length-preserving, so comparing `raw` against `soft` recovers
                # exactly the positions that were blanked: `⊘` marks a swallowed MARKER, and
                # `⏎⊘` is the weld signature. Honest wrap stays `⏎`.
                _ctx = ''.join(
                    ('⏎' if soft[lo + i] == '\n'
                     else '⊘' if (lo + i < len(raw) and raw[lo + i] != soft[lo + i]
                                  and soft[lo + i] == ' ') else c)
                    if (m.start() <= lo + i < m.end() and lo + i < len(soft)) else c
                    for i, c in enumerate(flat[lo:hi]))
                hits.append((_rel(path), line_at[m.start()], phrase,
                             re.sub(r'[ \t]+', ' ', _ctx).strip()))
    return sorted(hits), unreadable


def cmd_claim(phrases, pdfs=False):
    hits, unreadable = sweep_claim(phrases, pdfs=pdfs)
    by_file = {}
    for rel, line, phrase, ctx in hits:
        by_file.setdefault(rel, []).append((line, ctx))
    print('=' * 78)
    print('  CLAIM SWEEP — %d phrase(s) over %d tracked surface(s)'
          % (len(phrases), len(_claim_targets())))
    for p in phrases:
        print('    "%s"' % p)
    print('=' * 78)
    for rel in sorted(by_file):
        print('\n  %s' % rel)
        for line, ctx in by_file[rel]:
            print('    :%-5d ...%s...' % (line, ctx[:150]))
    # ⚠ NO SILENT TRUNCATION: a file that could not be read is REPORTED. Absence inferred from an
    # unread file is the shape that produced three false negatives in one month.
    if unreadable:
        print('\n  ⚠ COULD NOT READ — absence is NOT established for these:')
        for rel, why in unreadable:
            print('    %s — %s' % (rel, why))
    print('\n  %d site(s) across %d file(s).' % (len(hits), len(by_file)))
    print('  ⚠ READING LIST, NOT A FINDING LIST — read every hit; never act on the count.')
    if not pdfs:
        print('  ⚠ SOURCE ONLY. Add --pdf for the RENDERED text, which is the authoritative surface')
        print('    for a published claim: it has already resolved entities, escapes and string joins.')
    print('  ⚠ Run BOTH POLARITIES. Four gate rounds missed a live site for want of that.')
    return 0


def selftest_claim():
    """Controls for `--claim`. Subject is `sweep_claim` itself — never a re-implementation (DC-25).

    ⚠ EVERY MUST-FIRE PLANT IS IN A SHAPE THIS CORPUS ACTUALLY PRODUCES: wrapped mid-sentence,
    comment-prefixed, and split across adjacent Python string literals. A probe written FLAT passes
    against a detector that cannot see wrapping and teaches nothing — measured on `check_modal`,
    whose flat probe gave a false all-clear while the wrapped form was invisible.
    """
    import tempfile
    bad = 0
    CLAIM = 'choice enters only in the analytic realisations'

    MUST_FIRE = [
        ('flat, in markdown', 'x.md',
         'Text before. The claim: choice enters only in the analytic realisations. After.\n'),
        ('WRAPPED mid-sentence', 'x.md',
         'Text before. The claim: choice enters only\nin the analytic realisations. After.\n'),
        ('comment-prefixed and wrapped, Lean', 'x.lean',
         '-- The claim: choice enters only\n-- in the analytic realisations, said here.\n'),
        ('split across Python literals', 'x.py',
         "E.append(body(\n    'The claim: choice enters only '\n"
         "    'in the analytic realisations.'))\n"),
        # ⚠ FOUND BY RUNNING THE TOOL, NOT BY DESIGNING IT. On its first real sweep this shape was
        # SILENT: README carries `*essential* rather than inherited`, and a phrase a human types has
        # no asterisks in it. An editorial gate had that site by hand while the sweep called the file
        # clean — formatting acting as a search filter.
        ('markdown emphasis INSIDE the phrase', 'x.md',
         'The claim: choice *enters only* in the **analytic** realisations.\n'),
        ('HTML emphasis inside the phrase, rendered prose', 'x.py',
         "sp('The claim: choice enters <i>only</i> in the analytic realisations.')\n"),
        # ⚠ THE SIX THE EDITORIAL GATE ENUMERATED, EACH SILENT ON THE PREVIOUS VERSION. Two were
        # live in prose written the same hour as the tool, including one inside the very fix that
        # removed the claim. A formatting choice is a search filter, and an unexamined filter is a
        # blind half — this list is the examined half.
        ('HTML numeric entity mid-phrase', 'x.py',
         "sp('The claim: choice enters only &#8212; in the analytic realisations.')\n"),
        ('ESCAPED APOSTROPHE in a Python literal', 'x.py',
         "sp('The claim: the framework\\\\'s own choice enters only in the analytic realisations.')\n"),
        ('markdown link injected mid-phrase', 'x.md',
         'The claim: choice enters [only](README.md) in the analytic realisations.\n'),
        ('markdown table-cell pipes', 'x.md',
         '| choice enters only | in the analytic realisations |\n'),
        ('inline tags between words', 'x.md',
         'The claim: choice enters only<br/> in the <sub>analytic</sub> realisations.\n'),
    ]
    # ⚠ THE CURLY FOLD NEEDS ITS OWN PHRASE, and my first two probes for these were WRONG rather
    # than the tool being wrong (DC-22 — a control failing for a reason unrelated to the property).
    # I injected an em dash mid-phrase and put a digit inside a <sub>, then read the misses as tool
    # defects. Neither is: injected PUNCTUATION and injected CONTENT are different text, and a sweep
    # that matched across them would fire on anything. The fold's actual job is narrower — let an
    # ASCII-typed phrase reach text set with typographic quotes.
    CURLY = [('curly apostrophe vs an ASCII phrase', 'x.md',
              'It is the framework’s own choice, stated here.\n',
              "the framework's own choice")]
    MUST_SUPPRESS = [
        ('absent entirely', 'x.md', 'Nothing resembling it appears in this file at all.\n'),
        ('near-miss wording', 'x.md', 'choice enters in some of the analytic realisations\n'),
    ]

    print('  MUST FIRE  (claim sweep)')
    for label, name, content in MUST_FIRE:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / name
            io.open(p, 'w', encoding='utf-8', newline='\n').write(content)
            hits, _ = sweep_claim([CLAIM], files=[p])
        ok = len(hits) == 1
        bad += 0 if ok else 1
        print('    %-40s %s' % (label, 'ok' if ok else '*** MISSED ***'))

    for label, name, content, phrase in CURLY:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / name
            p.write_text(content, encoding='utf-8', newline='\n')
            hits, _ = sweep_claim([phrase], files=[p])
        ok = len(hits) == 1
        bad += 0 if ok else 1
        print('    %-40s %s' % (label, 'ok' if ok else '*** MISSED ***'))

    print('  MUST SUPPRESS  (claim sweep)')
    for label, name, content in MUST_SUPPRESS:
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / name
            io.open(p, 'w', encoding='utf-8', newline='\n').write(content)
            hits, _ = sweep_claim([CLAIM], files=[p])
        ok = not hits
        bad += 0 if ok else 1
        print('    %-40s %s' % (label, 'ok' if ok else '*** FALSE POSITIVE ***'))

    # ⚠ THE LINE NUMBER IS THE POINT OF THE EQUAL-LENGTH BLANKING. If softening changed lengths, a
    # wrapped hit would report the wrong line and send a reader to the wrong place — which is worse
    # than not reporting it, because it looks authoritative.
    print('  MUST FIRE  (line numbers survive softening)')
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / 'x.lean'
        io.open(p, 'w', encoding='utf-8', newline='\n').write(
            'one\ntwo\nthree\n-- The claim: choice enters only\n-- in the analytic realisations.\n')
        hits, _ = sweep_claim([CLAIM], files=[p])
    ok = len(hits) == 1 and hits[0][1] == 4
    bad += 0 if ok else 1
    print('    %-40s %s (line %s, want 4)'
          % ('a wrapped hit reports its OPENING line', 'ok' if ok else '*** WRONG ***',
             hits[0][1] if hits else '-'))

    # ⚠⚠ THE CONTROL THAT WAS MISSING, AND ITS ABSENCE IS WHY THE SKEW SHIPPED. The fixture above has
    # ZERO string-joins above the hit, so it passed while every real build script was reported one
    # line low PER JOIN above the match — up to 347 lines out in `build_zpe.py`. A control whose
    # fixture cannot exhibit the defect is a control that certifies nothing. This one puts joins
    # BEFORE the hit, which is the shape every rendered script actually has.
    print('  MUST FIRE  (line numbers survive JOINS ABOVE the hit)')
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / 'x.py'
        p.write_text(
            "E.append(body(\n    'filler one '\n    'filler two'))\n"
            "E.append(body(\n    'filler three '\n    'filler four'))\n"
            "sp('The claim: choice enters only in the analytic realisations.')\n",
            encoding='utf-8', newline='\n')
        hits, _ = sweep_claim([CLAIM], files=[p])
    ok = len(hits) == 1 and hits[0][1] == 7
    bad += 0 if ok else 1
    print('    %-40s %s (line %s, want 7)'
          % ('two joins above it, line still exact', 'ok' if ok else '*** SKEWED ***',
             hits[0][1] if hits else '-'))

    # An unreadable file must be REPORTED, never silently dropped.
    print('  MUST FIRE  (unreadable file is reported)')
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / 'x.md'
        io.open(p, 'wb').write(b'\xff\xfe\x00 not utf-8 \xff')
        hits, unreadable = sweep_claim([CLAIM], files=[p])
    ok = len(unreadable) == 1
    bad += 0 if ok else 1
    print('    %-40s %s' % ('absence is not claimed over it', 'ok' if ok else '*** DROPPED ***'))

    print('\n  claim-sweep controls: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return bad


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
        return selftest() + selftest_ride_along() + selftest_claim()
    if '--claim' in args:
        phrases = [a for a in args[args.index('--claim') + 1:] if not a.startswith('--')]
        if not phrases:
            print('--claim needs at least one phrase — and prefer two: the claim AND its inverse')
            return 2
        return cmd_claim(phrases, pdfs='--pdf' in args)
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
    # ⚠ REPO-RELATIVE, NOT ABSOLUTE. `tracked_markdown()` / `tracked_lean()` yield absolute paths;
    # handing those to the ledger made every subject read "not present at HEAD" and the record was
    # refused whole. The fence caught it rather than recording nonsense — but the conversion belongs
    # here. pathlib, not os.path: this module never imports `os`.
    def _rel(p):
        try:
            return Path(p).resolve().relative_to(common.REPO).as_posix()
        except ValueError:
            return str(p).replace('\\', '/')

    # ⚠⚠ A SKIPPED CLASS WITHHOLDS THE VERDICT — it never records a PASS. `ci_report.py`'s own header
    # records that scoring a skip as a pass would publish "a GREEN REQUIRED CHECK covering a gate
    # that was skipped". Withheld leaves the key MISSING, which BLOCKS.
    rc = common.record_if_asked(
        'check_paths',
        [_rel(p) for p in tracked_markdown()] + [_rel(p) for p in tracked_lean()],
        {_rel(p) for p, _ln, _ref in list(d1) + list(dl)},
        'a repo-relative reference does not resolve', args,
        switches=['tools/verify/vendored_files.txt'],
        withheld='it skipped a class (Mathlib absent)' if skipped_a_class else None)
    if rc:
        return rc

    if failed:
        return 1
    return EXIT_SKIPPED if skipped_a_class else 0


if __name__ == '__main__':
    sys.exit(main())
