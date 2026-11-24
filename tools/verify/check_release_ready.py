"""
check_release_ready.py - ZP pre-release readiness gate.

Run from the repo ROOT, BEFORE drafting a release body / cutting a tag:

    python check_release_ready.py <tag>      e.g.  v2.7

Exit 0 = all BLOCKING (mechanical) checks pass -> GO, pending the printed
          judgment checklist (editorial/adversary/etc., which a script cannot decide).
Exit 1 = one or more blocking checks failed -> NO-GO.
Exit 2 = usage error.

    python check_release_ready.py --ledger-only [--defects PATH]
runs only the defect-ledger leg (the release rule: no open content BEDROCK / BEDROCK-CANDIDATE
unit and no untagged open unit in DEFECTS.md): exit 0 CLEAR, 1 BLOCKED, 3 UNREADABLE. `--defects`
overrides the ledger path in either mode; by default it is the MAIN checkout's .claude-local.

Design: the deterministic checks are auto-verified and split into
  [FAIL]  blocking, high-confidence, unambiguous;
  [WARN]  best-effort / fragile-to-parse / hygiene -> surfaced, not blocking;
  [INFO]  context.
The judgment items (gates run, companion sync, version-bump decision, release
body approved) are PRINTED for the human to confirm - they are not mechanizable.

Spec + rationale: .claude-local/notes/release_readiness_gate_2026-06-24.md
Reuses check_hashes.py for register parsing + script hashes.
"""

import json
import os
import re
import subprocess
import sys
import glob

# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3), coerced to
# `str` because this module speaks `os.path`.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402
# ⚠ THE ONE REMAINING CHECKER-IMPORTS-A-CHECKER EDGE, AND IT IS DELIBERATE. This is the RELEASE
# gate re-running the HASH gate's own parser rather than a second copy of it: `check_hashes` owns
# `register.md`'s format, and the alternative is two parsers for one file, which is the mirror
# defect this bundle spent its length removing. It is a gate composing a gate, not a checker
# borrowing a peer's text utilities — which is what MIG-3 objected to.
import check_hashes as ch  # noqa: E402  (sha8, parse_register, *_SCRIPTS dicts)
import vendored  # noqa: E402  THE vendored-exemption definition (RR-2); never re-implemented here

HERE = str(common.HERE)
REPO = str(common.REPO)
SELF = common.self_rel(__file__)

REGISTER = 'register.md'
RELEASES = 'RELEASES.md'
REGISTRY = 'LEAN_CUSTOM_REGISTRY.md'
ZENODO = '.zenodo.json'
README = 'README.md'
GUIDE = 'GUIDE.md'
LEAN_GLOB = 'ZeroParadox/**/*.lean'
LOCAL = os.path.join(REPO, '.claude-local')   # signals only; per-push state, still private

fails = []
warns = []


def fail(msg):
    fails.append(msg)


def warn(msg):
    warns.append(msg)


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read()


def git(*args):
    """(returncode, stdout). The code is returned because an UNANSWERED probe is not a clean tree
    (`RLY43-1`): `git grep` outside a repo returned rc=128 with empty stdout, and reading stdout
    alone printed `[PASS] No conflict markers`. `None` means git could not be started at all."""
    try:
        r = subprocess.run(['git', *args], capture_output=True, text=True, cwd=REPO)
    except OSError:
        return None, ''
    return r.returncode, r.stdout


def norm_ver(v):
    return (v or '').strip().lstrip('vV').strip()


# --------------------------------------------------------------------------- checks

# Files that legitimately carry NO Engineer's Take (permanent). EXACT REPO-RELATIVE PATHS.
# Rationale: the Engineer's Take convention covers ZP-X *framework* layers; dev tooling is not
# ZP-original content and carries none by design. Vendored/ported files are exempt through
# `vendored.is_vendored`, never listed here.
# ⚠ (`RR-2`, /rely 2026-11-23) THESE WERE BASENAMES, so a take-less `Basic.lean` or `Snapshot.lean`
# ANYWHERE in the corpus passed. Anchored to the one path each names. `Basic.lean` was dropped: its
# only home, `ZeroParadox/Basic.lean`, was deleted in the v3.0 reorg (004f065a), and an exemption for
# a file that does not exist can only ever exempt a file nobody reviewed. `NaturalOps.lean` and
# `NaturalOpsPow.lean` are vendored.py's (directory and allowlist respectively).
TAKE_EXEMPT = frozenset({
    'ZeroParadox/Meta/ExtractDeps.lean',   # dev tooling ("not framework content" per MANIFEST)
    'ZeroParadox/Meta/Snapshot.lean',      # dev tooling (axiom-footprint snapshot generator)
})
# Files that OWE a take but are explicitly deferred — backlog, NOT exempt. Tolerated as a
# non-blocking WARN, never a silent pass. EXACT REPO-RELATIVE PATHS, for the same reason as above:
# a basename here downgraded a FAIL to a WARN for any file of that name anywhere. Empty since the
# five basenames it held (ZPB_PadicTree, ZPJ_AczelConn, ZPJ_Scale, ZPJ_SelfApp, ZPJ_WheelFrac) no
# longer exist in the corpus. Do NOT add new files here — every new Lean file ships a filled take.
# See .claude-local/notes/deferred_engineers_takes_2026-06-26.md
DEFERRED_TAKES = frozenset()

# The root `LEAN_GLOB` is resolved against and the repo-relative path is computed from. A module
# variable so the selftest can point it at a temp tree that carries the REAL `ZeroParadox/` prefix.
LEAN_ROOT = REPO


def _rel(path):
    return path.replace('\\', '/').lstrip('/')


def take_exempt(rel):
    """True if the repo-relative `rel` owes no take: an exact TAKE_EXEMPT path, or vendored by
    `vendored.is_vendored` - THE definition, imported, never re-implemented (Tim, ruling 81: "The
    "vendored" folder should be overridden as needed... None of it should need a take.").

    ⚠ `RR-2`: this used to test `'Vendored' in parts[:-1]`, a directory of that name at ANY depth,
    so `ZeroParadox/Order/Vendored/X.lean` passed with no take while vendored.py, which anchors the
    exemption to `ZeroParadox/Vendored/` because the nested form was a recorded self-exemption hole,
    said it was not vendored."""
    norm = _rel(rel)
    return norm in TAKE_EXEMPT or vendored.is_vendored(norm)


def _take_has_prose(body):
    """True when a take's body holds real prose.

    ⚠ `TK-1` (/rely 2026-11-24): the old test stripped `--` lines and accepted anything left, so a
    body of only the docstring terminator `-/` - exactly the template once its `TODO (Tim)` line is
    deleted - counted as filled, and so did an empty take followed by Lean code, because the body
    ran on past the `-/` to the next heading or EOF. The body now ENDS at the docstring terminator;
    `--` comment lines, comment delimiters and TODO/TBD/FIXME marker lines are dropped; and what is
    left must contain a word of three or more letters."""
    body = body.split('-/', 1)[0]
    kept = []
    for ln in body.splitlines():
        s = ln.strip()
        if not s or s.startswith('--') or s in ('/-', '/-!', '-/'):
            continue
        if re.match(r'(?i)^[\W_]*(TODO|TBD|FIXME|XXX)\b', s):
            continue
        kept.append(s)
    return bool(re.search(r'[A-Za-z]{3,}', ' '.join(kept)))


def c_engineers_takes():
    """Every ZP-X Lean file carries a filled Engineer's Take.

    Fails on a MISSING section, not only an empty or TODO-flagged one. The
    DEFERRED_TAKES backlog is tolerated as a WARN (owed, not exempt); TAKE_EXEMPT
    files are skipped. The heading match allows both the '## Engineer's Take'
    markdown form and the bare 'Engineer's Take:' form (ZPM).
    """
    hits = []
    # heading + body up to the next markdown heading or EOF; '#' is optional so the
    # bare 'Engineer's Take:' form is recognised too.
    take_re = r'((?:#+\s*)?Engineer.?s Take[^\n]*)\n(.*?)(?=\n#+\s|\Z)'
    for full in glob.glob(os.path.join(LEAN_ROOT, LEAN_GLOB), recursive=True):
        path = _rel(os.path.relpath(full, LEAN_ROOT))
        if '.lake' in path.split('/'):   # a `.lake` DIRECTORY, never a substring of a name
            continue
        if take_exempt(path):
            continue
        txt = read(full)
        for pat in ('TODO (Tim)', 'TODO: Engineer'):
            if pat in txt:
                hits.append(f'{path}: contains "{pat}"')
        if not re.search(r'Engineer.?s Take', txt, re.I):
            # no section at all
            if path in DEFERRED_TAKES:
                warn(f"Engineer's Take deferred (owed, not exempt) - {path}")
            else:
                hits.append(f'{path}: no "Engineer\'s Take" section')
            continue
        for m in re.finditer(take_re, txt, re.S | re.I):
            head = m.group(1).strip()
            # The bare `Engineer's Take: <prose>` form (ZPM) starts its prose on the heading line; a
            # markdown heading's own text is a title, never the take.
            inline = '' if head.startswith('#') else re.sub(r'(?i)^.*?Engineer.?s Take\s*:?', '', head)
            if not _take_has_prose(inline + '\n' + m.group(2)):
                hits.append(f'{path}: empty "{m.group(1).strip()}" section')
    if hits:
        for h in hits:
            fail(f'Engineer\'s Take unfilled - {h}')
    return not hits


def c_hash_integrity():
    """Every recorded build-input hash matches its bytes - all four tiers, plus the shared layer.

    ⚠ **THIS USED TO ITERATE `COMP_SCRIPTS` ALONE AND CALL THAT INTEGRITY** (`RLY5-1`, DC-18 proxy
    check). It was blind to the 10 FORMAL_ONLY scripts, the 3 standalone register tokens, and
    `zp_utils.py` - which all 43 build scripts import and which renders the meta line of every
    document. Measured: `zp_utils.py` moved ALONE gave `check_hashes.py` exit 1 while this printed
    `[PASS] Build-script hash integrity` and the gate said `GO`.

    **The push hook and CI both blocked correctly; only this one was blind - and this is the one whose
    output is a permanent Zenodo DOI.** Now DELEGATES to `check_hashes.all_hash_mismatches()`, which is
    the single definition of the property.

    ⚠ **THE TWO READERS ARE NOT CONTROL-BOUND, AND THIS DOCSTRING CLAIMED THEY WERE.** `hooks.py`
    judges `check_hashes.main()`'s EXIT CODE; this imports `all_hash_mismatches()`. The tier controls
    in `--selftest` cover only the second — measured (/rely round 4): deleting a tier's accumulator
    from `main()` leaves `--selftest` green, and `main()` then PRINTS the mismatch and returns zero.
    Nothing passes through that gap today, so it is ledger debt rather than a live fail-open — but
    the delegation's stated ground was stronger than what exists, which is the same overclaim shape
    this file's own history is full of. Binding them is the mutation harness's first control set.
    A second copy of the logic here is what produced the drift in the first place.
    """
    bad = ch.all_hash_mismatches()
    for b in bad:
        # ⚠ NAME THE ACTUAL REMEDY. One label for two different faults sent readers to the wrong fix:
        # a MISSING provenance token is not staleness, and no amount of bumping or rebuilding closes
        # it — the fix is to add a `formal:` token. (Editorial round 4; the wording is theirs.)
        if 'no formal: token in register.md' in b:
            fail(f'No register provenance token (add a formal: token; do NOT bump or rebuild) - {b}')
        else:
            fail(f'Hash mismatch (version bump/rebuild overdue) - {b}')
    return not bad


def _register_versions():
    """{ZP-X: (formal_ver, comp_ver)} from register.md columns (first-wins, base layer)."""
    out = {}
    for line in read(REGISTER).splitlines():
        if not line.strip().startswith('|'):
            continue
        cols = [c.strip() for c in line.split('|')]
        if len(cols) < 5:
            continue
        m = re.match(r'(ZP-[A-Z])', cols[1])
        if m and m.group(1) not in out:
            out[m.group(1)] = (cols[2], cols[4])
    return out


def _script_version(script):
    """The `VERSION` constant of a build script, or None if it cannot be read.

    ⚠ **THIS READ FROM `.claude-local/`, WHICH HAS HELD NO BUILD SCRIPTS SINCE 2026-08-15**
    (`RLY18-2`). The mirror was retired that day and `scripts/` became the only home, so every lookup
    returned None, `if rv and sv` never fired, and `c_register_vs_script_version` reported
    `[PASS] register <-> script VERSION` having resolved **0 of 26**. Measured live: `VERSION='9.99'`
    against a register row of `v1.21` still printed `[PASS]`.

    Same class as `RLY5-1` in this same file - a check reporting clean over ground it never walked.
    That is now twice here, which is why the caller below asserts a RESOLUTION FLOOR rather than
    trusting that silence means agreement.
    """
    path = os.path.join(ch.SCRIPT_DIR, script)
    if not os.path.exists(path):
        return None
    m = re.search(r"^VERSION\s*=\s*['\"]([^'\"]+)['\"]", read(path), re.M)
    return m.group(1) if m else None


def c_register_vs_script_version():
    """register version columns match each build script's VERSION (best-effort -> WARN)."""
    regv = _register_versions()
    issues = []
    for doc in ch.FORMAL_SCRIPTS:
        base = doc.replace('-formal', '')
        rv = regv.get(base, (None, None))[0]
        sv = _script_version(ch.FORMAL_SCRIPTS[doc])
        if rv and sv and norm_ver(rv) != norm_ver(sv):
            issues.append(f'{base} formal: register "{rv}" vs script "{sv}"')
    for doc in ch.COMP_SCRIPTS:
        rv = regv.get(doc, (None, None))[1]
        sv = _script_version(ch.COMP_SCRIPTS[doc])
        if rv and sv and norm_ver(rv) != norm_ver(sv):
            issues.append(f'{doc} comp: register "{rv}" vs script "{sv}"')

    # ⚠⚠ THE RESOLUTION FLOOR. Every comparison above is guarded by `if rv and sv`, so a script whose
    # VERSION cannot be read is skipped SILENTLY — and when the path was wrong, that was all 26 of
    # them and this still printed `[PASS]` (`RLY18-2`). **A comparison that ran zero times is not a
    # comparison that passed.** Count what actually resolved and fail when the answer is nothing.
    _total = len(ch.FORMAL_SCRIPTS) + len(ch.COMP_SCRIPTS)
    _resolved = sum(1 for s in list(ch.FORMAL_SCRIPTS.values()) + list(ch.COMP_SCRIPTS.values())
                    if _script_version(s) is not None)
    if _resolved == 0:
        fail(f'register<->script VERSION resolved 0 of {_total} build scripts - the check did not '
             f'run at all (bad path?), so its silence means nothing')
        return False
    if _resolved < _total:
        warn(f'register<->script VERSION: only {_resolved} of {_total} scripts had a readable '
             f'VERSION; the rest were skipped silently')

    for i in issues:
        warn(f'register<->script VERSION - {i} (authoritative check: /editorial-review)')
    return not issues


def c_registry_invariant():
    """LEAN_CUSTOM_REGISTRY '### ' entry count == [ZP-CUSTOM] tag count in the Lean sources."""
    entries = len(re.findall(r'(?m)^###\s', read(REGISTRY)))
    tags = 0
    for path in glob.glob(LEAN_GLOB, recursive=True):
        if '.lake' in path.replace('\\', '/'):
            continue
        tags += read(path).count('[ZP-CUSTOM]')
    if entries != tags:
        fail(f'LEAN_CUSTOM_REGISTRY out of sync: {entries} entries vs {tags} [ZP-CUSTOM] tags')
    return entries == tags, entries, tags


def c_zenodo():
    """.zenodo.json is valid JSON; surface the layer-count phrase for human check."""
    try:
        d = json.loads(read(ZENODO))
    except Exception as e:
        fail(f'.zenodo.json invalid JSON: {e}')
        return False, None
    desc = d.get('description', '')
    m = re.search(r'([A-Za-z]+|\d+)\s+formal layers', desc)
    phrase = m.group(0) if m else '(no "N formal layers" phrase found)'
    return True, phrase


def c_conflict_markers():
    """No unresolved git conflict markers in tracked files.

    `git grep -l` answers 0 with matches and 1 with none; any other code is a probe that did not
    answer, and it FAILS CLOSED rather than reading as a clean tree."""
    rc, out = git('grep', '-lE', r'^(<<<<<<<|>>>>>>>)')
    if rc not in (0, 1):
        fail('Conflict-marker probe did not answer (git grep exit %s) - NOT evidence of a clean '
             'tree' % rc)
        return False
    files = [f for f in out.splitlines() if f.strip()]
    if files:
        for f in files:
            fail(f'Conflict marker present in {f}')
    return not files


def c_releases_entry(tag):
    """RELEASES.md contains a '## <tag>' header for the version being cut."""
    txt = read(RELEASES)
    if re.search(r'(?m)^##\s+' + re.escape(tag) + r'\b', txt):
        return True
    fail(f'RELEASES.md has no "## {tag}" entry')
    return False


def c_doc_links():
    """Every PDF linked from README/GUIDE exists in the repo; em-dashes flagged."""
    ok = True
    for f in (README, GUIDE):
        if not os.path.exists(f):
            warn(f'{f} not found')
            continue
        txt = read(f)
        for m in re.finditer(r'\[[^\]]*\]\(([^)]+\.pdf)\)', txt):
            target = m.group(1).split('#')[0]
            if target.startswith('http'):
                continue
            if not os.path.exists(target):
                fail(f'{f}: linked PDF missing -> {target}')
                ok = False
        if '—' in txt:
            warn(f'{f}: contains em-dash (U+2014) - use hyphens (editorial enforces)')
    return ok


def c_scripts_mirror():
    """RETIRED 2026-08-15 — there is no mirror left to check, so the check is a deletion.

    This used to WARN when `scripts/build_X.py` had drifted from its `build_X.py`
    source. The honest reading of that check is that it existed to police a hazard the LAYOUT
    created: two live copies with a per-commit hand-copy obligation between them. It also could
    not do its job — only the private copy was fingerprinted in register.md, so the published copy
    was outside the integrity check, and `scan_pdfs.py` drifted for three months undetected.

    `scripts/` is now the single home. A stale mirror is not something to warn about; it is
    something that can no longer exist. Kept as a named no-op so the check list stays legible and
    nobody re-adds it — deleting the mirror is what closed the class."""
    return True


REVIEW_STEPS = ('editorial', 'adversary', 'claim_review', 'prior_art', 'rely')


def c_signals(tag):
    """Review coverage at HEAD, read from the verdictLedger (INFO — see the caution below).

    ⚠⚠ THIS READ `.claude-local/{er,ar,cr,pa}_cleared.txt` UNTIL 2026-09-01, AND THOSE FILES ARE
    DEAD. The `*_cleared.txt` scheme was RETIRED 2026-08-24; coverage is a ledger RECORD now.
    Nothing has written those paths since, but `er_cleared.txt` and `ar_cleared.txt` are STILL ON
    DISK, dated the day of the retirement — so this printed `er: !=HEAD (a1b2c3d4)`, which reads
    as *a signal exists and is stale* rather than *this mechanism no longer exists*. It sat two
    lines above the judgment checklist item "Editorial + adversary review ran on all touched
    prose", which is the exact confirmation a human makes here, and a release mints a permanent
    DOI. A gauge sourced from a retired mechanism, at the one moment it is read hardest.

    ⚠ `None` FROM `owing_paths` MEANS COULD-NOT-ASK, NEVER ZERO — it refuses on an unreachable
    ledger AND on a truncated list. It is reported as UNKNOWN and said in words not to be
    coverage; an unreachable ledger reading as clean is the absence-as-success shape this whole
    layer exists to remove. NOT-APPLICABLE is a THIRD answer and is kept distinct: a step whose
    registry `actions` exclude `tag` is a push obligation, and `coverage_gap` returns no row for
    it, which arrives here as the same `None`. Collapsing the two would report `prior_art` as an
    unknown at every release when it is simply not a release obligation.

    ⚠ STILL INFO, DELIBERATELY. Making a non-zero count block would change what a release
    REQUIRES — `rely` reports 87 owing as of 2026-09-01 — and that is Tim's call under R-RELEASE,
    not a correction to smuggle in beside one. The rows are honest; the policy is unchanged."""
    rows = []
    try:
        import record  # same directory; sys.path already primed at import time
    except ImportError as exc:
        return [f'UNKNOWN - cannot import record.py ({exc}) - this is NOT evidence of coverage']
    try:
        reg = json.loads(read(os.path.join(HERE, 'required.v2.json'))).get('types', {})
    except (OSError, ValueError):
        reg = {}
    for step in REVIEW_STEPS:
        acts = reg.get(step, {}).get('actions')
        if acts is not None and 'tag' not in acts:
            rows.append(f'{step}: n/a at tag (registry actions={acts or []}) - a push obligation')
            continue
        owing = record.owing_paths(step, 'HEAD', action='tag')
        if owing is None:
            rows.append(f'{step}: UNKNOWN - could not ask the ledger. NOT evidence of coverage')
        elif owing:
            rows.append(f'{step}: {len(owing)} path(s) owing at HEAD (first: {owing[0]})')
        else:
            rows.append(f'{step}: covered at HEAD')
    return rows


def c_untracked_pdfs():
    """Untracked PDFs in the repo root (the ZP_Reals_Companion.pdf class) -> WARN."""
    rc, out = git('status', '--porcelain')
    if rc != 0:
        warn('untracked-PDF probe did not answer (git status exit %s) - NOT evidence of none' % rc)
        return False
    pdfs = []
    for line in out.splitlines():
        if line.startswith('??'):
            path = line[3:].strip()
            if path.lower().endswith('.pdf') and '/' not in path.replace('\\', '/'):
                pdfs.append(path)
    for p in pdfs:
        warn(f'untracked PDF in root: {p} (archive / finish / .gitignore?)')
    return not pdfs


# --------------------------------------------------------------------------- the defect ledger
#
# The release rule (Tim, 2026-10-08, made permanent 2026-10-30): a release blocks only on OPEN
# `DEFECTS.md` units tagged CONTENT and BEDROCK (BEDROCK-CANDIDATE included, until graded). Content
# is what ships: the root PDFs and the prose of `scripts/build_*.py`, `ZeroParadox/**`, root `.md`,
# `.zenodo.json`, the HTML pages. ORDINARY content findings ship as public erratum issues; tooling,
# published-process (`.claude/commands/**`) entries and Tim-gated questions do not block.
#
# The open-unit test is the one printed in DEFECTS.md's own header, applied verbatim: a heading
# (`##` to `######`) is open if it carries the word OPEN (or REOPENED) and none of the closing words,
# or a withdrawn closure, or says PARTLY CLOSED / still OPEN; a table row whose first cell is a bold
# or backticked id is judged by the same test over its first two cells. An open unit whose tag cannot be read cannot be graded, so it
# FAILS CLOSED rather than being folded into a bucket.
#
# ⚠⚠ `RR-1` / `RR-1b` (/rely 2026-11-23, 2026-11-24) - AND WHY THIS LEG NO LONGER READS PROSE.
# The first fix judged closure from the line's prose: its first status word plus a list of withdrawal
# phrasings. Nine mutants walked past it the next day (`NOT **CLOSED**`, `was CLOSED, now OPEN`,
# `CLOSED in error`, `## RESOLVED-STATE-1 - OPEN`, ...). Every list of the ways "closed" can be negated
# is an ENUMERATION and misses the next phrasing (R-NOCONV), so the SHAPE changed: a release-blocking
# line is closed only when its TAG carries the closure token, and no prose is read for its status.
#
#   CLOSURE TOKEN: `[content · BEDROCK · CLOSED YYYY-MM-DD]` (also BEDROCK-CANDIDATE / BEDROCK-class).
#   Single spaces around each `·`, uppercase CLOSED, one real calendar date. Anything else is OPEN.
#
# A third tag segment that is not exactly that token is MALFORMED and blocks with its own message. A
# bracketed span naming BEDROCK that does not read as a tag at all is UNREADABLE and blocks as an
# untagged unit (`RR-1c`). An unbalanced code fence blocks too, since it hides the rest of the ledger
# (`RR-1d`). The general open test below (counts, untagged units) keeps its OPEN-word trigger.

DEFECTS_REL = os.path.join('.claude-local', 'DEFECTS.md')
# The closing words of DEFECTS.md's header rule, for the GENERAL open test only (`_is_open`). The
# release-blocking leg never consults them.
CLOSED_FORMS = ('CLOSED', 'WITHDRAWN', 'RESOLVED', 'RETRACTED', 'SUPERSEDED', 'DISCHARGED')
CLOSING_WORDS = CLOSED_FORMS + ('ACCEPTED',)
# The closure token, matched against the tag's severity part (everything after the kind's `·`).
_CLOSURE = re.compile(r'^(BEDROCK(?:-CANDIDATE|-class)?) · CLOSED (\d{4}-\d{2}-\d{2})$')
# Any bracketed span naming BEDROCK, whatever its case or separators: each must read as a tag.
_BEDROCK_SPAN = re.compile(r'\[[^\[\]\n]*bedrock[^\[\]\n]*\]', re.I)
# Withdrawn closures, for the GENERAL open test only.
_UNCLOSE = re.compile(r'\b(?:NOT|NEVER)\s+(?:YET\s+)?(?:%s)\b|\bRE-?OPEN|\bPARTLY\s+CLOSED\b|\bstill\s+OPEN\b'
                      % '|'.join(CLOSED_FORMS), re.I)
_HEADING = re.compile(r'^(#{2,6})\s+(.*)$')
_ROW = re.compile(r'^\|\s*(\*\*[^*|]+\*\*|`[^`|]+`)\s*\|([^|]*)\|')
_TAG = re.compile(r'\[([a-z][a-z+-]*)\s*·\s*([^\]]+)\]')
_SEVERITIES = ('BEDROCK', 'BEDROCK-CANDIDATE', 'ORDINARY')
_KINDS = ('content', 'tooling', 'published-process')

# R-ZERONULL: three distinct VALUES, never one value with three messages.
LEDGER_CLEAR = 'CLEAR'          # read, and no open content bedrock / untagged unit
LEDGER_BLOCKED = 'BLOCKED'      # read, and at least one blocking unit
LEDGER_UNREADABLE = 'UNREADABLE'  # not read at all; NOT evidence of a clear ledger


def defects_path():
    """(path, how) - DEFECTS.md in the MAIN checkout's `.claude-local`.

    `.claude-local` is its own gitignored repository, so a worktree does not carry it; the main
    checkout is the parent of the shared git directory, which is the same answer from either. `None`
    for the path means the location could not be derived, and the caller reports it as UNREADABLE."""
    rc, out = git('rev-parse', '--path-format=absolute', '--git-common-dir')
    if rc == 0 and out.strip():
        main_root = os.path.dirname(os.path.normpath(out.strip()))
        return os.path.join(main_root, DEFECTS_REL), 'main checkout (from the shared git dir)'
    return None, 'main checkout could not be derived (rev-parse exit %s)' % rc


def _closure(tag_sev):
    """The closure state of one tag's severity part: 'closed', 'open' or 'malformed'.

    'closed' ONLY for the exact token (`BEDROCK · CLOSED 2026-11-24`, a real date). A severity with no
    further segment is 'open'. Any further segment that is not exactly the token - a lowercase
    `closed`, a missing or impossible date, a second word, a `-` for the `·` - is 'malformed', which
    blocks like 'open' and is reported separately so it can be fixed rather than mistaken for a
    status."""
    import datetime
    s = tag_sev.strip()
    if '·' not in s and not re.search(r'\bclosed\b', s, re.I):
        return 'open'
    m = _CLOSURE.match(s)
    if not m:
        return 'malformed'
    try:
        datetime.date.fromisoformat(m.group(2))
    except ValueError:
        return 'malformed'
    return 'closed'


def _blocking_tags(text):
    """(open_or_malformed, unreadable) for one line - the release-blocking leg's whole input.

    `open_or_malformed`: [(grade, state)] for each CONTENT BEDROCK / BEDROCK-CANDIDATE tag on the line
    that does not carry the closure token. `unreadable`: bracketed spans naming BEDROCK that do not
    read as a tag. The line's PROSE is never consulted: only the tags."""
    hits, readable = [], set()
    for m in _TAG.finditer(text):
        g = _grade(m.group(1), m.group(2))
        if g is None:
            continue
        readable.add(m.span())
        if _blocks_release(g):
            st = _closure(m.group(2))
            if st != 'closed':
                hits.append((g, st))
    unreadable = [s.group(0) for s in _BEDROCK_SPAN.finditer(text) if s.span() not in readable]
    return hits, unreadable


def _is_open(text):
    """The general open-unit test (counts, untagged units) - DEFECTS.md header's rule, verbatim,
    plus one widening: a closing word that is withdrawn (`NOT CLOSED`, `REOPENED`, ...) no longer
    reads as closure.

    ⚠ NOT the RR-1 allow-list. Applying "not provably closed" here was measured against the live
    ledger 2026-11-23 and turned 78 untagged tooling headings and rows into release blockers: ids
    such as `ZPJK-OQE2-OPEN-1` put OPEN before CLOSED, and later table cells carry prose. The
    release-blocking grade is fail-closed in `scan_defects`; an UNTAGGED unit that never says OPEN
    or REOPENED is still not seen here, and that residual is recorded, not hidden."""
    if 'PARTLY CLOSED' in text or re.search(r'\bstill OPEN\b', text):
        return True
    if not re.search(r'\bOPEN\b|\bRE-?OPENED\b', text):
        return False
    if _UNCLOSE.search(text):
        return True
    return not any(re.search(r'\b%s\b' % w, text) for w in CLOSING_WORDS)


def _blocks_release(g):
    return g is not None and g[0] == 'content' and g[1] in ('BEDROCK', 'BEDROCK-CANDIDATE')


def _grade(tag_kind, tag_sev):
    """(kind, severity) for one tag, or None if either half is unreadable.

    Kind: anything naming `content` (`content+tooling` included) is content, because content is what
    ships and the worse reading wins; `published-process` is itself; `tooling` and the bare `process`
    are tooling (the ruling: tooling is everything else). Severity: any BEDROCK-prefixed grade is
    bedrock (`BEDROCK-class` included), CANDIDATE kept apart; any ORDINARY-prefixed grade is ordinary
    (`ORDINARY (recorded BLOCKING)` included - the audit's scale has no BLOCKING grade)."""
    k = tag_kind.strip()
    if 'content' in k.split('+'):
        kind = 'content'
    elif k == 'published-process':
        kind = 'published-process'
    elif k in ('tooling', 'process'):
        kind = 'tooling'
    else:
        return None
    s = tag_sev.strip().upper()
    if s.startswith('BEDROCK'):
        sev = 'BEDROCK-CANDIDATE' if s.startswith('BEDROCK-CANDIDATE') or s.startswith('BEDROCK CANDIDATE') \
            else 'BEDROCK'
    elif s.startswith('ORDINARY'):
        sev = 'ORDINARY'
    else:
        return None
    return kind, sev


def _rank(g):
    """Lower is more blocking: a release-blocking grade first, then by severity, content first."""
    blocks = g[0] == 'content' and g[1] != 'ORDINARY'
    return (not blocks, _SEVERITIES.index(g[1]), g[0] != 'content')


def _unit_grade(text):
    """The most blocking readable tag in `text`, or None when no tag reads."""
    grades = [g for g in (_grade(m.group(1), m.group(2)) for m in _TAG.finditer(text)) if g]
    return min(grades, key=_rank) if grades else None


def scan_defects(text):
    """{'units': [(line_no, kind, sev, label)], 'untagged': [(line_no, label)],
    'malformed': [(line_no, label)]} over open units.

    `malformed` lines are ALSO in `units` (they block as open content bedrock); the list exists so
    the report can say the closure token was attempted and is wrong, rather than calling it open."""
    units, untagged, malformed = [], [], []
    fence, fence_at = False, 0
    for n, raw in enumerate(text.splitlines(), 1):
        ln = raw.rstrip()
        if ln.lstrip().startswith('```'):
            fence, fence_at = (not fence), n
            continue
        if fence:
            continue
        hits, unreadable = _blocking_tags(ln)
        m = _HEADING.match(ln)
        r = None if m else _ROW.match(ln)
        label = (m.group(2) if m else r.group(1) if r else ln.strip()).strip()[:90]
        if unreadable:
            # RR-1c: a span naming BEDROCK that does not read as a tag cannot be graded or closed.
            untagged.append((n, 'unreadable bedrock tag %s - %s' % (unreadable[0][:40], label)))
            continue
        if hits:
            # RR-1b: a release-blocking tag WITHOUT the closure token is open, whatever the prose says
            # and whatever the line's shape. The most blocking open tag on the line is the unit.
            g, st = min(hits, key=lambda h: _rank(h[0]))
            units.append((n, g[0], g[1], label))
            if any(s == 'malformed' for _, s in hits):
                malformed.append((n, label))
            continue
        g = _unit_grade(ln)
        if _blocks_release(g):
            continue   # every release-blocking tag on the line carries the closure token
        if m or r:
            judged = m.group(2) if m else r.group(1) + ' | ' + r.group(2)
            if not _is_open(judged):
                continue
            label = m.group(2) if m else r.group(1)
        else:
            continue
        label = label.strip()[:90]
        if g is None:
            untagged.append((n, label))
        else:
            units.append((n, g[0], g[1], label))
    if fence:
        # RR-1d: an unclosed fence hid every line after it, so nothing below it was graded.
        untagged.append((fence_at, 'unbalanced ``` fence opened here hides the rest of the ledger'))
    return {'units': units, 'untagged': untagged, 'malformed': malformed}


def c_defects_ledger(path=None):
    """The release rule, mechanically. Returns (status, detail, counts, path_read).

    `status` is one of LEDGER_CLEAR / LEDGER_BLOCKED / LEDGER_UNREADABLE. A missing or unreadable
    ledger is UNREADABLE - a distinct value from CLEAR, failing the gate with its own message,
    because an absent list of defects is not a list with no defects in it."""
    how = 'given on the command line'
    if path is None:
        path, how = defects_path()
    if path is None:
        fail('Defect ledger UNREADABLE - %s; a release cannot be graded without it' % how)
        return LEDGER_UNREADABLE, how, None, None
    try:
        text = read(path)
    except (OSError, UnicodeDecodeError) as exc:
        fail('Defect ledger UNREADABLE - %s (%s): %s. This is NOT a clear ledger'
             % (path, how, exc.__class__.__name__))
        return LEDGER_UNREADABLE, str(exc), None, path
    res = scan_defects(text)
    counts = {(k, s): 0 for k in _KINDS for s in _SEVERITIES}
    for _, k, s, _ in res['units']:
        counts[(k, s)] += 1
    counts['untagged'] = len(res['untagged'])
    blocking = [u for u in res['units'] if u[1] == 'content' and u[2] in ('BEDROCK', 'BEDROCK-CANDIDATE')]
    bad_token = {n for n, _ in res['malformed']}
    for n, k, s, label in blocking:
        fail('Open content %s defect (DEFECTS.md:%d)%s - %s' % (
            s, n, ' - closure token MALFORMED, the one closed form is [content · %s · CLOSED '
            'YYYY-MM-DD]' % s if n in bad_token else '', label))
    if blocking:
        warn('a content bedrock unit is CLOSED only by its tag: [content · BEDROCK · CLOSED '
             'YYYY-MM-DD]. Prose status words are not read.')
    for n, label in res['untagged']:
        fail('Open defect with no readable [kind · SEVERITY] tag (DEFECTS.md:%d) - cannot be graded, '
             'so it blocks - %s' % (n, label))
    for n, k, s, label in res['units']:
        if k != 'content' and s != 'ORDINARY':
            warn('Open %s %s defect (DEFECTS.md:%d, does not block a release) - %s' % (k, s, n, label))
    ordc = counts[('content', 'ORDINARY')]
    if ordc:
        warn('%d open ORDINARY content defect(s) - owed as public erratum issues (or fixes), not a '
             'release blocker' % ordc)
    status = LEDGER_BLOCKED if (blocking or res['untagged']) else LEDGER_CLEAR
    detail = '%d blocking (content bedrock %d, untagged %d)' % (
        len(blocking) + len(res['untagged']), len(blocking), len(res['untagged']))
    return status, detail, counts, path


def print_defect_counts(counts):
    print('    open units by kind x severity (the rule in DEFECTS.md\'s header):')
    print('      %-18s %8s %18s %9s %6s' % ('kind', 'BEDROCK', 'BEDROCK-CANDIDATE', 'ORDINARY', 'total'))
    grand = 0
    for k in _KINDS:
        row = [counts[(k, s)] for s in _SEVERITIES]
        grand += sum(row)
        print('      %-18s %8d %18d %9d %6d' % (k, row[0], row[1], row[2], sum(row)))
    print('      %-18s %8s %18s %9s %6d' % ('untagged', '', '', '', counts['untagged']))
    print('      %-18s %8s %18s %9s %6d' % ('all open units', '', '', '', grand + counts['untagged']))


# --------------------------------------------------------------------------- runner

def line(status, name, detail=''):
    print(f'  [{status:4}] {name}{("  - " + detail) if detail else ""}')


def selftest():
    """MUST-FIRE and MUST-SUPPRESS controls on the release gate's decidable parts.

    Added 2026-08-15 for the Phase 1 exit. This gate is PROCEDURAL — no git event fires on tag
    creation, so nothing runs it automatically and a broken check here is invisible until a release
    is being cut, which is the worst moment to discover it.

    Scope is honest and narrow: the mechanically decidable helpers, plus the two structural facts a
    release depends on. It does NOT simulate a whole release; the judgement checklist this gate
    prints is not mechanizable and is not pretended to be."""
    bad = 0

    print('  MUST FIRE')
    # An absent tag must be NO-GO, never a silent pass.
    txt = read(RELEASES)
    ghost = 'v99.99'
    ok = ('## %s' % ghost) not in txt
    bad += 0 if ok else 1
    print('    %-34s %s' % ('an unknown tag has no RELEASES row', 'ok' if ok else '*** WRONG ***'))

    # A version mismatch must compare unequal after normalisation.
    ok = norm_ver('v1.2') != norm_ver('1.3')
    bad += 0 if ok else 1
    print('    %-34s %s' % ('differing versions compare unequal', 'ok' if ok else '*** WRONG ***'))

    print('  MUST SUPPRESS')
    # Normalisation must NOT invent a difference across the forms actually used in register.md.
    ok = norm_ver('v1.2') == norm_ver('1.2') == norm_ver(' V1.2 ')
    bad += 0 if ok else 1
    print('    %-34s %s' % ('v-prefix/space/case normalise equal', 'ok' if ok else '*** WRONG ***'))

    # The files this gate reads must exist; a missing one would make every check vacuous.
    missing = [f for f in (REGISTER, RELEASES, REGISTRY, ZENODO, README, GUIDE)
               if not os.path.exists(os.path.join(REPO, f))]
    ok = not missing
    bad += 0 if ok else 1
    print('    %-34s %s%s' % ('every input file exists', 'ok' if ok else '*** MISSING ***',
                              '' if ok else ' ' + ', '.join(missing)))

    # ⚠ The retired mirror check must stay a no-op returning True. If someone "restores" it, it
    # would compare scripts/ against a .claude-local/ that no longer holds build scripts and warn
    # on all 43 forever.
    ok = c_scripts_mirror() is True
    bad += 0 if ok else 1
    print('    %-34s %s' % ('the retired mirror check is inert', 'ok' if ok else '*** REVIVED ***'))

    # RLY43-1: an unanswered git probe is NOT a clean tree. Driven through the shipping functions
    # with `git` replaced, so the control reads the same return-code branch the release gate runs.
    print('  PROBE ANSWERS (MUST FIRE on an unanswered probe, MUST SUPPRESS on a clean answer)')
    global git
    real_git = git
    saved = (fails[:], warns[:])
    try:
        for label, fn, answer, want in (
                ('conflict probe rc=128 fails', c_conflict_markers, (128, ''), False),
                ('conflict probe not started fails', c_conflict_markers, (None, ''), False),
                ('conflict markers found fail', c_conflict_markers, (0, 'a.md\n'), False),
                ('conflict probe rc=1 is clean', c_conflict_markers, (1, ''), True),
                ('status probe rc=128 warns', c_untracked_pdfs, (128, ''), False),
                ('status probe clean passes', c_untracked_pdfs, (0, ''), True)):
            git = lambda *_a, _ans=answer: _ans
            got = fn()
            ok = got is want
            bad += 0 if ok else 1
            print('    %-34s %s' % (label, 'ok' if ok else '*** got %s ***' % got))
    finally:
        git = real_git
        fails[:], warns[:] = saved

    # The release rule's open-unit and grade reading, over in-memory ledgers.
    print('  DEFECT LEDGER (MUST FIRE on content bedrock / untagged, MUST SUPPRESS the rest)')

    def _blocks(text):
        r = scan_defects(text)
        return bool(r['untagged']) or any(k == 'content' and s != 'ORDINARY' for _, k, s, _ in r['units'])
    T = '[content · BEDROCK]'
    TC = '[content · BEDROCK · CLOSED 2026-11-24]'
    # want: True = blocks, False = passes, 'malformed' = blocks AND is reported as a bad token.
    ledger_controls = (
            ('open content BEDROCK blocks', '## X-1 - **OPEN** `%s`\n' % T, True),
            ('open BEDROCK-class blocks', '#### X-2 OPEN `[content · BEDROCK-class]`\n', True),
            ('open content CANDIDATE blocks', '## X-3 OPEN [content · BEDROCK-CANDIDATE]\n', True),
            ('open untagged heading blocks', '## X-4 - **OPEN 2026-10-31**\n', True),
            ('open bedrock table row blocks', '| **X-5** | OPEN | f `%s` |\n' % T, True),
            ('PARTLY CLOSED bedrock blocks', '## X-6 PARTLY CLOSED %s\n' % T, True),
            ('open content ORDINARY passes', '## X-8 OPEN [content · ORDINARY]\n', False),
            ('open tooling BEDROCK passes', '## X-9 OPEN [tooling · BEDROCK]\n', False),
            ('fenced heading is not a unit', '```\n## X-10 OPEN\n```\n', False),
            # RR-1 (2026-11-23) mutants.
            ('RR-1 OPEN, not yet RESOLVED', '## X-11 OPEN, not yet RESOLVED %s\n' % T, True),
            ('RR-1 fix ACCEPTED, not merged', '## X-12 OPEN - fix ACCEPTED by Tim, not merged %s\n' % T, True),
            ('RR-1 REOPENED', '## X-13 REOPENED 2026-11-22 %s\n' % T, True),
            ('RR-1 lowercase open', '## X-14 open %s\n' % T, True),
            ('RR-1 level-6 heading', '###### X-15 OPEN %s\n' % T, True),
            ('RR-1 bullet', '- **X-16** OPEN %s\n' % T, True),
            ('RR-1 status in third cell', '| **X-17** | f | OPEN `%s` |\n' % T, True),
            ('RR-1 REMEDIATED, NOT CLOSED', '## X-18 REMEDIATED AT 3c7fe97, NOT CLOSED %s\n' % T, True),
            ('RR-1 no status word at all', '## X-19 something %s\n' % T, True),
            ('RR-1 CLOSED then REOPENED', '## X-20 CLOSED 2026-11-01, REOPENED %s\n' % T, True),
            ('RR-1 lowercase closed', '## X-21 closed %s\n' % T, True),
            ('RR-1 bedrock prose line', 'note: still pending `[content · BEDROCK-CANDIDATE]`\n', True),
            ('RR-1 untagged REOPENED blocks', '## X-26 REOPENED 2026-11-22\n', True),
            ('RR-1 untagged OPEN, NOT CLOSED blocks', '## X-27 OPEN, NOT CLOSED\n', True),
            # RR-1b (2026-11-24) mutants: each passed the prose-reading fix.
            ('RR-1b closed word in the id', '## RESOLVED-STATE-1 - OPEN %s\n' % T, True),
            ('RR-1b closed word in the title', '## X SUPERSEDED theorem still cited - OPEN %s\n' % T, True),
            ('RR-1b closed word in a row id', '| **CLOSED-FORM-1** | OPEN | f %s |\n' % T, True),
            ('RR-1b NOT **CLOSED**', '## X-30 NOT **CLOSED** %s\n' % T, True),
            ('RR-1b was CLOSED, now OPEN', '## X-31 was CLOSED 2026-10-01, now OPEN again %s\n' % T, True),
            ('RR-1b CLOSED in error', '## X-32 CLOSED in error %s\n' % T, True),
            ('RR-1b closure withdrawn', '## X-33 CLOSED (closure withdrawn 2026-11-02) %s\n' % T, True),
            ('RR-1b CLOSED -> OPEN', '## X-34 CLOSED -> OPEN %s\n' % T, True),
            ('RR-1b UN-CLOSED', '## X-35 UN-CLOSED %s\n' % T, True),
            # A prose closure with no token is OPEN now, in every shape the live ledger used.
            ('prose CLOSED heading blocks', '## X-7 **CLOSED** (was OPEN) %s\n' % T, True),
            ('prose CLOSED row blocks', '| `X-23` | **CLOSED 2026-11-21** (fix abc) `%s` | f |\n' % T, True),
            ('prose WITHDRAWN bullet blocks', '- **X-24** WITHDRAWN %s\n' % T, True),
            # RR-1c: a near-miss tag cannot be graded, so it blocks as untagged.
            ('RR-1c capitalised kind', '## X-40 FIXED pending merge [Content · BEDROCK]\n', True),
            ('RR-1c dot-operator separator', '## X-41 NOT CLOSED [content ⋅ BEDROCK]\n', True),
            ('RR-1c hyphen separator', '## X-42 CLOSED [content - BEDROCK]\n', True),
            # RR-1d: an unbalanced fence hides the rest of the ledger.
            ('RR-1d unbalanced fence', '```\n## X-43 OPEN %s\n' % T, True),
            # THE closure token passes, in every line shape and every release-blocking grade.
            ('token heading passes', '## X-50 anything at all, even OPEN `%s`\n' % TC, False),
            ('token row passes', '| `X-51` | OPEN | f `%s` |\n' % TC, False),
            ('token bullet passes', '- **X-52** %s\n' % TC, False),
            ('token CANDIDATE passes', '## X-53 [content · BEDROCK-CANDIDATE · CLOSED 2026-11-24]\n', False),
            ('token BEDROCK-class passes', '## X-54 [content · BEDROCK-class · CLOSED 2026-11-24]\n', False),
            ('token beside an open bedrock blocks', '## X-55 %s %s\n' % (TC, T), True),
            # A malformed closure token blocks and is named as malformed.
            ('malformed lowercase closed', '## X-60 [content · BEDROCK · closed 2026-11-24]\n', 'malformed'),
            ('malformed no date', '## X-61 [content · BEDROCK · CLOSED]\n', 'malformed'),
            ('malformed impossible date', '## X-62 [content · BEDROCK · CLOSED 2026-13-40]\n', 'malformed'),
            ('malformed trailing words', '## X-63 [content · BEDROCK · CLOSED 2026-11-24 again]\n',
             'malformed'),
            ('malformed double space', '## X-64 [content · BEDROCK ·  CLOSED 2026-11-24]\n', 'malformed'),
            ('malformed hyphen before CLOSED', '## X-65 [content · BEDROCK - CLOSED 2026-11-24]\n',
             'malformed'),
            ('malformed other status word', '## X-66 [content · BEDROCK · RESOLVED 2026-11-24]\n',
             'malformed'),
            ('malformed short date', '## X-67 [content · BEDROCK · CLOSED 2026-11]\n', 'malformed'))
    for label, text, want in ledger_controls:
        got = _blocks(text)
        if want == 'malformed':
            ok = got is True and bool(scan_defects(text)['malformed'])
        else:
            ok = got is want
        bad += 0 if ok else 1
        print('    %-36s %s' % (label, 'ok' if ok else '*** WRONG ***'))
    saved = (fails[:], warns[:])
    try:
        st = c_defects_ledger(os.path.join(HERE, 'no-such-dir', 'DEFECTS.md'))[0]
    finally:
        fails[:], warns[:] = saved
    ok = st == LEDGER_UNREADABLE and st != LEDGER_CLEAR
    bad += 0 if ok else 1
    print('    %-34s %s' % ('missing ledger is UNREADABLE', 'ok' if ok else '*** got %s ***' % st))

    # Ruling 81: a take-less file in THE vendored directory passes; a take-less file elsewhere still
    # fails. Driven through c_engineers_takes over a temp tree carrying the real `ZeroParadox/`
    # prefix, so the exemption is RUN on the repo-relative path vendored.py anchors to.
    print('  ENGINEER\'S TAKE (MUST SUPPRESS the anchored exemptions, MUST FIRE elsewhere)')
    import tempfile
    global LEAN_ROOT
    real_root = LEAN_ROOT
    saved = (fails[:], warns[:])
    try:
        with tempfile.TemporaryDirectory() as td:
            for i, (label, rel, want) in enumerate((
                    ('take-less Vendored file passes', 'ZeroParadox/Vendored/X.lean', True),
                    ('take-less allowlisted file passes', 'ZeroParadox/Ordinal/NaturalOpsPow.lean', True),
                    ('take-less Meta/Snapshot passes', 'ZeroParadox/Meta/Snapshot.lean', True),
                    ('take-less Meta/ExtractDeps passes', 'ZeroParadox/Meta/ExtractDeps.lean', True),
                    ('take-less non-vendored file fails', 'ZeroParadox/Order/X.lean', False),
                    # RR-2 mutants: each passed before the fix.
                    ('RR-2 nested Vendored/ fails', 'ZeroParadox/Order/Vendored/X.lean', False),
                    ('RR-2 Basic.lean anywhere fails', 'ZeroParadox/Order/Basic.lean', False),
                    ('RR-2 Snapshot.lean elsewhere fails', 'ZeroParadox/Order/Snapshot.lean', False),
                    ('RR-2 ExtractDeps elsewhere fails', 'ZeroParadox/Order/ExtractDeps.lean', False),
                    ('RR-2 NaturalOps.lean elsewhere fails', 'ZeroParadox/Order/NaturalOps.lean', False),
                    ('RR-2 old deferred basename fails', 'ZeroParadox/Order/ZPJ_Scale.lean', False),
                    ('.lake substring is not exempt', 'ZeroParadox/Order/P.lakeside.lean', False))):
                d = os.path.join(td, str(i))
                os.makedirs(os.path.dirname(os.path.join(d, rel)))
                with open(os.path.join(d, rel), 'w', encoding='utf-8') as f:
                    f.write('theorem t : True := trivial\n')
                LEAN_ROOT = d
                fails[:] = []
                got = c_engineers_takes()
                ok = got is want and (want or bool(fails))
                bad += 0 if ok else 1
                print('    %-36s %s' % (label, 'ok' if ok else '*** got %s ***' % got))
            # TK-1: a take counts as filled only when its body holds real prose.
            H = "/-!\n# E\n\n## Engineer's Take\n"
            CODE = 'theorem t : True := trivial\n'
            for j, (label, body, want) in enumerate((
                    ('TK-1 body only -/ fails', H + '-/\n', False),
                    ('TK-1 empty take then code fails', H + '-/\n' + CODE, False),
                    ('TK-1 whitespace only fails', H + '   \n\t\n-/\n' + CODE, False),
                    ('TK-1 TODO marker only fails', H + 'TODO\n-/\n' + CODE, False),
                    ('TK-1 TBD comment only fails', H + '-- TBD\n-/\n' + CODE, False),
                    ('TK-1 punctuation only fails', H + '...\n-/\n' + CODE, False),
                    ('TK-1 bare form, empty, fails', "/-! Engineer's Take:\n-/\n" + CODE, False),
                    ('TK-1 titled heading, empty, fails', "/-!\n## Engineer's Take - ZP-A layer\n-/\n" + CODE,
                     False),
                    ('TK-1 filled take passes',
                     H + 'The order has a least element and nothing sits below it.\n-/\n' + CODE, True),
                    ('TK-1 bare form, inline, passes',
                     "/-! Engineer's Take: the snap is a one-way step.\n-/\n" + CODE, True))):
                d = os.path.join(td, 'tk%d' % j)
                rel = 'ZeroParadox/Order/Take.lean'
                os.makedirs(os.path.dirname(os.path.join(d, rel)))
                with open(os.path.join(d, rel), 'w', encoding='utf-8') as f:
                    f.write(body)
                LEAN_ROOT = d
                fails[:] = []
                got = c_engineers_takes()
                ok = got is want and (want or bool(fails))
                bad += 0 if ok else 1
                print('    %-36s %s' % (label, 'ok' if ok else '*** got %s ***' % got))
    finally:
        LEAN_ROOT = real_root
        fails[:], warns[:] = saved

    print('\n  selftest: %s' % ('PASS' if not bad else 'FAIL (%d)' % bad))
    return 1 if bad else 0


def main():
    args = [a for a in sys.argv[1:]]
    if args and args[0] == '--selftest':
        print('ZP Release-Readiness Gate - CONTROLS')
        print('=' * 64)
        return selftest()
    defects_override = None
    if '--defects' in args:
        i = args.index('--defects')
        if i + 1 >= len(args):
            print('usage: --defects needs a path')
            return 2
        defects_override = args[i + 1]
        del args[i:i + 2]
    if args and args[0] == '--ledger-only':
        # The defect-ledger leg alone. Exit 0 CLEAR, 1 BLOCKED, 3 UNREADABLE - three values, so a
        # caller branching on the code cannot read an unread ledger as a clear one.
        st, detail, counts, path = c_defects_ledger(defects_override)
        print('defect ledger: %s - %s' % (st, detail))
        print('    %s: %s' % ('COULD NOT READ' if st == LEDGER_UNREADABLE else 'read',
                                path or '(no path derived)'))
        if counts is not None:
            print_defect_counts(counts)
        for w in warns:
            print('  ! %s' % w)
        for f in fails:
            print('  X %s' % f)
        return {LEDGER_CLEAR: 0, LEDGER_BLOCKED: 1, LEDGER_UNREADABLE: 3}[st]
    if not args or args[0].startswith('-'):
        print('usage: python %s <tag> [--defects PATH]   (e.g. v2.7)' % SELF)
        print('       python %s --ledger-only [--defects PATH]' % SELF)
        return 2
    tag = args[0]

    print(f'ZP Release-Readiness Gate - tag {tag}')
    print('=' * 64)
    print('MECHANICAL (blocking unless noted):')

    line('PASS' if c_engineers_takes() else 'FAIL', "Engineer's Takes filled")
    line('PASS' if c_hash_integrity() else 'FAIL', 'Build-script hash integrity (register tokens)')
    inv_ok, ent, tg = c_registry_invariant()
    line('PASS' if inv_ok else 'FAIL', 'LEAN_CUSTOM_REGISTRY invariant', f'{ent} entries / {tg} tags')
    z_ok, z_phrase = c_zenodo()
    line('PASS' if z_ok else 'FAIL', '.zenodo.json valid JSON', f'description says: {z_phrase}')
    line('PASS' if c_conflict_markers() else 'FAIL', 'No conflict markers (tracked files)')
    line('PASS' if c_releases_entry(tag) else 'FAIL', f'RELEASES.md has "## {tag}" entry')
    line('PASS' if c_doc_links() else 'FAIL', 'README/GUIDE linked PDFs exist')
    d_status, d_detail, d_counts, d_path = c_defects_ledger(defects_override)
    line({LEDGER_CLEAR: 'PASS', LEDGER_BLOCKED: 'FAIL', LEDGER_UNREADABLE: 'FAIL'}[d_status],
         'No open content BEDROCK / BEDROCK-CANDIDATE or untagged defect',
         '%s: %s' % (d_status, d_detail))
    print('    %s: %s' % ('COULD NOT READ' if d_status == LEDGER_UNREADABLE else 'read',
                            d_path or '(no path derived - see the failure below)'))
    if d_counts is not None:
        print_defect_counts(d_counts)

    print('BEST-EFFORT / HYGIENE (warn-only):')
    line('PASS' if c_register_vs_script_version() else 'WARN', 'register <-> script VERSION')
    line('PASS' if c_scripts_mirror() else 'WARN', 'scripts/ mirror current')
    line('PASS' if c_untracked_pdfs() else 'WARN', 'No untracked root PDFs')

    print('INFO:')
    for r in c_signals(tag):
        print(f'    gate signal {r}')
    print('    (post-merge HEAD legitimately differs from the reviewed PR commit;')
    print('     signal freshness is context, not a blocker - confirm gates ran on the PR.)')

    if warns:
        print('-' * 64)
        print('WARNINGS (review, not blocking):')
        for w in warns:
            print(f'  ! {w}')

    print('-' * 64)
    print('JUDGMENT CHECKLIST (a human must confirm - not mechanizable):')
    for item in (
        'Editorial + adversary review ran on all touched prose (this release\'s PR).',
        'claim-review ran if any claim status changed; prior-art-review if a synthesis layer was created/strengthened.',
        'Companion synced for every formal doc whose version bumped.',
        'Major-vs-minor version decision is correct; Lean-only-change release question raised if applicable.',
        '.zenodo.json description reflects this release (cannot be updated retroactively).',
        'Every open ORDINARY content finding in DEFECTS.md is fixed or on a public erratum issue '
        '(labels erratum, open question), its issue number beside the ledger row. No bedrock item '
        'is filed as an erratum, and no grade was lowered to make this release.',
        'Release body drafted and Tim approved it BEFORE `gh release create`.',
        'Post-release: confirm the Zenodo snapshot minted. README badge is the CONCEPT DOI '
        '(auto-resolves to latest) - NO per-release badge edit needed.',
    ):
        print(f'  [ ] {item}')

    print('=' * 64)
    if fails:
        print(f'NO-GO - {len(fails)} blocking failure(s):')
        for f in fails:
            print(f'  X {f}')
        return 1
    print('GO (mechanical checks pass). Now confirm the judgment checklist above before cutting the tag.')
    return 0


if __name__ == '__main__':
    sys.exit(main())
