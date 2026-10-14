#!/usr/bin/env python3
"""Batch orchestrator — turns the collection of checkers into a PROCESS.

WHY (Tim, 2026-08-09): *"this feels a lot like having a collection of scripts but without any kind
of orchestration agent behind it yet."* Correct. The 2026-08-09 `class` batch produced SIX process
failures, every one of them "someone forgot" rather than a knowledge gap:

  * the cheap-AI stage was skipped entirely and nobody noticed until asked;
  * a new theorem shipped with no `#print axioms` entry;
  * the SSOT sync — a standing rule with its own memory entry — was never done;
  * trigger 5 firing was found by hand-measuring, not announced;
  * three ledger entries were duplicated because "consult the ledger" is a discipline, not a step;
  * the build broke four times on the identical insertion mistake, with no pre-flight.

All six are decidable mechanically. That is what this file is for.

THE SPLIT, same as everywhere else in this project: **the script owns sequencing and preconditions
(decidable); an agent owns note-writing and fix-versus-label (not).** This does not judge anything.
It refuses to let a stage run before its inputs exist, and refuses to let a commit or push happen
while a mechanical precondition is unmet.

    python batch.py start --bucket class     # snapshot state, emit the worklist
    python batch.py stage probe --note "..."  # record that probes ran
    python batch.py stage judge --note "..."
    python batch.py precommit                 # mechanical gate before committing
    python batch.py prepush                   # gate before pushing
    python batch.py close                     # prune baseline, require ledger touch
    python batch.py status
"""
import io, os, re, sys, json, hashlib, subprocess

# TWO roots. HERE is the tracked public bundle (checkers + the baselines they consult); PRIV is
# per-push private state — batch state, signals, the defect ledger — which did NOT move and may be
# absent entirely in a public clone. Conflating them is what made this migration more than a copy.
# Roots come from `common` — ONE derivation for the whole bundle (`DEFECTS.md` MIG-3). SELF is
# derived from `__file__`, never written down: a hardcoded invocation path is a copy of the path and
# drifts exactly like a mirrored file does.
#
# ⚠ COERCED TO `str`, not re-derived. This module speaks `os.path`; `common` speaks `pathlib`. A
# line of type conversion is not a second definition — change the layout and there is still exactly
# one place to edit.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common  # noqa: E402

HERE = str(common.HERE)
REPO = str(common.REPO)
PRIV = str(common.PRIV)
SELF = common.self_rel(__file__)
BASE = HERE   # retained: remaining call sites mean "where the tools and baselines live"

# The vendored exemption has exactly ONE definition. Path-insert so this works however batch.py is
# invoked, not only as a script from the repo root.
if HERE not in sys.path:
    sys.path.insert(0, HERE)
from vendored import is_vendored  # noqa: E402
import vendored  # noqa: E402
import report    # noqa: E402  the one formatter every entry point announces itself with
import agent_gate  # noqa: E402  the interpretation layer — ADVISORY, never blocks (rung 5)
import record      # noqa: E402  the ledger client — review freshness is asked, never re-derived
import selfheal    # noqa: E402  MARKERS ONLY — `_recurrence_note` selects its rows by name
STATE = os.path.join(PRIV, "batch_state.json")
# The ones that GATE. `check_poles.py` is a counter with no baseline (REL-3) and is excluded
# deliberately — see check_suite.
# ⚠ `check_encoding.py` joined 2026-08-20 and carries TWO TIERS rather than one baseline
# (Tim, 2026-08-21: *"make it warn instead of block, and keep a whitelist that have been verified
# exclusions"*). `bom` and `undecodable` are exact tests with no false-positive class and BLOCK;
# suspected `double-encoding` is a heuristic that provably cannot separate mojibake from some
# genuine Western-European typography, so it WARNS and is quieted by
# `encoding_whitelist.txt` — verified exclusions, each with a stated reason, never a baseline seeded
# from whatever happened to be there. The corpus is at ZERO suspected sites, and that is the state
# to preserve rather than a number to grow.
GATING_CHECKERS = ["check_prose.py", "check_pov.py", "check_modal.py", "check_classes.py",
                   "check_encoding.py"]

# The verification layer's FILTERS — everything `checker_hashes()` fingerprints for the batch freeze
# (`check_filters_frozen`). WIDER than the gating set on purpose: a defect in `hooks.py`, `vendored.py`
# or `batch.py` itself is silent and multiplies through every verdict. Where an entry's comment speaks
# of `/rely` routing, it states why that file is a filter; whether `/rely` has COVERED a file is the
# ledger's question, asked at TAG: `coverage_gap(step='rely', action='tag')`.
CHECKERS = GATING_CHECKERS + ["check_poles.py", "vendored.py", "vendored_files.txt",
                              "hooks.py", "batch.py", "ship.py", "report.py", "gate_round.py",
                              # ⚠ `agent_gate.py` IS HERE THOUGH IT ONLY WARNS. Its registry of
                              # `expected_failure` declarations is what the interpretation layer
                              # judges against, so editing one silently changes every verdict it
                              # produces — the same argument as the baselines below. Omitting it
                              # would be `RLY17-2`: routed to /rely, absent from CHECKERS.
                              "agent_gate.py",
                              # ⚠ `move_ridealong.py` MUTATES THE CORPUS AND EDITS NOTHING ELSE,
                              # which is exactly why it is hashed: it decides whether a
                              # grandfathered claim may be relocated, and a weakened version would
                              # let a baselined site be re-keyed into a frozen baseline silently.
                              "move_ridealong.py",
                              # ⚠ THE BASELINES ARE EXEMPTION SWITCHES AND MUST BE HASHED. One
                              # appended line to pov_baseline.txt took a planted violation from
                              # exit 1 to exit 0 with checker_hashes() unmoved, and
                              # `check_prose.py --baseline` absorbed a LIVE violation wholesale.
                              # The hook runs the same checkers against the same baseline, so there
                              # is no second opinion — it reaches the remote. This is the FOURTH
                              # route to one property: content marker, path, allowlist, baselines.
                              "prose_baseline.txt", "pov_baseline.txt",
                              "modal_baseline.txt", "class_baseline.txt",
                              # ⚠ AND THE ENCODING WHITELIST (2026-08-21). It is not a baseline —
                              # every line records a run a human VERIFIED is genuine typography, and
                              # an entry with no stated reason is ignored — but it is a suppression
                              # switch with exactly the power of the four above: one line silences
                              # one site permanently. Same rule, no exception for being better
                              # curated.
                              "encoding_whitelist.txt",
                              # ⚠ AND THE GUARD ITSELF. `guards.py` is the control that walks the
                              # four routes above; deleting a route from its registry re-opens that
                              # route AND removes the only thing that would have said so. A control
                              # left out of the hash is the same hole one level up — which is the
                              # FIFTH instance of this property, caught while wiring the fix for the
                              # first four. Enumerate the routes INCLUDING the enumerator.
                              "guards.py",
                              # ⚠ AND EVERY OTHER SCRIPT THAT BLOCKS A PUSH. These six are BLOCK
                              # steps in PRE_PUSH_PLAN and none was hashed, so replacing
                              # `check_paths.py` with a three-line `sys.exit(0)` gave `prepush PASS`
                              # exit 0 with a FRESH /rely signal and no row mentioning it (measured,
                              # /rely pass 6). `.claude-local/` is gitignored, so this hash list is
                              # the ONLY visibility that exists — a blocking check outside it is
                              # unreviewable by construction. The rule: if it can stop a push, it is
                              # in here.
                              "check_paths.py", "check_invariants.py", "check_hashes.py",
                              "scan_pdfs.py", "selfheal.py",
                              # ⚠ AND THE REMAINING DATA SWITCHES. Adding the four `*_baseline.txt`
                              # closed four routes and left two open, which is this property's whole
                              # history in one line. `decl_baseline.txt` is the FIFTH: `batch.py
                              # decls --baseline` — the command the hook itself prints as the remedy
                              # — absorbed a live purity+SSOT obligation, exit 1 -> exit 0, with
                              # `checker_hashes()` BYTE-IDENTICAL. `ar_status.json` is the SIXTH:
                              # editing it alone took `check_hashes.py` from exit 1 to exit 0 for
                              # `build_tools.py`, which builds a SHIPPED PDF and has no register.md
                              # row to anchor it. Both measured, /rely pass 7.
                              "decl_baseline.txt", "ar_status.json",
                              # ⚠ THE 2026-08-15 ADDITIONS, and the rule above ("if it can stop a
                              # push, it is in here") is what pulled them in. `check_moved.py` is a
                              # BLOCK step in the pre-push plan — it was built, given controls, and
                              # then left out of both the hook and this list, so a three-line
                              # `sys.exit(0)` in it would have gone unnoticed exactly as
                              # `check_paths.py` once would. `install_hooks.py` writes the hooks
                              # themselves, which is upstream of every gate. `ci_report.py` decides
                              # what the PUBLIC verification claim says; a fail-open there publishes
                              # a false clean.
                              "check_moved.py", "install_hooks.py", "ci_report.py",
                              "check_negatives.py", "negatives_baseline.txt",
                              "check_figures.py", "figures_baseline.txt", "check_checkers.py",
                              # ⚠ THE FREEZE CHECK AND ITS OWN SUBJECTS. `check_frozen.py` enforces
                              # that the accepted-defect baselines only shrink; editing it out is
                              # exactly as powerful as editing a baseline, so it is hashed like one.
                              "check_frozen.py",
                              # ⚠⚠ `common.py`, ADDED 2026-08-16 IN THE SAME CHANGE THAT CREATED IT,
                              # and it is now the WIDEST-BLAST-RADIUS entry in this list. It owns
                              # `SKIP_DIRS`, `SKIP_NAMES`, `GLOBS`, `targets()` and `load_baseline`
                              # for the checkers that use them, so ONE edited line there changes what
                              # several gates scan or what they treat as grandfathered — a false zero
                              # in all of them at once, where every route above is a false zero in
                              # one. The rule that pulled in the six blocking scripts ("if it can
                              # stop a push, it is in here") reaches further than intended once a
                              # shared module exists: it can stop a push, and it can stop several.
                              # ⚠ Deduplication CONCENTRATES risk even as it removes drift — that is
                              # the trade, and this line is the half that pays for it.
                              "common.py",
                              # ⚠⚠ AND `session_state.txt` (2026-09-13, ADDED IN THE SAME CHANGE
                              # THAT CREATED IT — the omission was caught before the first push, but
                              # it WAS the omission). It is a SUPPRESSION SWITCH with exactly the
                              # power of the four baselines above and a wider reach than any of
                              # them: every path listed is dropped from the subject set of EVERY
                              # recording checker, unconditionally, so one added line stops every
                              # gate from ever attesting to that file again — with no verdict
                              # turning red and nothing in any checker's output changing except a
                              # skip line nobody diffs. `RLY17-2`'s shape (routed to /rely, absent
                              # from CHECKERS) and the same argument the encoding whitelist carries:
                              # better curated is not an exemption from being hashed.
                              "session_state.txt",
                              # ⚠ AND ITS BASELINE. `scope_baseline.txt` pins the reviewed scan
                              # scope, so editing it is exactly as powerful as editing `SKIP_DIRS` —
                              # delete a line and the file it names can silently leave every
                              # checker's scope with the control still green. Same argument as the
                              # four suppression baselines above; a data switch left out of this
                              # list is unreviewable by construction.
                              "scope_baseline.txt",
                              # ⚠ AND THE PATTERN PIN (PAT-1). `scope_baseline.txt` records what the
                              # checkers LOOK AT; this one records what they look FOR. Deleting a
                              # line here retires a detection pattern, which is exactly as powerful
                              # as deleting a scanned directory — measured before it was written:
                              # 30 of 34 advertised patterns could be removed with every control
                              # green. Both pins are data switches and both belong in this list.
                              "pattern_baseline.txt",
                              # ⚠ AND THE SHARED-BUILD PIN (RLY3-2 / RLY4-4). `shared_build_baseline.txt`
                              # fingerprints `zp_utils.py`, which all 43 build scripts import and which
                              # renders the meta line of EVERY document — a surface the per-document
                              # tokens in `register.md` structurally cannot see, because a script's
                              # bytes do not change when its import does. Editing this baseline
                              # re-blesses whatever the shared layer currently says, so it is a data
                              # switch of exactly the kind the four suppression baselines are, and it
                              # blocks a push. It arrived ROUTED-BUT-UNHASHED, which `batch.py`'s own
                              # `_unhashed` leg caught and named on its first run — the enumerator
                              # working, one round after being written.
                              "shared_build_baseline.txt",
                              # ⚠⚠ AND THE RELEASE GATE. The rule above reads "if it can stop a PUSH,
                              # it is in here" — and `check_release_ready.py` cannot, so it sat
                              # outside this list while being the gate whose output is a permanent
                              # Zenodo DOI. Found by editing it: `RLY5-1` corrected its hash leg from
                              # a COMP-only subset to all four tiers plus the shared layer, and
                              # `prepush` did not route that change to `/rely` at all, because an
                              # unhashed file cannot be seen to have moved. **A fail-open here is
                              # strictly worse than one in a push gate: a push is amendable and a
                              # minted DOI is not.** The rule is therefore wider than it was written:
                              # if it can stop a push OR A RELEASE, it is in here.
                              "check_release_ready.py"]

# ⚠⚠ THE FILES UNDER THE ROUTED PREFIXES JOIN `CHECKERS` BY GLOB, NOT BY NAME — and the glob is the
# point. `CHECKERS` is what `checker_hashes()` fingerprints for the BATCH FREEZE: a filter that moves
# mid-batch makes the batch a measurement against a moving target. Every file under a `ROUTING` prefix
# is verification-layer machinery, so a list of names would close today's members and miss the next
# arrival. The prefixes are DERIVED from `ROUTING`, never re-typed beside it.
#
# ⚠ THIS IS NOT A PUSH LEG. `/rely` coverage is the ledger's to answer: the `rely` step is admitted
# at TAG (`gitRobot admission(action='tag')`) and `coverage_gap(step='rely', action='tag')` names
# the paths it still owes. Nothing in this file decides whether `/rely` covered anything.
def _gitignored(dirs):
    """What git IGNORES under `dirs` — generated artifacts, NOT merely untracked files.

    Returns repo-relative entries; one ending in `/` is a whole directory git collapsed. An UNTRACKED
    file is still verification-layer machinery and stays in the set; an IGNORED one is build output
    that can never be staged.

    ⛔ FAILS CLOSED BY WIDENING. Every error path returns the EMPTY set, which skips nothing and
    leaves the fingerprinted set at its widest.

    ⚠⚠ THE INSTRUMENT IS `status --ignored`, NOT `check-ignore`, AND THAT WAS MEASURED THE HARD WAY.
    `git check-ignore --stdin` gave the RIGHT answer for three paths passed alone and the WRONG one
    for the same three inside the real 117-path list — `rc=1`, empty stdout, empty stderr, i.e. a
    confident "nothing here is ignored" for files `status` flags `!!`. Prefer the instrument whose
    scope you can see, and never conclude an absence from the narrower.
    """
    if not dirs:
        return set()
    try:
        out = subprocess.run(["git", "status", "--porcelain", "--ignored=matching", "--"]
                             + sorted(dirs), cwd=REPO, capture_output=True,
                             text=True, encoding="utf-8", errors="replace")
    except OSError:
        return set()
    if out.returncode != 0:
        return set()
    # `!! path` for a file, `!! path/` for a whole directory git collapsed.
    return {ln[3:].strip().replace("\\", "/")
            for ln in out.stdout.splitlines() if ln.startswith("!! ")}


def _routed_files():
    """Every file under a routed prefix — recursive, all extensions, prefixes taken from ROUTING.

    A DISK walk, matching `checker_hashes()`, which fingerprints disk bytes: the freeze compares like
    with like. Generated artifacts are excluded by asking git (`_gitignored`), not by listing them;
    `__pycache__`/`.pyc` are kept as a fast path that also survives git being unavailable."""
    out, prefixes = [], []
    for pat, agent, _w in ROUTING:
        if agent != "/rely":
            continue
        rel = pat.pattern.lstrip("^").rstrip("/").replace("\\.", ".")
        d = os.path.join(REPO, *rel.split("/"))
        if not os.path.isdir(d):
            continue
        prefixes.append(rel)
        for root, dirs, names in os.walk(d):
            dirs[:] = [x for x in dirs if x != "__pycache__"]
            for n in names:
                if n.endswith((".pyc", ".pyo")):
                    continue
                out.append(os.path.relpath(os.path.join(root, n), REPO).replace("\\", "/"))
    ignored = _gitignored(prefixes)
    files = {p for p in ignored if not p.endswith("/")}
    trees = tuple(p for p in ignored if p.endswith("/"))
    return sorted(p for p in out
                  if p not in files and not (trees and p.startswith(trees)))


# ⚠⚠ THE VERDICT REGISTRY — WRITTEN BY THE PRODUCER, NEVER BY THE CALLER. `RLY28-1`.
#
# Every fix before this one asked *"does the call site LOOK like it honours the result?"* — a
# whole-file substring, then a windowed substring, then an AST shape test, then an AST Name test.
# All four were defeated, because a caller that receives a number can always throw it away, and
# `bad += routing_verdict(state, ranges) * 0` throws it away while leaving every one of those
# tokens exactly where the test looks for it. Measured 2026-08-23: `prepush` went exit 1 → exit 0,
# "prepush PASS", with three `/rely FAIL` rows still printed above it and `guards.py` at 81 ok / 0
# FAIL.
#
# **So the caller stops being the one who reports the number.** A step records its own outcome HERE,
# at the point it computes it, and `prepush_verdict()` reads the registry. `bad += f(...) * 0` is
# then INERT rather than merely detectable — there is nothing left for the annihilation to delete.
# Deleting the registry write instead moves the step out of `_EXPECTED`, and the completeness check
# fails closed on the absence, which is the one thing a "warrant satisfied while empty" cannot do.
#
# ⚠ THIS IS NOT A SECOND VERDICT STORE. `bad` is gone from the enforcement path entirely; the
# registry is the only place a push-time failure count lives, so there is nothing to drift against.
_VERDICT = {}

# Steps that MUST report before a verdict means anything. A step that never ran leaves no row, and
# absence-of-evidence is exactly what this project keeps mistaking for success — so it is an error.
#
# ⚠⚠ `B4`, 2026-09-05 — THIS TUPLE HELD ONE NAME WHILE SIX LEGS GATED THE PUSH, AND THAT GAP WAS
# THE WHOLE DEFECT. `routing` recorded itself here; `purity`, `ssot`, `pdf_coupling`,
# `prior_art_attrib` and the review-signal legs all accumulated into a LOCAL `bad` in `cmd_prepush`
# which was then handed to `enforce_prepush_verdict`. One integer, six independent properties — so
# `enforce_prepush_verdict(bad * 0)` switched off all six at once, and only `routing` survived.
#
# ⚠ A control that exercises ONE leg says nothing about the others — `B5`'s shape, a green control
# layer over a switched-off gate. The registry's controls are `guards.py`'s
# `check_push_verdict_registry`, which holds this tuple to an independently written statement of
# it and drives `enforce_prepush_verdict` behaviourally.
# ⚠ `routing` IS NOT IN THIS TUPLE: there is no `/rely` push leg. `/rely`'s obligation is the
# ledger's, at TAG — `coverage_gap(step='rely', action='tag')`.
_EXPECTED = ("purity", "ssot", "pdf_coupling", "prior_art_attrib")


# ⚠⚠ THE SECOND MEASUREMENT — `RLYB4-1`. What each leg DISPLAYED, tallied separately from what it
# RECORDED, so the two can be required to agree.
#
# WHY IT EXISTS: `B4` moved the annihilation out of the caller's argument and into the producer's,
# and stopped there. `verdict_record(key, (0 if ok else 1) * 0)` on the shared loop line silences
# FOUR legs in one token; the same edit on the signals line takes two more. `_EXPECTED` cannot see
# it — the ROW IS PRESENT, it simply holds a zero the leg did not earn. Presence was checked and
# value was not.
#
# ⭐ THE PRINCIPLE, and it is not local to this file: WHERE A NUMBER CROSSES BETWEEN TWO PARTIES,
# BOTH MEASURE, AND THE DISAGREEMENT IS THE SIGNAL. A leg's outcome crosses from the producer to the
# registry; tallying what reached the SCREEN gives a second, independently-written count of the same
# fact. Annihilating the recorded value now leaves `FAIL` printed and `0` recorded, and they
# disagree. Deleting the tally call leaves `1` recorded and nothing displayed, and they disagree the
# other way. It fails CLOSED in both directions.
#
# ⚠ WHAT THIS DOES NOT BUY, STATED SO NOBODY READS IT AS MORE: it is not tamper-proof. What it
# removes is the ONE-TOKEN edit that silences a leg while the evidence of the failure is still on
# screen — which is the shape that actually occurred, twice, in this file.
#
# ⛔ AND THE FIRST VERSION OF THIS CAVEAT WAS WRONG IN BOTH DIRECTIONS, measured by /rely round 2 the
# same day. It said *"editing `ok` itself, or the helper below, moves both halves together and they
# still agree."*
#   · THE HELPER HALF IS FALSE — a single edit to `display_fail` REFUSES, and editing both it and the
#     record turns three `guards.py` rows red. The caveat conceded a hole that is not there.
#   · THE `ok` HALF WAS TRUE AND UNDERSTATED — it was reachable by swapping two identifiers in a
#     `for` target, which is a plausible refactor rather than a deliberate neuter. That is `RLYB4-5`
#     and it is now closed by an explicit bool guard at both leg sites.
# ⭐ AN HONEST-SOUNDING CAVEAT IS STILL A CLAIM, and this one shipped un-measured beside a mechanism
# that had been. Do not write the limits of a control from the armchair; construct them and run them.
_DISPLAYED_FAILS = []


def display_fail(key):
    """Tally a leg that PRINTED `FAIL`. Called at the print site, never by the enforcement."""
    _DISPLAYED_FAILS.append(key)


def verdict_reset():
    """Start a push judgement. Called ONCE, at the top of the run that will be judged."""
    _VERDICT.clear()
    del _DISPLAYED_FAILS[:]


def verdict_record(step, failures):
    """Record one step's failure count. ⚠ Called BY THE STEP, never by whoever consumes it."""
    _VERDICT[step] = int(failures)
    return _VERDICT[step]


def prepush_verdict():
    """The push verdict: (failures, missing_steps). ⚠ A MISSING STEP IS NOT A PASS.

    Returns the total only alongside the steps that never reported, so a caller cannot read a
    zero out of a registry that is empty because nothing ran.

    ⚠ THIS IS THE QUERY, NOT THE ENFORCEMENT. Call `enforce_prepush_verdict` to act on it — a
    returned number is a number a caller can throw away, which is the whole history below."""
    missing = tuple(s for s in _EXPECTED if s not in _VERDICT)
    return sum(_VERDICT.values()), missing


def enforce_prepush_verdict():
    """DECIDE AND ACT IN ONE UNIT. Returns None on success; otherwise it does not return at all.

    ⚠⚠ ATTEMPT SIX, AND THE FIRST FIVE ALL DIED THE SAME DEATH. Every previous repair left the
    verdict as a VALUE HANDED TO THE CALLER, and a caller handed a value can discard it:

        bad += routing_verdict(state, ranges) * 0          <- defeated attempts 1-4
        _routing_bad, _missing = 0, ()                     <- defeated attempt 5, measured 2026-08-24

    That last one was found by a reliability trial against the fix written the same day: one added
    line took `batch.py prepush` to **exit 0, "prepush PASS"**, printed directly under two live
    `/rely FAIL` rows, while `guards.py` reported **81/81 ok** including all three brand-new
    `push verdict registry:` rows, and the mutation probe reported **11 of 11**. Every control was
    individually true and the artifact as a whole was worthless — because the controls call the
    query in their own frame, where the property really does still hold.

    **So the CALLER'S value is gone**: this function reads the registry and DIES, and there is no
    parameter for `cmd_prepush` to zero.

    ⚠⚠ AND SINCE `B4` (2026-09-05) IT TAKES NO ARGUMENT AT ALL. It used to accept `other_bad`, the
    caller's running total over the inline legs — purity, ssot, pdf coupling, prior-art attribution
    and the review signals — so `enforce_prepush_verdict(bad * 0)` annihilated SIX gating legs while
    leaving `routing` untouched.

    ⛔⛔ **RETRACTED THE SAME DAY, BY THE `/rely` ROUND ON THIS VERY CHANGE (`RLYB4-1`).** This
    docstring said *"there is no number to zero, no tuple to rebind"*. **THAT IS FALSE AND IT WAS
    FALSE WHEN WRITTEN.** The annihilation was RELOCATED, not removed — out of the consumer's
    argument and into the PRODUCER's, where `verdict_record(key, (0 if ok else 1) * 0)` on the shared
    loop line silences FOUR legs in one token, and the same edit on the signals line takes the other
    two. Measured, not argued: `purity FAIL SYNTHETIC` printed directly above `prepush PASS`, with
    `guards.py` green on all six `push verdict registry:` rows throughout. **That is the 2026-08-23
    photograph reproduced against the fix written for it.**

    ⚠ WHAT `B4` ACTUALLY BOUGHT, stated at its true size: the completeness check verifies every
    leg's PRESENCE and only `routing`'s VALUE. So `B4` widened the presence check from one leg to
    seven and left the value check at one. Deletion of a `verdict_record` fails CLOSED; an unearned
    ZERO written in its place does not. The value half is `RLYB4-1` and is what the
    displayed-versus-recorded check below cross-checks (`_DISPLAYED_FAILS` against `_VERDICT`) — two
    independent measurements of one count, where the disagreement is the finding.

    ⚠ DELETING the call is caught: `guards.py` asserts the name is read inside `cmd_prepush`.
    ⛔ WRAPPING it to swallow `SystemExit` is NOT caught by that row — the name stays in a Load
    position — and neither is changing `die`'s exit code to 0 (G1-1: each took a failing
    `cmd_prepush` to exit 0 with that row green). The IN-PROCESS "end to end" rows of
    `guards.check_push_verdict_registry` ("end to end: cmd_prepush with one FAILING inline leg exits
    non-zero", "… one FAILING review signal …", "… every leg clean exits 0") call `cmd_prepush` with
    stubbed legs and read the SystemExit it raises — they catch a wrap INSIDE `cmd_prepush` and the
    leg-site neuters, but NOT a SystemExit swallowed in `__main__` or a `die` that kills the process
    with code 0 (`R2-B1`, `R2-O1`), because the hook reads the PROCESS return code. That is the job of
    the SUBPROCESS row, "end to end (subprocess): batch.py prepush with a forced FAIL exits non-zero":
    it runs `python batch.py prepush --ranges …` with `ZP_PREPUSH_FORCE_FAIL` set (the fail-only seam,
    see `FORCE_FAIL_ENV`) and reads `returncode` — the exact value the hook branches on.

    ⛔ `RLYB4-5` silenced all four inline legs by swapping two identifiers in a `for` target, with
    nothing deleted and every control green; the explicit bool guards at both leg sites close it.
    ⚠ THE ENFORCEMENT ITSELF HELD UNDER EIGHTEEN CONSTRUCTED REGISTRY STATES and none of that is in
    doubt. What is in doubt is whether anything would TELL YOU if it stopped."""
    total, missing = prepush_verdict()
    if missing:
        # ⚠ A STEP THAT NEVER REPORTED IS NOT A PASS. An empty registry reads as "nothing ran",
        # never as "nothing wrong" — the one thing a warrant-satisfied-while-empty cannot do.
        die("push verdict incomplete — %s never reported. A step that did not run cannot have "
            "passed; this is a fail-CLOSED refusal, not a finding about the corpus."
            % ", ".join(missing))
    # ⚠⚠ THE TWO MEASUREMENTS MUST AGREE — `RLYB4-1`. Every leg in `_EXPECTED` prints through a leg
    # site that tallies `display_fail`, so the whole registry is held to the screen; no leg is exempt.
    _legs = sum(_VERDICT.values())
    if _legs != len(_DISPLAYED_FAILS):
        die("push verdict INCONSISTENT — %d leg failure(s) RECORDED but %d FAIL row(s) DISPLAYED "
            "(%s). One of the two was tampered with or dropped; a count that disagrees with the "
            "screen cannot be acted on either way, so this refuses rather than picking one."
            % (_legs, len(_DISPLAYED_FAILS), ", ".join(_DISPLAYED_FAILS) or "none displayed"))
    # ⚠ `any`, NEVER `if total:` — `RLYB4-3`. `total` is a SUM, so a negative in one leg cancels a
    # positive in another and the push proceeds with a real failure recorded. No producer writes a
    # negative today, which is why this was a walk-past route rather than a live hole — but `B4`
    # took the number of producers from one to seven, and "no leg is non-zero" is the property
    # actually wanted. A sum was never it.
    if any(_VERDICT.values()):
        die("%d push check(s) failed. Read the FAIL rows above.\n"
            "  legs: %s"
            % (total, ", ".join("%s=%d" % (k, v) for k, v in sorted(_VERDICT.items()))))


def rely_record():
    """The current `rely` ledger record as `{verdict, reason, subjects}`, or None if there is none.

    None means BOTH "no record" and "the ledger could not be asked". They are different facts and
    neither is coverage, so both land here — every caller treats None as fail-CLOSED."""
    try:
        # ⚠ `read_ref` — the ledger has no ref literally named INDEX. Passing the sentinel straight
        # through returned `ok: true` with every step MISSING, so a real record read as no record.
        out = record._call('inventory', {'ref': record.read_ref(common.INDEX), 'action': 'push'})
        if not out or not out.get('ok') or not isinstance(out.get('rows'), list):
            return None
        rid = None
        for r in out['rows']:
            if r.get('step') == 'rely':
                rid = r.get('record_id')
                break
        if not rid:
            return None
        got = record._call('get', {'id': rid})
        rec = (got or {}).get('record') or {}
        return {"verdict": rec.get("verdict"), "reason": rec.get("reason") or "",
                "subjects": rec.get("subjects") or []}
    except Exception:                                          # noqa: BLE001 — cannot ask == none
        return None


# ⚠ `register.md` IS DELIBERATELY NOT IN THIS LIST, AND IT WAS ADDED AND THEN REMOVED — the reasoning
# is worth more than the entry. It IS a switch: every hash check compares a script against a token
# recorded there, and blanking one disarmed a check while `checker_hashes()` stayed byte-identical
# (`RLY18-4`). But hashing it taxes the wrong thing. Measured over 60 days: **89 of 728 commits touch
# `register.md`, and 81 of those — 11% of all commits — touch it WITHOUT touching `tools/verify/`**,
# so every ordinary version bump would open a `/rely` round whose stated reason, *"N checker(s) changed
# since /rely last signed them"*, is false on its face. **A block whose reason is wrong is how bypass
# habits start.**
#
# The hole was also one tier wide, not general: COMP/FORMAL are immune via `(None, None)` and
# FORMAL_ONLY already had an explicit `if reg is None`. Only STANDALONE read `if reg and ...`, so only
# it could be disarmed by deleting a token — or the whole row. That is now fixed IN
# `check_hashes.all_hash_mismatches()`, which closes the route **at the check that was disarmed**
# instead of detecting the disarm afterwards, catches whole-row deletion too, and surfaces
# `build_tools.py`'s missing provenance for free. (/rely round 2 measured the cost and made the call;
# it overruled the author's choice to hash the file, with the commit data above.)
# ⚠ `gate_round.json` is DELIBERATELY NOT IN THIS LIST. It IS a real hole — hand-writing round 0
# takes the cap from exit 2 to exit 0 with `checker_hashes()` byte-identical, and the `reset_from`
# announcement only appears when `reset` itself writes it (/rely pass 8, REL8-3).
#
# It is STATE, not a switch DEFINITION: it changes on every legitimate bump. MEASURED, and stated as
# exactly what was measured — one `gate_round.py bump` moves its hash and produces a live `/rely`
# routing row, and `ship.py pre` bumps the round, so the entry would stale the signal it is about to
# require **on every single round**.
#
# ⚠ An earlier version of this comment called that "a permanent deadlock". That was NOT measured and
# it is FALSE: a post-bump `/rely` signature clears it, so the real cost is a per-round re-sign TAX
# (/rely pass 9, REL9-3). The conclusion stands — a mandatory extra gate round per bump is not worth
# it — but it stands on cost, not impossibility. The unjustified step was inferring "deadlock" from
# "the hash moves"; the test never run was "does signing afterwards clear it".
#
# A counter needs TAMPER-EVIDENCE (a marker `gate_round.py` writes and checks), not a content hash —
# new mechanism, ledgered as debt.
# ⚠ `vendored_files.txt` is DATA, and it is in here because data that switches a gate off is part of
# the verification layer. Adding one line to it exempts a file from all four checkers; leaving it out
# of this list meant that switch left `checker_hashes()` byte-identical, so `/rely` routing never
# fired. Measured THREE times: content route, path route, then the allowlist itself. **When fixing a
# self-exemption, enumerate every route to the property before calling it closed.**
# ⚠ `ledger` and `screen` are stages BECAUSE THEY WERE THE TWO THAT GOT SKIPPED. On 2026-08-09 the
# cheap-AI screen was omitted entirely and nobody noticed until asked, and the ledger was not
# consulted, so three "findings" duplicated rows already in it. A step that is not a stage is a
# step that can be forgotten; making it a stage makes forgetting it impossible and skipping it a
# deliberate act with a recorded note.
STAGES = ["start", "ledger", "screen", "probe", "judge", "precommit", "prepush", "close"]

# The prefixes whose files belong to `/rely` rather than to the three prose gates — a DECLARATION, not
# a gate. Read by `_routed_files()` (the batch-freeze set) and by `guards.py`, which holds it equal to
# the registry's `rely.scope` and to `EXEMPT_PREFIXES`. Nothing in this file blocks on it: whether
# `/rely` has covered these paths is the ledger's question, at TAG —
# `coverage_gap(step='rely', action='tag')`.
ROUTING = [
    # ⚠⚠ THE WHOLE DIRECTORY, NOT AN ALLOWLIST OF FILENAMES. This was an allowlist, and the
    # exemption that depends on it is a DIRECTORY PREFIX — so they did not cover the same set
    # and the justification for the exemption ("ROUTING fires on exactly this prefix ... they
    # are a pair") was false. Found independently by /rely and the adversary gate on
    # 2026-08-15, both with a real commit: `tools/verify/README.md` came back `reviewable: []`
    # and routing `ROWS: NONE` — a tracked, public, 22KB prose file reviewed by NOTHING, and
    # ~250 lines of argument had just been moved into it.
    #
    # An exemption and its compensating control must cover the SAME SET or the pair is a
    # story. Anything under `tools/verify/` now routes to `/rely`, whatever it is called.
    # ⚠ CASE-INSENSITIVE, because `reviewable_from()` lowercases before its prefix test and
    # this regex did not. /rely committed `Tools/Verify/CASETEST.md` and got `reviewable: []`
    # AND `ROUTING rows: NONE` — the same file exempt from the prose gates and routed to no
    # gate at all, which is the round-1 signature character for character. Latent on Windows
    # (git normalises case here) and LIVE on ubuntu-latest, where CI runs.
    # ⚠⚠ WIDENED TO THE WHOLE `tools/` FOLDER 2026-09-18, Tim's ruling: *"The tools folder doesn't
    # make sense for anything but rely to cover. Adversary is math, as is prior art. Editorial
    # doesn't make sense on tooling."* This row REPLACES the separate `^tools/verify/` and
    # `^tools/process/` rows; `EXEMPT_PREFIXES` and `rely.scope` moved in the SAME commit, because
    # `guards.check_registry_router_agreement` requires this prefix set and the scope to be EQUAL.
    # ⛔ THE GAP IT CLOSES WAS PRE-EXISTING, NOT NEW. Measured 2026-09-18 over all 109 tracked
    # `tools/` paths: 12 were claimed by NO gate at all — every file under `tools/registry/` and
    # `tools/render/` — because the prose gates excluded them via `tools/*.md` (`*` crosses `/`)
    # while `rely.scope` reached only `tools/verify/*` and `tools/process/*`. A /rely round read
    # that as a hole opened by the harmonisation; the census says orphans were 12 before and 12
    # after, so the harmonisation created none of it. **Two lists that disagree about a folder
    # leave its subdirectories to nobody, and neither list looks wrong on its own.**
    # ⚠ The two personas below are merged rather than lost: one prefix cannot carry two reasons,
    # and an overlapping second row would route the same file twice.
    (re.compile(r"^tools/", re.I),
     "/rely", "a checker, hook, exemption switch, or routed process document changed - the "
              "verification layer's first run produced CHK-2 and CHK-3, both checker bugs, and a "
              "routed rule whose trigger or pointer rots stops firing silently"),
    # `tools/process/` is CLAUDE.md's body — the argument behind each routed rule, split out so the
    # injected file can be a routing table rather than the payload. Same pairing as the prefix above:
    # it is exempt in EXEMPT_PREFIXES and routed here, and the two MUST be edited together. Added
    # 2026-08-20 with its first two files; the exemption is DECLARED in CLAUDE.md's header, never
    # inferred from "it is operating instructions" — that inference is what put `.claude/commands/`
    # in the exempt tuple for an hour before it was removed.
    (re.compile(r"^\.github/workflows/", re.I),
     "/rely", "CI workflow changed - a fail-open here publishes a false verification claim"),
]

# ⚠ THIS FILE'S OWN COPY OMITTED `line_buffering=True` — one of two out of eight that did, and this
# is the orchestrator, the entry point whose manifest ordering `report.py:34` was written to fix.
# Shared now, so a copy cannot be half right.
common.utf8_stdout()


def sh(*args, cwd=REPO):
    """`(rc, stdout + stderr)` — for a HUMAN-READABLE capture. Never parse it as data: see `sh_split`."""
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


def sh_split(*args, cwd=REPO):
    """`(rc, stdout, stderr)` — for output that is PARSED AS DATA.

    ⚠ `RLY29-2`: `changed_files` parsed `sh`'s merged capture, and git's exit-0 warning
    (`warning: in the working copy of '…', CRLF will be replaced by LF…`) arrived as a SCOPE ENTRY.
    The `rc != 0` guard is blind to it — a warning exits 0 — so the only fix is to never read stderr
    as a list of paths."""
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or ""), (r.stderr or "")


# ⚠ NOT EVERY WATCHED FILE LIVES IN THIS BUNDLE, and assuming so silently re-opened two
# closed routes. `CHECKERS` is the list of things whose change must route to `/rely`; after
# the 2026-08-15 move it was resolved wholesale against `tools/verify/`, so `scan_pdfs.py`
# (now in `scripts/`) and `ar_status.json` (private) were pinned at `<ABSENT>` forever.
#
# Measured by /rely: neutralising the PDF scanner to `sys.exit(0)` AND rewriting the AR
# tracker left the hash dict BYTE-IDENTICAL. Both entries were added specifically to close
# measured routes — the comments above call them the fifth and sixth — and the move undid
# both. The `<ABSENT>` sentinel, which exists so a DELETED checker still trips the routing,
# is what made it silent: a file in the wrong place is indistinguishable from a deleted one.
def _checker_path(name):
    """Where a watched file actually lives. Three roots, not one — plus explicit repo-relative
    entries.

    ⚠ AN ENTRY CONTAINING `/` IS A REPO-RELATIVE PATH, NOT A BASENAME, and that escape hatch exists
    because basenames stopped being unique. `tools/process/` routes to `/rely` and holds a
    `README.md`, which collides with `tools/verify/README.md`; a bare-basename list cannot express
    both, and the `_unhashed` leg compares PATHS precisely so a collision is a MISS rather than a
    false cover. Added 2026-08-21 after `/rely` measured 8 routed-but-unhashed files — the routing
    was opened for `tools/process/` without the hash leg that discharges it, so the exemption it
    justifies had a compensating control that could not be satisfied. Prefer a path for anything
    outside the verification bundle."""
    if "/" in name:
        return os.path.join(REPO, *name.split("/"))     # explicit, collision-proof
    if name == "scan_pdfs.py":
        return os.path.join(REPO, "scripts", name)      # build-side tool
    if name == "ar_status.json":
        return os.path.join(PRIV, name)                 # private legacy tracker
    return os.path.join(BASE, name)                     # the verification bundle


# ⚠ EXTENDED HERE, NOT AT THE LITERAL, BECAUSE THE DEDUPE NEEDS `_checker_path`. The list above
# names bundle files by BASENAME; `_routed_files()` returns REPO-RELATIVE paths, and the same file
# reached both ways must not be hashed twice under two keys — that would double-count it in the
# filter fingerprint and make a one-file edit look like two. Resolving both through the one path
# function is what makes "already covered" a fact rather than a string comparison.
CHECKERS = CHECKERS + [
    f for f in _routed_files()
    if f not in {os.path.relpath(_checker_path(c), REPO).replace("\\", "/") for c in CHECKERS}
]


def checker_hashes():
    """Fingerprint the filters, so a mid-batch change to one is VISIBLE.

    A batch worked against a moving target is not a measurement. This is the mechanical form of
    "freeze the filter before a batch" — unenforceable as a discipline, trivial as a hash."""
    out = {}
    for c in CHECKERS:
        p = _checker_path(c)
        # ⚠ A MISSING file gets a sentinel, not an omission. Skipping it meant DELETING a checker
        # did not trip the routing — the hash simply vanished from the dict and nothing compared
        # unequal, so removing a gate was quieter than editing one (/rely pass 2).
        out[c] = (hashlib.sha256(io.open(p, "rb").read()).hexdigest()[:12]
                  if os.path.exists(p) else "<ABSENT>")
    return out


def load():
    if not os.path.exists(STATE):
        return None
    return json.load(io.open(STATE, encoding="utf-8"))


def save(s):
    # ⚠ Via the shared writer, which creates `.claude-local/` if it is absent. It IS absent in every
    # clone that is not the author's, and `batch.py start` used to die there with a raw
    # FileNotFoundError — on the command this project's own manual calls the default entry point for
    # any multi-site work.
    common.write_text_lf(STATE, json.dumps(s, indent=1, ensure_ascii=False))


def die(msg):
    print("BLOCKED: %s" % msg)
    sys.exit(1)


def self_hash():
    return hashlib.sha256(io.open(os.path.abspath(__file__), "rb").read()).hexdigest()[:12]


def stage_done(state, stage):
    """A gate stage counts as done only if THIS version of the tool passed it.

    ⚠ A bare `done` flag is a PROXY for "the check passed" (DC-18). Measured 2026-08-09: `prepush`
    passed under a weaker signal check, the check was then fixed to validate freshness and coverage,
    and the stale `done` survived — so `status` reported a stage as complete while running it
    blocked. Gate stages therefore record the tool hash that passed them and are invalidated when
    the tool changes. Judgement stages (`ledger`, `screen`, `probe`, `judge`) carry a human note and
    are not invalidated: their content does not depend on this file."""
    rec = state["stages"].get(stage)
    if rec is None:
        return False
    if stage in ("precommit", "prepush") and rec.get("tool") != self_hash():
        return False
    return True


def require(state, stage):
    """A stage may only run once every earlier stage has, under the CURRENT tool."""
    if state is None:
        die("no batch in progress — run `batch.py start --bucket <name>` first")
    i = STAGES.index(stage)
    for prior in STAGES[1:i]:
        if not stage_done(state, prior):
            extra = ("" if prior not in state["stages"]
                     else " (it passed under an older version of batch.py — re-run it)")
            die("stage '%s' has not run; cannot enter '%s'%s" % (prior, stage, extra))


# ---------------------------------------------------------------- mechanical preconditions

DECL_PAT = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma|def|instance|abbrev)\s+([A-Za-z_][\w'.!?]*)", re.M | re.U)
COMMENTS = re.compile(r"/-[-!]?.*?-/", re.S)
LINE_COMMENT = re.compile(r"--.*$", re.M)


def strip_comments(src):
    """Remove Lean comments, honouring that block comments NEST.

    ⚠ The regex this replaces was `/-[-!]?.*?-/` — non-greedy, so on
    `/- outer /- inner -/ #print axioms X -/` it stopped at the FIRST `-/` and left
    `#print axioms X -/` behind as live code. That satisfied the purity obligation for a
    declaration whose only `#print axioms` was commented out, and it is reachable by commenting out
    a purity section that happens to contain a docstring (measured, /rely pass 5). Lean block
    comments nest, so nothing regular can strip them; this is a depth counter."""
    out, depth, i, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif two == "--":                       # line comment, only outside a block
            j = src.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def decls_in(src):
    """Declaration names in Lean source, with COMMENTS STRIPPED FIRST.

    Two earlier versions parsed the DIFF and both failed. The first reused the CAPITALISED
    class-name pattern, so a lowercase theorem name read as "(none) added" and precommit PASSED on
    a state owing a purity entry and an SSOT row - a fail-open on its first run, caught only
    because the batch's answer was already known. The second anchored at column 0, which does not
    help: prose inside a `/-! ... -/` block wraps at column 0 too, so a sentence continuing with the
    word "instance" produced phantom declarations named `below` and `without`. No anchoring can fix
    that - doc blocks and declarations occupy the same column. The diff has no comment structure to
    see; the FILE does. Parse the file."""
    stripped = strip_comments(src)
    return {m.group(2) for m in DECL_PAT.finditer(stripped)}


DECL_BASELINE = os.path.join(BASE, "decl_baseline.txt")
PRINT_AX_PAT = re.compile(r"#print\s+axioms\s+([A-Za-z_][\w.'!?]*)", re.M)


def lean_files_on_disk():
    """Every .lean under ZeroParadox/, read from DISK.

    Deliberately not `git ls-files`: a brand-new file is untracked until it is added, and its
    declarations owe a purity entry and an SSOT row exactly like any other. Walking the directory
    sees them; asking git does not."""
    out, src = [], os.path.join(REPO, "ZeroParadox")
    for root, _dirs, names in os.walk(src):
        out += [os.path.join(root, n) for n in names if n.endswith(".lean")]
    return sorted(out)


def decl_key(rel, name):
    """`file::name`, because a bare name COLLIDES.

    ⚠ The baseline was keyed on the short name alone, so a brand-new `theorem le` in one file was
    invisible whenever `le` was already baselined from another — and six short names already collide
    in this corpus (RLY2-10). Keying on the file makes each declaration its own obligation."""
    return "%s::%s" % (rel.replace("\\", "/"), name)


def decls_on_disk():
    """Declarations that OWE a purity entry and an SSOT row, as `file::name`. Vendored excluded.

    ⚠ The exemption is IMPORTED from `vendored.py`, never restated here. This function briefly
    carried its own copy and it was already wrong three ways after one day — a looser Apache
    pattern, an unanchored `Upstream:` that matched prose about upstream, and a character window
    instead of a line window."""
    names = set()
    for fp in lean_files_on_disk():
        rel = os.path.relpath(fp, REPO)
        if is_vendored(fp, rel):
            continue
        src = io.open(fp, encoding="utf-8", errors="replace").read()
        names |= {decl_key(rel, n) for n in decls_in(src)}
    return names


def tracked_lean_rels():
    """Repo-relative `.lean` paths git TRACKS (index included), or None if git cannot be asked.

    STDOUT ONLY — a warning on stderr is not a path (`RLY29-2`'s shape)."""
    try:
        r = subprocess.run(["git", "ls-files", "--", "ZeroParadox"], cwd=REPO, capture_output=True,
                           text=True, encoding="utf-8", errors="replace")
    except OSError:
        return None
    if r.returncode != 0:
        return None
    return {l.strip().replace("\\", "/") for l in r.stdout.splitlines() if l.strip().endswith(".lean")}


def print_axioms_on_disk(files=None, tracked=False):
    """`(anywhere, own)`: short names whose `#print axioms` may discharge ANY declaration, and
    `{rel: names}` whose print may discharge only a declaration IN THAT SAME FILE.

    Collected in ONE pass from disk: the per-declaration `git grep` this replaced cost one
    subprocess per name and could see only TRACKED files, so a purity line in a new file read as
    missing.

    ⚠⚠ AN UNTRACKED FILE'S PRINTS COUNT ONLY FOR ITS OWN DECLARATIONS (`P5-4`). Measured: an
    untracked scratch `.lean` holding `#print axioms X` satisfied the purity obligation for a
    declaration `X` in a TRACKED file, permanently, with nothing the push carries backing it. A
    brand-new file still discharges its own declarations before it is staged — its prints sit
    beside the declarations they cover — so the manual precommit run is unchanged for new work.
    ⛔ FAILS CLOSED: when git cannot say what is tracked, every file is treated as untracked, which
    only ever narrows what a print may discharge.

    `files` = [(rel, src)] and `tracked` = a set of rels are injection points for the selftest."""
    if files is None:
        files = [(os.path.relpath(fp, REPO).replace("\\", "/"),
                  io.open(fp, encoding="utf-8", errors="replace").read())
                 for fp in lean_files_on_disk()]
    if tracked is False:
        tracked = tracked_lean_rels()
    tracked = tracked or set()
    anywhere, own = set(), {}
    for rel, src in files:
        # ⚠ STRIP COMMENTS FIRST. Without this a commented-out `-- #print axioms X` satisfied the
        # purity obligation for X — the requirement discharged by a line the elaborator never sees.
        # `decls_in` strips comments and documents exactly why; this did not, so the two halves of
        # the same check disagreed about what counts as code (RLY2-9).
        names = {m.group(1).split(".")[-1] for m in PRINT_AX_PAT.finditer(strip_comments(src))}
        if rel in tracked:
            anywhere |= names
        else:
            own.setdefault(rel, set()).update(names)
    return anywhere, own


def load_decl_baseline():
    if not os.path.exists(DECL_BASELINE):
        return None
    return {l.strip() for l in io.open(DECL_BASELINE, encoding="utf-8-sig").read().splitlines()
            if l.strip() and not l.startswith("#")}


def write_decl_baseline(names):
    hdr = ("# Declaration names present on disk when this baseline was taken.\n"
           "# `added` = (declarations on disk now) - (this set). NEVER a git comparison: see SIG-2.\n"
           "# A STALE baseline is SAFE - it can only make more declarations look new, never fewer,\n"
           "# so the checks get stricter rather than vacuous. Refresh with:\n"
           "#     python %s decls --baseline\n" % SELF)
    body = "".join("%s\n" % n for n in sorted(names))
    # ⚠ utf-8, NOT ascii: declaration names carry subscripts (`T₂`, `lt_nmul_iff₃`) and an ascii
    # write raises UnicodeEncodeError mid-run, leaving NO baseline — which then fails closed and
    # looks like a missing-baseline problem rather than an encoding one. Same non-ASCII trap CHK-2
    # recorded for check_classes.py.
    io.open(DECL_BASELINE, "w", encoding="utf-8", newline="\n").write(hdr + body)


def orphan_baseline_keys():
    """Baseline keys with no declaration on disk — the DELETION half of the ledger.

    ⚠ Tim, 2026-08-10: *"we should be doing pruning of files that no longer exist in the git commits
    not just additions."* Correct, and it is a fail-open rather than untidiness: the baseline is
    `file::name`, so a declaration that is baselined, DELETED, and later RE-ADDED gets the identical
    key and is therefore still grandfathered — it owes no `#print axioms` entry and no `ssot.json`
    row, silently. The additions half was built and the deletions half was not, so the baseline only
    ever grows and every stale key is a slot a future declaration can be born into.

    Reported by `decls`, applied by `decls --prune`. Deliberately NOT automatic: a check that
    mutates the state it checks can hide the thing it was meant to surface."""
    base = load_decl_baseline()
    if base is None:
        return None, None
    live = decls_on_disk()
    orphans = sorted(base - live)
    gone_files = sorted({k.split("::")[0] for k in orphans
                         if "::" in k and not os.path.exists(os.path.join(REPO, k.split("::")[0]))})
    return orphans, gone_files


def added_decls():
    """Declarations on disk that are NOT in the on-disk baseline - those owe a purity entry and an
    SSOT row.

    ⚠ NEVER computed against git (Tim, 2026-08-09; SIG-2). It used to diff the working tree against
    `git show "HEAD:<rel>"`, which is meaningful ONLY before the commit: once committed the two are
    identical, `added` came back empty, and check_purity and check_ssot - two of the four obligations
    this tool exists to enforce - both passed VACUOUSLY. Reproduced on 2026-08-09: precommit run just
    after a commit printed "added declarations in the working diff: (none)" with both checks ok.

    Returns None when no baseline exists, so the caller FAILS CLOSED rather than reporting zero.

    ⚠ PRUNES AUTOMATICALLY, and the asymmetry is the whole justification (Tim, 2026-08-10: *"when
    and how should the pruning run automatically? it seems like it should happen without me needing
    to expressly trigger it"*):

        auto-ADD to the baseline    = DANGEROUS. It silently grandfathers a new obligation.
        auto-PRUNE from the baseline = SAFE. It only ever REMOVES an exemption.

    Pruning can therefore never hide a defect — it strictly increases strictness, and it makes a
    re-added declaration MORE visible, not less. My first version made it manual out of a general
    "a check should not mutate what it checks" instinct, which is right for adding and wrong here;
    manual meant it would simply never run. **It announces every key it removes**, so the deletion
    half is visible in the log rather than silent."""
    base = load_decl_baseline()
    if base is None:
        return None
    live = decls_on_disk()
    orphans = sorted(base - live)
    if orphans:
        base -= set(orphans)
        write_decl_baseline(base)
        print("  baseline pruned: %d key(s) whose declaration is gone (each was a slot a new "
              "declaration could be born into already exempt)" % len(orphans))
        for k in orphans[:5]:
            print("     - %s" % k)
        if len(orphans) > 5:
            print("     … and %d more" % (len(orphans) - 5))
    return sorted(live - base)


def check_build():
    rc, out = sh("lake", "build")
    if rc != 0:
        return False, "lake build exited %d" % rc
    if re.search(r"declaration uses `sorry`|sorryAx", out):
        return False, "build contains a sorry"
    return True, "build green"


def nm(key):
    """The bare declaration name from a `file::name` baseline key."""
    return key.split("::")[-1].split(".")[-1]


def check_purity(decls):
    """Every added theorem/lemma needs a `#print axioms` line somewhere in the tree.

    ⚠ Matches a NAMESPACE-QUALIFIED print too. `#print axioms SeparatedSuccession.seq_ne_succ` is the
    correct form when the short name is ambiguous, and comparing on the bare short name missed it - a
    false positive that would have sent someone to add a duplicate purity line. Both sides are
    reduced to the short name here, so either form matches.

    Read from DISK in one pass, never `git grep`: git sees only tracked files, so a purity line in a
    newly created file read as missing."""
    if decls is None:
        return False, "NO DECLARATION BASELINE — run `batch.py decls --baseline` (failing closed)"
    missing = [nm(d) for d in missing_purity_keys(decls)]
    return (not missing), ("purity entries present" if not missing
                           else "no `#print axioms` for: %s" % ", ".join(missing))


def missing_purity_keys(decls, have=None):
    """The `file::name` keys owing a `#print axioms` line. ONE computation, two consumers.

    ⚠ The emitter needs the KEYS and the message needs the short names, and computing them twice
    would be two implementations of "which declarations are unpurified" — the mirror defect, in the
    check whose whole job is noticing an obligation nobody discharged.

    `have` is `print_axioms_on_disk()`'s pair; injectable for the selftest."""
    anywhere, own = print_axioms_on_disk() if have is None else have
    return [d for d in decls
            if nm(d) not in anywhere and nm(d) not in own.get(d.split("::")[0], ())]


def check_ssot(decls):
    if decls is None:
        return False, "NO DECLARATION BASELINE — run `batch.py decls --baseline` (failing closed)"
    p = os.path.join(REPO, "ssot.json")
    if not os.path.exists(p):
        # ⚠⚠ FAILS CLOSED — `RLYB4-4`, AND THIS RETURNED `True, "no ssot.json in tree"` UNTIL
        # 2026-09-05. That is the 0-versus-null defect in one line: the SSOT being ABSENT and every
        # declaration being COVERED produced the identical verdict, a recorded zero, and the more
        # complete the coverage looked the less had actually been read. `ssot.json` is the canonical
        # registry at the repo root, ~2.2 MB, exported by SJV — it is not an optional file, so its
        # absence means "I could not read what I judge", never "nothing is owed".
        # ⭐ Its sibling `check_purity` two functions up already got this right for a missing
        # baseline, in the same shape, with the words "(failing closed)" in the message.
        return False, ("ssot.json is MISSING from the tree — the SSOT could not be read, so no "
                       "declaration can be shown covered. This is a read failure, not a finding "
                       "about the corpus; it fails CLOSED. Run the SJV `export_full` to an "
                       "ABSOLUTE path to regenerate it.")
    blob = io.open(p, encoding="utf-8").read()
    # ⚠ EXACT names, not a substring test. `"t_snap" in blob` is true because `t_snap_derived` is in
    # there, so a brand-new `theorem t_snap` with no SSOT row passed (RLY2-8). Parse the identifiers
    # out once and compare set membership.
    present = set(re.findall(r'"(?:qualified|short)"\s*:\s*"([^"]+)"', blob))
    present |= {n.split(".")[-1] for n in present}
    missing = [d.split("::")[-1] for d in decls
               if nm(d) not in present and d.split("::")[-1] not in present]
    return (not missing), ("SSOT covers new decls" if not missing
                           else "NOT in ssot.json (SJV sync owed): %s" % ", ".join(missing))


def missing_ssot_keys(decls):
    """The `file::name` keys with no `ssot.json` row. Same one-computation rule as purity above."""
    p = os.path.join(REPO, "ssot.json")
    if not os.path.exists(p):
        return []
    blob = io.open(p, encoding="utf-8").read()
    present = set(re.findall(r'"(?:qualified|short)"\s*:\s*"([^"]+)"', blob))
    present |= {n.split(".")[-1] for n in present}
    return [d for d in decls
            if nm(d) not in present and d.split("::")[-1] not in present]


_UNRECORDED_WHY = re.compile(r"UNDECIDED|not recorded|refused|\bV\d+[a-z]?\b", re.I)


def unrecorded_line(name, rc, out):
    """The suite line for a checker that ran and left NO RECORD — exit 2 or exit 4.

    ⚠⚠ `LED-8` / `BATCH-1`: this was ONE canned sentence for every exit 2 — *"ledger unreachable or
    the record refused. No key exists for this content."* — and it was false in the commonest case:
    a `V11` refusal means a key at that basis DOES exist. The child had printed the real reason and
    the suite discarded it. So the line now (a) DISPATCHES ON THE EXIT CODE, the fleet vocabulary
    (`verdictLedger vocabulary(name='exit_code')`): 2 = could not ask, retryable; 4 = asked and
    REFUSED, terminal — and (b) QUOTES THE CHILD'S OWN REASON, because what specifically failed is the
    checker's to say. It asserts nothing about whether a key exists. ⛔ It still BLOCKS: an
    unrecorded verdict is not a pass."""
    why = [l.strip() for l in (out or "").splitlines() if _UNRECORDED_WHY.search(l)][:4]
    head = ("exit 4 — the ledger was reached and REFUSED the record (terminal: read the rule it "
            "named and fix the record or the content; do not retry)" if rc == 4 else
            "exit 2 — ran, but its verdict was NOT RECORDED (the checker could not record; its "
            "own reason follows)")
    tail = ("; ".join(why) if why else
            "the checker printed no reason — re-run it alone to see its output")
    hint = ""
    if os.environ.get("ZPLEDGER_BASIS") == common.INDEX:
        hint = (" [basis is the STAGED content: an edit that is not staged cannot be keyed to it — "
                "stage it, then re-run]")
    return "%s: %s: %s%s" % (name, head, tail, hint)


def check_suite():
    """Run the GATING checkers (`GATING_CHECKERS`) and honour their exit codes.

    ⚠ The count is NOT written here. This said "the four" while `GATING_CHECKERS` held five —
    `check_encoding.py` joined and the docstring did not — in the same commit that added
    "COUNT THE TUPLE, DO NOT TRUST A WORD" to `hooks.py`. Name the list; let the reader count it.

    ⚠ It used to discard every exit code and grep only for a `NEW …: N` line, which meant it
    returned `suite reports 0 new` for a checker that was ABSENT from disk, a checker that CRASHED,
    and a tagged POV denial — measured by `/rely` on 2026-08-10 (REL-2). A gate that reports success
    when its evidence never arrived is worse than no gate.

    ⚠ `check_poles.py` is deliberately NOT in this set (REL-3). It has no baseline and exits 1
    whenever any pole site exists — 29 today — so it is a COUNTER, not a gate, and including it
    would make the suite permanently red. It is reported separately below so the number stays
    visible. This is why "all five checkers at zero new" was only ever true of four."""
    bad = []
    for c in GATING_CHECKERS:
        p = os.path.join(BASE, c)
        if not os.path.exists(p):
            bad.append("%s: MISSING from disk — cannot be satisfied by absence" % c)
            continue
        rc, out = sh(sys.executable, p, "--block", "--record")
        # ⚠ EXIT 2 AND 4 ARE "NOT RECORDED", NOT "FAILED" — see `unrecorded_line`.
        if rc in (2, 4):
            bad.append(unrecorded_line(c, rc, out))
            continue
        if rc != 0:
            hit = [l.strip() for l in out.splitlines() if re.search(r"NEW[^:]*:\s*[1-9]", l)]
            bad.append("%s: exit %d%s" % (c, rc, (" — " + "; ".join(hit)) if hit else ""))
    return (not bad), ("suite reports 0 new (%d gating checkers)" % len(GATING_CHECKERS)
                       if not bad else "; ".join(bad))


def check_filters_frozen(state):
    now, then = checker_hashes(), state.get("checker_hashes", {})
    drift = [k for k in now if then.get(k) and now[k] != then[k]]
    return (not drift), ("filters unchanged since start" if not drift
                         else "FILTERS CHANGED MID-BATCH: %s — the batch was worked against a "
                              "moving target; re-run the worklist or start a new batch" % drift)


# ⚠⚠ THE PUSH-DIFF PROPERTY GETS ITS OWN STEP NAME, AND THE SPLIT IS THE FIX RATHER THAN A TIDY-UP.
# Two questions were sharing one name, and the WEAK one was the one recorded:
#   `pdf_coupling`  (the ledger step, produced by `record_pdf_coupling` below) asks a TREE question --
#                   does any `scripts/build_*.py` ON DISK name this PDF literally. Every PDF has a
#                   builder, so it is 40 of 40 PASS and near-vacuous as a gate. Measured 2026-09-21:
#                   `coverage_gap(step='pdf_coupling', ref='HEAD')` returns `missing: 0, nothing owed`.
#   `check_pdf_coupling` below asks a PUSH-DIFF question -- does a build script CHANGED IN THIS PUSH
#                   name this changed PDF. That is the one with teeth, and the one `P7-3` tightened.
#                   Same tree, same bytes, same moment: 33 of 40 FAIL.
#
# ⭐ THE IMPLICATION RUNS ONE WAY ONLY, AND THAT IS WHY THE NAIVE CONSULT IS FATAL. A script arriving
# in the push necessarily names the PDF on disk, so push-diff implies tree; a script merely SITTING on
# disk says nothing about what arrived, so tree does NOT imply push-diff. A consult that honoured the
# tree step's PASS would replace the strong check with the weak one on every future push -- and it
# would look SIGNED while doing it, which is worse than loosening the check openly. That is exactly
# the hole `P7-3` closed.
#
# ⛔⛔ AND UNDER `sign()` ONE NAME FOR BOTH IS UNSOUND, NOT MERELY CONFUSING. Measured by `mcpdev` in
# `core/ledger.py`, 2026-09-21: an accept is stored as `verdict: "PASS"` -- the literal string, in
# `_decided`. So a signature clearing the push-diff leg would ALSO satisfy the tree-scope property at
# that basis: ONE SIGNATURE DISCHARGING 40 SUBJECTS FOR A QUESTION NOBODY EXAMINED, on a step pinned
# at `min_coverage: 1.0`. Hence a second registered step rather than a cleverer consult.
#
# ⚠ REGISTERED, DELIBERATELY NOT ADMITTED. `sign()` validates against the REGISTRY
# (`required.v2.json`), never against gitRobot's `admission.v1.json`, and `find`/`get` do not consult
# admission at all -- so this name is signable and consultable HERE and gates nothing at the ledger.
# Fixture case H (`tools/verify/LEDGER_GATE_FIXTURE.md`): registering does not gate, promoting does.
#
# ⚠⚠ NO PRODUCER, BY DESIGN -- and saying so matters, because a registered step with no producer is
# how `pdf_coupling` ITSELF sat unsatisfiable (the `<ABSENT>` floor, invisible behind a dead `when`
# glob). The ONLY writer of this step is `sign()` / `override()`, by hand, by a person. Nothing in
# this pipeline records it, for two measured reasons: `sign()` emits DE NOVO, so a recorded FAIL is
# not needed to have something to accept; and a producer here would owe an `approved_modules` repin on
# every future `batch.py` edit -- a third one, beside `decls` and `pdf_coupling` -- for no property
# gained. The debt is made visible by the leg PRINTING it on every run instead.
PDF_COUPLING_PUSH_STEP = "pdf_coupling_in_push"


def pdf_coupling_accepts(subjects):
    """The `{path}` of `subjects` carrying a HUMAN ACCEPT at THOSE EXACT BYTES, or None if unaskable.

    ⚠⚠ `None` IS NOT AN EMPTY SET (`R-ZERONULL`). "I could not ask the ledger" and "nobody has
    accepted anything" are different facts with different remedies, and the caller treats None as
    fail-CLOSED. An empty set means the question WAS answered and the answer was "none". An accept
    path that fails open when the ledger is down is a bypass with better manners.

    ⚠⚠ THE DISCRIMINATOR IS `decided.how`, AND NOTHING ELSE CAN SERVE. A signed accept is stored with
    `verdict: "PASS"` hardcoded, so BY VERDICT ALONE a human accept and a mechanical pass are
    indistinguishable -- a consult keyed on the verdict field cannot tell them apart and would clear
    this leg for ever off the tree-scope record. `tier` cannot separate them either: `override()` also
    defaults to `H`.

    ⚠ ONLY `signature` CLEARS, AND `override` DELIBERATELY DOES NOT. They are opposite signals: an
    accept says the finding STANDS and we ship anyway (corpus debt), an override says the STEP is
    defective. An override here would assert `check_pdf_coupling` erred -- a different decision with a
    different remedy -- so it is refused rather than quietly honoured. Widening to `override` is a
    one-word change and wants its own ruling, not an inference from this one.

    ⚠ THE PAIR IS THE KEY, NEVER THE BLOB ALONE. `find(subject_sha=...)` matches any record naming
    that blob ANYWHERE, so two byte-identical PDFs at different paths would clear each other. The
    `(path, git_blob_id)` pair is what `R-GATED` requires, and it is re-checked inside the record.
    """
    accepted = set()
    for s in subjects:
        path = (s.get("path") or "").replace("\\", "/")
        blob = s.get("git_blob_id") or ""
        # A subject that cannot be keyed to bytes is one no accept could bind to. Fail closed rather
        # than skip it: a silently unkeyable offender is an exemption with no expiry.
        if not path or not blob:
            return None
        try:
            out = record._call("find", {"step": PDF_COUPLING_PUSH_STEP,
                                        "subject_sha": blob, "limit": 500})
        except Exception:                          # noqa: BLE001 — cannot ask == None
            return None
        if not out or not out.get("ok") or not isinstance(out.get("records"), list):
            return None
        for rec in out["records"]:
            decided = rec.get("decided") or {}
            if decided.get("how") != "signature" or not decided.get("who"):
                continue
            if any((sub.get("path") or "").replace("\\", "/") == path
                   and sub.get("git_blob_id") == blob
                   for sub in (rec.get("subjects") or [])):
                accepted.add(path)
                break
    return accepted


def _script_at_push(path, ranges):
    """The text of build script `path` as the PUSH carries it, or None if it cannot be read there.

    ⚠ `REL8-5`: the pairing read the script from the WORKING TREE, so a commit adding a PDF while
    renaming the output literal in its script passed — the disk copy still named the PDF. With
    `ranges` the bytes are read AT EACH PUSHED TIP (`git show <tip>:<path>`, stdout only) and a pairing
    holds if any tip's copy names the PDF; a script absent or unreadable at every tip returns None and
    pairs nothing (fails closed). A manual run (`ranges is None`) judges the working tree, so it reads
    the disk, matching `changed_files(None)`."""
    if ranges is None:
        try:
            return io.open(os.path.join(REPO, path), encoding="utf-8", errors="replace").read()
        except OSError:
            return None
    texts = []
    for tip in _range_tips(ranges):
        rc, out, _err = sh_split("git", "show", "%s:%s" % (tip, path))
        if rc == 0:
            texts.append(out)
    return "\n".join(texts) if texts else None


def shared_layer_note(changed):
    """A sentence naming the SHARED build layer when it is in `changed`; '' otherwise.

    ⚠ `COUPLE-SHARED-1`: a `zp_utils.py` change moves EVERY rendered PDF, and this leg reported it as
    N PDFs "with no build script in this push" — the shared producer present and unnamed. The note
    names it. ⛔ IT CHANGES NO DECISION: the leg still requires a per-document pairing or a human
    accept, because a shared-layer change moves more deposited artifacts, not fewer. The list is
    `check_hashes.SHARED_BUILD`, the one definition of the shared layer; unreadable -> no claim."""
    try:
        import check_hashes as _ch
        shared = ["scripts/%s" % n for n in _ch.SHARED_BUILD]
    except Exception:                                         # noqa: BLE001 — no claim on failure
        return ""
    hit = sorted(set(shared) & {f.replace("\\", "/") for f in changed})
    if not hit:
        return ""
    return ("  ⚠ THE SHARED BUILD LAYER IS IN THIS PUSH (%s): it moves every rendered PDF, so these "
            "were likely produced by it rather than by nothing. That still does not pair them — "
            "rebuild each with its own script in the push, or accept them at these bytes "
            "(`%s`); `check_hashes.py --seed-shared` re-seeds the shared fingerprint."
            % (", ".join(hit), PDF_COUPLING_PUSH_STEP))


def check_pdf_coupling(ranges=None):
    """A changed PDF must arrive with the build script that produced it.

    ⚠ Measured by /rely pass 6: a PDF-only commit cleared EVERYTHING — `scope: 0 reviewable
    file(s)`, `prepush PASS`, `check_hashes` 0, `ship.py post` PASS — because PDFs are classified as
    data and data cannot stale a review (correctly: that was the fix for the old HEAD-equality
    scheme). But a PDF is the artifact a Zenodo DOI freezes PERMANENTLY, and the only thing tying it
    to reviewed prose was the manual `scripts/` mirror convention with no mechanical backstop.

    This does not review the PDF — nothing can. It enforces the coupling CLAUDE.md already states:
    *"whenever a build script produces a newly committed PDF, copy the script to `scripts/` as part
    of the same commit."* With the script in the push, its prose IS reviewable and the existing
    gates apply. A PDF arriving alone means either a hand-edited artifact or a script change that
    skipped the mirror — both worth stopping before they become permanent."""
    changed = changed_files(ranges)
    pdfs = [f for f in changed if f.lower().endswith(".pdf")]
    # Cheap exit FIRST. Almost every push carries no PDF at all, and the deletion filter below
    # spawns a `git diff` per range; running it to discover there was nothing to filter is a
    # subprocess bought for no information. (The early return was here, and the deletion narrowing
    # displaced it — measured when Tim asked whether this fires every iteration. It did.)
    if not pdfs:
        return True, "no PDF in scope"
    # ⚠ DELETIONS ARE EXEMPT — there is no artifact left to review, and a bulk cleanup is the
    # commonest PDF-only commit there is. Unnarrowed, this fired on `f09ed5c`, the `historical/`
    # retirement (179 removals), which is precisely the cry-wolf shape CLAUDE.md says to narrow
    # rather than tolerate. A gate that fires on correct work gets muted, and then it protects
    # nothing.
    if ranges is not None:
        alive = set()
        for r in ranges:
            # ⚠ NO PATHSPEC. It used to pass `-- "*.pdf"`, which git matches CASE-SENSITIVELY while
            # the selection above lowercases — so a hand-crafted `ZZ_Handcrafted.PDF` was selected
            # and then filtered straight back out as "deleted", and a push containing nothing else
            # reported `prepush PASS`, exit 0, `0 reviewable file(s)`. That is pass 6's BLOCKING-3
            # reopened through the FILENAME, one line from where it was fixed (/rely pass 7).
            # Listing every surviving path and filtering in Python keeps ONE definition of "is a
            # PDF" — the `.lower()` above — instead of two that disagree.
            rc, out, _err = sh_split("git", "diff", "--name-only", "--diff-filter=d", r)
            if rc != 0:
                return False, ("git could not resolve range %r for the PDF check — refusing to "
                               "report a scope it could not read" % r)
            alive.update(l.strip() for l in out.splitlines() if l.strip())
        pdfs = [f for f in pdfs if f in alive]
    else:
        pdfs = [f for f in pdfs if os.path.exists(os.path.join(REPO, f))]
    if not pdfs:
        return True, "no added or modified PDF in scope"
    # ⚠ `scripts/build_*.py` ONLY. Any `scripts/*.py` was too wide: `scripts/scan_pdfs.py` NAMES 25
    # of the 40 root PDFs (measured) and BUILDS none, so one touch to it certified four hand-tampered
    # PDFs as "each paired with the script naming it". A scanner mentions every artifact by design;
    # only a builder is evidence that an artifact was rebuilt. Consequence measured before applying:
    # 0 of 40 root PDFs lose their pairing, and `scan_pdfs.py` is the only multi-namer
    # (/rely pass 9, REL9-1).
    scripts = [f for f in changed if f.lower().startswith("scripts/build_")
               and f.lower().endswith(".py")]
    # ⚠ PAIR EACH PDF WITH THE SCRIPT THAT BUILDS IT. Accepting ANY `scripts/*.py` is what the code
    # did while the docstring promised the producing script, so one unrelated new script satisfied a
    # range carrying five changed PDFs (/rely pass 7). 41 of 43 build scripts name their own output
    # filename as a literal, so the mapping is exact and needs no table to go stale.
    unpaired = []
    _texts = {s: _script_at_push(s, ranges) for s in scripts}
    for pdf in pdfs:
        base = os.path.basename(pdf)
        hit = False
        for s in scripts:
            src = _texts[s]
            if src is None:
                continue                      # unreadable at the pushed tip pairs nothing
            # ⚠ ANCHORED. An unanchored `base in src` pairs by SUBSTRING: 40 bytes of junk named
            # `Companion.pdf` was certified "paired with the script naming it", because every
            # companion script contains `ZP-A_Illustrated_Companion.pdf`. A filename is a token, not
            # a substring (/rely pass 8, REL8-1).
            # The lookbehind excludes `.` but the lookahead did not, so `X.pdf` matched inside
            # `X.pdf.bak` — an asymmetry, not a decision (/rely pass 9, REL9-4). No such token exists
            # in the corpus today; symmetric is still what was meant.
            if re.search(r"(?<![\w.\-])" + re.escape(base) + r"(?![\w.])", src):
                hit = True
                break
        if not hit:
            # ⚠ THE REPO-RELATIVE PATH, NOT THE BASENAME. It used to collect `base`, which reads
            # identically for the 40 root-level PDFs and is NOT a key: an accept binds to
            # `(step, path, git_blob_id)` and `common.ledger_subjects` resolves a repo-relative
            # path. A basename would resolve nothing, or -- worse -- the wrong file of that name
            # under `historical/`. The message below still PRINTS basenames; only the key changed.
            unpaired.append(pdf)
    if not unpaired:
        return True, "%d PDF(s), each paired with the script naming it (%s)" % (
            len(pdfs), ", ".join(scripts[:3]))
    unpaired = sorted(unpaired)
    _why = ("%d of %d changed PDF(s) have no build script IN THIS PUSH that names them "
            "(%s) — a DOI freezes the PDF permanently, and the build script is the only "
            "reviewable surface it has. Mirror the producing script per CLAUDE.md. "
            "Two build scripts do not name their output literal; if this is one, say so."
            % (len(unpaired), len(pdfs),
               ", ".join(os.path.basename(u) for u in unpaired[:3])))
    _why += shared_layer_note(changed)

    # ⭐⭐ THE RATCHET: CONSULT THE LEDGER BEFORE BLOCKING (Tim, 2026-09-21, "update the behavior so
    # the ratchet works"; the requirement it comes from is "you just have to be able to sign off on
    # them as a human accepting the fact that they are not all fully remediated yet").
    #
    # ⛔ THIS IS NOT A LOOSENING OF THE PAIRING TEST, AND IT MUST NEVER BECOME ONE. `P7-3` tightened
    # the pairing from *any* `scripts/*.py` to *a script that NAMES the PDF*, and the shared-layer
    # rebuild that motivated this change would have sailed straight through the hole `P7-3` closed.
    # The finding above is computed identically and still FAILS; what follows asks only whether a
    # PERSON has already looked at this exact finding, at these exact bytes, and accepted it as debt.
    #
    # ⚠⚠ AND THE CONSULT IS THE DANGEROUS HALF OF THIS FILE. `LEDGER_GATE_FIXTURE.md`: "Cases C and K
    # are the dangerous ones to get wrong. Everything else fails closed; those two are the paths that
    # let a push through." Every branch below therefore names why it blocks, and only the last one
    # returns True.
    try:
        subjects, skipped = common.ledger_subjects(unpaired, ref="HEAD")
    except common.BasisUnresolved as e:
        # ⚠ NO VERIFIED SUBJECTS IS NOT "NO SUBJECTS" (`R-ZERONULL`). Without keys no accept can be
        # looked up, so the leg returns False with its own reason — never the empty-subjects path,
        # which would ask the ledger about nothing and read the silence as owed or as accepted.
        return False, (_why + "  ⚠ AND THE OFFENDING PATHS COULD NOT BE KEYED (%s: %s), so no "
                       "accept could be looked up. UNDECIDED, fails CLOSED — fix the basis or "
                       "gitRobot's reachability and re-push." % (type(e).__name__, e))
    if skipped:
        # ⚠ AN OFFENDER WE CANNOT KEY TO COMMITTED BYTES CANNOT BE ACCEPTED, so no accept is even
        # looked for. An exemption that cannot say WHICH BYTES either never expires or expires by
        # someone noticing -- which is the `DEFECTS.md` accept route this design exists to replace.
        return False, (_why + "  ⚠ AND %d OFFENDING PATH(S) CANNOT BE KEYED TO COMMITTED BYTES (%s), "
                       "so no signature could bind to them and none was sought. Fails CLOSED."
                       % (len(skipped), "; ".join("%s: %s" % (p, r) for p, r in skipped[:2])))
    accepted = pdf_coupling_accepts(subjects)
    if accepted is None:
        # ⚠⚠ THE FORCED ANSWER, settled before this was built: LEDGER UNREACHABLE => BLOCK. An accept
        # path that fails OPEN when the ledger is down is a bypass with better manners, and the exact
        # inversion of `R-GATED`'s fail-closed requirement.
        return False, (_why + "  ⚠ AND THE LEDGER COULD NOT BE ASKED whether these bytes carry a "
                       "human accept, so this is UNDECIDED rather than owed. Fails CLOSED — fix the "
                       "reachability and re-push; do not read an outage as a finding about the PDFs.")
    owed = [u for u in unpaired if u not in accepted]
    if owed:
        _hint = _write_pdf_coupling_owed(subjects, owed)
        return False, (_why + "  ⚠ %d of the %d carry a human accept at these bytes and %d do NOT: "
                       "%s. Accept those too, or pair them with the script that builds them.%s"
                       % (len(unpaired) - len(owed), len(unpaired), len(owed),
                          ", ".join(os.path.basename(o) for o in owed[:3]), _hint))

    # ⚠⚠ ACCEPTED AS CARRIED DEBT — THE ONE PATH HERE THAT LETS A PUSH THROUGH WITH A RED FINDING.
    # Fixture case K: "the allow line must make that visible rather than rendering identically to a
    # clean pass." So it prints its own block, on every run, and the leg's one-line summary leads
    # with the words rather than with a count.
    print("")
    print("  ⚠⚠ pdf coupling: ACCEPTED AS CARRIED DEBT — NOT a clean pass.")
    print("     %d unpaired PDF(s) are shipping with the finding STANDING, on a human signature"
          % len(unpaired))
    print("     over these exact bytes (`%s`, decided.how=signature)." % PDF_COUPLING_PUSH_STEP)
    for u in unpaired[:10]:
        print("       debt  %s" % u)
    if len(unpaired) > 10:
        print("       debt  ... and %d more" % (len(unpaired) - 10))
    print("     The accept binds to (step, path, git_blob_id), so it EXPIRES BY CONSTRUCTION the")
    print("     instant any of these files changes — there is no expiry logic and nothing to")
    print("     remember. Each discharges when its document is next rebuilt with its own script.")
    return True, ("ACCEPTED AS CARRIED DEBT — %d of %d changed PDF(s) are unpaired and every one "
                  "carries a `%s` signature at these bytes; the FAIL stands as debt"
                  % (len(unpaired), len(pdfs), PDF_COUPLING_PUSH_STEP))


def _write_pdf_coupling_owed(subjects, owed):
    """Dump the owed `(path, git_blob_id)` set so the printed `sign()` route is actually followable.

    ⚠ THE POINT IS THAT A ROUTE NOBODY CAN WALK IS THE DEFECT THIS WHOLE CHANGE FIXES. The six hook
    lines pointed at `.claude-local/DEFECTS.md`, which nothing reads; telling an operator to `sign()`
    33 subjects while making them hand-derive 33 blob ids would be the same failure in a new costume.
    Returns a sentence to append to the leg's message, or "" if the dump could not be written -- a
    failure here must never change the VERDICT, only the helpfulness of the refusal."""
    try:
        _basis = common.ledger_basis("HEAD")
    except common.BasisUnresolved:
        return ""
    payload = {
        "step": PDF_COUPLING_PUSH_STEP,
        # ⚠ `common.ledger_basis`, NOT `record.read_ref`. The first draft used `read_ref("HEAD")`,
        # which resolves the INDEX sentinel and returns every other ref UNCHANGED -- so the dump
        # said `basis: {"value": "HEAD"}` and an accept written from it would have bound to a MOVING
        # LABEL rather than to a commit, quietly re-applying itself at whatever HEAD became. This is
        # the one function that resolves a basis the way the WRITE path does, and it also supplies
        # `resolved_from`, which V1 requires and a hand-built block forgets.
        "basis": _basis,
        "why": ("Each subject is a PDF this push changes with no build script in the push naming "
                "it. Signing accepts the finding as carried debt at THESE bytes only."),
        "subjects": [s for s in subjects if s.get("path") in set(owed)],
    }
    try:
        p = os.path.join(PRIV, "pdf_coupling_owed.json")
        with io.open(p, "w", encoding="utf-8") as fh:
            fh.write(json.dumps(payload, indent=2, sort_keys=True))
    except OSError:
        return ""
    return ("  The exact subject set is written to %s — pass it to "
            "`verdictLedger sign(step='%s', subjects=..., who=..., reason=...)`."
            % (os.path.join(PRIV, "pdf_coupling_owed.json"), PDF_COUPLING_PUSH_STEP))


# ⚠⚠ THE PATHSPEC AND `prior_art`'s REGISTRY `scope` MUST AGREE, AND NEITHER ALONE DOES ANYTHING.
# The leg blocks on `touched ∩ owing`: this function supplies `touched`, and `owing` comes from
# `coverage_gap`, which only ever returns paths inside the step's registry `scope`. Widen one and the
# intersection stays empty — the obligation silently does not exist. If you add an extension here,
# add the matching glob to `prior_art.scope` in `required.v2.json` in the SAME change.
#
# ⚠⚠ `*.md` JOINED 2026-09-17, IN THE SAME COMMIT as `prior_art.scope` in `required.v2.json`, which
# is what the paragraph above demands. Tim: *"My concern on the prior art is that it probably
# shouldn't just be restricted to the lean files."* Re-derived on a 29-commit arc, ENFORCED being
# `touched ∩ owing` and NOT `owing`: today 44/0/**0**; registry widened ALONE 44/6/**0** — inert,
# and it LOOKS landed because `owing` moves 0→6; both routes widened 77/6/**6**. The first proposal
# widened the registry only, and the deciding number was measured THROUGH THE LEDGER, which reads
# registry scope and cannot reach this constant — a true number about the wrong object.
# ⚠ OVER-MATCHING HERE IS SAFE, UNDER-MATCHING IS THE FAILURE MODE. This tuple has no exclusion
# mechanism, so `touched` over-matches; `owing` honours `prior_art`'s `scope_exclude`, so the
# intersection filters the excluded paths back out. `CLAUDE.md` is the live example — matched here,
# excluded there, never owed.
# ⛔ THIS COMMENT ONCE NAMED `tools/*.md` AS THAT EXAMPLE AND WENT FALSE INSIDE ITS OWN COMMIT.
# `b13e67cc` struck `tools/*.md` from `prior_art.scope_exclude` in the SAME change that wrote the
# sentence relying on it, so the claim was true when drafted and false when committed — 29
# `tools/*.md` paths now appear in `prior_art`'s owing list. Found by `/rely` 2026-09-18 (`O1`).
# **A worked example is a FACT ABOUT THE CURRENT CONFIG, not an illustration** — it goes stale
# exactly like a count, and it goes stale fastest in the commit that edits the config it cites.
ATTRIBUTABLE = ("*.lean", "scripts/build_*.py", "*.md")


def changed_attributable(ranges=None):
    """The files this push touches that OWE prior-art attribution. Range-aware, per REL-1.

    ⚠⚠ `scripts/build_*.py` JOINED 2026-09-13 (Tim: *"adjust the scope so the build scripts are also
    in scope (when edited, just like anything else)"*), and the measured reason is that a build
    script is the ONLY surface where a false claim about someone else's work reaches a DOI. A
    prior-art round that night found a wheel/meadow mischaracterisation live in two published PDFs;
    `prior_art` had never covered `scripts/` at all, and the round only saw them because the agent
    swept `--full` on its own initiative. The prose gates DO read these files — they are in
    `adversary` and `editorial` scope — but neither gate's job is *is this claim about an external
    structure placed against the work that owns it*. That is this one's, and it was not asked.

    ⚠ The containment property is unchanged and is the whole design (Tim, 2026-09-01): *"whenever a
    specific file gets edited that that file is properly attributed … the current logic I think hits
    the entire corpus. and that is impossible to fill at one time."* You owe attribution for what you
    TOUCHED and never for the corpus — widening the set of attributable EXTENSIONS does not widen the
    set of files any one push owes.
    """
    # ⚠ ACMR: a DELETED file owes nothing. Without the filter a pure deletion is named and a
    #   verdict is demanded at bytes that no longer exist — unsatisfiable by construction, because
    #   no review can attribute a file that is gone. Found by /rely (RLY42-2) on a real deletion
    #   commit while the leg was still latent behind RLY42-1; it goes live the moment that is fixed.
    #   Added/Copied/Modified/Renamed all owe attribution at their new bytes; Deleted does not.
    seen = set()
    targets = ["--"] + list(ATTRIBUTABLE)
    if ranges is not None:
        for r in ranges:
            rc, out, _err = sh_split("git", "diff", "--name-only", "--diff-filter=ACMR", r, *targets)
            if rc != 0:
                die("git could not resolve range %r for the prior-art attribution leg — refusing "
                    "to report a scope it could not read:\n%s" % (r, _err or out))
            seen.update(l.strip() for l in out.splitlines() if l.strip())
    else:
        rc, out, _err = sh_split("git", "diff", "--name-only", "--diff-filter=ACMR", "HEAD", *targets)
        if rc != 0:
            die("git failed listing changed attributable files:\n%s" % (_err or out))
        seen.update(l.strip() for l in out.splitlines() if l.strip())
    return sorted(seen)


# The ledger step the `prior-art attrib` BLOCK leg below asks about. A NAME, not a second list: the
# leg reads it and so does `ENFORCED_REVIEW_LEGS`, so the review report cannot drift from the leg.
ATTRIB_STEP = "prior_art"


def check_prior_art_attribution(ranges=None):
    """EVERY ATTRIBUTABLE FILE THIS PUSH EDITS MUST CARRY A PASSING `prior_art` VERDICT AT ITS CURRENT BYTES.

    ⚠ "ATTRIBUTABLE" IS `ATTRIBUTABLE` ABOVE, NARROWED BY `prior_art`'s REGISTRY SCOPE — not
    ".lean". This sentence said `.lean` through TWO widenings (`scripts/build_*.py` 2026-09-13,
    `*.md` 2026-09-17) and the prepush manifest line said it on every run, which `R-PRECOMMIT`
    points readers at. Second occurrence of the same staleness = a class (RLY-PA-3); a
    string-versus-`ATTRIBUTABLE` check is the cheap detector and is not built yet.

    ⚠⚠ PER FILE, NEVER PER CORPUS, AND THE DIFFERENCE IS THE WHOLE POINT (Tim, 2026-09-01: *"my goal
    be lean files specifically that whenever a specific file gets edited that that file is properly
    attributed. the current logic I think hits the entire corpus. and that is impossible to fill at
    one time."*). The registry's `scope` is a STATIC GLOB, so the strongest thing it can say is "all
    218 `.lean` files" — which reads as a 215-file backlog nobody can ever clear, and which does not
    block anyway, because narrowed coverage is REPORTED rather than enforced. Measured 2026-09-01:
    promoting `prior_art` with `scope: ZeroParadox/*.lean` gave `have 3 / missing 215` and the only
    thing that actually blocked was an unrelated recorded FAIL. So the glob delivers an impossible
    number AND no per-file enforcement — backwards on both counts.

    The obligation is CONTAINMENT OF THE CHANGED SET, and it is satisfiable incrementally by
    construction: you owe attribution for the files you touched and never for the ones you did not.
    Touch nothing, owe nothing. Touch one file, run one review.

    ⚠ IT LIVES HERE BECAUSE ONLY HERE KNOWS THE RANGE. REL-1: the working tree is empty post-commit,
    so `prior_art`'s scope cannot be narrowed to "this push" anywhere in the registry. The ledger
    stays the single source of what was VERDICTED; this intersects that with what changed. When
    verdictLedger gains a dynamic scope (its R-8/R-9), this leg is what moves into it.

    ⚠ FAILS CLOSED ON AN UNREACHABLE LEDGER. `owing_paths` returns None rather than an empty set,
    for the reason the whole file repeats: "I could not ask" must never render as "nothing is owed".
    """
    touched = changed_attributable(ranges)
    # ⚠⚠ NAME THE SET THAT WAS MEASURED, NEVER "this push". With `ranges` this reads the
    # PUSHED RANGE and the phrase is true; without them it reads the WORKING TREE, and the same
    # phrase then described a nine-commit push owing four attributed files as owing none
    # (measured 2026-09-12). Every count below was true; the referent was not. `cmd_prepush`
    # now refuses the manual case that made this reachable — see `unjudgeable_scope` — so this
    # is the second line of defence rather than the first, and it says which set it read.
    basis = "the pushed range(s)" if ranges is not None else "the WORKING TREE (manual run)"
    if not touched:
        return True, ("no attributable file in %s — no attribution owed" % basis)
    ref = record.read_ref("HEAD")
    owing = record.owing_paths(ATTRIB_STEP, ref, "push")
    if owing is None:
        return False, ("could not ask the ledger which attributable files carry a passing prior_art "
                       "verdict, so the %d edited file(s) in %s cannot be shown attributed. "
                       "An unreachable ledger is not a clean bill." % (len(touched), basis))
    gap = sorted(set(touched) & set(owing))
    if not gap:
        # ⚠⚠ DO NOT SAY "all N carry a passing verdict". `touched` is the PATHSPEC's answer and
        # `ATTRIBUTABLE` has no exclusion mechanism, so it includes files `prior_art`'s registry
        # scope EXCLUDES — which are never judged and CANNOT be. Counting them as attributed was
        # RLY-PA-1 (2026-09-17, /rely): widening the pathspec to `*.md` took the blind set from 1
        # to 83, and the leg reported `all 4 … carry a passing prior_art verdict` over a range
        # whose 4 files included `CLAUDE.md` and two `tools/process/` docs. TRUE OF THE DECISION,
        # FALSE OF THE OUTPUT — the intersection was right and the sentence about it was not.
        # ⚠ The number that is KNOWN here is the GAP, not the judged set: `owing` names what is in
        # scope and unverdicted, so a file absent from it is either verdicted OR out of scope, and
        # this function cannot tell those apart without reimplementing the ledger's glob matcher.
        # A second copy of that matcher is the same one-of-two-routes defect this leg exists to
        # avoid, so the message reports what it can defend and names scope as the discriminator.
        return True, ("no file edited in %s owes an unmet prior_art verdict (%d attributable "
                      "path(s) touched; `prior_art`'s registry scope decides which of them are "
                      "judged at all, and files it excludes are NOT attributed by this line)"
                      % (basis, len(touched)))
    return False, ("%d of %d attributable file(s) edited in %s have NO passing prior_art "
                   "verdict at their current bytes: %s%s — run `/prior-art-review` over these "
                   "files and let it record. You owe the files you TOUCHED, never the corpus."
                   % (len(gap), len(touched), basis, ", ".join(gap[:4]),
                      "" if len(gap) <= 4 else " (+%d more)" % (len(gap) - 4)))


def check_trigger5(ranges=None):
    """Prior-art trigger 5: a new `.lean` file, or >=50 inserted `.lean` lines.

    Range-aware for the same reason as `changed_files` (REL-1): computed against the working tree
    it reads 0 insertions once committed, so the prior-art requirement silently switched off at
    exactly the moment of pushing."""
    if ranges is not None:
        ins, newfile = 0, False
        for r in ranges:
            rc, out, _err = sh_split("git", "diff", "--numstat", r, "--", "*.lean")
            # ⚠ A git error must never read as "no insertions". Unfixed, a bogus range returned
            # (False, 0, False) — i.e. PRIOR-ART NOT REQUIRED — which is a fail-open on the one
            # trigger that cannot be recovered later.
            if rc != 0:
                die("git could not resolve range %r for trigger 5 — refusing to report a scope "
                    "it could not read:\n%s" % (r, _err or out))
            ins += sum(int(l.split("\t")[0]) for l in out.splitlines()
                       if l.split("\t")[0].isdigit())
            rc2, st, _err2 = sh_split("git", "diff", "--name-status", r, "--", "*.lean")
            if rc2 != 0:
                die("git could not resolve range %r for trigger 5:\n%s" % (r, _err2 or st))
            newfile = newfile or any(l.startswith("A") for l in st.splitlines())
        return (ins >= 50 or newfile), ins, newfile
    _rc, out, _err = sh_split("git", "diff", "--numstat", "--", "*.lean")
    ins = sum(int(l.split("\t")[0]) for l in out.splitlines() if l.split("\t")[0].isdigit())
    _rc2, untracked, _err2 = sh_split("git", "ls-files", "--others", "--exclude-standard", "--",
                                      "*.lean")
    newfile = bool(untracked.strip())
    return (ins >= 50 or newfile), ins, newfile


# Not reviewable: no prose or construction a gate could read. DELIBERATELY NARROW — this is
# default-reviewable, explicit-exclude, so anything not named here must be covered by a review.
#
# ⚠ These two tuples reproduce the retired shell hook's filter EXACTLY, and the parity matters:
# porting it, I widened `.json` from two named files to the whole extension, which silently dropped
# `.zenodo.json` and `tools/registry/tag_vocab.json` out of review coverage — `.zenodo.json` is the
# text Zenodo reads at release time and cannot be corrected afterwards. I also added `.svg`,
# `.lock`, and matched `claude.md` at ANY depth rather than only the root. All four were
# regressions found by `/rely` on 2026-08-10. **Widening an exclusion list is how coverage dies
# quietly: nothing fails, a file simply stops being looked at.**
DATA_EXT = (".pdf", ".png", ".jpg", ".jpeg", ".ico", ".olean",
            # ⚠ FONTS ADDED 2026-08-15, and this is the one direction the warning above does NOT
            # cover. That warning is about WIDENING an exclusion so text quietly stops being
            # reviewed. This is a genuinely NEW binary type entering the repo: the 13 TTFs were
            # published with the build scripts, and `reviewable_changed()` counted every one as
            # prose — so a push would have demanded that an editorial reviewer read, and hash into
            # its signal, thirteen binary font files.
            #
            # Not a judgement call, and not decided here: `.gitattributes` already classifies
            # `*.ttf`/`*.otf`/`*.woff`/`*.woff2` as `binary`, precisely so git never touches their
            # bytes. This list now agrees with that independent authority instead of contradicting
            # it. A font carries no prose; there is nothing for a prose gate to review.
            ".ttf", ".otf", ".woff", ".woff2")

# Excluded by exact repo-relative path, never by basename at any depth. CLAUDE.md is the operating
# manual and its own header exempts it from the editorial and adversary gates; the other two are
# generated data.
EXEMPT_PATHS = ("claude.md", "ssot.json", "lake-manifest.json")

# ⚠⚠ THIS WIDENS AN EXCLUSION SURFACE, WHICH THE COMMENT ABOVE WARNS AGAINST. Read the argument
# before trusting it, because "nothing fails, a file simply stops being looked at" is the failure
# mode and it is invisible.
#
# The claim is that this is NOT a coverage loss, and it rests on two facts that can be checked:
#
#   1. COVERAGE IS UNCHANGED, NOT REDUCED. Until 2026-08-15 every one of these paths lived in
#      gitignored `.claude-local/`. `changed_files()` reads git, so the editorial and adversary
#      gates have NEVER seen them - not once. Making them tracked and then demanding retroactive
#      prose review of ~30 Python files would be a new obligation invented by a directory move,
#      not a restored one.
#
#   2. THE LAYER IS REVIEWED, BY THE RIGHT GATE, AND THE LEDGER ENFORCES IT. `/rely` is the measured
#      persona for the verification layer, `ROUTING` above declares exactly this prefix, and the
#      registry's `rely` step is admitted at TAG (`gitRobot admission(action='tag')`), where
#      `coverage_gap(step='rely', action='tag')` names every path it still owes. So a checker change
#      is routed away from two prose gates that cannot judge it and toward the one that can. The
#      price of this exemption is that `rely` stays ADMITTED at tag; if it is ever narrowed out of
#      the tag set, THIS exemption becomes a hole and must go with it. They are a pair.
#      ⚠ No PUSH leg here blocks on `/rely` coverage (Tim's ruling 2026-10-14): a push may carry
#      verification-layer changes `/rely` has not yet examined, and a release cannot.
#
# What is deliberately NOT exempt: `scripts/**` (build scripts render into published PDFs, so their
# prose is publication prose) and every method document - DEFECT_CLASSES.md, vocabulary_reference.md,
# the protocols - which stay private precisely because publishing them needs both gates.
#
# ⚠ `.claude/commands/` WAS in this tuple for about an hour and was REMOVED. The argument for
# exempting it was that gate briefs are operating instructions, like CLAUDE.md, which is published
# and exempt. That reasoning is wrong here, and VERIFICATION_BUILDOUT.md Phase 7 already settles it:
# it lists "the gate command files" under what PUBLISHING THE METHOD means, and attaches
# "Externally-facing copy -> both gates fire ... Non-discretionary." CLAUDE.md is exempt because it
# is an internal manual that happens to sit in a public repo; the gate briefs are being published
# ON PURPOSE, as the artifact showing how this project reviews itself. That is publication.
#
# ⚠ `tools/process/` JOINED THIS TUPLE 2026-08-20, and it is the one case where the reasoning the
# paragraph above rejects is nonetheless correct — so the difference has to be stated, not felt.
# `.claude/commands/` is published ON PURPOSE, as the artifact showing how this project reviews
# itself; that is publication and both prose gates fire on it. `tools/process/` is the opposite: it
# is the BODY of CLAUDE.md, split out only so the injected file can be a routing table instead of
# the payload, and CLAUDE.md is exempt. Moving a paragraph across a file boundary must not invent a
# review obligation the paragraph did not have while it was inline — that would make the split cost
# a gate round per extraction and the cleanup would stop.
# The exemption is DECLARED in CLAUDE.md's header rather than inferred here, and `ROUTING` above
# fires on this exact prefix, so the pair covers the same set. Fence: anything in there asserting
# mathematics belongs in the corpus and is gated normally.
# ⚠⚠ WIDENED TO `tools/` 2026-09-18 IN THE SAME COMMIT AS `ROUTING` AND `rely.scope`, because the
# three describe one fact and the file's own history is that editing one alone breaks it. The
# exemption and its compensating route must cover the SAME SET or the pair is a story.
EXEMPT_PREFIXES = ("tools/",)


def _range_tips(ranges):
    """The TIP revision of each pushed range — the bytes that will land on the remote.

    A range is `<base>..<tip>`; a bare rev is its own tip. The LEFT side is what the remote already
    has, so every question about what a push PUBLISHES belongs at the right. `a...b` (symmetric
    difference) takes the same answer.

    Its caller is `check_signals`, which asks the ledger about review freshness at the content being
    PUSHED (RLY36-2).

    ⚠ A blank or malformed range yields `HEAD` rather than an empty ref — `step_status("")` would
    ask the ledger about nothing and get a confident answer about the wrong thing. Empty push scopes
    are fenced upstream in `changed_files` (the `is not None` guard, /rely pass 2).

    ⚠⚠ THIS IS ONE DEFINITION BECAUSE IT WAS BRIEFLY TWO. A second `_range_tips` was added lower in
    this file on 2026-08-26 without checking whether the name was taken; Python takes the LAST
    definition silently, so a helper written for `check_signals` quietly replaced the one the
    stale-at-tip leg had been using. Nothing caught it — not the selftest, not `check_checkers`, not
    the commit gate — because a shadowed duplicate is valid Python. `SH-7` (duplicated definition
    that drifted) is the recurring shape `selfheal.py` counts and it had no class row."""
    tips = []
    for r in (ranges or []):
        r = (r or "").strip()
        if not r:
            continue
        tips.append(r.rsplit("..", 1)[-1].strip() or "HEAD")
    return tips or ["HEAD"]


def changed_files(ranges=None):
    """Files changed — from the pushed RANGES when given, else the working tree.

    ⚠ This is the `REL-1` fix. The working-tree form (`git diff --name-only HEAD`) is correct
    BEFORE a commit and EMPTY after it, so every consumer went vacuous at push time. The hook knows
    the ranges being pushed, so when it calls in it supplies them and the answer is correct at the
    only moment that matters. Manual `precommit` use passes nothing and gets the working tree,
    which is right for that moment."""
    # ⚠ `is not None`, NEVER truthiness. An EMPTY range list means "a push whose scope is genuinely
    # empty", which is not the same as "no ranges supplied, fall back to the working tree" — and
    # `if ranges:` conflated them. Measured by /rely pass 2: `prepush --ranges ""` skipped the
    # fail-closed guard, fell through to the working tree, and printed `prepush PASS` on a clean
    # tree; reachable from the hook, since it passes `",".join(ranges)` unconditionally, so
    # `hooks.py pre-push < /dev/null` exited 0. The first fix guarded the FLAG; the property is SCOPE.
    if ranges is not None:
        out = set()
        for r in ranges:
            rc, o, e = sh_split("git", "diff", "--name-only", r)
            if rc != 0:
                # A git error must never be read as data.
                die("git could not resolve range %r — refusing to guess a scope:\n%s" % (r, e or o))
            out |= {l.strip() for l in o.splitlines() if l.strip()}
        return sorted(out)
    rc, out, err = sh_split("git", "diff", "--name-only", "HEAD")
    if rc != 0:
        die("git failed listing changed files:\n%s" % (err or out))
    return [l.strip() for l in out.splitlines() if l.strip()]


def reviewable_changed(ranges=None):
    """Changed files a review must cover: everything minus pure data/binary and gate-exempt meta.

    THE one definition. The shell hook used to carry a second copy of this filter and the two
    disagreed three ways (PIPE-1); the hook is now a shim that calls in here."""
    return reviewable_from(changed_files(ranges))


def reviewable_from(paths):
    """THE exemption decision, as a pure function of a path list.

    Split out of `reviewable_changed` on 2026-08-15 so `guards.py` can interrogate the decision
    DIRECTLY instead of inferring it from a checker's exit code. Every other guarded property is
    tested by planting a violation and watching a gate react; this surface has no gate to watch —
    a file that falls out of this set is simply never reviewed, silently. Asking the classifier is
    the only honest control for it."""
    out2 = []
    for f in paths:
        norm = f.replace(chr(92), '/').lower()
        if f.lower().endswith(DATA_EXT):
            continue
        if norm in EXEMPT_PATHS:
            continue
        if norm.startswith(EXEMPT_PREFIXES):
            continue          # operating machinery: `/rely`'s, owed at TAG in the ledger. See above.
        out2.append(f)
    return out2


def signal_verdict(name):
    """Line 1 of a signal — the verdict it was written under.

    Echoed at prepush so "cleared" is never silently read as "clean": a STOP-ORDINARY signal is a
    sanctioned proceed with findings outstanding, and that distinction is the whole reason line 1
    exists rather than the file's mere presence."""
    p = os.path.join(PRIV, name)
    if not os.path.exists(p):
        return None
    first = io.open(p, encoding="utf-8-sig", errors="replace").readline().strip()
    return (first[:150] + "…") if len(first) > 150 else first


# ⚠⚠ `prior_art` WAS REMOVED FROM THIS TUPLE 2026-09-05, AND WHAT STILL BLOCKS IS NAMED HERE
# BECAUSE `R-NOCONV` REQUIRES IT: "the guard asserting what still BLOCKS lands in the same change,
# or the exemption that block paid for is given up with it."
#
# WHAT STILL BLOCKS: `check_prior_art_attribution` (this file), which enforces the SAME obligation
# PER FILE over the touched set and is a BLOCK leg of the prepush plan. It is strictly stronger for
# the files a push actually carries, and it is satisfiable incrementally — "you owe the files you
# TOUCHED, never the corpus". Verified by RUNNING rather than asserted: with a touched `.lean` file
# lacking a passing verdict it reports `N of M ... have NO passing prior_art verdict` and fails.
#
# WHY THE LEG WENT: `check_signals` asks whether the STEP is current, and the step's registry scope
# is every `.lean` file. Measured 2026-09-05 on the ZP-I push — `coverage_gap(step='prior_art')`:
# `applies_to 220 / have 11 / missing 209`, while the push TOUCHED SIX and covered six of six. The
# leg therefore blocked on 209 files the push never opened, in every state, so it discriminated
# nothing. Tim, the same day: "the entire premise here is iterative fixing... we didn't touch 220
# files. that right there is the false premise."
#
# ⚠⚠ THIS PARAGRAPH CLAIMED `prior_art` WAS ABSENT FROM BOTH PUSH ADMISSION SETS. BOTH HALVES ARE
# NOW FALSE, and the first one gates a push. Re-derived 2026-09-26 by calling `gitRobot admission`
# for all three actions rather than relaying any of them: commit -> `registered_not_admitted`,
# push -> **ADMITTED**, tag -> `registered_not_admitted`. So `prior_art` DOES gate a push at the
# ledger, which is the single action this sentence was about. No set sizes are written here: the
# push figure once recorded on this line went stale inside the range a `/rely` round was reviewing
# (`RLY56-1`). The `count` field of `gitRobot admission(action=...)` is the only number to quote.
# ⚠ ADMISSION IS PER ACTION, and a sentence naming no action is wrong about at least one of them.
# `required.v2.json` records this exact correction at `prior_art._admission_is_action_scoped_2026_09_22`
# — so this is that fix failing to travel to its second site, which is `DC-53`, not a new defect.
# ⛔ THE QUOTATION IS RETIRED TOO: "deliberately ABSENT from admission... blocks nothing at the
# ledger" was DELETED from the registry on 2026-09-22 when that key was renamed and its central
# claim reversed. Do not re-quote it — read the live entry.
# ⭐ WHAT SURVIVES, AND IT IS WHY REMOVING THE LEG STILL STANDS: the argument never rested on
# admission. The leg went because it asked a STEP-level question whose scope was every `.lean` file
# while the push touched six, so it discriminated nothing in any state. That is untouched by who
# admits what, which is precisely why the false sentence sat here unnoticed — it was decoration on
# a sound conclusion.
# ⚠ The second half was wrong differently: this repo's `tools/verify/admission.v1.json` was not
# merely dead, it should never have been named beside the live one. DELETED 2026-09-26. There is
# one admission set and it is gitRobot's.
#
# ⚠ THE RELEASE GATE KEEPS IT ON PURPOSE. `check_release_ready.py`'s own `REVIEW_STEPS` still lists
# `prior_art`, and that is correct rather than an oversight: a release mints a permanent DOI, so
# corpus-wide is the right question THERE and the wrong one for an incremental push. Do not
# "harmonise" the two lists — they price different acts.
#
# ⭐ THIS IS THE INTERIM, NOT THE REPAIR. The repair is CHANGE-SCOPING the step so its denominator
# is the touched set, which belongs in the ledger (dynamic scope) and not here. The criterion that
# makes that legitimate rather than gaming, and it is checkable: CAN THE SCOPE BE DERIVED WITHOUT
# LOOKING AT THE COVERAGE? A touched-set scope falls out of the diff before any verdict is read;
# a scope chosen so `applies_to` lands on `have` is picked to fit the numerator. The first is
# routing, the second manufactures green by shrinking the denominator.
REVIEW_STEPS = ("editorial", "adversary")

# ⚠⚠ THE REVIEW-SIGNAL LEGS MUST REPORT TOO — `B4`. They gate the push exactly as the four inline
# legs do, and before this they rode the same annihilable accumulator. DERIVED FROM `REVIEW_STEPS`,
# NEVER MIRRORED: writing the names out again would be a second list to drift, and this file has
# already removed one step from that tuple (`prior_art`, above). Deriving means a removal cannot
# leave `_EXPECTED` demanding a leg that no longer runs, and an addition cannot ride in unexpected.
_EXPECTED += tuple("signal:%s" % s for s in REVIEW_STEPS)

# ⚠⚠ THE FAIL-ONLY TEST SEAM (`R2-B1`). The hook runs `batch.py prepush --ranges …` as a SEPARATE
# PROCESS and blocks on its return code, so the only control that sees a SystemExit swallowed in
# `__main__`, or a `die` that exits 0, is one that runs that same command as a subprocess and reads
# `returncode`. It needs a push that is GUARANTEED to fail whatever the tree holds, which is this:
# `ZP_PREPUSH_FORCE_FAIL=<leg>` forces exactly that one leg to FAIL, through the normal
# `display_fail` + `verdict_record` path.
# ⛔ WHY THIS IS NOT A BYPASS: it can only ADD a failure. It assigns `ok = False` at the one leg it
# names, never True, skips nothing and touches no other leg's result; an unknown name REFUSES
# (exit 1) rather than being ignored, so a typo cannot read as "seam inert". The worst any value of
# this variable can do is block a push that would otherwise have passed.
FORCE_FAIL_ENV = "ZP_PREPUSH_FORCE_FAIL"


def forced_fail_leg(environ=None):
    """The `_EXPECTED` leg `FORCE_FAIL_ENV` names, or None when unset or empty. An unknown name dies."""
    env = os.environ if environ is None else environ
    raw = (env.get(FORCE_FAIL_ENV) or "").strip()
    if not raw:
        return None
    if raw not in _EXPECTED:
        die("%s=%r names no prepush leg. Accepted: %s. Refusing rather than ignoring it — a seam that "
            "silently does nothing would read as a control that ran." % (FORCE_FAIL_ENV, raw,
                                                                        ", ".join(_EXPECTED)))
    return raw

# ⭐ THE REPORT STATES TWO LISTS, AND THEY ANSWER DIFFERENT QUESTIONS.
# (a) ENFORCED HERE — the review steps this hook itself BLOCKS on, whatever any admission set says:
#     `REVIEW_STEPS` (the signals leg) and `ATTRIB_STEP` (the prior-art attrib leg). Derived from
#     those two names, never written out again. `REVIEW_STEPS` stays a literal, guarded by
#     `guards.py`'s independently-written `_need` (`R-NOCONV`: the guard asserting what still BLOCKS).
# (b) ADMITTED — gitRobot's push admission set, handed to the hook as the env var below, intersected
#     with the registry's `family: review` types, so a review step admitted at push (`copy_editor`)
#     is reported without anyone editing a list. ⛔ TRUST FOOTING: anyone can set an env var, so (b)
#     REPORTS and never BLOCKS, and no BLOCK leg may read it (a selftest row holds that); the ledger
#     (gitRobot's push inventory) is the enforcement. An admission set is NOT a statement of what
#     this hook requires: treating it as one dropped (a) from the page in the SET and EMPTY states.
# ⚠ NOT `GITROBOT_ADMISSION` — that name is the admission FILE PATH override, something else entirely.
ADMITTED_ENV = "GITROBOT_ADMITTED"
ENFORCED_REVIEW_LEGS = (tuple((s, "signals") for s in REVIEW_STEPS)
                        + ((ATTRIB_STEP, "prior-art attrib"),))


def registry_review_family(path=None):
    """Sorted tuple of registry types with `family: review`, or None if the registry is unreadable.

    None, never (): an unreadable registry and a registry with no review types are different answers,
    and only the first may fall back (`R-ZERONULL`). A registry of the wrong SHAPE (top level or
    `types` not an object) is unreadable for this purpose, and returns None rather than raising."""
    try:
        with io.open(path or os.path.join(BASE, "required.v2.json"), encoding="utf-8") as fh:
            doc = json.load(fh)
        types = doc.get("types") if isinstance(doc, dict) else None
        if not isinstance(types, dict):
            return None
        return tuple(sorted(k for k, v in types.items()
                            if isinstance(v, dict) and v.get("family") == "review"))
    except (OSError, ValueError, RecursionError):
        return None


def admitted_review_steps(raw=False, family=False):
    """Classify the admission set handed to this hook. Returns `(state, steps, detail)`.

    `raw` is the env var's text (False = read the environment; None = ABSENT). `family` is the registry
    review family (False = read the registry). The three states carry DIFFERENT VALUES (`R-ZERONULL`):
      SET      steps = sorted tuple of admitted review steps — () when steps were admitted but none
               is a review step; `detail` = how many steps were admitted in all
      EMPTY    steps = () — the admission set was read and admits nothing at all
      UNKNOWN  steps = None — never (): absent (a human `git push`), unparseable, malformed, for a
               different action, or no readable registry to derive against
    """
    try:
        if raw is False:
            raw = os.environ.get(ADMITTED_ENV)
        if family is False:
            family = registry_review_family()
        return _classify_admission(raw, family)
    except Exception as e:
        # ⚠ F3: a crafted value (32k nested brackets measured a RecursionError out of `json.loads`)
        # must land in UNKNOWN, never raise into `cmd_prepush`. RecursionError is an Exception.
        return ("UNKNOWN", None, "%s could not be classified (%s)" % (ADMITTED_ENV, type(e).__name__))


def _classify_admission(raw, family):
    """`admitted_review_steps`' body, behind its catch-all. Same contract, same three states."""
    if raw is None:
        return ("UNKNOWN", None, "%s is not set — a push not launched by gitRobot (e.g. a human "
                                 "`git push`)" % ADMITTED_ENV)
    try:
        doc = json.loads(raw)
    except (ValueError, RecursionError):
        return ("UNKNOWN", None, "%s is not parseable JSON" % ADMITTED_ENV)
    if not isinstance(doc, dict):
        return ("UNKNOWN", None, "%s is JSON but not an object" % ADMITTED_ENV)
    state, action, admitted = doc.get("state"), doc.get("action"), doc.get("admitted")
    if state == "UNKNOWN":
        return ("UNKNOWN", None, "gitRobot could not read the admission set: %s"
                % (doc.get("why") or "no reason given"))
    if action != "push":
        return ("UNKNOWN", None, "%s describes action %r, not push" % (ADMITTED_ENV, action))
    if (state not in ("SET", "EMPTY") or not isinstance(admitted, list)
            or not all(isinstance(s, str) for s in admitted)
            or (state == "SET") != bool(admitted)):
        return ("UNKNOWN", None, "%s is malformed (state %r with %r)" % (ADMITTED_ENV, state, admitted))
    if family is None:
        return ("UNKNOWN", None, "the registry's review family could not be read, so nothing can be "
                                 "derived from the admission set")
    if state == "EMPTY":
        return ("EMPTY", (), "the admission set was read and admits no step at all")
    steps = tuple(sorted(set(admitted) & set(family)))
    return ("SET", steps, "%d step(s) admitted at push" % len(admitted))


def review_report_lines(adm):
    """Render the review report: what this hook ENFORCES, then what gitRobot ADMITTED. Pure.

    The enforced list prints in EVERY state, because the BLOCK legs apply whatever the admission set
    says; an EMPTY or SET-without-reviews admission set is gitRobot's statement, never a waiver here.
    ⚠ UNKNOWN NEVER RENDERS AS A COUNT. It names itself UNKNOWN and points at the enforced list as
    the FALLBACK — those steps are owed wherever their legs' triggers apply."""
    state, steps, detail = adm
    legs = {}
    for s, leg in ENFORCED_REVIEW_LEGS:
        legs.setdefault(s, []).append(leg)
    out = ["  enforced here: %s — BLOCK legs of this hook, each on its own trigger, whatever the "
           "admission set says"
           % "; ".join("%s (%s)" % (s, " + ".join(l)) for s, l in legs.items())]
    if state == "UNKNOWN":
        out.append("  admitted review set: UNKNOWN — %s. gitRobot's review set could not be read; "
                   "this is NOT \"none required\"." % detail)
        out.append("      FALLBACK (owed wherever their legs apply: the enforced list above): %s"
                   % ", ".join(legs))
        return out
    if state == "EMPTY":
        out.append("  admitted review set: EMPTY — %s, so gitRobot's set names no review step. This "
                   "does NOT lift the enforced list above." % detail)
        return out
    if not steps:
        out.append("  admitted review set: SET — %s, NONE of them in the registry's review family. "
                   "This does NOT lift the enforced list above." % detail)
        return out
    out.append("  admitted review set: SET — %s ∩ registry family:review — %d review step(s) (%s)"
               % (ADMITTED_ENV, len(steps), detail))
    for s in steps:
        out.append("      %-14s %s" % (s, "admitted at push; ALSO enforced here by the %s BLOCK leg"
                                       % " + ".join(legs[s]) if s in legs else
                                       "admitted at push; ENFORCED BY THE LEDGER (gitRobot push "
                                       "inventory) — this hook reports it and carries no BLOCK leg "
                                       "for it"))
    return out


def signal_need(name, fires):
    """Whether the signals leg REQUIRES step `name` this push. A function so a control can run it
    under a forged admission set and show the answer does not move: it must never read `ADMITTED_ENV`."""
    return (name != "prior_art") or fires


def review_report():
    """The report as `cmd_prepush` prints it. Never raises: the report must not take the hook down."""
    try:
        return review_report_lines(admitted_review_steps())
    except Exception as e:
        try:
            return review_report_lines(("UNKNOWN", None, "the review report itself errored (%s)"
                                        % type(e).__name__))
        except Exception:
            return ["  admitted review set: UNKNOWN — the review report errored; this is NOT "
                    "\"none required\"."]


def _numstat(ranges=None):
    """`{path: (added, deleted)}` over the pushed ranges, or the working tree when none.

    Mirrors `changed_files`' scope decision exactly — `is not None`, never truthiness, so an EMPTY
    range list stays an empty push scope rather than falling back to the tree.

    ⚠ Binary files report `-\t-` in numstat and are skipped: a PDF has no line count and pretending
    it does would put nonsense in the arithmetic below."""
    acc = {}
    for r in (list(ranges) if ranges is not None else [None]):
        rc, o, _err = (sh_split("git", "diff", "--numstat", r) if r
                       else sh_split("git", "diff", "--numstat", "HEAD"))
        if rc != 0:
            die("git could not resolve range %r — refusing to guess a scope:\n%s" % (r, _err or o))
        for line in o.splitlines():
            bits = line.split("\t")
            if len(bits) != 3 or bits[0] == "-" or bits[1] == "-":
                continue
            f = bits[2].strip().replace("\\", "/")
            pa, pd = acc.get(f, (0, 0))
            acc[f] = (pa + int(bits[0]), pd + int(bits[1]))
    return acc


def prose_shrank_unpaired(ranges=None, floor=8):
    """`.lean` files that NET-LOST >= `floor` lines with no sibling `.md` gaining any, in scope.

    ⚠⚠ THE BLIND SPOT. `check_prose` counts LINES, so DELETING an oversized block and MIGRATING it
    to a ride-along score identically — and `.lean` plus `ZeroParadox/*.md` sit outside both prose
    gates' declared scope while `/rely` does not gate. Nothing mechanical distinguished "I moved
    this" from "I destroyed this".

    Measured 2026-08-26 over 32 days and ~240 commits: the practice is sound — every large removal
    carries a per-item justification in its commit message, and three distinct verification patterns
    are in use (verify duplication per declaration; move onto the declaration; the strip test per
    item). TWO instances escaped. `170bdaf` records one caught by the gates and restored in the same
    commit: *"That was mathematics, not narrative — it passed the strip test and was cut anyway."*
    The other was `DEL-1`, caught by a human reading narration, which is not a control.

    ⚠⚠ ADVISORY, AND IT MUST STAY SO. A deletion is legitimate whenever the content was a verified
    duplicate, and no mechanical test can tell that from a loss — the honest check is a human
    reading each declaration's docstring. Blocking would fire on every honest dedup in this repo's
    own history and earn itself a bypass. What this CAN do is refuse to let a large unpaired shrink
    pass UNNOTICED, which is the only part that failed.

    ⚠ NET, not gross: a rewrite that adds 40 and removes 45 is not a migration candidate. And a
    sibling that merely CHANGED is not enough — it must have GAINED lines, because a `.md` edited in
    the same commit says nothing about whether the `.lean`'s content arrived there.

    ⚠⚠ **IT WOULD NOT HAVE CAUGHT `DEL-1`, AND SAYING SO IS THE POINT.** Measured on the real
    ranges: `b9884e6` -> 2 hits (SnapDichotomy -23, BranchingSnapChain -16, both genuinely
    unpaired), `e9be5f6` -> 0 (the -25 SHORTFALL case, correctly silent because the `.md` gained
    69 — a shortfall is not an unpaired deletion), and `2a304b3`, which IS `DEL-1`'s commit, -> 0.
    The deletion and the ride-along that repaired it landed in the same commit, so by commit time
    the pair was whole. **This detects the shape at COMMIT and PUSH scope, never mid-edit**, and
    the mid-edit window is exactly where `DEL-1` lived. Do not read a clean row as "nothing was
    destroyed this session"; read it as "nothing left this scope unpaired.\""""
    stat = _numstat(ranges)
    out = []
    for f, (added, deleted) in stat.items():
        if not f.endswith(".lean") or (deleted - added) < floor:
            continue
        if stat.get(f[:-5] + ".md", (0, 0))[0] > 0:
            continue
        out.append((f, deleted - added))
    return sorted(out, key=lambda t: -t[1])


def check_signals(ranges=None):
    """Ask the LEDGER whether each review step is recorded and current. Returns (step, ok, why).

    ⛔ THE PROSE SIGNAL FILES ARE RETIRED (`tools/process/review-gates.md`). This used to read
    `er/ar/pa_cleared.txt` and re-hash every file they named. Those files could be written by any
    process, recorded NO AUTHOR, and held one verdict for N passes — measured 2026-08-24, three
    concurrent passes of one prose gate raced on a single path and the survivor was decided by
    scheduling, leaving an unattributed verdict on disk that `prepush` then echoed as cleared.

    ⚠⚠ ONE QUESTION, SERVER-SIDE. `record.stale_or_missing` is the only staleness predicate;
    re-deriving freshness here would be the mirror defect at exactly the point the split exists to
    protect — two implementations of "is this verdict still good", disagreeing silently. This
    reports; it never decides what GATES. gitRobot owns admission.

    ⚠ UNREACHABLE LEDGER FAILS **CLOSED**. `stale_or_missing` returns None when it cannot ask, and
    None is not an empty set: "no steps need re-running" and "I could not find out" render
    identically otherwise, which is the absence-as-success shape this whole layer exists to remove.
    """
    changed = set(reviewable_changed(ranges))
    if not changed:
        # Unchanged rule, and it was a measured hook divergence (PIPE-1): nothing reviewable in
        # scope means no review is owed at all.
        return [(s, True, "no reviewable change in scope — review not required")
                for s in REVIEW_STEPS]
    # ⚠⚠ POSITIVE STATUS, NEVER "ABSENT FROM THE RE-RUN SET". This asked `stale_or_missing` and took
    # `s not in need` as a pass — a PROXY, and it failed open in three ways at once: `SATISFIED`,
    # `NOT_APPLICABLE` and *a step the registry has never heard of* all sit outside that set, so a
    # typo in `REVIEW_STEPS` became a permanent green with an affirmative message. Measured
    # 2026-08-24: `prior_art` is `NOT_APPLICABLE` with `record_id: null` and printed `ok REQUIRED`
    # on a trigger-5 push. Ask what a PASS PROVES, then build the state where the proxy holds and
    # the property does not — DC-18.
    # ⚠⚠ RLY36-2. THIS ASKED ABOUT THE LITERAL REF `HEAD`, WHATEVER WAS BEING PUSHED. The changed
    # -file half above already honours `ranges` (REL-1); the FRESHNESS half did not, so the two
    # halves of one answer described different content. Measured by /rely round 6 with a spy on
    # `record.step_status`: `check_signals(["origin/main..HEAD~9"])` reported `reviewable=122` from
    # the range and then asked the ledger about `('HEAD','push')` — nine commits past what the push
    # publishes. And the answers genuinely differ by ref: `editorial` was FAIL at HEAD and STALE at
    # `HEAD~1..HEAD~18`, so this was not a distinction without a difference.
    #
    # ⚠ ASK AT EVERY TIP, AND TAKE THE WORST. A push may carry several refs; a step is current for
    # this push only if it is current for ALL the content the push publishes. Taking the first, or
    # `any`, would rebuild the same fail-open one level up.
    #
    # ⚠ THIS IS STILL TIP-ONLY, AND SAYING SO IS THE POINT. `can_push` is what judges EVERY commit
    # in a range; this reports on the content each range ends at. That is a strictly smaller claim
    # than "the range is clean", and it is the claim this function is entitled to make — SCOPE-1
    # is closed at the gitRobot/`can_push` layer, not here.
    refs = _range_tips(ranges) if ranges is not None else ["HEAD"]
    status, asked_at = None, None
    for ref in refs:
        st = record.step_status(ref, "push")
        if st is None:
            return [(s, False, "UNDECIDED — the ledger could not be asked at %r, so freshness is "
                               "UNKNOWN. This is a recording-path failure, not a finding about the "
                               "corpus; it fails CLOSED on purpose." % ref) for s in REVIEW_STEPS]
        if status is None:
            status, asked_at = dict(st), ref
            continue
        for k, v in st.items():
            # Worst-wins: anything that is not SATISFIED at THIS tip governs, and a step absent
            # from either answer stays absent (an unknown step is a failure downstream).
            if status.get(k) == "SATISFIED" and v != "SATISFIED":
                status[k], asked_at = v, ref
    out = []
    for s in REVIEW_STEPS:
        st = status.get(s)
        if st is None:
            # ⚠ AN UNKNOWN STEP IS A FAILURE, NOT A PASS. The ledger returns a row for every
            # REGISTERED step, so a missing key means this name is not registered — a caller
            # asking about a gate that does not exist has established nothing whatsoever.
            out.append((s, False, "NOT REGISTERED in the ledger — this step name buys no coverage. "
                                  "Fix the name or register the type; do not read it as a pass."))
        elif st == "SATISFIED":
            out.append((s, True, "SATISFIED — recorded and current in the ledger"))
        elif st == "NOT_APPLICABLE":
            # Legitimate, and it must SAY SO rather than borrow the word "recorded": nothing was
            # examined, and the reason is the ledger's to state.
            out.append((s, True, "NOT_APPLICABLE — the ledger declares this step does not gate "
                                 "here. Nothing was examined; this is not a clean bill."))
        # ⚠ NORMALISED HERE ONLY (`RLY54-2`): `REFUSED` with stray case or whitespace fell to the
        #   generic `else` and printed the one remedy this branch exists to withhold. Both paths
        #   BLOCK, so this moves only the MESSAGE. The SATISFIED test above stays exact on purpose:
        #   normalising a PASS token is the fail-open direction.
        elif isinstance(st, str) and st.strip().upper() == "REFUSED":
            # ⛔⛔ REFUSED IS NOT FAIL, AND THE REMEDY IS THE WHOLE POINT OF THIS BRANCH. It already
            # BLOCKED without it — the generic `else` fails closed — but it printed "run the gate and
            # let it record its own verdict", which is the one instruction that cannot work: the gate
            # DID run, the ledger declined its record, and re-running reproduces the same refusal.
            # A control measured that verbatim before this branch existed. `RLY41-2`'s shape: a true
            # blocking answer wearing a remedy for a different failure.
            #
            # ⚠⚠ AND IT CONDEMNS NOTHING. A FAIL indicts subjects; a REFUSED establishes NOTHING —
            # the ledger never accepted a claim about those bytes, so there is no finding about the
            # corpus here and a reader must not go looking for one. Treating it as a FAIL would stamp
            # condemnation on blobs nothing judged, which is `LED-10` arriving through a new door.
            # ⚠ It blocks for the ONLY honest reason: absence of an established verdict.
            out.append((s, False,
                        "REFUSED — the ledger declined this step's record; NOTHING has been "
                        "established about these subjects. This is a defect in the RECORD, not a "
                        "finding about the corpus: do not read it as a failure of the mathematics, "
                        "and do not simply re-run the gate — it will be refused again. Read the "
                        "rule the ledger named and fix the emitter, then record."))
        else:
            out.append((s, False, "%s — run the gate and let it record its own verdict "
                                  "(`record.py --step %s`)" % (st, s)))
    return out


# ---------------------------------------------------------------- commands

def cmd_start(bucket):
    rc, head = sh("git", "rev-parse", "--short", "HEAD")
    rc2, work = sh(sys.executable, os.path.join(BASE, "debaseline.py"), "--bucket", bucket)
    sites = [l for l in work.splitlines() if l.strip() and not l.startswith(("GRAND", "site("))]
    state = {"bucket": bucket, "head": head.strip(), "checker_hashes": checker_hashes(),
             "worklist_size": max(0, len(sites) - 1), "stages": {"start": {"ok": True}},
             # Snapshot the baseline so `close` can assert the result is a STRICT SUBSET. Without
             # this, "pruned" and "regenerated" are indistinguishable at close time.
             "baseline_at_start": sorted(baseline_entries(bucket) or [])}
    save(state)
    print("batch '%s' started at %s" % (bucket, state["head"]))
    print("  worklist: %d site(s)" % state["worklist_size"])
    print("  filters frozen at: %s" % json.dumps(state["checker_hashes"]))
    print("\nNext: run the probes, then `batch.py stage probe --note '<what you built>'`")


def cmd_stage(stage, note):
    state = load()
    require(state, stage)
    if not note:
        die("stage '%s' needs --note describing what was actually done" % stage)
    state["stages"][stage] = {"ok": True, "note": note}
    save(state)
    print("stage '%s' recorded: %s" % (stage, note))


def cmd_decls(regen, block, prune=False):
    """Report — or re-seed — the on-disk declaration baseline.

    `--baseline` seeds it from the tree as it stands, so behaviour is unchanged at the moment of
    seeding and only genuinely NEW declarations are ever reported afterwards."""
    on_disk = decls_on_disk()
    if regen:
        write_decl_baseline(on_disk)
        print("declaration baseline written: %d name(s) from %d file(s) on disk"
              % (len(on_disk), len(lean_files_on_disk())))
        return
    if prune:
        orphans, _gone = orphan_baseline_keys()
        if orphans is None:
            print("NO BASELINE — nothing to prune.")
            return
        base = load_decl_baseline() - set(orphans)
        write_decl_baseline(base)
        print("pruned %d orphan key(s); baseline now %d" % (len(orphans), len(base)))
        for k in orphans[:10]:
            print("   removed  %s" % k)
        return

    decls = added_decls()
    if decls is None:
        print("NO BASELINE at %s — run `batch.py decls --baseline`" % DECL_BASELINE)
        sys.exit(1 if block else 0)
    p_ok, p_msg = check_purity(decls)
    s_ok, s_msg = check_ssot(decls)
    orphans, gone = orphan_baseline_keys()
    if orphans:
        print("STALE BASELINE: %d key(s) with no declaration on disk"
              " (%d from files that no longer exist)." % (len(orphans), len(gone)))
        print("  Each is a slot a future declaration can be born into already"
              " grandfathered. Prune with: batch.py decls --prune")
    print("declarations on disk : %d" % len(on_disk))
    print("not in the baseline  : %d  %s" % (len(decls), ", ".join(decls[:8])))
    print("  purity  %-4s %s" % ("ok" if p_ok else "FAIL", p_msg))
    print("  ssot    %-4s %s" % ("ok" if s_ok else "FAIL", s_msg))

    # ⚠ THE SUBJECT SET IS THE WHOLE `.lean` CORPUS PLUS `ssot.json`, NOT THE FILES THAT CHANGED.
    # The obligation is discharged by a `#print axioms` line ANYWHERE in the tree and by a row in a
    # single shared `ssot.json`, so the verdict depends on every file that could carry either.
    # Naming only the added declarations' files would leave the record SATISFIED after a purity line
    # was deleted somewhere else — a verdict recorded against the wrong file set, which claims a
    # property still holds when its inputs moved.
    # ⚠ `decl_baseline.txt` is the SWITCH: it decides what counts as "added", so editing it changes
    # this verdict without touching a single subject. Same argument as the accepted-defect baselines.
    _rels = sorted({os.path.relpath(fp, REPO).replace("\\", "/") for fp in lean_files_on_disk()})
    if os.path.exists(os.path.join(REPO, "ssot.json")):
        _rels.append("ssot.json")
    _bad = {d.split("::")[0] for d in (missing_purity_keys(decls) + missing_ssot_keys(decls))}
    _rc = common.record_if_asked(
        "decls", _rels, _bad,
        "a declaration is missing its #print axioms entry or its ssot.json row",
        switches=["tools/verify/decl_baseline.txt"])
    if _rc:
        sys.exit(_rc)
    sys.exit(0 if (p_ok and s_ok) or not block else 1)


def record_pdf_coupling():
    """Record `pdf_coupling` over EVERY tracked PDF, not merely the changed ones.

    ⚠⚠ THIS TYPE HAD NO PRODUCER AT ALL. `check_pdf_coupling` computes a verdict and PRINTS it;
    nothing anywhere emitted a record, so the key was MISSING and unsatisfiable by construction —
    the same shape as the routing gate's `<ABSENT>` floor. It was invisible until 2026-08-25
    because the `when` glob was `**/*.pdf`, which under fnmatch requires at least one `/` and
    therefore matched NONE of the 40 root-level PDFs. The row read `NOT_APPLICABLE — no path
    matched`, which is a true sentence and a benign-looking one. **Fixing the dead pattern is what
    exposed the missing producer**; two defects stacked, the outer one masking the inner.

    ⚠ FULL SCOPE, NOT THE PUSH DIFF, AND THAT IS THE HONEST CHOICE. `check_pdf_coupling` asks its
    question of the PDFs in a push, because that is what it gates. The REGISTRY scopes this type to
    every `*.pdf` (40 of them), and a record covering only the changed few would leave the rest
    permanently unexamined while the key read SATISFIED. The pairing property — does some
    `scripts/build_*.py` name this file literally — is cheap to evaluate for all of them, so the
    record says exactly what was checked and checks everything it claims.

    ⚠ The pairing test is the anchored one from `check_pdf_coupling`, deliberately reused rather
    than re-derived: an unanchored `base in src` certified 40 bytes of junk named `Companion.pdf`
    as paired, because every companion script contains that substring. A filename is a token."""
    rc, out, _err = sh_split("git", "ls-files", "--", "*.pdf")
    if rc != 0:
        return None
    pdfs = [p.strip().replace("\\", "/") for p in out.splitlines() if p.strip()]
    if not pdfs:
        return None
    sdir = os.path.join(REPO, "scripts")
    srcs = []
    for name in sorted(os.listdir(sdir)) if os.path.isdir(sdir) else []:
        if not (name.startswith("build_") and name.endswith(".py")):
            continue
        try:
            srcs.append(io.open(os.path.join(sdir, name), encoding="utf-8",
                                errors="replace").read())
        except OSError:
            continue
    unpaired = []
    for pdf in pdfs:
        base = os.path.basename(pdf)
        pat = r"(?<![\w.\-])" + re.escape(base) + r"(?![\w.])"
        if not any(re.search(pat, src) for src in srcs):
            unpaired.append(pdf)
    # ⚠ `argv=["--record"]` IS EXPLICIT BECAUSE THIS CALL SITE **IS** THE RECORDER. `record_if_asked`
    # gates on `--record` appearing in `sys.argv`, which is right for a checker invoked as its own
    # process by the hook — and wrong here, where the call is IN-PROCESS from `cmd_precommit` and
    # the real argv is `['batch.py', 'precommit']`. Left implicit, this returned 0 and recorded
    # NOTHING while precommit printed PASS: a producer that silently does not produce, which is the
    # exact defect this function was written to close, reintroduced one layer up.
    return common.record_if_asked(
        "pdf_coupling", pdfs, unpaired,
        "a committed PDF has no scripts/build_*.py naming it literally — a DOI freezes the PDF "
        "permanently and the build script is the only reviewable surface it has",
        argv=["--record"], module="tools/verify/batch.py")


def cmd_precommit():
    """The mechanical gate before ANY commit — batch or not.

    ⚠ It used to require a batch, which made it unusable as a default: a one-line fix would have
    needed `batch start` first, and a gate that is annoying to run does not get run. The
    UNIVERSAL obligations (build green, a purity entry and an SSOT row for every added declaration,
    the suite at zero) apply to every commit; only stage ordering and filter-freezing are
    batch-specific. Without a batch it runs the universal half and says so."""
    state = load()
    # ⚠⚠ RECORD AGAINST THE INDEX, NOT HEAD, AND THE REASON IS EASY TO GET WRONG. At pre-commit time
    # HEAD is the PARENT — the commit being made does not exist yet — so a record keyed to HEAD would
    # cover the content being replaced. The STAGED blobs are the new commit's blobs, and coverage is
    # content-addressed, so recording the index covers a commit that has not happened. That is what
    # makes `can_push` satisfiable across a RANGE rather than only at its tip: every commit earns its
    # keys as it is made, instead of one sweep at the end that leaves the intermediates NOT_RUN.
    os.environ.setdefault("ZPLEDGER_BASIS", "INDEX")
    os.environ.setdefault("ZPLEDGER_RUN", "precommit-%s" % (state.get("bucket") if state
                                                            else "universal"))
    # ⚠ BASIS-EMPTY-1: resolve the index tree ONCE, before any checker runs, so every one records
    # the same basis and none contends for `.git/index.lock` (see `common.pin_index_tree`).
    _pin = ("not pinned — basis is %s, not INDEX" % os.environ["ZPLEDGER_BASIS"])
    if os.environ["ZPLEDGER_BASIS"] == common.INDEX:
        _tree, _why = common.pin_index_tree()
        _pin = (("index tree %s, pinned for every checker" % _tree) if _tree else
                ("NOT PINNED — %s; each checker resolves its own and exits 2 if it cannot" % _why))
    report.banner("precommit pipeline", [
        ("entry", "batch.py precommit (manual; the pre-commit HOOK runs the checkers)"),
        ("records", "verdicts recorded to verdictLedger against the STAGED content (not HEAD)"),
        ("batch", ("bucket '%s'" % state.get("bucket", "?")) if state
                  else "none — universal obligations only, stage ordering skipped"),
        ("scope", "the WORKING TREE as it stands"),
        ("basis", "declarations diffed against decl_baseline.txt on disk, never against git"),
        ("ledger basis", _pin),
        ("exempt", "vendored: %s" % (", ".join(sorted(vendored.allowlist())) or "(allowlist empty)")
                   + " + anything under Vendored/"),
    ])
    report.plan(
        ([("filters frozen", "BLOCK", "no checker changed since batch start")] if state else []) +
        [("build", "BLOCK", "lake build green and no `sorry`"),
         ("purity", "BLOCK", "every new declaration has a #print axioms entry"),
         ("ssot", "BLOCK", "every new declaration has an ssot.json row"),
         ("suite", "BLOCK", "the %d gating checkers at zero new (check_poles is a counter)"
                   % len(GATING_CHECKERS))])
    if state is None:
        print("no batch in progress — running the UNIVERSAL checks only")
    else:
        require(state, "precommit")
    decls = added_decls()
    print("declarations on disk not in the baseline: %s"
          % ("NO BASELINE — failing closed" if decls is None else (", ".join(decls) or "(none)")))
    # Filter-freezing is the only BATCH-specific check here; the rest are universal obligations
    # that apply to every commit.
    checks = ([("filters frozen",) + check_filters_frozen(state)] if state else []) + [
              ("build",) + check_build(),
              ("purity",) + check_purity(decls),
              ("ssot",) + check_ssot(decls),
              ("suite",) + check_suite()]
    bad = 0
    for name, ok, msg in checks:
        print("  %-16s %-4s %s" % (name, "ok" if ok else "FAIL", msg))
        bad += 0 if ok else 1
    if bad:
        die("%d precommit check(s) failed" % bad)
    if state:
        state["stages"]["precommit"] = {"ok": True, "tool": self_hash()}
        save(state)
    # ⚠ RECORDED HERE BECAUSE THE LEDGER'S OWN REMEDY LINE SAYS SO: the MISSING row prints
    # "INSTEAD: python tools/verify/batch.py precommit". A remedy that does not discharge the
    # thing it names is `LED-2` — an operator following the instruction and watching nothing
    # change learns to distrust the whole layer.
    _rcp = record_pdf_coupling()
    if _rcp:
        sys.exit(_rcp)
    run_field_discipline()
    print("\nprecommit PASS — safe to commit")


def run_field_discipline():
    """ADVISORY: nominate prose that claims a typeclass FIELD is proved which the Lean SUPPLIES.

    ⚠ NEVER GATES, AND THAT IS DELIBERATE. Its judgement half — the proved/supplied split — is
    computed from the Lean and cannot be wrong; its ENUMERATION half is a text scan over prose
    blocks and can be. `CLAUDE.md` rung 5: the screen may replace the enumeration, it may NEVER
    replace the verdict. So this prints a reading list and returns nothing to `bad`.

    ⚠ IT EXISTS BECAUSE FOUR CONSECUTIVE HAND SWEEPS MISSED THE SAME CLAIM FAMILY, each time by
    widening a pattern. `R-RECUR`: 4th occurrence builds the checker. The surface that escaped all
    four contains no numeral, which is why the property it tests is a fact about the Lean rather
    than a shape of the sentence."""
    p = os.path.join(BASE, "check_fields.py")
    if not os.path.exists(p):
        return
    rc, out = sh(sys.executable, p, "--record")
    tail = [l for l in out.splitlines() if "NEW sites" in l or "blocks claiming" in l]
    for l in tail:
        print(" %s" % l.rstrip())
    if rc == 2:
        print("  field discipline    WARN  ran, but its verdict was NOT RECORDED (exit 2)")


# ⚠⚠ THE REFUSAL IS A FUNCTION SO A CONTROL CAN CALL IT. As the
# literal `if ranges is None and not changed_files(None)` this decision was unreachable by any
# check — and that unreachability is precisely how it stayed WRONG for weeks with every control
# green. `guards.py` now carries a row per case; see `check_prepush_scope_refusal`.
def unjudgeable_scope(ranges, tree=None):
    """`None` when this run may judge the push scope; otherwise ONE LINE saying why it may not.

    ⚠⚠ `None` VERSUS A STRING — THE VALUE CARRIES THE DECISION AND THE STRING ONLY EXPLAINS IT
    (`R-ZERONULL`). Two distinct unjudgeable states share one exit but not one message, because
    naming the set that was actually measured is the half that misled a reader.

    ⛔⛔ `not changed_files(None)` ALONE WAS NEVER RIGHT, AND IT WAS MEASURED DEAD RATHER THAN
    ARGUED DEAD. It fires only on a WHOLLY clean tree, so any dirty path at all disarms it. Since
    `34bd217` (2026-09-03) `gate_round.json` is TRACKED and deliberately kept modified — *static
    initializer tracked, INSTANCE in the working copy* — so during a gate arc past round 0 the
    tree is never clean and this guard never fired. The manual run then judged the range-scoped
    legs against a working tree holding no attributable file at all, and printed `no attributable
    file changed in this push` at a moment the pushed range owed FOUR.

    ⚠ AND THE FIRST DIAGNOSIS NAMED THE WRONG CAUSE, WHICH IS `DC-39`. It blamed `f377e325` for
    making the two halves of the bundle disagree about whether `gate_round.json` is content.
    Measured 2026-09-12: that commit never touched this file — `f377e325^:tools/verify/batch.py`
    and `f377e325:tools/verify/batch.py` are the SAME blob `3f11ba68…` — and `changed_files` is
    session-state-aware in neither version. Executing `f377e325^`'s own `changed_files(None)`
    against the live tree returns `['gate_round.json']`, so the guard was already silent before
    that commit existed. A wrong mechanism on a right symptom terminates the search.

    ⭐ THE PROPERTY: a tree whose only changes are SESSION STATE is indistinguishable from a clean
    one for this purpose, and neither is a scope this command may judge. `common.session_state()`
    is the ONE declaration of that set (`tools/verify/session_state.txt`), so this arm cannot
    drift from what `ledger_subjects` excludes — which is the drift that produced the divergence.

    ⚠ `tree` IS AN INJECTION POINT FOR CONTROLS ONLY. Production callers pass nothing and get the
    real working tree; `guards.py` passes constructed trees so the decision can be exercised
    without a dirty checkout.
    """
    if ranges is not None:
        return None
    tree = changed_files(None) if tree is None else list(tree)
    if not tree:
        return "the working tree is CLEAN"
    if set(tree) <= common.session_state():
        return ("the working tree's only change(s) are SESSION STATE, which carries no reviewable "
                "content: %s" % ", ".join(sorted(tree)))
    return None


def cmd_prepush(ranges=None):
    """The mechanical gate before ANY push — batch or not.

    `ranges` is supplied by the pre-push hook (the refs actually being pushed) and omitted by a
    manual run, which then reads the working tree. Same code either way; see `changed_files`.

    ⚠ It used to `require` a batch, which is the SAME defect `cmd_precommit` had already fixed and
    documents in its own docstring: a gate that refuses to run outside a batch is a gate that does
    not run. Fix-the-site-not-the-class, one function away from the fix.

    `/rely` is NOT a leg here: its obligation is the ledger's, at TAG
    (`coverage_gap(step='rely', action='tag')`), and the manifest says so in its own row.

    Everything below is universal; only the stage record is batch-specific, and it was already
    guarded. There is ONE pipeline, and it must fire in both states rather than grow a second."""
    state = load()
    # ⚠ THE FAIL-ONLY TEST SEAM is validated FIRST, so an unknown leg name refuses before any work.
    _forced = forced_fail_leg()
    if _forced is not None:
        print("TEST SEAM: %s=%s — that leg is FORCED to FAIL (it can only add a failure)"
              % (FORCE_FAIL_ENV, _forced))
    # ⚠ RLY36-3. `hooks.py pre_push` sets ZPLEDGER_RUN and `cmd_precommit` setdefaults it; this
    # function did NEITHER, so a MANUAL `batch.py prepush` ran the whole pipeline and every
    # `--record` in it was refused with V9 (`run.id is required`). Measured cost: ~96s and ~$0.11
    # of model calls on `agent_gate` alone, spent to produce a verdict that could never leave a
    # key. It failed CLOSED — the key stayed MISSING, which is honest — so this is waste, not a
    # fail-open. `setdefault`, never assignment: the hook sets the real id first and must win.
    os.environ.setdefault("ZPLEDGER_RUN", "prepush-manual")
    report.banner("prepush pipeline", [
        ("entry", "batch.py prepush%s" % (" --ranges (called by the pre-push hook)"
                                          if ranges is not None else " (manual)")),
        ("batch", ("bucket '%s'" % state.get("bucket", "?")) if state
                  else "none — universal push checks only"),
        # `is not None`, matching changed_files: an EMPTY range list is a real, empty push scope and
        # must not be described as — or fall back to — the working tree.
        ("scope", (["range %s" % r for r in ranges] or ["(empty push scope: no ranges)"])
                  if ranges is not None
                  else ["the WORKING TREE (manual run; the hook supplies real ranges)"]),
        ("basis", "pushed ranges when given — REL-1: the working tree is empty post-commit"),
    ])
    report.plan([
        ("trigger 5", "report", "a new .lean file or >=50 inserted .lean lines requires prior-art"),
        ("purity", "BLOCK", "every new declaration has a #print axioms entry"),
        ("ssot", "BLOCK", "every new declaration has an ssot.json row"),
        ("pdf coupling", "BLOCK", "a changed PDF arrives with its scripts/ build script"),
        # ⚠ THE OBLIGATION TRIGGER 5 REPORTS, ACTUALLY ENFORCED — and per FILE, not per corpus.
        # Trigger 5 has always been a `report` row: it announces that prior art is owed and blocks
        # nothing, which is why 927 inserted .lean lines shipped 2026-08-31 with the step resolving
        # NOT_APPLICABLE and check_signals rendering that as ok. This row is the enforcement, and it
        # is scoped to the files the push EDITED so it can be satisfied one review at a time.
        ("prior-art attrib", "BLOCK",
         "every ATTRIBUTABLE file edited in this push carries a passing prior_art verdict at its "
         "current bytes — attributable = batch.ATTRIBUTABLE, narrowed by prior_art's registry scope"),
        ("prose migration", "WARN",
         "a .lean prose block that SHRANK with no sibling .md gaining — deleted or migrated?"),
        # ⚠ A `report` row that runs nothing, so a reader looking for the `/rely` leg finds where the
        # obligation lives instead of concluding it is unenforced.
        ("rely", "report",
         "NOT a push leg: owed at TAG in the ledger — coverage_gap(step='rely', action='tag')"),
        # ⚠ THESE ROWS MUST STAY LITERALS: `hooks._batch_rows` reads this list with `ast.literal_eval`
        # and returns None on any expression. So the signals row cannot be derived from
        # `REVIEW_STEPS`; a selftest row holds it to that tuple instead.
        ("signals", "BLOCK", "editorial + adversary fresh and covering"),
        ("review set", "report",
         "names the review steps this hook ENFORCES (signals + prior-art attrib) in every state, then "
         "those admitted at push: GITROBOT_ADMITTED ∩ registry family:review; UNKNOWN when absent "
         "or unreadable — never blocks"),
        ("agent gate", "WARN", "an agent judges whether each check's PASS is EARNED; never blocks"),
    ])
    if state is None:
        print("no batch in progress — running the UNIVERSAL push checks only")
    else:
        require(state, "prepush")

    # ⚠⚠ FAIL CLOSED when asked to judge a push whose scope we cannot see (F3, /rely 2026-08-10),
    # and the predicate is a NAMED FUNCTION so a control can call it — see `unjudgeable_scope`,
    # which carries the measurement showing the old literal had stopped firing entirely.
    _unjudgeable = unjudgeable_scope(ranges)
    if _unjudgeable is not None:
        print("\nCANNOT JUDGE: no --ranges given and %s, so the scope of the"
              % _unjudgeable)
        print("push is unknown. This command is only meaningful BEFORE committing; afterwards the")
        print("hook supplies the pushed ranges. Run `git push` and let the hook decide, or pass")
        print("--ranges <base>..<tip>.")
        sys.exit(1)

    fires, ins, newfile = check_trigger5(ranges)
    print("trigger 5: %s (%d insertions, new .lean file: %s)"
          % ("FIRES — prior-art review REQUIRED" if fires else "does not fire", ins, newfile))
    # ⚠⚠ THERE IS NO `bad` ACCUMULATOR HERE ANY MORE, AND ITS ABSENCE IS THE POINT (`B4`). Every
    # gating leg below writes its own row via `verdict_record` at the moment it computes; nothing in
    # this frame holds a failure count, so nothing in this frame can discard one. If you find
    # yourself re-introducing a local total to hand to the enforcement call, you are rebuilding the
    # exact defect this removed — read `_EXPECTED` and `enforce_prepush_verdict` first.
    #
    # ⚠ ONE judgement per run. Without this a second `cmd_prepush` in the same process would
    # inherit the first run's rows, and a step that failed to run would look like it had reported.
    verdict_reset()
    # Purity and SSOT are enforced HERE as well as at precommit, because precommit is a manual
    # command and the pre-commit hook never blocks — so before this they were the only two
    # obligations with no automatic enforcement anywhere (Tim, 2026-08-09). They are safe at push in
    # a way `build` is not: neither has anything to do with `sorry`, so neither conflicts with the
    # stub-first protocol, which commits and pushes deliberately incomplete proofs.
    decls = added_decls()
    # ⚠⚠ EACH LEG RECORDS ITS OWN COUNT — THERE IS NO ACCUMULATOR TO ANNIHILATE (`B4`). These four
    # incremented a local `bad` that was handed to `enforce_prepush_verdict`, so `bad * 0` silenced
    # all four (plus the two signal legs below) in one edit. The first element of each row is now a
    # REGISTRY KEY, stable and identifier-shaped, distinct from the display name beside it.
    for key, name, ok, why in [("purity", "purity") + check_purity(decls),
                               ("ssot", "ssot") + check_ssot(decls),
                               ("pdf_coupling", "pdf coupling") + check_pdf_coupling(ranges),
                               # ⚠ BLOCKS, and it is satisfiable one file at a time by construction
                               #   — see check_prior_art_attribution. Placed with purity and ssot
                               #   because it is the same shape: a per-declaration obligation the
                               #   corpus owes, enforced against what THIS push actually changed.
                               ("prior_art_attrib", "prior-art attrib")
                               + check_prior_art_attribution(ranges)]:
        # ⚠⚠ `RLYB4-5` — `ok` MUST BE A BOOL, AND THIS IS `DC-45` INSIDE THE LOOP THAT ENFORCES IT.
        #   Measured by /rely round 2: swapping two identifiers in the `for` target above —
        #   `for key, name, ok, why` -> `for key, name, why, ok` — makes each leg's non-empty `why`
        #   STRING the truthy `ok`. Every leg then reads as passing, BOTH halves move together so
        #   the agreement check has nothing to disagree about, `guards.py` stays at exit 0 and the
        #   probe is blind because the routing count never moves. Result: `ssot ok False` printed
        #   above `prepush PASS`, exit 0. **A truthy string and `True` are indistinguishable to
        #   `if not ok` and carry entirely different meanings** — so the fix is to make the VALUE
        #   carry the difference rather than to trust the unpacking order.
        if not isinstance(ok, bool):
            die("push verdict leg %r reported a non-boolean outcome (%s: %r). A leg's verdict must "
                "be True or False; a truthy string reads as PASS at every site that tests it. This "
                "is a wiring error in cmd_prepush, not a finding about the corpus — it fails CLOSED."
                % (key, type(ok).__name__, ok))
        if key == _forced:                     # FAIL-ONLY: assigns False, never True
            ok, why = False, "FORCED FAIL by %s (test seam) — real result: %s" % (FORCE_FAIL_ENV, why)
        print("  %-18s %-4s %s" % (name, "ok" if ok else "FAIL", why))
        # ⚠ TWO SEPARATE STATEMENTS, DELIBERATELY (`RLYB4-1`). The tally counts what reached the
        #   SCREEN; the registry holds what was RECORDED. `enforce_prepush_verdict` requires them to
        #   agree, so annihilating either one alone now refuses instead of passing.
        if not ok:
            display_fail(key)
        verdict_record(key, 0 if ok else 1)

    # ⚠ ADVISORY, and `bad` is deliberately NOT incremented — see `prose_shrank_unpaired`. Only a
    # human can tell a verified duplicate from a loss. The count PRINTS on every run, clean or not,
    # because a downgraded leg has to get louder rather than quieter (RLY25-1) and because the one
    # instance that reached a commit did so by being unnoticed, not by being waved through.
    _shrunk = prose_shrank_unpaired(ranges)
    if _shrunk:
        print("  %-18s %-4s %d .lean prose block(s) shrank with no sibling .md gaining lines"
              % ("prose migration", "WARN", len(_shrunk)))
        for _f, _n in _shrunk[:5]:
            print("      %s  net -%d — was it a VERIFIED duplicate, or should it have MIGRATED?"
                  % (_f, _n))
        print("      Migrate to <Name>.md, or record per-item why deletion was safe in the")
        print("      commit message. A line-counting gate scores both identically.")
    else:
        print("  %-18s %-4s no .lean prose block shrank unpaired in this scope"
              % ("prose migration", "ok"))
    # THE INTERPRETATION LAYER. Advisory by construction: `agent_gate.run()` always returns 0 and
    # `bad` is deliberately NOT incremented, so a fuzzy component can never stop a push.
    # ⚠ DO NOT PROMOTE THIS TO BLOCK. Measured 2026-08-21 before adoption: 1 false positive in 6
    # healthy runs, and UNSTABLE — byte-identical input returned TRUSTWORTHY twice and
    # NOT_TRUSTWORTHY once. The >=2-of-3 rule takes that to 0, but the underlying variance is real
    # and blocking on a coin flip is how a gate earns itself a bypass. CLAUDE.md rung 5: the screen
    # may replace the enumeration, it may NEVER replace the verdict.
    # ⚠ It is announced in the manifest even when switched off, so "not run" is visible rather than
    # silent — the failure `RLY25-1` is made of.
    try:
        agent_gate.run()
    except Exception as e:                                  # never let the advisory layer break a push
        print("  agent gate         WARN  interpretation layer errored, ignored: %r" % (e,))
    # WHICH reviews are required, WHY, and WHAT their signals actually say — named in full rather
    # than left as three filenames (Tim, 2026-08-10: report the reviews being run and a summary of
    # their parameters). A signal is only as good as what it certified, so the recorded verdict line
    # is echoed here: "cleared" must never be read as "clean".
    scope = reviewable_changed(ranges)
    # ⚠ SAME REFERENT FIX AS `check_prior_art_attribution`. "scope: 1 reviewable file(s)" over a
    # WORKING TREE whose only change was `gate_round.json` read as a one-file push and nearly
    # cleared a nine-commit one (measured 2026-09-12). A count with no named set is a true
    # number about an unstated object.
    _scope_basis = ("the PUSHED RANGE(S)" if ranges is not None
                    else "the WORKING TREE (manual run)")
    print("\n=== Reviews required for this push ===")
    print("  scope: %d reviewable file(s) in %s%s"
          % (len(scope), _scope_basis,
             (" — e.g. " + ", ".join(scope[:3])) if scope else " (none)"))
    # REPORT ONLY — see `ADMITTED_ENV`. Nothing below reads this answer; the signals legs are unchanged.
    for _line in review_report():
        print(_line)
    meta = {
        "editorial": ("/editorial-review", "internal consistency + prose precision",
                      "any reviewable prose in the push"),
        "adversary": ("/adversary-review", "cold-reader triage + central-claim audit",
                      "any reviewable prose in the push"),
        "prior_art": ("/prior-art-review", "closest prior art cited or shown absent",
                      "trigger 5: a new .lean file, or >=50 inserted .lean lines"),
    }
    for name, valid, why in check_signals(ranges):
        need = signal_need(name, fires)
        ok = valid or not need
        if "signal:%s" % name == _forced:      # FAIL-ONLY: assigns False, never True
            ok, why = False, "FORCED FAIL by %s (test seam) — real result: %s" % (FORCE_FAIL_ENV, why)
        agent, purpose, when = meta[name]
        print("  %-20s %-4s %s" % (agent, "ok" if ok else "FAIL",
                                   "REQUIRED" if need else "not required"))
        print("      purpose  %s" % purpose)
        print("      fires on %s" % when)
        print("      ledger   step `%s` — %s" % (name, why))
        # ⚠ `B4`: the signal legs record themselves too. The key is prefixed so a failing review
        #   signal is distinguishable from a mechanical leg in the refusal message, and so a step
        #   name can never collide with one of the four inline keys above.
        # ⚠ And the same two-statement split as the loop above (`RLYB4-1`) — this line was the
        #   SECOND one-token site, covering both signal legs at once. Same bool guard, same reason
        #   (`RLYB4-5`): `ok` is computed as `valid or not need` and must stay a bool.
        if not isinstance(ok, bool):
            die("push verdict leg 'signal:%s' reported a non-boolean outcome (%s: %r). It fails "
                "CLOSED — see the identical guard on the inline legs above."
                % (name, type(ok).__name__, ok))
        if not ok:
            display_fail("signal:%s" % name)
        verdict_record("signal:%s" % name, 0 if ok else 1)
    # ⚠ BEFORE the `die`, not after the PASS. On the success path only it would print just when the
    # push was already clear — and a recurrence count matters MOST while something is failing. That
    # placement would have re-created the original defect (surfacing at the rarest moment) in a new
    # location, which is the shape this whole change exists to correct.
    _recurrence_note()
    # ⚠⚠ ONE CALL, NO ARGUMENT, NO RETURN VALUE, NOTHING TO DISCARD. `enforce_prepush_verdict` reads
    # the registry and DIES on a failure; it does not hand this frame a number to rebind, zero out
    # or ignore. That is `RLY28-1` attempt six, and the five before it all failed at exactly this
    # line by leaving a value here for the caller to throw away.
    # ⚠ `B4` TOOK THE LAST ONE AWAY. Until 2026-09-05 this read `enforce_prepush_verdict(bad)`, and
    # `bad` carried six gating legs, so `(bad * 0)` was a live one-token neuter for all six. There is
    # no argument now — every leg writes its own registry row where it computes it.
    enforce_prepush_verdict()
    if state:
        state["stages"]["prepush"] = {"ok": True, "tool": self_hash()}
        save(state)
    print("\nprepush PASS")


def _recurrence_note():
    """Surface the top recurring PROCESS shapes. Advisory — never blocks.

    ⚠⚠ **THE SELF-HEALING INPUT WAS WIRED TO THE WRONG ENTRY POINT, AND THAT IS A TRIGGER DEFECT
    RATHER THAN A MISSING RULE.** `selfheal.py` counts how often a process shape has recurred, which
    is the one fact the escalation ladder in `CLAUDE.md` § *WHEN A FAILURE RECURS* needs — and it ran
    **only from `/ship`**, the release command, i.e. the least frequent action in the project.
    `CLAUDE.md` does not mention it at all, so a fresh session cannot know it exists.

    The ladder's own trigger is *"a gate returned FAIL"*, which fires on every ORDINARY finding too —
    so it fires constantly and therefore fires never, the cry-wolf shape this project elsewhere says
    to narrow. **The fact that discriminates is RECURRENCE, and it is decidable, so it belongs in the
    output of the command that runs before every push.**

    Measured 2026-08-18, which is why this exists: one session made the SAME control-subject error
    three times (`DC-25`), each time closing the instance with a local comment and never lifting it to
    a class — while the counter that would have said *"this shape has now happened three times"* sat
    unrun. Six commits, zero process files touched.

    ⚠ ADVISORY BY DESIGN. Counting is decidable; deciding whether N rows are one phenomenon or N
    coincidences is not, and auto-filing would produce a class register nobody verified — the failure
    `DEFECT_CLASSES.md` exists to avoid. It prints; a human or an agent judges.
    """
    try:
        # ⚠ ENCODING EXPLICIT. `text=True` alone decodes with the Windows codepage, and this child's
        # output contains the arrow and star glyphs the report format uses — so it raised
        # `UnicodeDecodeError`, left `stdout` as None, and took the whole `prepush` down with it.
        # That is `SH-2` (encoding/codepage, 9 ledger rows, still no class row) occurring INSIDE the
        # function written to surface recurrences, which is as good an argument for the class row as
        # the count was.
        r = subprocess.run([sys.executable, os.path.join(str(HERE), "selfheal.py")],
                           # 5s, not 60: a hanging child would otherwise cost a full minute on
                           # EVERY push for a note that is advisory. (/rely round 3, ORDINARY.)
                           capture_output=True, text=True, timeout=5,
                           encoding="utf-8", errors="replace")
    except (OSError, subprocess.SubprocessError) as e:
        # ⚠ SECOND ROUTE TO THE SAME PROPERTY (`/rely` R3-O1). The `else` below was fixed while
        # this branch still returned in silence — and `TimeoutExpired` IS a `SubprocessError`, so
        # a hung child rendered exactly like "nothing over threshold". SH-3 inside the function
        # whose own comment cites SH-3. Advisory either way; it never blocks.
        print()
        print("  recurrence note: selfheal.py could not be run (%s) — advisory, and NOT a clean"
              " bill" % type(e).__name__)
        return
    # ⚠ ADVISORY MEANS ADVISORY: this must never be able to fail the caller. A note about process
    # health that can block a push is a worse defect than the one it reports.
    # ⚠⚠ THE EXIT CODE IS READ FIRST, NOT ONLY WHEN STDOUT IS EMPTY (`/rely` round 4, B4). A real
    # child that printed a TRUNCATED report and then died rendered as a complete advisory, because
    # the status was consulted only on empty output. Partial output is the dangerous case: it
    # LOOKS like a full answer.
    # ⛔ AN EARLIER VERSION OF THIS COMMENT SAID `ship.py cmd_plan` "is the sibling that had this
    # right", AND THAT WAS MEASURABLY FALSE — round 5 found `cmd_plan` reading content before
    # status, the third of three consumers to carry the defect. Corrected 2026-09-16. All three
    # now check the exit code first; a claim about a sibling is a claim, and this one was not run.
    # ⚠ SILENT AND NOTHING-TO-REPORT ARE DIFFERENT ANSWERS (R-ZERONULL). Advisory either way.
    if r.returncode != 0 or not r.stdout:
        print()
        print("  recurrence note: selfheal.py did not complete (exit %s, %d byte(s) of output) —"
              " advisory, and NOT a clean bill" % (r.returncode, len(r.stdout or "")))
        return
    # ⚠ THE MARKERS ARE IMPORTED, NOT RETYPED (`/rely` R2-B1). A retyped literal here matched one
    # of the two UNCLASSED markers, so shapes naming a class row that does not exist never
    # reached this channel — under a heading promising the whole set. SH-7 selecting SH-7.
    rows = [l.strip() for l in r.stdout.splitlines()
            if any(m in l for m in selfheal.UNCLASSED_MARKS)]
    if not rows:
        return
    print()
    print("  recurring process shapes with NO class row (advisory — `selfheal.py` for the full list):")
    for line in rows[:3]:
        print("    %s" % line.lstrip("0123456789. "))
    print("  A shape here has recurred and has no DETECTOR. Second occurrence = a class"
          " (DEFECT_CLASSES.md);")
    print("  third = the rule's TRIGGER is wrong. See CLAUDE.md § R-RECUR.")


BUCKET_BASELINE = {"class": "class_baseline.txt", "modal": "modal_baseline.txt",
                   "pov": "pov_baseline.txt", "prose-block": "prose_baseline.txt",
                   "prose-doc": "prose_baseline.txt", "prose-bare": "prose_baseline.txt",
                   "prose-unlabelled": "prose_baseline.txt"}


def baseline_entries(bucket):
    """The non-comment entries of this bucket's baseline, as a set."""
    fn = BUCKET_BASELINE.get(bucket)
    if not fn:
        return None
    p = os.path.join(BASE, fn)
    if not os.path.exists(p):
        return set()
    return {l.strip() for l in io.open(p, encoding="utf-8-sig").read().splitlines()
            if l.strip() and not l.startswith("#")}


def cmd_close():
    """Close the batch, VERIFYING the two things a close is supposed to guarantee.

    ⚠ This used to print two reminders and delete the state file — a close that checks nothing is a
    proxy for a close that happened (DC-18). The baseline must have SHRUNK and the result must be a
    STRICT SUBSET of what it was at `start`: regenerating grandfathers sites nobody read, which
    falsifies the baseline's own premise that each entry was verified by reading it."""
    state = load()
    require(state, "close")
    bucket = state["bucket"]
    print("close: bucket '%s'" % bucket)

    bad = 0
    before = set(state.get("baseline_at_start") or [])
    after = baseline_entries(bucket)
    if after is None:
        print("  %-22s %-4s %s" % ("baseline", "—", "no baseline maps to this bucket"))
    elif not before:
        print("  %-22s %-4s %s" % ("baseline", "—", "no snapshot at start (batch predates the check)"))
    else:
        shrank = len(after) < len(before)
        subset = after <= before
        ok = shrank and subset
        detail = ("%d → %d entries, strict subset" % (len(before), len(after)) if ok
                  else ("NOT a subset — %d entry/entries were ADDED or REGENERATED: %s"
                        % (len(after - before), sorted(after - before)[:2]) if not subset
                        else "did not shrink (%d entries, unchanged)" % len(after)))
        print("  %-22s %-4s %s" % ("baseline", "ok" if ok else "FAIL", detail))
        bad += 0 if ok else 1

    # ⚠ STDOUT ONLY (`RLY29-2`): a warning on stderr is not a porcelain line, and reading one as
    # "the ledger is dirty" would pass this check because of the warning.
    rc_d, dirty, _err = sh_split("git", "status", "--porcelain", "--", ".claude-local/DEFECTS.md")
    if rc_d != 0:
        # A git error here used to read as "the ledger was touched" — the close check passing
        # BECAUSE the probe failed.
        die("git failed probing the ledger; refusing to judge whether it was updated:\n%s" % dirty)
    ledgered = bool(dirty.strip()) or bool(state.get("ledgered"))
    print("  %-22s %-4s %s" % ("ledger", "ok" if ledgered else "WARN",
                               "DEFECTS.md touched" if ledgered
                               else "DEFECTS.md unchanged — findings recorded nowhere?"))

    if bad:
        die("%d close check(s) failed — the batch is not finished" % bad)
    os.remove(STATE)
    print("\nbatch closed. State cleared.")


def cmd_status():
    state = load()
    if not state:
        print("no batch in progress")
        return
    print("bucket '%s' started at %s (%d sites)"
          % (state["bucket"], state["head"], state["worklist_size"]))
    for s in STAGES:
        mark = ("done" if stage_done(state, s)
                else ("STALE" if s in state["stages"] else "—"))
        note = state["stages"].get(s, {}).get("note", "")
        print("  %-11s %-5s %s" % (s, mark, note))


# --------------------------------------------------------------------------- controls
# Every case below is a bug this file actually shipped on 2026-08-09, in the order they were found.
DECL_CASES = [
    ("lowercase theorem name", "theorem member_ne_floor : True := trivial\n", {"member_ne_floor"}),
    ("prose in a /-! block wrapping onto 'instance'",
     "/-! the content is in the `Category`\ninstance below (Kleisli composition). -/\n", set()),
    ("prose in a /-- docstring", "/-- not a global `instance` without colliding. -/\n", set()),
    ("line comment", "-- def notReal : Nat := 0\n", set()),
    ("noncomputable + attribute",
     "@[simp]\nnoncomputable def realOne : Nat := 0\n", {"realOne"}),
    ("declaration after a comment block",
     "/-! a note. -/\ntheorem realTwo : True := trivial\n", {"realTwo"}),
]


def _basis_controls():
    """BASIS-EMPTY-1. Returns `(bad, total)`. Every git touch and every send is a seam, so nothing
    here runs `write-tree` or reaches the ledger. `sent` records what `record.emit` WOULD have sent;
    the red rows assert it stays EMPTY, because "refused by the ledger" was the old, accidental
    safety net and must not be what these rows rely on."""
    import threading
    print("ledger basis: never sent unresolved; one pinned tree per run (BASIS-EMPTY-1)")
    T1, T2, STALE = "a" * 40, "b" * 40, "c" * 40
    P, BLOB = "README.md", "d" * 40
    saved = {n: getattr(common, n) for n in ("_git_write_tree", "ledger_subjects", "ref_blobs",
                                             "_BASIS_BACKOFF")}
    saved_emit, saved_env = record.emit, os.environ.get(common.INDEX_TREE_ENV)
    sent, calls, lock = [], [], threading.Lock()

    def _wt(seq):
        """A `write-tree` seam answering from `seq`, its last entry repeating."""
        def run():
            with lock:
                calls.append(1)
                return seq[min(len(calls), len(seq)) - 1]
        return run

    def _fake_emit(**kw):
        with lock:
            sent.append(kw["basis"]["value"])
        return "rec-ctl"

    def _leg(capture=True):
        if not capture:          # threaded legs: the caller holds ONE redirect for all of them
            return common.emit_verdict("ctl_step", ok_rels=[P], ref=common.INDEX), ""
        buf, real = io.StringIO(), sys.stdout
        try:
            sys.stdout = buf
            rc = common.emit_verdict("ctl_step", ok_rels=[P], ref=common.INDEX)
        finally:
            sys.stdout = real
        return rc, buf.getvalue()

    def _setup(seq, pin=None, held=None):
        del sent[:], calls[:]
        common._git_write_tree = _wt(seq)
        common._BASIS_BACKOFF = 0
        common.ledger_subjects = lambda rels, ref="HEAD": ([{"path": P, "git_blob_id": BLOB}], [])
        common.ref_blobs = lambda ref="HEAD": ({P: BLOB} if held is None else held)
        record.emit = _fake_emit
        if pin is None:
            os.environ.pop(common.INDEX_TREE_ENV, None)
        else:
            os.environ[common.INDEX_TREE_ENV] = pin

    LOCKED = (128, "", "fatal: Unable to create '.git/index.lock': File exists.")
    rows = []
    try:
        for label, seq, pin, held, why in [
                ("write-tree lock loss: NOT sent, exit 2", [LOCKED], None, None, "index.lock"),
                ("write-tree exit 0, empty stdout: NOT sent", [(0, "", "")], None, None,
                 "basis unresolved"),
                ("a malformed pin: NOT sent, exit 2", [(0, T1, "")], "zzz", None,
                 "not a tree id"),
                ("pinned tree lacking the blob: NOT sent", [(0, T1, "")], T1, {P: "e" * 40},
                 "does not carry")]:
            try:
                _setup(seq, pin, held)
                rc, out = _leg()
                rows.append((label, rc == 2 and not sent and why in out))
            except Exception:                                  # noqa: BLE001 — a crash is red
                rows.append((label, False))
        try:
            _setup([LOCKED, LOCKED, (0, T1 + "\n", "")])
            rc, out = _leg()
            rows.append(("transient lock loss is retried, then sent", rc == 0 and sent == [T1]))
        except Exception:                                      # noqa: BLE001
            rows.append(("transient lock loss is retried, then sent", False))
        # The concurrency property itself: eight legs at once, a write-tree that would answer each
        # differently, and the parent's pin must be the only value any of them sends.
        for label, pin_first in [("8 concurrent legs send the PINNED tree only", False),
                                 ("parent pins once; 8 legs share it, 1 write-tree", True)]:
            try:
                _setup([(0, T2, ""), (0, "f" * 40, ""), (0, "9" * 40, "")],
                       pin=(STALE if pin_first else T1),
                       held={P: BLOB})
                if pin_first:
                    common.pin_index_tree()
                want = T2 if pin_first else T1
                rcs = []
                ths = [threading.Thread(target=lambda: rcs.append(_leg(False)[0]))
                       for _ in range(8)]
                _real_out, sys.stdout = sys.stdout, io.StringIO()
                try:
                    for th in ths:
                        th.start()
                    for th in ths:
                        th.join()
                finally:
                    sys.stdout = _real_out
                rows.append((label, rcs == [0] * 8 and sent == [want] * 8
                             and len(calls) == (1 if pin_first else 0)))
            except Exception:                                  # noqa: BLE001
                rows.append((label, False))
        try:
            _setup([LOCKED], pin=STALE)
            got = common.pin_index_tree()
            rows.append(("a failed parent pin CLEARS an inherited pin",
                         got[0] is None and common.INDEX_TREE_ENV not in os.environ))
        except Exception:                                      # noqa: BLE001
            rows.append(("a failed parent pin CLEARS an inherited pin", False))
    finally:
        for n, v in saved.items():
            setattr(common, n, v)
        record.emit = saved_emit
        if saved_env is None:
            os.environ.pop(common.INDEX_TREE_ENV, None)
        else:
            os.environ[common.INDEX_TREE_ENV] = saved_env
    # Both parents pin BEFORE any leg launches: `hooks._pre_commit` before its prefetch and its
    # leg loop, `cmd_precommit` before `check_suite`. Read from source, since neither can be run here.
    import ast as _ast

    def _pins_first(path, fn, later):
        try:
            with io.open(path, encoding="utf-8") as fh:
                tree = _ast.parse(fh.read())
        except (OSError, SyntaxError, ValueError):
            return False
        for f in _ast.walk(tree):
            if isinstance(f, _ast.FunctionDef) and f.name == fn:
                pin = [c.lineno for c in _ast.walk(f) if isinstance(c, _ast.Call)
                       and getattr(c.func, "attr", None) == "pin_index_tree"]
                after = [c.lineno for c in _ast.walk(f) if isinstance(c, _ast.Call)
                         and (getattr(c.func, "id", None) in later
                              or getattr(c.func, "attr", None) in later)]
                return bool(pin) and bool(after) and min(pin) < min(after)
        return False
    _here = os.path.dirname(os.path.abspath(__file__))
    rows.append(("hooks._pre_commit pins before any leg",
                 _pins_first(os.path.join(_here, "hooks.py"), "_pre_commit",
                             ("_start_commit_prefetch", "py"))))
    rows.append(("cmd_precommit pins before check_suite",
                 _pins_first(os.path.abspath(__file__), "cmd_precommit", ("check_suite",))))
    b = 0
    for label, ok in rows:
        print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
        b += 0 if ok else 1
    return b, len(rows)


def _g1_controls():
    """Controls for LED-8, RLY29-2, P5-4, REL8-5, COUPLE-SHARED-1, RLY54-2 and the unverified-subjects
    branch of the pdf coupling leg. Each row pins BOTH directions: the defect state must give the
    fixed answer, and a clean state must keep the old one. Returns (bad, total)."""
    bad = total = 0
    rows = []

    # LED-8 / BATCH-1: an unrecorded checker's line quotes ITS reason and dispatches on 2 vs 4.
    _real_sh = globals()["sh"]
    _child = {"check_prose.py": (2, "UNDECIDED: record refused by verdictLedger: V11 revision 0 "
                                    "already exists\n"),
              "check_pov.py": (4, "UNDECIDED: record refused by verdictLedger: V16c unapproved\n"),
              "check_modal.py": (0, "ok\n"), "check_classes.py": (0, "ok\n"),
              "check_encoding.py": (0, "ok\n")}
    try:
        globals()["sh"] = lambda *a, **k: _child.get(os.path.basename(str(a[1])), (0, ""))
        _ok, _msg = check_suite()
    finally:
        globals()["sh"] = _real_sh
    rows += [("LED-8: exit 2 quotes the child's reason",
              "check_prose.py: exit 2" in _msg and "V11 revision 0" in _msg),
             ("LED-8: exit 4 is named a terminal REFUSAL",
              "check_pov.py: exit 4" in _msg and "REFUSED" in _msg and "V16c" in _msg),
             ("LED-8: no line asserts 'No key exists'", "No key exists" not in _msg and not _ok),
             ("LED-8: clean checkers stay off the line", "check_modal.py" not in _msg)]

    # RLY29-2: an exit-0 warning on stderr is never a changed file.
    class _P(object):
        def __init__(self, out, err, rc=0):
            self.stdout, self.stderr, self.returncode = out, err, rc
    _real_run = subprocess.run
    try:
        subprocess.run = lambda *a, **k: _P("tools/verify/a.py\n",
                                             "warning: in the working copy of 'x', CRLF will be "
                                             "replaced by LF\n")
        _got = changed_files(["o/m..T"])
    finally:
        subprocess.run = _real_run
    rows.append(("RLY29-2: stderr warning is not a scope entry", _got == ["tools/verify/a.py"]))

    # P5-4: an untracked file's print discharges only its OWN declarations.
    _files = [("ZeroParadox/T.lean", "theorem t1 : True := trivial\n#print axioms t1\n"),
              ("ZeroParadox/Scratch.lean", "theorem s1 : True := trivial\n#print axioms s1\n"
                                           "#print axioms t2\n")]
    _have = print_axioms_on_disk(_files, {"ZeroParadox/T.lean"})
    _miss = missing_purity_keys(["ZeroParadox/T.lean::t1", "ZeroParadox/T.lean::t2",
                                 "ZeroParadox/Scratch.lean::s1"], _have)
    rows += [("P5-4: untracked print does not cover a tracked decl",
              "ZeroParadox/T.lean::t2" in _miss),
             ("P5-4: tracked print and own-file print still count",
              "ZeroParadox/T.lean::t1" not in _miss and "ZeroParadox/Scratch.lean::s1" not in _miss),
             ("P5-4: git unreadable narrows, never widens",
              print_axioms_on_disk(_files, None)[0] == set())]

    # REL8-5: the pairing reads the script AT THE PUSHED TIP, not from disk.
    _real_split = globals()["sh_split"]
    try:
        globals()["sh_split"] = lambda *a, **k: ((0, "OUT = 'ZP-Q_Renamed.pdf'\n", "")
                                                 if a[1] == "show" and a[2].startswith("T:")
                                                 else (128, "", "fatal: no such path"))
        _at = _script_at_push("scripts/build_q.py", ["o/m..T"])
        _none = _script_at_push("scripts/build_q.py", ["o/m..U"])
    finally:
        globals()["sh_split"] = _real_split
    rows += [("REL8-5: script text comes from the pushed tip", _at is not None and "Renamed" in _at),
             ("REL8-5: absent at every tip pairs nothing (None)", _none is None)]

    # REL8-5 at the CALL SITE (`G1-3`): `check_pdf_coupling` itself pairs from the tip's bytes. The
    # script does not exist on disk, so a disk read pairs nothing and the leg would fall through to
    # the (stubbed, raising) ledger and return False.
    def _raise(*_a, **_k):
        raise common.BasisUnresolved("ctl: gitRobot unreachable")

    def _coupling(tip_text):
        def _split(*a, **k):
            if a[1] == "diff":
                return 0, "ZP-Q_Tip.pdf\nscripts/build_g1_ctl_only_at_tip.py\n", ""
            if a[1] == "show" and a[2] == "T:scripts/build_g1_ctl_only_at_tip.py":
                return 0, tip_text, ""
            return 128, "", "fatal: ctl"
        saved = (globals()["sh_split"], globals()["changed_files"], common.ledger_subjects)
        try:
            globals()["sh_split"] = _split
            globals()["changed_files"] = lambda ranges=None: [
                "ZP-Q_Tip.pdf", "scripts/build_g1_ctl_only_at_tip.py"]
            common.ledger_subjects = _raise
            return check_pdf_coupling(["o/m..T"])
        except Exception as _e:                              # noqa: BLE001
            return "raised", repr(_e)
        finally:
            globals()["sh_split"], globals()["changed_files"], common.ledger_subjects = saved
    _p_ok, _p_why = _coupling("OUT = 'ZP-Q_Tip.pdf'\n")
    _n_ok, _n_why = _coupling("OUT = 'ZP-Q_Renamed.pdf'\n")
    rows += [("REL8-5 call site: tip copy naming the PDF pairs it",
              _p_ok is True and "paired with the script" in str(_p_why)),
             ("REL8-5 call site: tip copy NOT naming it does not",
              _n_ok is False and "no build script IN THIS PUSH" in str(_n_why))]

    # COUPLE-SHARED-1: the shared layer is NAMED when in the push, silent otherwise.
    rows += [("COUPLE-SHARED-1: shared layer named when pushed",
              "SHARED BUILD LAYER" in shared_layer_note(["scripts/zp_utils.py", "ZP-A.pdf"])),
             ("COUPLE-SHARED-1: no note without it", shared_layer_note(["ZP-A.pdf"]) == "")]

    # Unverified subjects (common.BasisUnresolved) fail the coupling leg CLOSED, with its own reason.
    _saved = (globals()["changed_files"], common.ledger_subjects, globals()["_script_at_push"])
    try:
        globals()["changed_files"] = lambda ranges=None: ["ZP-Z_Orphan.pdf"]
        globals()["_script_at_push"] = lambda p, r: None
        common.ledger_subjects = _raise
        _orig_exists = os.path.exists
        os.path.exists = lambda p: True if p.endswith("ZP-Z_Orphan.pdf") else _orig_exists(p)
        try:
            _ok_u, _why_u = check_pdf_coupling(None)
        finally:
            os.path.exists = _orig_exists
    except Exception as _e:                                  # noqa: BLE001 — a raise IS the defect
        _ok_u, _why_u = "raised", repr(_e)
    finally:
        globals()["changed_files"], common.ledger_subjects, globals()["_script_at_push"] = _saved
    rows.append(("unverified subjects -> False, named, no raise",
                 _ok_u is False and "COULD NOT BE KEYED" in (_why_u or "")))

    # RLY54-2: REFUSED with stray case/whitespace still takes the REFUSED branch.
    _real_ss, _real_rc = record.step_status, globals()["reviewable_changed"]
    try:
        globals()["reviewable_changed"] = lambda ranges=None: ["README.md"]
        record.step_status = lambda ref, action="commit": {
            s: (" refused\n" if s == REVIEW_STEPS[0] else "SATISFIED") for s in REVIEW_STEPS}
        _r = [x for x in check_signals(["o/m..A"]) if x[0] == REVIEW_STEPS[0]][0]
    finally:
        record.step_status, globals()["reviewable_changed"] = _real_ss, _real_rc
    rows.append(("RLY54-2: ' refused\\n' takes the REFUSED branch",
                 not _r[1] and "NOTHING has been established" in _r[2]))

    # R2-B1: the FAIL-ONLY seam. Unknown name refuses; a real name FAILs exactly that leg; unset or
    # empty is inert; and it never moves any OTHER leg (a purity failure survives a forced ssot).
    def _fs(env):
        try:
            return forced_fail_leg(env)
        except SystemExit as _x:
            return ("exit", _x.code)
    rows += [("R2-B1 seam: unset / empty is inert",
              _fs({}) is None and _fs({FORCE_FAIL_ENV: "  "}) is None),
             ("R2-B1 seam: a real leg name is accepted", _fs({FORCE_FAIL_ENV: "ssot"}) == "ssot"),
             ("R2-B1 seam: an unknown name REFUSES (exit 1)",
              _fs({FORCE_FAIL_ENV: "nosuchleg"}) == ("exit", 1))]

    def _run_prepush(force, purity_ok=True):
        stubs = {"unjudgeable_scope": lambda *a, **k: None,
                 "check_trigger5": lambda *a, **k: (False, 0, False),
                 "added_decls": lambda *a, **k: [],
                 "check_purity": lambda d: (purity_ok, "stub"),
                 "check_ssot": lambda d: (True, "stub"),
                 "check_pdf_coupling": lambda *a, **k: (True, "stub"),
                 "check_prior_art_attribution": lambda *a, **k: (True, "stub"),
                 "prose_shrank_unpaired": lambda *a, **k: [],
                 "reviewable_changed": lambda *a, **k: [],
                 "review_report": lambda *a, **k: [],
                 "check_signals": lambda *a, **k: [(s, True, "stub") for s in REVIEW_STEPS],
                 "_recurrence_note": lambda *a, **k: None,
                 "load": lambda *a, **k: None}
        g = globals()
        saved = {n: g[n] for n in stubs}
        saved_ag, saved_env = agent_gate.run, os.environ.get(FORCE_FAIL_ENV)
        buf, real = io.StringIO(), sys.stdout
        code = None
        try:
            g.update(stubs)
            agent_gate.run = lambda *a, **k: 0
            if force is None:
                os.environ.pop(FORCE_FAIL_ENV, None)
            else:
                os.environ[FORCE_FAIL_ENV] = force
            sys.stdout = buf
            try:
                cmd_prepush(["HEAD~1..HEAD"])
                code = 0
            except SystemExit as _x:
                code = 0 if _x.code is None else _x.code
            verdict = dict(_VERDICT)
        finally:
            sys.stdout = real
            g.update(saved)
            agent_gate.run = saved_ag
            if saved_env is None:
                os.environ.pop(FORCE_FAIL_ENV, None)
            else:
                os.environ[FORCE_FAIL_ENV] = saved_env
            verdict_reset()
        return code, verdict, buf.getvalue()
    c0, v0, o0 = _run_prepush(None)
    c1, v1, o1 = _run_prepush("ssot")
    c2, v2, _o2 = _run_prepush("ssot", purity_ok=False)
    c3, v3, _o3 = _run_prepush("signal:%s" % REVIEW_STEPS[0])
    rows += [("R2-B1 seam: unset, clean legs -> prepush PASS", c0 == 0 and "prepush PASS" in o0
              and not any(v0.values())),
             ("R2-B1 seam: forced ssot FAILs ssot only, exits 1",
              c1 == 1 and v1.get("ssot") == 1 and sum(v1.values()) == 1 and "FORCED FAIL" in o1),
             ("R2-B1 seam: a real purity FAIL survives a forced ssot",
              c2 == 1 and v2.get("purity") == 1 and v2.get("ssot") == 1),
             ("R2-B1 seam: forced review signal FAILs it, exits 1",
              c3 == 1 and v3.get("signal:%s" % REVIEW_STEPS[0]) == 1 and sum(v3.values()) == 1)]

    print("G1 fixes: LED-8 / RLY29-2 / P5-4 / REL8-5 / COUPLE-SHARED-1 / RLY54-2 / R2-B1 seam")
    for label, ok in rows:
        print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
        bad += 0 if ok else 1
        total += 1
    return bad, total


def selftest():
    bad = 0
    # ⚠ `total` EXISTS SO THE SUMMARY CAN BE RE-DERIVED FROM THE ROWS ABOVE IT. Until 2026-09-16
    # this printed a bare "selftest: PASS" with no count at all, so the only way to learn how much
    # it covered was to count the lines by hand — which two readers did on the same day and got
    # 28 and 33. A suite that cannot state its own size cannot be cited, and `R-NOTINLIB` now
    # requires re-deriving any count of what a tool does from that tool's own output.
    total = 0
    print("decls_in — comment stripping and name shape")
    for label, src, want in DECL_CASES:
        got = decls_in(src)
        ok = got == want
        print("  %-46s %s" % (label, "ok" if ok else "*** got %s, want %s ***" % (got, want)))
        bad += 0 if ok else 1
        total += 1

    print("stage ordering")
    st = {"stages": {"start": {"ok": True}}, "checker_hashes": {}}
    cases = [("skipping a stage blocks", "probe", False),
             ("the next stage in order is allowed", "ledger", True)]
    for label, stage, should_pass in cases:
        i = STAGES.index(stage)
        allowed = all(stage_done(st, p) for p in STAGES[1:i])
        ok = allowed == should_pass
        print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
        bad += 0 if ok else 1
        total += 1

    print("gate-stage staleness (DC-18)")
    fresh = {"stages": {"precommit": {"ok": True, "tool": self_hash()}}}
    stale = {"stages": {"precommit": {"ok": True, "tool": "deadbeef1234"}}}
    for label, state, want in [("passed under THIS tool counts", fresh, True),
                               ("passed under an OLDER tool does not", stale, False)]:
        ok = stage_done(state, "precommit") == want
        print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
        bad += 0 if ok else 1
        total += 1

    # ⚠⚠ RLY36-2. The freshness question must be asked about the content the push PUBLISHES, and
    # for two months it was asked about the literal ref `HEAD` while the changed-file half of the
    # same answer honoured `ranges`. A spy on `record.step_status` is the only way to see which ref
    # was asked — the return value is identical either way, which is precisely why nothing caught
    # it. Mutation-verified when landed: restoring `refs = ["HEAD"]` turns exactly the three
    # range-sensitive rows below red and leaves the fail-closed row green.
    print("signal freshness is asked at the pushed TIP (RLY36-2)")
    tip_cases = [("tip of a..b", ["origin/main..HEAD~9"], ["HEAD~9"]),
                 ("bare ref is its own tip", ["deadbeef"], ["deadbeef"]),
                 ("two ranges, two tips", ["o/m..A", "o/m..B"], ["A", "B"]),
                 ("no ranges falls back to HEAD", None, ["HEAD"]),
                 ("a blank range never asks about nothing", ["  "], ["HEAD"])]
    for label, rngs, want in tip_cases:
        got = _range_tips(rngs)
        ok = got == want
        print("  %-46s %s" % (label, "ok" if ok else "*** got %s, want %s ***" % (got, want)))
        bad += 0 if ok else 1
        total += 1

    asked, _real = [], record.step_status
    _real_changed = reviewable_changed
    try:
        globals()["reviewable_changed"] = lambda ranges=None: ["README.md"]

        def _spy(ref, action="commit"):
            asked.append(ref)
            # STALE only at the SECOND tip, so "worst-wins" is what is being measured and not
            # "the first answer happened to be right".
            return {s: ("STALE" if (ref == "B" and s == REVIEW_STEPS[0]) else "SATISFIED")
                    for s in REVIEW_STEPS}

        record.step_status = _spy
        rows = check_signals(["o/m..A", "o/m..B"])
        for label, ok in [("asks at EVERY tip, not just the first", asked == ["A", "B"]),
                          ("not-SATISFIED at ANY tip governs",
                           not [r for r in rows if r[0] == REVIEW_STEPS[0]][0][1]),
                          ("a step clean at both tips still passes",
                           all(r[1] for r in rows if r[0] != REVIEW_STEPS[0]))]:
            print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
            bad += 0 if ok else 1
            total += 1

        record.step_status = lambda ref, action="commit": None if ref == "B" else {}
        rows = check_signals(["o/m..A", "o/m..B"])
        ok = all(not r[1] for r in rows)
        print("  %-46s %s" % ("unreachable at ANY tip fails CLOSED", "ok" if ok else "*** WRONG ***"))
        bad += 0 if ok else 1
        total += 1

        # ⚠⚠ `REFUSED` BLOCKED BEFORE THIS BRANCH EXISTED — the generic `else` fails closed — so a
        # control that only asserted BLOCKING would have been green against the defect. The defect
        # was the REMEDY: it printed "run the gate and let it record its own verdict", the one
        # instruction that cannot work when the ledger has declined the record. Measured verbatim
        # before the fix. So this control asserts all THREE properties, and the middle one is the
        # only one that was ever wrong.
        _step = REVIEW_STEPS[0]
        record.step_status = lambda ref, action="commit": {
            s: ("REFUSED" if s == _step else "SATISFIED") for s in REVIEW_STEPS}
        _why = [r for r in check_signals(["o/m..A"]) if r[0] == _step][0]
        for label, ok in [
                ("REFUSED blocks", not _why[1]),
                ("REFUSED does NOT say to re-run the gate",
                 "run the gate and let it record its own verdict" not in _why[2]),
                ("REFUSED names the RECORD, not the corpus",
                 "NOTHING has been established" in _why[2])]:
            print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
            bad += 0 if ok else 1
            total += 1
    finally:
        record.step_status = _real
        globals()["reviewable_changed"] = _real_changed

    # ⚠⚠ The migration detector, exercised on SYNTHETIC numstat rather than on history, so the
    # controls keep working after the commits they describe scroll out of any range. The three
    # shapes are taken from the 2026-08-26 audit: a real migration (Wall 191 -> 206), a real
    # unpaired deletion (DEL-1's SnapFrameChange), and a rewrite that must NOT be flagged.
    print("prose migration: shrank-unpaired detection (DEL-1)")
    _real_numstat = globals()["_numstat"]
    mig_cases = [
        ("migration: .md gained more than .lean lost",
         {"A.lean": (7, 191), "A.md": (206, 0)}, []),
        ("unpaired deletion is flagged",
         {"B.lean": (4, 37)}, [("B.lean", 33)]),
        ("a rewrite that adds as much as it cuts is not",
         {"C.lean": (40, 45)}, []),
        ("a sibling that CHANGED but did not GAIN is not enough",
         {"D.lean": (2, 60), "D.md": (0, 12)}, [("D.lean", 58)]),
        ("below the floor is ignored",
         {"E.lean": (1, 5)}, []),
        ("a .md shrinking on its own is not a .lean finding",
         {"F.md": (0, 90)}, []),
    ]
    try:
        for label, fake, want in mig_cases:
            globals()["_numstat"] = lambda ranges=None, _f=fake: dict(_f)
            got = prose_shrank_unpaired(["dummy"])
            ok = got == want
            print("  %-46s %s" % (label, "ok" if ok else "*** got %s, want %s ***" % (got, want)))
            bad += 0 if ok else 1
            total += 1
    finally:
        globals()["_numstat"] = _real_numstat

    # ⚠⚠ `_recurrence_note` HAD NO CONTROL AT ALL (`/rely` R3-O3): reverting its marker set
    # changed what reaches the push-time channel (2 shapes -> 1) while this suite printed PASS
    # either way. Both halves, on synthetic child output, so nothing here shells out.
    print("push-time recurrence advisory (R3-O3)")
    _real_run = subprocess.run

    class _FakeChild(object):
        def __init__(self, out, rc=0):
            self.stdout, self.returncode, self.stderr = out, rc, ""

    _both = ("  1. [SH-A] a shape — 4 row(s)  %s\n"
             "  2. [SH-B] another — 3 row(s)  ← DC-999 %s\n"
             % (selfheal.MARK_NO_ROW, selfheal.MARK_NAMES_NO_ROW))
    _rec_cases = [
        ("both UNCLASSED markers reach the channel", _FakeChild(_both), 2, None),
        ("an unreadable child is not a clean bill", _FakeChild("", 2), 0, "NOT a clean"),
    ]
    for label, child, want_rows, want_text in _rec_cases:
        try:
            subprocess.run = lambda *a, **k: child
            buf = io.StringIO()
            _real_stdout = sys.stdout
            try:
                sys.stdout = buf
                _recurrence_note()
            finally:
                sys.stdout = _real_stdout
        finally:
            subprocess.run = _real_run
        got = buf.getvalue()
        rows = len([l for l in got.splitlines() if "row(s)" in l])
        ok = rows == want_rows and (want_text is None or want_text in got)
        print("  %-46s %s" % (label, "ok" if ok else "*** got %d row(s) ***" % rows))
        bad += 0 if ok else 1
        total += 1

    # ⭐⭐ THE ACCEPT CONSULT — EVERY ROW OF THE RATCHET CONTROL TABLE, EXECUTED.
    # This is the half of `check_pdf_coupling` that can let a push through with a RED finding, and
    # `LEDGER_GATE_FIXTURE.md` names that as one of the two dangerous cases: "everything else fails
    # closed; those two are the paths that let a push through, so they are where a fail-open would
    # actually cost something."
    #
    # ⚠⚠ THE ROWS PIN BOTH DIRECTIONS, WHICH IS WHY THERE IS A POSITIVE ONE. Row 1 requires the
    # consult to ACCEPT and rows 2-8 require it to REFUSE, so a stub returning an empty set fails
    # row 1 and a stub returning every path fails the other seven. A one-directional suite over an
    # accept path is how a control layer stays green over a switched-off gate (`B5`).
    #
    # ⚠ THE FAKE HONOURS THE SERVER'S OWN FILTERS — both `step` and `subject_sha` — so a row cannot
    # pass merely because the double is more permissive than `find` is. It also refuses any tool but
    # `find`, so a consult that started asking a different question would go red here rather than
    # silently reading something else.
    print("pdf coupling: the accept consult (the ratchet)")
    _real_call = record._call
    _P, _B = "ZP-A_Illustrated_Companion.pdf", "a" * 40
    _SUBJ = [{"path": _P, "git_blob_id": _B}]
    _asked = []

    def _mkrec(step=PDF_COUPLING_PUSH_STEP, path=_P, blob=_B, how="signature", who="Tim"):
        # ⚠ `verdict` is "PASS" on EVERY row, including the ones that must be refused. That is not
        # laziness: a signed accept really is stored as "PASS" (mcpdev, from `_decided`), so if the
        # consult ever keyed on the verdict field instead of `decided.how`, all eight rows would
        # look identical to it and seven would go red. The fixture bakes in the thing that bites.
        return {"step": step, "verdict": "PASS",
                "decided": {"how": how, "who": who},
                "subjects": [{"path": path, "git_blob_id": blob}]}

    def _mkfake(records, answers=True):
        def _call(tool, args):
            if tool != "find":
                raise AssertionError("the consult asked %r, expected 'find'" % tool)
            _asked.append(args.get("step"))
            if not answers:
                return None                     # the ledger did not answer
            return {"ok": True, "records": [
                r for r in records
                if r["step"] == args.get("step")
                and any(s["git_blob_id"] == args.get("subject_sha") for s in r["subjects"])]}
        return _call

    def _raises(_tool, _args):
        raise RuntimeError("transport down")

    _accept_cases = [
        ("accepted FAIL at THESE bytes clears", _mkfake([_mkrec()]), _SUBJ, {_P}),
        ("accepted at DIFFERENT bytes does not", _mkfake([_mkrec(blob="b" * 40)]), _SUBJ, set()),
        ("no accept at all does not", _mkfake([]), _SUBJ, set()),
        ("accept for a DIFFERENT STEP does not", _mkfake([_mkrec(step="pdf_coupling")]), _SUBJ,
         set()),
        ("accept for a DIFFERENT PATH does not", _mkfake([_mkrec(path="ZP-B_Other.pdf")]), _SUBJ,
         set()),
        ("a MECHANICAL PASS does not clear", _mkfake([_mkrec(how="mechanical", who=None)]), _SUBJ,
         set()),
        ("an OVERRIDE does not clear (opposite signal)", _mkfake([_mkrec(how="override")]), _SUBJ,
         set()),
        ("a signature with no WHO does not clear", _mkfake([_mkrec(who=None)]), _SUBJ, set()),
        # ⚠⚠ None, NEVER set() — `R-ZERONULL`. "I could not ask" and "nobody accepted" must differ
        # in the VALUE, because the caller blocks on one and computes an owed list from the other.
        ("ledger unreachable is None, not empty", _mkfake([], answers=False), _SUBJ, None),
        ("a raising transport is None too", _raises, _SUBJ, None),
        ("an unkeyable subject is None too", _mkfake([_mkrec()]),
         [{"path": _P, "git_blob_id": ""}], None),
    ]
    for label, caller, subj, want in _accept_cases:
        try:
            record._call = caller
            got = pdf_coupling_accepts(subj)
        except Exception as e:                            # noqa: BLE001 — a raise IS a failure here
            got = "raised %r" % (e,)
        finally:
            record._call = _real_call
        ok = got == want
        print("  %-46s %s" % (label, "ok" if ok else "*** got %r, want %r ***" % (got, want)))
        bad += 0 if ok else 1
        total += 1

    # ⚠ AND IT MUST ASK ABOUT THE PUSH-DIFF STEP, NOT THE TREE ONE. The whole design turns on the
    # split, so a consult that quietly asked `pdf_coupling` would read the near-vacuous 40-of-40
    # PASS and clear this leg for ever — green on every row above, because those fakes answer
    # whatever step they are handed. The step name is the one thing the rows cannot pin themselves.
    _wrong = sorted({s for s in _asked if s != PDF_COUPLING_PUSH_STEP})
    _ok_step = bool(_asked) and not _wrong
    print("  %-46s %s" % ("the consult asks the PUSH-DIFF step",
                          "ok" if _ok_step else "*** asked %r ***" % (_wrong or "nothing",)))
    bad += 0 if _ok_step else 1
    total += 1

    # ⚠ THE REVIEW REPORT IS DERIVED FROM THE ADMISSION SET, AND THESE ROWS ARE WHAT HOLDS IT THERE.
    # The family is passed explicitly so a registry edit cannot move the fixture; the SET row uses a
    # step outside `REVIEW_STEPS` on purpose, because a step the hand-written pair already names would
    # appear in the report whether or not the derivation ran.
    print("review report: derived from %s, three states (R-ZERONULL)" % ADMITTED_ENV)
    _fam = ("adversary", "claim_review", "copy_editor", "editorial", "prior_art", "rely")
    _set = json.dumps({"state": "SET", "action": "push",
                       "admitted": ["adversary", "build", "copy_editor", "editorial", "guards"]})
    _adm_set = admitted_review_steps(_set, _fam)
    _txt_set = "\n".join(review_report_lines(_adm_set))
    _adm_unk = admitted_review_steps(None, _fam)
    _txt_unk = "\n".join(review_report_lines(_adm_unk))
    _adm_emp = admitted_review_steps(json.dumps({"state": "EMPTY", "action": "push", "admitted": []}),
                                     _fam)
    _rev_cases = [
        ("SET: every admitted review step is reported",
         _adm_set[0] == "SET" and all(re.search(r"^\s+%s\s" % s, _txt_set, re.M)
                                      for s in ("adversary", "copy_editor", "editorial"))),
        ("SET: a non-review admitted step is not",
         not re.search(r"^\s+(build|guards)\s", _txt_set, re.M)),
        ("UNKNOWN (absent) is None, never an empty list", _adm_unk[1] is None),
        ("UNKNOWN renders UNKNOWN + the fallback pair",
         "UNKNOWN" in _txt_unk and "FALLBACK" in _txt_unk
         and all(s in _txt_unk for s in REVIEW_STEPS)),
        ("unparseable JSON is UNKNOWN",
         admitted_review_steps("{not json", _fam)[1] is None),
        ("EMPTY differs from UNKNOWN and from SET-with-none",
         _adm_emp[:2] == ("EMPTY", ()) and _adm_emp[1] != _adm_unk[1]
         and admitted_review_steps(json.dumps({"state": "SET", "action": "push",
                                               "admitted": ["build"]}), _fam)[:2] == ("SET", ())),
    ]
    # The manifest's signals row is a LITERAL (see the comment on it), so it is held to the tuple the
    # leg iterates here: every `REVIEW_STEPS` name appears in it, and no other registry review step.
    import ast as _ast
    _sig = None
    try:
        for _n in _ast.walk(_ast.parse(io.open(__file__, encoding="utf-8").read())):
            if isinstance(_n, _ast.FunctionDef) and _n.name == "cmd_prepush":
                for _c in _ast.walk(_n):
                    if (isinstance(_c, _ast.Call) and isinstance(_c.func, _ast.Attribute)
                            and _c.func.attr == "plan" and _c.args):
                        _sig = [r[2] for r in _ast.literal_eval(_c.args[0]) if r[0] == "signals"]
    except (OSError, SyntaxError, ValueError):
        _sig = None
    _rev_cases.append(
        ("manifest signals row names exactly REVIEW_STEPS",
         bool(_sig) and len(_sig) == 1
         and set(re.findall(r"[a-z_]+", _sig[0])) & set(_fam) == set(REVIEW_STEPS)))

    # ⚠⚠ ENFORCED vs ADMITTED (`/rely` 2026-10-03, F1-F4). The admission set is gitRobot's statement,
    # never this hook's requirement list, so the enforced list must print in every state, and a step
    # with a BLOCK leg here must never be labelled as having none.
    _enf = [s for s, _l in ENFORCED_REVIEW_LEGS]
    _adm_none = admitted_review_steps(json.dumps({"state": "SET", "action": "push",
                                                  "admitted": ["build"]}), _fam)
    _adm_pa = admitted_review_steps(json.dumps({"state": "SET", "action": "push",
                                                "admitted": ["copy_editor", "prior_art"]}), _fam)
    _enf_line = [all(s in (review_report_lines(a) or [""])[0] for s in _enf)
                 and (review_report_lines(a) or [""])[0].startswith("  enforced here:")
                 for a in (_adm_set, _adm_none, _adm_emp, _adm_unk)]
    _txt_pa = review_report_lines(_adm_pa)
    _rev_cases.append(("every state prints the enforced list first", all(_enf_line)))
    _rev_cases.append(
        ("no enforced step labelled 'no BLOCK leg'",
         _adm_pa[1] == ("copy_editor", "prior_art")
         and not [l for l in _txt_pa if re.match(r"^\s+(%s)\s.*no BLOCK leg" % "|".join(_enf), l)]
         and [l for l in _txt_pa if re.match(r"^\s+copy_editor\s.*no BLOCK leg", l)] != []))
    # F3: a crafted env value and a mis-shaped registry are UNKNOWN / None, never a raise.
    _deep = "[" * 16000 + "]" * 16000
    try:
        _ok_deep = admitted_review_steps(_deep, _fam)[:2] == ("UNKNOWN", None)
    except BaseException:
        _ok_deep = False
    _rev_cases.append(("deep-nested env value is UNKNOWN, never raises", _ok_deep))
    _saved_env = os.environ.get(ADMITTED_ENV)
    try:
        os.environ[ADMITTED_ENV] = _deep
        try:
            _ok_rep = any("UNKNOWN" in l for l in review_report())
        except BaseException:
            _ok_rep = False
    finally:
        if _saved_env is None:
            os.environ.pop(ADMITTED_ENV, None)
        else:
            os.environ[ADMITTED_ENV] = _saved_env
    _rev_cases.append(("review_report() under a deep env value -> UNKNOWN", _ok_rep))
    # M9: an admission set for another action is not a push set.
    _rev_cases.append(
        ("a commit-action set is UNKNOWN, not SET",
         admitted_review_steps(json.dumps({"state": "SET", "action": "commit",
                                           "admitted": ["editorial"]}), _fam)[:2]
         == ("UNKNOWN", None)))
    # M10: a mis-shaped registry is unreadable (None), never "no review types" (()).
    import tempfile as _tf
    _reg_ok = []
    for _body in ('{"types": []}', "[1, 2]", '{"types": {"x": {"family": "review"}}}'):
        _fd, _rp = _tf.mkstemp(suffix=".json")
        try:
            with io.open(_fd, "w", encoding="utf-8") as _fh:
                _fh.write(_body)
            try:
                _reg_ok.append(registry_review_family(_rp))
            except BaseException as _e:
                _reg_ok.append("raised %s" % type(_e).__name__)
        finally:
            os.remove(_rp)
    _rev_cases.append(("mis-shaped registry is None; a good one is a tuple",
                       _reg_ok == [None, None, ("x",)]))
    # M11: the signals leg's `need` must not move under a forged admission set (behaviour), and no
    # function outside the report reads the env var or its parser (shape) — so no BLOCK leg can.
    _need_rows = []
    try:
        for _forge in (None, json.dumps({"state": "EMPTY", "action": "push", "admitted": []}),
                       json.dumps({"state": "SET", "action": "push", "admitted": ["build"]})):
            if _forge is None:
                os.environ.pop(ADMITTED_ENV, None)
            else:
                os.environ[ADMITTED_ENV] = _forge
            _need_rows.append(tuple(signal_need(_s, _f) for _s in _enf + ["prior_art"]
                                    for _f in (True, False)))
    finally:
        if _saved_env is None:
            os.environ.pop(ADMITTED_ENV, None)
        else:
            os.environ[ADMITTED_ENV] = _saved_env
    _rev_cases.append(("signals need unchanged under forged EMPTY / SET",
                       len(set(_need_rows)) == 1 and len(_need_rows) == 3))
    _allowed = {"admitted_review_steps", "_classify_admission", "review_report_lines",
                "review_report", "selftest"}
    _tainted = {"admitted_review_steps", "_classify_admission", "review_report_lines", ADMITTED_ENV,
                "ADMITTED_ENV"}
    _readers, _site_ok = None, False
    try:
        _tree = _ast.parse(io.open(__file__, encoding="utf-8").read())
        _readers = set()
        for _f in _ast.walk(_tree):
            if not isinstance(_f, _ast.FunctionDef):
                continue
            for _c in _ast.walk(_f):
                _id = (_c.id if isinstance(_c, _ast.Name) else
                       _c.value if isinstance(_c, _ast.Constant) and isinstance(_c.value, str) else
                       _c.attr if isinstance(_c, _ast.Attribute) else None)
                if _id in _tainted:
                    _readers.add(_f.name)
            if _f.name == "cmd_prepush":
                # M6: the report is printed by `for _line in review_report(): print(_line)`, and
                # `review_report` appears nowhere else in the hook.
                _uses = [_c for _c in _ast.walk(_f) if isinstance(_c, _ast.Name)
                         and _c.id == "review_report"]
                _loops = [_c for _c in _ast.walk(_f) if isinstance(_c, _ast.For)
                          and isinstance(_c.iter, _ast.Call)
                          and isinstance(_c.iter.func, _ast.Name)
                          and _c.iter.func.id == "review_report"
                          and len(_c.body) == 1 and isinstance(_c.body[0], _ast.Expr)
                          and isinstance(_c.body[0].value, _ast.Call)
                          and getattr(_c.body[0].value.func, "id", None) == "print"]
                _site_ok = len(_uses) == 1 and len(_loops) == 1
    except (OSError, SyntaxError, ValueError):
        _readers = None
    _rev_cases.append(("only the report reads %s" % ADMITTED_ENV,
                       _readers is not None and _readers <= _allowed))
    _rev_cases.append(("cmd_prepush prints review_report() once", _site_ok))
    # The report's attrib step IS the step the attrib leg asks the ledger about.
    _attrib_ok = False
    try:
        for _f in _ast.walk(_tree):
            if isinstance(_f, _ast.FunctionDef) and _f.name == "check_prior_art_attribution":
                _attrib_ok = any(isinstance(_c, _ast.Call) and getattr(_c.func, "attr", None)
                                 == "owing_paths" and _c.args and isinstance(_c.args[0], _ast.Name)
                                 and _c.args[0].id == "ATTRIB_STEP" for _c in _ast.walk(_f))
    except NameError:
        _attrib_ok = False
    _rev_cases.append(("attrib leg asks the ledger about ATTRIB_STEP",
                       _attrib_ok and (ATTRIB_STEP, "prior-art attrib") in ENFORCED_REVIEW_LEGS))
    for label, ok in _rev_cases:
        print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
        bad += 0 if ok else 1
        total += 1

    _b, _t = _g1_controls()
    bad += _b
    total += _t

    _b, _t = _basis_controls()
    bad += _b
    total += _t

    print("\nselftest: %s (%d/%d control(s))"
          % ("PASS" if not bad else "FAIL", total - bad, total))
    return 1 if bad else 0


if __name__ == "__main__":
    a = sys.argv[1:]
    if a and a[0] == "selftest":
        sys.exit(selftest())
    if not a:
        print(__doc__)
    elif a[0] == "start":
        cmd_start(a[a.index("--bucket") + 1] if "--bucket" in a else die("need --bucket"))
    elif a[0] == "stage":
        note = a[a.index("--note") + 1] if "--note" in a else None
        cmd_stage(a[1], note)
    elif a[0] == "review":
        # ⚠ REFUSED, NOT SILENTLY MAPPED TO `status`. A review is recorded in the LEDGER by the gate
        # that ran it (`record.py --step <step>`); a claim in `batch_state.json` discharges nothing.
        die("`batch.py review` records nothing: a review's verdict goes to the ledger "
            "(`record.py --step <step>`), and `/rely` is owed at TAG — "
            "coverage_gap(step='rely', action='tag')")
    elif a[0] == "decls":
        cmd_decls("--baseline" in a, "--block" in a, "--prune" in a)
    elif a[0] == "precommit":
        cmd_precommit()
    elif a[0] == "prepush" and "--ranges" in a:
        # Passing the flag puts us in RANGE mode even when the list is empty — an empty push scope
        # is a real answer, and must never silently mean "look at the working tree instead".
        cmd_prepush([r for r in a[a.index("--ranges") + 1].split(",") if r.strip()])
    elif a[0] == "prepush":
        cmd_prepush()
    elif a[0] == "close":
        cmd_close()
    else:
        cmd_status()
