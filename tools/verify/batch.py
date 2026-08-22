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

# Everything whose change must route to `/rely`. WIDER than the gating set on purpose: a defect in
# `hooks.py`, `vendored.py` or `batch.py` itself is silent and multiplies through every verdict, and
# until 2026-08-10 none of the three routed anywhere — the git rule cannot see them (`.claude-local`
# is gitignored) and the hash rule covered only the five checkers (F8).
CHECKERS = GATING_CHECKERS + ["check_poles.py", "vendored.py", "vendored_files.txt",
                              "hooks.py", "batch.py", "ship.py", "report.py", "gate_round.py",
                              # ⚠ `agent_gate.py` IS HERE THOUGH IT ONLY WARNS. Its registry of
                              # `expected_failure` declarations is what the interpretation layer
                              # judges against, so editing one silently changes every verdict it
                              # produces — the same argument as the baselines below. Omitting it
                              # would be `RLY17-2`: routed to /rely, absent from CHECKERS.
                              "agent_gate.py",
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
                              "scan_pdfs.py", "gatelock.py", "selfheal.py",
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


# ⚠⚠ THE PROSE UNDER THE ROUTED PREFIXES IS HASHED BY GLOB, NOT BY NAME — and the glob is the point.
# `tools/verify/**.md` and `tools/process/**.md` are EXEMPT from the editorial and adversary gates and
# routed to `/rely` instead. That re-route is the entire warrant for the exemption, and `/rely` can
# only discharge what the hash leg can see, so an unhashed `.md` under either prefix is exempt from
# every prose gate AND undischargeable — reviewed by nothing, exactly the round-1 signature.
#
# Measured 2026-08-21: `tools/process/` was added to `EXEMPT_PREFIXES` and `ROUTING` and NOT here, so
# `batch.py`'s own `_unhashed` leg reported 8 routed files it could not see. It failed CLOSED and
# named the fix, which is why this was ordinary rather than blocking — the enumerator working, one
# round after the previous entry was added the same way.
#
# ⚠ A LIST OF NAMES WOULD BE THE WRONG SHAPE. Naming the 8 files closes 8 holes; the 9th arrives with
# the next routed document and nothing says so. This file's own history is that argument — the four
# baselines, then a fifth, then a sixth. A glob over the routed prefix cannot fall behind the
# directory it globs. Sorted so the signal's line order is stable across machines.
def _routed_docs():
    out = []
    for rel in ("tools/verify", "tools/process"):
        d = os.path.join(REPO, *rel.split("/"))
        if os.path.isdir(d):
            out += ["%s/%s" % (rel, n) for n in os.listdir(d) if n.lower().endswith(".md")]
    return sorted(out)


CHECKERS = CHECKERS + _routed_docs()


# ⚠⚠ THE THREE KINDS IN `CHECKERS` ARE NOT ONE OBLIGATION, AND UNTIL 2026-08-21 THEY SHARED ONE ROW.
# The list mixes executable LOGIC (`.py`), exemption SWITCHES (the baselines, whitelists and pins) and
# routed PROSE (`.md`, via `_routed_docs()` above), and `check_routing` reported "N checker(s) changed"
# over the union. That single count is what deadlocked the routed set: a dated-figure correction in
# `tools/process/claim-revalidation.md` — mechanically verified, zero judgement, demanded by another
# blocking checker — re-armed exactly the same gate a rewritten `check_prose.py` would.
#
# ⚠ DERIVED FROM THE EXTENSION, NOT HAND-LISTED, for the reason `_routed_docs()` already gives one
# comment up: naming today's members closes today's holes and the next arrival is invisible. A new
# `.py` is logic, a new `.txt`/`.json` is a switch, a new routed `.md` is prose. Nobody has to
# remember, and the partition cannot fall behind the list it partitions.
#
# ⚠⚠ ONLY THE PROSE LEG MAY EVER BE DOWNGRADED (CLAUDE.md rung 5, *split at the leg, never at the
# check*). Logic and switches are FAIL-OPEN surfaces — one appended line to `pov_baseline.txt` took a
# planted violation from exit 1 to exit 0 with `checker_hashes()` unmoved — and rung 5 is explicit
# that a fail-open never downgrades, however many rounds it costs. Prose under a routed prefix is an
# ENUMERATION obligation whose own repairs re-arm it, which is the shape that downgrades.
def _leg_of(name):
    n = name.lower()
    if n.endswith(".md"):
        return "docs"
    if n.endswith(".py"):
        return "logic"
    return "switch"


# Why each leg matters, kept beside the partition so a row can never state the wrong reason for the
# kind it is reporting. A block whose stated reason is wrong is how bypass habits start.
_LEG_WHY = {
    "logic": "a fail-open here is silent and multiplies through every downstream verdict",
    "switch": "one line in a baseline or whitelist silences one site permanently, with every "
              "control still green",
    "docs": "prose under a routed prefix is exempt from editorial and adversary, so /rely is the "
            "only gate covering it",
}
_LEG_NOUN = {"logic": "checker(s)", "switch": "exemption switch(es)", "docs": "routed document(s)"}

# ⚠⚠ THE ONE DEFINITION OF ENFORCEMENT MODE. `check_routing` reads this table and `guards.py` asserts
# on it, so there is no second copy to drift and no literal at a call site for a control to be blind
# to. Before 2026-08-21 the mode was the literal `bad += 0 if ran else 1` in `cmd_prepush`, and a
# probe measured `guards.py` printing `ok` over a router that had stopped blocking — not because the
# warrant was weak but because there was nothing for it to read.
#
# ⚠ `logic` and `switch` are FAIL-OPEN surfaces and MUST stay True, whatever it costs in rounds.
# CLAUDE.md rung 5 is explicit: non-convergence in an ENUMERATION is a fact about the enumeration; a
# fail-open is a fact about the work. Flipping either of these to False silently un-prices the
# editorial/adversary exemption that `tools/verify/**` and `tools/process/**` hold.
#
# ⚠⚠ `docs` IS FALSE BY DECISION, 2026-08-21, AND THE EVIDENCE IS NAMED BECAUSE RUNG 5 DEMANDS IT.
# Four `/rely` rounds on this layer ran 10 → 4 → 6 → 9 findings and never quiesced, because each
# round reviews code written in response to the last; then the loop deadlocked outright, when a
# one-line mechanically-verified fix to `tools/process/claim-revalidation.md` re-staled the signature
# and blocked the push it was made to unblock. That is an ENUMERATION gate whose own repairs re-arm
# it, which is the shape rung 5 downgrades. *"This keeps blocking"* would not have been evidence;
# `10 → 4 → 6 → 9` and a measured deadlock are.
_LEG_BLOCKING = {"logic": True, "switch": True, "docs": False}


def routing_bad(rows):
    """How many routing rows actually BLOCK — the one place the enforcement decision is made.

    ⚠ IT IS A FUNCTION SO A CONTROL CAN CALL IT. As a literal (`bad += 0 if ran else 1`) the decision
    was unreachable by any check, which is why `guards.py` printed `ok` over a neutered router on
    2026-08-21. A named function can be exercised directly AND its call site can be asserted to still
    exist — gutting this to `bad += 0` removes the call, and `guards.py` fires on the absence."""
    return sum(0 if (ran or not blocking) else 1 for _a, ran, _w, blocking in rows)
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

# Preconditions that route to a DEEPER review than the three prose gates. Keyed to what changed,
# because the worst findings of 2026-08-09 were all in the VERIFICATION LAYER rather than the
# corpus - a defect there is silent and multiplies through every downstream verdict.
# ⭐ The 2026-08-15 move makes this rule WORK RATHER THAN NEARLY WORK. While the bundle lived in
# gitignored `.claude-local`, a checker edit was invisible to `git diff` and this pattern could only
# fire off the working tree; the hash rule was carrying the whole load. Tracked under `tools/verify/`
# a checker change is an ordinary tracked diff, so git sees it, CI sees it, and a reviewer sees it.
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
    (re.compile(r"^tools/verify/", re.I),
     "/rely", "a checker, hook, or exemption switch changed - its first run produced CHK-2 and "
              "CHK-3, both checker bugs, so this is the measured persona for the verification layer"),
    # `tools/process/` is CLAUDE.md's body — the argument behind each routed rule, split out so the
    # injected file can be a routing table rather than the payload. Same pairing as the prefix above:
    # it is exempt in EXEMPT_PREFIXES and routed here, and the two MUST be edited together. Added
    # 2026-08-20 with its first two files; the exemption is DECLARED in CLAUDE.md's header, never
    # inferred from "it is operating instructions" — that inference is what put `.claude/commands/`
    # in the exempt tuple for an hour before it was removed.
    (re.compile(r"^tools/process/", re.I),
     "/rely", "CLAUDE.md's routed body changed - a rule whose trigger or pointer rots stops firing "
              "silently, which is the failure mode the split exists to remove"),
    (re.compile(r"^\.github/workflows/", re.I),
     "/rely", "CI workflow changed - a fail-open here publishes a false verification claim"),
]

# ⚠ THIS FILE'S OWN COPY OMITTED `line_buffering=True` — one of two out of eight that did, and this
# is the orchestrator, the entry point whose manifest ordering `report.py:34` was written to fix.
# Shared now, so a copy cannot be half right.
common.utf8_stdout()


def sh(*args, cwd=REPO):
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return r.returncode, (r.stdout or "") + (r.stderr or "")


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


def print_axioms_on_disk():
    """Short names carrying a `#print axioms` anywhere in the tree, collected in ONE pass.

    The per-declaration `git grep` this replaces cost one subprocess per name, which is fine for a
    handful and impossible for the 1847 declarations on disk - and it could only see TRACKED files,
    so a purity line in a new file read as missing."""
    got = set()
    for fp in lean_files_on_disk():
        src = io.open(fp, encoding="utf-8", errors="replace").read()
        # ⚠ STRIP COMMENTS FIRST. Without this a commented-out `-- #print axioms X` satisfied the
        # purity obligation for X — the requirement discharged by a line the elaborator never sees.
        # `decls_in` ten lines up strips comments and documents exactly why; this did not, so the
        # two halves of the same check disagreed about what counts as code (RLY2-9).
        src = strip_comments(src)
        got |= {m.group(1).split(".")[-1] for m in PRINT_AX_PAT.finditer(src)}
    return got


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
    have = print_axioms_on_disk()
    missing = [nm(d) for d in decls if nm(d) not in have]
    return (not missing), ("purity entries present" if not missing
                           else "no `#print axioms` for: %s" % ", ".join(missing))


def check_ssot(decls):
    if decls is None:
        return False, "NO DECLARATION BASELINE — run `batch.py decls --baseline` (failing closed)"
    p = os.path.join(REPO, "ssot.json")
    if not os.path.exists(p):
        return True, "no ssot.json in tree"
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
        rc, out = sh(sys.executable, p, "--block")
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


def check_routing(state, ranges=None):
    """Which deeper reviews this change has TRIGGERED, and whether they were recorded as run.

    The three prose gates ask: is the wording right, is the claim over-stated, is it novel. NONE of
    them asks whether a CHECK ACTUALLY CHECKS WHAT IT SAYS. That question is `/rely`'s, and its only
    run to date returned two checker bugs. So a change touching the verification layer routes there
    - and the routing is a precondition here rather than a line in a document, because seven
    conventions of that shape have already leaked.

    ⭐ CHECKER CHANGES USED TO BE INVISIBLE TO GIT, AND ARE NOT ANY MORE. While the bundle lived in
    gitignored `.claude-local/`, `git diff` never reported a modified checker, so a routing rule
    keyed to the path fired never and this hash comparison carried the entire load. Since the
    2026-08-15 move to tracked `tools/verify/` the ROUTING pattern above fires off an ordinary diff.

    The hash rule is DELIBERATELY KEPT as a second layer, not retired with the problem that
    motivated it: it catches an uncommitted working-tree edit, which a diff against the pushed range
    does not see, and it records WHICH REVIEWED VERSION each checker was last cleared at rather than
    merely that the file changed. Two routes to one property, which is this bundle's own rule."""
    rows = []
    # (a) the verification layer, by hash against the last /rely signal
    sig = os.path.join(PRIV, "rely_cleared.txt")
    reviewed = {}
    if os.path.exists(sig):
        for line in io.open(sig, encoding="utf-8").read().splitlines()[1:]:
            parts = line.split()
            if len(parts) == 2:
                reviewed[parts[1]] = parts[0]
    now = checker_hashes()
    moved = [c for c, h in now.items() if reviewed.get(c) != h]
    # ⚠ NOT `"/rely" in state["reviews"]`. That let a CLAIM in the unhashed `batch_state.json`
    # discharge a HASH obligation: measured `prepush PASS`, exit 0, with seven checkers changed
    # since /rely last signed them — and the warning text still printing beside the word `ok`.
    # `batch.py review /rely` reached it too, attaching no evidence. The hash leg asks one
    # question — does the SIGNAL cover the bytes on disk — and only the signal can answer it.
    # Anything else is self-certification wearing a state file (/rely pass 8, REL8-2).
    #
    # ⚠⚠ ONE ROW PER LEG, AND EACH ROW CARRIES ITS OWN ENFORCEMENT MODE AS DATA. That fourth field is
    # the point, not bookkeeping: the 2026-08-21 warrant probe measured `guards.py` printing `ok`
    # while the router no longer blocked, and the reason it could not do better is that enforcement
    # mode existed ONLY as a literal at the call site (`bad += 0 if ran else 1`) and was therefore
    # unreadable by any control. `CLAUDE.md` names that shape: *enforcement mode is not part of the
    # pattern*. Putting it in the row makes it testable — see the `guards.py` route.
    for leg in ("logic", "switch", "docs"):
        m = sorted(c for c in moved if _leg_of(c) == leg)
        if m:
            rows.append(("/rely", False,
                         "[%s] %d %s changed since /rely last signed them: %s — %s"
                         % (leg, len(m), _LEG_NOUN[leg], ", ".join(m[:3]), _LEG_WHY[leg]),
                         _LEG_BLOCKING[leg]))
        elif not _LEG_BLOCKING[leg]:
            # ⚠⚠ A DOWNGRADED LEG PRINTS ITS COUNT EVEN AT ZERO, AND THAT IS THE PRICE OF THE
            # DOWNGRADE, NOT DECORATION. A warning nobody reads is strictly worse than a block,
            # because it manufactures the appearance of coverage — `RLY25-1` exactly: a report
            # publishing `pass` for a property it no longer checks. Printing the count on every run,
            # blocked or clear, is how rubber-stamping shows up as a rising number instead of going
            # quiet. Same move as `check_poles.py`'s suppression counter.
            rows.append(("/rely", True,
                         "[%s] 0 %s stale — WARN-only leg, count printed every run so a rising "
                         "number is visible rather than silent" % (leg, _LEG_NOUN[leg]),
                         False))
    # (b) tracked files, by git — RANGE-AWARE. It read the working tree, so a `.github/workflows/`
    # change routed to `/rely` while uncommitted and produced ZERO rows once committed: the leg
    # fired never at push time, which is the only time it matters (measured, /rely pass 4).
    files = [f.replace("\\", "/") for f in changed_files(ranges)]
    done = set(state.get("reviews", []))
    # ⚠⚠ WITHOUT THIS, A VERIFICATION-LAYER PUSH OUTSIDE A BATCH HAD NO DISCHARGE AT ALL, AND THE
    # DEBASELINING WORKFLOW COULD NOT TERMINATE (`BATCH-1`, measured 2026-08-17 end to end).
    # `batch.py review /rely` is the only writer of `state["reviews"]` and it opens with
    # `load() or die("no batch in progress")`. So with no batch this leg was unsatisfiable — and
    # `close` REQUIRES a baseline prune, whose output is itself a `tools/verify/` file, so finishing
    # a batch produced a change that this leg then blocked, with the state already deleted by the
    # `close` that demanded it. Re-running the batch did not escape: the next `close` wanted another
    # shrink, hence another verification-layer change.
    #
    # The signature is the STRONGER evidence, which is why this is safe: leg (a) above still demands
    # a `rely_cleared.txt` covering the CURRENT bytes of every checker, so a real `/rely` pass is
    # still forced. What is dropped is only the bookkeeping duplicate that a batch happens to carry.
    # ⚠ Deliberately narrow: `/rely` ONLY, no batch ONLY, and only when leg (a) is clean (`moved`
    # empty). If the hashes have drifted, `moved` is non-empty and this does nothing.
    # ⚠ THE DISCHARGE MUST REQUIRE THAT EVERY ROUTED FILE IS ACTUALLY HASHED. `moved` is computed
    # only over `CHECKERS`, so a verification-layer file OUTSIDE that list never appears in it - and
    # replacing `check_release_ready.py` with `sys.exit(0)` produced `prepush PASS`, exit 0, with
    # the manifest printing "routing BLOCK - /rely has signed ..." directly above "/rely  ok"
    # (measured end to end, /rely pass 4, RLY16-2). Adding four names would close those four; this
    # closes the property, which is `CHECKERS`' own stated rule: if it can stop a push, it is hashed.
    _routed = [f for f in files
               if any(pat.match(f) for pat, agent, _w in ROUTING if agent == "/rely")]
    # ⚠⚠ COMPARE PATHS, NOT BASENAMES. `now` is keyed on bare filenames and each key resolves
    # through `_checker_path` to exactly ONE location, so a basename test is a NAME lookup wearing a
    # path lookup's clothes. Measured (RLY17-1): a push whose entire content was a new
    # `tools/verify/sub/check_prose.py` containing `sys.exit(0)` returned `prepush PASS`, exit 0 --
    # the basename was a key, so the guard called it covered, while the only file ever hashed was
    # `tools/verify/check_prose.py`. `/rely` is the ONLY gate covering a `.py` under `tools/verify/`,
    # so nothing reviewed it at all. A basename collision in a subdirectory is a MISS.
    _hashed_paths = {os.path.relpath(_checker_path(c), REPO).replace("\\", "/") for c in now}
    _unhashed = sorted(f for f in _routed if f not in _hashed_paths)
    # ⚠⚠ THE TWO LEGS DISAGREE ABOUT WHICH BYTES ARE BEING PUSHED, AND THE DISCHARGE FOLLOWED THE
    # WRONG ONE. Leg (a) `moved` hashes the files ON DISK; leg (b) `_routed` reads the PUSHED RANGE.
    # When the pushed ref is not the checkout those are different, and `prepush` returned PASS on a
    # CLEAN tree for a range that adds unreviewed prose to a routed file — the row naming the file
    # and clearing it in the same breath (measured end to end in a detached worktree, /rely round 2).
    #
    # It needs no dirty tree and no unusual command: `git push HEAD~2:branch`, pushing one branch
    # while another is checked out, or any worktree. CLAUDE.md already names *"push a subset to dodge
    # a signal"* as a known move; this made that move SUCCEED. Same shape as `REL-1`, which fixed the
    # leg and left the discharge reading the other one.
    #
    # The fix asks leg (a)'s question about leg (b)'s bytes: for every routed file in the RANGE,
    # does the signal cover the content AT THE RANGE TIP? Hashing a git object is correct precisely
    # here — the pushed content IS a git value, and the "hash the file on disk" rule governs what a
    # REVIEWER signs, not what a push contains.
    _stale_at_tip = []
    if ranges and _routed and not _unhashed:
        for f in _routed:
            key = next((c for c in now
                        if os.path.relpath(_checker_path(c), REPO).replace("\\", "/") == f), None)
            if key is None:
                continue                      # already reported by _unhashed
            for tip in _range_tips(ranges):
                # ⚠⚠ ABSENT AT THE TIP IS `<ABSENT>`, NOT `continue`. Skipping it meant a push that
                # DELETES a gating checker cleared: measured (/rely round 3), a range removing
                # `tools/verify/check_prose.py` from a checkout that still had it returned exit 0
                # with `/rely ok ... — e.g. tools/verify/check_prose.py` — the row NAMING the
                # deleted checker in the same breath as clearing it. The asymmetry was exact: the
                # same deletion on disk hits `checker_hashes()`'s `<ABSENT>` sentinel and blocks.
                # The sentinel already existed for precisely this reason one leg over; this leg
                # simply has to use it, so deleting a gate stays louder than editing one.
                h = _blob_hash(tip, f) or "<ABSENT>"
                if reviewed.get(key) != h:
                    _stale_at_tip.append(f)
                    break
    # ⚠⚠ THIS LEG IS THE SAME OBLIGATION MEASURED AGAINST DIFFERENT BYTES, SO IT TAKES THE SAME LEG
    # SPLIT. `moved` asks whether the signal covers the files on DISK; this asks whether it covers
    # them at the PUSHED TIP. Leaving it whole while downgrading `moved` would have defeated the
    # downgrade entirely — a docs-only push would clear the hash leg and block here instead, with the
    # deadlock intact and a new place to look for it. Found by tracing the docs-only path rather than
    # by flipping the flag and assuming.
    for _blocking in (True, False):
        s = sorted({f for f in _stale_at_tip
                    if _LEG_BLOCKING[_leg_of(f)] is _blocking})
        if s:
            rows.append(("/rely", False,
                         "[%s] %d routed file(s) differ at the PUSHED TIP from what /rely signed, "
                         "even though the working tree matches: %s — the push carries bytes nobody "
                         "reviewed" % ("blocking" if _blocking else "warn", len(s), ", ".join(s[:3])),
                         _blocking))
    # ⚠ THE AUTO-DISCHARGE COUNTS ONLY THE BLOCKING LEGS. It gates the git leg below, so leaving it
    # keyed to the whole of `moved` would have kept a docs-only change blocking through a THIRD code
    # path while both hash rows read WARN — the downgrade visibly applied and factually undone.
    _moved_blocking = [c for c in moved if _LEG_BLOCKING[_leg_of(c)]]
    _tip_blocking = [f for f in _stale_at_tip if _LEG_BLOCKING[_leg_of(f)]]
    if not state and not _moved_blocking and not _unhashed and not _tip_blocking:
        done.add("/rely")
    elif _unhashed and not moved:
        rows.append(("/rely", False,
                     "%d routed file(s) are NOT hashed by CHECKERS, so the hash leg cannot see them "
                     "and the auto-discharge is unsafe: %s — add the name to CHECKERS and re-sign "
                     "(that is the fix, not a workaround)"
                     % (len(_unhashed), ", ".join(_unhashed[:3])),
                     True))
    # ⚠⚠ THE GIT LEG TAKES THE LEG SPLIT TOO, AND MISSING THIS WOULD HAVE LEFT THE DEADLOCK ALIVE
    # INSIDE A BATCH. The auto-discharge above is guarded by `not state`, so during a batch it never
    # fires and this leg decides alone — meaning a docs-only edit would still have BLOCKED, in the
    # one mode used for exactly the multi-site prose work the downgrade exists to unblock. Found by
    # reading the final manifest rather than by a test, which is why it is written down.
    # ⚠ FAILS CLOSED ON A MIXED PUSH: blocking if ANY hit is logic or a switch, WARN only when every
    # hit under the prefix is routed prose. An unknown extension resolves to `switch`, so a new kind
    # of file blocks until someone classifies it deliberately.
    for pat, agent, why in ROUTING:
        hits = [f for f in files if pat.match(f)]
        if hits:
            blocking = any(_LEG_BLOCKING[_leg_of(f)] for f in hits)
            rows.append((agent, agent in done,
                         "%s — e.g. %s%s" % (why, hits[0],
                                             "" if blocking else "  [routed prose only — WARN]"),
                         blocking))
    return rows


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
            rc, out = sh("git", "diff", "--name-only", "--diff-filter=d", r)
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
    for pdf in pdfs:
        base = os.path.basename(pdf)
        hit = False
        for s in scripts:
            try:
                src = io.open(os.path.join(REPO, s), encoding="utf-8", errors="replace").read()
            except OSError:
                continue
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
            unpaired.append(base)
    if not unpaired:
        return True, "%d PDF(s), each paired with the script naming it (%s)" % (
            len(pdfs), ", ".join(scripts[:3]))
    return False, ("%d of %d changed PDF(s) have no build script IN THIS PUSH that names them "
                   "(%s) — a DOI freezes the PDF permanently, and the build script is the only "
                   "reviewable surface it has. Mirror the producing script per CLAUDE.md. "
                   "Two build scripts do not name their output literal; if this is one, say so."
                   % (len(unpaired), len(pdfs), ", ".join(unpaired[:3])))


def check_trigger5(ranges=None):
    """Prior-art trigger 5: a new `.lean` file, or >=50 inserted `.lean` lines.

    Range-aware for the same reason as `changed_files` (REL-1): computed against the working tree
    it reads 0 insertions once committed, so the prior-art requirement silently switched off at
    exactly the moment of pushing."""
    if ranges is not None:
        ins, newfile = 0, False
        for r in ranges:
            rc, out = sh("git", "diff", "--numstat", r, "--", "*.lean")
            # ⚠ A git error must never read as "no insertions". Unfixed, a bogus range returned
            # (False, 0, False) — i.e. PRIOR-ART NOT REQUIRED — which is a fail-open on the one
            # trigger that cannot be recovered later.
            if rc != 0:
                die("git could not resolve range %r for trigger 5 — refusing to report a scope "
                    "it could not read:\n%s" % (r, out))
            ins += sum(int(l.split("\t")[0]) for l in out.splitlines()
                       if l.split("\t")[0].isdigit())
            rc2, st = sh("git", "diff", "--name-status", r, "--", "*.lean")
            if rc2 != 0:
                die("git could not resolve range %r for trigger 5:\n%s" % (r, st))
            newfile = newfile or any(l.startswith("A") for l in st.splitlines())
        return (ins >= 50 or newfile), ins, newfile
    _rc, out = sh("git", "diff", "--numstat", "--", "*.lean")
    ins = sum(int(l.split("\t")[0]) for l in out.splitlines() if l.split("\t")[0].isdigit())
    _rc2, untracked = sh("git", "ls-files", "--others", "--exclude-standard", "--", "*.lean")
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
#   2. THE LAYER IS REVIEWED, BY THE RIGHT GATE, AND THAT GATE IS ENFORCED. `/rely` is the measured
#      persona for the verification layer, `ROUTING` above fires on exactly this prefix, and the
#      routing check BLOCKS at push. So a checker change is not unreviewed - it is routed away from
#      two prose gates that cannot judge it and toward the one that can. If the `/rely` routing is
#      ever weakened, THIS exemption becomes a hole and must go with it. They are a pair.
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
EXEMPT_PREFIXES = ("tools/verify/", "tools/process/")


def _range_tips(ranges):
    """The TIP revision of each pushed range — the bytes that will land on the remote.

    A range is `<base>..<tip>`; a bare rev is its own tip. Used only by the stale-at-tip leg, which
    asks whether `/rely` signed the content being PUSHED rather than the content on disk."""
    tips = []
    for r in ranges or []:
        r = r.strip()
        if not r:
            continue
        tips.append(r.split("..")[-1] if ".." in r else r)
    return tips


def _blob_hash(rev, path):
    """SHA-256 (first 12 hex) of `path` AT `rev`, hashed as RAW BYTES.

    ⚠ Bytes, never text. `sh()` decodes as UTF-8 with `errors="replace"`, which is lossy — every
    undecodable byte collapses to U+FFFD, so two different blobs can hash the same. That is exactly
    the class of defect `check_encoding.py` exists for, and it would sit inside the check meant to
    stop unreviewed bytes. Returns None when the path does not exist at `rev`."""
    r = subprocess.run(["git", "cat-file", "-p", "%s:%s" % (rev, path)],
                       cwd=REPO, capture_output=True)
    if r.returncode != 0:
        return None
    return hashlib.sha256(r.stdout).hexdigest()[:12]


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
            rc, o = sh("git", "diff", "--name-only", r)
            if rc != 0:
                # A git error must never be read as data. `sh` merges stderr into stdout, so
                # `fatal: Invalid revision range ...` would otherwise be returned as a filename.
                die("git could not resolve range %r — refusing to guess a scope:\n%s" % (r, o))
            out |= {l.strip() for l in o.splitlines() if l.strip()}
        return sorted(out)
    rc, out = sh("git", "diff", "--name-only", "HEAD")
    if rc != 0:
        die("git failed listing changed files:\n%s" % out)
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
            continue          # operating machinery: routed to /rely, which BLOCKS. See above.
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


def check_signals(ranges=None):
    """Validate each signal — EXISTENCE IS NOT ENOUGH.

    ⚠ The first version checked only that the file was present, and `prepush` PASSED on signals
    written for an earlier push that covered none of the 18 files changed since. A stale-signal
    fail-open is the exact failure the SHA-256-per-file scheme exists to prevent, reproduced in the
    tool meant to enforce it. A signal is valid iff (a) every file it records still hashes to the
    recorded value, and (b) every reviewable changed file is covered by a recorded hash.

    ⚠ Two rules below exist to keep this in step with the hook, which is a SECOND implementation of
    the same logic (PIPE-1). Both were measured as divergences on 2026-08-10:
      * NOTHING REVIEWABLE CHANGED -> no signal is required at all. The hook prints "review signals
        not required" and skips the section; this checked unconditionally, so a CLAUDE.md-only edit
        was blocked here and waved through there.
      * A GATE-EXEMPT file recorded in a signal must not stale it. Reviewers list CLAUDE.md for
        coverage, and it is edited constantly — so its hash drifting invalidated all three signals
        for a file no gate reviews. Exempt means exempt in both directions."""
    changed = set(reviewable_changed(ranges))
    out = []
    if not changed:
        return [(n, True, "no reviewable change in scope — signal not required")
                for n in ("er_cleared.txt", "ar_cleared.txt", "pa_cleared.txt")]
    for name in ("er_cleared.txt", "ar_cleared.txt", "pa_cleared.txt"):
        p = os.path.join(PRIV, name)
        if not os.path.exists(p):
            out.append((name, False, "missing"))
            continue
        recorded, drifted = {}, []
        for line in io.open(p, encoding="utf-8").read().splitlines()[1:]:
            parts = line.split(None, 1)
            if len(parts) == 2 and len(parts[0]) == 64:
                recorded[parts[1].strip()] = parts[0]
        for rel, want in recorded.items():
            _n = rel.replace(chr(92), '/').lower()
            if _n in EXEMPT_PATHS or _n.startswith(EXEMPT_PREFIXES):
                continue          # gate-exempt: its hash must not gate anything
            fp = os.path.join(REPO, rel)
            got = (hashlib.sha256(io.open(fp, "rb").read()).hexdigest()
                   if os.path.exists(fp) else "<deleted>")
            if got != want:
                drifted.append(rel)
        uncovered = sorted(changed - set(recorded))
        if drifted:
            out.append((name, False, "STALE — %d reviewed file(s) changed since: %s"
                        % (len(drifted), ", ".join(drifted[:3]))))
        elif uncovered:
            out.append((name, False, "does not cover %d changed file(s): %s"
                        % (len(uncovered), ", ".join(uncovered[:3]))))
        else:
            out.append((name, True, "fresh, covers %d file(s)" % len(recorded)))
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
    sys.exit(0 if (p_ok and s_ok) or not block else 1)


def cmd_precommit():
    """The mechanical gate before ANY commit — batch or not.

    ⚠ It used to require a batch, which made it unusable as a default: a one-line fix would have
    needed `batch start` first, and a gate that is annoying to run does not get run. The
    UNIVERSAL obligations (build green, a purity entry and an SSOT row for every added declaration,
    the suite at zero) apply to every commit; only stage ordering and filter-freezing are
    batch-specific. Without a batch it runs the universal half and says so."""
    state = load()
    report.banner("precommit pipeline", [
        ("entry", "batch.py precommit (manual; the pre-commit HOOK runs the checkers)"),
        ("batch", ("bucket '%s'" % state.get("bucket", "?")) if state
                  else "none — universal obligations only, stage ordering skipped"),
        ("scope", "the WORKING TREE as it stands"),
        ("basis", "declarations diffed against decl_baseline.txt on disk, never against git"),
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
    print("\nprecommit PASS — safe to commit")


def cmd_prepush(ranges=None):
    """The mechanical gate before ANY push — batch or not.

    `ranges` is supplied by the pre-push hook (the refs actually being pushed) and omitted by a
    manual run, which then reads the working tree. Same code either way; see `changed_files`.

    ⚠ It used to `require` a batch, which is the SAME defect `cmd_precommit` had already fixed and
    documents in its own docstring: a gate that refuses to run outside a batch is a gate that does
    not run. Fix-the-site-not-the-class, one function away from the fix.

    The cost was not merely inconvenience. The `/rely` routing — the hash signal that exists
    precisely because "checker changes are invisible to git" — lives HERE, so while this refused
    without a batch, a checker could be changed and pushed with the routing never consulted. That
    happened on 2026-08-09 (RLY-1).

    Everything below is universal; only the stage record is batch-specific, and it was already
    guarded. There is ONE pipeline, and it must fire in both states rather than grow a second."""
    state = load()
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
        # ⚠ TWO ROWS, NOT ONE, BECAUSE THE LEGS NOW ENFORCE DIFFERENTLY. A manifest that still said
        # "routing BLOCK" over a leg that warns is `RLY25-1` — a report publishing a stronger
        # property than it checks. The declaration is the whole point of the manifest.
        ("routing: logic + switches", "BLOCK",
         "/rely has signed every checker, hook and exemption switch at its current hashes"),
        ("routing: routed docs", "WARN",
         "prose under tools/verify|tools/process — DOWNGRADED 2026-08-21 (rung 5, measured "
         "non-convergence 10>4>6>9 then deadlock); stale count prints every run"),
        ("signals", "BLOCK", "editorial + adversary (+ prior-art on trigger 5) fresh and covering"),
        ("agent gate", "WARN", "an agent judges whether each check's PASS is EARNED; never blocks"),
    ])
    if state is None:
        print("no batch in progress — running the UNIVERSAL push checks only")
    else:
        require(state, "prepush")

    # ⚠ FAIL CLOSED when asked to judge a push whose scope we cannot see (F3, /rely 2026-08-10).
    # Run manually on a CLEAN tree this printed `prepush PASS, exit 0` for the very state where the
    # hook — which passes the real ranges — reported trigger 5 firing and all three signals failing
    # to cover 154 files. The working tree simply does not know what a push contains once the work
    # is committed, so saying PASS is a claim the command is not entitled to make.
    if ranges is None and not changed_files(None):
        print("\nCANNOT JUDGE: no --ranges given and the working tree is clean, so the scope of the")
        print("push is unknown. This command is only meaningful BEFORE committing; afterwards the")
        print("hook supplies the pushed ranges. Run `git push` and let the hook decide, or pass")
        print("--ranges <base>..<tip>.")
        sys.exit(1)

    fires, ins, newfile = check_trigger5(ranges)
    print("trigger 5: %s (%d insertions, new .lean file: %s)"
          % ("FIRES — prior-art review REQUIRED" if fires else "does not fire", ins, newfile))
    bad = 0
    # Purity and SSOT are enforced HERE as well as at precommit, because precommit is a manual
    # command and the pre-commit hook never blocks — so before this they were the only two
    # obligations with no automatic enforcement anywhere (Tim, 2026-08-09). They are safe at push in
    # a way `build` is not: neither has anything to do with `sorry`, so neither conflicts with the
    # stub-first protocol, which commits and pushes deliberately incomplete proofs.
    decls = added_decls()
    for name, ok, why in [("purity",) + check_purity(decls), ("ssot",) + check_ssot(decls),
                          ("pdf coupling",) + check_pdf_coupling(ranges)]:
        print("  %-18s %-4s %s" % (name, "ok" if ok else "FAIL", why))
        bad += 0 if ok else 1
    # ⚠⚠ ENFORCEMENT MODE COMES FROM THE ROW, NOT FROM THIS LINE. It used to be the literal
    # `bad += 0 if ran else 1`, which made the mode unreadable by any control — measured 2026-08-21,
    # `guards.py` kept printing `ok` over a router that no longer blocked, because a warrant can
    # compare a ROUTING pattern and has nothing to compare an enforcement decision against. A row
    # that carries `blocking` can be tested; a literal here cannot.
    # ⚠ A non-blocking row still PRINTS, and prints WARN rather than FAIL — a downgraded gate must
    # get louder, not quieter (`RLY25-1`: a report publishing `pass` for a property it stopped
    # checking).
    _routing_rows = check_routing(state or {}, ranges)
    for agent, ran, why, blocking in _routing_rows:
        print("  %-18s %-4s %s"
              % (agent, ("ok" if ran else ("FAIL" if blocking else "WARN")), why))
    bad += routing_bad(_routing_rows)
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
    print("\n=== Reviews required for this push ===")
    print("  scope: %d reviewable file(s)%s"
          % (len(scope), (" — e.g. " + ", ".join(scope[:3])) if scope else " (none)"))
    meta = {
        "er_cleared.txt": ("/editorial-review", "internal consistency + prose precision",
                           "any reviewable prose in the push"),
        "ar_cleared.txt": ("/adversary-review", "cold-reader triage + central-claim audit",
                           "any reviewable prose in the push"),
        "pa_cleared.txt": ("/prior-art-review", "closest prior art cited or shown absent",
                           "trigger 5: a new .lean file, or >=50 inserted .lean lines"),
    }
    for name, valid, why in check_signals(ranges):
        need = (name != "pa_cleared.txt") or fires
        ok = valid or not need
        agent, purpose, when = meta[name]
        print("  %-20s %-4s %s" % (agent, "ok" if ok else "FAIL",
                                   "REQUIRED" if need else "not required"))
        print("      purpose  %s" % purpose)
        print("      fires on %s" % when)
        print("      signal   %s/%s — %s"
              % (os.path.relpath(PRIV, REPO).replace("\\", "/"), name, why))
        v = signal_verdict(name)
        if v:
            print("      verdict  %s" % v)
        bad += 0 if ok else 1
    # ⚠ BEFORE the `die`, not after the PASS. On the success path only it would print just when the
    # push was already clear — and a recurrence count matters MOST while something is failing. That
    # placement would have re-created the original defect (surfacing at the rarest moment) in a new
    # location, which is the shape this whole change exists to correct.
    _recurrence_note()
    if bad:
        die("%d review signal(s) missing — run the gates" % bad)
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
    except (OSError, subprocess.SubprocessError):
        return
    # ⚠ ADVISORY MEANS ADVISORY: this must never be able to fail the caller. A note about process
    # health that can block a push is a worse defect than the one it reports.
    if not r.stdout:
        return
    rows = [l.strip() for l in r.stdout.splitlines() if "← NO CLASS ROW" in l]
    if not rows:
        return
    print()
    print("  recurring process shapes with NO class row (advisory — `selfheal.py` for the full list):")
    for line in rows[:3]:
        print("    %s" % line.lstrip("0123456789. "))
    print("  A shape here has recurred and has no DETECTOR. Second occurrence = a class"
          " (DEFECT_CLASSES.md);")
    print("  third = the rule's TRIGGER is wrong. See CLAUDE.md § WHEN A FAILURE RECURS.")


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

    rc_d, dirty = sh("git", "status", "--porcelain", "--", ".claude-local/DEFECTS.md")
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


def selftest():
    bad = 0
    print("decls_in — comment stripping and name shape")
    for label, src, want in DECL_CASES:
        got = decls_in(src)
        ok = got == want
        print("  %-46s %s" % (label, "ok" if ok else "*** got %s, want %s ***" % (got, want)))
        bad += 0 if ok else 1

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

    print("gate-stage staleness (DC-18)")
    fresh = {"stages": {"precommit": {"ok": True, "tool": self_hash()}}}
    stale = {"stages": {"precommit": {"ok": True, "tool": "deadbeef1234"}}}
    for label, state, want in [("passed under THIS tool counts", fresh, True),
                               ("passed under an OLDER tool does not", stale, False)]:
        ok = stage_done(state, "precommit") == want
        print("  %-46s %s" % (label, "ok" if ok else "*** WRONG ***"))
        bad += 0 if ok else 1

    print("\nselftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
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
        # Record that a routed deeper review ran, e.g. `batch.py review /rely`.
        st = load() or die("no batch in progress")
        st.setdefault("reviews", []).append(a[1])
        save(st)
        print("recorded review: %s" % a[1])
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
