# -*- coding: utf-8 -*-
"""MUTATION CONTROL for the behavioural routing routes in `guards.py` (ROUTE 3 and ROUTE 5).

⭐ THE CONTROL IS THE DELIVERABLE, NOT THE GUARD. A guard that is green on a clean tree has
demonstrated nothing whatsoever; the only evidence it works is that it goes RED when the property it
claims to protect is actually broken. This file breaks it, nine ways, and requires the predicted row
to fail each time.

⚠ IT ASSERTS THE ROW, NOT THE EXIT CODE. `guards.py` walks many routes and others may be failing for
unrelated reasons, so "exit 1" would pass this control for the wrong reason — the classic
warrant-satisfied-while-empty shape this whole layer keeps producing. Each mutation below names the
row that must go red.

⚠ TWO OF THE NINE REQUIRE THE GUARD TO STAY **GREEN**, AND THEY ARE NOT PADDING. `RLY27-1` (one
space before an argument list) and `RLY27-3` (a `list(...)` wrapper) each defeated the previous
AST-based version while changing NOTHING about behaviour. A behavioural control must be indifferent
to them. If a future version of this control starts requiring red on those two, someone has
reintroduced a syntax test.

**Provenance.** The nine are the six escapes `/rely` pass 6 executed against attempt 3 (`RLY27-1..6`),
plus the three classic neuters (`if False:` at the release gate, dropping `and blocking`, and
downgrading the `logic` leg). Written up in full in
`.claude-local/notes/reliability_2026-08-22_rely-routing-c01c0e3.md`.

**It runs in its own detached worktree and removes it.** ⚠⚠ NEVER point it at the shared checkout:
it edits `ship.py` and `batch.py` in place, and `CLAUDE.md`'s hardest rule is that an agent
exercising the gates must not touch the caller's tree. Self-provisioning is not convenience here, it
is the safety property.

**The mutations run CONCURRENTLY across a pool of K worktrees** (`ZP_PROBE_WORKERS`, default
`DEFAULT_WORKERS`; `1` is the old sequential run). The zero point, both controls and the baseline stay
sequential in the primary; every other pool worktree is provisioned to the primary's state and must
read the same baseline before it takes a mutation. See the block above `_execute`.

    python tools/verify/probe_routing_behavioural.py
    python tools/verify/probe_routing_behavioural.py --selftest     # the pool's own controls
"""
import hashlib
import io
import os
import queue
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import traceback

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common                                                    # noqa: E402

common.utf8_stdout()
SELF = common.self_rel(__file__)
REPO = str(common.REPO)

# ⚠ A SENTINEL, NOT A ROW LABEL. A mutation carrying this instead of a `guards.py` row is judged by
# running `batch.py prepush` and reading its EXIT CODE — see `_prepush_exit`.
EXIT_NEEDLE = "__prepush_exit__"

SHIP_ANCHOR = '        if agent == "/rely" and not ran and blocking:'
SHIP_LOOP = "    for agent, ran, why, blocking in batch.check_routing({}, ranges):"


def _read(p):
    return io.open(p, encoding="utf-8").read()


def _write(p, s):
    io.open(p, "w", encoding="utf-8", newline="\n").write(s)


def _guards_rows(wt):
    """Run guards.py inside the worktree and return {row label: ok|FAIL}."""
    p = subprocess.run([sys.executable, os.path.join(wt, "tools", "verify", "guards.py")],
                       capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=wt)
    rows = {}
    for line in (p.stdout + p.stderr).splitlines():
        m = re.match(r"\s+(ok|FAIL)\s+(.*)", line)
        if m:
            rows[m.group(2).strip()[:70]] = m.group(1)
    return p.returncode, rows


def _prepush_exit(wt):
    """Run `batch.py prepush` inside the worktree and return its EXIT CODE.

    ⚠⚠ THE OBSERVABLE THE FIRST FIVE CONTROLS LACKED. Every earlier attempt read a `guards.py` ROW,
    and a row is computed by calling the verdict functions in `guards`' own frame — where the
    property still holds however thoroughly `cmd_prepush` discards the answer. Measured 2026-08-24:
    one added line (`_routing_bad, _missing = 0, ()`) took prepush to exit 0 with `prepush PASS`
    printed under live FAIL rows, while guards reported 81/81 ok and this probe reported 11 of 11.

    **An exit code cannot be faked by rebinding a name.** It is the thing the hook actually consumes,
    so it is the thing the control must observe.

    ⚠⚠ `--ranges` IS LOAD-BEARING, AND ITS ABSENCE DEFEATED THIS CONTROL COMPLETELY (found by
    /rely, 2026-08-25). With no ranges and a clean worktree, `cmd_prepush` prints
    `CANNOT JUDGE: no --ranges given` and takes `sys.exit(1)` — BEFORE `routing_verdict` and
    `enforce_prepush_verdict` ever run. So the baseline's exit 1 came from the argument parser,
    not from the enforcement, and every mutation was compared against a run that never reached
    the code under test. The control reported 13 of 13 while observing nothing.

    That is `DC-22` — a control passing for the wrong reason — landing on the control built to
    close `RLY28-1`. The docstring above promised *"if that ever stops holding, this control has
    lost its teeth and must say so rather than pass"*; it could not say so, because nothing looked.
    `_assert_reached` is that check, and it fails LOUD rather than returning a code.

    ⚠⚠ IT RETURNS THE **ROUTING COUNT**, NOT THE EXIT CODE, AND THAT IS THE THIRD ATTEMPT AT THIS
    OBSERVABLE. The exit code is OVER-DETERMINED: `prepush` exits non-zero for review signals, the
    pushed-tip leg, a crash, or routing, so `exit != 0` cannot distinguish an ENFORCING router from
    an ABSENT one. Measured by /rely 2026-08-26 twice over:

      · `check_routing` replaced with `return []` -> "0 routing, 2 other", exit 1. The old probe
        read BLOCKS and every mutation still passed. The router was GONE and the control was green.
      · a fail-open planted in the copied `record.py` took prepush from 4 routing failures to 2 —
        `[logic]`, `[switch]` and both review-signal legs cleared — and the probe printed 13 of 13.

    Widening what the probe COPIED (the previous fix) changed what it could SEE and not what it
    LOOKED AT. `enforce_prepush_verdict` already prints the routing count separately — "%d push
    check(s) failed — %d routing, %d other" — so the number that answers the question is right
    there in the output the enforcement itself emits. A router that stops enforcing drives it to
    zero; nothing else does."""
    # ⭐⭐ THE NESTED RUNS DO NOT PAY THE ADVISORY INTERPRETATION LAYER. Measured 2026-09-07 in a
    # seeded worktree, in the invocation this function actually uses:
    #     prepush --ranges HEAD~1..HEAD, agent gate ON  : 119 s
    #     prepush --ranges HEAD~1..HEAD, agent gate OFF :   1 s
    # 118 of 119 seconds, across the 9 nested runs this probe makes — ~1084 s of an 1800 s pre-push
    # budget the run was exceeding at exit 124.
    #
    # ⚠ IT IS SAFE BECAUSE THE LAYER CANNOT MOVE A VERDICT, AND THAT WAS MEASURED RATHER THAN READ:
    # `agent_gate.run()` always returns 0 and `batch.py` deliberately does not increment `bad`, so
    # skipping it cannot touch the exit code half of `_prepush_blocks`'s conjunction. The whole probe
    # was then run with the gate off and returned **17 of 17 behaved as required**, zero point still
    # `routing=0 exit=0`, with the four EXIT_NEEDLE rows — the ones whose environment this changes —
    # among the passes.
    #
    # ⚠⚠ AND THE JUDGEMENT WAS NOT MEANINGLESS, IT WAS INVARIANT — the sharper reason and not the
    # one first written here. This probe mutates the ROUTER (`ship.py`, `batch.py`), never the
    # corpus, so `check_encoding`, `check_moved` and `check_figures` read a corpus the mutations do
    # not touch and legitimately answer "earned" every time. **We are declining to re-derive a
    # constant nine times, not discarding a verdict.**
    #
    # ⛔ SCOPED TO THE NESTED RUNS ONLY. The TOP-LEVEL layer still runs once per pre-push, where its
    # judgement is novel. ⚠ The 17-of-17 run had the gate off EVERYWHERE — a strictly MORE aggressive
    # configuration than this — so it bounds this change from above and is not a measurement of it.
    # ⚠ The skip is DISCLOSED: `batch.py:436` prints `agent gate skip — interpretation layer NOT run`.
    p = subprocess.run([sys.executable, os.path.join(wt, "tools", "verify", "batch.py"),
                        "prepush", "--ranges", "HEAD~1..HEAD"],
                       capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=wt,
                       env={**os.environ, "ZP_AGENT_GATE": "0"})
    out = p.stdout + p.stderr
    try:
        _assert_reached(out)
        m = re.search(r"push check\(s\) failed\s*[—-]\s*(\d+)\s+routing", out)
        if m:
            return int(m.group(1)), p.returncode
        # `prepush PASS` means the enforcement ran and found nothing: zero routing failures.
        if _ENFORCE_OK in out:
            return 0, p.returncode
        raise SystemExit(
            "probe could not read a ROUTING COUNT from prepush, and must not fall back to the exit\n"
            "  code alone — that is the over-determined observable this leg exists to stop using.")
    except SystemExit as e:
        # ⚠ KEEP THE EVIDENCE. An unreadable run used to be reported by its symptom alone, with the
        # child's output discarded — so the K=13 measurement (2026-10-04) could name WHICH observation
        # died but not WHY. The raw output goes to a file OUTSIDE the tree and the path rides along.
        fd, raw = tempfile.mkstemp(prefix="zp_probe_prepush_", suffix=".log")
        with io.open(fd, "w", encoding="utf-8") as fh:
            fh.write("cwd: %s\nexit: %d\n\n%s" % (wt, p.returncode, out))
        raise SystemExit("%s\n  raw prepush output: %s" % (e.code, raw))


def _prepush_blocks(wt):
    """True only when the router BOTH said it refused AND the process actually refused.

    ⚠⚠ FOURTH ATTEMPT AT THIS OBSERVABLE, AND THE DEFECT EACH TIME WAS **SUBSTITUTION**. Enforcement
    has two halves — *say it* (the routing count in `enforce_prepush_verdict`'s own message) and
    *do it* (the process exit code `hooks.py pre_push` actually consumes). Every previous version
    watched exactly one half and dropped the other, so each fix moved the blindness rather than
    removing it:

      · attempts 1-2 read a `guards.py` ROW — computed in guards' own frame, true however
        thoroughly `cmd_prepush` discards the answer.
      · attempt 3 read the EXIT CODE alone — over-determined, so `check_routing` replaced with
        `return []` still gave exit 1 and the probe printed 13 of 13 with the router GONE.
      · attempt 4 read the ROUTING COUNT alone and stopped reading `p.returncode` at all. /rely
        round 6 broke the *doing* half twice — `try/except SystemExit: pass` around
        `enforce_prepush_verdict`, and `die`'s `sys.exit(1)` changed to `sys.exit(0)` — and got,
        verbatim: `BLOCKED: 6 push check(s) failed — 4 routing, 2 other` followed by
        `prepush PASS`, `prepush exit=0`, `guards exit=0`, `RESULT: 13 of 13 behaved as required`.
        A green local push gate printing four routing failures directly above itself.

    Attempt 3's own docstring had the argument right — *"an exit code cannot be faked by rebinding
    a name; it is the thing the hook actually consumes, so it is the thing the control must
    observe"* — and attempt 4 then removed the exit code. **That is why this is a CONJUNCTION and
    not a better single signal.** Neither half is the property; the property is that they agree.
    Narrowing a proxy is the failure repeating, and swapping one proxy for another is the same move
    wearing a fix's clothes.

    ⚠ The two halves fail in OPPOSITE directions, which is what makes the conjunction total: the
    count goes to zero when the router stops enforcing and the exit code stays non-zero for four
    unrelated reasons; the exit code goes to zero when the refusal is swallowed and the count stays
    high because the message was already printed. Requiring both is the only reading under which
    each mutation above is visible."""
    routing, returncode = _prepush_exit(wt)
    return routing > 0 and returncode != 0


# ⚠⚠ THE OBSERVABLE MUST NAME THE ENFORCEMENT ITSELF. These are `enforce_prepush_verdict`'s own
# `die()` strings and `cmd_prepush`'s success line — the only outputs that exist BECAUSE the
# enforcement ran. Anything printed earlier proves nothing about it.
# ⚠⚠ `RLYB4-C2`: THE THIRD STRING WAS MISSING FOR AS LONG AS IT TOOK A `/rely` ROUND TO NOTICE.
# `enforce_prepush_verdict` gained `push verdict INCONSISTENT` on 2026-09-05 (the display-vs-record
# agreement check) and this tuple was not updated with it. Consequence, measured: in any state where
# the agreement check is the thing that fires, `_assert_reached` saw none of its needles and raised
# *"probe baseline produced NO output that only enforce_prepush_verdict can emit"* — so every
# mutation case that needed a failing NON-routing leg was unsatisfiable by construction. The author
# who added the message also added two mutation cases for it and ran neither.
# ⭐ WHEN YOU ADD A `die()` TO THE ENFORCEMENT, ADD ITS STRING HERE IN THE SAME EDIT. This tuple is
# the probe's only evidence that the code under test was reached at all.
_ENFORCE_DIE = ("push check(s) failed", "push verdict incomplete", "push verdict INCONSISTENT")
# ⚠ `prepush PASS` IS *NOT* ENFORCEMENT-EXCLUSIVE, and saying so would be the same mistake this
# check exists to catch. Measured by /rely 2026-08-25: it is printed four lines AFTER
# `enforce_prepush_verdict` returns, so with the enforcement call deleted `_assert_reached` does
# NOT fire — the exit-code leg is what catches that case. Kept because a genuine pass must still
# be accepted, but it carries no proof on its own; the die-strings above are the exclusive ones.
_ENFORCE_OK = "prepush PASS"


def _assert_reached(out):
    """Raise unless the run actually reached `enforce_prepush_verdict`.

    ⚠⚠ THE FIRST VERSION OF THIS CHECK WAS ITSELF DEFEATED, WHICH IS THE WHOLE LESSON. It looked
    for `"routing:"` / `"/rely"` — both printed by `report.plan()` BEFORE any routing happens — so
    it could only ever fire on an import crash. Measured by /rely 2026-08-25: with
    `enforce_prepush_verdict()` DELETED FROM THE PROGRAM, `_prepush_exit` still reported BLOCKS
    and the probe still printed `13 of 13`, because an unguarded `reviewed.get` raised
    `AttributeError` and the traceback exited 1 — the SAME code the enforcement exits.

    **An exit code cannot distinguish a gate that blocked from a gate that DIED.** That is `DC-22`
    landing on the control built to close `DC-22`, twice in two rounds. So the needles below are
    the enforcement's own words, and a traceback is now an explicit failure rather than a pass."""
    if "Traceback (most recent call last)" in out:
        raise SystemExit(
            "probe baseline CRASHED. Its exit 1 is a traceback, not the enforcement — every\n"
            "  mutation would be compared against a run that died before the code under test.\n"
            "  Fix the crash; do NOT relax this assertion.")
    if "CANNOT JUDGE" in out:
        raise SystemExit(
            "probe baseline never reached the enforcement: prepush exited at 'CANNOT JUDGE'.\n"
            "  Fix the invocation; do NOT relax this assertion.")
    if not (any(n in out for n in _ENFORCE_DIE) or _ENFORCE_OK in out):
        raise SystemExit(
            "probe baseline produced NO output that only `enforce_prepush_verdict` can emit.\n"
            "  Expected one of %r (it refused) or %r (it passed). Seeing neither means the run\n"
            "  ended before the enforcement, however plausible its exit code looks."
            % (_ENFORCE_DIE, _ENFORCE_OK))


def _row_state(rows, needle):
    hits = [v for k, v in rows.items() if needle in k]
    if not hits:
        return "ABSENT"
    return "FAIL" if "FAIL" in hits else "ok"


# -- ⭐⭐ RLY41-1: the failing baseline is CONSTRUCTED, never inherited -------------------
#
# ⚠⚠ THIS CONTROL PREVIOUSLY GOT ITS RED BASELINE BY ACCIDENT, AND THE ACCIDENT WAS REPAIRED
# OUT FROM UNDER IT. The old comment said it plainly: the worktree "supplies the failing state
# for free — it is detached at HEAD and `.claude-local/` is gitignored, so the `/rely` signal is
# absent there and the routing legs FAIL. If that ever stops holding, this control has lost its
# teeth and must say so rather than pass." Review signals then moved from `*_cleared.txt` files
# to LEDGER RECORDS keyed on `(step, path, blob)` — service-side, so a detached worktree with the
# same tree now gets the SAME answers as the main checkout. The blind spot the baseline stood on
# was a real defect and removing it was correct; standing on it undeclared was this file's defect,
# not the migration's. 2026-08-29: the control did the one thing `RLY31-8` gave it the ability to
# do, and refused to certify a tree it could not judge.
#
# ⭐ SO: a MUST-FIRE / MUST-SUPPRESS PAIR, which is this bundle's house style and which this probe
# has never had. Not a before/after delta.
#
#     A  perturb a ROUTED subject    -> MUST FIRE     (routing > 0, exit != 0)
#     B  perturb an UNROUTED subject -> MUST SUPPRESS (routing == 0, exit == 0)
#
# Both runs sit at the SAME HEAD, so `--ranges HEAD~1..HEAD` resolves identically; both are
# index-dirty; both are single-file. **The only free variable is routing membership**, which is
# the property under test. B is the half that was missing: if perturbing an UNROUTED file turns
# the routing legs red, the routing SCOPE is wrong, and nothing here would have caught it.
#
# ⚠⚠ STAGED, NOT COMMITTED, AND NOT LEFT IN THE WORKING TREE.
#
# ⚠⚠ THE FIRST VERSION OF THIS BLOCK STATED A FALSE PREMISE, AND IT IS CORRECTED HERE RATHER THAN
# QUIETLY REWRITTEN, because this block is the durable record and a wrong reason in it outlives a
# wrong line of code. It said: "unstaged edit -> index unchanged -> `moved` does NOT fire". That is
# WRONG. `moved` DOES fire on an unstaged edit — `ledger_subjects(rels, INDEX)` DROPS paths that are
# worktree-modified (skip reason: "modified in the worktree since it was staged"), so
# `checker_blobs()` returns `<ABSENT>` for them, and `<ABSENT>` is in no record and counts as moved.
# Measured: the HEAD blob `761cf303` IS covered by four `rely` records, and the unstaged edit still
# produced a red. Neither session opened `ledger_subjects` before asserting this.
#
#     unstaged edit  -> path DROPPED from the index read -> `<ABSENT>` -> red BY ABSENCE
#     STAGED edit    -> index blob genuinely differs      -> red BY MISMATCH
#     committed      -> also red, but MOVES HEAD
#
# ⭐ SO STAGING IS STILL RIGHT, FOR A DIFFERENT REASON THAN THE ONE ORIGINALLY RECORDED: it makes
# the baseline red because a blob DISAGREES with the record, not because a path went missing from
# the comparison. Red-by-absence and red-by-mismatch are the same colour and different facts, and a
# control that constructs the first while claiming the second is exactly the "red for the wrong
# reason" defect (`RLY31-8`) it exists to prevent. The sentinel path would also go green the moment
# `ledger_subjects` changed how it reports skips — a dependency on an error channel rather than on
# the property.
#
# `batch.py` has two routing legs, not one. `_stale_at_tip` reads the PUSHED TIP; `moved` /
# `_moved_blocking` reads the INDEX — `checker_blobs()` is `ledger_subjects(rels, common.INDEX)`
# and says "from the INDEX" in its own docstring. Committing is not merely overkill: it moves HEAD,
# so `HEAD~1..HEAD` would resolve to the perturbation commit in one run and to the whole prior
# range in the other — two SCOPES compared as though only content differed, which is exactly the
# confound this pair exists to remove.
#
# ⭐ This is the same fact that built `unstage`: on this pipeline STAGING IS THE VERIFICATION STEP,
# because the ledger keys on the index.
#
# ⚠ THE FILENAME IS A DIAGNOSTIC AND NEVER A PASS CRITERION. The first draft of this asserted that
# the refusal NAMES the perturbed file. That is attempt 5 of the defect this file already died of
# four times: the filename appears in the routing FAIL row, which is printed BEFORE
# `enforce_prepush_verdict` runs, and `_ENFORCE_DIE`'s comment says "Anything printed earlier proves
# nothing about it." `_assert_reached`'s own first version died this way, grepping strings
# `report.plan()` prints before any routing happens. A grep for the filename is that same string one
# round later — satisfied by a run that printed the row and then had the enforcement deleted,
# swallowed or `sys.exit(0)`-ed. A named red ASSERTED on the wrong string is worse than an unnamed
# red, because it reads as more rigorous. Print it; do not assert it.

# ⚠ A: ROUTED (`^tools/verify/`) and a `CHECKERS` entry, because `moved` is computed over CHECKERS.
#     `_leg_of` -> "logic", and `_LEG_BLOCKING["logic"] is True`, so it blocks. Verified both.
_A_SUBJECT = "tools/verify/check_moved.py"
# ⚠ B: UNROUTED — outside `^tools/verify/`, `^tools/process/` and `^.github/workflows/`. MEASURED
#     to trip nothing rather than reasoned into; see `_require_suppressed`, which reads the ROWS and
#     not merely the tuple, because "(0, 0)" is also what "something fired and something else
#     cancelled" looks like. Do NOT weaken this to fit a subject: pick another subject.
_B_SUBJECT = "scripts/fonts/DejaVuSans.ttf"
# ⚠ INERT BY CONSTRUCTION: a trailing comment in a `.py`, trailing junk in a binary nothing parses
#     at push time. The perturbation must change the BLOB without changing BEHAVIOUR, or A's red
#     could come from the file breaking rather than from the routing leg.
_PERTURBATION = b"\n# probe: staged perturbation (RLY41-1)\n"


def _cannot_judge(msg):
    """Abort with exit 2 — "the control could not look", never "a mutation escaped".

    ⚠⚠ THE FIRST VERSION OF THESE HELPERS USED BARE `raise SystemExit(msg)`, WHICH EXITS 1 — the
    MUTATION-FAILURE code. So four of the seven "cannot judge" paths were indistinguishable from a
    real fail-open finding, in the same change that added an explicit zero-point refusal returning
    2. Caught by `/rely` 2026-08-29.

    ⚠ This is the `died`/`failed` distinction that `preflight` exists to preserve — "it failed" and
    "it never ran" are different facts, and only one means the gate actually judged your tree —
    leaking out of the control that was arguing for it. `hooks.py:347` then collapses 2 into 1
    anyway (`RLY41-2`, and `:318` already has the `== 2` pattern to match), but that is a separate
    defect: this side must emit the distinction before the reader's side can be blamed for erasing
    it."""
    print(msg)
    raise SystemExit(2)


def _staged_paths(wt):
    """Exactly what is in the worktree's index, as repo-relative paths."""
    p = subprocess.run(["git", "diff", "--cached", "--name-only"], cwd=wt,
                       capture_output=True, text=True, encoding="utf-8", errors="replace")
    return sorted(x for x in p.stdout.split() if x)


def _perturb_and_stage(wt, rel):
    """Perturb ONE named path in the worktree and stage it BY NAME. Returns (abspath, original).

    ⚠⚠ NAMED PATH, NEVER A BULK ADD, AND THE PROBE ASSERTS IT STAGED EXACTLY ONE THING. The
    worktree is seeded with ~63 working-tree copies from `tools/verify/` that are deliberately
    UNSTAGED — which is why `moved` compares HEAD blobs and the unperturbed run reads green. An
    `add -A` / `add .` / `add -u` would sweep all of them into the index.

    ⚠ AND THE TRAP IS CONDITIONAL, WHICH IS WHY THIS IS AN ASSERTION AND NOT JUST CARE. While the
    INVOKING checkout is clean the seeded bytes equal HEAD, so a bulk add moves no blob and the
    damage is invisible. The moment the invoking checkout is DIRTY, seeded bytes differ from HEAD,
    `moved` fires across the whole bundle, and BOTH A and B go red — B red for a reason that has
    nothing to do with its subject, which is `RLY31-8` (red for the wrong reason) landing on the
    control built to replace it. A bulk add would silently couple this probe's verdict to the
    cleanliness of whatever checkout invoked it. Checking is a property of the probe; being careful
    is only a property of whoever edits it next."""
    p = os.path.join(wt, *rel.split("/"))
    if not os.path.exists(p):
        _cannot_judge(
            "probe cannot perturb %r — it is not in the worktree. The subject must be a tracked\n"
            "  path; do NOT substitute a different one to make this run." % rel)
    before = _staged_paths(wt)
    if before:
        _cannot_judge(
            "probe expected a CLEAN index before perturbing, found staged: %s\n"
            "  A previous perturbation was not restored; the two would compound." % before)
    with io.open(p, "rb") as fh:
        original = fh.read()
    with io.open(p, "wb") as fh:
        fh.write(original + _PERTURBATION)
    add = subprocess.run(["git", "add", "--", rel], cwd=wt,
                         capture_output=True, text=True, encoding="utf-8", errors="replace")
    if add.returncode != 0:
        _cannot_judge("probe could not stage %r: %s" % (rel, (add.stdout + add.stderr).strip()))
    staged = _staged_paths(wt)
    if staged != [rel]:
        _cannot_judge(
            "probe staged %s, expected exactly [%r].\n"
            "  A bulk add would sweep in the ~63 seeded copies and make BOTH controls red for a\n"
            "  reason unrelated to their subjects. Stage by NAMED PATH; do NOT relax this."
            % (staged, rel))
    return p, original


def _restore_staged(wt, rel, p, original):
    """Put the bytes back and return the index to HEAD, asserting nothing is left staged."""
    with io.open(p, "wb") as fh:
        fh.write(original)
    subprocess.run(["git", "add", "--", rel], cwd=wt,
                   capture_output=True, text=True, encoding="utf-8", errors="replace")
    staged = _staged_paths(wt)
    if staged:
        _cannot_judge(
            "probe could not restore the index after perturbing %r; still staged: %s" % (rel, staged))


def _require_suppressed(wt, rel):
    """B: perturbing an UNROUTED subject must leave the routing legs silent AND prepush green.

    ⚠⚠ KNOWN-WEAK, LEDGERED AS DEBT (`RLY41-3`), AND SAYING SO IS THE POINT. `/rely` measured that
    NO staged perturbation of this subject can reach the prefix-routing leg at all: `checker_blobs()`
    iterates `CHECKERS` only, and `changed_files(ranges)` is a commit-range diff — B's subject is in
    neither, and matches no `/rely` pattern. So the original version of this function printed "the
    routing SCOPE is wrong", **a claim about a defect it structurally cannot detect**. "A checker
    that cannot fail is not a check" is this project's own phrase, and it applied here.

    ⚠ WHAT IT ACTUALLY TESTS, stated narrowly enough to be true: that staging an UNROUTED file does
    not turn prepush red. That catches a GROSS over-fire — routing widened to everything, or the
    index read losing its `CHECKERS` restriction — and it catches nothing subtler. It does NOT
    verify prefix membership. A stronger B needs a NEAR-MISS subject (a `.py` outside every routed
    prefix, e.g. under `scripts/`) so that a plausible scope widening, rather than only a total one,
    would trip it. Not done here: choosing it requires a measured run per candidate, and this tree
    is one `/rely` round from a push. `RLY41-3`.

    ⚠⚠ THE ROWS ARE COMPARED AGAINST A BASELINE TAKEN BEFORE THE PERTURBATION, and the first version
    was not. It read the guards rows only AFTER perturbing, so any row that was ALREADY red got
    blamed on B's subject — the same misattribution the zero point exists to prevent, one leg over,
    in the function whose failure text names the subject. `(0, 0)` is also what "something fired and
    something else cancelled" looks like, which is why the rows are read at all."""
    _rc0, base_rows = _guards_rows(wt)          # the origin, taken BEFORE anything moves
    p, original = _perturb_and_stage(wt, rel)
    try:
        routing, rc = _prepush_exit(wt)
        _rc, rows = _guards_rows(wt)
        # Only rows this perturbation CHANGED for the worse are attributable to it.
        # ⚠⚠ THE `"ok"` DEFAULT IS A FAIL-OPEN FIX, NOT TIDINESS. `base_rows.get(k)` returns None
        # for a row ABSENT from the baseline, and `None != "ok"` classified it as PRE-EXISTING — so
        # a row that appears only AFTER the perturbation, which is the most attributable evidence
        # there is, was excused instead of counted. Absent-at-baseline means "was not red then",
        # so it defaults to "ok" and lands in `fired`. Caught by `/rely` 2026-08-29.
        fired = sorted(k for k, v in rows.items()
                       if v != "ok" and base_rows.get(k, "ok") == "ok")
        already = sorted(k for k, v in rows.items()
                         if v != "ok" and base_rows.get(k, "ok") != "ok")
    finally:
        _restore_staged(wt, rel, p, original)
    print("    suppress control  unrouted %-34s routing=%d exit=%d" % (rel, routing, rc))
    if already:
        print("       (pre-existing red rows, NOT attributed to %s: %s)" % (rel, ", ".join(already)))
    if routing or rc or fired:
        print("    ** SUPPRESS CONTROL FAILED — an UNROUTED subject moved something. **")
        if routing or rc:
            print("       routing=%d exit=%d on a subject in neither CHECKERS nor the range."
                  % (routing, rc))
            print("       That is a GROSS over-fire: the index read or the routed set has lost its")
            print("       restriction. It is NOT evidence about prefix membership — see RLY41-3.")
        if fired:
            print("       rows this perturbation turned red: %s" % ", ".join(fired))
            print("       %r is not exempt from everything. PICK A DIFFERENT SUBJECT for B;" % rel)
            print("       do NOT weaken this control to accommodate it.")
        return False
    return True


def _require_fires(wt, rel):
    """A: perturbing a ROUTED subject must make the router BOTH say it refused AND refuse.

    ⚠⚠ THE VERDICT COMES FROM `_prepush_blocks`, AND THE FIRST VERSION OF THIS FUNCTION LIED ABOUT
    THAT. It said "Uses `_prepush_blocks`, UNTOUCHED" while actually recomputing
    `routing > 0 and rc != 0` inline — a COPY of the conjunction, in the fix for the control whose
    four previous deaths were all substitution, with a docstring asserting the opposite. A fifth
    attempt at that observable would have been made in `_prepush_blocks` and never reached here,
    silently. Caught by `/rely` 2026-08-29, and it is the sharpest instance of the class tonight
    precisely because the docstring made it unreadable as a copy.

    ⚠ THE NUMBERS ARE PRINTED, THE VERDICT IS CALLED. `_prepush_exit` supplies the diagnostic line;
    `_prepush_blocks` supplies the decision. That is two prepush runs rather than one, and the cost
    is the point: deriving the verdict from the numbers already in hand is exactly how the copy got
    written. The conjunction is four attempts of hard-won — neither half is the property, the
    property is that the two AGREE — so it is CALLED, never re-expressed.

    The perturbation is left STAGED on purpose: it is the red baseline the consumer-neuter cases
    below are measured against."""
    p, original = _perturb_and_stage(wt, rel)
    routing, rc = _prepush_exit(wt)          # diagnostic only — NOT the verdict
    blocks = _prepush_blocks(wt)             # THE verdict: the shared conjunction, not a copy
    print("    fire control      routed   %-34s routing=%d exit=%d" % (rel, routing, rc))
    if not blocks:
        print("    ** FIRE CONTROL FAILED — a STAGED perturbation of a ROUTED subject did not")
        print("       block. Either the routing legs stopped reading the index, or %r" % rel)
        print("       left CHECKERS. Fix the cause; do NOT relax this into a weaker observable. **")
        _restore_staged(wt, rel, p, original)
        return None
    return p, original


def mutations(ship, batch):
    """(label, path, transform, row-needle, required state) — see the module docstring."""
    return [
        # --- must stay GREEN: pure syntax, zero behavioural content ---------------------------
        ("RLY27-1  one space before the arg list", ship,
         lambda s: s.replace("batch.check_routing({}, ranges)", "batch.check_routing ({}, ranges)"),
         "release gate", "ok"),
        ("RLY27-3  list(...) wrapper around the call", ship,
         lambda s: s.replace(SHIP_LOOP,
                             "    _rows = list(batch.check_routing({}, ranges))\n"
                             "    for agent, ran, why, blocking in _rows:"),
         "release gate", "ok"),

        # --- must go RED: the enforcement is actually gone ------------------------------------
        ("NEUTER   release gate `if False:`", ship,
         lambda s: s.replace(SHIP_ANCHOR, "        if False:"),
         "release gate", "FAIL"),
        ("RLY27-7  release gate prints the flag, obeys nothing", ship,
         lambda s: s.replace(SHIP_ANCHOR,
                             '        print("routing:", blocking)\n        if False:'),
         "release gate", "FAIL"),
        ("RLY27-2  release gate as a comprehension with `and False`", ship,
         lambda s: s.replace(SHIP_LOOP + "\n" + SHIP_ANCHOR,
                             "    for agent, ran, why, blocking in [\n"
                             "            r for r in batch.check_routing({}, ranges) if False]:\n"
                             "        if True:"),
         "release gate", "FAIL"),
        ("NEUTER   release gate drops `and blocking`", ship,
         lambda s: s.replace(SHIP_ANCHOR, '        if agent == "/rely" and not ran:'),
         "release gate", "FAIL"),
        ("RLY27-4  verdict counts a sequence it did not print", batch,
         lambda s: s.replace('    return verdict_record("routing", routing_bad(rows))',
                             '    return verdict_record("routing", routing_bad([]))'),
         "push verdict", "FAIL"),
        ("NEUTER   cmd_prepush never calls routing_verdict", batch,
         lambda s: s.replace("    routing_verdict(state, ranges)\n", "    pass\n"),
         "prepush still calls", "FAIL"),
        # ⚠⚠ `RLY28-1` VERBATIM, AND IT MUST STAY **GREEN**. This is the mutation that defeated the
        # gate on 2026-08-23 — exit 1 → exit 0, "prepush PASS", three `/rely FAIL` rows on screen —
        # and it is here as a MUST-STAY-OK case because the producer now records its own count, so
        # discarding the return value at the call site changes nothing. ⚠ If a future version of
        # this control starts requiring RED here, someone has put the verdict back in the caller's
        # hands and the annihilation is live again.
        ("RLY28-1  caller annihilates the return value", batch,
         lambda s: s.replace("    routing_verdict(state, ranges)\n",
                             "    routing_verdict(state, ranges) * 0\n"),
         "push verdict registry", "ok"),
        # The other half of the same property: delete the producer's record and the registry must
        # fail CLOSED on the absence, never report zero failures.
        ("NEUTER   the producer stops recording its count", batch,
         lambda s: s.replace('    return verdict_record("routing", routing_bad(rows))',
                             "    return routing_bad(rows)"),
         "push verdict registry", "FAIL"),
        ("NEUTER   the logic leg downgraded to non-blocking", batch,
         lambda s: s.replace('_LEG_BLOCKING = {"logic": True, "switch": True, "docs": False}',
                             '_LEG_BLOCKING = {"logic": False, "switch": True, "docs": False}'),
         "fail-open leg still BLOCKS: logic", "FAIL"),

        # ⚠⚠ THE CONSUMER-SIDE NEUTERS, AND THEY ARE THE ONES THE FIRST FIVE CONTROLS COULD NOT SEE.
        # Observable is the PROCESS EXIT CODE of `batch.py prepush`, not a guards row — a row is
        # computed in guards' own frame and stays true no matter what `cmd_prepush` does with the
        # answer. Measured 2026-08-24: the mutation below took prepush to exit 0 / "prepush PASS"
        # under live FAIL rows while guards printed 81/81 ok and this probe printed 11 of 11.
        # Both REQUIRE `BLOCKS`: the enforcement must survive the caller trying to drop it.
        #
        # ⚠⚠ `RLY28-1b` WAS RETIRED HERE BY `B4`, AND RETIRING IT IS THE EVIDENCE, NOT A GAP.
        # It mutated `enforce_prepush_verdict(bad)` to `(bad * 0)` and required BLOCKS, with the
        # comment "annihilating the caller's own count cannot hide a ROUTING failure". Every word
        # of that was true and it tested the ONE leg that was already safe: `bad` also carried
        # purity, ssot, pdf coupling, prior-art attribution and both review signals, and `* 0`
        # silenced all six. The case is now UNEXPRESSIBLE because the function takes no argument
        # and no accumulator exists to annihilate — re-adding it would only raise `NameError` and
        # "block" on a crash, which is a control passing for the wrong reason.
        #
        # ⭐ WHAT REPLACES IT ATTACKS THE NEW SURFACE. With every leg recording itself, the way to
        # re-open the hole is no longer to zero a number — it is to quietly shrink the set of steps
        # that MUST report, so a deleted write stops failing closed. That is one token, it looks
        # like tidying, and `guards.py`'s independently-written expected set is what refuses it.
        # MUST GO RED.
        ("B4       `_EXPECTED` quietly loses a gating leg", batch,
         lambda s: s.replace(
             '_EXPECTED = ("routing", "purity", "ssot", "pdf_coupling", "prior_art_attrib")',
             '_EXPECTED = ("routing", "purity", "ssot", "pdf_coupling")'),
         "push verdict registry", "FAIL"),
        # ⚠⚠ `RLYB4-1` — THE VALUE HALF, AND IT IS HERE BECAUSE A `/rely` ROUND BROKE `B4` WITH IT
        # ON THE DAY `B4` LANDED. `_EXPECTED` checks that every leg is PRESENT and checks only
        # `routing`'s VALUE, so annihilating a leg's recorded count leaves the row present holding a
        # zero it did not earn. Measured: this exact mutation printed `purity FAIL SYNTHETIC`
        # directly above `prepush PASS`, with `guards.py` green on all six registry rows — the
        # 2026-08-23 photograph reproduced against the fix written for it.
        # MUST STAY BLOCKING: `display_fail` tallies what reached the SCREEN, so a recorded zero now
        # disagrees with a displayed FAIL and `enforce_prepush_verdict` refuses on the mismatch.
        ("RLYB4-1  producer annihilates its own recorded count", batch,
         lambda s: s.replace("        verdict_record(key, 0 if ok else 1)",
                             "        verdict_record(key, (0 if ok else 1) * 0)"),
         EXIT_NEEDLE, "BLOCKS"),
        # The other half of the same property: drop the DISPLAY tally instead of the record. It must
        # fail closed in this direction too, or the agreement check is a one-way ratchet that a
        # single deletion walks past.
        ("RLYB4-1b the display tally is dropped", batch,
         lambda s: s.replace("        if not ok:\n            display_fail(key)\n", "        pass\n"),
         EXIT_NEEDLE, "BLOCKS"),
        # MUST GO RED: deleting the enforcement outright is the one consumer-side move left, and the
        # AST row is what makes it loud. ⚠ Judged on the guards ROW, not the exit code — a deleted
        # enforcement genuinely does let prepush exit 0, so "still blocks" is not achievable here and
        # demanding it would be a control that can never pass.
        ("NEUTER   cmd_prepush discards the enforcement call", batch,
         lambda s: s.replace("    enforce_prepush_verdict()", "    pass"),
         "prepush enforces the verdict", "FAIL"),

        # ⚠⚠ RLY36-1, AND THESE TWO ARE THE REASON `_prepush_blocks` IS A CONJUNCTION. Both break
        # the *doing* half of enforcement while leaving the *saying* half untouched, so the routing
        # count stays at its real value and only the exit code moves. /rely round 6 measured both
        # against the routing-count-only observable and the probe printed 13 of 13 over a push gate
        # that exits 0 with editorial FAIL, adversary FAIL, rely FAIL and four routing failures
        # printed above it. They require "PASSES": the observable must NOTICE that the process
        # stopped refusing. ⚠ MEASURED BOTH WAYS WHEN THIS LANDED, which is the only reason it is a
        # control and not a hypothesis: with the conjunct, 15 of 15 and both report PASSES; with the
        # conjunct removed (`return routing > 0`), 13 of 15 and both report BLOCKS. Exactly these two
        # moved — the other thirteen cases were unaffected, so the added conjunct does not over-fire. ⚠ If either of these ever reads "BLOCKS" again, someone has gone back to
        # watching one half, and the fourth instance of this defect is live.
        #
        # ⚠ `guards.py` cannot cover either one. Its row is an AST query for the NAME
        # `enforce_prepush_verdict` in a Load context, and its own comment claims the enumeration is
        # complete — "the only remaining consumer-side move is to DELETE the call". Wrapping the call
        # keeps the name in a Load context, and editing `die` never touches the call site at all;
        # both are instances the control's construction can never produce, which is detector 1 from
        # the brief. The unit of that check is a name; the unit of the claim is whether the push is
        # refused.
        ("RLY36-1a consumer swallows the refusal (try/except SystemExit)", batch,
         lambda s: s.replace("    enforce_prepush_verdict()",
                             "    try:\n"
                             "        enforce_prepush_verdict()\n"
                             "    except SystemExit:\n"
                             "        pass"),
         EXIT_NEEDLE, "PASSES"),
        # ⚠ WRITTEN AGAINST THIS ONE FIRST, per DC-26. `die` is the shared refusal primitive — it
        # prints "BLOCKED: ..." and exits. Flipping its exit status alone leaves every message,
        # every FAIL row and every count byte-identical, so nothing that reads OUTPUT can see it.
        ("RLY36-1b the refusal primitive exits 0", batch,
         lambda s: s.replace('    print("BLOCKED: %s" % msg)\n    sys.exit(1)',
                             '    print("BLOCKED: %s" % msg)\n    sys.exit(0)'),
         EXIT_NEEDLE, "PASSES"),
    ]


# -- ⭐ CONCURRENT MUTATIONS (Tim, 2026-10-04: "Tooling speed concurrent checks.") -----------------
#
# Each mutation edits `ship.py` or `batch.py` IN PLACE, observes, and restores, so two mutations in
# ONE worktree would observe each other's bytes. The unit of concurrency is therefore the WORKTREE:
# a pool of K, one mutation per worktree at a time, never two.
#
# ⚠⚠ A POOL WORKTREE IS ONLY A SUBSTITUTE FOR THE PRIMARY IF IT IS IN THE PRIMARY'S STATE, and that
# state is CONSTRUCTED above, not inherited: detached at HEAD, the whole `tools/verify/` bundle copied
# from the working tree, B perturbed and RESTORED (index clean), then A perturbed and LEFT STAGED by
# `_require_fires` — the red baseline every EXIT_NEEDLE case is measured against. `_provision`
# rebuilds exactly that (A staged by the same `_perturb_and_stage`), and `_pool_problems` then REFUSES
# (exit 2) unless each pool worktree matches the primary on bytes, index, status AND the observed
# baseline (every guards row plus the prepush BLOCKS state). A worktree that merely LOOKS provisioned
# is not trusted with a verdict.
#
# ⚠ The zero point and both controls are NOT re-run per pool worktree: they establish that the
# PRIMARY's construction is attributable, and the pool is then checked to be the same construction.
#
# ⭐ R-ZERONULL: a mutation that could not run is `DIED`, its own outcome, never PASS and never a
# mutation FAIL. A pool that could not be built, a worktree held by two mutations at once, or a
# mutation that never ran all exit 2. The RESULT denominator is `len(muts)`, never the count that
# happened to come back.
WORKERS_ENV = "ZP_PROBE_WORKERS"
DEFAULT_WORKERS = 8
_GIT_LOCK = threading.Lock()     # `git worktree add/remove` mutate the shared common dir: serialise


class _CannotJudge(Exception):
    """The probe could not LOOK. Exit 2 — distinct from a mutation escaping (exit 1)."""


def _workers(n):
    """K from `ZP_PROBE_WORKERS`, capped at the mutation count. Malformed input refuses."""
    raw = os.environ.get(WORKERS_ENV, "").strip()
    if not raw:
        return max(1, min(DEFAULT_WORKERS, n))
    try:
        k = int(raw)
    except ValueError:
        k = 0
    if k < 1:
        _cannot_judge("%s=%r is not a positive integer — refusing rather than guessing a pool size."
                      % (WORKERS_ENV, raw))
    return min(k, n)


def _add_worktree(wt):
    with _GIT_LOCK:
        return subprocess.run(["git", "worktree", "add", "--detach", wt, "HEAD"],
                              capture_output=True, text=True, encoding="utf-8", errors="replace",
                              cwd=REPO)


def _seed(wt):
    """Copy the WHOLE working-tree `tools/verify/` bundle into `wt`. Returns the file count."""
    copied = 0
    for root, dirs, files in os.walk(os.path.join(REPO, "tools", "verify")):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        for f in files:
            src = os.path.join(root, f)
            dst = os.path.join(wt, os.path.relpath(src, REPO))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(src, dst)
            copied += 1
    return copied


def _provision(wt, created):
    """Build one pool worktree in the primary's mutation-time state (see the block above)."""
    add = _add_worktree(wt)
    if add.returncode != 0:
        raise _CannotJudge("git worktree add failed: %s" % (add.stdout + add.stderr).strip()[:300])
    created.append(wt)
    _seed(wt)
    _perturb_and_stage(wt, _A_SUBJECT)


def _tree_state(wt):
    """What a worktree IS, for comparison with the primary: HEAD, index, status and the bytes of
    every file the mutations or the observers read from the copied bundle (plus A's subject)."""
    def g(*args):
        p = subprocess.run(["git"] + list(args), cwd=wt, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        return "%d\n%s" % (p.returncode, p.stdout)
    h = hashlib.sha256()
    rels = []
    for root, dirs, files in os.walk(os.path.join(wt, "tools", "verify")):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        rels += [os.path.relpath(os.path.join(root, f), wt).replace("\\", "/") for f in files]
    for rel in sorted(rels) + [_A_SUBJECT, _B_SUBJECT]:
        h.update(rel.encode("utf-8") + b"\0")
        with io.open(os.path.join(wt, *rel.split("/")), "rb") as fh:
            h.update(hashlib.sha256(fh.read()).digest())
    return {"head": g("rev-parse", "HEAD"), "staged": _staged_paths(wt),
            "index": hashlib.sha256(g("ls-files", "-s").encode("utf-8")).hexdigest(),
            "status": g("status", "--porcelain"), "bytes": h.hexdigest()}


def _baseline_obs(wt, needles):
    """({needle: state}, {guards row: ok|FAIL}) — the unmutated observation every verdict is
    judged against. Shared by the primary's printed baseline and each pool worktree's check."""
    _rc, rows = _guards_rows(wt)
    obs = {}
    for n in needles:
        obs[n] = (("BLOCKS" if _prepush_blocks(wt) else "PASSES") if n == EXIT_NEEDLE
                  else _row_state(rows, n))
    return obs, rows


def _why(e):
    if isinstance(e, SystemExit):
        return "exited %r" % (e.code,)
    return "%s: %s" % (type(e).__name__, e)


def _build_pool(paths, provision_one, state_of, created):
    """Provision every path concurrently and observe each one's state. Returns (states, problems).
    Judged against the primary by `_pool_problems`, never trusted on its own."""
    problems, states = [], {}
    lock = threading.Lock()

    def one(p):
        try:
            provision_one(p, created)
            st = state_of(p)
        except BaseException as e:                      # noqa: BLE001 — SystemExit included
            with lock:
                problems.append("%s: could NOT be provisioned — %s" % (p, _why(e)))
            return
        with lock:
            states[p] = st

    threads = [threading.Thread(target=one, args=(p,)) for p in paths]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return states, problems


def _pool_problems(paths, states, problems, ref):
    """Every reason the pool may NOT take a mutation. An empty list is the ONLY licence."""
    problems = list(problems)
    for p in paths:
        if p not in states:
            continue
        elif states[p] != ref:
            diff = sorted(k for k in set(ref) | set(states[p]) if ref.get(k) != states[p].get(k))
            problems.append("%s: does NOT read the primary's baseline (differs in: %s)"
                            % (p, ", ".join(diff)))
    return problems


def _make_runner(muts_by_wt, observe, pristine):
    """run_one(wt, i): apply mutation i IN `wt`, observe, restore. Refuses on non-pristine bytes."""
    def run_one(wt, i):
        label, path, mutate, needle, _want = muts_by_wt[wt][i]
        original = _read(path)
        if original != pristine[path]:
            raise _CannotJudge("%s is not pristine before %r — another mutation's bytes are in it"
                               % (path, label.strip()))
        mutated = mutate(original)
        if mutated == original:
            return ("NOAPPLY",)
        _write(path, mutated)
        try:
            got = observe(wt, needle)
        finally:
            _write(path, original)
        return ("GOT", got)
    return run_one


def _observe(wt, needle):
    """The real observation — exactly what the sequential loop has always done per mutation."""
    if needle == EXIT_NEEDLE:
        return "BLOCKS" if _prepush_blocks(wt) else "PASSES"
    _rc, rows = _guards_rows(wt)
    return _row_state(rows, needle)


def _dispatch(pool, order, run_one):
    """Run every index in `order` across `pool`, one worker per worktree. Returns
    (results {i: outcome}, done [completion order], problems)."""
    if len(set(pool)) != len(pool):
        return {}, [], ["the pool names a worktree twice: %s" % pool]
    results, done, problems = {}, [], []
    lock = threading.Lock()
    held = set()

    def one(wt, i):
        with lock:
            breach = wt in held
            if not breach:
                held.add(wt)
        # ("DIED", code, message, re-observable?). ⚠ An isolation breach or a non-pristine refusal is
        # a defect in the POOL and is never re-observed — a retry at concurrency 1 would hide exactly
        # what the ISOLATION control exists to catch. Only an OBSERVATION that died may be retried.
        if breach:
            out = ("DIED", 2, "ISOLATION BREACH: %s already holds a mutation" % wt, False)
        else:
            try:
                out = run_one(wt, i)
            except _CannotJudge as e:
                out = ("DIED", 2, str(e), False)
            except SystemExit as e:
                # A string code is the house `raise SystemExit(msg)` -> exit 1; an int keeps its
                # code; 0/None mid-mutation is NOT a pass, so it cannot judge.
                if isinstance(e.code, str):
                    out = ("DIED", 1, e.code, True)
                else:
                    out = ("DIED", e.code if e.code else 2, "exited %r" % (e.code,), True)
            except BaseException:                       # noqa: BLE001 — a crash is not a verdict
                out = ("DIED", 1, traceback.format_exc(), True)
            finally:
                with lock:
                    held.discard(wt)
        with lock:
            if i in results:
                problems.append("mutation #%d ran twice" % i)
            results[i] = out
            done.append(i)

    if len(pool) == 1:                                  # K=1: inline, in order, no threads
        for i in order:
            one(pool[0], i)
        return results, done, problems
    q = queue.Queue()
    for i in order:
        q.put(i)

    def worker(wt):
        while True:
            try:
                i = q.get_nowait()
            except queue.Empty:
                return
            one(wt, i)

    threads = [threading.Thread(target=worker, args=(wt,)) for wt in pool]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    return results, done, problems


def _last(msg):
    return (msg.strip().splitlines() or [""])[-1].strip()


def _judge(muts, results, done, retried=None):
    """(lines, exit code), in ORIGINAL mutation order whatever the completion order was.
    `retried` {i: (first death, second outcome)} adds a note under every re-observed line."""
    lines, fails, died = [], 0, []
    retried = retried or {}
    for i in range(len(muts)):
        label, _path, _m, needle, want = muts[i]
        out = results.get(i, ("DIED", 2, "this mutation NEVER RAN", False))
        if out[0] == "NOAPPLY":
            lines.append("  !! %-52s MUTATION DID NOT APPLY — anchor missing" % label)
            fails += 1
        elif out[0] == "DIED":
            lines.append("  !! %-52s DIED — %s" % (label, _last(out[2])))
            died.append(out)
        else:
            got = out[1]
            ok = (got == want)
            fails += 0 if ok else 1
            lines.append("  %-6s %-52s row[%s]=%s (want %s)"
                         % ("PASS" if ok else "**FAIL", label, needle, got, want))
        if i in retried:
            first, second = retried[i]
            lines.append("         ^ RE-OBSERVED once at concurrency 1 after it DIED in the pool "
                         "(%s); second observation: %s"
                         % (_last(first[2]), "DIED again — " + _last(second[2])
                            if second[0] == "DIED" else "verdict above"))
    if died:
        lines += ["", "  ** %d mutation(s) could NOT be observed — no RESULT is claimed. First:"
                  % len(died), died[0][2].rstrip()]
        return lines, died[0][1]
    lines += ["", "  RESULT: %d of %d behaved as required" % (len(muts) - fails, len(muts))]
    if fails:
        lines += ["  ** A behavioural route did not respond to a real neuter. `CLAUDE.md` rung 5 and",
                  "     the stopping rule in queue/: this is the FOURTH defeat of this control, and",
                  "     the answer is to GIVE UP THE EXEMPTION, not to write attempt five. **"]
    return lines, 1 if fails else 0


def _execute(muts, pool, order, run_one):
    """Dispatch, re-observe deaths once, then judge. A pool problem (a mutation missing or run
    twice) exits 2.

    ⭐ THE RETRY IS FOR THE UNOBSERVABLE, NEVER FOR A VERDICT (2026-10-04). At K=13 two prepush
    observations died because load made an unrelated leg fail inside the child, which pre-empted the
    routing count. So a mutation that DIED — and only one whose OBSERVATION died, never a pool
    defect — is observed ONCE more, after the pool has drained, at concurrency 1, in an idle pool
    worktree. A mutation that produced a verdict, PASS or FAIL, is never re-run: a retry may make an
    unreadable run readable and can never overturn what was read. Dying twice leaves DIED standing,
    and every re-observed line says so beneath it."""
    results, done, problems = _dispatch(pool, order, run_one)
    retried = {}
    redo = [i for i in sorted(results) if results[i][0] == "DIED" and results[i][3]]
    if redo:
        again, _done, more = _dispatch([pool[0]], redo, run_one)
        problems += more
        for i in redo:
            second = again.get(i, ("DIED", 2, "the re-observation NEVER RAN", False))
            retried[i] = (results[i], second)
            if second[0] != "DIED":
                results[i] = second
    missing = [i for i in range(len(muts)) if i not in results]
    if missing:
        problems.append("%d of %d mutation(s) never ran: %s"
                        % (len(missing), len(muts), ", ".join(muts[i][0].strip() for i in missing)))
    lines, code = _judge(muts, results, done, retried)
    if problems:
        lines += ["", "  ** THE POOL COULD NOT JUDGE — refusing (exit 2):"] + \
                 ["     %s" % p for p in problems]
        code = 2
    return lines, code


def main():
    tmp = tempfile.mkdtemp(prefix="zp_routing_probe_")
    wt = os.path.join(tmp, "wt")
    created = []            # every worktree registered, so `finally` removes each one
    bg = None               # the background pool build, joined before any teardown
    print("%s — mutation control for the behavioural routing routes" % SELF)
    add = _add_worktree(wt)
    if add.returncode != 0:
        print("  cannot provision a worktree — REFUSING to run in the shared tree.")
        print(  (add.stdout + add.stderr).strip()[:500])
        shutil.rmtree(tmp, ignore_errors=True)
        return 2
    created.append(wt)
    try:
        # The worktree is at HEAD; copy the WORKING copies in, so the control tests what is about to
        # be committed rather than what already was.
        #
        # ⚠⚠ THE WHOLE BUNDLE, NOT A HAND-KEPT LIST. This was seven hardcoded names while the
        # routed set is 96 entries, so 89 of them — INCLUDING `record.py` — ran from HEAD inside
        # the worktree. Measured by /rely 2026-08-25: planting a fail-open in `record.py` (routed,
        # and staged-modified at the time) that serves a fabricated `rely` record took
        # `batch.py prepush` from 4 routing failures to 2 — the `[logic]`, `[switch]` and `[docs]`
        # hash legs all vanished — while THIS probe still printed `13 of 13`, exit 0.
        #
        # The comment here used to say the copy exists "so the control tests what is about to be
        # committed rather than what already was". That was true for seven files and false for
        # eighty-nine, and a control whose stated scope is wider than its real one is the third
        # instance of `DC-22` found in this file in three rounds. Copying the directory removes
        # the hand-kept list entirely, so it cannot drift again as files are added.
        _copied = _seed(wt)
        # ⚠ SAY WHAT WAS COVERED. `probe-red` means something is broken; `probe-green` means only
        # that the copied set enforces. Routed files OUTSIDE this bundle still run from HEAD.
        print("  worktree seeded with %d working-tree file(s) from tools/verify/" % _copied)
        print("  (routed entries outside tools/verify/ run from HEAD — probe-green is scoped to "
              "the bundle)")
        ship = os.path.join(wt, "tools", "verify", "ship.py")
        batch = os.path.join(wt, "tools", "verify", "batch.py")
        muts = mutations(ship, batch)
        needles = sorted({m[3] for m in muts})

        # -- the pool, built IN THE BACKGROUND while the primary runs its preconditions ----------
        # ⚠ Nothing the pool does feeds the zero point, the controls or the baseline below — they
        # run exactly as before, in the primary, in order. The pool only has to END in the state
        # the primary reaches, and `_pool_problems` checks that after the baseline, before any
        # mutation is dispatched. Overlapping saves the pool's own ~60 s baseline.
        k = _workers(len(muts))
        paths = [os.path.join(tmp, "pool%d" % j) for j in range(1, k)]
        pool_box = {"states": {}, "problems": ["the pool build never finished"]}

        def _state_of(p):
            o, r = _baseline_obs(p, needles)
            return {"tree": _tree_state(p), "obs": o, "rows": r}

        def _bg():
            try:
                pool_box["states"], pool_box["problems"] = _build_pool(
                    paths, _provision, _state_of, created)
            except BaseException as e:                  # noqa: BLE001
                pool_box["problems"] = ["the pool build died — %s" % _why(e)]
        if paths:
            bg = threading.Thread(target=_bg)
            bg.start()

        # ⭐⭐ RLY41-1: CONSTRUCT the failing baseline. See the block above `mutations()`.
        # ⚠ B BEFORE A, and the order is load-bearing: B asserts a CLEAN index as its own
        # precondition and restores it, while A is left STAGED on purpose because it IS the red
        # baseline the consumer-neuter cases below are measured against. A first would trip B's
        # precondition and the failure would look like a defect in B.
        print("  controls (routing membership is the only variable):")
        # ⚠⚠ THE ZERO POINT, AND DROPPING IT WAS A REAL DEFECT IN THE FIRST DRAFT OF THIS PAIR.
        # A/B controls for routing MEMBERSHIP, but only if the unperturbed tree reads (0, 0). If it
        # does not, B's `routing > 0` is not attributable to B's subject at all — it was already
        # there — and the probe would report "the routing SCOPE is wrong" about a file that matches
        # no routed prefix. Measured 2026-08-29: the first run did exactly that, blaming
        # `scripts/fonts/DejaVuSans.ttf` for a routing count it had not caused.
        #
        # ⚠ This was in the design as an explicit precondition and I removed it as redundant to the
        # A/B pair. It is not redundant: A/B establishes a DIFFERENCE, and a difference is only
        # attributable from a known origin. Restored, and asserted rather than assumed.
        _r0, _c0 = _prepush_exit(wt)
        print("    zero point        unperturbed (index clean)          routing=%d exit=%d"
              % (_r0, _c0))
        if _r0 or _c0:
            print("    ** ZERO POINT IS NOT ZERO — the unperturbed tree already blocks. **")
            print("       Neither control below can attribute anything: any red they produce was")
            print("       already present. This is NOT a licence to subtract a baseline; a probe")
            print("       that measures from a moving origin is the defect, not the arithmetic.")
            print("       Fix the tree (or the invocation) so the unperturbed run is (0, 0).")
            return 2
        if not _require_suppressed(wt, _B_SUBJECT):
            return 2
        _fired = _require_fires(wt, _A_SUBJECT)
        if _fired is None:
            return 2
        _a_path, _a_original = _fired

        obs, base = _baseline_obs(wt, needles)
        print("  baseline (unmutated):")
        bad = 0
        for n in needles:
            if n == EXIT_NEEDLE:
                # ⚠⚠ THE PRECONDITION, AND WITHOUT IT THE EXIT-CODE CASES PROVE NOTHING. Discarding
                # the verdict is only observable while there IS a verdict to discard: on a fully
                # green tree prepush exits 0 either way and the mutation looks harmless.
                #
                # ⚠⚠ THE FAILING STATE IS **CONSTRUCTED BY `_require_fires` ABOVE**, AND IS NOT
                # INHERITED. This comment used to say the worktree supplied it "for free" — detached
                # at HEAD with `.claude-local/` gitignored, so the `/rely` signal was absent there
                # and the routing legs failed. **THAT MECHANISM IS RETIRED** (see the RLY41-1 block
                # above `mutations()`): review signals moved to ledger records keyed on
                # `(step, path, blob)`, so a detached worktree now gets the SAME answers as the main
                # checkout, and the free red vanished. The old text survived here for one round after
                # being quoted as retired forty lines up — two copies of one premise in one file,
                # `DC-28`, corrected 2026-08-29.
                #
                # ⛔ DO NOT DELETE `_require_fires` AS REDUNDANT. `BLOCKS` below is true only
                # BECAUSE A staged a perturbation of a routed subject; remove it and every case here
                # goes vacuous again, which is the exact state this control refused to certify.
                state = obs[n]
                print("    %-38s %s (prepush exit)" % (n, state))
                if state != "BLOCKS":
                    print("    ** BASELINE BROKEN: prepush already exits 0 unmutated, so the")
                    print("       consumer-neuter cases below cannot distinguish anything. **")
                    bad += 1
                continue
            print("    %-38s %s" % (n, _row_state(base, n)))
            if _row_state(base, n) != "ok":
                print("    ** BASELINE BROKEN for %r — every verdict below is meaningless **" % n)
                bad += 1
        if bad:
            return 2

        # -- the pool: K-1 more worktrees, each REQUIRED to match the primary before use --------
        pool = [wt]
        if paths:
            _t0 = time.time()
            bg.join()
            bg = None
            ref = {"tree": _tree_state(wt), "obs": obs, "rows": base}
            problems = _pool_problems(paths, pool_box["states"], pool_box["problems"], ref)
            if problems or len(created) != k:
                print("  ** POOL REFUSED — %d of %d extra worktree(s) unusable; NO mutation runs. **"
                      % (len(problems), len(paths)))
                for p in problems:
                    print("     %s" % p)
                return 2
            pool += paths
            print("  pool: %d worktree(s) provisioned, each matching the primary's tree and baseline"
                  " (waited %.1fs after the baseline)" % (len(paths), time.time() - _t0))
        muts_by_wt = {w: mutations(os.path.join(w, "tools", "verify", "ship.py"),
                                   os.path.join(w, "tools", "verify", "batch.py")) for w in pool}
        pristine = {m[1]: _read(m[1]) for w in pool for m in muts_by_wt[w]}
        # The four cheap `batch.py prepush` observations (EXIT_NEEDLE, ~2 s) go FIRST, before the
        # pool fills with guards.py runs (~35 s each): measured at K=13 (2026-10-04), prepush runs
        # dispatched LAST overlapped ~9 heavy runs and two died of the load. K=1 keeps the original
        # order exactly. Output is in ORIGINAL order either way (`_judge`).
        order = (list(range(len(muts))) if k == 1 else
                 sorted(range(len(muts)), key=lambda i: muts[i][3] != EXIT_NEEDLE))
        print()
        _t0 = time.time()
        lines, code = _execute(muts, pool, order, _make_runner(muts_by_wt, _observe, pristine))
        for line in lines:
            print(line)
        print("  (%d mutation(s) across %d worktree(s), %s=%s: %.1fs)"
              % (len(muts), len(pool), WORKERS_ENV, os.environ.get(WORKERS_ENV, "<default>"),
                 time.time() - _t0))
        return code
    finally:
        if bg is not None:          # never tear down while the pool build may still add one
            bg.join()
        with _GIT_LOCK:
            for p in created:
                subprocess.run(["git", "worktree", "remove", "--force", p],
                               capture_output=True, text=True, cwd=REPO)
            subprocess.run(["git", "worktree", "prune"], capture_output=True, text=True, cwd=REPO)
        shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------------- pool controls (--selftest)
# (label, control, anchor, replacement), hooks.py's `_CONTROLS` shape: each control must PASS on
# the live module and FAIL on the mutant built by replacing ONE anchor ABOVE the marker below. The
# controls drive the REAL `_execute`/`_build_pool` with stub observers over scratch files, so they
# test the pool machinery in seconds; the EQUIVALENCE of real verdicts is measured by running the
# probe at K=1 and K=N and diffing (see the commit that landed this).
_CONTROLS_MARK = "# " + "-" * 70 + " pool controls (--selftest)"


def _stub(mod, n, k, wrong=None, delays=None, dies=None):
    """Run mod._execute over n stub mutations on k scratch worktrees. Returns (lines, code, overlap).
    `dies` {i: "loaded"|"always"}: the observation raises (as an unreadable prepush does) when other
    observations are still in flight, or every time."""
    tmp = tempfile.mkdtemp(prefix="zp_probe_selftest_")
    try:
        pool = []
        for j in range(k):
            d = os.path.join(tmp, "w%d" % j)
            os.makedirs(d)
            mod._write(os.path.join(d, "f.txt"), "pristine\n")
            pool.append(d)

        def muts_for(w):
            return [("STUB-%02d" % i, os.path.join(w, "f.txt"),
                     (lambda s, i=i: s + "mutation %d\n" % i), "n%d" % i,
                     "WRONG" if i == wrong else "ok") for i in range(n)]
        muts_by_wt = {w: muts_for(w) for w in pool}
        pristine = {m[1]: mod._read(m[1]) for w in pool for m in muts_by_wt[w]}
        inflight, overlap, lock = {}, [], threading.Lock()
        total = [0]

        def observe(w, needle):
            i = int(needle[1:])
            with lock:
                inflight[w] = inflight.get(w, 0) + 1
                total[0] += 1
                if inflight[w] > 1:
                    overlap.append(w)
            time.sleep((delays or {}).get(i, 0.05))
            body = mod._read(os.path.join(w, "f.txt"))
            with lock:
                inflight[w] -= 1
                loaded = total[0] > 1
                total[0] -= 1
            mode = (dies or {}).get(i)
            if mode == "always" or (mode == "loaded" and loaded):
                raise SystemExit("stub: no routing count (%s)\n  raw prepush output: <stub %d>"
                                 % (mode, i))
            return "ok" if body == "pristine\nmutation %d\n" % i else "TRAMPLED"
        lines, code = mod._execute(muts_for(pool[0]), pool, list(range(n)),
                                   mod._make_runner(muts_by_wt, observe, pristine))
        return lines, code, overlap
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def _ctl_isolation(mod):
    lines, code, overlap = _stub(mod, 6, 3)
    ok = code == 0 and not overlap and "  RESULT: 6 of 6 behaved as required" in lines
    return ok, "K=3: exit %d, overlap seen by the stub on %s" % (code, sorted(set(overlap)) or "none")


def _ctl_count(mod):
    lines, code, _o = _stub(mod, 5, 2)
    ran = sum(1 for ln in lines if "STUB-" in ln and ln.lstrip().startswith("PASS"))
    ok = code == 0 and ran == 5 and "  RESULT: 5 of 5 behaved as required" in lines
    return ok, "K=2: exit %d, %d of 5 mutation lines PASS" % (code, ran)


def _ctl_fail_propagates(mod):
    lines, code, _o = _stub(mod, 5, 3, wrong=3)
    ok = code == 1 and "  RESULT: 4 of 5 behaved as required" in lines
    return ok, "K=3 with STUB-03 wanting WRONG: exit %d (must be 1)" % code


def _ctl_equivalence(mod):
    delays = {0: 0.30, 1: 0.20, 2: 0.10, 3: 0.0, 4: 0.0, 5: 0.0}
    one, c1, _o = _stub(mod, 6, 1, delays=delays)
    many, cn, _o = _stub(mod, 6, 3, delays=delays)
    ok = c1 == 0 and cn == 0 and one == many
    return ok, "K=1 vs K=3 (later jobs finish first): %s" % (
        "identical" if one == many else "DIFFER: %s" % [ln.strip()[:24] for ln in many if "STUB" in ln])


def _ctl_retry_recovers(mod):
    # STUB-02 is fast and finishes while the others are still in flight, so it dies in the pool;
    # alone, at concurrency 1, it reads. It must come back PASS, with the re-observation noted.
    delays = dict((i, 0.3) for i in range(6))
    delays[2] = 0.02
    lines, code, _o = _stub(mod, 6, 3, delays=delays, dies={2: "loaded"})
    noted = [ln for ln in lines if "RE-OBSERVED once at concurrency 1" in ln and "verdict above" in ln]
    ok = code == 0 and "  RESULT: 6 of 6 behaved as required" in lines and len(noted) == 1
    return ok, "dies only under load: exit %d, %d re-observation note(s)" % (code, len(noted))


def _ctl_retry_never_masks(mod):
    # STUB-02 dies every time. It must stay DIED (no RESULT, non-zero), AND the note must show it
    # WAS re-observed and died again — a probe that skipped the retry would not print that.
    lines, code, _o = _stub(mod, 5, 2, dies={2: "always"})
    again = [ln for ln in lines if "RE-OBSERVED" in ln and "DIED again" in ln]
    ok = (code == 1 and not any("RESULT:" in ln for ln in lines) and len(again) == 1
          and any("STUB-02" in ln and "DIED" in ln for ln in lines))
    return ok, "always dies: exit %d, %d 'DIED again' note(s), RESULT claimed: %s" % (
        code, len(again), any("RESULT:" in ln for ln in lines))


def _pool_case(mod, fail_at=None, differ_at=None):
    created, ref = [], {"tree": "same"}

    def prov(p, c):
        if p == fail_at:
            raise mod._CannotJudge("stub: git worktree add failed")
        c.append(p)

    def state_of(p):
        return {"tree": "DIFFERENT"} if p == differ_at else {"tree": "same"}
    paths = ["p1", "p2", "p3"]
    states, problems = mod._build_pool(paths, prov, state_of, created)
    return mod._pool_problems(paths, states, problems, ref)


def _ctl_provision_fails(mod):
    problems = _pool_case(mod, fail_at="p2")
    return bool(problems), "one worktree fails to provision -> %d problem(s)" % len(problems)


def _ctl_baseline_differs(mod):
    problems = _pool_case(mod, differ_at="p3")
    clean = _pool_case(mod)
    return bool(problems) and not clean, "one worktree reads another baseline -> %d problem(s); " \
        "identical pool -> %d" % (len(problems), len(clean))


_CONTROLS = [
    ("ISOLATION   two concurrent mutations never share a worktree", _ctl_isolation,
     "    threads = [threading.Thread(target=worker, args=(wt,)) for wt in pool]",
     "    threads = [threading.Thread(target=worker, args=(pool[0],)) for wt in pool]"),
    ("COUNT       a mutation dropped from the pool is caught", _ctl_count,
     "    for i in order:\n        q.put(i)",
     "    for i in order[:-1]:\n        q.put(i)"),
    ("FAIL        a wrong observation still exits 1", _ctl_fail_propagates,
     "            fails += 0 if ok else 1",
     "            fails += 0"),
    ("EQUIVALENCE K=N prints what K=1 prints, in original order", _ctl_equivalence,
     "    for i in range(len(muts)):\n        label, _path, _m, needle, want = muts[i]",
     "    for i in done:\n        label, _path, _m, needle, want = muts[i]"),
    ("PROVISION   a worktree that cannot be built refuses", _ctl_provision_fails,
     '                problems.append("%s: could NOT be provisioned — %s" % (p, _why(e)))',
     "                pass"),
    ("BASELINE    a worktree reading another baseline refuses", _ctl_baseline_differs,
     "        elif states[p] != ref:",
     "        elif False:"),
    ("RETRY       a death under load is re-observed once, and says so", _ctl_retry_recovers,
     "    if redo:\n        again, _done, more",
     "    if False:\n        again, _done, more"),
    ("RETRY       a death that recurs stays DIED after its re-observation", _ctl_retry_never_masks,
     "    if redo:\n        again, _done, more",
     "    if False:\n        again, _done, more"),
]


def _mutant(anchor, repl):
    """(module, None) from this file's source with ONE anchor above the marker replaced, or
    (None, why) — a mutation that does not apply fails the suite rather than retiring a control."""
    import types
    src_path = os.path.abspath(__file__)
    with io.open(src_path, encoding="utf-8") as fh:
        src = fh.read()
    head, sep, tail = src.partition(_CONTROLS_MARK)
    if head.count(anchor) != 1:
        return None, "MUTATION DID NOT APPLY — anchor found %d time(s)" % head.count(anchor)
    mod = types.ModuleType("zp_probe_mutant")
    mod.__file__ = src_path
    try:
        exec(compile(head.replace(anchor, repl, 1) + sep + tail, src_path + ".mutant", "exec"),
             mod.__dict__)
    except SyntaxError as e:
        return None, "MUTATION DID NOT APPLY — mutant does not compile: %s" % (e,)
    return mod, None


def selftest():
    me = sys.modules[__name__]
    print("%s --selftest — pool controls (each: MUST PASS live, MUST FIRE on its mutant)" % SELF)
    bad = 0
    for label, ctl, anchor, repl in _CONTROLS:
        try:
            ok_live, why_live = ctl(me)
        except Exception as e:                              # noqa: BLE001 — a raise is a failure
            ok_live, why_live = False, "raised %r" % (e,)
        mod, err = _mutant(anchor, repl)
        if mod is None:
            ok_mut, why_mut = True, err                     # True = the mutant "passed" = FAIL
        else:
            try:
                ok_mut, why_mut = ctl(mod)
            except Exception as e:                          # noqa: BLE001 — a crash is not a catch
                ok_mut, why_mut = True, "mutant raised %r, which proves nothing" % (e,)
        good = ok_live and not ok_mut
        bad += 0 if good else 1
        print("  %-4s %-58s live: %s" % ("ok" if good else "FAIL", label, why_live))
        print("       %-58s mutant fired: %s — %s" % ("", "yes" if not ok_mut else "NO", why_mut))
    print("  selftest: %d of %d control(s) passed live AND fired on their mutant"
          % (len(_CONTROLS) - bad, len(_CONTROLS)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(selftest() if "--selftest" in sys.argv[1:] else main())
