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

    python tools/verify/probe_routing_behavioural.py [--mutations]
    python tools/verify/probe_routing_behavioural.py --selftest     # the probe's own controls
                                                                    # (a BLOCK leg of every push)
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
    return _count_from(*_run_prepush(wt), wt=wt)


def _run_prepush(wt, overlay=None):
    """(combined output, exit code) of ONE nested `batch.py prepush --ranges HEAD~1..HEAD` in `wt`.
    Every observable below reads this run; none re-implements it. `overlay`: see `_OVERLAY`."""
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
    real = os.path.join(wt, "tools", "verify", "batch.py")
    argv = ["prepush", "--ranges", "HEAD~1..HEAD"]
    made = []
    try:
        if overlay is None:
            cmd = [sys.executable, real] + argv
        else:
            # `overlay` is batch.py SOURCE to EXECUTE in place of the bytes on disk — see `_OVERLAY`.
            for body in (_OVERLAY_LAUNCHER, overlay):
                fd, p = tempfile.mkstemp(prefix="zp_probe_overlay_", suffix=".py")
                with io.open(fd, "w", encoding="utf-8", newline="\n") as fh:
                    fh.write(body)
                made.append(p)
            cmd = [sys.executable, made[0], real, made[1]] + argv
        p = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace",
                           cwd=wt, env={**os.environ, "ZP_AGENT_GATE": "0"})
    finally:
        for f in made:
            try:
                os.remove(f)
            except OSError:
                pass
    return p.stdout + p.stderr, p.returncode


# ⭐⭐ `_OVERLAY` — RELY-CC-6 (2026-10-04): HOW A MUTATION IS OBSERVED IN THE ROUTING-CLEAN STATE.
# The agreement check matters ONLY at routing == 0 (above zero the push is refused anyway), and an
# on-disk edit of `batch.py` can never be observed there: `batch.py` is a routed CHECKER, so editing
# it makes `moved` fire (red BY ABSENCE unstaged, BY MISMATCH staged). Measured in this change's
# worktree: unperturbed `prepush PASS`; the same tree with `_SYNTH_FAIL` written to disk,
# "3 push check(s) failed — 2 routing, 1 other". So the clean-phase rows leave the routed BYTES
# untouched and EXECUTE the mutated source instead: this launcher runs it as `__main__` with
# `__file__` and `sys.path[0]` set to the real `batch.py`, which models a weakening that was
# already reviewed and committed, the state in which nothing but the enforcement stands in the way.
_OVERLAY_LAUNCHER = (
    "import io, os, sys\n"
    "real, src = sys.argv[1], sys.argv[2]\n"
    "sys.argv = [real] + sys.argv[3:]\n"
    "sys.path[0] = os.path.dirname(real)\n"
    "g = {'__name__': '__main__', '__file__': real, '__builtins__': __builtins__}\n"
    "exec(compile(io.open(src, encoding='utf-8').read(), real, 'exec'), g)\n")


class _RefusalUnread(SystemExit):
    """The nested prepush REACHED `enforce_prepush_verdict` and it REFUSED, in a form the observable
    asking could not read. That is a VERDICT, not a transport failure, so `_attempt` marks it NEVER
    re-observable (RELY-CC-1: a retry replaced exactly such a death with a vacuous pass)."""


def _died(e, out, rc, wt):
    """Re-raise an unreadable observation with the child's raw output saved, TYPED by that output.

    ⚠ KEEP THE EVIDENCE. An unreadable run used to be reported by its symptom alone, with the child's
    output discarded — so the K=13 measurement (2026-10-04) could name WHICH observation died but not
    WHY. The raw output goes to a file OUTSIDE the tree and the path rides along.
    ⚠⚠ AND THE TYPE IS DECIDED BY THE RAW OUTPUT, NOT BY WHICH BRANCH RAISED: if the enforcement's own
    refusal is anywhere in it, the death is a refusal (`_RefusalUnread`) whatever else went wrong."""
    fd, raw = tempfile.mkstemp(prefix="zp_probe_prepush_", suffix=".log")
    with io.open(fd, "w", encoding="utf-8") as fh:
        fh.write("cwd: %s\nexit: %d\n\n%s" % (wt, rc, out))
    msg = "%s\n  raw prepush output: %s" % (e.code, raw)
    if any(n in out for n in _ENFORCE_DIE):
        raise _RefusalUnread(msg)
    raise SystemExit(msg)


def _count_from(out, rc, wt="?"):
    """(routing count, exit code) read from one prepush run's output — see `_prepush_exit`."""
    try:
        _assert_reached(out)
        m = re.search(r"push check\(s\) failed\s*[—-]\s*(\d+)\s+routing", out)
        if m:
            return int(m.group(1)), rc
        # `prepush PASS` means the enforcement ran and found nothing: zero routing failures.
        if _ENFORCE_OK in out:
            return 0, rc
        raise SystemExit(
            "probe could not read a ROUTING COUNT from prepush, and must not fall back to the exit\n"
            "  code alone — that is the over-determined observable this leg exists to stop using.")
    except SystemExit as e:
        _died(e, out, rc, wt)


# ⭐⭐ RELY-CC-1 (2026-10-04): THE SECOND OBSERVABLE, AND WHY THE ROUTING COUNT COULD NOT JUDGE RLYB4.
# `RLYB4-1`/`RLYB4-1b` exist for `enforce_prepush_verdict`'s AGREEMENT CHECK (recorded leg failures
# must equal displayed FAIL rows, else "push verdict INCONSISTENT"). `/rely` measured them VACUOUS
# under the count observable: the constructed baseline always has routing > 0, so `BLOCKS` held with
# the agreement check DELETED (`if _legs != len(_DISPLAYED_FAILS):` -> `if False:`). The check only
# fires when a NON-routing inline leg FAILS, and then it `die()`s before the `%d routing` line, so the
# count observable read nothing and recorded DIED — the K=13 deaths, reproduced deterministically.
# So these cases now CONSTRUCT that state (`_SYNTH_FAIL`) and read WHICH refusal the enforcement
# reached, conjoined with the exit code (say AND do, the `_prepush_blocks` lesson).
# ⚠⚠ RELY-CC-6, THE SAME ROOT ONE LEVEL DOWN: read with A staged, every one of those words was a
# refusal, so the rows told apart WHICH MESSAGE printed and never WHETHER THE PUSH WAS REFUSED, and
# /rely moved the check inside `if any(_VERDICT.values()):` (V3) with all rows green while the real
# enforcement let RLYB4-1 through. So REFUSAL_NEEDLE rows now run ONLY in the ROUTING-CLEAN phase
# (`_clean_phase`: the zero-point tree, index clean, the mutation EXECUTED through `_OVERLAY`), where
# `PASS` means the push PROCEEDS. The words:
#     INCONSISTENT · INCOMPLETE · FAILED · PASS   -> the refusal reached, process agreed
#     <kind>-BUT-EXIT-0 / PASS-BUT-EXIT-<n>       -> the two halves disagree (never a want)
#     MIXED(...)                                  -> more than one refusal printed (never a want)
REFUSAL_NEEDLE = "__prepush_refusal__"
_REFUSAL_KINDS = (("push verdict INCONSISTENT", "INCONSISTENT"),
                  ("push verdict incomplete", "INCOMPLETE"),
                  ("push check(s) failed", "FAILED"))


def _refusal_from(out, rc, wt="?"):
    """The refusal one prepush run reached, as a word — see the block above. Unreadable -> raises."""
    try:
        _assert_reached(out)
        kinds = [k for needle, k in _REFUSAL_KINDS if needle in out]
        if len(kinds) > 1:
            return "MIXED(%s)" % "+".join(kinds)
        kind = kinds[0] if kinds else "PASS"      # `_assert_reached` guarantees PASS when no die
        refused = kind != "PASS"
        if refused and rc == 0:
            return kind + "-BUT-EXIT-0"
        if not refused and rc != 0:
            return "PASS-BUT-EXIT-%d" % rc
        return kind
    except SystemExit as e:
        _died(e, out, rc, wt)


def _prepush_refusal(wt, overlay=None):
    return _refusal_from(*_run_prepush(wt, overlay), wt=wt)


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


# The RLYB4 surface of `batch.py`, as (anchor, replacement) pairs NAMED ONCE so each case and its
# meta-control compose the identical edits.
# ⚠ `_SYNTH_FAIL` IS THE PRECONDITION, NOT A MUTATION: it forces the `purity` inline leg to FAIL at
#   the print site, so a FAIL row is displayed and a 1 is recorded — the state in which the agreement
#   check has something to compare. It lives only in the worktree's copy, restored with the rest.
#   Chosen over a real failing leg because a real one (deleting `ssot.json`, renaming the decl
#   baseline) would change the worktree STATE every pool member is compared on, for two cases.
_SYNTH_FAIL = ('        print("  %-18s %-4s %s" % (name, "ok" if ok else "FAIL", why))',
               '        ok = False if key == "purity" else ok\n'
               '        print("  %-18s %-4s %s" % (name, "ok" if ok else "FAIL", why))')
_RLYB4_1 = ("        verdict_record(key, 0 if ok else 1)",
            "        verdict_record(key, (0 if ok else 1) * 0)")
_RLYB4_1B = ("        if not ok:\n            display_fail(key)\n", "        pass\n")
_NO_AGREE = ("    if _legs != len(_DISPLAYED_FAILS):", "    if False:")
# The refusal branch itself: the PRECOND row's protection (an honest FAIL refuses only through it).
_REFUSE_BRANCH = "    if any(_VERDICT.values()):\n"
_NO_REFUSE = (_REFUSE_BRANCH, "    if False:\n")
# ⚠ /rely r2's two weakenings, VERBATIM (`rely_concurrency_r2/variants.py`). Each keeps every anchor
#   above present exactly once and disables the agreement check only where routing == 0.
_AGREE_BLOCK = (
    '    _legs = sum(v for k, v in _VERDICT.items() if k != "routing")\n'
    '    if _legs != len(_DISPLAYED_FAILS):\n'
    '        die("push verdict INCONSISTENT — %d leg failure(s) RECORDED but %d FAIL row(s) DISPLAYED "\n'
    '            "(%s). One of the two was tampered with or dropped; a count that disagrees with the "\n'
    '            "screen cannot be acted on either way, so this refuses rather than picking one."\n'
    '            % (_legs, len(_DISPLAYED_FAILS), ", ".join(_DISPLAYED_FAILS) or "none displayed"))\n')
# V3: the check moved INSIDE the refusal branch ("cross-check only when refusing anyway").
_V3 = ((_AGREE_BLOCK, ""),
       (_REFUSE_BRANCH, _REFUSE_BRANCH + "".join(("    " + ln if ln.strip() else ln)
                                                 for ln in _AGREE_BLOCK.splitlines(True))))
# V4: one inserted statement before the unchanged check.
_V4 = ((_AGREE_BLOCK,
        "    if not any(_VERDICT.values()):\n        del _DISPLAYED_FAILS[:]\n" + _AGREE_BLOCK),)

# Row labels named ONCE: `mutations()` and the vacuity table (`_VACUITY`) must name the same rows.
L_PRE = "PRECOND  _SYNTH_FAIL alone: an honest purity FAIL"
L_PRE_META = "META     PRECOND with the refusal branch DELETED"
L_B4_1 = "RLYB4-1  producer annihilates its own recorded count"
L_B4_1B = "RLYB4-1b the display tally is dropped"
L_B4_1_META = "META     RLYB4-1 with the agreement check DELETED"
L_B4_1B_META = "META     RLYB4-1b with the agreement check DELETED"
L_B4_1_V3 = "META-V3  RLYB4-1, check moved inside the refusal branch"
L_B4_1_V4 = "META-V4  RLYB4-1, tally cleared when nothing is recorded"


def _apply_all(*edits):
    """A transform applying every (anchor, replacement) in order, or NONE of them: if any anchor is
    not present exactly once at its turn, the source comes back unchanged, which `_make_runner`
    reports as NOAPPLY. Half a composition is never observed."""
    def go(s):
        out = s
        for a, b in edits:
            if out.count(a) != 1:
                return s
            out = out.replace(a, b, 1)
        return out
    return go


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
        # MUST READ `INCONSISTENT`: `display_fail` tallies what reached the SCREEN, so a recorded zero
        # disagrees with a displayed FAIL and `enforce_prepush_verdict` refuses on the mismatch.
        # ⚠⚠ ONLY OBSERVABLE WITH A FAILING NON-ROUTING LEG (`_SYNTH_FAIL`, same edit) AND ONLY AT
        # ROUTING == 0 (RELY-CC-6): every REFUSAL_NEEDLE row runs in `_clean_phase`, never in the pool.
        # The observable is whether the PUSH IS REFUSED (exit code AND refusal word), so each row
        # below differs from its PRECOND only through the check it names:
        #     PRECOND (honest FAIL)        FAILED        refused by the refusal branch
        #     RLYB4-1 / RLYB4-1b           INCONSISTENT  refused by the agreement check
        #     META RLYB4-1 (check gone)    PASS          the push PROCEEDS over a displayed FAIL
        #     META RLYB4-1b (check gone)   FAILED        still refused: the RECORD holds the 1, so
        #                                                deleting the check costs only the screen
        (L_PRE, batch, _apply_all(_SYNTH_FAIL), REFUSAL_NEEDLE, "FAILED"),
        (L_PRE_META, batch, _apply_all(_SYNTH_FAIL, _NO_REFUSE), REFUSAL_NEEDLE, "PASS"),
        (L_B4_1, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1), REFUSAL_NEEDLE, "INCONSISTENT"),
        # The other half of the same property: drop the DISPLAY tally instead of the record. It must
        # fail closed in this direction too, or the agreement check is a one-way ratchet that a
        # single deletion walks past.
        (L_B4_1B, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1B), REFUSAL_NEEDLE, "INCONSISTENT"),
        # ⭐ THE META-CONTROLS (RELY-CC-1, RELY-CC-6): the same compositions with the protection
        # DELETED or WEAKENED, built from the SAME named tuples so case and meta cannot drift. Each
        # pair is checked by `_VACUITY` to differ in want and to compose exactly row + deletion.
        (L_B4_1_META, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1, _NO_AGREE), REFUSAL_NEEDLE, "PASS"),
        (L_B4_1B_META, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1B, _NO_AGREE), REFUSAL_NEEDLE,
         "FAILED"),
        (L_B4_1_V3, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1, *_V3), REFUSAL_NEEDLE, "PASS"),
        (L_B4_1_V4, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1, *_V4), REFUSAL_NEEDLE, "PASS"),
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


# ⭐ RELY-CC-7: THE ROW COUNT IS PINNED. A deleted row used to shrink the denominator silently
# ("0 of 0" passed). `_pin_problems` refuses (exit 2) when this or `_EXPECTED_CONTROLS` disagrees with
# the list, and `hooks.py`'s routing-control plan line states the same number. ⚠ Same-file pinning:
# it catches an UNCOORDINATED deletion only; one edit changing row and constant together passes.
_EXPECTED_MUTATIONS = 23

# ⭐⭐ THE VACUITY DETECTOR (DC: "a mutation row observed in a state that masks the property it
# names"; RELY-CC-1 and RELY-CC-6 are its two instances). A row is VACUOUS when its observation does
# not change once the protection it names is deleted. For each COVERED row the table names a paired
# row composing EXACTLY that row's transform plus the deletion; `_ctl_vacuity` asserts, on the real
# `batch.py` source, that the pair composes so and that the two WANTS DIFFER, and the probe run then
# requires both observations — so a pair that both PASS is an observed flip. (row, pair, edits)
_VACUITY = (
    (L_PRE, L_PRE_META, (_NO_REFUSE,)),
    (L_B4_1, L_B4_1_META, (_NO_AGREE,)),
    (L_B4_1B, L_B4_1B_META, (_NO_AGREE,)),
    (L_B4_1, L_B4_1_V3, _V3),
    (L_B4_1, L_B4_1_V4, _V4),
)
# Rows NOT covered, and why — every row is in exactly one of `_VACUITY` (as row or pair) or here.
_GUARDS_ROUTE = ("its protection is a guards.py ROUTE (the detector the row reads), another file: "
                 "no single same-file deletion expresses it; baseline-ok vs want-FAIL only shows the "
                 "mutation moves the row")
_STAY_GREEN = "a MUST-STAY-GREEN row: its claim is indifference, not a protection that can be deleted"
_EXIT_HALF = ("its protection is the probe's own exit conjunct (`_prepush_blocks`); covered at unit "
              "level by the CONJUNCTION control in --selftest, not end to end")
_VACUITY_UNCOVERED = {
    "RLY27-1  one space before the arg list": _STAY_GREEN,
    "RLY27-3  list(...) wrapper around the call": _STAY_GREEN,
    "RLY28-1  caller annihilates the return value": _STAY_GREEN,
    "NEUTER   release gate `if False:`": _GUARDS_ROUTE,
    "RLY27-7  release gate prints the flag, obeys nothing": _GUARDS_ROUTE,
    "RLY27-2  release gate as a comprehension with `and False`": _GUARDS_ROUTE,
    "NEUTER   release gate drops `and blocking`": _GUARDS_ROUTE,
    "RLY27-4  verdict counts a sequence it did not print": _GUARDS_ROUTE,
    "NEUTER   cmd_prepush never calls routing_verdict": _GUARDS_ROUTE,
    "NEUTER   the producer stops recording its count": _GUARDS_ROUTE,
    "NEUTER   the logic leg downgraded to non-blocking": _GUARDS_ROUTE,
    "B4       `_EXPECTED` quietly loses a gating leg": _GUARDS_ROUTE,
    "NEUTER   cmd_prepush discards the enforcement call": _GUARDS_ROUTE,
    "RLY36-1a consumer swallows the refusal (try/except SystemExit)": _EXIT_HALF,
    "RLY36-1b the refusal primitive exits 0": _EXIT_HALF,
}


def _vacuity_problems(muts, src):
    """Every way the vacuity table fails to hold over `muts` and the real `batch.py` source `src`."""
    by = {m[0]: m for m in muts}
    out = []
    named = set(_VACUITY_UNCOVERED)
    for row, pair, edits in _VACUITY:
        named |= {row, pair}
        if row not in by or pair not in by:
            out.append("vacuity pair names a missing row: %r / %r" % (row, pair))
            continue
        r, p = by[row], by[pair]
        if r[4] == p[4]:
            out.append("%r and its pair %r WANT the same state (%s): no flip is required"
                       % (row, pair, r[4]))
        if (r[1], r[3]) != (p[1], p[3]):
            out.append("%r and %r differ in file or observable" % (row, pair))
        rs = r[2](src)
        if rs == src:
            out.append("%r does not apply to batch.py" % row)
        elif p[2](src) != _apply_all(*edits)(rs) or p[2](src) == rs:
            out.append("%r is not EXACTLY %r plus its deletion" % (pair, row))
    for m in muts:
        if m[0] not in named:
            out.append("row %r is neither covered by a vacuity pair nor listed as uncovered" % m[0])
    out += ["%r is listed but is not a row" % k for k in sorted(named - set(by))]
    return out


def _pin_problems():
    """RELY-CC-7: every way the row and control counts disagree with their pins (here and in
    `hooks.py`'s plan line). Non-empty -> `_cli` refuses with exit 2 before running anything."""
    out = []
    n = len(mutations("ship.py", "batch.py"))
    if n != _EXPECTED_MUTATIONS:
        out.append("mutations() holds %d row(s), pinned at %d" % (n, _EXPECTED_MUTATIONS))
    c = len(_CONTROLS)
    if c != _EXPECTED_CONTROLS:
        out.append("_CONTROLS holds %d control(s), pinned at %d" % (c, _EXPECTED_CONTROLS))
    hooks = os.path.join(os.path.dirname(os.path.abspath(__file__)), "hooks.py")
    try:
        txt = _read(hooks)
    except OSError as e:
        return out + ["cannot read hooks.py to check its stated counts: %s" % e]
    for phrase in ("%d probe mutation rows" % _EXPECTED_MUTATIONS,
                   "%d probe controls" % _EXPECTED_CONTROLS):
        if phrase not in txt:
            out.append("hooks.py's plan does not state %r" % phrase)
    return out


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
# ⚠ REFUSAL rows never reach the pool (RELY-CC-6): A staged masks them. They run first, in the
# primary's ROUTING-CLEAN phase (`_clean_phase`), verified against the zero point's own state.
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


def _seed_drift(wt):
    """Repo-relative paths whose bytes in `wt` differ from the `_seed` source (or are missing)."""
    out = []
    for root, dirs, files in os.walk(os.path.join(REPO, "tools", "verify")):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        for f in files:
            src = os.path.join(root, f)
            rel = os.path.relpath(src, REPO)
            dst = os.path.join(wt, rel)
            with io.open(src, "rb") as a:
                want = a.read()
            try:
                with io.open(dst, "rb") as b:
                    same = b.read() == want
            except OSError:
                same = False
            if not same:
                out.append(rel.replace("\\", "/"))
    return sorted(out)


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
        if n == REFUSAL_NEEDLE:
            raise _CannotJudge("REFUSAL rows are observed only in the routing-clean phase "
                               "(`_clean_phase`), never with A staged — RELY-CC-6")
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
    if needle == REFUSAL_NEEDLE:
        raise _CannotJudge("a REFUSAL row reached the pool observer; it is observed only in the "
                           "routing-clean phase (`_clean_phase`) — RELY-CC-6")
    _rc, rows = _guards_rows(wt)
    return _row_state(rows, needle)


def _make_overlay_runner(muts, pristine):
    """run_one(wt, i) for the ROUTING-CLEAN phase: the mutated `batch.py` source is EXECUTED through
    `_OVERLAY` and never written, so the routed bytes (and therefore routing) stay at the zero point."""
    def run_one(wt, i):
        label, path, mutate, needle, _want = muts[i]
        if needle != REFUSAL_NEEDLE or os.path.basename(path) != "batch.py":
            raise _CannotJudge("%r is not a batch.py REFUSAL row; the clean phase runs only those"
                               % label.strip())
        original = _read(path)
        if original != pristine[path]:
            raise _CannotJudge("%s is not pristine before %r" % (path, label.strip()))
        mutated = mutate(original)
        if mutated == original:
            return ("NOAPPLY",)
        got = _prepush_refusal(wt, overlay=mutated)
        if _read(path) != original:
            raise _CannotJudge("the overlay run of %r changed %s ON DISK" % (label.strip(), path))
        return ("GOT", got)
    return run_one


def _clean_phase(wt, muts, idx, zero_state):
    """Observe the REFUSAL rows `idx` in the ROUTING-CLEAN state — the zero point's own tree (index
    clean, bundle bytes as seeded), before A is staged. Returns (results, retried, problems, done), or 2
    when the state cannot be verified or its baseline is not a clean PASS.

    ⚠ THE STATE IS VERIFIED, NEVER ASSUMED: `_tree_state` must equal the zero point's before AND after,
    and the unmutated source run through the SAME overlay must read `PASS` (routing 0, exit 0) — so a
    row's refusal is attributable to its mutation, and the launcher itself is shown to perturb nothing."""
    def drift():
        now = _tree_state(wt)
        out = sorted(k for k in set(zero_state) | set(now) if zero_state.get(k) != now.get(k))
        if now["staged"]:
            out.append("index NOT clean: %s" % now["staged"])
        return out + ["bundle bytes differ from the seed: %s" % r for r in _seed_drift(wt)]
    d = drift()
    if d:
        print("    ** CLEAN PHASE REFUSED — the primary is not in its zero-point state (differs in: %s)"
              % ", ".join(d))
        return 2
    batch = os.path.join(wt, "tools", "verify", "batch.py")
    try:
        base = _prepush_refusal(wt, overlay=_read(batch))
    except SystemExit as e:
        print("    ** CLEAN PHASE could not read its baseline: %s" % _last(str(e.code)))
        return 2
    print("    clean baseline    unmutated source via overlay, index clean  refusal=%s" % base)
    if base != "PASS":
        print("    ** CLEAN BASELINE BROKEN: the routing-clean state must PASS unmutated, or no")
        print("       REFUSAL row below can attribute its refusal to its mutation. **")
        return 2
    pristine = {batch: _read(batch)}
    results, retried, problems, done = _observe_phase([wt], list(idx),
                                                      _make_overlay_runner(muts, pristine))
    d = drift()
    if d:
        problems.append("the clean phase left the primary out of its zero-point state (differs in: %s)"
                        % ", ".join(d))
    return results, retried, problems, done


def _attempt(wt, i, run_one, held, lock):
    """Run mutation `i` on `wt` -> its outcome. A death is ("DIED", code, message, re-observable?).

    ⚠ ONLY AN OBSERVATION THAT COULD NOT BE READ FOR A TRANSPORT-SHAPED REASON IS RE-OBSERVABLE: a
    crash, a run that never reached the enforcement, an unparsed exit. Three deaths never are:
      · an ISOLATION BREACH and a non-pristine refusal (`_CannotJudge`) — defects in the POOL, and a
        retry at concurrency 1 would hide exactly what the isolation control exists to catch;
      · `_RefusalUnread` — the enforcement RAN and REFUSED (RELY-CC-1). That is the state a case may
        exist to observe, so re-observing it on an idle machine can only swap it for another state."""
    with lock:
        breach = wt in held
        if not breach:
            held.add(wt)
    if breach:
        return ("DIED", 2, "ISOLATION BREACH: %s already holds a mutation" % wt, False)
    try:
        return run_one(wt, i)
    except _CannotJudge as e:
        return ("DIED", 2, str(e), False)
    except _RefusalUnread as e:
        return ("DIED", 1, str(e.code), False)
    except SystemExit as e:
        # A string code is the house `raise SystemExit(msg)` -> exit 1; an int keeps its code;
        # 0/None mid-mutation is NOT a pass, so it cannot judge.
        if isinstance(e.code, str):
            return ("DIED", 1, e.code, True)
        return ("DIED", e.code if e.code else 2, "exited %r" % (e.code,), True)
    except BaseException:                               # noqa: BLE001 — a crash is not a verdict
        return ("DIED", 1, traceback.format_exc(), True)
    finally:
        with lock:
            held.discard(wt)


def _dispatch(pool, order, run_one):
    """Run every index in `order` across `pool`, one worker per worktree. Returns
    (results {i: outcome}, done [completion order], problems)."""
    if len(set(pool)) != len(pool):
        return {}, [], ["the pool names a worktree twice: %s" % pool]
    results, done, problems = {}, [], []
    lock = threading.Lock()
    held = set()

    def one(wt, i):
        out = _attempt(wt, i, run_one, held, lock)     # which deaths may be retried: see there
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


def _execute(muts, pool, order, run_one, dispatch=None, prior=None):
    """Dispatch, re-observe deaths once, then judge. A pool problem (a mutation missing or run
    twice) exits 2. `dispatch` defaults to `_dispatch`; only a control passes another.

    ⭐ THE RETRY IS FOR THE UNOBSERVABLE, NEVER FOR A VERDICT (2026-10-04). A mutation that DIED of a
    TRANSPORT-shaped death (`_attempt` decides which) is observed ONCE more, after the pool has
    drained, at concurrency 1, in an idle pool worktree. A mutation that produced a verdict, PASS or
    FAIL, is never re-run; dying twice leaves DIED standing; every re-observed line says so.
    ⚠⚠ NARROWED BY RELY-CC-1. The retry was written for the two K=13 deaths, read then as "load made
    an unrelated leg fail and pre-empted the routing count". The leg that failed was non-routing (a
    verdictLedger restart under the run's load, per the supervisor logs), and with an RLYB4 mutation
    applied that made the ENFORCEMENT REFUSE (`push verdict INCONSISTENT`) — the one state those
    cases exist for. Re-observing it on an idle machine swapped that state for the vacuous one and
    printed PASS. A death whose raw output carries an enforcement refusal is now `_RefusalUnread`
    and is never retried; the RLYB4 cases read the refusal directly and do not die on it at all.

    `prior`: (results, retried, problems, done) from `_clean_phase`, merged before judging; a mutation
    observed in BOTH phases is a pool problem."""
    results, retried, problems, done = _observe_phase(pool, order, run_one, dispatch)
    if prior is not None:
        p_results, p_retried, p_problems, p_done = prior
        done = list(p_done) + list(done)
        problems += p_problems
        for i, out in p_results.items():
            if i in results:
                problems.append("mutation #%d was observed in both phases" % i)
            results[i] = out
        retried.update(p_retried)
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


def _observe_phase(pool, order, run_one, dispatch=None):
    """Dispatch `order` across `pool`, re-observing transport-shaped deaths once (see `_execute`).
    Returns (results, retried, problems, done)."""
    dispatch = dispatch or _dispatch
    results, done, problems = dispatch(pool, order, run_one)
    retried = {}
    redo = [i for i in sorted(results) if results[i][0] == "DIED" and results[i][3]]
    if redo:
        again, _done, more = dispatch([pool[0]], redo, run_one)
        problems += more
        for i in redo:
            second = again.get(i, ("DIED", 2, "the re-observation NEVER RAN", False))
            retried[i] = (results[i], second)
            if second[0] != "DIED":
                results[i] = second
    return results, retried, problems, done


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
        # ⭐ RELY-CC-6: REFUSAL rows run in the ROUTING-CLEAN phase of the primary (`_clean_phase`),
        # every other row in the A-staged pool. The pool is compared on the pool's needles only.
        clean_idx = [i for i, m in enumerate(muts) if m[3] == REFUSAL_NEEDLE]
        needles = sorted({m[3] for m in muts if m[3] != REFUSAL_NEEDLE})

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
        # ⭐ THE ROUTING-CLEAN PHASE, in the zero point's own state and BEFORE B and A touch the
        # index: the only state in which the agreement check decides whether the push proceeds.
        clean = _clean_phase(wt, muts, clean_idx, _tree_state(wt))
        if isinstance(clean, int):
            return clean
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
        # The cheap `batch.py prepush` observations (EXIT_NEEDLE / REFUSAL_NEEDLE, ~2 s) go FIRST, before the
        # pool fills with guards.py runs (~35 s each): measured at K=13 (2026-10-04), prepush runs
        # dispatched LAST overlapped ~9 heavy runs and two died of the load. K=1 keeps the original
        # order exactly. Output is in ORIGINAL order either way (`_judge`).
        pool_idx = [i for i in range(len(muts)) if i not in clean_idx]
        order = (pool_idx if k == 1 else
                 sorted(pool_idx, key=lambda i: muts[i][3] != EXIT_NEEDLE))
        print()
        _t0 = time.time()
        lines, code = _execute(muts, pool, order, _make_runner(muts_by_wt, _observe, pristine),
                               prior=clean)
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
    `dies` {i: "loaded"|"always"|"refused"}: the observation raises (as an unreadable prepush does)
    when other observations are still in flight, or every time; "refused" raises `_RefusalUnread`
    (the enforcement refused) when in flight with others, and reads fine alone."""
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
            if mode == "refused" and loaded:
                raise mod._RefusalUnread("stub: BLOCKED: push verdict INCONSISTENT (under load)\n"
                                         "  raw prepush output: <stub %d>" % i)
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


# -- RELY-CC-1 / RELY-CC-2 (2026-10-04): the properties the first eight controls never exercised ---

def _ctl_retry_not_on_refusal(mod):
    # STUB-02 dies ONLY under load, as `_RefusalUnread` — the enforcement refused. Alone it would read
    # fine, so a retry WOULD turn it into a PASS. It must stay DIED, un-re-observed, with no RESULT.
    delays = dict((i, 0.3) for i in range(6))
    delays[2] = 0.02
    lines, code, _o = _stub(mod, 6, 3, delays=delays, dies={2: "refused"})
    noted = [ln for ln in lines if "RE-OBSERVED" in ln]
    ok = (code == 1 and not noted and not any("RESULT:" in ln for ln in lines)
          and any("STUB-02" in ln and "DIED" in ln for ln in lines))
    return ok, "refusal under load: exit %d, %d re-observation(s), RESULT claimed: %s" % (
        code, len(noted), any("RESULT:" in ln for ln in lines))


def _rm_raw(msg):
    m = re.search(r"raw prepush output: (\S+)", str(msg))
    if m and os.path.isfile(m.group(1)):
        os.remove(m.group(1))


def _ctl_refusal_typed(mod):
    # The OBSERVABLE side of the same property: an unreadable run whose raw output carries an
    # enforcement refusal is typed `_RefusalUnread` (never retried); a crash is a plain death.
    outs = [("refusal", "ok rows\nBLOCKED: push verdict INCONSISTENT — 0 leg failure(s) RECORDED "
                        "but 1 FAIL row(s) DISPLAYED (purity)\n", 1),
            ("crash", "Traceback (most recent call last):\n  File \"x\", line 1\nKeyError: 'x'\n", 1)]
    got = []
    for name, out, rc in outs:
        try:
            mod._count_from(out, rc, "ctl")
            got.append((name, "READ"))
        except mod._RefusalUnread as e:
            got.append((name, "REFUSAL"))
            _rm_raw(e.code)
        except SystemExit as e:
            got.append((name, "DIED"))
            _rm_raw(e.code)
    return got == [("refusal", "REFUSAL"), ("crash", "DIED")], "typed as %s" % got


def _ctl_refusal_conjunction(mod):
    # The RLYB4 observable names the refusal AND requires the process to agree (say AND do).
    inc = "BLOCKED: push verdict INCONSISTENT — 0 leg failure(s) RECORDED but 1 DISPLAYED\n"
    fail = "BLOCKED: 3 push check(s) failed — 2 routing, 1 other.\n"
    got = (mod._refusal_from(inc, 1), mod._refusal_from(inc, 0), mod._refusal_from(fail, 1),
           mod._refusal_from("prepush PASS\n", 0), mod._refusal_from("prepush PASS\n", 1))
    want = ("INCONSISTENT", "INCONSISTENT-BUT-EXIT-0", "FAILED", "PASS", "PASS-BUT-EXIT-1")
    return got == want, "read %s" % (got,)


def _mini_pool(mod, n):
    """One scratch worktree, n trivial mutations whose observation reads "ok". (muts, pool, run_one,
    tmp) — the caller removes tmp."""
    tmp = tempfile.mkdtemp(prefix="zp_probe_selftest_")
    w = os.path.join(tmp, "w0")
    os.makedirs(w)
    muts = []
    for i in range(n):
        f = os.path.join(w, "f%d.txt" % i)
        mod._write(f, "pristine\n")
        muts.append(("STUB-%02d" % i, f, (lambda s: s + "m\n"), "n%d" % i, "ok"))
    pristine = {m[1]: "pristine\n" for m in muts}
    return muts, [w], mod._make_runner({w: muts}, lambda wt, needle: "ok", pristine), tmp


def _ctl_breach_not_retried(mod):
    # Q4. A breach cannot be PRODUCED through the live `_dispatch` (that is the point of it), so a
    # stand-in dispatch hands the REAL `_attempt` a worktree already held, on the first pass only.
    # Re-observed, the breach would read "ok": it must stay DIED and the run must refuse (exit 2).
    muts, pool, run_one, tmp = _mini_pool(mod, 3)
    calls = [0]

    def dispatch(pl, order, ro):
        calls[0] += 1
        held, lock, results, done = set(), threading.Lock(), {}, []
        for i in order:
            if calls[0] == 1 and i == 0:
                held.add(pl[0])
            results[i] = mod._attempt(pl[0], i, ro, held, lock)
            held.discard(pl[0])
            done.append(i)
        return results, done, []
    try:
        lines, code = mod._execute(muts, pool, [0, 1, 2], run_one, dispatch=dispatch)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    ok = (code == 2 and not any("RESULT:" in ln for ln in lines)
          and any("ISOLATION BREACH" in ln for ln in lines))
    return ok, "breach on the first pass: exit %d, dispatch passes %d, RESULT claimed: %s" % (
        code, calls[0], any("RESULT:" in ln for ln in lines))


def _ctl_dirty_not_retried(mod):
    # Q5. Through the REAL `_dispatch` and `_make_runner`: STUB-00's file is not pristine when it is
    # taken, and STUB-01's observation then cleans it — so a retry WOULD read "ok". It must not run.
    muts, pool, _ro, tmp = _mini_pool(mod, 2)
    try:
        f0 = muts[0][1]
        mod._write(f0, "dirty\n")

        def observe(wt, needle):
            if needle == "n1":
                mod._write(f0, "pristine\n")
            return "ok"
        run_one = mod._make_runner({pool[0]: muts}, observe, {m[1]: "pristine\n" for m in muts})
        lines, code = mod._execute(muts, pool, [0, 1], run_one)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    ok = (code == 2 and not any("RESULT:" in ln for ln in lines)
          and any("not pristine" in ln for ln in lines))
    return ok, "non-pristine first, clean later: exit %d, RESULT claimed: %s" % (
        code, any("RESULT:" in ln for ln in lines))


class _NoGit(object):
    """`subprocess` stand-in for `_ctl_main_refuses`: `main()`'s teardown must not reach real git."""
    class _R(object):
        returncode, stdout, stderr = 0, "", ""

    def run(self, *a, **k):
        return self._R()


def _main_case(mod, failing=None, short=None):
    """Run the REAL `mod.main()` with every process and observation stubbed, K=3. One pool worktree
    either fails to provision (`failing`) or provisions without registering (`short`). Returns
    (return code, whether any mutation was dispatched)."""
    import contextlib
    dispatched = []

    def files(wt):
        d = os.path.join(wt, "tools", "verify")
        os.makedirs(d, exist_ok=True)
        for f in ("ship.py", "batch.py"):
            mod._write(os.path.join(d, f), "stub\n")

    def add_wt(wt):
        os.makedirs(wt, exist_ok=True)
        return _NoGit._R()

    def provision(p, created):
        files(p)
        if p.endswith("pool%d" % failing if failing else "\0"):
            raise mod._CannotJudge("stub: provisioning failed")
        if not p.endswith("pool%d" % short if short else "\0"):
            created.append(p)

    def obs(wt, needles):
        o = {n: ("BLOCKS" if n == mod.EXIT_NEEDLE else "FAILED" if n == mod.REFUSAL_NEEDLE
                 else "ok") for n in needles}
        return o, {n: "ok" for n in needles}

    stubs = {"_add_worktree": add_wt, "_seed": lambda wt: files(wt) or 2,
             "_clean_phase": lambda *a, **k: ({}, {}, [], []),
             "_workers": lambda n: 3, "_provision": provision, "_baseline_obs": obs,
             "_tree_state": lambda wt: {"same": True}, "_prepush_exit": lambda wt: (0, 0),
             "_require_suppressed": lambda wt, rel: True,
             "_require_fires": lambda wt, rel: ("stub", b""),
             "_execute": lambda *a, **k: (dispatched.append(1), (["  RESULT: stub"], 0))[1],
             "subprocess": _NoGit()}
    saved = {k: getattr(mod, k) for k in stubs}
    try:
        for k, v in stubs.items():
            setattr(mod, k, v)
        with contextlib.redirect_stdout(io.StringIO()):
            rc = mod.main()
    finally:
        for k, v in saved.items():
            setattr(mod, k, v)
    return rc, bool(dispatched)


def _ctl_main_refuses(mod):
    # Q1. The REAL `main()`: a pool worktree that could not be provisioned, and a pool that came up
    # one worktree short, must each refuse (exit 2) BEFORE any mutation is dispatched.
    a = _main_case(mod, failing=2)
    b = _main_case(mod, short=2)
    ok = a == (2, False) and b == (2, False)
    return ok, "provisioning failed -> rc=%s dispatched=%s; pool short -> rc=%s dispatched=%s" % (
        a[0], a[1], b[0], b[1])


def _ctl_tree_bytes(mod):
    # Q2. The REAL `_tree_state` on two scratch trees (git cannot climb out: GIT_CEILING_DIRECTORIES):
    # identical trees compare equal; one byte changed under tools/verify must differ, in `bytes`.
    tmp = tempfile.mkdtemp(prefix="zp_probe_selftest_")
    # ⚠ A pre-push hook may export GIT_DIR & co., which would point these git calls at the REAL repo;
    #   they are removed for the control's lifetime, and the ceiling stops discovery above `tmp`.
    loc = ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR", "GIT_OBJECT_DIRECTORY",
           "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE", "GIT_PREFIX")
    saved_loc = {k: os.environ.pop(k) for k in loc if k in os.environ}
    saved = os.environ.get("GIT_CEILING_DIRECTORIES")
    os.environ["GIT_CEILING_DIRECTORIES"] = tmp
    try:
        trees = []
        for j in range(2):
            d = os.path.join(tmp, "t%d" % j)
            for rel in ("tools/verify/x.py", mod._A_SUBJECT, mod._B_SUBJECT):
                p = os.path.join(d, *rel.split("/"))
                os.makedirs(os.path.dirname(p), exist_ok=True)
                mod._write(p, "same\n")
            trees.append(d)
        same = mod._tree_state(trees[0]) == mod._tree_state(trees[1])
        mod._write(os.path.join(trees[1], "tools", "verify", "x.py"), "samf\n")
        s0, s1 = mod._tree_state(trees[0]), mod._tree_state(trees[1])
        differ = sorted(k for k in set(s0) | set(s1) if s0.get(k) != s1.get(k))
    finally:
        if saved is None:
            os.environ.pop("GIT_CEILING_DIRECTORIES", None)
        else:
            os.environ["GIT_CEILING_DIRECTORIES"] = saved
        os.environ.update(saved_loc)
        shutil.rmtree(tmp, ignore_errors=True)
    return same and differ == ["bytes"], "identical -> equal=%s; one tools/verify byte -> differs " \
        "in %s" % (same, differ or "nothing")


# -- RELY-CC-6 / RELY-CC-7 (2026-10-04): the routing-clean phase, the vacuity table, the count pins ---

def _ctl_vacuity(mod):
    # The class detector over the REAL rows and the REAL batch.py source beside this file.
    src = mod._read(os.path.join(os.path.dirname(os.path.abspath(mod.__file__)), "batch.py"))
    problems = mod._vacuity_problems(mod.mutations("ship.py", "batch.py"), src)
    return not problems, "%d vacuity problem(s)%s" % (len(problems),
                                                        (": " + problems[0]) if problems else "")


def _ctl_blocks_conjunction(mod):
    # Q6 (r2): the EXIT half of `_prepush_blocks` is RLY36-1a/b's protection. A printed refusal with
    # exit 0 must NOT read BLOCKS.
    saved = mod._prepush_exit
    try:
        got = []
        for pair in ((3, 0), (3, 1), (0, 1)):
            mod._prepush_exit = lambda wt, pair=pair: pair
            got.append(mod._prepush_blocks("ctl"))
    finally:
        mod._prepush_exit = saved
    return got == [False, True, False], "(routing, exit) (3,0) (3,1) (0,1) -> %s" % got


def _ctl_overlay_executes(mod):
    # `_OVERLAY` must EXECUTE the overlay as the real batch.py (argv, __file__, sys.path[0]) and leave
    # the bytes on disk unrun; a plain run must still run the disk file.
    tmp = tempfile.mkdtemp(prefix="zp_probe_selftest_")
    try:
        d = os.path.join(tmp, "tools", "verify")
        os.makedirs(d)
        mod._write(os.path.join(d, "batch.py"), 'print("DISK")\n')
        ov = ("import os, sys\nprint('OVERLAY', sys.argv[1:], os.path.basename(__file__), "
              "os.path.basename(sys.path[0]))\nsys.exit(3)\n")
        out, rc = mod._run_prepush(tmp, overlay=ov)
        plain, _rc = mod._run_prepush(tmp)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    want = "OVERLAY ['prepush', '--ranges', 'HEAD~1..HEAD'] batch.py verify"
    ok = want in out and "DISK" not in out and rc == 3 and "DISK" in plain
    return ok, "overlay run rc=%d, read %r; plain run read %r" % (rc, out.strip()[:70], plain.strip())


def _clean_case(mod, zero, now, drift=(), base="PASS"):
    """Run the REAL `_clean_phase` over one scratch REFUSAL row with every observation stubbed.
    Returns (outcome: 2 or the results dict, observations made)."""
    import contextlib
    tmp = tempfile.mkdtemp(prefix="zp_probe_selftest_")
    seen = []
    saved = {k: getattr(mod, k) for k in ("_tree_state", "_seed_drift", "_prepush_refusal")}
    try:
        d = os.path.join(tmp, "tools", "verify")
        os.makedirs(d)
        b = os.path.join(d, "batch.py")
        mod._write(b, "x = 1\n")
        muts = [("STUB-CLEAN", b, lambda s: s + "y = 2\n", mod.REFUSAL_NEEDLE, "INCONSISTENT")]
        mod._tree_state = lambda wt: dict(now)
        mod._seed_drift = lambda wt: list(drift)
        mod._prepush_refusal = lambda wt, overlay=None: (
            seen.append(overlay) or (base if overlay == "x = 1\n" else "INCONSISTENT"))
        with contextlib.redirect_stdout(io.StringIO()):
            res = mod._clean_phase(tmp, muts, [0], dict(zero))
    finally:
        for k, v in saved.items():
            setattr(mod, k, v)
        shutil.rmtree(tmp, ignore_errors=True)
    return (res if isinstance(res, int) else res[0]), len(seen)


_CLEAN_OK = {"staged": [], "bytes": "b0", "head": "h"}


def _ctl_clean_state_verified(mod):
    # The clean phase refuses BEFORE any observation when the tree is not the zero point's (here: A
    # left staged), and reads a row when it is.
    bad, n_bad = _clean_case(mod, _CLEAN_OK, dict(_CLEAN_OK, staged=[mod._A_SUBJECT]))
    good, n_good = _clean_case(mod, _CLEAN_OK, _CLEAN_OK)
    ok = bad == 2 and n_bad == 0 and isinstance(good, dict) and good.get(0) == ("GOT", "INCONSISTENT")
    return ok, "A staged -> %r after %d observation(s); zero-point state -> %r" % (bad, n_bad, good)


def _ctl_clean_seed_verified(mod):
    # Same state record, but the bundle bytes differ from the seed: refuse.
    res, n = _clean_case(mod, _CLEAN_OK, _CLEAN_OK, drift=["tools/verify/batch.py"])
    return res == 2 and n == 0, "seed drift -> %r after %d observation(s)" % (res, n)


def _ctl_clean_baseline(mod):
    # The unmutated source through the overlay must read PASS, or no row is attributable.
    res, n = _clean_case(mod, _CLEAN_OK, _CLEAN_OK, base="FAILED")
    return res == 2 and n == 1, "baseline FAILED -> %r after %d observation(s)" % (res, n)


def _ctl_refusal_not_in_pool(mod):
    # A REFUSAL row handed to the pool observer (A staged) must refuse to be read there.
    try:
        got = mod._observe("ctl", mod.REFUSAL_NEEDLE)
    except mod._CannotJudge as e:
        return True, "refused: %s" % str(e)[:60]
    return False, "the pool observer READ it: %r" % (got,)


def _ctl_pins(mod):
    problems = mod._pin_problems()
    return not problems, "%d pin problem(s)%s" % (len(problems),
                                                  (": " + problems[0]) if problems else "")


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
    # ⚠ RELY-CC-1: a death that IS the enforcement refusing is never re-observed — dispatch side,
    #   observable side, and the RLYB4 observable's say-AND-do conjunction in both directions.
    ("RETRY       a refusal death is never re-observed", _ctl_retry_not_on_refusal,
     '        return ("DIED", 1, str(e.code), False)',
     '        return ("DIED", 1, str(e.code), True)'),
    ("TYPED       an unreadable run that REFUSED is a refusal death", _ctl_refusal_typed,
     "    if any(n in out for n in _ENFORCE_DIE):\n        raise _RefusalUnread(msg)",
     "    if False:\n        raise _RefusalUnread(msg)"),
    ("REFUSAL     a printed refusal with exit 0 is not the refusal", _ctl_refusal_conjunction,
     "        if refused and rc == 0:",
     "        if False:"),
    ("REFUSAL     a printed PASS with a non-zero exit is not PASS", _ctl_refusal_conjunction,
     "        if not refused and rc != 0:",
     "        if False:"),
    # ⚠ RELY-CC-2: the four pool properties `/rely` mutated past all eight controls above (Q1-Q5).
    ("MAIN        main() refuses a pool that failed to provision", _ctl_main_refuses,
     "            if problems or len(created) != k:",
     "            if False:"),
    ("MAIN        main() refuses a pool one worktree short", _ctl_main_refuses,
     "            if problems or len(created) != k:",
     "            if problems:"),
    ("TREE        _tree_state compares the tools/verify BYTES", _ctl_tree_bytes,
     '"status": g("status", "--porcelain"), "bytes": h.hexdigest()}',
     '"status": g("status", "--porcelain")}'),
    ("RETRY       an isolation breach is never re-observed", _ctl_breach_not_retried,
     '        return ("DIED", 2, "ISOLATION BREACH: %s already holds a mutation" % wt, False)',
     '        return ("DIED", 2, "ISOLATION BREACH: %s already holds a mutation" % wt, True)'),
    ("RETRY       a non-pristine refusal is never re-observed", _ctl_dirty_not_retried,
     '        return ("DIED", 2, str(e), False)',
     '        return ("DIED", 2, str(e), True)'),
    # ⚠ RELY-CC-6: the class detector. Each mutant breaks the table a different way: a pair that no
    #   longer requires a flip, a pair that no longer composes row + deletion, a row dropped from
    #   coverage, an uncovered row dropped from the list.
    ("VACUITY     a META row wanting its row's state is caught", _ctl_vacuity,
     '    (L_B4_1_META, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1, _NO_AGREE), REFUSAL_NEEDLE, "PASS"),',
     '    (L_B4_1_META, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1, _NO_AGREE), REFUSAL_NEEDLE, '
     '"INCONSISTENT"),'),
    ("VACUITY     a META row not composing row + deletion is caught", _ctl_vacuity,
     "        (L_B4_1B_META, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1B, _NO_AGREE), REFUSAL_NEEDLE,",
     "        (L_B4_1B_META, batch, _apply_all(_SYNTH_FAIL, _RLYB4_1B), REFUSAL_NEEDLE,"),
    ("VACUITY     a row dropped from its vacuity pair is caught", _ctl_vacuity,
     "    (L_B4_1B, L_B4_1B_META, (_NO_AGREE,)),\n", ""),
    ("VACUITY     a row dropped from the uncovered list is caught", _ctl_vacuity,
     '    "RLY36-1b the refusal primitive exits 0": _EXIT_HALF,\n', ""),
    ("CONJUNCTION a printed refusal with exit 0 is not BLOCKS (Q6)", _ctl_blocks_conjunction,
     "    return routing > 0 and returncode != 0",
     "    return routing > 0"),
    ("OVERLAY     the clean phase EXECUTES the mutated source", _ctl_overlay_executes,
     "            cmd = [sys.executable, made[0], real, made[1]] + argv",
     "            cmd = [sys.executable, real] + argv"),
    ("CLEAN       the clean phase refuses a tree not at the zero point", _ctl_clean_state_verified,
     '    if d:\n        print("    ** CLEAN PHASE REFUSED',
     '    if False:\n        print("    ** CLEAN PHASE REFUSED'),
    ("CLEAN       the clean phase refuses bundle bytes off the seed", _ctl_clean_seed_verified,
     '    return out + ["bundle bytes differ from the seed: %s" % r for r in _seed_drift(wt)]',
     "    return out"),
    ("CLEAN       the clean phase refuses a baseline that is not PASS", _ctl_clean_baseline,
     '    if base != "PASS":',
     "    if False:"),
    ("CLEAN       a REFUSAL row is never read by the A-staged pool", _ctl_refusal_not_in_pool,
     '    if needle == REFUSAL_NEEDLE:\n        raise _CannotJudge("a REFUSAL row reached',
     '    if needle == REFUSAL_NEEDLE:\n        return "INCONSISTENT"\n'
     '        raise _CannotJudge("a REFUSAL row reached'),
    # ⚠ RELY-CC-7: a row deleted with its pin left unchanged refuses.
    ("PINS        a deleted mutation row is caught by the count pin", _ctl_pins,
     '        ("B4       `_EXPECTED` quietly loses a gating leg", batch,\n'
     "         lambda s: s.replace(\n"
     "             '_EXPECTED = (\"routing\", \"purity\", \"ssot\", \"pdf_coupling\", \"prior_art_attrib\")',\n"
     "             '_EXPECTED = (\"routing\", \"purity\", \"ssot\", \"pdf_coupling\")'),\n"
     '         "push verdict registry", "FAIL"),\n',
     ""),
]
_EXPECTED_CONTROLS = 28


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


def _cli(argv):
    """`--selftest` runs the pool controls; `--mutations` (or no argument) runs the probe.
    ⚠ The push hook passes `--mutations` EXPLICITLY: `reconcile` matches a launched argv by PREFIX,
    so a bare `probe_routing_behavioural.py` expectation would be satisfied by the `--selftest` run
    alone, and deleting the probe's own call site would reconcile green. Anything else refuses.
    ⚠ RELY-CC-7: both modes refuse (exit 2) first when a count disagrees with its pin."""
    pins = _pin_problems() if argv in ([], ["--mutations"], ["--selftest"]) else []
    if pins:
        print("%s: REFUSING — the probe's counts disagree with their pins:" % SELF)
        for p in pins:
            print("  %s" % p)
        return 2
    if argv == ["--selftest"]:
        return selftest()
    if argv in ([], ["--mutations"]):
        return main()
    print("%s: unrecognised arguments %r — expected --selftest or --mutations" % (SELF, argv))
    return 2


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
