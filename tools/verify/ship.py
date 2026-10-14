"""The deterministic half of the single production command. Driven by `/ship`.

    python ship.py pre        # ALL mechanical work + round bump + plan + freeze
    python ship.py plan       # the plan alone, nothing run
    python ship.py check      # the mechanical half only
    python ship.py post       # release the lock, validate the signals

WHY (Tim, 2026-08-10): *"the pipeline is supposed to handle the gates as part of this — the whole
idea was a single command that does everything we need to do for our production work, guaranteed."*

Until now the pipeline **demanded** review signals and had no way to **produce** them: `batch.py
prepush` checked that `er/ar/pa_cleared.txt` were fresh and a human had to remember to spawn four
review agents by hand. That is the same defect as everything else this arc fixed — a step outside
the one path is a step that gets skipped — and it is the worst place for it, because the gates find
exactly the defects the mechanical checkers provably cannot see (measured: none of twelve content
findings in one gate round was visible to any checker).

**THE SPLIT, and it is the same one this project uses everywhere: the SCRIPT owns what is decidable,
the AGENT owns what is not.** This file decides *which* gates a change owes and *whether* their
signals are valid — both mechanical. It does not run the gates: spawning a review agent is the
`/ship` slash command's job, through the normal Agent tool, so the runs are visible, streamed and
attributable.

⚠ **An earlier draft shelled out to `claude -p` to run the gates from inside this script. That was
wrong** (Tim: *"a slash command that executes the scripts and review agents would be sufficient"*)
— it buried the reviews in an opaque subprocess, invented a second way to spawn agents alongside the
one that already works, and made cost and progress invisible. The lesson is the arc's own: **do not
build a second mechanism for something that already has one.**

⚠ **Deliberately NOT in the git hook.** A gate run is 15-25 minutes; four in a pre-push hook would
hang git for over an hour and be disabled within a day. Division of labour: **`/ship` PRODUCES the
signatures, the hook REFUSES work that lacks them.** Without the hook `/ship` is optional; without
`/ship` the hook is a wall with no door.
"""
import io
import os
import re
import sys

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
BASE = HERE   # retained: call sites below mean "where the tools live"
if BASE not in sys.path:
    sys.path.insert(0, BASE)

import report                                    # noqa: E402
import batch                                     # noqa: E402
import selfheal                                  # noqa: E402  (SUMMARY_TAG only — see below)

# gate key -> (command file to read, LEDGER STEP it records, human name)
#
# ⚠ THE MIDDLE FIELD WAS A SIGNAL FILENAME UNTIL 2026-08-24 AND IS NOW A LEDGER STEP. The prose
# signal files are retired: a FAIL is recorded by the gate itself, a PASS is reported to the caller
# who records the agreement or takes a signature. This field is printed so an operator can see WHAT
# each gate must produce; naming a file nothing writes any more would send them looking for it.
GATES = {
    "editorial": ("editorial-review.md", "editorial", "/editorial-review"),
    "adversary": ("adversary-review.md", "adversary", "/adversary-review"),
    "prior-art": ("prior-art-review.md", "prior_art", "/prior-art-review"),
    # `/rely` records a `rely` verdict in the ledger and writes no signal file; what it owes is
    # `coverage_gap(step='rely')`, and it gates at TAG through gitRobot's admission set.
    "rely":      ("rely.md",             "rely", "/rely"),
}


def gate_round():
    _rc, out = batch.sh(sys.executable, os.path.join(BASE, "gate_round.py"), "show")
    m = re.search(r"Gate round:\s*(\d+)", out)
    return int(m.group(1)) if m else 1


def refuse_if_scope_unknown(ranges, who):
    """FAIL CLOSED when asked to judge a push whose scope cannot be seen.

    ⚠ One definition, used by `plan`, `pre` and `post`. `cmd_prepush` had this guard and the other
    three did not, so the documented form of the command — no `--ranges`, clean tree — reported
    `no gates required … PASS, exit 0` for a commit carrying a 60-declaration new `.lean` layer that
    owed editorial, adversary AND prior-art. With `--ranges` the same state returned BLOCKED.
    Measured by /rely pass 4, in the code written to prevent exactly this class of thing."""
    if ranges is None and not batch.changed_files(None):
        print("\nCANNOT JUDGE: no --ranges given and the working tree is clean, so the scope of the")
        print("push is unknown — a clean tree is not an empty push. This form is only meaningful")
        print("BEFORE committing; afterwards pass --ranges <base>..<tip>, which is what the hook")
        print("does. Refusing to report a verdict %s cannot support." % who)
        sys.exit(1)


def required_gates(ranges):
    """WHICH review agents this change should spawn and WHY — the PLAN, not the verdict.

    Returns (scope, [(key, why)]). Whether the action may proceed is `cmd_verify`'s question, and it
    is answered by the services, never from this list."""
    scope = batch.reviewable_changed(ranges)
    fires, ins, newfile = batch.check_trigger5(ranges)
    need = []
    if scope:
        why = "reviewable prose/construction in scope (%d file(s))" % len(scope)
        need.append(("editorial", why))
        need.append(("adversary", why))
    if fires:
        need.append(("prior-art",
                     "trigger 5 fires: %d inserted .lean line(s), new .lean file=%s"
                     % (ins, newfile)))
    # ⚠ `/rely` IS NOT DERIVED HERE. Which paths it still owes is verdictLedger's
    # `coverage_gap(step='rely')`, and whether it gates an action is gitRobot's admission set
    # (`rely` is admitted at TAG). `cmd_verify` asks both; a local routing predicate is the control
    # plane leaking out of the services, and `guards.py` asserts none is left here.
    return scope, need


_UNSET = object()

RELY_CAP = 2


def rely_capped(rec=_UNSET):
    """Is `/rely` past its iteration cap with nothing BLOCKING outstanding?

    ⚠ Tim, 2026-08-10: *"any non bedrock failure should cap at a certain iteration. it used to be
    two. A nitpicker will always find a knit to pick."* `/rely` was never under the cap at all — it
    issues no PASS/FAIL verdict, so the ORDINARY/BEDROCK tiers were written for the three prose
    gates and silently excluded it. Measured cost: four passes finding 10 → 4 → 6 → 9, never
    converging, because each pass reviews a layer changed in response to the last. That is not a
    signal the layer is bad; it is what an unbounded adversarial loop does.

    **BLOCKING here means a finding that lets bad work THROUGH** — a fail-open, a gate that can be
    walked past, a signal that can be forged. Everything else (a mislabelled manifest line, a
    discarded return code at a site that fails closed anyway) is ordinary and caps out."""
    # PRIV, not BASE. A signal is per-push private state and did not move with the tools on
    # 2026-08-15 — and getting this wrong was silent in the worst way: `rely_capped()` returns
    # "not capped" for a MISSING file, so reading the wrong directory did not error, it just
    # answered False forever. Caught only because guards.py plants a must-fire control here and
    # reported BASELINE BROKEN; without that control the cap would have quietly stopped existing.
    # ⚠⚠ THE LEDGER, NOT `rely_cleared.txt`. That file is RETIRED (2026-08-24). `rec` is injectable
    # so a control can drive both directions without planting a fixture — the signal comes from a
    # SERVER now, and that is the only honest way to exercise it.
    if rec is _UNSET:
        rec = batch.rely_record()
    if rec is None:
        # ⚠ Covers BOTH "no record" and "the ledger could not be asked", and returns NOT CAPPED —
        # which is the conservative direction here: an uncapped loop costs a round, a wrongly-capped
        # one ships findings. Note this is the OPPOSITE polarity to a coverage check, deliberately.
        return False, ""
    # ⚠ BLOCKING COMES FROM THE VERDICT FIRST, the reason text second. The brief records a FAIL only
    # when BLOCKING > 0 and records nothing at BLOCKING:0, so the verdict already carries the fact
    # and the prose is corroboration — the reverse of the old file, where prose was all there was.
    m = re.search(r"BLOCKING:\s*(\d+)", rec.get("reason") or "", re.I)
    if m:
        blocking = int(m.group(1))
    elif rec.get("verdict") == "PASS":
        blocking = 0
    else:
        # A cap that cannot read the record is not a cap. Say so instead of quietly not capping —
        # silent non-capping is precisely the unbounded loop the cap exists to stop.
        return False, ("RECORD MALFORMED — a `rely` FAIL with no `BLOCKING:<n>` in its reason, so "
                       "the cap cannot be evaluated. Re-run /rely; do not read this as 'not capped'.")

    # ⚠ COUNT PASSES FROM THE SIGNAL, not only from the round counter. Measured 2026-08-10: five
    # /rely passes had run and `gate_round.json` recorded `rely-verification-layer x1`, because the
    # bump only happens when a caller remembers `--target` — so the cap Tim asked for could never
    # fire. The reviewer writes its own pass number into line 1 ("pass 5"), which is the one record
    # that cannot be skipped by forgetting a flag. Take the larger of the two.
    _rc, out = batch.sh(sys.executable, os.path.join(BASE, "gate_round.py"), "show")
    pm = re.search(r"rely-verification-layer\s+x(\d+)", out)
    sm = re.search(r"\bpass\s+(\d+)", rec.get("reason") or "", re.I)
    passes = max(int(pm.group(1)) if pm else 0, int(sm.group(1)) if sm else 0)
    if blocking == 0 and passes >= RELY_CAP:
        return True, ("capped at %d passes with BLOCKING:0 — remaining findings are ledgered debt, "
                      "not a reason to iterate (a nitpicker always finds a nit)" % passes)
    return False, ""


def cmd_pre(ranges, target):
    """EVERYTHING scriptable that happens BEFORE the agents: checks, round bump, plan.

    One call, not three. The caller runs this, spawns exactly the gates it names, then runs `post`."""
    # ⚠ VALIDATE THE SCOPE BEFORE SPENDING A ROUND. Measured 2026-08-10: `pre` bumped, then refused
    # on an unknown scope — so a run that spawned no gate at all still burned a round, pushing the
    # counter toward a cap that then fires early. `gate_round.py`'s own docstring names that as the
    # unsafe direction (a fresh arc inheriting a count is told to stop on its round 1). A round is
    # spent when a gate reads the tree, never when the caller mistypes an invocation.
    refuse_if_scope_unknown(ranges, 'a gate round')
    rc = batch.sh(sys.executable, os.path.join(BASE, "batch.py"), "precommit")
    print(rc[1])
    if rc[0] != 0:
        report.done("ship pre", False, "mechanical checks FAILED — fix before spending a gate round")
        return 1
    # ⚠ CHECK THE CAP WHETHER OR NOT WE BUMP. It used to live inside `if target:`, so omitting
    # `--target` skipped the bump, which skipped the cap, and `pre` exited 0 at round 6 — the third
    # route past a boundary whose first two routes had just been closed. The cap is a property of
    # the ROUND, not of whether this invocation happened to increment it.
    rc_cap, out_cap = batch.sh(sys.executable, os.path.join(BASE, "gate_round.py"), "show")
    # ⚠ ANY non-zero, not just 2. `gate_round.py` exits 2 past the cap, but a CRASH
    # (corrupt gate_round.json, an encoding error) exits 1 — and testing only for 2
    # read that as 'cap fine'. A cap check that cannot run is not a cap check.
    if rc_cap != 0:
        print(out_cap)
        report.done("ship pre", False,
                    "PAST THE BEDROCK CAP — refusing to spawn another round. Escalate to Tim; "
                    "if this is genuinely new work, `gate_round.py reset` first.")
        return 2

    if target:
        rc2, out = batch.sh(sys.executable, os.path.join(BASE, "gate_round.py"),
                            "bump", "--target", target)
        print(out)
        # ⚠ ACT on the bedrock cap, do not merely relay it. `gate_round.py` exits 2 past
        # BEDROCK_CAP; before 2026-08-10 it exited 0 and every caller sailed past the boundary the
        # cap exists to defend. The ORDINARY tier stays advisory on purpose — the REVIEWER decides
        # STOP-ORDINARY vs FAIL-BEDROCK from outside the loop — but the BEDROCK tier is the backstop
        # on that judgement, and a loop that has burned it needs a human, not another round.
        if rc2 == 2:
            report.done("ship pre", False,
                        "PAST THE BEDROCK CAP — refusing to spawn another round. Escalate to Tim; "
                        "if this is genuinely new work, `gate_round.py reset` first.")
            return 2
    rc_plan = cmd_plan(ranges)
    if rc_plan != 0:
        return rc_plan

    # ⚠ THE REVIEW SCOPE IS NOT FROZEN, AND THE PROPERTY IT PROTECTED IS STILL ENFORCED — by
    # DETECTION rather than prevention. The hazard is real and measured: twice, a caller wrote "the
    # tree is stable" into a gate brief and then edited the reviewed files mid-round, once
    # invalidating a signal computed against a tree that had moved. What catches that now is the
    # per-file SHA-256 scheme — an edited file no longer hashes to what the signal recorded, so
    # `prepush` refuses and names it.
    #
    # That is strictly harder to walk past than the read-only bit this replaced: git unlinks and
    # recreates rather than opening for write, so `checkout` and `reset --hard` silently un-froze a
    # locked path — measured, and recorded in the retired tool's own header.
    return 0


def cmd_plan(ranges):
    refuse_if_scope_unknown(ranges, 'a plan')
    scope, need = required_gates(ranges)
    rnd = gate_round()
    report.banner("ship — plan", [
        ("scope", (["%d reviewable file(s):" % len(scope)] +
                   ["  " + f for f in scope[:8]] +
                   (["  … and %d more" % (len(scope) - 8)] if len(scope) > 8 else []))
                  if scope else ["no reviewable files in scope"]),
        ("round", "gate round %d (cap 2 ORDINARY / 5 BEDROCK)" % rnd),
        ("gates", "%d required" % len(need)),
    ])
    report.plan([("mechanical", "BLOCK", "build green, purity, ssot, 4 gating checkers")] +
                [(GATES[k][2], "BLOCK", w) for k, w in need] +
                [("signals", "BLOCK", "verdictLedger reports gitRobot's %s admission set "
                                      "satisfied (`post`)" % VERIFY_ACTION)])
    if need:
        print("\n  Gates to spawn (one fresh agent each, brief read from its command file):")
        for k, w in need:
            cf, sig, human = GATES[k]
            print("    %-20s brief=%-24s signal=%s" % (human, cf, sig or "(none — not a gate)"))
    # Standing self-improvement pass. REPORTS ONLY — it never edits, never files, and never blocks
    # (Tim, 2026-08-10: *"not automatic correction, but if we hit the same bug repeatedly you should
    # suggest process improvements"*). It runs here rather than on request because the rule it
    # enforces — "the SECOND occurrence is a class" — requires holding 67 ledger rows in mind at
    # once, which is exactly the kind of remembering this project has measured itself failing at.
    # ⚠ THE SELECTOR IS IMPORTED, NOT RETYPED (`/rely` O2, 2026-09-16). It used to require a line
    # that both began `⚠` AND contained "shape(s)"; no line selfheal prints has ever satisfied
    # both, so this block was dead from the day it was written and `/ship` reported nothing while
    # looking like it reported nothing to report. That is SH-6 — success not earned — reached
    # through SH-7 — a definition copied instead of imported.
    sh_rc, sh_out = batch.sh(sys.executable, os.path.join(BASE, "selfheal.py"))
    tail = [l for l in sh_out.splitlines() if selfheal.SUMMARY_TAG in l]
    if sh_rc != 0:
        # ⚠ STATUS BEFORE CONTENT — the THIRD consumer of this child, and the one still reading
        # content first after rounds 3 and 4 fixed the other two (`/rely` round 5, B2). A child
        # that printed its summary line and THEN died satisfied `tail` and rendered as a complete
        # advisory with no mention of the exit code.
        print("\n  self-heal: did not complete (exit %s) — advisory, and NOT a clean bill" % sh_rc)
    elif tail:
        print("\n  self-heal: %s" % tail[0].strip())
        print("             run `python %s/selfheal.py` for the suggestions"
              % os.path.dirname(SELF))
    elif sh_rc == 0:
        # ⚠ THREE OUTCOMES, NOT TWO (`/rely` R3-O2). `cmd_verify` got the third and this sibling
        # kept two, so a MEASURED "nothing at or over the threshold" printed "not a clean bill" —
        # over-warning, which is the safe polarity and still the wrong sentence.
        print("\n  self-heal: nothing at or over the recurrence threshold — nothing to propose.")
    else:
        # ⚠ SILENCE AND NOTHING-TO-REPORT ARE DIFFERENT ANSWERS (R-ZERONULL). Advisory either
        # way — this never blocks — but an unreadable self-heal must not render as a clean one.
        print("\n  self-heal: NO SUMMARY LINE (selfheal.py exit %s) — advisory, and NOT a clean"
              " bill" % sh_rc)

    # ⚠ THE GATES READ A TREE THAT CAN MOVE UNDER THEM, AND THAT IS HANDLED DOWNSTREAM, NOT HERE.
    # Editing a reviewed file mid-round changes its SHA-256, the signal stops covering it, and
    # `prepush` refuses by name. Two distinct vectors, and only the first is this file's business:
    # the CALLER's accidental edits (detected as above) versus an AGENT mutating git state (the
    # worktree rule, AGT-1, and now gitRobot refusing the destructive verbs outright).
    print("\n  SHIP_SCOPE=%s" % ",".join(scope))
    print("  SHIP_GATES=%s" % ",".join(k for k, _w in need))
    print("  SHIP_ROUND=%d" % rnd)
    return 0


def cmd_check():
    return batch.sh(sys.executable, os.path.join(BASE, "batch.py"), "precommit")[0]


# ⚠ THE TWO QUESTIONS `post` ASKS, AND WHO ANSWERS THEM. What must be green for the action is
# gitRobot's admission set; whether it IS green is verdictLedger's — `can_push(rev_range)` for a
# committed range, `inventory(ref)` for the staged tree. Seams, so controls never reach a service.
VERIFY_ACTION = "tag"
_ASK_GITROBOT = None      # controls only: callable(tool, arguments) -> payload
_ASK_LEDGER = None        # controls only: callable(tool, arguments) -> payload


def _ask(which, tool, arguments):
    import record
    seam = _ASK_GITROBOT if which == "gitrobot" else _ASK_LEDGER
    if seam is not None:
        return seam(tool, arguments)
    return (record.gitrobot_call if which == "gitrobot" else record._call)(tool, arguments)


def served_verdict(ranges):
    """`(allowed, lines)` — the services' answer for `VERIFY_ACTION`, or `(None, lines)` when it
    could not be asked. Three values, never two (`R-ZERONULL`): `None` is not a refusal.

    Nothing here decides which steps gate or whether one is satisfied: the admission set is passed
    through as gitRobot gave it, and `allowed` / `complete` are read as the ledger computed them.
    (`RLY28-2` was a hard-coded `/rely` refusal here; `SIGSTALE-1` a local re-derivation of
    editorial/adversary staleness at the tips. Both are the servers' questions.)"""
    try:
        adm = _ask("gitrobot", "admission", {"action": VERIFY_ACTION})
    except Exception as e:                                # noqa: BLE001 — any failure is "not asked"
        return None, ["gitRobot admission(action=%r) could not be asked: %s" % (VERIFY_ACTION, e)]
    admitted = adm.get("admitted") if isinstance(adm, dict) and adm.get("ok") is True else None
    if not isinstance(admitted, list):
        return None, ["gitRobot admission(action=%r) gave no admission set: %r"
                      % (VERIFY_ACTION, str(adm)[:300])]
    lines = ["admission (%s, from gitRobot): %s" % (VERIFY_ACTION, ", ".join(admitted))]
    # ⚠⚠ AN EMPTY ADMISSION SET IS A REFUSAL, NEVER A PASS (`G1-5`, `R-ZERONULL`). Measured: given
    #   `admitted: []` the ledger's `can_push` returns `allowed: true` with `admission_state: EMPTY`,
    #   while its own `line` says "Treated as REFUSED because an unconfigured gate fails closed".
    #   "Nothing gates" and "everything passed" must not be one value, so this does not ask at all.
    if not admitted:
        return False, lines + ["gitRobot admission(action=%r) is EMPTY — an unconfigured gate fails "
                               "CLOSED; REFUSED, not a pass" % VERIFY_ACTION]
    if ranges:
        asks = [("can_push", {"rev_range": r, "action": VERIFY_ACTION, "admission": admitted},
                 "allowed", r) for r in ranges]
    else:
        # The staged tree, resolved here exactly as recording resolves it (`record.read_ref`).
        try:
            tree = common.ledger_basis(common.INDEX)["value"]
        except common.BasisUnresolved as e:
            return None, lines + ["the staged tree could not be resolved: %s" % e]
        asks = [("inventory", {"action": VERIFY_ACTION, "ref": tree, "admission": admitted},
                 "complete", "staged tree %s" % tree[:12])]
    allowed = True
    for tool, args, key, what in asks:
        try:
            out = _ask("ledger", tool, args)
        except Exception as e:                            # noqa: BLE001
            return None, lines + ["verdictLedger %s for %s could not be asked: %s" % (tool, what, e)]
        if not isinstance(out, dict) or out.get("ok") is not True or not isinstance(
                out.get(key), bool):
            return None, lines + ["verdictLedger %s for %s gave no `%s` answer: %r"
                                  % (tool, what, key, str(out)[:300])]
        lines.append("verdictLedger %s %s -> %s=%s" % (tool, what, key, out[key]))
        lines.extend("  " + l for l in str(out.get("line") or "").splitlines())
        # ⚠ The ledger's own EMPTY marker overrides its boolean, by its own stated rule (`G1-5`).
        if out.get("admission_state") == "EMPTY":
            lines.append("  admission_state EMPTY — an unconfigured gate fails CLOSED; REFUSED")
            allowed = False
            continue
        allowed = allowed and out[key]
    return allowed, lines


def cmd_verify(ranges):
    refuse_if_scope_unknown(ranges, 'a signal verdict')
    scope, need = required_gates(ranges)
    keys = {k for k, _w in need}
    report.banner("ship — verify", [
        ("scope", "%d reviewable file(s)" % len(scope)),
        ("spawned", ", ".join(sorted(keys)) or "no review agents planned"),
    ])
    allowed, lines = served_verdict(ranges)
    for l in lines:
        print("  " + l)
    bad = 0 if allowed is True else 1
    report.done("ship verify", allowed is True,
                "the ledger reports the %s admission set satisfied" % VERIFY_ACTION
                if allowed is True else
                ("UNDECIDED — a service could not be asked; this is not a pass"
                 if allowed is None else "the ledger reports the admission set NOT satisfied"))

    # Answer the standing question at the END of a run as well as the start. Tim, 2026-08-10:
    # *"what should we be doing here and now to make the next run better? that's the question that
    # I'm going to keep wanting to ask."* Asked at `pre` it reports what the last runs cost; asked
    # here it reports what THIS run just added, while the evidence is still in front of you.
    print("")
    # ⚠ THE SECOND SELECTOR, and it was untouched when the first was fixed (`/rely` R2-B2) —
    # a retyped heading, the exit status discarded, and no branch for "produced nothing". That is
    # `SH-3`, one of two routes to the same property, committed inside the fix for the other one.
    # THREE outcomes here, and they must not render alike (R-ZERONULL): a report, a measured
    # nothing-to-propose, and a failure to report at all.
    sh_rc, out = batch.sh(sys.executable, os.path.join(BASE, "selfheal.py"))
    tail = out.split(selfheal.ACTIONS_HEADING, 1)
    if sh_rc != 0:
        # ⚠ STATUS BEFORE CONTENT (`/rely` round 4, B4). A child that printed a truncated report
        # and then died satisfied the split below and rendered as a complete advisory.
        print("\n  self-heal: did not complete (exit %s) — advisory, and NOT a clean bill" % sh_rc)
    elif len(tail) == 2:
        print("  " + selfheal.ACTIONS_HEADING + tail[1].rstrip())
    elif sh_rc == 0:
        print("  self-heal: nothing at or over the recurrence threshold — nothing to propose.")
    else:
        print("  self-heal: NO REPORT (selfheal.py exit %s) — advisory, and NOT a clean bill"
              % sh_rc)
    # 2 when a service could not be asked, never 1: an outage is not a finding about the work.
    return 2 if allowed is None else (1 if bad else 0)


def selftest():
    """Controls for `served_verdict`: the services' answer is carried, never re-derived, and every
    way of not getting one is `None`. Seams only — no service is reached. Returns 1 on failure."""
    global _ASK_GITROBOT, _ASK_LEDGER
    ADM = ["adversary", "editorial", "rely"]
    asked = []

    def gr(answer):
        def f(tool, args):
            if isinstance(answer, Exception):
                raise answer
            return answer
        return f

    def led(answers):
        def f(tool, args):
            asked.append((tool, args))
            a = answers[min(len(asked), len(answers)) - 1]
            if isinstance(a, Exception):
                raise a
            return a
        return f

    ok_adm = {"ok": True, "admitted": ADM}
    yes = {"ok": True, "allowed": True, "line": "ALLOWED"}
    no = {"ok": True, "allowed": False, "line": "REFUSED  tag  1/1 commit(s) short"}
    cases = [
        ("the ledger's ALLOWED is carried", ok_adm, [yes], ["a..b"], True),
        ("the ledger's REFUSED is carried", ok_adm, [no], ["a..b"], False),
        ("one refused range of two refuses", ok_adm, [yes, no], ["a..b", "b..c"], False),
        ("gitRobot unreachable is UNDECIDED", OSError("refused (control)"), [yes], ["a..b"], None),
        ("no admission set is UNDECIDED", {"ok": True}, [yes], ["a..b"], None),
        ("ledger unreachable is UNDECIDED", ok_adm, [OSError("down (control)")], ["a..b"], None),
        ("a ledger answer with no verdict is UNDECIDED", ok_adm, [{"ok": True}], ["a..b"], None),
        ("a ledger refusal body is UNDECIDED", ok_adm,
         [{"ok": False, "error_type": "x", "allowed": True}], ["a..b"], None),
        # G1-5: the live reply shape for an empty admission set — `allowed: true` — must REFUSE.
        ("an EMPTY admission set refuses, never passes", {"ok": True, "admitted": []},
         [{"ok": True, "allowed": True, "admission_state": "EMPTY",
           "line": "Treated as REFUSED because an unconfigured gate fails closed"}], ["a..b"], False),
        ("an EMPTY admission set refuses even if the ledger omits its marker",
         {"ok": True, "admitted": []}, [yes], ["a..b"], False),
        ("the ledger's admission_state EMPTY refuses", ok_adm,
         [{"ok": True, "allowed": True, "admission_state": "EMPTY", "line": "x"}], ["a..b"], False),
    ]
    rows = []
    saved = _ASK_GITROBOT, _ASK_LEDGER
    try:
        for label, adm, answers, ranges, want in cases:
            del asked[:]
            _ASK_GITROBOT, _ASK_LEDGER = gr(adm), led(answers)
            got, _lines = served_verdict(ranges)
            rows.append((label, got is want))
        del asked[:]
        _ASK_GITROBOT, _ASK_LEDGER = gr(ok_adm), led([yes])
        served_verdict(["a..b"])
        rows.append(("the admission set is passed through as given (rely included)",
                     bool(asked) and asked[0][1].get("admission") == ADM
                     and asked[0][1].get("action") == VERIFY_ACTION))
        del asked[:]
        _ASK_LEDGER = led([{"ok": True, "complete": True, "line": "SATISFIED"}])
        got, _lines = served_verdict(None)
        rows.append(("no range asks inventory at the staged TREE",
                     got is True and bool(asked) and asked[0][0] == "inventory"
                     and bool(re.match(r"^[0-9a-f]{40}$", str(asked[0][1].get("ref"))))))
    finally:
        _ASK_GITROBOT, _ASK_LEDGER = saved
    bad = 0
    print("SERVED VERDICT (ship post asks gitRobot + verdictLedger; decides nothing)")
    for label, ok in rows:
        print("  %-62s %s" % (label, "ok" if ok else "*** FAILED ***"))
        bad += 0 if ok else 1
    print("\nselftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
    return 1 if bad else 0


def main():
    a = sys.argv[1:]
    if a == ["--selftest"]:
        return selftest()
    what = a[0] if a else "pre"
    ranges = None
    if "--ranges" in a:
        i = a.index("--ranges")
        if i + 1 >= len(a):
            print("ship: --ranges needs a value (comma-separated). Refusing to guess a scope.")
            return 1
        ranges = [r for r in a[i + 1].split(",") if r.strip()]
    # ⚠ `--ranges` refused a missing value and `--target` silently became None four lines away —
    # and a silently-absent target skips the round bump, which skips the BEDROCK-CAP check, which
    # is how `/rely` pass 4 walked past a cap that had just been given teeth. Same guard, both flags.
    target = None
    if "--target" in a:
        i = a.index("--target")
        if i + 1 >= len(a) or a[i + 1].startswith("--"):
            print("ship: --target needs a value. Refusing to run without bumping the round, "
                  "because that would skip the bedrock-cap check.")
            return 1
        target = a[i + 1]
    if what == "pre":
        return cmd_pre(ranges, target)
    if what == "post":
        return cmd_verify(ranges)
    if what == "plan":
        return cmd_plan(ranges)
    if what == "check":
        return cmd_check()
    print(__doc__)
    return 1


if __name__ == "__main__":
    sys.exit(main())
