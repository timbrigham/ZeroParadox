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

# gate key -> (command file to read, signal file it writes, human name)
GATES = {
    "editorial": ("editorial-review.md", "er_cleared.txt", "/editorial-review"),
    "adversary": ("adversary-review.md", "ar_cleared.txt", "/adversary-review"),
    "prior-art": ("prior-art-review.md", "pa_cleared.txt", "/prior-art-review"),
    # ⚠ `/rely` writes `rely_cleared.txt` too, as of 2026-08-10. It used to write nothing while
    # `batch.py`'s routing blocked on that exact file — so it was the one gate that did not produce
    # the metadata the hook consumes, and the CALLER had to write it about its own work, which is
    # the self-certification the routing exists to prevent. Its line 1 records REVIEWED, never PASS:
    # `/rely` still issues no verdict, it records which hashes were examined.
    "rely":      ("rely.md",             "rely_cleared.txt", "/rely"),
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
    """WHICH gates this change owes and WHY — the same predicates the hook enforces.

    Decidable, so it lives here rather than in anyone's memory. Returns (scope, [(key, why)])."""
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
    # ⚠ SECOND CONSUMER OF `check_routing`, AND THE WARRANT IS BLIND TO BOTH. `batch.py`'s prepush
    # site is the other. A `guards.py` route asserting the router still BLOCKS has to cover this one
    # too, or half the enforcement can be removed with the control still green.
    # ⚠ A non-blocking row does not raise a requirement here. `need` is what `ship.py` will refuse to
    # proceed without, and a leg deliberately downgraded to WARN is by definition not that — carrying
    # it would re-impose at release the block that was lifted at push, which is the `rely_capped()`
    # deadlock in a new place.
    for agent, ran, why, blocking in batch.check_routing({}, ranges):
        if agent == "/rely" and not ran and blocking:
            base = why.split("—")[0].strip()
            capped, reason = rely_capped()
            # ⚠ A CAP NEVER MAKES THE HOOK LENIENT. This used to DROP the requirement when capped,
            # so `ship.py post` reported PASS exit 0 for a push `batch.py prepush` refused exit 1 —
            # and the only way out of that deadlock was hand-writing the hash lines, i.e. the caller
            # certifying its own work, which is the exact thing the routing exists to prevent.
            # The project's own scheme already says how this resolves: a capped reviewer WRITES ITS
            # SIGNAL, and the hook then clears on its own merits. So the cap governs what the next
            # pass is FOR — re-signing the current hashes rather than hunting further findings —
            # never whether a signal is owed. Found by /rely pass 6.
            need.append(("rely", base + (
                " — CAPPED (%s). This pass RE-SIGNS the current hashes; do not iterate on findings."
                % reason if capped else "")))
    return scope, need


RELY_CAP = 2


def rely_capped():
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
    sig = os.path.join(PRIV, "rely_cleared.txt")
    if not os.path.exists(sig):
        return False, ""
    line1 = io.open(sig, encoding="utf-8-sig", errors="replace").readline()
    m = re.search(r"BLOCKING:\s*(\d+)", line1, re.I)
    blocking = int(m.group(1)) if m else None
    if blocking is None:
        # A cap that cannot read the signal is not a cap. Say so instead of quietly not capping —
        # silent non-capping is precisely the unbounded loop the cap exists to stop.
        return False, ("SIGNAL MALFORMED — no `BLOCKING:<n>` on line 1 of rely_cleared.txt, so the "
                       "cap cannot be evaluated. Re-run /rely; do not read this as 'not capped'.")

    # ⚠ COUNT PASSES FROM THE SIGNAL, not only from the round counter. Measured 2026-08-10: five
    # /rely passes had run and `gate_round.json` recorded `rely-verification-layer x1`, because the
    # bump only happens when a caller remembers `--target` — so the cap Tim asked for could never
    # fire. The reviewer writes its own pass number into line 1 ("pass 5"), which is the one record
    # that cannot be skipped by forgetting a flag. Take the larger of the two.
    _rc, out = batch.sh(sys.executable, os.path.join(BASE, "gate_round.py"), "show")
    pm = re.search(r"rely-verification-layer\s+x(\d+)", out)
    sm = re.search(r"\bpass\s+(\d+)", line1, re.I)
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

    # FREEZE the review scope — in `pre` ONLY, never in `plan`. Restored 2026-08-10 (Tim: *"we used
    # to have logic that locked those files from being accidentally edited... might have been lost
    # in the revamp"* — correct: `gatelock.py` still had `acquire`, both hooks still ran `guard`,
    # and NOTHING called `acquire`; the guard survived and the lock it guards was never taken).
    #
    # It exists because discipline demonstrably failed twice: the caller wrote "the tree is stable"
    # into a gate brief and then edited the reviewed files mid-round, once invalidating a signal
    # computed against a tree that had moved. v2 sets the read-only attribute, so the Edit tool
    # fails at the syscall with EPERM rather than reporting success on a write that landed.
    #
    # ⚠ It was briefly wired into `cmd_plan`, which strands the tree on a read-only inspection
    # command — measured within minutes: a cap drill left a lock held and the next `plan` refused.
    # `plan` inspects and runs nothing; only `pre` commits you to a round.
    # ⚠ Released by `ship.py post`, so fixing findings between rounds is unblocked. An abandoned run
    # leaves it held, the pre-push guard refuses, and recovery is `gatelock.py sweep --clear`.
    # ⚠ This guards the CALLER's accidental edits. It is NOT the protection against an agent
    # mutating git state (that is the worktree rule, AGT-1) — different vector.
    scope = batch.reviewable_changed(ranges)
    if scope:
        rc, out = batch.sh(sys.executable, os.path.join(BASE, "gatelock.py"), "acquire",
                           "--round", str(gate_round()),
                           "--reason", "ship: gates reading this scope", *scope)
        print(out.rstrip())
        if rc != 0:
            report.done("ship pre", False,
                        "could not freeze the review scope — refusing to spawn gates against a "
                        "tree that can move under them. Resolve above, or `gatelock.py sweep --clear`.")
            return 1
        print("  scope FROZEN for the gate window; `ship.py post` releases it.")
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
                [("signals", "BLOCK", "every required signal fresh and covering the scope")])
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
    _rc, sh_out = batch.sh(sys.executable, os.path.join(BASE, "selfheal.py"))
    tail = [l for l in sh_out.splitlines() if l.strip().startswith("⚠") and "shape(s)" in l]
    if tail:
        print("\n  self-heal: %s" % tail[0].strip().lstrip("⚠ "))
        print("             run `python %s/selfheal.py` for the suggestions"
              % os.path.dirname(SELF))

    # FREEZE the files the gates are about to read. Restored 2026-08-10 (Tim: *"we used to have
    # logic that locked those files from being accidentally edited... might have been lost in the
    # revamp"* — correct: `gatelock.py` still had `acquire`, both hooks still ran `guard`, and
    # NOTHING called `acquire`. The guard survived and the lock it guards was never taken).
    #
    # It exists because discipline demonstrably failed twice: the caller wrote "the tree is stable"
    # into a gate brief and then edited the reviewed files mid-round, once invalidating a signal
    # computed against a tree that had moved. v2 sets the read-only attribute, so the Edit tool
    # fails at the syscall with EPERM rather than reporting success on a write that landed.
    #
    # ⚠ Released by `ship.py post`, so fixing findings between rounds is unblocked. If a run is
    # abandoned mid-round the lock stays held, the pre-push guard refuses, and recovery is
    # `gatelock.py sweep --clear` — that is fail-closed on purpose.
    # ⚠ This protects against the CALLER's accidental edits. It is NOT the protection against an
    # agent mutating git state (that is the worktree rule, AGT-1) — different vector.
    print("\n  SHIP_SCOPE=%s" % ",".join(scope))
    print("  SHIP_GATES=%s" % ",".join(k for k, _w in need))
    print("  SHIP_ROUND=%d" % rnd)
    return 0


def cmd_check():
    return batch.sh(sys.executable, os.path.join(BASE, "batch.py"), "precommit")[0]


def cmd_verify(ranges):
    refuse_if_scope_unknown(ranges, 'a signal verdict')
    # UNFREEZE first: the gates have finished reading, and the caller needs to be able to fix what
    # they found. Released here rather than left to the operator, because an unreleased lock blocks
    # the next push and the recovery command is one nobody remembers under pressure.
    rc, out = batch.sh(sys.executable, os.path.join(BASE, "gatelock.py"), "release")
    line = [l for l in out.splitlines() if l.strip()]
    if line:
        print("  gatelock: %s" % line[0].strip())

    scope, need = required_gates(ranges)
    keys = {k for k, _w in need}
    bad = 0
    report.banner("ship — verify", [
        ("scope", "%d reviewable file(s)" % len(scope)),
        ("expect", ", ".join(sorted(keys)) or "no gates required"),
    ])
    for name, valid, why in batch.check_signals(ranges):
        needed = (name != "pa_cleared.txt") or ("prior-art" in keys)
        ok = valid or not needed
        print("  %-20s %-4s %s" % (name, "ok" if ok else "FAIL", why))
        v = batch.signal_verdict(name)
        if v:
            print("      verdict  %s" % v)
        bad += 0 if ok else 1
    if "rely" in keys:
        print("  %-20s %-4s %s" % ("/rely", "FAIL",
                                   "verification layer changed since /rely last signed it"))
        bad += 1
    report.done("ship verify", bad == 0,
                "all required signals present and covering" if bad == 0
                else "%d outstanding" % bad)

    # Answer the standing question at the END of a run as well as the start. Tim, 2026-08-10:
    # *"what should we be doing here and now to make the next run better? that's the question that
    # I'm going to keep wanting to ask."* Asked at `pre` it reports what the last runs cost; asked
    # here it reports what THIS run just added, while the evidence is still in front of you.
    print("")
    _rc, out = batch.sh(sys.executable, os.path.join(BASE, "selfheal.py"))
    tail = out.split("WHAT TO DO BEFORE THE NEXT RUN", 1)
    if len(tail) == 2:
        print("  WHAT TO DO BEFORE THE NEXT RUN" + tail[1].rstrip())
    return 1 if bad else 0


def main():
    a = sys.argv[1:]
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
