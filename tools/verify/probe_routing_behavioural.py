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

    python tools/verify/probe_routing_behavioural.py
"""
import io
import os
import re
import shutil
import subprocess
import sys
import tempfile

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
    so it is the thing the control must observe."""
    p = subprocess.run([sys.executable, os.path.join(wt, "tools", "verify", "batch.py"), "prepush"],
                       capture_output=True, text=True, encoding="utf-8", errors="replace", cwd=wt)
    return p.returncode


def _row_state(rows, needle):
    hits = [v for k, v in rows.items() if needle in k]
    if not hits:
        return "ABSENT"
    return "FAIL" if "FAIL" in hits else "ok"


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
        # MUST STAY BLOCKING: annihilating the caller's own count cannot hide a ROUTING failure,
        # because that count comes from the registry and never passes through this argument. This is
        # the property attempt six actually buys, stated so it can be measured rather than asserted.
        ("RLY28-1b caller annihilates the inline count", batch,
         lambda s: s.replace("    enforce_prepush_verdict(bad)",
                             "    enforce_prepush_verdict(bad * 0)"),
         EXIT_NEEDLE, "BLOCKS"),
        # MUST GO RED: deleting the enforcement outright is the one consumer-side move left, and the
        # AST row is what makes it loud. ⚠ Judged on the guards ROW, not the exit code — a deleted
        # enforcement genuinely does let prepush exit 0, so "still blocks" is not achievable here and
        # demanding it would be a control that can never pass.
        ("NEUTER   cmd_prepush discards the enforcement call", batch,
         lambda s: s.replace("    enforce_prepush_verdict(bad)", "    pass"),
         "prepush enforces the verdict", "FAIL"),
    ]


def main():
    tmp = tempfile.mkdtemp(prefix="zp_routing_probe_")
    wt = os.path.join(tmp, "wt")
    print("%s — mutation control for the behavioural routing routes" % SELF)
    add = subprocess.run(["git", "worktree", "add", "--detach", wt, "HEAD"],
                         capture_output=True, text=True, encoding="utf-8", errors="replace",
                         cwd=REPO)
    if add.returncode != 0:
        print("  cannot provision a worktree — REFUSING to run in the shared tree.")
        print(  (add.stdout + add.stderr).strip()[:500])
        shutil.rmtree(tmp, ignore_errors=True)
        return 2
    try:
        # The worktree is at HEAD; copy the WORKING copies in, so the control tests what is about to
        # be committed rather than what already was.
        for f in ("guards.py", "batch.py", "ship.py", "report.py", "common.py", "agent_gate.py",
                  "scan_routing_consumers.py"):
            src = os.path.join(REPO, "tools", "verify", f)
            if os.path.exists(src):
                shutil.copyfile(src, os.path.join(wt, "tools", "verify", f))
        ship = os.path.join(wt, "tools", "verify", "ship.py")
        batch = os.path.join(wt, "tools", "verify", "batch.py")

        muts = mutations(ship, batch)
        _rc, base = _guards_rows(wt)
        needles = sorted({m[3] for m in muts})
        print("  baseline (unmutated):")
        bad = 0
        for n in needles:
            if n == EXIT_NEEDLE:
                # ⚠⚠ THE PRECONDITION, AND WITHOUT IT THE EXIT-CODE CASES PROVE NOTHING. Discarding
                # the verdict is only observable while there IS a verdict to discard: on a fully
                # green tree prepush exits 0 either way and the mutation looks harmless. The
                # worktree supplies the failing state for free — it is detached at HEAD and
                # `.claude-local/` is gitignored, so the `/rely` signal is absent there and the
                # routing legs FAIL. If that ever stops holding, this control has lost its teeth
                # and must say so rather than pass.
                state = "BLOCKS" if _prepush_exit(wt) != 0 else "PASSES"
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

        print()
        fails = 0
        for label, path, mutate, needle, want in muts:
            original = _read(path)
            mutated = mutate(original)
            if mutated == original:
                print("  !! %-52s MUTATION DID NOT APPLY — anchor missing" % label)
                fails += 1
                continue
            _write(path, mutated)
            try:
                if needle == EXIT_NEEDLE:
                    # ⚠ THE END-TO-END OBSERVABLE. A `guards.py` row is computed by calling the
                    # verdict functions in guards' own frame, where the property survives any
                    # amount of discarding by `cmd_prepush`. The EXIT CODE is what the hook
                    # consumes, so it is the only thing a consumer-side neuter cannot fake.
                    got = "BLOCKS" if _prepush_exit(wt) != 0 else "PASSES"
                else:
                    _rc, rows = _guards_rows(wt)
                    got = _row_state(rows, needle)
            finally:
                _write(path, original)
            ok = (got == want)
            fails += 0 if ok else 1
            print("  %-6s %-52s row[%s]=%s (want %s)"
                  % ("PASS" if ok else "**FAIL", label, needle, got, want))
        print()
        print("  RESULT: %d of %d behaved as required" % (len(muts) - fails, len(muts)))
        if fails:
            print("  ** A behavioural route did not respond to a real neuter. `CLAUDE.md` rung 5 and")
            print("     the stopping rule in queue/: this is the FOURTH defeat of this control, and")
            print("     the answer is to GIVE UP THE EXEMPTION, not to write attempt five. **")
        return 1 if fails else 0
    finally:
        subprocess.run(["git", "worktree", "remove", "--force", wt],
                       capture_output=True, text=True, cwd=REPO)
        subprocess.run(["git", "worktree", "prune"], capture_output=True, text=True, cwd=REPO)
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
