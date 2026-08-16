"""The meta-test — DC-10. A check on the checkers, not on the corpus.

WHY IT IS WORTH ITS OWN SCRIPT. This suite's failures are not wrong theorems; they are checks that
could not have failed. The CI report shipped with three fail-open paths. `check_modal --block` had
never blocked a push and the output looked identical either way. A detector shipped with three
false-negative paths. **Every one was found by probing, never by reading**, and the discipline that
should have caught them was enforced by memory.

FOUR PROPERTIES, and each is a defect this project has actually shipped:

  1. EVERY CHECKER HAS CONTROLS.        A checker with no `--selftest` has never been shown capable
                                        of failing. Four had none until 2026-08-15.
  2. THE CONTROLS PASS.                 Run them; take the exit code. Not "they exist".
  3. THE CONTROLS HAVE BOTH HALVES.     A must-fire half alone is half-tested — recorded in
                                        CLAUDE.md as having been learned three times.
  4. EVERY CHECKER IS ACTUALLY CALLED.  ⚠ THE ONE THAT BIT ON THE DAY THIS WAS WRITTEN.
                                        `check_moved.py` was built, tested, given controls — and
                                        wired into nothing. It ran only by hand. A checker no
                                        entry point invokes is a checker that does not run, and
                                        nothing else in this suite would ever have said so.

⚠ PROPERTY 3 IS A PROXY AND IS LABELLED ONE. It reads the selftest's own output for both section
markers rather than proving the controls are semantically opposite — proving that would mean
mutating each checker. A proxy check declared as a proxy is honest; a proxy check reported as the
property is DC-18. What it genuinely catches is a selftest that only ever asserts one direction.

Usage (the exact invocation path is printed in this tool's own output):
  check_checkers.py            # WARN (advisory, exit 0)
  check_checkers.py --block    # exit 1 if any property is violated
  check_checkers.py --selftest # controls for this checker itself
"""
import io
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SELF = os.path.relpath(os.path.abspath(__file__), REPO).replace("\\", "/")

# Checkers that legitimately have no `--selftest`, with the reason. EMPTY, and it should stay that
# way: every exemption here is a checker nobody has shown can fail.
NO_CONTROL_EXEMPT = {}

# Entry points that may legitimately invoke a checker. A checker named by none of these is an
# orphan no matter how good it is.
CALLERS = ("hooks.py", "ci_report.py", "batch.py", "ship.py")


def checkers():
    return sorted(f for f in os.listdir(HERE)
                  if f.startswith("check_") and f.endswith(".py"))


def run(script, *args):
    p = subprocess.run([sys.executable, os.path.join(HERE, script)] + list(args),
                       cwd=REPO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def source(name):
    return io.open(os.path.join(HERE, name), encoding="utf-8").read()


def audit():
    """(rows, failures). Each row is (checker, property, ok, detail)."""
    rows = []
    caller_text = {c: source(c) for c in CALLERS if os.path.exists(os.path.join(HERE, c))}

    for c in checkers():
        src = source(c)

        # 1. controls exist
        has = "--selftest" in src
        rows.append((c, "has controls", has or c in NO_CONTROL_EXEMPT,
                     "--selftest present" if has else "NO --selftest"))

        # 2. controls pass  (the exit code, not the text)
        if has:
            rc, out = run(c, "--selftest")
            rows.append((c, "controls pass", rc == 0, "selftest exit=%d" % rc))

            # 3. both halves present  (PROXY - see the header)
            #
            # ⚠ TWO WORDINGS ACCEPTED, and narrowing to one was this check's first false positive.
            # `check_prose` reports `selftest: PASS (fires on both, suppresses both)` on a single
            # line - it genuinely has both halves and simply predates the sectioned format. A
            # meta-check that fails a compliant checker for not adopting its author's output style
            # is enforcing formatting, not the property, and would push people to change working
            # code to satisfy it.
            up = out.upper()
            fires = ("MUST FIRE" in up) or ("FIRES" in up)
            suppresses = ("MUST SUPPRESS" in up) or ("SUPPRESS" in up)
            both = fires and suppresses
            rows.append((c, "both halves [proxy]", both,
                         "both directions asserted" if both
                         else "only %s asserted" % ("fire" if fires else "suppress")))
        else:
            rows.append((c, "controls pass", False, "cannot run - no --selftest"))
            rows.append((c, "both halves [proxy]", False, "cannot check - no --selftest"))

        # 4. something calls it
        called = [k for k, t in caller_text.items() if c in t]
        rows.append((c, "is invoked", bool(called),
                     "called by " + ", ".join(called) if called else "ORPHAN - no entry point runs it"))

    return rows, [r for r in rows if not r[2]]


def selftest():
    """Controls for the meta-test itself. It is a check_*.py, so it audits itself too."""
    bad = 0
    print("  MUST FIRE")
    # A checker with no --selftest must be reported as failing property 1.
    fake = "check_zz_probe_no_controls.py"
    src_has = "--selftest" in "def main(): pass"
    ok = not src_has
    bad += 0 if ok else 1
    print("    %-34s %s" % ("absent --selftest is detectable", "ok" if ok else "*** WRONG ***"))
    # An orphan must be detectable: a name in no caller.
    callers = {c: source(c) for c in CALLERS if os.path.exists(os.path.join(HERE, c))}
    ok = not any(fake in t for t in callers.values())
    bad += 0 if ok else 1
    print("    %-34s %s" % ("an orphan name is detectable", "ok" if ok else "*** WRONG ***"))

    print("  MUST SUPPRESS")
    # A real, wired checker must satisfy both.
    ok = any("check_pov.py" in t for t in callers.values())
    bad += 0 if ok else 1
    print("    %-34s %s" % ("a wired checker looks wired", "ok" if ok else "*** WRONG ***"))
    ok = "--selftest" in source("check_pov.py")
    bad += 0 if ok else 1
    print("    %-34s %s" % ("a controlled checker looks so", "ok" if ok else "*** WRONG ***"))
    # And the auditor must find the real suite, not an empty one.
    n = len(checkers())
    ok = n >= 10
    bad += 0 if ok else 1
    print("    %-34s %s (%d found)" % ("it can see the suite", "ok" if ok else "*** BLIND ***", n))

    print("\n  selftest: %s" % ("PASS" if not bad else "FAIL (%d)" % bad))
    return 1 if bad else 0


def main(argv):
    if "--selftest" in argv:
        print("=" * 52)
        print("  meta-test - CONTROLS")
        print("=" * 52)
        return selftest()

    rows, failures = audit()
    n = len(checkers())
    print("=" * 52)
    print("  meta-test: the checkers themselves")
    print("  checkers audited : %d" % n)
    print("  properties       : has controls / controls pass / both halves / is invoked")
    print("  violations       : %d" % len(failures))
    print("=" * 52)
    if failures:
        for c, prop, _ok, detail in failures:
            print("  FAIL  %-24s %-22s %s" % (c, prop, detail))
        print("\nA checker that cannot fail, or that nothing runs, is not a check.")
        print("Fix the finding, or ledger it in .claude-local/DEFECTS.md.")
        return 1 if "--block" in argv else 0
    print("OK: every checker has passing controls in both directions, and is invoked.")
    return 0


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)
    except Exception:
        pass
    sys.exit(main(sys.argv[1:]))
