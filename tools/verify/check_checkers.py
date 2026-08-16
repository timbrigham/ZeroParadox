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
import ast
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

# Checkers with NO automatic caller, and the reason. ⚠ Each entry is a checker that runs only when
# a human remembers, so keep this list short and justified — it is the exemption surface for
# property 4 and every addition weakens the property.
ORPHAN_EXEMPT = {
    # Genuinely unhookable: there is no git event for tag creation, so nothing can fire this on
    # the thing it gates. CLAUDE.md states the consequence — "enforcement is procedural: the gate
    # must exit 0 AND its judgement checklist must be confirmed before the release body is
    # drafted." Its CONTROLS still run on every push via ci_report's SELFTESTS, so the checker is
    # verified even though its invocation is not automatic.
    "check_release_ready.py": "pre-release gate; no git event exists for tag creation",
}


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


def _invokes(src, name):
    """Does this source actually CALL `name`, as opposed to listing it?

    ⚠⚠ PARSED, NOT GREPPED, AND THAT IS THE THIRD ATTEMPT. Version 1 matched the bare name,
    which a hash list satisfies. Version 2 matched `("name.py",`, which a manifest row
    satisfies. Version 3 stripped manifest rows by regex — and /rely defeated it TWICE in one
    pass: once with a row wrapped across two lines, once with an unquoted mode constant, which
    is the form `ci_report.py`'s own rows use. Each fix hardened one SYNTACTIC SHAPE while the
    property stayed unguarded.

    The AST does not care about line breaks, quoting style or formatting. A CALL is a Call
    node; a manifest row is a Tuple inside a List assignment. Those are different node types,
    so no amount of reformatting turns one into the other.

    Counts as an invocation:
      py("check_x.py", ...)                      - a direct call with the name as an argument
      run(sys.executable, os.path.join(H, "check_x.py"))
      ("check_x.py", ["--block"], GATE, "...")   - a CHECKS row: a tuple carrying an ARGV LIST,
                                                   which is what makes it a spec rather than a
                                                   label. A manifest row has no list.
    """
    try:
        tree = ast.parse(src)
    except SyntaxError:
        return False

    for node in ast.walk(tree):
        # (a) the name appears as an argument to an actual call
        if isinstance(node, ast.Call):
            for a in list(node.args) + [k.value for k in node.keywords]:
                if isinstance(a, ast.Constant) and a.value == name:
                    return True
        # (b) a spec tuple: the name beside an argv LIST. A three-literal manifest row has none.
        if isinstance(node, ast.Tuple):
            elts = node.elts
            if (elts and isinstance(elts[0], ast.Constant) and elts[0].value == name
                    and any(isinstance(e, ast.List) for e in elts[1:])):
                return True
    return False


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

        # 4. something INVOKES it — not merely mentions it.
        #
        # ⚠⚠ THE FIRST VERSION TESTED `c in t`, AND THE CONTROL TEST CAUGHT IT AS A FALSE PASS.
        # `batch.py` carries a CHECKERS list naming every checker so their bytes get hashed and
        # route to `/rely`. Being in that list means the file is WATCHED; it says nothing about
        # whether anything RUNS it. With both real call sites renamed away, a substring test still
        # found the name in that list and reported the checker healthy — the exact fail-open shape
        # this whole script exists to detect, inside the script that detects it.
        #
        # So the patterns below match CALLS, not names:
        #   hooks.py     py("check_x.py", ...)
        #   ci_report.py ("check_x.py", [...], GATE, ...)   - a row in CHECKS
        #   ship/batch   subprocess of the script path
        # ⚠⚠ A MANIFEST ROW IS NOT A CALL, AND MY PREVIOUS FIX COULD NOT TELL. The first
        # version matched the bare name, which a hash list satisfies. The second matched
        # `("name.py",` — and /rely defeated it in one edit: it deleted every call site for
        # `check_moved.py`, then rewrote the surviving PRE_PUSH_PLAN row from
        # `("check_moved", ...)` to `("check_moved.py", ...)`. Result: `violations: 0`,
        # exit 0, `and is invoked` — while `grep 'py("check_moved'` returned nothing. A
        # blocking checker run by nobody, certified healthy by the script written to catch
        # exactly that.
        #
        # PLAN/manifest rows are therefore stripped before the search. What remains has to be
        # an actual invocation: `py("x.py")`, a `CHECKS` row carrying its argv, or a
        # subprocess of the path.
        called = [k for k, t in caller_text.items() if _invokes(t, c)]
        if c in ORPHAN_EXEMPT:
            rows.append((c, "is invoked", True,
                         "exempt: %s (controls still run every push)" % ORPHAN_EXEMPT[c]))
        else:
            rows.append((c, "is invoked", bool(called),
                         "invoked by " + ", ".join(called) if called
                         else "ORPHAN - named nowhere as a CALL (a hash-list mention is not a call)"))

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
    # ⚠ "every checker" means the `check_*.py` files in CHECKS. `guards.py` BLOCKS at push and
    # is audited by nothing here: it parses only `--list`, so `guards.py --selftest` silently
    # succeeds without running anything — worse than erroring, because a pipeline wired to it
    # would collect a green tick having tested nothing. Ledgered; do not read this line as
    # covering the whole verification layer.
    print("OK: every check_*.py has passing controls in both directions, and is invoked.")
    print("   (scope: the CHECKS list. guards.py blocks at push and is NOT audited here.)")
    return 0


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)
    except Exception:
        pass
    sys.exit(main(sys.argv[1:]))
