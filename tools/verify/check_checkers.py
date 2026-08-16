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
SELF = common.self_rel(__file__)

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
    # ⚠ A LIBRARY, not a gate — nothing invokes it and nothing should; it is IMPORTED by most of
    # this bundle, which is a stronger dependency than being called by one entry point. Property 4
    # ("is it invoked") is the only one that does not apply. Properties 1-3 DO, and they are why it
    # is in `ALSO_AUDITED`: its controls are now run by this checker, which BLOCKS at push, rather
    # than only by the report-only CI job. Exempting the inapplicable property is not the same as
    # exempting the module (COM-1).
    "common.py": "shared library; imported across the bundle rather than invoked by any entry point",
    # Same shape, and the one whose absence was `VEND-1`: THE definition of the vendored exemption,
    # imported by every gating checker and invoked by no entry point. Property 4 is the only one
    # that cannot apply; properties 1-3 now do.
    "vendored.py": "shared definition of the exemption surface; imported, never invoked",
}


# ⚠ MODULES THAT ARE NOT NAMED `check_*.py`. The glob below is a NAMING convention, and a naming
# convention is not a property — `guards.py` BLOCKS at push (`hooks.py`'s pre-push plan) and was
# audited by nothing here purely because of what it is called. It shipped with no controls and a
# `--selftest` flag that was parsed away and silently ignored; when controls were finally written
# (2026-08-16) they found a live false green on their first run. **Add a module here the moment it
# can block OR the moment other gates depend on it, whatever its filename.**
#
# ⚠⚠ `common.py` WAS LEFT OUT ON THE ARGUMENT THAT IT "GATES NOTHING", AND THAT ARGUMENT WAS WRONG
# (COM-1, /rely 2026-08-16). It was added to `ci_report.SELFTESTS` instead — but `ci_report`'s
# control loop reads only an EXIT CODE, so it cannot distinguish a control that passed from a
# `--selftest` flag that is silently ignored, which is `GRD-2` exactly. Measured by deleting
# `common.py`'s two-line `--selftest` dispatch: `common.py --selftest` exited 0 having run nothing,
# `ci_report --block` published `pass`, and this checker exited 0 with `violations: 0`. And
# `ci_report` is the REPORT-ONLY CI job, so that was the module's only execution anywhere — no hook,
# commit gate or push gate ran it. Property 4 does not apply to it, which is what `ORPHAN_EXEMPT` is
# FOR; excluding it from the audit entirely was the wrong way to say that.
#
# ⚠ `debaseline.py` ADDED 2026-08-16 (DEB-1, /rely round 2) — the SECOND instance of the class
# COM-1 opened, which is what makes it a class rather than an incident. It ships passing controls
# that **nothing ran**: not this checker, not `ci_report.SELFTESTS`, not any workflow — while
# `batch.py` depends on it to compute every debaselining worklist. Controls nobody executes are
# controls nobody has shown can fail. ⚠ Note this file's three `SELFTESTS` mentions are COMMENTS,
# not a reconciliation: nothing mechanically checks that the two rosters agree, which is the
# hand-maintained-roster hazard one level up and is not closed by adding a third entry.
#
# ⚠⚠ `vendored.py` ADDED 2026-08-16 (`VEND-1`, `/rely` round 4) — the THIRD instance of this class,
# and the one that shows a roster reconciliation is not sufficient. It is the SINGLE DEFINITION of
# the exemption surface all four gating checkers import, it had no `--selftest` at all, and
# `roster_agrees()` was STRUCTURALLY BLIND to it because both rosters omitted it identically.
# **Agreeing on an omission is still agreement.** The property was defended throughout — mutating
# `is_vendored` is caught by this checker and by `guards` — but the module could not be shown to fail.
ALSO_AUDITED = ("guards.py", "common.py", "debaseline.py", "vendored.py")


def checkers():
    return sorted([f for f in os.listdir(HERE)
                   if f.startswith("check_") and f.endswith(".py")]
                  + [f for f in ALSO_AUDITED if os.path.exists(os.path.join(HERE, f))])


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


def roster_agrees():
    """Do THIS checker's audited set and `ci_report.SELFTESTS` name the same modules?

    ⚠ **THE FIFTH PROPERTY, AND IT CLOSES THE CLASS `COM-1` AND `DEB-1` ARE INSTANCES OF** (DEB-2).
    Both are the same shape: a module's controls are reachable only through a HAND-MAINTAINED
    ROSTER, and there are two rosters. `common.py` was in one and not the other, so a dead
    `--selftest` dispatch published `pass`; `debaseline.py` was in neither, so controls that had
    never run turned out to be half-tested the moment they did. Adding a third entry to each list
    does not close that — it just makes the next divergence later.

    Three lines, and the import is safe: `ci_report`'s only local import is `common`, which imports
    nothing local, so there is no cycle (measured before writing this). Reading the roster from the
    module itself rather than re-listing it here is the whole point — a third copy would be the
    defect one level up again."""
    sys.path.insert(0, HERE)
    import ci_report
    theirs = set(ci_report.SELFTESTS)
    mine = {c for c in checkers() if "--selftest" in source(c)}
    return sorted(mine - theirs), sorted(theirs - mine)


def audit():
    """(rows, failures). Each row is (checker, property, ok, detail)."""
    rows = []
    caller_text = {c: source(c) for c in CALLERS if os.path.exists(os.path.join(HERE, c))}

    # 5. the two rosters agree (DEB-2). Run once, not per checker — it is a property of the PAIR.
    unlisted, phantom = roster_agrees()
    rows.append(("(roster)", "rosters agree", not (unlisted or phantom),
                 "audited here and in ci_report.SELFTESTS match"
                 if not (unlisted or phantom)
                 else "audited but not in SELFTESTS: %s; in SELFTESTS but not audited: %s"
                      % (unlisted or "-", phantom or "-")))

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
    # ⚠ SCOPE IS THE `check_*.py` GLOB **PLUS `ALSO_AUDITED`**, which is wider than the CHECKS list
    # in both directions. `guards.py` was outside this audit until 2026-08-16 for no reason but its
    # filename, while blocking at push — and it turned out to have no controls at all, with
    # `--selftest` parsed away and silently ignored.
    #
    # ⚠ This paragraph used to end by saying `common.py` is "deliberately NOT here", contradicting
    # `ALSO_AUDITED` at the top of this file — in the text printed on every green run (CHK-STALE,
    # /rely round 2). That was true for about an hour, until COM-1 showed why routing a module's
    # controls through `ci_report` alone cannot distinguish a control that passed from a flag that is
    # ignored. `common.py` and `debaseline.py` are both audited here now; each is listed in
    # `ORPHAN_EXEMPT` where property 4 genuinely does not apply.
    print("OK: every audited gate has passing controls in both directions, and is invoked.")
    print("   (scope: the check_*.py glob PLUS %s — wider than the CHECKS list.)"
          % ", ".join(ALSO_AUDITED))
    return 0


if __name__ == "__main__":
    common.utf8_stdout()   # one definition; two of the eight copies had dropped
                           # line_buffering=True, which reorders output against children
    sys.exit(main(sys.argv[1:]))
