"""Run the deterministic checkers and publish what they found, as a markdown report.

VERIFICATION_BUILDOUT Phase 3. The goal in the buildout's first sentence is *"run those checks in
public CI so nobody takes our word for it"* — until now every checker ran only on one machine, and
**a bypassed local gate is invisible**. This is the step that turns a local claim into public
evidence.

REPORT-ONLY BY DEFAULT, AND THAT IS DELIBERATE. Phase 3 publishes; Phase 4 makes it block, via
branch protection on `main`.

⚠ FLIPPING IT IS **NOT** FREE, AND THIS PARAGRAPH SAID IT WAS UNTIL 2026-08-15. The claim was
that `--block` is the whole change because the exit code is already computed honestly. Measured
in the real CI environment (a checkout with no Mathlib), it is not:

  1. `check_paths.py` legitimately returns 3 (EXIT_SKIPPED) there, and a skip is scored as a
     non-failure, so `ci_report.py --block` exits 0 while that gate has not run. Adding
     `--block` today would publish a GREEN REQUIRED CHECK covering a gate that was skipped.
  2. `SKIPPED_RC = 3` is applied to every row, but only `check_paths.py` defines it. So ANY
     checker can exempt itself from the CI gate by returning 3 — verified by patching
     `check_pov.py`'s gate path to return 3, after which `--block` exits 0 and the row reads
     `**skipped**` with its controls still passing. `guards.py --list` registers four routes
     for a FILE to self-exempt and none for a CHECKER to.

Both are prerequisites for Phase 4, ledgered as such. Until they are closed, `--block` buys a
worse signal than no signal: a required check that is green because nothing ran.

⚠ **EXIT CODES ARE TAKEN AS VALUES, NEVER INFERRED FROM LOG TEXT.** The buildout records three
fail-opens in an earlier CI report that all came from parsing output: Lean tags some diagnostics
`error(lean.xxx):` with no bare `error:` in them, and `tee` swallows a command's status unless
`PIPESTATUS` is read. Every verdict below is `subprocess.returncode`, an integer.

⚠ **THE BASELINE COUNT IS PUBLISHED BESIDE THE GREEN, and that is the point of the table.** These
checkers block on NEW sites only; several hundred known sites are grandfathered. A report saying
"0 violations" while hundreds of sites sit suppressed would be true and misleading in the way this
project most often gets caught. "0 new, N grandfathered" is the honest form, and it makes the debt
visible on every run instead of only when someone thinks to ask.

⚠ The count itself is NEVER written here — it is computed by `baselines()` on every run. Recording
it in this docstring would be DC-6 in the file whose job is to publish it honestly.

    python tools/verify/ci_report.py            # report, always exit 0  (Phase 3)
    python tools/verify/ci_report.py --block    # exit 1 if any checker failed (Phase 4)
"""
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

# Checkers that run against the PUBLIC corpus alone. Each is (script, args, what it enforces).
#
# ⚠ Deliberately excluded, with reasons, so the omissions are visible rather than silent:
#   guards.py            - writes probe files to test each exemption route and restores them. Safe
#                          on an ephemeral runner, but it MUTATES the tree; it goes in once this
#                          report has been quiet for an arc, not in the first cut.
#   check_release_ready  - needs a release tag argument; it is a pre-release gate, not a per-push one.
#   check_paths --all    - the extra scope is the private notes layer, which does not exist in CI.
# ⚠⚠ `--block` HERE IS NOT THE SAME FLAG AS `--block` ON THIS SCRIPT, AND CONFLATING THEM SHIPPED A
# FAIL-OPEN. The first version ran every checker with NO arguments. In warn mode a checker prints
# its findings and exits 0, so the report rendered `check_pov.py | pass` with a planted DENIAL
# sitting in the tree — the report was structurally incapable of ever showing a violation. Measured
# locally before this workflow ever ran, by planting one.
#
#   `--block` on the CHECKER  = report the finding honestly in the exit code (always wanted here)
#   `--block` on ci_report.py = let a finding fail the CI JOB          (Phase 4, not yet)
#
# This is the exact defect the buildout records for `check_modal --block`: it had never blocked a
# push and the output looked identical either way. A checker invoked in the mode that cannot fail
# is not a check.
# (script, args, mode, what). MODE IS PUBLISHED, because a gate that does not declare its own
# enforcement mode cannot be audited by reading its output — three defects hid behind exactly that.
#
#   GATE    a finding is a failure; the run goes red.
#   COUNT   a number worth watching that is NOT a pass/fail. Never run with --block.
#
# ⚠ `check_poles` is a COUNT, and this is not a softening. It is a counter with NO BASELINE (REL-3):
# 29 known pre-existing pole-equality sites, which is why batch.py deliberately excludes it from
# GATING_CHECKERS. Run with --block it fails on a clean tree forever — a permanently red check is
# one people learn to ignore, which is the cry-wolf shape this project says to narrow rather than
# tolerate. It reports its number; the number moving is the signal.
# ⚠ EXIT 3 IS A THIRD STATE, AND ITS ABSENCE PUBLISHED A PASS NOBODY EARNED.
#
# `check_paths` skips Mathlib citations when `.lake/packages/` is missing, which is ALWAYS the
# case in CI — this workflow runs `checkout` + `setup-python` and no lake setup. The checker
# said so in its own output; this reporter reads the exit code and DISCARDS stdout, so the
# summary rendered `check_paths.py | GATE | pass | every repo-relative reference resolves`
# while 0 of 63 citations had been verified.
#
# Both gates found it independently. /rely planted two genuinely dangling citations in a
# tracked .lean file, ran this reporter in the CI environment, and got `**all checks pass**`,
# exit 0 — with the published summary BYTE-IDENTICAL to the run where all 63 were checked.
#
# The fix is a code, not a parsed string: deciding a verdict from log text is the fail-open
# this file already warns about three times. A skipped class now renders as `skipped`, which
# is neither a pass nor a failure and is visible to a reader of the summary.
SKIPPED_RC = 3
GATE, COUNT = "GATE", "count"
CHECKS = [
    ("check_prose.py",      ["--block"], GATE,  "prose caps: block size, docstring vs declaration, gloss labels"),
    ("check_pov.py",        ["--block"], GATE,  "POV claims declare a KIND; a DENIAL is never allowed"),
    ("check_modal.py",      ["--block"], GATE,  "modal claims carry a measurement or a reduction"),
    ("check_classes.py",    ["--block"], GATE,  "a requirements class records a degeneracy verdict"),
    ("check_encoding.py",   ["--block"], GATE,  "no BOM, no double-encoded text in any tracked file"),
    ("check_moved.py",      ["--block"], GATE,  "nothing points at a relocated path"),
    ("check_negatives.py",  ["--block"], GATE,  "a universal negative carries a date or a search record"),
    ("check_figures.py",    ["--block"], GATE,  "an artifact count carries a date, or is measured on demand"),
    ("check_checkers.py",   ["--block"], GATE,  "every audited gate has passing controls in both directions, and is invoked (scope: check_*.py plus guards.py)"),
    # No --block flag: these exit non-zero on a finding natively.
    ("check_invariants.py", [],          GATE,  "always-true invariants hold across the corpus"),
    ("check_paths.py",      [],          GATE,  "every repo-relative reference resolves"),
    ("check_hashes.py",     [],          GATE,  "build-script bytes match the register.md fingerprints"),
    ("check_poles.py",      [],          COUNT, "pole-equality sites (no baseline; watch the number)"),
]

# The controls. A checker suite whose own controls are not run is a suite nobody has verified.
# ⚠ ALL TEN, as of 2026-08-15. The last four (`check_paths`, `check_invariants`, `check_hashes`,
# `check_release_ready`) had no `--selftest` at all until then — the Phase 1 exit says "each with
# both control types" and four checkers had never met it, including the one guarding the claim
# register.md makes to a reader about which scripts built which PDFs.
#
# ⚠ `guards.py` ADDED 2026-08-16, and it was the largest remaining hole in this list. It runs 22
# routes across 6 properties on every invocation and they all passed — but **nothing checked that it
# would still NOTICE a regression**: it shipped no controls, and `--selftest` was parsed away and
# silently ignored, so the flag produced an ordinary run. The controls it now carries found a live
# false green on their first execution (a route invoking a flag its checker does not have, inert for
# its whole life, scoring `ok` because the attack never happened). A registry of routes that cannot
# detect a dead route is the fail-open shape it exists to prevent, one level up.
SELFTESTS = ["check_prose.py", "check_pov.py", "check_modal.py",
             "check_classes.py", "check_encoding.py", "check_poles.py", "check_moved.py",
             "check_paths.py", "check_invariants.py", "check_hashes.py", "check_negatives.py",
             "check_figures.py", "check_checkers.py", "check_frozen.py", "check_claude_md.py",
             "check_release_ready.py", "common.py", "guards.py", "debaseline.py",
             # ⚠ `VEND-1`: THE definition of the vendored exemption, imported by every gating
             # checker and audited by nothing until 2026-08-16.
             "vendored.py"]


def run(script, args):
    """Return (exit_code, output). The code is subprocess's integer, never read out of the text."""
    p = subprocess.run([sys.executable, os.path.join(HERE, script)] + args,
                       cwd=REPO, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    return p.returncode, (p.stdout or "") + (p.stderr or "")


# ⚠ `decl_baseline.txt` is NOT DEBT and must not be counted as it. It is a reference SNAPSHOT of
# the declaration names present when it was taken, used to compute "what is new" for the purity and
# SSOT checks — nothing in it is a suppressed violation. Measured 2026-08-15: counting its entries
# alongside the suppression baselines reported roughly three times the real debt — an OVERSTATEMENT,
# which is exactly as wrong as understating it and would have been published on every run. Caught by
# reading the first local report instead of accepting its total.
NOT_DEBT = ("decl_baseline.txt",)


def baselines():
    """(bucket, count) for every SUPPRESSED site, so the green is never read as 'clean'."""
    out = []
    for fn in sorted(os.listdir(HERE)):
        if not fn.endswith("_baseline.txt") or fn in NOT_DEBT:
            continue
        n = 0
        for line in io.open(os.path.join(HERE, fn), encoding="utf-8-sig").read().splitlines():
            s = line.strip()
            if s and not s.startswith("#"):
                n += 1
        out.append((fn.replace("_baseline.txt", ""), n))
    return out


def main(argv):
    block = "--block" in argv
    rows, failed = [], 0

    skipped = 0
    for script, args, mode, what in CHECKS:
        rc, _out = run(script, args)
        # A COUNT never contributes to the verdict; that is what makes it a count.
        # SKIPPED_RC is not a failure and is emphatically not a pass.
        if rc == SKIPPED_RC:
            skipped += 1
        elif rc != 0 and mode == GATE:
            failed += 1
        rows.append((script, rc, mode, what))

    ctl_rows, ctl_failed = [], 0
    for script in SELFTESTS:
        rc, _out = run(script, ["--selftest"])
        if rc != 0:
            ctl_failed += 1
        ctl_rows.append((script, rc))

    w = []
    w.append("## Deterministic verification\n")
    w.append("Every verdict is a process exit code, never inferred from log text.\n")
    w.append("| checker | mode | result | enforces |")
    w.append("|---|---|---|---|")
    for script, rc, mode, what in rows:
        if mode == COUNT:
            result = "reported"
        elif rc == SKIPPED_RC:
            result = "**skipped**"
        else:
            result = "pass" if rc == 0 else "**FAIL (%d)**" % rc
        w.append("| `%s` | %s | %s | %s |" % (script, mode, result, what))

    w.append("\n### Detector controls\n")
    w.append("A must-fire and a must-suppress control per checker. A suite whose own controls "
             "are not run is a suite nobody has verified.\n")
    w.append("| checker | controls |")
    w.append("|---|---|")
    for script, rc in ctl_rows:
        w.append("| `%s` | %s |" % (script, "pass" if rc == 0 else "**FAIL (%d)**" % rc))

    bl = baselines()
    total = sum(n for _b, n in bl)
    w.append("\n### Grandfathered sites\n")
    w.append("These checkers block on **new** sites only. The counts below are known, recorded "
             "debt — a passing run above means *no new violations*, **not** a clean corpus.\n")
    w.append("| baseline | sites |")
    w.append("|---|---|")
    for b, n in bl:
        w.append("| `%s` | %d |" % (b, n))
    w.append("| **total** | **%d** |" % total)

    if failed or ctl_failed:
        verdict = "%d checker(s) and %d control(s) failing" % (failed, ctl_failed)
    elif skipped:
        verdict = ("all checks that COULD run pass — %d skipped part of its scope in this "
                   "environment (see the table; a skip is not a pass)" % skipped)
    else:
        verdict = "all checks pass"
    w.append("\n**%s** — %d grandfathered site(s) outstanding.\n" % (verdict, total))
    if not block:
        w.append("_Report-only (Phase 3): this step does not block. "
                 "Phase 4 turns it into a required status check._")

    report = "\n".join(w)
    print(report)

    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with io.open(summary, "a", encoding="utf-8") as fh:
            fh.write(report + "\n")

    return 1 if (block and (failed or ctl_failed)) else 0


if __name__ == "__main__":
    common.utf8_stdout()   # one definition; two of the eight copies had dropped
                           # line_buffering=True, which reorders output against children
    sys.exit(main(sys.argv[1:]))
