"""Run the deterministic checkers and publish what they found, as a markdown report.

VERIFICATION_BUILDOUT Phase 3. The goal in the buildout's first sentence is *"run those checks in
public CI so nobody takes our word for it"* — until now every checker ran only on one machine, and
**a bypassed local gate is invisible**. This is the step that turns a local claim into public
evidence.

REPORT-ONLY BY DEFAULT, AND THAT IS DELIBERATE. Phase 3 publishes; Phase 4 makes it block, via
branch protection on `main`. Flipping it is `--block` on the command line and nothing else — the
exit code is already computed honestly, it is simply not returned unless asked for.

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

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
SELF = os.path.relpath(os.path.abspath(__file__), REPO).replace("\\", "/")

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
    ("check_moved.py",      ["--block"], GATE,  "nothing points at a relocated path"),
    ("check_negatives.py",  ["--block"], GATE,  "a universal negative carries a date or a search record"),
    ("check_figures.py",    ["--block"], GATE,  "an artifact count carries a date, or is measured on demand"),
    ("check_checkers.py",   ["--block"], GATE,  "every checker has passing controls in both directions, and is invoked"),
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
SELFTESTS = ["check_prose.py", "check_pov.py", "check_modal.py",
             "check_classes.py", "check_poles.py", "check_moved.py",
             "check_paths.py", "check_invariants.py", "check_hashes.py", "check_negatives.py",
             "check_figures.py", "check_checkers.py",
             "check_release_ready.py"]


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
    try:
        sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)
    except Exception:
        pass
    sys.exit(main(sys.argv[1:]))
