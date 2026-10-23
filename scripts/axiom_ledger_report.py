#!/usr/bin/env python3
"""Run-summary report for the Axiom Ledger gate.

Reads the Lean elaboration output of ZeroParadox/Meta/AxiomLedger.lean together with Lean's own
exit code, and emits a Markdown report: one table row per ledger row, from the tab-separated
`LEDGER` lines the ledger prints, plus the audit's failure messages if any. Exits 0 only if the
ledger verified AND the log carries the evidence, 1 otherwise, so it doubles as a CI gate.

THE VERDICT IS LEAN'S EXIT CODE. The vendored audit throws on any failed row, which is an
elaboration error and a non-zero exit. The log can only make the verdict STRICTER, never rescue
it, for the reasons `minimal_core_report.py` measured:

1. Deciding success from log text fails OPEN: a killed process or an empty log prints no error.
2. `lake env lean` exits 0 on a file containing `sorry`, so the `sorry` warning is scanned too.
   (The audit also rejects any row reaching `sorryAx`; this is the second, independent detector.)
3. An exit 0 with no `LEDGER` rows, or without the audit's green line, proved nothing and fails
   closed. So does a row printed FAIL under an exit 0: the table and the audit disagree, and a
   disagreement is never read as a pass.

Usage: axiom_ledger_report.py <lean-elaboration-log> <lean-exit-code>
"""
import re
import sys

# Emit UTF-8 regardless of platform default (Windows cp1252 chokes on the subset sign).
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

if len(sys.argv) < 3:
    sys.stderr.write(
        "usage: axiom_ledger_report.py <lean-elaboration-log> <lean-exit-code>\n"
        "the exit code is REQUIRED - deciding success from log text alone fails open\n")
    sys.exit(2)

# utf-8-sig: a log written by PowerShell carries a BOM; one written by `tee` does not.
log = open(sys.argv[1], encoding="utf-8-sig", errors="replace").read()
try:
    lean_rc = int(sys.argv[2])
except ValueError:
    sys.stderr.write(f"lean-exit-code must be an integer, got {sys.argv[2]!r}\n")
    sys.exit(2)

COLS = ["kind", "source", "predecessor", "declared", "computed", "predecessor_computed", "verdict"]

# A `LEDGER` line may carry a message prefix (`lake build` prints `info: <file>:<l>:<c>: ` before
# the first line of an `#eval`'s output), so match the marker anywhere and split from it.
rows = []
for raw in log.splitlines():
    i = raw.find("LEDGER\t")
    if i < 0:
        continue
    cols = raw[i:].split("\t")[1:]
    if cols == COLS or len(cols) != len(COLS):
        continue
    rows.append(dict(zip(COLS, cols)))

green_line = re.search(r"^audit green: .*$", log, re.M)
failed = [r for r in rows if r["verdict"] != "PASS"]

# The audit's own failure text: from `audit FAILED:` to the next diagnostic header, the next
# `#print axioms` line (`lake env lean` prints info messages with no header), or EOF.
fail_block = []
m = re.search(r"audit FAILED:\n", log)
if m:
    for ln in log[m.end():].splitlines():
        if (re.match(r"^\S+\.lean:\d+:\d+: ", ln) or ln.startswith(("info:", "warning:", "error:"))
                or re.match(r"^'.+' (depends on axioms|does not depend on any axioms)", ln)):
            break
        fail_block.append(ln)
other_errors = [ln for ln in log.splitlines() if re.search(r"\berror\b", ln)][:20]

SORRY_WARNING = "declaration uses `sorry`"
has_sorry = SORRY_WARNING in log
no_evidence = not rows or green_line is None
ok = (lean_rc == 0) and not has_sorry and not no_evidence and not failed

print(f"[report] rc={lean_rc} rows={len(rows)} failed_rows={len(failed)} sorry={has_sorry} "
      f"green_line={green_line is not None} -> ok={ok}", file=sys.stderr)

out = []
out.append("## Axiom Ledger: every declared profile matches the kernel ✓" if ok
           else "## Axiom Ledger: VERIFICATION FAILED ✗")
out.append("")
if ok:
    out.append(
        "Lean recomputed the axioms each ledgered declaration reaches and compared them with what "
        "the ledger declares. Every row matched, every replacement has its predecessor's exact "
        "statement and a strictly smaller axiom set, and every theorem in scope has a row.")
elif lean_rc == 0 and no_evidence and not has_sorry:
    out.append(
        "**Nothing was verified here.** Lean reported no failure, and the log carries no ledger "
        "rows or no audit result, so this run produced no evidence. The raw output is in the run log.")
else:
    if has_sorry:
        reason = "a declaration uses `sorry`"
    elif lean_rc != 0:
        reason = f"elaboration failed (exit status {lean_rc})"
    else:
        reason = "a ledger row printed FAIL although Lean exited 0"
    out.append(f"**The ledger did NOT verify:** {reason}. The raw output is in the run log.")
out.append("")

if rows:
    out.append("| kind | declaration | predecessor | declared | computed | predecessor computed | verdict |")
    out.append("|---|---|---|---|---|---|---|")
    for r in rows:
        out.append("| " + " | ".join(
            r[c] if c in ("kind", "verdict") or r[c] == "-" else f"`{r[c]}`" for c in COLS) + " |")
    out.append("")
else:
    out.append("*(no ledger rows in the log)*")
    out.append("")

if fail_block:
    out.append("**Audit failures (verbatim):**")
    out.append("```")
    out.extend(fail_block[:50])
    out.append("```")
    out.append("")
elif lean_rc != 0 and other_errors:
    out.append("**Lean errors (first 20 lines naming one):**")
    out.append("```")
    out.extend(other_errors)
    out.append("```")
    out.append("")

out.append(
    "**Scope.** A replacement row checks two supplied proofs of one statement: that they share "
    "the type, and that ours reaches strictly fewer axioms. It does not show our profile is the "
    "least possible, nor that the predecessor's statement needs `Classical.choice`. Checker: "
    "the auditor of `GuardianEngineAI/corpus` (Apache-2.0), vendored in "
    "`ZeroParadox/Vendored/CorpusAudit/`.")

sys.stdout.write("\n".join(out) + "\n")
print(f"[report] wrote {len(out)} lines, exiting {0 if ok else 1}", file=sys.stderr)
sys.exit(0 if ok else 1)
