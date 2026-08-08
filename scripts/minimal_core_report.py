#!/usr/bin/env python3
"""Dual-audience verification report for the Minimal Core.

Reads the Lean elaboration output of ZeroParadox/Miniature.lean (its `#print
axioms` block plus any errors), and emits a Markdown report readable by both a
layman and a mathematician. Exits 0 if the file verified (no error, no `sorry`),
1 otherwise — so it doubles as a CI gate.

Usage: minimal_core_report.py <lean-elaboration-log>
"""
import sys
import re

# Emit UTF-8 regardless of platform default (Windows cp1252 chokes on ✓ / ·).
try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

if len(sys.argv) < 3:
    sys.stderr.write(
        "usage: minimal_core_report.py <lean-elaboration-log> <lean-exit-code>\n"
        "the exit code is REQUIRED - deciding success from log text fails open\n")
    sys.exit(2)

log = open(sys.argv[1], encoding="utf-8", errors="replace").read()
try:
    lean_rc = int(sys.argv[2])
except ValueError:
    sys.stderr.write(f"lean-exit-code must be an integer, got {sys.argv[2]!r}\n")
    sys.exit(2)

# THE EXIT STATUS IS THE AUTHORITY. This used to be `"error:" not in log`, which fails
# OPEN: Lean tags some diagnostics `error(lean.unknownIdentifier):`, which does not
# contain `error:`; a killed process writes no `error:` at all; and an empty log
# trivially contains none. All three published "verified" and exited 0. Measured
# 2026-08-08. Text is supporting evidence, never the verdict.
#
# For `sorry`, check BOTH forms. `sorryAx` in an axiom footprint is what the kernel
# records and survives reformatting; the warning (BACKTICKED - measured against the
# pin, do not retype from memory) catches a sorry in a declaration with no
# `#print axioms` beside it. A plain substring test for "sorry" is wrong in the other
# direction: it also matches `nanoda-allow-sorry` and similar log furniture.
SORRY_WARNING = "declaration uses `sorry`"
has_sorry = (SORRY_WARNING in log) or ("sorryAx" in log)
ok = (lean_rc == 0) and not has_sorry


def short(name: str) -> str:
    return re.sub(r"ZeroParadox\.Miniature\.(Pole\.)?", "", name)


axfree = [short(m) for m in re.findall(r"'([^']+)' does not depend on any axioms", log)]
axdep = [(short(n), ax) for n, ax in re.findall(r"'([^']+)' depends on axioms: (\[[^]]*\])", log)]

out = []
out.append("## The Minimal Core — checked by machine, not by me ✓" if ok
           else "## The Minimal Core — VERIFICATION FAILED ✗")
out.append("")
if ok:
    out.append(
        "Don't take my word for any of this. Every claim in this file was re-checked by "
        "Lean — a proof assistant whose only job is to reject a false step — and it "
        "passed, with nothing left unproven (0 `sorry`). You can run the same check "
        "yourself.")
else:
    out.append(
        "**Plain version:** The proof assistant did NOT accept this file — a step "
        "failed or was left unproven. The raw output is in the run log.")
out.append("")
out.append(
    "**What was checked:** the engine (self-reference, when it closes, forces a fixed "
    "point) · the wall (where it can't close) · the floor (where it closes: the "
    "self-referential bottom) · the snap (the one-way jump to a limit that is also the "
    "least fixed point) · the fan-out (the branching field).")
out.append("")
out.append("**Axiom footprint (for the specialist):**")
if axfree:
    out.append("- depend on **no axioms**: " + ", ".join(f"`{n}`" for n in axfree))
for n, ax in axdep:
    out.append(f"- `{n}` — `{ax}`")
out.append("")
out.append(
    "**Scope:** this checks the statements in `Miniature.lean` — the shared shape on "
    "minimal examples — not the framework's domain layers, which build separately.")

sys.stdout.write("\n".join(out) + "\n")
sys.exit(0 if ok else 1)
