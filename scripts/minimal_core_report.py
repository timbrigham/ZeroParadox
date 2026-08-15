#!/usr/bin/env python3
"""Dual-audience verification report for the Minimal Core.

Reads the Lean elaboration output of ZeroParadox/Miniature.lean (its `#print axioms`
block plus any diagnostics) together with Lean's own exit code, and emits a Markdown
report readable by both a layman and a mathematician. Exits 0 only if the file
verified AND the log actually recorded evidence, 1 otherwise - so it doubles as a
CI gate.

TWO THINGS THIS GOT WRONG, BOTH MEASURED, BOTH WORTH NOT REPEATING.

1. Success was decided by searching the log for "error:". That fails OPEN: Lean tags
   some diagnostics `error(lean.unknownIdentifier):`, which contains no `error:`; a
   killed process writes none at all; an empty log trivially contains none. Hence the
   required exit-code argument.

2. But the exit code is NOT sufficient either, and the asymmetry is the important
   part: `lake env lean` on a file containing `sorry` **exits 0**. The exit status
   says nothing whatever about `sorry`, so for that one property the text scan is the
   only detector there is. Exit code for "did it elaborate", text for "is anything
   unproved", and BOTH are required.

3. An empty log satisfies both and proves nothing, so absence of evidence fails
   closed rather than printing a credential over a blank section.

Usage: minimal_core_report.py <lean-elaboration-log> <lean-exit-code>
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
        "the exit code is REQUIRED - deciding success from log text alone fails open\n")
    sys.exit(2)

log = open(sys.argv[1], encoding="utf-8", errors="replace").read()
try:
    lean_rc = int(sys.argv[2])
except ValueError:
    sys.stderr.write(f"lean-exit-code must be an integer, got {sys.argv[2]!r}\n")
    sys.exit(2)


def short(name: str) -> str:
    return re.sub(r"ZeroParadox\.Miniature\.(Pole\.)?", "", name)


# Scan for evidence BEFORE deciding the verdict - the verdict depends on it.
# ⚠ `.+` NOT `[^']+`. A Lean name may end in a prime, which `[^']+` cannot span, so
# primed declarations were dropped from the listing. Greedy and line-bounded, anchored
# by the trailing literal.
axfree = [short(m) for m in re.findall(r"'(.+)' does not depend on any axioms", log)]
axdep = [(short(n), ax) for n, ax in re.findall(r"'(.+)' depends on axioms: (\[[^]]*\])", log)]
no_evidence = not axfree and not axdep

# The backticked warning is measured against the pin - do not retype it from memory.
# `sorryAx` is what the kernel records and survives log reformatting. A plain substring
# test for "sorry" is wrong in the other direction: it matches `nanoda-allow-sorry` and
# similar log furniture.
SORRY_WARNING = "declaration uses `sorry`"
has_sorry = (SORRY_WARNING in log) or ("sorryAx" in log)
ok = (lean_rc == 0) and not has_sorry and not no_evidence

print(f"[report] rc={lean_rc} sorry={has_sorry} evidence={not no_evidence} -> ok={ok}",
      file=sys.stderr)

out = []
out.append("## The Minimal Core — checked by machine, not by me ✓" if ok
           else "## The Minimal Core — VERIFICATION FAILED ✗")
out.append("")
if ok:
    out.append(
        "Don't take my word for any of this. Lean — a proof assistant that will not accept "
        "a step it cannot justify — re-checked every theorem in this file, and it passed "
        "with nothing left unproved. You can run the same check yourself.")
    out.append("")
    # Kept inside the ok branch: printing a list of what was checked under a FAILED
    # headline asserts the opposite of the verdict above it.
    out.append(
        # NOT "the self-referential bottom": this file proves bare fixed-point existence
        # and says so of itself twice. The self-referential witness lives in
        # Settheory/SetTheoryAFA.lean, which this workflow does not elaborate.
        "**What was checked:** the engine (self-reference, when it closes, forces a fixed "
        "point) · the wall (where it can't close) · the floor (where it closes: a fixed "
        "point) · the snap (the one-way jump to a limit that is also the least fixed "
        "point) · the fan-out (the branching field).")
elif no_evidence and lean_rc == 0 and not has_sorry:
    out.append(
        "**Nothing was verified here.** Lean reported no failure, and it also reported no "
        "axiom footprints at all — so this run produced no evidence, and an absence of "
        "evidence is not a check. The raw output is in the run log.")
else:
    reason = ("a step was left unproved" if has_sorry
              else f"elaboration failed (exit status {lean_rc})")
    out.append(f"**Plain version:** The proof assistant did NOT accept this file — "
               f"{reason}. The raw output is in the run log.")
out.append("")

out.append("**Axiom footprint (for the specialist):**")
if axfree:
    out.append("- depend on **no axioms**: " + ", ".join(f"`{n}`" for n in axfree))
for n, ax in axdep:
    out.append(f"- `{n}` — `{ax}`")
if no_evidence:
    out.append("- *(none recorded — see above)*")
out.append("")
out.append(
    "**Scope.** This checks the statements in `Miniature.lean` — the shared shape on "
    "minimal examples — not the framework's domain layers, which build separately. "
    "Machine-checking establishes that each proof follows from its stated hypotheses; "
    "it does not establish that a theorem is interesting, correctly named, or says what "
    "its docstring says. Where this file marks something a modelling commitment rather "
    "than a theorem, that marking is the honest one.")

sys.stdout.write("\n".join(out) + "\n")
print(f"[report] wrote {len(out)} lines, exiting {0 if ok else 1}", file=sys.stderr)
sys.exit(0 if ok else 1)
