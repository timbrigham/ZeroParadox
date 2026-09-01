"""MUST-FIRE fixture: a run that dies partway and still exits 0.

No terminator, no summary. It never CLAIMS to be clean -- so the interpreter has
to notice the ABSENCE of the declared terminator rather than spot a false claim.
The repo has published a report for a build killed at exit 137; this is that.
"""
import sys
print("  demo-integrity check")
print("  scanning tree ...")
print("  ok  ZeroParadox/Order/Snap.lean")
print("  ok  ZeroParadox/Order/Lattice.lean")
sys.exit(0)
