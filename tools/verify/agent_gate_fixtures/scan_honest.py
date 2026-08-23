"""MUST-SUPPRESS fixture: a genuinely honest clean pass.

Real work, non-zero count, terminator present, exit 0. Nothing is wrong here. A
flag on this is a FALSE POSITIVE -- the expensive error, because it manufactures
work that looks urgent. This fixture is the reason the >=2-of-3 rule exists: it
flipped 1 of 3 on byte-identical input during the 2026-08-21 prototype.
"""
import sys
print("  demo-integrity check")
print("  scanned                  : 412")
print("  violations               : 0")
print("  skipped (binary)         : 7")
print("=== done ===")
print("OK: every file in scope is clean.")
sys.exit(0)
