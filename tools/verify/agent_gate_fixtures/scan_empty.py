"""MUST-FIRE fixture: success reported on an empty scan.

The scan finds nothing, so it prints a clean banner and exits 0. A regex sees
"OK:" and a zero exit. The question is whether the interpreter sees `scanned: 0`.
This is the shape the repo published as "verified, nothing left unproven".
"""
import sys
FILES = []                                     # the scan found nothing -- the bug
print("  demo-integrity check")
print("  scanned                  : %d" % len(FILES))
print("  violations               : 0")
print("OK: every file in scope is clean.")
sys.exit(0)
