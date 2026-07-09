#!/usr/bin/env python3
"""Regenerate the import headers of the refactor-harness metaprograms.

`ZeroParadox/Meta/ExtractDeps.lean` and `Snapshot.lean` each `import` every tracked
ZeroParadox module so their env-walk sees the whole framework. A refactor cut that ADDS,
MOVES, or DELETES a file changes the module set, so these headers must be regenerated before
re-running the harness (else the new/moved file is invisible to the snapshot/deps extraction).

Run after any file add/move/delete, before `lake build ZeroParadox.Meta.Snapshot`:
    python tools/registry/regen_meta_imports.py

Preserves each file's body verbatim; only rewrites the leading `import ZeroParadox.*` block.
"""
import glob, os, sys
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
os.chdir(REPO)
mods = sorted({p.replace(os.sep, "/")[:-5].replace("/", ".")
               for p in glob.glob("ZeroParadox/**/*.lean", recursive=True)
               if not p.replace(os.sep, "/").startswith("ZeroParadox/Meta")})
imports = "\n".join(f"import {m}" for m in mods) + "\n"
for fn in ["ZeroParadox/Meta/ExtractDeps.lean", "ZeroParadox/Meta/Snapshot.lean"]:
    if not os.path.exists(fn):
        print(f"skip (missing): {fn}"); continue
    lines = open(fn, encoding="utf-8").read().split("\n")
    i = 0
    while i < len(lines) and (lines[i].startswith("import ZeroParadox") or lines[i].strip() == ""):
        i += 1
    open(fn, "w", encoding="utf-8", newline="\n").write(imports + "\n".join(lines[i:]))
    print(f"regenerated {fn}  ({len(mods)} ZP imports)")
