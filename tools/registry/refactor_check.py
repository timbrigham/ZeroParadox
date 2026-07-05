#!/usr/bin/env python3
"""Differential content-preservation checker for a codebase refactor.

Compares a BEFORE golden master (frozen baseline) against the CURRENT state and reports
whether a refactor cut preserved content. Three layers:

  1. INVENTORY   — decls removed / added (keyed by qualified name).
  2. STATEMENTS  — decls whose TYPE fingerprint (Expr.hash) changed = their statement altered.
  3. PURITY      — decls whose AXIOM profile changed = a purity regression.
  4. DEPENDENCY  — deps edges added / removed = the structural change the move made.

A PURE MOVE/RENAME is content-preserving iff: 0 type changes, 0 axiom changes on retained
decls, and every inventory removal is explained by an intended rename (its type-hash reappears
under the new name) or an intended drop. A pure file-move (qualified unchanged) shows ALL zero.

Inputs (golden master = output of `lake build ZeroParadox.Meta.Snapshot`):
  baseline:  .claude-local/translation_matrix/golden_master_baseline.json  + deps_baseline.json
  current:   .claude-local/translation_matrix/golden_master.json           + deps.json

Run:  python tools/registry/refactor_check.py
Exit: 0 = content preserved (or only intended renames), 1 = unexplained statement/purity change.
"""
import json, os, sys
from collections import Counter

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
TM = os.path.join(REPO, ".claude-local", "translation_matrix")
if hasattr(sys.stdout, "reconfigure"): sys.stdout.reconfigure(encoding="utf-8")

def load_gm(p):
    return {r["q"]: r for r in json.load(open(p, encoding="utf-8"))}
def load_deps(p):
    return {(e["from"], e["to"], e.get("kind")) for e in json.load(open(p, encoding="utf-8"))}

base = load_gm(os.path.join(TM, "golden_master_baseline.json"))
curr = load_gm(os.path.join(TM, "golden_master.json"))
bkeys, ckeys = set(base), set(curr)

removed = sorted(bkeys - ckeys)
added   = sorted(ckeys - bkeys)
retained = bkeys & ckeys
type_changed = sorted(q for q in retained if base[q]["th"] != curr[q]["th"])
axiom_changed = sorted(q for q in retained if base[q].get("ax") != curr[q].get("ax"))

# rename inference: a removed decl whose type-hash reappears among added decls
byhash_added = {}
for q in added: byhash_added.setdefault(curr[q]["th"], []).append(q)
renames = []          # (old, new) — same type-hash, name changed
unexplained_removed = []
for q in removed:
    cand = byhash_added.get(base[q]["th"], [])
    if len(cand) == 1:
        renames.append((q, cand[0]))
    else:
        unexplained_removed.append(q)
renamed_new = {n for _, n in renames}
genuinely_added = [q for q in added if q not in renamed_new]

dbase = load_deps(os.path.join(TM, "deps_baseline.json"))
dcurr = load_deps(os.path.join(TM, "deps.json"))
dep_removed = sorted(dbase - dcurr)
dep_added   = sorted(dcurr - dbase)

def sn(q): return q.replace("ZeroParadox.", "")
print("=== refactor content-preservation check ===")
print(f"decls: baseline {len(base)} -> current {len(curr)}   retained {len(retained)}")
print(f"\n[1] INVENTORY")
print(f"  inferred renames (same type-hash, new name): {len(renames)}")
for o, n in renames[:20]: print(f"      {sn(o)}  ->  {sn(n)}")
print(f"  unexplained REMOVED (dropped, no type-hash match): {len(unexplained_removed)}")
for q in unexplained_removed[:20]: print(f"      - {sn(q)}")
print(f"  genuinely ADDED (new decls): {len(genuinely_added)}")
for q in genuinely_added[:20]: print(f"      + {sn(q)}")
print(f"\n[2] STATEMENTS — type-hash changed on a RETAINED decl (statement altered): {len(type_changed)}")
for q in type_changed[:30]: print(f"      ! {sn(q)}")
print(f"\n[3] PURITY — axiom profile changed on a RETAINED decl: {len(axiom_changed)}")
for q in axiom_changed[:30]:
    print(f"      ! {sn(q)}   {base[q].get('ax')} -> {curr[q].get('ax')}")
print(f"\n[4] DEPENDENCY — edges removed {len(dep_removed)}, added {len(dep_added)}")
for f,t,k in dep_removed[:12]: print(f"      - {sn(f)} -> {sn(t)} [{k}]")
for f,t,k in dep_added[:12]:   print(f"      + {sn(f)} -> {sn(t)} [{k}]")

# verdict
fatal = len(type_changed) + len(axiom_changed) + len(unexplained_removed)
print(f"\n=== VERDICT ===")
if fatal == 0:
    print("CONTENT PRESERVED. No statement changed, no purity regression, no unexplained drop.")
    if renames: print(f"  ({len(renames)} intended rename(s), dep-graph delta shown above.)")
    sys.exit(0)
else:
    print(f"CONTENT NOT PRESERVED: {len(type_changed)} statement change(s), "
          f"{len(axiom_changed)} purity change(s), {len(unexplained_removed)} unexplained drop(s). REVIEW.")
    sys.exit(1)
