#!/usr/bin/env python3
"""Build the declaration-level dependency edge set (interop Issue 13) for the sjv `deps` collection.

Pipeline:
  1. `ZeroParadox/Meta/ExtractDeps.lean`  (run via `lake build ZeroParadox.Meta.ExtractDeps`)
     walks the Lean environment and writes the RAW per-declaration reference dump
     `.claude-local/translation_matrix/deps_raw.json`
     (each record: {from, module, type_deps:[...], val_deps:[...]} — UNFILTERED, includes
      Mathlib / auto-generated / self references).
  2. THIS script intersects both endpoints of every edge with the registry's tracked
     qualified-name set (effective-current qualified per the Issue-5 reconcile match rule),
     drops self-loops, dedups, and assigns `kind` (`type` if the dependency appears in the
     dependent's TYPE, else `proof`). Result: `.claude-local/translation_matrix/deps.json`
     — a flat edge list `[{from, to, kind}]` where EVERY endpoint is a registered decl, so
     sjv's cross-collection reference integrity (Issue 13 / D3) cannot flag a dangling edge.

Direction: an edge {from, to} means "`from` directly uses `to`" (arrow -> the prerequisite).
  upstream(X)   = dependencies = { to : from==X }
  downstream(X) = dependents    = { from : to==X }

Run:  python tools/registry/deps_build.py
Out:  .claude-local/translation_matrix/deps.json  (+ a stats summary on stdout)
"""
import json, os, sys
from collections import Counter, defaultdict

if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
RAW = os.path.join(REPO, ".claude-local", "translation_matrix", "deps_raw.json")
EXPORT = os.path.join(HERE, "registry_export.json")
OUT = os.path.join(REPO, ".claude-local", "translation_matrix", "deps.json")


def registry_decls(export_path):
    reg = json.load(open(export_path, encoding="utf-8"))
    if "collections" in reg:
        return reg["collections"]["declarations"]["entries"]
    return reg["entries"]


def effective_qualified(e):
    """The Issue-5 reconcile match key: the name a live decl is currently known by.
    dropped/merged/split sources are GONE (return None so they can't be an edge endpoint)."""
    disp = e.get("disposition")
    old = (e.get("old") or {}).get("qualified")
    new = (e.get("new") or {}).get("qualified")
    if disp in ("dropped", "merged", "split"):
        return None
    if disp == "renamed":
        return new or old
    return old  # pending / present / moved / (default)


def main():
    if not os.path.exists(RAW):
        sys.exit(f"missing {RAW}\n  run first:  lake build ZeroParadox.Meta.ExtractDeps")
    raw = json.load(open(RAW, encoding="utf-8"))
    decls = registry_decls(EXPORT)
    tracked = {q for q in (effective_qualified(e) for e in decls) if q}
    print(f"registry tracked decls: {len(tracked)}   raw extracted decls: {len(raw)}")

    edges = []                       # [{from, to, kind}]
    seen = set()                     # (from, to) dedup — keep strongest kind (type wins)
    stat_from_untracked = 0          # raw 'from' not in registry (source drift ahead of anchor)
    ext_refs = 0                     # references dropped as non-registry (Mathlib / auto-gen)
    self_loops = 0
    type_edges = proof_edges = 0
    out_deg = Counter()
    in_deg = Counter()

    for rec in raw:
        f = rec.get("from")
        if f not in tracked:
            stat_from_untracked += 1
            continue
        tdeps = set(rec.get("type_deps") or [])
        vdeps = set(rec.get("val_deps") or [])
        allrefs = tdeps | vdeps
        for t in allrefs:
            if t == f:
                self_loops += 1
                continue
            if t not in tracked:
                ext_refs += 1
                continue
            key = (f, t)
            if key in seen:
                continue
            seen.add(key)
            kind = "type" if t in tdeps else "proof"
            edges.append({"from": f, "to": t, "kind": kind})
            out_deg[f] += 1
            in_deg[t] += 1
            if kind == "type":
                type_edges += 1
            else:
                proof_edges += 1

    edges.sort(key=lambda e: (e["from"], e["to"]))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    json.dump(edges, open(OUT, "w", encoding="utf-8"), ensure_ascii=False, indent=1)

    roots = sorted(t for t in tracked if out_deg[t] == 0)       # depend on nothing internal
    leaves = sorted(t for t in tracked if in_deg[t] == 0)       # nothing internal depends on them
    print(f"\nwrote {OUT}")
    print(f"  edges: {len(edges)}   (type={type_edges}, proof={proof_edges})")
    print(f"  self-loops dropped: {self_loops}   external/auto-gen refs dropped: {ext_refs}")
    print(f"  raw 'from' not in registry (source drift ahead of anchor): {stat_from_untracked}")
    print(f"  internal roots (0 internal deps): {len(roots)}   internal leaves (0 dependents): {len(leaves)}")
    print("\n  most depended-ON (highest in-degree — the load-bearing decls):")
    for name, d in in_deg.most_common(12):
        print(f"    {d:4}  {name}")
    print("\n  heaviest dependents (highest out-degree):")
    for name, d in out_deg.most_common(6):
        print(f"    {d:4}  {name}")


if __name__ == "__main__":
    main()
