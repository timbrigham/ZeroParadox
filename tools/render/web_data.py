#!/usr/bin/env python3
"""Shared registry->web-graph extractor for make_web_diagram.py / make_web_tree.py.

Reads the SSOT export (tools/registry/registry_export.json) and returns the nodes
(domain faces of bottom) and edges (cross-domain transforms) that the registry
SANCTIONS — nothing hand-drawn. An edge exists in the diagram iff >=1 tagged decl
in the registry backs it. This is the anti-inflation property: the generated SVG
cannot draw a relation the register does not carry.

Node set   = every domain (except the `unscoped` sentinel) that appears on a
             bottom-face decl OR as an endpoint of a cross-domain edge.
Edge roles = bridge (directional transform), core (cross-domain identity /
             Rosetta), no-go (obstruction). Each keeps its backing decl names.
Hubs       = the two highest-degree domains (data-derived, not asserted).
"""
import json, os
from itertools import combinations
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_EXPORT = os.path.join(HERE, "..", "registry", "registry_export.json")

# Presentation-only gloss: HOW a domain's bottom reads. The STRUCTURE (which
# domains/edges appear) is registry-derived; this dict only prettifies labels.
DOMAIN_GLOSS = {
    "set-theory":    ("Set theory",       "Quine atom  ⊥={⊥}"),
    "computability": ("Computation",      "Kleene quine / selfApp fp"),
    "valuation":     ("Number theory",    "p-adic floor  v₂(0)=∞"),
    "information":   ("Information",       "Fin 0 / surprisal ↑"),
    "state":         ("Hilbert / linear", "zero module (StateSpace 0)"),
    "order":         ("Order / lattice",  "least element ⊥"),
    "category":      ("Category theory",  "initial object"),
    "algebra":       ("Algebra",          "wheel bottom 0·/0"),
    "ordinal":       ("Proof theory",     "ε₀-tower → floor"),
    "reals":         ("Reals",            "counterexample: snap fails"),
    "logic":         ("Logic",            "negation, no fixed point"),
}

EDGE_ROLES = ("bridge", "core", "no-go")


def _short(e):
    o = e.get("old") or {}
    return o.get("short") or (o.get("qualified") or "?").split(".")[-1]


def load(export_path=None):
    path = export_path or DEFAULT_EXPORT
    reg = json.load(open(path, encoding="utf-8"))
    ent = reg["entries"]

    face_reps = defaultdict(list)      # domain -> [decl names] realizing object=bottom
    edges = {}                         # (a,b,role) -> [decl names]
    for e in ent:
        o = e["ontology"]
        dom = [d for d in (o.get("domain") or []) if d != "unscoped"]
        roles = o.get("role") or []
        if "bottom" in (o.get("object") or []):
            for d in dom:
                face_reps[d].append(_short(e))
        if len(dom) >= 2:
            for r in EDGE_ROLES:
                if r in roles:
                    for a, b in combinations(sorted(set(dom)), 2):
                        edges.setdefault((a, b, r), []).append(_short(e))

    node_set = set(face_reps)
    for (a, b, _r) in edges:
        node_set.add(a); node_set.add(b)

    degree = defaultdict(int)
    for (a, b, _r), decls in edges.items():
        degree[a] += len(decls); degree[b] += len(decls)

    nodes = []
    for d in sorted(node_set, key=lambda x: (-degree[x], x)):
        label, sub = DOMAIN_GLOSS.get(d, (d.title(), ""))
        nodes.append({
            "domain": d, "label": label, "sub": sub,
            "faces": len(face_reps.get(d, [])),
            "has_bottom_face": d in face_reps,
            "degree": degree[d],
            "reps": face_reps.get(d, []),
        })

    edge_list = [{"a": a, "b": b, "role": r, "decls": decls, "count": len(decls)}
                 for (a, b, r), decls in edges.items()]
    edge_list.sort(key=lambda e: (e["role"], -e["count"]))

    hubs = [n["domain"] for n in sorted(nodes, key=lambda n: -n["degree"])[:2]]
    src_hash = (reg.get("anchor") or {}).get("commit", "")
    return {"nodes": nodes, "edges": edge_list, "hubs": hubs,
            "n_decls": len(ent), "source": path}


if __name__ == "__main__":
    d = load()
    print(f"nodes={len(d['nodes'])} edges={len(d['edges'])} hubs={d['hubs']}")
    for n in d["nodes"]:
        print(f"  {n['domain']:14} deg={n['degree']:3} faces={n['faces']:2} face={n['has_bottom_face']}")
    from collections import Counter
    print("edges by role:", dict(Counter(e["role"] for e in d["edges"])))
