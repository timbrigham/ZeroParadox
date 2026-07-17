#!/usr/bin/env python3
"""Tree/DAG view of the web — domains (top) descend through the two hubs into ⊥ (bottom).

REGISTRY-DRIVEN. Nodes, edges, and the two hubs are all extracted from the SSOT
export via web_data.py — the hubs are the two highest-degree domains in the
register, not an asserted claim. Every edge is backed by >=1 tagged decl. Shared
leaves feeding both hubs make it a DAG, tree-shaped. Pure stdlib -> SVG.

Run:  python tools/render/make_web_tree.py [export.json]
Out:  tools/render/the_web_tree.svg  (gitignored artifact — re-run to regenerate)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import web_data

HERE = os.path.dirname(os.path.abspath(__file__))
TM = HERE
W, H = 1240, 900

ROLE = {                              # role -> (colour, width, dash)
    "bridge": ("#2f5fd0", 2.4, ""),
    "core":   ("#1a9988", 1.8, ""),
    "no-go":  ("#d98a16", 1.8, 'stroke-dasharray="6 5"'),
}
PRIO = {"bridge": 0, "core": 1, "no-go": 2}   # which role labels a multi-role pair

def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

def main():
    data = web_data.load(sys.argv[1] if len(sys.argv) > 1 else None)
    hubs = data["hubs"]
    nodes = {n["domain"]: n for n in data["nodes"]}
    leaves = [n["domain"] for n in data["nodes"] if n["domain"] not in hubs]

    P = {}                                              # domain -> (x, y)
    P["__bot__"] = (W / 2, H - 78)
    hx = [W * 0.36, W * 0.64]
    for i, hdom in enumerate(hubs):
        P[hdom] = (hx[i], H - 270)
    n = len(leaves)
    for i, d in enumerate(leaves):
        x = 95 + (W - 190) * (i / max(1, n - 1))
        P[d] = (x, 205)

    S = []
    S.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" '
             f'font-family="Segoe UI, Helvetica, Arial, sans-serif">')
    S.append(f'<rect width="{W}" height="{H}" fill="#fbfbfd"/>')
    S.append(f'<text x="{W/2}" y="40" text-anchor="middle" font-size="25" font-weight="700" fill="#1b1b2b">'
             f'The Web as a tree — two hubs converging on the one floor ⊥</text>')
    S.append(f'<text x="{W/2}" y="65" text-anchor="middle" font-size="13" fill="#6b6b80">'
             f'generated from the SSOT registry · hubs (highest degree, data-derived): '
             f'{esc(hubs[0])} + {esc(hubs[1])} · {len(data["edges"])} edges, each a tagged decl · '
             f'shared leaves feed both hubs → a DAG</text>')

    # trunk: each hub is a face of ⊥
    bx, by = P["__bot__"]
    for hdom in hubs:
        hxp, hyp = P[hdom]
        S.append(f'<line x1="{hxp:.0f}" y1="{hyp:.0f}" x2="{bx:.0f}" y2="{by:.0f}" stroke="#7a7a92" '
                 f'stroke-width="4"/>')
    S.append(f'<text x="{(P[hubs[0]][0]+bx)/2-8:.0f}" y="{(P[hubs[0]][1]+by)/2:.0f}" font-size="9.5" '
             f'fill="#7a7a92" text-anchor="end">= a face of ⊥</text>')

    # collapse multi-role pairs -> one drawn edge (priority role), keep all-role tally for width
    pair = {}
    for e in data["edges"]:
        k = tuple(sorted((e["a"], e["b"])))
        pair.setdefault(k, {"roles": {}, "count": 0})
        pair[k]["roles"][e["role"]] = e
        pair[k]["count"] += e["count"]
    for (a, b), info in pair.items():
        if a not in P or b not in P:
            continue
        role = min(info["roles"], key=lambda r: PRIO[r])
        e = info["roles"][role]
        col, wd, dash = ROLE[role]
        x1, y1 = P[a]; x2, y2 = P[b]
        w = wd + min(1.4, 0.22 * (info["count"] - 1))
        leaf_leaf = a not in hubs and b not in hubs
        if leaf_leaf:                                   # bow leaf-leaf links above the top row
            mx, my = (x1 + x2) / 2, min(y1, y2) - 55
            S.append(f'<path d="M {x1:.0f} {y1:.0f} Q {mx:.0f} {my:.0f} {x2:.0f} {y2:.0f}" fill="none" '
                     f'stroke="{col}" stroke-width="{w:.1f}" {dash} opacity="0.85"/>')
            lx, ly = mx, my + 6
        else:
            S.append(f'<line x1="{x1:.0f}" y1="{y1:.0f}" x2="{x2:.0f}" y2="{y2:.0f}" stroke="{col}" '
                     f'stroke-width="{w:.1f}" {dash} opacity="0.9"/>')
            lx, ly = (x1 + x2) / 2, (y1 + y2) / 2
        if role == "bridge":
            tag = e["decls"][0] + (f" +{info['count']-1}" if info["count"] > 1 else "")
            S.append(f'<rect x="{lx-3:.0f}" y="{ly-10:.0f}" width="{len(tag)*5.4+6:.0f}" height="14" rx="3" '
                     f'fill="#fbfbfd" opacity="0.85"/>')
            S.append(f'<text x="{lx:.0f}" y="{ly:.0f}" font-size="9" fill="{col}">{esc(tag)}</text>')

    # ⊥ node
    S.append(f'<circle cx="{bx:.0f}" cy="{by:.0f}" r="46" fill="#1b1b2b"/>')
    S.append(f'<text x="{bx:.0f}" y="{by-2:.0f}" text-anchor="middle" font-size="26" font-weight="700" fill="#fff">⊥</text>')
    S.append(f'<text x="{bx:.0f}" y="{by+16:.0f}" text-anchor="middle" font-size="9" fill="#c9c9e6">the floor</text>')

    # domain nodes
    for d, (x, y) in P.items():
        if d == "__bot__":
            continue
        nd = nodes[d]; hub = d in hubs
        bw, bh = (196, 48) if hub else (150, 46)
        fill = "#eef3ff" if hub else ("#ffffff" if nd["has_bottom_face"] else "#f4f4f8")
        S.append(f'<rect x="{x-bw/2:.0f}" y="{y-bh/2:.0f}" width="{bw}" height="{bh}" rx="9" fill="{fill}" '
                 f'stroke="#2f5fd0" stroke-width="{2.0 if hub else 1.4}"/>')
        top = nd["label"] + ("  ◆ HUB" if hub else "")
        S.append(f'<text x="{x:.0f}" y="{y-5:.0f}" text-anchor="middle" font-size="12" font-weight="700" '
                 f'fill="#1b1b2b">{esc(top)}</text>')
        sub = nd["sub"] + (f"  ({nd['faces']})" if nd["faces"] else "")
        S.append(f'<text x="{x:.0f}" y="{y+11:.0f}" text-anchor="middle" font-size="9" fill="#55556b">{esc(sub)}</text>')

    # legend
    ly = H - 96
    S.append(f'<rect x="40" y="{ly-18}" width="{W-80}" height="100" rx="10" fill="#ffffff" stroke="#e3e3ee"/>')
    S.append(f'<text x="58" y="{ly}" font-size="12" font-weight="700" fill="#1b1b2b">Legend '
             f'— multi-role pairs shown in the strongest role; only bridges labelled · ◆ = hub</text>')
    leg = [("#2f5fd0", "", "bridge — proved directional transform"),
           ("#1a9988", "", "core — cross-domain identity (Rosetta)"),
           ("#d98a16", 'stroke-dasharray="6 5"', "no-go — cross-domain obstruction"),
           ("#7a7a92", "", "trunk — hub is a face of ⊥ (the floor)")]
    for i, (c, da, t) in enumerate(leg):
        ry = ly + 18 + i * 16
        S.append(f'<line x1="58" y1="{ry-4}" x2="100" y2="{ry-4}" stroke="{c}" stroke-width="2.6" {da}/>')
        S.append(f'<text x="110" y="{ry}" font-size="11" fill="#33333f">{esc(t)}</text>')
    S.append(f'<text x="{W-58}" y="{ly+64}" text-anchor="end" font-size="9.5" fill="#9a9ab0">'
             f'Two hubs feed one floor. The literal one-object identity is retired as ill-typed, not drawn.</text>')

    S.append('</svg>')
    os.makedirs(TM, exist_ok=True)
    out = os.path.join(TM, "the_web_tree.svg")
    open(out, "w", encoding="utf-8").write("\n".join(S))
    print(f"wrote {out}  (hubs={hubs}, leaves={len(leaves)}, edges={len(data['edges'])})")

if __name__ == "__main__":
    main()
