#!/usr/bin/env python3
"""Honest status-coded map of "the web": faces of ⊥ and the transforms between them.

REGISTRY-DRIVEN. Nodes and edges are extracted from the SSOT export
(ssot.json at the repo root) via web_data.py — nothing is hand-drawn.
Every edge on the canvas is backed by >=1 tagged decl; the diagram cannot draw a
relation the register does not carry. Pure stdlib -> SVG.

Run:  python tools/render/make_web_diagram.py [export.json]
Out:  tools/render/the_web_honest_map.svg  (gitignored artifact — re-run to regenerate)
"""
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import web_data

HERE = os.path.dirname(os.path.abspath(__file__))
TM = HERE
W, H = 1180, 1040
CX, CY = 590, 470
R = 300

ROLE_STYLE = {                        # role -> (colour, width, dash, label?)
    "bridge": ("#2f5fd0", 2.4, "",                    True),   # directional transform
    "core":   ("#1a9988", 1.7, "",                    False),  # cross-domain identity (Rosetta)
    "no-go":  ("#d98a16", 1.7, 'stroke-dasharray="6 5"', False),  # obstruction
}

def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

def main():
    export = sys.argv[1] if len(sys.argv) > 1 else None
    data = web_data.load(export)
    nodes = data["nodes"]
    N = len(nodes)
    idx = {n["domain"]: i for i, n in enumerate(nodes)}
    pos = []
    for i in range(N):
        a = 2 * math.pi * i / N - math.pi / 2
        pos.append((CX + R * math.cos(a), CY + R * math.sin(a)))

    S = []
    S.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
             f'viewBox="0 0 {W} {H}" font-family="Segoe UI, Helvetica, Arial, sans-serif">')
    S.append(f'<rect width="{W}" height="{H}" fill="#fbfbfd"/>')
    S.append(f'<text x="{W/2}" y="42" text-anchor="middle" font-size="26" font-weight="700" '
             f'fill="#1b1b2b">The Web — faces of ⊥ and the transforms between them</text>')
    ne = len(data["edges"])
    S.append(f'<text x="{W/2}" y="68" text-anchor="middle" font-size="13" fill="#6b6b80">'
             f'generated from the SSOT registry · {data["n_decls"]} decls · {N} domain nodes · '
             f'{ne} edges · hubs (highest degree): {esc(", ".join(data["hubs"]))} · '
             f'every edge is a tagged decl — the diagram cannot draw an unsanctioned relation</text>')

    # commitment ring (dotted): the literal one-object identity (MC-1) — NOT registry-derivable
    S.append(f'<ellipse cx="{CX}" cy="{CY}" rx="{R+108}" ry="{R+92}" fill="none" '
             f'stroke="#9a9ab0" stroke-width="2" stroke-dasharray="2 7"/>')
    S.append(f'<text x="{CX}" y="{CY-R-98}" text-anchor="middle" font-size="12.5" fill="#7a7a92" '
             f'font-style="italic">MC-1: "these are one object" — retired as ill-typed '
             f'(not type-statable; members provably distinct; not an edge)</text>')

    # spokes: each bottom-face domain = its domain's floor (the correspondence half)
    for n, (x, y) in zip(nodes, pos):
        if n["has_bottom_face"]:
            S.append(f'<line x1="{CX}" y1="{CY}" x2="{x:.1f}" y2="{y:.1f}" stroke="#cdcdda" '
                     f'stroke-width="1.3"/>')

    # inter-domain edges (registry-sanctioned), colour-coded by role
    for e in data["edges"]:
        if e["a"] not in idx or e["b"] not in idx:
            continue
        x1, y1 = pos[idx[e["a"]]]; x2, y2 = pos[idx[e["b"]]]
        col, wd, dash, lbl = ROLE_STYLE[e["role"]]
        w = wd + min(1.4, 0.28 * (e["count"] - 1))       # thicker = more backing decls
        S.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                 f'stroke="{col}" stroke-width="{w:.1f}" {dash} opacity="0.9"/>')
        if lbl and e["decls"]:
            mx, my = (x1 + x2) / 2, (y1 + y2) / 2
            tag = e["decls"][0] + (f" +{e['count']-1}" if e["count"] > 1 else "")
            S.append(f'<rect x="{mx-3:.1f}" y="{my-10:.1f}" width="{len(tag)*5.4+6:.0f}" height="14" '
                     f'rx="3" fill="#fbfbfd" opacity="0.82"/>')
            S.append(f'<text x="{mx:.1f}" y="{my:.1f}" font-size="9" fill="{col}">{esc(tag)}</text>')

    # center node : the base / diagonal fixed point
    S.append(f'<circle cx="{CX}" cy="{CY}" r="60" fill="#1b1b2b"/>')
    S.append(f'<text x="{CX}" y="{CY-4}" text-anchor="middle" font-size="30" font-weight="700" '
             f'fill="#ffffff">⊥</text>')
    S.append(f'<text x="{CX}" y="{CY+16}" text-anchor="middle" font-size="10" fill="#c9c9e6">'
             f'the diagonal fixed point</text>')

    # face nodes
    bw, bh = 170, 50
    for n, (x, y) in zip(nodes, pos):
        hub = n["domain"] in data["hubs"]
        fill = "#eef3ff" if hub else ("#ffffff" if n["has_bottom_face"] else "#f4f4f8")
        sw = 2.0 if hub else 1.4
        S.append(f'<rect x="{x-bw/2:.1f}" y="{y-bh/2:.1f}" width="{bw}" height="{bh}" rx="9" '
                 f'fill="{fill}" stroke="#2f5fd0" stroke-width="{sw}"/>')
        top = n["label"] + ("  ◆" if hub else "")
        S.append(f'<text x="{x:.1f}" y="{y-6:.1f}" text-anchor="middle" font-size="12.5" '
                 f'font-weight="700" fill="#1b1b2b">{esc(top)}</text>')
        sub = n["sub"] + (f"  ({n['faces']})" if n["faces"] else "")
        S.append(f'<text x="{x:.1f}" y="{y+11:.1f}" text-anchor="middle" font-size="9.5" '
                 f'fill="#55556b">{esc(sub)}</text>')

    # legend
    ly = H - 138
    items = [
        ("#2f5fd0", "",                      "bridge — a proved directional transform between two domains (role=bridge; label = decl)"),
        ("#1a9988", "",                      "core — a cross-domain identity / Rosetta restatement of the keystone (role=core)"),
        ("#d98a16", 'stroke-dasharray="6 5"',"no-go — an obstruction spanning two domains (role=no-go)"),
        ("#cdcdda", "",                      "spoke — each domain's bottom is that domain's floor (a bottom face of ⊥)"),
        ("#9a9ab0", 'stroke-dasharray="2 6"',"shape ring — the shared diagonal shape (MC-1); the one-object identity is retired as ill-typed, not an edge"),
    ]
    S.append(f'<rect x="40" y="{ly-22}" width="{W-80}" height="132" rx="10" fill="#ffffff" '
             f'stroke="#e3e3ee" stroke-width="1"/>')
    S.append(f'<text x="58" y="{ly-2}" font-size="12.5" font-weight="700" fill="#1b1b2b">Legend '
             f'— edge width scales with the number of backing decls · ◆ = hub</text>')
    for k, (col, da, txt) in enumerate(items):
        row_y = ly + 16 + k * 18
        S.append(f'<line x1="58" y1="{row_y-4}" x2="104" y2="{row_y-4}" stroke="{col}" '
                 f'stroke-width="2.4" {da}/>')
        S.append(f'<text x="114" y="{row_y}" font-size="11.5" fill="#33333f">{esc(txt)}</text>')

    S.append(f'<text x="{W/2}" y="{H-6}" text-anchor="middle" font-size="10" fill="#9a9ab0">'
             f'The web is the unification you can have without the type-incoherent object-identity. '
             f'Generated from the register — no hand-drawn edges.</text>')
    S.append('</svg>')

    os.makedirs(TM, exist_ok=True)
    out = os.path.join(TM, "the_web_honest_map.svg")
    open(out, "w", encoding="utf-8").write("\n".join(S))
    print(f"wrote {out}  ({N} nodes, {ne} edges, hubs={data['hubs']})")

if __name__ == "__main__":
    main()
