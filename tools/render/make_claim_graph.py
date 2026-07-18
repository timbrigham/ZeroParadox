#!/usr/bin/env python3
"""The CLAIM GRAPH — ⊥-face domain nodes and the adjudicated transforms between them.

REGISTRY-DRIVEN, gate-honest. Reads the curated `claims` collection from the SSOT
envelope export (ssot.json at the repo root) via web_data.load_claims().
Every node and edge is a claim in the store; every `proved`/`deep` claim is drawn
ONLY because a sorry-free declaration witnesses it (the store's cross-collection
invariant refuses to record a witnessless proved/deep claim). So the map's status
colours cannot outrun the Lean evidence — the anti-inflation property, one layer up
from the decl-derived web (make_web_diagram.py).

Distinct from make_web_diagram.py: that one DERIVES a web from every bottom-face decl
(descriptive); this one draws the CURATED, adjudicated claim graph (9 domain nodes +
the hand-adjudicated edges + the free-standing keystones), status-coded.

Run:  python tools/render/make_claim_graph.py [export.json]
Out:  tools/render/the_claim_graph.svg  (gitignored artifact — re-run to regenerate)
"""
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import web_data

HERE = os.path.dirname(os.path.abspath(__file__))
TM = HERE
W, H = 1200, 1120
CX, CY = 600, 470
R = 300

# status -> (colour, width, dash, glyph) — the claims-collection status vocabulary
STATUS_STYLE = {
    "proved":     ("#1a9988", 2.6, "",                     "proved"),
    "deep":       ("#0e6b7d", 3.4, "",                     "deep"),
    "corr":       ("#6b7280", 1.9, 'stroke-dasharray="7 5"',   "corr"),
    "conj":       ("#d98a16", 1.9, 'stroke-dasharray="2 5"',   "conj"),
    "commitment": ("#9a9ab0", 1.6, 'stroke-dasharray="2 7"',   "commitment"),
}

# curated ring order (clockwise from top) — clusters the p-adic sink `valuation`
# beside its in-edges (ordinal/computability/information) and category beside its
# correspondence targets. Any domain not listed is appended alphabetically.
RING_ORDER = ["set-theory", "computability", "ordinal", "information", "valuation",
              "state", "category", "order", "algebra"]

# short edge tag for the mid-line label (keeps the canvas readable)
def edge_tag(cid):
    return cid.split("-")[0] if cid[0] in "EBP" else ("MC-1" if cid.startswith("MC1") else
           "Lawvere" if cid.startswith("Lawvere") else cid)


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def main():
    export = sys.argv[1] if len(sys.argv) > 1 else None
    data = web_data.load_claims(export)
    if not data.get("n_claims"):
        sys.exit("no claims collection in export (legacy decl-only export?) — nothing to draw")

    nodes = data["nodes"]
    # domain of a node claim: node-<domain>  -> its single domain
    ndom = {n["id"]: (n["domain"][0] if n["domain"] else n["id"][5:]) for n in nodes}
    order = [d for d in RING_ORDER if d in ndom.values()]
    order += sorted(d for d in ndom.values() if d not in order)
    dom_pos = {}
    N = len(order)
    for i, d in enumerate(order):
        a = 2 * math.pi * i / N - math.pi / 2
        dom_pos[d] = (CX + R * math.cos(a), CY + R * math.sin(a))
    node_by_dom = {ndom[n["id"]]: n for n in nodes}

    S = []
    S.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
             f'viewBox="0 0 {W} {H}" font-family="Segoe UI, Helvetica, Arial, sans-serif">')
    S.append(f'<rect width="{W}" height="{H}" fill="#fbfbfd"/>')
    S.append(f'<text x="{W/2}" y="42" text-anchor="middle" font-size="26" font-weight="700" '
             f'fill="#1b1b2b">The claim graph — faces of ⊥ and the adjudicated transforms</text>')
    c = data["counts"]
    cstr = " · ".join(f'{k}={c[k]}' for k in ("proved", "deep", "corr", "conj", "commitment") if k in c)
    S.append(f'<text x="{W/2}" y="68" text-anchor="middle" font-size="13" fill="#6b6b80">'
             f'from the SSOT `claims` collection · {data["n_claims"]} claims ({esc(cstr)}) · '
             f'{N} domain nodes · {len(data["edges"])} edges · every proved/deep edge carries a live '
             f'sorry-free witness — the gate rejects any that do not</text>')

    # shape ring (dotted): MC-1 — the shared apophatic shape; the one-object identity is retired as ill-typed
    S.append(f'<ellipse cx="{CX}" cy="{CY}" rx="{R+96}" ry="{R+84}" fill="none" '
             f'stroke="#9a9ab0" stroke-width="2" stroke-dasharray="2 7"/>')
    S.append(f'<text x="{CX}" y="{CY-R-90}" text-anchor="middle" font-size="12.5" fill="#7a7a92" '
             f'font-style="italic">MC-1: the shared diagonal shape; "these bottoms are one object" is '
             f'retired as ill-typed — members provably distinct (not an edge)</text>')

    # spokes: each domain node is a face of ⊥ at the floor
    for d, (x, y) in dom_pos.items():
        S.append(f'<line x1="{CX}" y1="{CY}" x2="{x:.1f}" y2="{y:.1f}" stroke="#dcdce6" '
                 f'stroke-width="1.2"/>')

    # edges, status-coded
    for e in data["edges"]:
        da = ndom.get(e["from"]); db = ndom.get(e["to"])
        if da not in dom_pos or db not in dom_pos:
            continue
        x1, y1 = dom_pos[da]; x2, y2 = dom_pos[db]
        col, wd, dash, _ = STATUS_STYLE.get(e["status"], STATUS_STYLE["corr"])
        # arrowhead marker per colour
        mid = 0.62
        ax, ay = x1 + (x2 - x1) * mid, y1 + (y2 - y1) * mid
        S.append(f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
                 f'stroke="{col}" stroke-width="{wd:.1f}" {dash} opacity="0.9"/>')
        # direction tick (small filled arrow at ~62% toward `to`)
        ang = math.atan2(y2 - y1, x2 - x1)
        for sgn in (1,):
            hx, hy = ax, ay
            p1 = (hx - 9 * math.cos(ang - 0.4), hy - 9 * math.sin(ang - 0.4))
            p2 = (hx - 9 * math.cos(ang + 0.4), hy - 9 * math.sin(ang + 0.4))
            S.append(f'<path d="M {hx:.1f} {hy:.1f} L {p1[0]:.1f} {p1[1]:.1f} L {p2[0]:.1f} {p2[1]:.1f} Z" '
                     f'fill="{col}" opacity="0.9"/>')
        mx, my = (x1 + x2) / 2, (y1 + y2) / 2
        tag = f'{edge_tag(e["id"])}'
        tw = len(tag) * 6.0 + 10
        S.append(f'<rect x="{mx-tw/2:.1f}" y="{my-9:.1f}" width="{tw:.0f}" height="15" rx="3" '
                 f'fill="#fbfbfd" opacity="0.9" stroke="{col}" stroke-width="0.8"/>')
        S.append(f'<text x="{mx:.1f}" y="{my+2:.1f}" text-anchor="middle" font-size="9.5" '
                 f'fill="{col}" font-weight="600">{esc(tag)}</text>')

    # center: ⊥, the diagonal fixed point
    S.append(f'<circle cx="{CX}" cy="{CY}" r="58" fill="#1b1b2b"/>')
    S.append(f'<text x="{CX}" y="{CY-3}" text-anchor="middle" font-size="30" font-weight="700" '
             f'fill="#ffffff">⊥</text>')
    S.append(f'<text x="{CX}" y="{CY+16}" text-anchor="middle" font-size="9.5" fill="#c9c9e6">'
             f'the diagonal fixed point</text>')

    # domain nodes
    bw, bh = 176, 58
    for d, (x, y) in dom_pos.items():
        n = node_by_dom[d]
        label, sub = web_data.DOMAIN_GLOSS.get(d, (d.title(), ""))
        col, _, _, _ = STATUS_STYLE.get(n["status"], STATUS_STYLE["proved"])
        S.append(f'<rect x="{x-bw/2:.1f}" y="{y-bh/2:.1f}" width="{bw}" height="{bh}" rx="9" '
                 f'fill="#ffffff" stroke="{col}" stroke-width="2.0"/>')
        S.append(f'<text x="{x:.1f}" y="{y-12:.1f}" text-anchor="middle" font-size="12.5" '
                 f'font-weight="700" fill="#1b1b2b">{esc(label)}</text>')
        S.append(f'<text x="{x:.1f}" y="{y+2:.1f}" text-anchor="middle" font-size="9.3" '
                 f'fill="#55556b">{esc(sub)}</text>')
        wit = (n["witnesses"] or ["—"])[0]
        S.append(f'<text x="{x:.1f}" y="{y+16:.1f}" text-anchor="middle" font-size="8.6" '
                 f'fill="{col}" font-style="italic">{esc(wit)} · {n["live"]}w</text>')

    # keystones panel (free-standing claims: no from/to — cross-cutting, not domain-located)
    ky = H - 250
    kw = W - 80
    S.append(f'<rect x="40" y="{ky-22}" width="{kw}" height="104" rx="10" fill="#ffffff" '
             f'stroke="#e3e3ee" stroke-width="1"/>')
    S.append(f'<text x="58" y="{ky-4}" font-size="12.5" font-weight="700" fill="#1b1b2b">'
             f'Keystones — cross-cutting claims (not a single from→to edge)</text>')
    for i, k in enumerate(data["keystones"]):
        col, _, _, _ = STATUS_STYLE.get(k["status"], STATUS_STYLE["conj"])
        row = ky + 16 + (i % 5) * 15
        S.append(f'<circle cx="66" cy="{row-3.5:.0f}" r="4.5" fill="{col}"/>')
        wtag = f' · {k["live"]}w' if k["live"] else ""
        S.append(f'<text x="80" y="{row:.0f}" font-size="11" fill="#33333f">'
                 f'<tspan font-weight="600">{esc(k["id"])}</tspan> '
                 f'[<tspan fill="{col}">{esc(k["status"])}</tspan>{esc(wtag)}] — {esc(k["statement"][:88])}</text>')

    # legend
    ly = H - 132
    S.append(f'<rect x="40" y="{ly-20}" width="{kw}" height="120" rx="10" fill="#ffffff" '
             f'stroke="#e3e3ee" stroke-width="1"/>')
    S.append(f'<text x="58" y="{ly-2}" font-size="12.5" font-weight="700" fill="#1b1b2b">'
             f'Legend — status colours (Nw = live sorry-free witnesses)</text>')
    leg = [
        ("proved",     "a proved directional transform between two ⊥-faces (≥1 live witness, gate-enforced)"),
        ("deep",       "proved transport of a cold-audited theorem across the boundary (e.g. Perron-Frobenius)"),
        ("corr",       "correspondence / co-location at the shared floor — witness-backed, but not a transform"),
        ("conj",       "conjectural / intended — NOT built (e.g. Lawvere unification; no witness, cannot be proved-coded)"),
        ("commitment", "MC-1 one-object identity — retired as ill-typed (not a well-formed proposition); the shared shape survives, not an edge"),
    ]
    for k, (st, txt) in enumerate(leg):
        col, wd, dash, _ = STATUS_STYLE[st]
        row_y = ly + 16 + k * 18
        S.append(f'<line x1="58" y1="{row_y-4}" x2="104" y2="{row_y-4}" stroke="{col}" '
                 f'stroke-width="{max(2.4, wd):.1f}" {dash}/>')
        S.append(f'<text x="114" y="{row_y}" font-size="11.5" fill="#33333f">'
                 f'<tspan font-weight="700" fill="{col}">{st}</tspan> — {esc(txt)}</text>')

    S.append(f'<text x="{W/2}" y="{H-6}" text-anchor="middle" font-size="10" fill="#9a9ab0">'
             f'Generated from the sjv claims collection — a proved/deep edge cannot be drawn without a '
             f'live Lean witness. Old N2(number-theory)+N5(topology) are now one valuation node.</text>')
    S.append('</svg>')

    os.makedirs(TM, exist_ok=True)
    out = os.path.join(TM, "the_claim_graph.svg")
    open(out, "w", encoding="utf-8").write("\n".join(S))
    print(f"wrote {out}  ({N} nodes, {len(data['edges'])} edges, "
          f"{len(data['keystones'])} keystones, counts={data['counts']})")


if __name__ == "__main__":
    main()
