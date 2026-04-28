"""
Build ZP-B Illustrated Companion (v1.2, revised)
Changes from original:
1. "Non-Archimedean" is now defined in plain language near the top.
2. "2-adic valuation" is briefly explained when the isolation of 0 is discussed.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Ellipse
from reportlab.graphics import renderPDF

def clopen_balls_diagram():
    """Two disjoint clopen balls, completely separated."""
    dw, dh = TW, 1.8 * inch
    d = Drawing(dw, dh)
    cy = dh * 0.5
    r  = 55

    # Left ball (Ball A)
    lx = dw * 0.27
    d.add(Ellipse(lx, cy, r, r * 0.85,
                  fillColor=colors.HexColor('#D6E8F4'), strokeColor=COMP_BLUE, strokeWidth=1.5))
    d.add(String(lx - 16, cy + 4, 'Ball A', fontSize=9, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(lx - 18, cy - 10, '(clopen)', fontSize=8, fontName='DV-I', fillColor=COMP_BLUE))

    # Right ball (Ball B)
    rx = dw * 0.73
    d.add(Ellipse(rx, cy, r, r * 0.85,
                  fillColor=colors.HexColor('#D6E8F4'), strokeColor=COMP_BLUE, strokeWidth=1.5))
    d.add(String(rx - 16, cy + 4, 'Ball B', fontSize=9, fontName='DV-B', fillColor=COMP_BLUE))
    d.add(String(rx - 18, cy - 10, '(clopen)', fontSize=8, fontName='DV-I', fillColor=COMP_BLUE))

    # Gap label
    mid = dw / 2
    d.add(String(mid - 22, cy + 6, '← gap →', fontSize=8, fontName='DV-B',
                 fillColor=colors.HexColor('#CC4444')))
    d.add(String(mid - 24, cy - 6, 'no overlap,', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))
    d.add(String(mid - 14, cy - 18, 'no path', fontSize=7.5, fontName='DV-I',
                 fillColor=colors.HexColor('#888888')))

    # Title above — avoid unicode subscript ₂ (missing from DejaVu); use plain 'Q2'
    d.add(String(dw/2 - 130, dh - 14,
                 'Balls in Q2 are completely separated — open AND closed',
                 fontSize=8.5, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def nested_balls_diagram():
    """Nested balls B(0,1) ⊃ B(0,1/2) ⊃ B(0,1/4) ⊃ B(0,1/8) converging on 0."""
    dw, dh = TW, 2.6 * inch
    d = Drawing(dw, dh)
    cx = dw / 2
    cy = dh * 0.48

    radii   = [110, 85, 62, 42]
    labels  = ['B(0, 1)', 'B(0, 1/2)', 'B(0, 1/4)', 'B(0, 1/8)']
    label_x = [cx + r + 4 for r in radii]
    label_y = [cy + r - 4  for r in radii]

    fill_cols = [
        colors.HexColor('#E8F5F5'),
        colors.HexColor('#C8EAEA'),
        colors.HexColor('#A8DDDD'),
        colors.HexColor('#88CCCC'),
    ]

    for i in range(len(radii) - 1, -1, -1):
        d.add(Ellipse(cx, cy, radii[i], radii[i] * 0.92,
                      fillColor=fill_cols[i], strokeColor=COMP_BLUE, strokeWidth=0.8))

    for i, (lx, ly, lbl) in enumerate(zip(label_x, label_y, labels)):
        d.add(String(lx - radii[i] * 2 - 10, ly, lbl, fontSize=7.5,
                     fontName='DV-I', fillColor=COMP_BLUE))

    # Amber dot at 0
    d.add(Circle(cx, cy, 6, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(cx + 9, cy - 4, '0', fontSize=9, fontName='DV-B', fillColor=COMP_AMBER))

    # ε₀ label (snap boundary, between B(0,1/4) and B(0,1/8))
    snap_r = (radii[2] + radii[3]) / 2
    d.add(Line(cx + snap_r, cy, cx + snap_r + 18, cy + 18,
               strokeColor=COMP_AMBER, strokeWidth=0.8))
    d.add(String(cx + snap_r + 20, cy + 14, 'ε', fontSize=8, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(cx + snap_r + 28, cy + 10, '0', fontSize=6, fontName='DV-B', fillColor=COMP_AMBER))
    d.add(String(cx + snap_r + 34, cy + 14, '(Snap boundary)', fontSize=7,
                 fontName='DV-I', fillColor=COMP_AMBER))

    d.add(String(cx - 85, dh - 14,
                 '0 is isolated — no continuous path reaches it from outside',
                 fontSize=8, fontName='DV-I', fillColor=colors.HexColor('#555555')))
    return d

def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-B_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-B Companion  |  p-Adic Topology  |  April 2026  |  v1.2')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM,
                            topMargin=TM, bottomMargin=BM,
                            title='ZP-B Illustrated Companion',
                            author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Header banner ──────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-B Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    E += [
        Paragraph('Why the geometry of state space is non-Archimedean', CS['title']),
        Paragraph('p-Adic Topology | Version 1.2', CS['subtitle']),
        Paragraph('ZP Companion | April 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and real-world '
            'examples. It is not the formal ontology — every claim here restates a result already '
            'proven in the corresponding technical document. Consult that document for the '
            'authoritative mathematics.',
            CS['disc']),
    ]

    # ── Page 1 ─────────────────────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-B Doing?', CS['h1']))
    E.append(cbody(
        'ZP-B puts the Zero Paradox on a specific geometric foundation: the 2-adic number field '
        'ℚ₂. This is not standard Euclidean geometry. In ℚ₂, distance works in a fundamentally '
        'different way — one that makes the singularity at zero structurally unavoidable.'))
    E.append(cbody(
        'The starting point is a single axiom: AX-B1 (Binary Existence) — a state either exists '
        'or it does not. From this, together with a minimality principle (MP-1), the document '
        'derives that the field must be ℚ₂. The choice of geometry is proven as Theorem T0, '
        'not assumed.'))
    E.append(example_box('Real-world example — Light switch vs. dimmer', [
        'AX-B1 says existence is like a light switch: on or off, no dimmer. This is the '
        'foundational claim. From "binary only," the 2-adic geometry follows mathematically.',
    ]))
    E.append(sp(8))

    # ── NEW: define non-Archimedean before using it ────────────────────────────
    E.append(Paragraph('What Does "Non-Archimedean" Mean?', CS['h1']))
    E.append(cbody(
        'The title uses the term <i>non-Archimedean</i>, which simply means: the usual rule about '
        'distance does not apply. In ordinary geometry (Archimedean), if you take enough small '
        'steps you can travel any large distance — pile up enough pennies and you reach any amount. '
        'A non-Archimedean geometry breaks this: adding more small steps does <i>not</i> necessarily '
        'get you further. Distance is measured by a completely different rule — one based on '
        'divisibility by 2, not on cumulative size.'))
    E.append(cbody(
        'The practical consequence: in ℚ₂, two points can be "far apart" even if their numerical '
        'difference looks small, and "close together" even if their numerical difference looks large. '
        'Closeness is about shared binary structure, not about proximity on the number line.'))
    E.append(sp(6))

    E.append(Paragraph('The Ultrametric: A Different Kind of Distance', CS['h1']))
    E.append(cbody(
        'In ordinary geometry the triangle inequality says: A-to-C ≤ A-to-B plus B-to-C. '
        'In ℚ₂ a stronger law holds: A-to-C ≤ maximum of the two. This is the <i>ultrametric</i>. '
        'Every ball is simultaneously open and closed (clopen). There are no gradual boundaries '
        '— regions are entirely inside or entirely outside.'))

    # ── Page 2 ─────────────────────────────────────────────────────────────────
    E.append(clopen_balls_diagram())
    E.append(ccaption(
        'Two disjoint balls in ℚ₂. They cannot overlap or gradually merge — completely separated. '
        'Every ball is both open and closed.'))

    E.append(example_box('Real-world example — File folders on a computer', [
        'A file is either in a folder or it isn\'t — there\'s no "halfway in." Two files in '
        'completely different folder trees are maximally separated regardless of how similar their '
        'names are. This is ultrametric thinking: location in a hierarchy determines distance, '
        'not surface similarity.',
    ]))
    E.append(sp(10))

    E.append(Paragraph('The Ball Hierarchy Around Zero', CS['h1']))
    E.append(cbody(
        'The element 0 ∈ ℚ₂ is surrounded by nested balls B(0,1), B(0,½), B(0,¼), … converging '
        'on 0. But 0 itself remains isolated. To understand why, we need the concept of a '
        '<b>2-adic valuation</b>.'))
    # NEW: define valuation before invoking it
    E.append(cbody(
        'The 2-adic valuation of a number counts how many times 2 divides it. For example: '
        '12 = 4 × 3 = 2² × 3, so its valuation is 2. The number 7 is not divisible by 2 at all, '
        'so its valuation is 0. In ℚ₂, distance between two numbers is determined by their '
        'valuation: the more times 2 divides their difference, the <i>closer</i> they are. '
        'This is the opposite of ordinary intuition — high divisibility means proximity.'))
    E.append(cbody(
        'The element 0 has a special status: it is divisible by 2 an <i>unlimited</i> number of '
        'times (0 = 2 × 0 = 4 × 0 = … always). Its valuation is therefore infinite. '
        'This means 0 is at infinite "depth" in the hierarchy — no finite sequence of steps from '
        'the outside ever reaches it.'))

    E.append(nested_balls_diagram())
    E.append(ccaption(
        'Balls in ℚ₂ converging on 0 (amber). The ε₀ threshold marks the Snap boundary. '
        '0 is isolated — no continuous path reaches it from outside.'))

    E.append(key_result_box('Key Result: Total Disconnectedness (T5)',
        'The only connected subsets of ℚ₂ are single points. There are no curves, no paths, no '
        'continuous structures bridging regions. This is proven from the clopen ball structure '
        '— a theorem, not an assumption.'))

    # ── Page 3 ─────────────────────────────────────────────────────────────────
    E.append(key_result_box('Key Result: The Snap is Topologically Irreversible (C3)',
        'There is no continuous path from any non-zero point back to 0. This follows directly '
        'from total disconnectedness (T5). Irreversibility is a corollary of the geometry, '
        'not a postulate.'))
    E.append(sp(8))

    E.append(example_box('Real-world example — Crossing a river with no bridge', [
        'Imagine a world where rivers have no bridges and no fords. Once you\'re on one bank, '
        'there is literally no continuous path to the other. That\'s total disconnectedness. '
        '0 is on one side; every non-zero state is on the other. The Snap is the only crossing, '
        'and it only goes one way.',
    ]))
    E.append(sp(8))

    E.append(remember_box(
        'Remember: The topological structure — ultrametric, clopen balls, isolation of 0 — is '
        'universal across all instantiations. The numerical value of ε₀ (the Snap threshold) is '
        'universe-contingent: it depends on physical constants. The Zero Paradox is a structural '
        'ontology, not a physical theory of our particular universe.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
