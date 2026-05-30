"""
Build ZP-M Illustrated Companion
Version 1.2 | May 2026
v1.2: fix HTML entities in String() drawing primitives (rendered literally);
      add validate_drawing() to both diagram functions; increase triangle_diagram
      dh 3.2→3.5 in to clear top-circle geometry overflow.
v1.1: vocab fix: null state → ⊥.
v1.0: Initial release. Covers snapEmbed type bridge, triangle diagram,
      diagonalization unification, and R-M.1 on DA-1 Path 2 boundary.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
from reportlab.graphics import renderPDF

VERSION = '1.2'


def triangle_diagram():
    """The Kleene-Ordinal-2adic triangle."""
    dw = TW
    dh = 3.5 * inch  # 3.5 * 72 = 252 pts; top circle top = 222, dh-10 = 242 ✓

    d = Drawing(dw, dh)

    cx = dw / 2
    # Three vertices of the triangle
    top_x, top_y   = cx,         200   # ε₀ / c₁ (ordinal snap)
    left_x, left_y = cx - 160,    30   # c₀ = ⊥ (Kleene quine)
    right_x, right_y = cx + 160,  30   # 0 ∈ ℤ₂ (2-adic limit)

    # Triangle edges
    d.add(Line(left_x, left_y, top_x, top_y,
               strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(right_x, right_y, top_x, top_y,
               strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(left_x, left_y, right_x, right_y,
               strokeColor=INDIGO, strokeWidth=1.5))

    # Vertex circles
    r = 22
    for (vx, vy) in [(top_x, top_y), (left_x, left_y), (right_x, right_y)]:
        d.add(Circle(vx, vy, r, fillColor=INDIGO_LITE,
                     strokeColor=INDIGO, strokeWidth=1.5))

    # Vertex labels (inside circles) — Unicode directly; String() does not parse entities
    d.add(String(top_x - 14,   top_y - 6,   'ε₀ / c₁',
                 fontSize=10, fontName='DV-B', fillColor=INDIGO))
    d.add(String(left_x - 18,  left_y - 6,  'c₀ = ⊥',
                 fontSize=10, fontName='DV-B', fillColor=INDIGO))
    d.add(String(right_x - 18, right_y - 6, '0 ∈ ℤ₂',
                 fontSize=10, fontName='DV-B', fillColor=INDIGO))

    # Edge labels
    d.add(String(left_x - 80, (top_y + left_y) / 2,
                 'ordinal snap',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))
    d.add(String(right_x + 8, (top_y + right_y) / 2,
                 'snapEmbed',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))
    d.add(String(cx - 55, left_y - 18,
                 '2-adic convergence',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))

    d.add(String(14, 10,
                 'Three objects, three edges, one formal context — zpm_triangle co-proves all three.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))

    return validate_drawing(d, dh, 'triangle_diagram')


def diag_pattern_diagram():
    """Side-by-side: Kleene diagonal vs ordinal diagonal."""
    dw = TW
    dh = 2.0 * inch  # 144 pts; two boxes side by side

    d = Drawing(dw, dh)

    mid = dw / 2
    box_w = mid - 20
    box_h = 100
    box_y = (dh - box_h) / 2  # ~22 pts — stays above 5pt minimum

    # Left box: Kleene
    d.add(Rect(10, box_y, box_w, box_h,
               fillColor=SLATE_LITE, strokeColor=SLATE, strokeWidth=1))
    d.add(String(10 + box_w / 2 - 55, box_y + box_h - 22,
                 'Kleene (computability)',
                 fontSize=9, fontName='DV-B', fillColor=SLATE))
    d.add(String(10 + 8, box_y + box_h - 44,
                 'Operation: eval c = selfApply c',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))
    d.add(String(10 + 8, box_y + box_h - 60,
                 'Fixed point: ∃ c, IsComputationalQuine c',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))
    d.add(String(10 + 8, box_y + box_h - 76,
                 'Domain: codes + Gödel numbers',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))
    d.add(String(10 + 8, box_y + box_h - 92,
                 'Forced by: second recursion theorem',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))

    # Right box: ordinal
    d.add(Rect(mid + 10, box_y, box_w, box_h,
               fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1))
    d.add(String(mid + 10 + box_w / 2 - 50, box_y + box_h - 22,
                 'Ordinal (set theory)',
                 fontSize=9, fontName='DV-B', fillColor=INDIGO))
    d.add(String(mid + 18, box_y + box_h - 44,
                 'Operation: α ↦ ω^α',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))
    d.add(String(mid + 18, box_y + box_h - 60,
                 'Fixed point: ε₀ = ω^ε₀ (minimal)',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))
    d.add(String(mid + 18, box_y + box_h - 76,
                 'Domain: ordinals + ω-tower iteration',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))
    d.add(String(mid + 18, box_y + box_h - 92,
                 'Forced by: least fixed-point theorem',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))

    # Caption at bottom
    d.add(String(14, 10,
                 'Same schema, different domains — no shared machinery between the two.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))

    return validate_drawing(d, dh, 'diag_pattern_diagram')


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-M_Illustrated_Companion.pdf')
    print(f'[build_zpm_companion] Output: {out_path}')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            'Zero Paradox ZP-M  |  Illustrated Companion  |  May 2026')
        canvas.restoreState()

    doc = SimpleDocTemplate(
        out_path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-M Illustrated Companion', author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb)

    E = []

    print('[build_zpm_companion] Building header...')
    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),INDIGO),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-M Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
        Paragraph('THE ZERO PARADOX', CS['title']),
        Paragraph('ZP-M: Kleene&#8211;Ordinal Bridge', CS['title']),
        Paragraph('ZP Companion | Version ' + VERSION + ' | May 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language. It is not the formal '
            'document &#8212; every claim here restates a result already proved in '
            'ZP-M: Kleene-Ordinal Bridge. Consult that document for the authoritative '
            'mathematics.',
            CS['disc']),
        sp(4),
        hr(),
        sp(4),
    ]

    # ── §1: What ZP-M Does ─────────────────────────────────────────────────────
    print('[build_zpm_companion] Building §1...')
    E += [Paragraph('1. What This Layer Does', CS['h1']), sp(4)]

    E.append(cbody(
        'ZP-M is a consolidation layer. Its job is to connect two results that were '
        'proved separately in ZP-K and ZP-L and show that they are looking at the same '
        'structure from different angles.'))
    E.append(cbody(
        'ZP-K proved that the initial state c₀ (⊥) is a '
        'Kleene fixed point — a program that is its own program, with no external '
        'executor required. ZP-L proved that the ordinal ε₀ is the exact snap '
        'threshold: the tower ω, ω^ω, ω^ω^ω, … approaches ε₀ from below, and '
        'any monotone map that sends tower stages to c₀ must send ε₀ to c₁. '
        'ZP-L also showed that the tower encodings in ℤ₂ converge to 0.'))
    E.append(cbody(
        'ZP-M builds the bridge connecting these: a formal map snapEmbed that sends '
        'c₁ (the snap state) to 0 in ℤ₂, and proves that all three objects '
        '— the ordinal ε₀, the snap state c₁, and the 2-adic zero — are '
        'formally co-witnessed in a single theorem (zpm_triangle). It also closes '
        'a gap in ZP-L\'s minimality theorem by showing that its free hypothesis '
        'follows from simpler conditions.'))

    E.append(sp(6))

    # ── §2: The Type Bridge ────────────────────────────────────────────────────
    print('[build_zpm_companion] Building §2...')
    E += [hr(), Paragraph('2. The Type Bridge (snapEmbed)', CS['h1']), sp(4)]

    E.append(cbody(
        'The two layers — ZP-E\'s machine state space {c₀, c₁} and ZP-B\'s '
        '2-adic integers ℤ₂ — are mathematically unrelated types. One is a two-element '
        'set; the other is an infinite algebraic structure. snapEmbed is the map that '
        'connects them structurally.'))

    E.append(label_box('snapEmbed', [
        'c₀  (pre-snap)  ↦  1 ∈ ℤ₂   (a 2-adic unit, valuation 0)',
        'c₁  (snap state)  ↦  0 ∈ ℤ₂   (the 2-adic zero, infinite valuation)',
    ]))
    E.append(sp(6))

    E.append(cbody(
        'The map is injective (c₀ and c₁ land in distinct places) and '
        'preserves the algebraic structure: joining c₁ with anything gives c₁, '
        'and multiplying 0 by anything gives 0. The same absorbing-element pattern '
        'holds in both types, under different operations.'))
    E.append(cbody(
        'The key geometric fact: 0 in ℤ₂ is divisible by every power of 2. '
        'That is what "infinite 2-adic valuation" means. This is the same mathematical '
        'signature as ⊥ = {⊥} — a structure that contains itself at every level of '
        'depth, with no bottom that is not also the top.'))

    E.append(sp(6))

    # ── §3: The Triangle ───────────────────────────────────────────────────────
    print('[build_zpm_companion] Building §3...')
    E += [hr(), Paragraph('3. The Triangle', CS['h1']), sp(4)]

    E.append(cbody(
        'Three objects that appear in three different layers of the framework are '
        'co-witnessed in a single Lean theorem: zpm_triangle.'))

    E.append(triangle_diagram())
    E.append(ccaption('The Kleene–Ordinal–2-adic triangle: three edges, one formal proof.'))
    E.append(sp(8))

    E.append(cbody(
        'The left-side edge is the ordinal snap: below ε₀, the tower stages map '
        'to c₀; at ε₀, the canonical map flips to c₁. '
        'The right-side edge is the type bridge: snapEmbed sends c₁ to 0. '
        'The bottom edge is the 2-adic convergence proved in ZP-L: the tower encodings '
        'in ℤ₂ converge to 0 as the ordinal stages approach ε₀.'))
    E.append(cbody(
        'All three edges are theorems, and zpm_triangle assembles them into a single '
        'formal statement. This is the first place in the framework where the ordinal, '
        'computational, and 2-adic threads appear in the same proof.'))

    E.append(sp(6))

    # ── §4: Closing the Gap in ZP-L ───────────────────────────────────────────
    print('[build_zpm_companion] Building §4...')
    E += [hr(), Paragraph('4. Closing a Gap in ZP-L', CS['h1']), sp(4)]

    E.append(cbody(
        'ZP-L\'s central minimality theorem (snap_exactly_at_epsilon_zero) carried a '
        'free hypothesis called hfp. It asserted that for any map from ordinals to '
        'machine phases, every fixed point of ω-exponentiation must be sent to c₁. '
        'This was not proved from the ordinal structure — it was an extra assumption.'))
    E.append(cbody(
        'ZP-M §II closes this gap. The argument is short: if a map is monotone and '
        'sends ε₀ to c₁, then for any other fixed point α ≥ ε₀, '
        'monotonicity forces the map to agree with c₁ at α (because c₁ absorbs '
        'every join). The minimality theorem now holds under weaker hypotheses: just '
        'monotonicity and "snap at ε₀" together imply the full result, without hfp '
        'as a separate commitment.'))

    E.append(callout(
        'hfp is not an additional assumption — it is a consequence of the ordinal '
        'structure plus the alignment condition φ(ε₀) = c₁. The gap in ZP-L is closed.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(6))

    # ── §5: The Diagonalization Pattern ───────────────────────────────────────
    print('[build_zpm_companion] Building §5...')
    E += [hr(), Paragraph('5. One Pattern, Two Domains', CS['h1']), sp(4)]

    E.append(cbody(
        'The deepest result in ZP-M is not a new theorem but a recognition: Kleene\'s '
        'second recursion theorem (computability) and the construction of ε₀ '
        '(ordinal theory) are the same argument running in different mathematical worlds.'))

    E.append(diag_pattern_diagram())
    E.append(ccaption('The diagonalization schema in two domains: same structure, no shared machinery.'))
    E.append(sp(8))

    E.append(cbody(
        'In each case: you define an operation that refers to itself, and the framework '
        'forces a fixed point to exist. In computability theory, the operation refers to '
        'a program\'s own Gödel number (its address in the code space). In ordinal theory, '
        'the operation is ω-exponentiation, and the fixed point is the first ordinal that '
        'the tower cannot exceed. The mechanisms are entirely different. The schema is identical.'))
    E.append(cbody(
        'The theorem both_fixed_points_exist states this directly: both fixed points '
        'exist, and their proofs live in the same Lean context. This is not a coincidence '
        'that requires explanation — it is the recognition that diagonalization is a '
        'structural fact that transcends any particular domain.'))

    E.append(sp(6))

    # ── §6: R-M.1 and the Boundary ────────────────────────────────────────────
    print('[build_zpm_companion] Building §6...')
    E += [hr(), Paragraph('6. Remark R-M.1: Where the Frame Ends', CS['h1']), sp(4)]

    E.append(cbody(
        'ZP-M establishes the diagonalization frame for two of the three threads in '
        'the DA-1 argument. Path 1 (AFA structural) and Path 3 (Kleene computational) '
        'are both diagonalization instances — they were unified in ZP-K. Now both share '
        'the frame with the ordinal result.'))
    E.append(cbody(
        'Path 2 (informational) remains outside this frame. L-INF (ZP-C) says that '
        '⊥ has unbounded information content — no finite description can '
        'capture it. This is structurally analogous to the diagonalization pattern, '
        'but the analogy has not been made formal.'))
    E.append(cbody(
        'The reason, visible from ZP-M, is a framework separation: L-INF is a '
        'measure-theoretic result (about probability distributions and Shannon entropy), '
        'while Kleene\'s theorem is a computability-theoretic result (about codes and '
        'recursive functions). The two use no shared mathematical machinery. The concept '
        'that bridges them — Kolmogorov complexity, which is simultaneously an '
        'information-theoretic and computability-theoretic notion — is not yet formalized '
        'in Mathlib.'))

    E.append(callout(
        'DA-1 Path 2 is not a missing proof step — it is a genuine framework boundary. '
        'ZP-M makes the boundary precise: on one side, diagonalization over codes and '
        'ordinals (in Lean scope). On the other side, the AIT bridge between '
        'incompressibility and self-execution (outside current Lean scope).',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(8))

    # ── Key Result Box ─────────────────────────────────────────────────────────
    print('[build_zpm_companion] Building key result box...')
    E.append(hr())
    E.append(result_box(
        'Key Results — ZP-M v1.0',
        [
            'snapEmbed: c₀ ↦ 1, c₁ ↦ 0 in ℤ₂ — injective, join-to-multiply morphism. ✓',
            'hfp_from_epsilon_zero: hfp derived from monotonicity + φ(ε₀) = c₁ alone. ✓',
            'zpm_triangle: all three edges co-proved — ordinal snap, 2-adic convergence, '
            'type bridge. ✓',
            'both_fixed_points_exist: Kleene and ordinal fixed points co-witnessed '
            'in one formal context. ✓',
            'R-M.1: DA-1 Path 2 boundary made precise — AIT bridge is outside current '
            'Lean scope; gap is framework separation, not missing proof.',
            'All 9 theorems proved sorry-free. '
            'Axiom footprint: [propext, Classical.choice, Quot.sound].',
        ]
    ))
    E.append(sp(8))

    E += [
        hr(),
        Paragraph(
            '<i>ZP-M Illustrated Companion | May 2026 | '
            'Companion to ZP-M: Kleene-Ordinal Bridge | '
            'Formal verification: ZPM.lean (Lean 4 + Mathlib) | '
            'Zero Paradox Project</i>',
            CS['meta']),
    ]

    print('[build_zpm_companion] Building document...')
    doc.build(E)
    print(f'[build_zpm_companion] Done: {out_path}')


if __name__ == '__main__':
    build()
