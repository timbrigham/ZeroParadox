"""
Build ZP-M Illustrated Companion
Version 1.14 | November 2026
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Polygon
from reportlab.graphics import renderPDF

VERSION = '1.14'
FIRST_RELEASED = 'May 2026'


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
    # Bottom edge label — y=16 clears the caption zone; internal caption removed
    # (ccaption() in build() already provides it externally)
    d.add(String(cx - 55, 16,
                 '2-adic convergence',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))

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
                 'From: second recursion theorem',
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
                 'From: iterating ω^· from 0 to a supremum',
                 fontSize=8, fontName='DV', fillColor=GREY_TEXT))

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
            'Zero Paradox ZP-M  |  Illustrated Companion  |  ' + version_date())
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
        Paragraph('ZP Companion | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
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
        'proved separately in ZP-K and ZP-L, through maps between their types rather than an '
        'identity across them.'))
    E.append(cbody(
        'ZP-K names a code beside the initial state c₀ (⊥ of MachinePhase) as a KleeneStructure '
        'requirement (botCode_is_quine), a periodicity condition that constant codes also meet. Reading '
        'c₀ as the Kleene quine, a program that is its own program, splits in two. It is not an equation, '
        'since a code and a machine state are different types, so that half is retired; that ⊥ of '
        'MachinePhase runs is the occurrence commitment, and if it runs, nothing outside it runs it (DA-1, '
        'Path 1). ZP-L proved that nothing fires below the ordinal ε₀: '
        'the tower ω, ω^ω, ω^ω^ω, … approaches ε₀ from below, and '
        'any monotone map that sends tower stages to c₀ also sends every ordinal below ε₀ '
        'to c₀ (snap_threshold_is_epsilon_zero). Firing at ε₀ itself is not forced (the map '
        'that is c₀ everywhere meets both conditions); it is the hypothesis hε₀, that the map '
        'sends ε₀ to c₁ (ZP-M §II), and given it, ε₀ is the least firing point. '
        'ZP-L also showed that the tower images in ℤ₂ converge to 0.'))
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
        'and multiplying 0 by anything gives 0. In the die (ZeroParadox/Die.lean), with join as the step on '
        'the machine states and multiplication as the step on ℤ₂, each is the only point that steps to itself '
        'and to nothing else, and snapEmbed is a map between those two motions (snapEmbedHom, '
        'ZeroParadox/Ordinal/Incompleteness.lean §I-b). Along it the role carries over at c₁, because 0 has '
        'only itself as a successor (snapEmbed_selfOnlyAt_c1), though the map&#8217;s back clause fails at c₀, so the general transport does not apply. That relates the two '
        'occupants by a map; it does not make them one object. Under a self-application map supplied by AbstractSelfApp, '
        'the occupant on the machine states is c₀, by that class&#8217;s fields: which point fills the role depends on the step.'))
    E.append(cbody(
        'The key geometric fact: 0 in ℤ₂ is divisible by every power of 2. '
        'That is what "infinite 2-adic valuation" means, and under doubling 0 is the only point '
        'that steps to itself and to nothing else (z2_double_selfOnlyAt_iff). The snap step itself does not '
        'carry over to doubling: c₀ → c₁ goes to 1 → 0, and 0 is not 2 · 1 '
        '(snapEmbed_doubling_noStepAt).'))

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
        'The bottom edge is the 2-adic convergence proved in ZP-L: the tower images '
        'in ℤ₂ converge to 0 as the ordinal stages approach ε₀.'))
    E.append(cbody(
        'All three edges are theorems, and zpm_triangle assembles them into a single '
        'formal statement. The ordinal, machine-state and 2-adic threads appear in the same proof; '
        'it has no computational conjunct, and the Kleene reading of c₀ is not part of it.'))

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
        'every join). The minimality theorem now holds under weaker hypotheses: '
        'monotonicity, every tower stage sent to c₀, and "snap at ε₀" together imply the full '
        'result (snap_unconditional), without hfp as a separate commitment.'))

    E.append(callout(
        'hfp is not an additional assumption — it is a consequence of monotonicity '
        'plus the alignment condition φ(ε₀) = c₁ (hfp_from_epsilon_zero). The gap in ZP-L is closed.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(6))

    # ── §5: The Diagonalization Pattern ───────────────────────────────────────
    print('[build_zpm_companion] Building §5...')
    E += [hr(), Paragraph('5. Two Fixed Points, Two Domains', CS['h1']), sp(4)]

    E.append(cbody(
        'ZP-M closes by putting two fixed points side by side: the one Kleene\'s '
        'second recursion theorem gives (computability) and ε₀ (ordinal theory). '
        'Reading them as one argument running in two mathematical worlds is the framework\'s '
        'interpretation; the theorem proves less, as below.'))

    E.append(diag_pattern_diagram())
    E.append(ccaption('Two fixed points in two domains, by two constructions, with no shared machinery.'))
    E.append(sp(8))

    E.append(cbody(
        'In computability theory, a diagonal argument over a program\'s own Gödel number (its '
        'address in the code space) gives a code fixed up to evaluation. In ordinal theory, '
        'iterating ω-exponentiation from 0 and taking the supremum gives ε₀, the first ordinal '
        'the tower cannot exceed: the fixed-point lemma for normal functions, not a diagonal '
        'argument. The mechanisms are entirely different.'))
    E.append(cbody(
        'The theorem both_fixed_points_exist records the ordinal fixed point and, on the computability '
        'side, a code periodic with period its own Gödel number (constant codes also meet that condition, so '
        'it does not by itself pin self-reference), and the proofs live in the same Lean context. It is a conjunction of two existence proofs over '
        'different types, a Code and an Ordinal, so it does not show they are one pattern; no '
        'equation between the two is even well-formed.'))

    E.append(sp(6))

    # ── §6: R-M.1 and the Boundary ────────────────────────────────────────────
    print('[build_zpm_companion] Building §6...')
    E += [hr(), Paragraph('6. Remark R-M.1: Where the Frame Ends', CS['h1']), sp(4)]

    E.append(cbody(
        'ZP-M sets two of the three threads in the DA-1 argument beside the ordinal result. '
        'Path 1 (AFA structural) and Path 3 (incompressibility, whose Lean counterpart is a Kleene field) had their Lean counterparts '
        'carried together in ZP-K as a conjunction (da1_paths_unified), and Path 3\'s counterpart '
        'is not a witness of execution; that they are one structural fact, and that they share a '
        'frame with the ordinal result, is the framework\'s reading.'))
    E.append(cbody(
        'Path 2 (informational) remains outside this frame. It has two charts. Depth chart, ZP-C L-INF: '
        'surprisal grows without bound with depth in the ball hierarchy, each value finite '
        '(l_inf). Point chart: at 0 of ℚ₂, the one point in every ball of the chain centred at 0, the 2-adic '
        'additive valuation is ⊤ (padic_addVal_bot), the point to which ZP-C has c₀, ⊥ of the machine-state type, '
        'correspond. (As of 2026-11-01 no single declared map from the machine-state type into the 2-adic integers '
        'or numbers sends c₀ to 0: a search of the corpus\'s Lean files for both type names finds snapEmbed and two '
        'negative examples. A composite of two maps the corpus has does send c₀ to 0 of ℚ₂: an order isomorphism '
        'onto a two-point type, read there as order shape only, then poleToSphere; that composite is not declared. '
        'snapEmbed, above, is a different map, sending '
        'c₀ to 1, and the two are not composed.) '
        'This is structurally analogous to the Kleene fixed point, but the analogy has not been '
        'made formal.'))
    E.append(cbody(
        'The reason, visible from ZP-M, is a framework separation: L-INF is a '
        'measure-theoretic result (about probability distributions and Shannon entropy), '
        'while Kleene\'s theorem is a computability-theoretic result (about codes and '
        'recursive functions). The two use no shared mathematical machinery, and ZP-C keeps '
        'surprisal and Kolmogorov complexity as two separate arguments (ZP-C Remark R-BRIDGE). Kolmogorov '
        'complexity is itself both an information-theoretic and a computability-theoretic notion; it was not '
        'located in the pinned Mathlib as of 2026-10-04, searched as recorded in '
        'ZeroParadox/Information/Disjunctive.md.'))

    E.append(callout(
        'DA-1 Path 2 is not a missing proof step — it is a genuine framework boundary. '
        'ZP-M makes the boundary precise: on one side, the fixed points over codes and '
        'ordinals (in Lean scope). On the other side, L-INF, which neither R-M.1 nor '
        'both_fixed_points_exist links to the Kleene quine, and the step from unbounded surprisal to executing: a bridge '
        'principle of its own, which the framework does not adopt (ZP-E, DA-1 Path 2).',
        bg=AMBER_LITE, border=AMBER
    ))
    E.append(sp(8))

    # ── Key Result Box ─────────────────────────────────────────────────────────
    print('[build_zpm_companion] Building key result box...')
    E.append(hr())
    E.append(result_box(
        'Key Results',
        [
            'snapEmbed: c₀ ↦ 1, c₁ ↦ 0 in ℤ₂ — injective, join-to-multiply morphism. ✓',
            'hfp_from_epsilon_zero: hfp derived from monotonicity + φ(ε₀) = c₁ alone. ✓',
            'zpm_triangle: all three edges co-proved — ordinal snap, 2-adic convergence, '
            'type bridge. ✓',
            'both_fixed_points_exist: Kleene and ordinal fixed points co-witnessed '
            'in one formal context. ✓',
            'R-M.1: DA-1 Path 2 boundary made precise — it does not link L-INF to the '
            'Kleene quine, and the step from unbounded surprisal to executing is an unadopted bridge '
            'principle, not a missing proof.',
            'Every theorem proved sorry-free. '
            'Axiom footprint: at most [propext, Classical.choice, Quot.sound], per declaration in ZP-M.',
        ]
    ))
    E.append(sp(8))

    E += [
        hr(),
        Paragraph(
            '<i>ZP-M Illustrated Companion | ' + version_date() + ' | '
            'Companion to ZP-M: Kleene-Ordinal Bridge | '
            'Formal verification: Incompleteness.lean (Lean 4 + Mathlib) | '
            'Zero Paradox Project</i>',
            CS['meta']),
    ]

    print('[build_zpm_companion] Building document...')
    doc.build(E)
    print(f'[build_zpm_companion] Done: {out_path}')


if __name__ == '__main__':
    build()
