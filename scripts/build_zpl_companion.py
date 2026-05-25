"""
Build ZP-L Illustrated Companion
Version 1.0 | May 2026
v1.0: Initial release. Covers ε₀ as the ordinal snap threshold, 2-adic tower
convergence, and Kleene-ordinal structural homology. Notes that ZPM closes the
snapEmbed type bridge identified in ZPL's Remaining Gap section.
Formal doc: ZP-L Incomputability Convergence v1.0.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle
from reportlab.graphics import renderPDF


def snap_tower_diagram():
    """Horizontal: tower stages (c0) climbing toward ε₀; snap to c1 at ε₀."""
    # dh = 155 pts (≈ 2.15 × 72); box_cy = 88 fixed.
    # Box top = 88+17 = 105. SNAP label at 105+8 = 113. Header at 105+20 = 125.
    # Encoding labels at 71-18 = 53. Caption at 10.
    # Content: top = 125 < 145 (dh-10). Bottom = 10 > 5. ✓
    dw, dh = TW, 155
    d = Drawing(dw, dh)

    bw, bh = 60, 34
    spacing = 12
    box_cy = 88          # fixed — does not derive from dh
    box_by = box_cy - bh // 2   # = 71

    # Stage labels (raw Unicode — String() does not parse HTML entities)
    stage_labels = ['0', '1', 'ω', 'ω^ω']   # 0, 1, ω, ω^ω
    n = len(stage_labels)

    stages_w = n * bw + (n - 1) * spacing   # 4×60 + 3×12 = 276
    dots_w = 30
    gap_w = 22
    eps_bw = 62
    total_w = stages_w + dots_w + gap_w + eps_bw   # = 390
    x0 = (dw - total_w) / 2   # ≈ 39 pts

    # ── Stage boxes (teal) ───────────────────────────────────────────────────
    for i, lbl in enumerate(stage_labels):
        bx = x0 + i * (bw + spacing)
        d.add(Rect(bx, box_by, bw, bh,
                   fillColor=TEAL_LITE, strokeColor=TEAL, strokeWidth=1.2, rx=3, ry=3))
        lbl_x = bx + max(4, (bw - len(lbl) * 6) / 2)
        d.add(String(lbl_x, box_by + bh - 14, lbl,
                     fontSize=9.5, fontName='DV-B', fillColor=TEAL))
        d.add(String(bx + bw / 2 - 7, box_by + 7, 'c0',
                     fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))
        if i < n - 1:
            d.add(Line(bx + bw + 2, box_cy, bx + bw + spacing - 2, box_cy,
                       strokeColor=TEAL, strokeWidth=1.0))

    # ── Continuation dots ────────────────────────────────────────────────────
    dots_x = x0 + stages_w + 6
    for j in range(3):
        d.add(Circle(dots_x + j * 9, box_cy, 2.5,
                     fillColor=TEAL, strokeColor=TEAL, strokeWidth=0))

    # ── Arrow from dots to ε₀ box ────────────────────────────────────────────
    eps_bx = x0 + stages_w + dots_w + gap_w
    arr_x1 = dots_x + 3 * 9 + 6
    arr_x2 = eps_bx - 3
    d.add(Line(arr_x1, box_cy, arr_x2, box_cy, strokeColor=AMBER, strokeWidth=1.5))
    d.add(Line(arr_x2, box_cy, arr_x2 - 7, box_cy + 4, strokeColor=AMBER, strokeWidth=1.5))
    d.add(Line(arr_x2, box_cy, arr_x2 - 7, box_cy - 4, strokeColor=AMBER, strokeWidth=1.5))

    # ── ε₀ box (amber — snap point) ──────────────────────────────────────────
    d.add(Rect(eps_bx, box_by, eps_bw, bh,
               fillColor=AMBER_LITE, strokeColor=AMBER, strokeWidth=1.8, rx=3, ry=3))
    # ε as large glyph, 0 as subscript-positioned smaller glyph
    d.add(String(eps_bx + 12, box_by + bh - 13, 'ε',
                 fontSize=12, fontName='DV-B', fillColor=AMBER))
    d.add(String(eps_bx + 22, box_by + bh - 17, '0',
                 fontSize=8, fontName='DV-B', fillColor=AMBER))
    d.add(String(eps_bx + eps_bw / 2 - 7, box_by + 7, 'c1',
                 fontSize=8.5, fontName='DV-B', fillColor=AMBER))

    # ── "SNAP" label above the transition arrow ───────────────────────────────
    snap_label_x = arr_x1 + (arr_x2 - arr_x1) / 2 - 14
    d.add(String(snap_label_x, box_by + bh + 8, 'SNAP',
                 fontSize=7.5, fontName='DV-B', fillColor=AMBER))

    # ── Caption (raw Unicode — no HTML entities) ──────────────────────────────
    d.add(String(14, 10,
                 'Each tower stage is strictly below ε-zero and maps to c0. '
                 'The snap to c1 occurs exactly at ε-zero.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))

    return d


def dual_convergence_diagram():
    """Two rows: ordinal tower approaching ε₀ (top) and 2-adic norms converging to 0 (bottom)."""
    # dh = 190 pts. row_top = 148 fixed, row_bot = 68 fixed.
    # Top box top = 148+16 = 164. Top row label at 164+8 = 172 < 180 (dh-10). ✓
    # Bottom box bottom = 68-16 = 52. Caption at 10. ✓
    dw, dh = TW, 190
    d = Drawing(dw, dh)

    bw, bh = 58, 32
    spacing = 12
    row_top = 148     # ordinal row center (fixed)
    row_bot = 68      # 2-adic row center (fixed)

    # Four corresponding stage columns
    stage_ord  = ['1', 'ω', 'ω^ω', 'ω^ω^ω']
    stage_norm = ['1/2', '1/4', '1/8', '1/16']   # 2-adic norms ||2^n||_2
    n = len(stage_ord)

    stages_w = n * bw + (n - 1) * spacing   # 4×58 + 3×12 = 268
    dots_w = 28
    gap_w = 22
    end_bw = 62
    total_w = stages_w + dots_w + gap_w + end_bw   # = 380
    x0 = (dw - total_w) / 2   # ≈ 44 pts

    top_by = row_top - bh // 2   # = 132
    bot_by = row_bot - bh // 2   # = 52

    # ── Ordinal row (top, teal) ───────────────────────────────────────────────
    for i, lbl in enumerate(stage_ord):
        bx = x0 + i * (bw + spacing)
        d.add(Rect(bx, top_by, bw, bh,
                   fillColor=TEAL_LITE, strokeColor=TEAL, strokeWidth=1.2, rx=3, ry=3))
        lbl_x = bx + max(4, (bw - len(lbl) * 5.5) / 2)
        d.add(String(lbl_x, top_by + bh - 13, lbl,
                     fontSize=9, fontName='DV-B', fillColor=TEAL))
        if i < n - 1:
            d.add(Line(bx + bw + 2, row_top, bx + bw + spacing - 2, row_top,
                       strokeColor=TEAL, strokeWidth=1.0))

    # Ordinal dots
    dots_x = x0 + stages_w + 5
    for j in range(3):
        d.add(Circle(dots_x + j * 8, row_top, 2,
                     fillColor=TEAL, strokeColor=TEAL, strokeWidth=0))

    # Arrow to ε₀ box
    end_bx = x0 + stages_w + dots_w + gap_w
    arr1_x1 = dots_x + 3 * 8 + 4
    arr1_x2 = end_bx - 3
    d.add(Line(arr1_x1, row_top, arr1_x2, row_top, strokeColor=AMBER, strokeWidth=1.5))
    d.add(Line(arr1_x2, row_top, arr1_x2 - 7, row_top + 4, strokeColor=AMBER, strokeWidth=1.5))
    d.add(Line(arr1_x2, row_top, arr1_x2 - 7, row_top - 4, strokeColor=AMBER, strokeWidth=1.5))

    # ε₀ box (amber)
    d.add(Rect(end_bx, top_by, end_bw, bh,
               fillColor=AMBER_LITE, strokeColor=AMBER, strokeWidth=1.8, rx=3, ry=3))
    d.add(String(end_bx + 10, top_by + bh - 13, 'ε',
                 fontSize=12, fontName='DV-B', fillColor=AMBER))
    d.add(String(end_bx + 20, top_by + bh - 17, '0',
                 fontSize=8, fontName='DV-B', fillColor=AMBER))
    d.add(String(end_bx + 5, top_by + 5, '(snap: c1)',
                 fontSize=7.5, fontName='DV-I', fillColor=AMBER))

    # Row label (above top row)
    d.add(String(x0, top_by + bh + 8, 'Ordinal: each stage strictly below ε-zero',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))

    # ── 2-adic row (bottom, indigo) ───────────────────────────────────────────
    for i, lbl in enumerate(stage_norm):
        bx = x0 + i * (bw + spacing)
        d.add(Rect(bx, bot_by, bw, bh,
                   fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1.2, rx=3, ry=3))
        lbl_x = bx + max(4, (bw - len(lbl) * 5.5) / 2)
        d.add(String(lbl_x, bot_by + bh - 13, lbl,
                     fontSize=9, fontName='DV-B', fillColor=INDIGO))
        if i < n - 1:
            d.add(Line(bx + bw + 2, row_bot, bx + bw + spacing - 2, row_bot,
                       strokeColor=INDIGO, strokeWidth=1.0))

    # 2-adic dots
    for j in range(3):
        d.add(Circle(dots_x + j * 8, row_bot, 2,
                     fillColor=INDIGO, strokeColor=INDIGO, strokeWidth=0))

    # Arrow to 0 = ⊥ box
    arr2_x1 = dots_x + 3 * 8 + 4
    arr2_x2 = end_bx - 3
    d.add(Line(arr2_x1, row_bot, arr2_x2, row_bot, strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(arr2_x2, row_bot, arr2_x2 - 7, row_bot + 4, strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(arr2_x2, row_bot, arr2_x2 - 7, row_bot - 4, strokeColor=INDIGO, strokeWidth=1.5))

    # 0 = ⊥ box (indigo)
    d.add(Rect(end_bx, bot_by, end_bw, bh,
               fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1.8, rx=3, ry=3))
    d.add(String(end_bx + 5, bot_by + bh - 13, '0 = ⊥',
                 fontSize=9.5, fontName='DV-B', fillColor=INDIGO))
    d.add(String(end_bx + 5, bot_by + 5, '(limit)',
                 fontSize=7.5, fontName='DV-I', fillColor=INDIGO))

    # Row label (above bottom row, in the inter-row gap)
    d.add(String(x0, bot_by + bh + 8, '2-adic norm of encoding (converges to 0 = ⊥):',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))

    # ── Vertical dashed connectors between rows ───────────────────────────────
    for i in range(n):
        bx_mid = x0 + i * (bw + spacing) + bw / 2
        d.add(Line(bx_mid, top_by - 2, bx_mid, bot_by + bh + 2,
                   strokeColor=colors.HexColor('#BBBBBB'), strokeWidth=0.8,
                   strokeDashArray=[3, 3]))
    # End column connector
    bx_mid = end_bx + end_bw / 2
    d.add(Line(bx_mid, top_by - 2, bx_mid, bot_by + bh + 2,
               strokeColor=colors.HexColor('#BBBBBB'), strokeWidth=0.8,
               strokeDashArray=[3, 3]))

    # Caption
    d.add(String(14, 10,
                 'Same tower, two perspectives. Teal (top): ordinal stages approach ε-zero. '
                 'Indigo (bottom): their 2-adic norms approach 0.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))

    return d


VERSION = '1.0'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-L_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            'Zero Paradox ZP-L Companion  |  Incomputability Convergence  |  May 2026  |  v' + VERSION)
        canvas.restoreState()

    doc = SimpleDocTemplate(
        out_path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='ZP-L Illustrated Companion', author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Header banner ─────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0, 0), (-1, -1), COMP_BLUE),
        ('TOPPADDING',    (0, 0), (-1, -1), 8),
        ('BOTTOMPADDING', (0, 0), (-1, -1), 8),
        ('LEFTPADDING',   (0, 0), (-1, -1), 10),
    ])
    hdr = Table([[Paragraph('ZP-L Illustrated Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    # ── Title block ───────────────────────────────────────────────────────────
    E += [
        Paragraph('The Ordinal Summit', CS['title']),
        Paragraph('Where the Tower Snaps to c&#8321; | Version ' + VERSION, CS['subtitle']),
        Paragraph('ZP Companion  |  May 2026', CS['meta']),
        Paragraph(
            'This companion explains the ideas in plain language with diagrams and examples. '
            'It is not the formal document &#8212; every claim here restates a result already '
            'proved in ZP-L Incomputability Convergence v1.0. Consult that document for the '
            'authoritative mathematics.',
            CS['disc']),
    ]

    # ── What Is ZP-L Doing? ───────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-L Doing?', CS['h1']))
    E.append(cbody(
        'ZP-K proved that the initial machine state c&#8320; is its own program &#8212; '
        'a Kleene fixed point, a self-executing Quine, the same object at the bottom of '
        'every formal language in the framework. ZP-L picks up the thread from a different '
        'direction: the ordinal direction. If a map &#981; assigns machine phases to ordinals '
        '&#8212; sending c&#8320; to everything below a certain point and c&#8321; above it '
        '&#8212; what is that threshold ordinal? ZP-L establishes the answer: &#949;&#8320;, '
        'the first fixed point of the map &#945; &#8614; &#969;^&#945;.'))
    E.append(cbody(
        'This is not an arbitrary choice. ZP-L proves that &#949;&#8320; is the minimal '
        'threshold &#8212; no monotone, tower-aligned map can snap before &#949;&#8320;, and '
        'the canonical map snaps exactly there. ZP-L also establishes the connection to '
        'ZP-B: as the tower stages approach &#949;&#8320; in ordinal order, their '
        '2-adic encodings converge to 0 = &#8869; in &#8484;&#8322;. The same sequence '
        'witnesses both convergences simultaneously.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy &#8212; the unreachable horizon', [
        'Imagine a path where each step is longer than the last: you walk 1 mile, then '
        '2, then 4, then 8, ... You are always getting further from the start, but you '
        'are also always somewhere on the path &#8212; never at the horizon. The horizon '
        '(&#949;&#8320;) is the limit of all those steps combined. It exists as a '
        'mathematical object, but no finite number of steps reaches it.',
        'The ordinal tower works the same way. The snap that ZP-E proved occurs at &#949;&#8320; '
        'is not a step you can take from inside the tower. It is the point where the tower '
        'stops and something new begins.',
    ]))
    E.append(sp(8))

    # ── What Is ε₀? ───────────────────────────────────────────────────────────
    E.append(Paragraph('What Is &#949;&#8320;?', CS['h1']))
    E.append(cbody(
        '&#949;&#8320; (epsilon-zero) is the smallest ordinal &#945; satisfying the '
        'equation &#969;^&#945; = &#945;. In other words, it is the first fixed point '
        'of the map that sends any ordinal &#945; to &#969;^&#945; (omega raised to the '
        'power &#945;). This is not a coincidence or a definition by fiat &#8212; it is '
        'a property &#949;&#8320; satisfies and no smaller ordinal does.'))
    E.append(cbody(
        'The tower 0, 1, &#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230; climbs '
        'through the ordinals, each stage being &#969; raised to the previous stage. '
        'Every stage is strictly below &#949;&#8320;, and &#949;&#8320; is their limit &#8212; '
        'the supremum of the whole sequence. It is never reached from below; it is '
        'the boundary above all stages.'))
    E.append(sp(4))
    E.append(snap_tower_diagram())
    E.append(ccaption(
        'The tower stages 0, 1, &#969;, &#969;^&#969;, &#8230; all lie strictly below &#949;&#8320; '
        'and map to c&#8320;. The snap transition to c&#8321; occurs at the threshold &#949;&#8320; itself. '
        'The arrow marks the snap. ZP-L &#167;VII: epsilon_zero_snap_canonical.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: &#949;&#8320; is not "infinity." It is a specific countable ordinal &#8212; '
        'the first one satisfying &#969;^&#945; = &#945;. Ordinals larger than &#949;&#8320; '
        'exist (&#949;&#8320; + 1, &#949;&#8321;, and many more). ZP-L is not claiming that '
        '&#949;&#8320; is the largest ordinal or that the framework breaks down above it. It is '
        'the minimal snap threshold for monotone, tower-aligned maps &#8212; and that minimality '
        'is exactly what is proved.'))
    E.append(sp(8))

    # ── Why ε₀ Is the Exact Threshold ────────────────────────────────────────
    E.append(Paragraph('Why &#949;&#8320; Is the Exact Threshold', CS['h1']))
    E.append(cbody(
        'Two facts together pin &#949;&#8320; as the minimal snap threshold. They work like '
        'a lower bound and an upper bound that meet at the same point.'))
    E.append(cbody(
        '<b>Lower bound</b> (snap cannot happen before &#949;&#8320;): The fundamental sequence '
        'is cofinal in &#949;&#8320;. This means: for any ordinal &#945; below &#949;&#8320;, '
        'some tower stage eventually exceeds &#945;. A monotone map that assigns c&#8320; '
        'to every tower stage must therefore assign c&#8320; to &#945; too (it cannot '
        'increase between a stage above &#945; and &#945; itself). So no ordinal strictly '
        'below &#949;&#8320; can be a snap point for such a map.'))
    E.append(cbody(
        '<b>Upper bound</b> (snap does happen at &#949;&#8320;): &#949;&#8320; is itself a '
        'fixed point of &#969;^&#183; (&#969;^&#949;&#8320; = &#949;&#8320;). A map that '
        'assigns c&#8321; to all fixed points of &#969;^&#183; must assign c&#8321; to &#949;&#8320;. '
        'Together with the lower bound, &#949;&#8320; is the first place where c&#8321; can '
        'and must appear.'))
    E.append(cbody(
        'The canonical witness map &#981;(&#945;) = c&#8320; if &#945; < &#949;&#8320;, '
        'else c&#8321; satisfies all five conditions at once &#8212; monotonicity, '
        'tower-alignment, fixed-point-respecting, snapping at &#949;&#8320;, and minimality '
        '&#8212; with no free hypotheses. This is the central result of ZP-L.'))
    E.append(sp(4))
    E.append(remember_box(
        '"Minimal" does not mean "unique." ZP-L proves that no snap can occur strictly '
        'before &#949;&#8320; (under the stated conditions), not that &#949;&#8320; is the '
        'only possible snap point. Maps that also assign c&#8321; to ordinals above &#949;&#8320; '
        'are not ruled out. The framework fixes &#949;&#8320; as the threshold by '
        'the canonical witness, not by uniqueness of all satisfying maps.'))
    E.append(sp(8))

    # ── The Two-Adic Connection ───────────────────────────────────────────────
    E.append(Paragraph('The Two-Adic Connection', CS['h1']))
    E.append(cbody(
        'ZP-B established that 0 = &#8869; in the 2-adic integers &#8484;&#8322; is the '
        'valuative sink: the 2-adic valuation of 0 is infinite, which means 0 sits at the '
        'bottom of the 2-adic metric. ZP-L connects this to the ordinal tower via an '
        'encoding of ordinals below &#949;&#8320; into &#8484;&#8322; using their Cantor '
        'normal forms.'))
    E.append(cbody(
        'The encoding (cnfToZp2 in ZPL.lean) maps the n-th tower stage to 2<sup>n</sup> '
        'in &#8484;&#8322;. The 2-adic norm of 2<sup>n</sup> is (1/2)<sup>n</sup>, which '
        'goes to 0 as n increases. So as the ordinal tower climbs toward &#949;&#8320; from '
        'below, its 2-adic image descends toward 0 = &#8869; from above. Two convergences, '
        'one tower.'))
    E.append(sp(4))
    E.append(dual_convergence_diagram())
    E.append(ccaption(
        'Same tower stages, two perspectives. Teal (top row): ordinal stages 1, &#969;, &#969;^&#969;, &#8230; '
        'approach &#949;&#8320; from below. Indigo (bottom row): the 2-adic norms of their '
        'encodings 1/2, 1/4, 1/8, &#8230; converge to 0 = &#8869;. '
        'ZP-L &#167;VII: snap_zp2_correspondence.'))
    E.append(sp(4))
    E.append(cbody(
        'This dual convergence is what snap_zp2_correspondence formalizes in ZP-L &#167;VII: '
        'four independently proved facts about the same tower sequence &#8212; '
        'all stages below &#949;&#8320; in ordinal order, all assigned c&#8320; by the '
        'canonical map, all encoding to 2<sup>n</sup> in &#8484;&#8322; with 2-adic norm '
        '(1/2)<sup>n</sup> &#8594; 0, and the canonical map snapping to c&#8321; at &#949;&#8320;.'))
    E.append(sp(8))

    # ── The Kleene Connection ─────────────────────────────────────────────────
    E.append(Paragraph('The Kleene Connection', CS['h1']))
    E.append(cbody(
        'ZP-K identified &#8869; as a Kleene fixed point: a program that is its own output, '
        'guaranteed to exist by Kleene\'s second recursion theorem. ZP-L identifies '
        '&#949;&#8320; as an ordinal fixed point: the first ordinal satisfying &#969;^&#945; = &#945;, '
        'guaranteed to exist by the fixed-point theorem for normal functions. Both fixed-point '
        'proofs require Classical.choice at the same non-constructive step &#8212; the '
        'diagonal step where the fixed point is selected from an infinite collection.'))
    E.append(cbody(
        'ZP-L &#167;VI (kleene_ordinal_snap_bridge) names this structural parallel explicitly. '
        'The theorem itself is purely ordinal &#8212; no Code or eval object appears in it. '
        'What the section establishes is that the hypothesis structure of the two proofs '
        'is the same: diagonalization, non-constructive selection, fixed-point existence.'))
    E.append(sp(4))
    E.append(example_box('Two rooms, same pattern', [
        'Imagine two mathematicians working in separate rooms. One (ZP-K) is computing '
        'with programs and asking: what program runs itself? The other (ZP-L) is computing '
        'with ordinals and asking: what ordinal satisfies &#969;^&#945; = &#945;? Neither '
        'knows what the other is doing. When they compare notes, they find the same proof '
        'structure: the same diagonal argument, the same non-constructive selection step, '
        'the same kind of fixed-point existence result.',
        'ZPM (released with ZP-L) makes this precise by constructing a formal type bridge '
        '(snapEmbed) between the machine-phase and 2-adic settings, closing the gap that '
        'ZP-L\'s "Remaining Gap" section identified as outside Lean scope at time of '
        'writing. The two rooms share the same floor plan.',
    ]))
    E.append(sp(8))

    # ── Axiom Footprint Note ──────────────────────────────────────────────────
    E.append(Paragraph('A Note on Classical.choice', CS['h1']))
    E.append(cbody(
        'Every ZP-L theorem carries the axiom footprint [propext, Classical.choice, '
        'Quot.sound]. This is the standard footprint of Lean 4 + Mathlib for any theorem '
        'that uses ordinal theory, p-adic analysis, or computability. It is not a novel '
        'ZP-L commitment.'))
    E.append(cbody(
        'What is notable is where Classical.choice appears. Across the four mathematical '
        'settings of the ZP framework &#8212; topology (ZP-B), information theory (ZP-C), '
        'set theory and computation (ZP-J/K), and ordinal theory (ZP-L) &#8212; the same '
        'axiom appears at the same structural step: the non-constructive diagonal. '
        'ZP-L &#167;I documents this convergence. Whether Classical.choice is structurally '
        'forced by the ZP framework &#8212; rather than merely inherited from Mathlib '
        'infrastructure &#8212; remains an open question.'))
    E.append(sp(8))

    # ── Key Result ────────────────────────────────────────────────────────────
    E.append(key_result_box(
        'Key Result &#8212; ZP-L: The Ordinal Snap Threshold',
        'epsilon_zero_snap_canonical (ZPL.lean &#167;VII): The canonical map '
        '&#981;(&#945;) = c&#8320; if &#945; < &#949;&#8320;, else c&#8321; '
        'satisfies all five conditions simultaneously &#8212; monotone, tower-aligned '
        '(c&#8320; on every fundamental sequence stage), fixed-point-respecting '
        '(c&#8321; on every fixed point of &#969;^&#183;), snapping at &#949;&#8320;, '
        'and &#949;&#8320; minimal &#8212; with no free hypotheses. '
        'snap_zp2_correspondence co-proves that the same tower witnesses both the '
        'ordinal approach to &#949;&#8320; and the 2-adic convergence to 0 = &#8869;. '
        '24 theorems, zero sorry. ZPM closes the snapEmbed type bridge gap. &#10003;'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
