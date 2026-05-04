"""
Build ZP-Reals Illustrated Companion
Where the Snap Fails: The Real Numbers as Counterexample
Version 1.0 | May 2026
v1.0: Initial release. Explains why the real number line cannot serve as the
      mathematical substrate for the Binary Snap, and why Q2 (2-adic metric)
      is required. Covers: density symmetry, where infinity lives, finite
      precision forcing, the Planck scale angle, mathematical constants as
      forced values, and structural vs. statistical incompressibility (L-INF).
"""

import os, math
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle
from reportlab.graphics import renderPDF


def pi_curve_diagram():
    """Two-panel: same circular arch smooth (many points) vs discrete (few points)."""
    dw = TW
    dh = 2.5 * inch
    d = Drawing(dw, dh)

    pw = (dw - 0.45 * inch) / 2
    pb = 0.60 * inch
    ph = 1.68 * inch
    p1x = 0.0
    p2x = pw + 0.45 * inch

    # Panel backgrounds
    for px in [p1x, p2x]:
        d.add(Rect(px + 0.08 * inch, pb, pw - 0.16 * inch, ph,
                   fillColor=colors.HexColor('#F5F9FC'),
                   strokeColor=colors.HexColor('#C5D8E8'),
                   strokeWidth=0.7, rx=5, ry=5))

    def draw_arch(panel_x, n_points, line_color, show_dots=False):
        cx = panel_x + pw / 2
        cy = pb + 0.18 * inch
        r  = pw * 0.36
        angles = [math.pi * i / (n_points - 1) for i in range(n_points)]
        pts = [(cx - r * math.cos(a), cy + r * math.sin(a)) for a in angles]
        for i in range(len(pts) - 1):
            d.add(Line(pts[i][0], pts[i][1], pts[i+1][0], pts[i+1][1],
                       strokeColor=line_color, strokeWidth=2.3))
        if show_dots:
            for pt in pts:
                d.add(Circle(pt[0], pt[1], 3.2,
                             fillColor=line_color, strokeColor=WHITE, strokeWidth=0.9))

    draw_arch(p1x, 60, COMP_BLUE,  show_dots=False)
    draw_arch(p2x,  6, COMP_AMBER, show_dots=True)

    cx1 = p1x + pw / 2
    cx2 = p2x + pw / 2

    d.add(String(cx1, 0.36 * inch,
                 'Standard scale — smooth and continuous',
                 fontSize=8, fontName='DV', fillColor=COMP_BLUE, textAnchor='middle'))
    d.add(String(cx2, 0.36 * inch,
                 'Zoomed in — the same arc shows discrete steps',
                 fontSize=8, fontName='DV', fillColor=COMP_AMBER, textAnchor='middle'))
    d.add(String(cx1, 0.19 * inch,
                 'No first step away from zero',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT, textAnchor='middle'))
    d.add(String(cx2, 0.19 * inch,
                 'A minimum unit of departure becomes visible',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT, textAnchor='middle'))

    return d


def comparison_table():
    """Side-by-side structural comparison of R and Q2."""
    hdr = [Paragraph('&#8477; Real Numbers', CS['kr_hdr']),
           Paragraph('Q&#8322; 2-adic Numbers', CS['kr_hdr'])]
    rows = [
        ['0 is a limit point — surrounded by non-zero reals on all sides',
         '0 is isolated — 2-adic valuation of 0 is +&#8734;'],
        ['Infinity lives in the representation (infinite decimal = finite magnitude)',
         'Infinity is the address of 0 (the valuation itself is +&#8734;)'],
        ['Departure from 0 is continuous — always subdivisible',
         'Departure from 0 is a discrete jump in valuation'],
        ['The snap cannot occur — density blocks every candidate first step',
         'The snap is a theorem — the valuation gap forces it'],
    ]
    data = [hdr] + [[Paragraph(fix(r[0]), CS['kr_body']),
                     Paragraph(fix(r[1]), CS['kr_body'])] for r in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (0,0),  COMP_BLUE),
        ('BACKGROUND',    (1,0), (1,0),  TEAL),
        ('ROWBACKGROUNDS',(0,1), (-1,-1), [WHITE, colors.HexColor('#EDF5F3')]),
        ('BOX',           (0,0), (-1,-1), 0.5, colors.HexColor('#888888')),
        ('LINEBELOW',     (0,0), (-1, 0), 0.5, colors.HexColor('#888888')),
        ('INNERGRID',     (0,1), (-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('LINEBEFORE',    (1,0), (1,-1),  0.5, colors.HexColor('#888888')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 7),
        ('RIGHTPADDING',  (0,0), (-1,-1), 7),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW * 0.5, TW * 0.5])
    t.setStyle(ts)
    return t


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP_Reals_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            'Zero Paradox | Where the Snap Fails: The Real Numbers as Counterexample'
            '  |  May 2026  |  v1.0')
        canvas.restoreState()

    doc = SimpleDocTemplate(
        out_path, pagesize=LETTER,
        leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
        title='Where the Snap Fails: The Real Numbers as Counterexample',
        author='Zero Paradox Project',
        onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # ── Header ─────────────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('Zero Paradox Companion',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('Where the Snap Fails', CS['title']),
          Paragraph('The Real Numbers as Counterexample', CS['subtitle']),
          Paragraph('ZP Companion  |  Version 1.0  |  May 2026', CS['meta']),
          Paragraph(
              'This companion document is written for general readers. It explains in plain '
              'language why the real number line cannot serve as the mathematical substrate '
              'for the Binary Snap, and why the 2-adic metric Q&#8322; is required. No Lean '
              'verification is associated with this document; the relevant formal results are '
              'in ZP-B (p-adic topology) and ZP-C (information theory).',
              CS['disc'])]

    # ── I. The Natural Question ─────────────────────────────────────────────────
    E.append(Paragraph('I. The Natural Question', CS['h1']))
    E.append(cbody(
        'If you have read ZP-B, a natural question arises: why the 2-adic metric? '
        'Why p-adic numbers at all? The real numbers are more familiar and more widely '
        'used. They seem like the natural substrate for any framework involving '
        'continuity, limits, and state transitions. This document is the answer.'))
    E.append(cbody(
        'The answer begins with a counterexample. The real number line is not a valid '
        'substrate for the Binary Snap — not because it is wrong, but because it is '
        'the space where the snap is structurally impossible. Understanding why the snap '
        'fails in &#8477; is the clearest path to understanding why Q&#8322; is required.'))
    E.append(sp(4))

    # ── II. The Density Symmetry ────────────────────────────────────────────────
    E.append(Paragraph('II. The Density Symmetry', CS['h1']))
    E.append(cbody(
        'The smooth nature of the real numbers comes from the fact that numbers like '
        '&#960; can have infinitely long decimal expansions. In that framework, there '
        'is no cleanly getting away from zero for the same reason there is no cleanly '
        'approaching it. The density is symmetric: approaching and departing from zero '
        'both have the same property. Between any two real numbers — no matter how '
        'close — there is always another one.'))
    E.append(cbody(
        'Zero in &#8477; is not a special topological location. It is an ordinary point '
        'on a continuum that looks the same from every direction. For any candidate '
        'first step &#949;&#8320; > 0, the number &#949;&#8320; / 2 also exists, '
        'and &#949;&#8320; / 4, and &#949;&#8320; / 2&#8319; for every n. '
        'A discrete, irreversible departure from zero — the Binary Snap — is '
        'structurally impossible in &#8477;.'))
    E.append(sp(6))
    E.append(pi_curve_diagram())
    E.append(ccaption(
        'The same mathematical arc — a piece of a circle, the curve that defines '
        '&#960; — at two sampling resolutions. At standard scale it appears smooth '
        'and continuous (left). At high zoom, discrete steps become visible (right). '
        'In the actual real numbers, the decimal expansion can always continue; '
        'the smooth curve never structurally breaks down. The snap requires '
        'a space where that breakdown is built in, not imposed.'))
    E.append(sp(8))

    # ── III. Where the Infinity Lives ──────────────────────────────────────────
    E.append(Paragraph('III. Where the Infinity Lives', CS['h1']))
    E.append(cbody(
        'The distinction between &#8477; and Q&#8322; is not a matter of degree. '
        'It is a question of where the infinity lives.'))
    E.append(cbody(
        'In &#8477;, the infinity lives in the <i>representation</i>. An infinitely '
        'long decimal like &#960; = 3.14159&#8230; describes a finite magnitude — '
        'a number sitting between 3 and 4. The infinite expansion is the notation, '
        'not the thing being noted. The number itself is finite and well-located '
        'on the line. Zero is a limit point: surrounded by non-zero reals, '
        'reachable as a limit but not isolated from them.'))
    E.append(cbody(
        'In Q&#8322;, the infinity is the <i>address</i> of zero. The 2-adic '
        'valuation assigns +&#8734; to 0 — not as a limit the valuation approaches, '
        'but as its actual value. Every non-zero element carries a finite integer '
        'valuation. The gap between infinite valuation and any finite valuation is '
        'not a limit. It is a structural discontinuity built into the metric itself.'))
    E.append(sp(4))
    E.append(comparison_table())
    E.append(sp(8))

    # ── IV. Finite Precision Forces the Snap ────────────────────────────────────
    E.append(Paragraph('IV. Finite Precision Forces the Snap', CS['h1']))
    E.append(cbody(
        'Every computer already knows this. Any number system with a maximum number '
        'of decimal places — any fixed-point arithmetic system, any discretized '
        'simulation — has a smallest representable positive number. Call it &#948;. '
        'Below &#948; you cannot go. The density argument fails at &#948;. The snap '
        'is forced: there is a genuine first step, and halving it is not possible.'))
    E.append(cbody(
        'The real numbers are the idealization in which this floor is removed — the '
        'limiting case in which precision is unbounded and the minimum disappears. '
        'That is not a feature from the perspective of the Zero Paradox. It is '
        'exactly what blocks the snap.'))
    E.append(cbody(
        'Q&#8322; is not an artificially truncated real line. It is a different '
        'metric space in which the floor is structural — not imposed by finite '
        'memory or finite precision, but built into the 2-adic valuation itself.'))
    E.append(sp(4))
    E.append(remember_box(
        'Every finite computational system is already subject to the Binary Snap by '
        'construction. The minimum representable positive value exists; the density '
        'argument fails there. The real numbers are the exceptional case — the one '
        'structure that removes the floor by allowing infinite precision. Q&#8322; '
        'puts the floor back in, mathematically rather than by truncation.'))
    E.append(sp(8))

    # ── V. The Curve of a Perfect Pi ────────────────────────────────────────────
    E.append(Paragraph('V. The Curve of a Perfect &#960;', CS['h1']))
    E.append(cbody(
        'There is a physical version of this argument. If the Planck length is a '
        'genuine minimum — if anything smaller is physically indistinguishable from '
        'zero — then even the curve of a perfect &#960;, zoomed in past that scale, '
        'would show discrete jumps rather than smooth continuity. The infinite '
        'decimal expansion becomes physically meaningless below that threshold. '
        'The real number is smooth because we allowed the decimal to run forever. '
        'If the universe does not, the real number line is an idealization of '
        'something that is actually discrete.'))
    E.append(cbody(
        'The Planck length may or may not be the correct value for that minimum. '
        'The specific number is a question for physics, and it remains open. '
        'But the structural claim is independent of it: some minimum deviation '
        'from zero must exist in any physical system where zero and non-zero are '
        'genuinely distinct conditions. If the continuum ran all the way down '
        'with no floor, the difference between something and nothing would be a '
        'matter of infinite precision, not a real physical distinction. '
        'The minimum does not have to be the Planck length. It just has to exist.'))
    E.append(sp(8))

    # ── VI. Mathematical Constants and Forcing ──────────────────────────────────
    E.append(Paragraph('VI. Mathematical Constants and Forcing', CS['h1']))
    E.append(cbody(
        'A natural follow-on question: if infinitely long decimals are the issue, '
        'what about &#960; itself? &#960; is infinitely long. Does it already '
        'qualify for the incompressibility results elsewhere in the ZP framework?'))
    E.append(cbody(
        'No — and the reason matters. &#960; is infinitely long in its decimal '
        'expansion, but it is <i>computable</i>. Finite algorithms — the Leibniz '
        'formula, the BBP algorithm, dozens of others — generate &#960; to any '
        'desired precision. The Kolmogorov complexity of the first n digits of '
        '&#960; is tiny relative to n: the short algorithm is the information, '
        'not the infinite decimal.'))
    E.append(cbody(
        'This is what makes &#960; a <i>constant</i> rather than an arbitrary '
        'number. It is the necessary consequence of a geometric relationship — '
        'the ratio of circumference to diameter — and that relationship provides '
        'the compression. The value is forced by the definition. The computability '
        'follows from the forcing. Constants are computable because they have '
        'finite definitions; the finite definition is the short program.'))
    E.append(cbody(
        'Most real numbers are not like this. Almost all real numbers — in the '
        'measure-theoretic sense — have no finite definition that picks them out. '
        'They are algorithmically random: no short program generates them; the '
        'first n digits have Kolmogorov complexity close to n. High algorithmic '
        'complexity is the signature of a number with no mathematical structure '
        'behind it, no definition that points to it specifically.'))
    E.append(sp(8))

    # ── VII. Two Kinds of Incompressibility ─────────────────────────────────────
    E.append(Paragraph('VII. Two Kinds of Incompressibility', CS['h1']))
    E.append(cbody(
        'This brings us to a subtle but important point. ZP-C includes the result '
        'L-INF: the null state &#8869; has unbounded surprisal — no finite external '
        'description can capture it. A careful reader might ask: is this the same '
        'as saying &#8869; is algorithmically incompressible, like a random real number?'))
    E.append(cbody(
        'It is not. The distinction is the difference between randomness and necessity.'))
    E.append(cbody(
        'A random real number is incompressible because it has no structure — '
        'no mathematical relationship forces it to be what it is. Its complexity '
        'is high because it is arbitrary. Nothing points to it specifically.'))
    E.append(cbody(
        '&#8869; is incompressible for the opposite reason: because anything '
        'standing external to it is structurally excluded. Nothing can occupy '
        'a position outside &#8869; to describe it — not because the description '
        'is too complex, but because the position of "external to &#8869;" does '
        'not exist. &#8869; is not arbitrary. It is the most constrained object '
        'in the framework, the unique global minimum of the lattice. Its '
        'incompressibility is not the noise of randomness. It is the silence '
        'of structural necessity.'))
    E.append(cbody(
        'The real number line mixes both kinds — computable constants alongside '
        'algorithmically random reals — with no topological distinction between '
        'them. ZP-C\'s L-INF is a claim of an entirely different character.'))
    E.append(sp(4))
    E.append(example_box(
        'The contrast in one sentence',
        ['A random real is incompressible because nothing forced it to be what it is. '
         '&#8869; is incompressible because nothing can stand outside it. '
         'One is the absence of structure. The other is structure all the way down.']))
    E.append(sp(8))

    # ── Closing ─────────────────────────────────────────────────────────────────
    E.append(Paragraph('The Minimal Required Structure', CS['h1']))
    E.append(cbody(
        'The real numbers are the most natural, most familiar metric space in '
        'mathematics. They are also precisely the space where the Binary Snap '
        'cannot occur. Zero is a limit point, density is symmetric, and every '
        'candidate first step admits an infinite sequence of smaller steps below it.'))
    E.append(cbody(
        'Q&#8322; is not an exotic choice. It is the minimal metric structure in '
        'which the structural isolation of zero is built in — not imposed by finite '
        'precision, not approximated, but present in the 2-adic valuation itself. '
        'The framework did not choose unusual mathematics for its own sake. '
        'It followed the result to the structure the result required.'))
    E.append(sp(6))
    E.append(key_result_box(
        'Where the Snap Fails',
        'The Binary Snap is impossible in &#8477;: for any &#949;&#8320; > 0, '
        '&#949;&#8320; / 2 also exists, and the density argument shows no '
        'discrete departure from zero can occur. Q&#8322; is required because '
        'the 2-adic valuation structurally isolates zero — its valuation is '
        '+&#8734;, while every non-zero element carries a finite valuation. '
        'The gap between them is not a limit. It is the theorem.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
