"""
Build ZP-F Illustrated Companion
Where the Snap Fails: The Real Numbers as Counterexample
Version 1.10 | May 2026
v1.5: Renamed to ZP-F Illustrated Companion; disclaimer updated to cite ZP-F
      Lean verification (F-SNAP-IMPOSSIBLE and general ordered field result).
v1.6: Section V retitled "The Coach and the Players" — reframed around zero's
      membership status rather than "wrong kind of zero"; directionality argument
      added: return paths are structurally blocked only when zero is categorically
      off the field, not a peer member of the space.
v1.7: Section IV phrasing naturalised — "Below δ you cannot go" replaced with
      "Below that, there's nowhere to go."
v1.8: Multiple fixes following reviewer feedback: (1) Section II "cleanly getting
      away" rewritten for clarity; (2) Section V "membership status" and
      "topologically identical" language replaced throughout — zero is valuatively
      distinguished in Q₂, not topologically isolated; (3) asymptotic limit
      sentence direction clarified; (4) Section III Riemann sphere analogy added;
      (5) closing "topologically isolated" replaced with correct valuative framing;
      (6) scope note added: ZP-F targets ordered fields as comparison class, not
      the most general setting where the phenomenon occurs.
v1.9: Four-fingerprint scan pass — precision review of all sections; no
      structural changes.
v1.10: New Section VIII "Two Approaches to the Same Boundary" — the density
       argument and the ordinal threshold argument are formally dual, approaching
       the same structural boundary from opposite directions; the squeeze pattern
       explained as structurally necessary rather than an optional proof technique.
v1.0: Initial release.
v1.1: Three clarifications following reviewer feedback (density/rationals,
      Planck/geometry, pi/algorithm length).
v1.2: Section V geometry note revised — floor tile / sqrt(2) argument
      correctly scoped to macroscopic scales; at the minimum unit itself,
      discrete geometry applies and irrational multiples cannot be realised.
v1.3: Section V Planck paragraph replaced with single sentence — prior
      framing overclaimed discrete geometry and integer multiples; correct
      framing is that current models break down at that scale, and the
      argument does not depend on what replaces them.
v1.4: Section V renamed "The Wrong Kind of Zero" — new structural argument
      that R models zero as a reachable point while any state-change domain
      requires zero to be an unrealizable asymptotic floor; Q2 is more
      honest because valuation +inf encodes this structurally.
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
         '0 is valuatively distinct — v&#8322;(0) = +&#8734;; every nonzero element has a finite valuation'],
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


VERSION = '1.10'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-F_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState()
        canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(
            LETTER[0] / 2, 0.6 * inch,
            'Zero Paradox ZP-F Companion | Where the Snap Fails: The Real Numbers as Counterexample'
            '  |  May 2026  |  v' + VERSION)
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
          Paragraph('ZP-F Companion  |  Version ' + VERSION + '  |  May 2026', CS['meta']),
          Paragraph(
              'This companion document is written for general readers. It explains in plain '
              'language why the real number line cannot serve as the mathematical substrate '
              'for the Binary Snap, and why the 2-adic metric Q&#8322; is required. '
              'The formal results are machine-verified in Lean 4 as part of ZP-F '
              '(F-SNAP-IMPOSSIBLE and the general ordered field result); see also '
              'ZP-B (p-adic topology) for the positive case.',
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
        'The smooth nature of the real numbers comes from the fact that between any '
        'two real numbers — no matter how close — there is always another one. '
        'This density applies uniformly: for any proposed first step &#949; > 0 away '
        'from zero, the value &#949;/2 is smaller and also positive. There is no '
        'minimal departure. The density that prevents a closest real number to zero '
        'is the same density that prevents a smallest positive real number — '
        'it works in every direction.'))
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
    E.append(cbody(
        'A geometric analogy: the Riemann sphere maps the entire complex plane onto '
        'a sphere of diameter 1, placing the origin at one pole and the point at '
        'infinity at the other. The two are antipodal — as far apart as any two '
        'points on the sphere can be. The 2-adic valuation does something '
        'structurally similar: it places zero at infinite valuation and every '
        'non-zero element at finite valuation, making zero and the rest of the '
        'number line antipodal in the valuative sense. What the Riemann sphere '
        'shows geometrically, the 2-adic valuation encodes algebraically.'))
    E.append(sp(4))
    E.append(comparison_table())
    E.append(sp(8))

    # ── IV. Finite Precision Forces the Snap ────────────────────────────────────
    E.append(Paragraph('IV. Finite Precision Forces the Snap', CS['h1']))
    E.append(cbody(
        'Every computer already knows this. Any number system with a maximum number '
        'of decimal places — any fixed-point arithmetic system, any discretized '
        'simulation — has a smallest representable positive number — call it &#948;. '
        'Below that, there\'s nowhere to go. The density argument fails at &#948;. The snap '
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
        'argument fails there. The real numbers are the most familiar example of a '
        'structure that removes this floor — but any dense ordered set has the same '
        'property, including the rational numbers: for any &#949;&#8320; > 0, '
        '&#949;&#8320; / 2 also exists. Q&#8322; puts the floor back in, '
        'mathematically rather than by truncation.'))
    E.append(sp(8))

    # ── V. The Coach and the Players ─────────────────────────────────────────────
    E.append(Paragraph('V. The Coach and the Players', CS['h1']))
    E.append(cbody(
        'The real number line is not wrong. It is internally consistent and '
        'extraordinarily useful for calculus, analysis, and modeling continuous '
        'change. But it cannot host the Binary Snap — not because it fails as '
        'a mathematical structure, but because of how it treats zero.'))
    E.append(cbody(
        'Consider a sports team. The coach and the players are not peers. The coach '
        'is not on the field, does not wear the same uniform, and cannot be substituted '
        'in. The role is categorically different — the coach is the origin and '
        'organising principle of the game, not a participant in it. You cannot return '
        'to the coach the way you move between players. That path does not exist.'))
    E.append(cbody(
        'Zero has the same relationship to the states above it. It is the floor '
        'from which everything departs — not a peer of the states, but their origin. '
        'In the ZP framework, zero is the asymptotic limit that the system moves '
        'away from, not a state it can stably occupy or return to. In &#8477;, zero '
        'has no such character: it is a regular limit point, reachable from any '
        'direction, indistinguishable in structure from 1 or &#960;. That is '
        'exactly what disqualifies it.'))
    E.append(cbody(
        'The real number line treats zero as an ordinary point — a peer of every '
        'other element, with the same local structure as 1 or &#960;. '
        'In &#8477;, zero is not valuatively distinct from any other element; '
        'every point looks the same from the perspective of the metric. '
        'That is why return paths are permitted: if zero is just another player, '
        'nothing distinguishes the path back from any other movement on the line. '
        'Directionality &#8212; the one-way ratchet the framework requires &#8212; '
        'cannot be grounded in a space where zero is indistinguishable in kind '
        'from everything else.'))
    E.append(cbody(
        'Q&#8322; gives zero a genuinely different role. The 2-adic valuation assigns '
        'zero the address +&#8734; &#8212; not a limit the other elements approach, '
        'but a categorical distinction built into the structure itself: v&#8322;(0) = '
        '+&#8734;, while every non-zero element carries a finite integer valuation. '
        'Zero is in Q&#8322; but it is not a peer. The gap between infinite and finite '
        'valuation is not a limit. It is a structural discontinuity. '
        'The coach is not on the field. The path back does not exist.'))
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
        'formula, the BBP algorithm, dozens of others — can generate &#960; to any '
        'precision you specify, however large. There is no bound on the precision '
        'you can ask for. But this is the point, not a problem: the Kolmogorov '
        'complexity of the first n digits of &#960; is tiny relative to n. '
        'The short algorithm is the information, not the infinite decimal. '
        'You can demand arbitrarily many digits; the specification of &#960; '
        'remains short regardless.'))
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

    # ── VIII. Two Approaches to the Same Boundary ────────────────────────────────
    E.append(Paragraph('VIII. Two Approaches to the Same Boundary', CS['h1']))
    E.append(cbody(
        'The density argument and the ordinal threshold argument feel like two separate '
        'observations &#8212; one about why the snap fails in &#8477;, one about where '
        'it succeeds. But they are approaching the same boundary from opposite directions, '
        'and that is not a coincidence.'))
    E.append(cbody(
        'From the field side: density shows there is no smallest positive element in &#8477;. '
        'For any candidate first step &#949; > 0, the value &#949;/2 is smaller '
        'and also positive. There is always something between any candidate step and zero. '
        'Zero is a limit point &#8212; surrounded, always approachable, never a structural floor.'))
    E.append(cbody(
        'From the ordinal side: &#949;&#8320; has no ordinal immediately below it. There is '
        'no &#945; with &#945; + 1 = &#949;&#8320;. It is the limit of the tower '
        '&#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230; &#8212; approachable from below '
        'by finite iteration, but not reachable in any finite number of steps. The snap is '
        'possible at &#949;&#8320; precisely because it has no predecessor: there is no '
        '&#8220;just before&#8221; it that the snap would have to pass through.'))
    E.append(cbody(
        'Both conditions describe the same structure from opposite sides. In the field '
        'case, zero has no smallest positive neighbour in &#8477; &#8212; density fills '
        'the gap above zero completely. In the ordinal case, &#949;&#8320; has no immediate '
        'predecessor in the ordinals &#8212; no &#945; with &#945; + 1 = &#949;&#8320; exists. '
        'The snap is the meeting point &#8212; the boundary both sides are approaching.'))
    E.append(cbody(
        'This is why the snap cannot be located by looking in just one direction. '
        'From inside the real numbers, you can see that density blocks something, '
        'but you cannot see &#949;&#8320; directly. From inside the ordinals, you '
        'can see the limit ordinal structure, but not the 2-adic topology. Neither '
        'framework alone is enough. The snap is precisely the point where each '
        'framework runs out of its own descriptive reach &#8212; which means you need '
        'both frameworks, approaching from their respective directions, to pin it down.'))
    E.append(cbody(
        'Mathematicians call this pattern the squeeze &#8212; the same idea behind the '
        'squeeze theorem in calculus, where two functions approaching a limit from above '
        'and below force the middle to the same point. Here the squeeze is not an optional '
        'proof technique. It is the only way to locate the snap, because the snap is '
        'the point where each framework runs out of its own descriptive reach.'))
    E.append(sp(8))

    # ── Closing ─────────────────────────────────────────────────────────────────
    E.append(Paragraph('The Minimal Required Structure', CS['h1']))
    E.append(cbody(
        'The real numbers are the most natural, most familiar metric space in '
        'mathematics. They are also precisely the space where the Binary Snap '
        'cannot occur. Zero is a limit point, density is symmetric, and every '
        'candidate first step admits an infinite sequence of smaller steps below it.'))
    E.append(cbody(
        'Q&#8322; is not an exotic choice. Among all completions of the rationals, '
        'Ostrowski\'s theorem says there are exactly two kinds: Archimedean ones '
        '(like &#8477;, where zero is a limit point — always approachable, never a floor) '
        'and non-Archimedean ones (&#8474;&#8346;, where the p-adic valuation assigns '
        'zero infinite valuation while every non-zero element has finite valuation). '
        'Q&#8322; is the non-Archimedean completion at p&#160;=&#160;2, '
        'the minimum prime compatible with binary existence. '
        'The valuative distinction of zero is not imposed; it follows from the completion. '
        'The framework did not choose unusual mathematics for its own sake. '
        'It followed the result to the structure the result required.'))
    E.append(cbody(
        'A note on scope: ZP-F establishes this result for linearly ordered fields — '
        'the class that contains &#8477; and &#8474; — because that is the natural '
        'comparison class for the most familiar number systems. The blocking '
        'phenomenon is not unique to fields; simpler structures with a limit point '
        'at zero show the same property. The ordered field result is the right '
        'frame for the &#8477; comparison. The broader phenomenon is the same.'))
    E.append(sp(6))
    E.append(key_result_box(
        'Where the Snap Fails',
        'The Binary Snap is impossible in &#8477;: for any &#949;&#8320; > 0, '
        '&#949;&#8320; / 2 also exists, and the density argument shows no '
        'discrete departure from zero can occur. Q&#8322; is required because '
        'the 2-adic valuation valuatively distinguishes zero — v&#8322;(0) = +&#8734;, '
        'while every non-zero element carries a finite valuation. '
        'The gap between infinite and finite valuation is not a limit. '
        'It is the theorem.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
