"""
Build ZP-E Illustrated Companion
Version 1.27 | October 2026
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect
from reportlab.graphics import renderPDF
from reportlab.platypus import KeepTogether

def four_framework_diagram():
    """Central 'Binary Snap' circle with four framework boxes pointing inward."""
    # 3.2 * 72 = 230.4 pts; content top = ZP-A box top at cy+cr+14+bh = 215.6,
    # bottom = ZP-C box bottom at cy-cr-14-bh = 14.4 (bh = 0.62in = 44.6)
    dw, dh = TW, 3.2 * inch
    d = Drawing(dw, dh)

    cx = dw / 2
    cy = 115  # fixed — do not derive from dh; top 215.6 < dh-10 = 220.4, bottom 14.4 > 5

    # Central amber circle
    cr = 42
    from reportlab.graphics.shapes import Circle
    d.add(Circle(cx, cy, cr, fillColor=COMP_AMBER, strokeColor=COMP_AMBER, strokeWidth=0))
    d.add(String(cx - 26, cy + 6,  'Binary', fontSize=9.5, fontName='DV-B', fillColor=WHITE))
    d.add(String(cx - 17, cy - 7, 'Snap',   fontSize=9.5, fontName='DV-B', fillColor=WHITE))

    # Helper: draw a teal box with two text lines and an arrow toward the center
    def framework_box(bx, by, bw, bh, label, sub1, sub2, ax1, ay1, ax2, ay2):
        d.add(Rect(bx, by, bw, bh, fillColor=COMP_BLUE, strokeColor=COMP_BLUE,
                   strokeWidth=1, rx=4, ry=4))
        d.add(String(bx + 8, by + bh - 16, label, fontSize=9.5,
                     fontName='DV-B', fillColor=WHITE))
        d.add(String(bx + 8, by + bh - 28, sub1, fontSize=7.5,
                     fontName='DV-I', fillColor=colors.white))
        d.add(String(bx + 8, by + bh - 39, sub2, fontSize=7.5,
                     fontName='DV-I', fillColor=colors.white))
        # Arrow
        d.add(Line(ax1, ay1, ax2, ay2, strokeColor=COMP_BLUE, strokeWidth=1.8))
        dx, dy = ax2 - ax1, ay2 - ay1
        ln = (dx*dx + dy*dy) ** 0.5
        if ln > 0:
            ux, uy = dx/ln, dy/ln
            px, py = -uy, ux
            hs = 6
            d.add(Line(ax2, ay2,
                       ax2 - hs*ux + hs*0.5*px, ay2 - hs*uy + hs*0.5*py,
                       strokeColor=COMP_BLUE, strokeWidth=1.8))
            d.add(Line(ax2, ay2,
                       ax2 - hs*ux - hs*0.5*px, ay2 - hs*uy - hs*0.5*py,
                       strokeColor=COMP_BLUE, strokeWidth=1.8))

    # 1.6in = 115.2 pts: the widest title, 'ZP-C: Info Theory' at 9.5pt DV-B, measures 93.2 pts
    # plus the 8 pt left inset; at 1.35in it ran past the right edge of its box.
    bw, bh = 1.6*inch, 0.62*inch

    # Top: ZP-A (above)
    bx = cx - bw/2; by = cy + cr + 14
    framework_box(bx, by, bw, bh,
                  'ZP-A: Algebra', '⊥ ≤ x for all x', 'Join accumulates',
                  cx, by, cx, cy + cr + 2)

    # Bottom: ZP-C (below)
    by2 = cy - cr - 14 - bh
    framework_box(cx - bw/2, by2, bw, bh,
                  'ZP-C: Info Theory', 'I(x) → ∞ as x → 0', 'Singularity',
                  cx, by2 + bh, cx, cy - cr - 2)

    # Left: ZP-B
    bxl = cx - cr - 16 - bw; byl = cy - bh/2
    framework_box(bxl, byl, bw, bh,
                  'ZP-B: Topology', 'Clopen structure', 'No path returns',
                  bxl + bw, cy, cx - cr - 2, cy)

    # Right: ZP-D
    bxr = cx + cr + 16; byr = cy - bh/2
    framework_box(bxr, byr, bw, bh,
                  'ZP-D: Hilbert', 'T(0) = e₀', 'Orthogonal shift',
                  bxr, cy, cx + cr + 2, cy)

    # No internal caption string: the ccaption below the diagram carries it.
    return validate_drawing(d, dh, 'four_framework_diagram')

def tsnap_chain_diagram():
    """Two rows. Shape: L-RUN -> TQ-IH -> ZP-A D2 -> T-SNAP.
    Occurrence: P0 -> occurrence commitment -> DA-1 -> the Snap occurs.

    The occurrence commitment is drawn before DA-1 because it supplies DA-1's precondition (Sense B
    at P0) and DA-1 consumes it; T-SNAP fixes the shape.
    Content: top of row-1 boxes at 134pt, lowest sub-label baseline at 14pt; dh = 2.1in (151pt).
    """
    dw, dh = TW, 2.1 * inch   # content spans 12pt .. 134pt
    d = Drawing(dw, dh)

    label_col = 62
    gap = 14
    bw = (dw - label_col - 10 - 3 * gap) / 4
    bh = 28
    rows = [
        (106, 'Shape', [
            ('L-RUN',   ('Exec =', 'non-bottom'), COMP_BLUE),
            ('TQ-IH',   ('No ⊥-only', 'trace'), COMP_BLUE),
            ('ZP-A D2', ('State change', '= Snap'), COMP_BLUE),
            ('T-SNAP',  ('Derived', 'theorem'), COMP_AMBER),
        ]),
        (38, 'Occurrence', [
            ('P₀',          ('Incomp.', 'threshold'), COMP_BLUE),
            ('Sense B',     ('occurrence', 'commitment'), COMP_SLATE),
            ('DA-1',        ('consumes it,', 'given DP-2'), COMP_BLUE),
            ('Snap occurs', ('c₀ → c₁', 'by D7'), COMP_SLATE),
        ]),
    ]
    for by, row_label, steps in rows:
        d.add(String(4, by + bh / 2 - 3, row_label, fontSize=8, fontName='DV-B', fillColor=GREY_TEXT))
        n = len(steps)
        for i, (label, sub, fill) in enumerate(steps):
            bx = label_col + i * (bw + gap)
            d.add(Rect(bx, by, bw, bh, fillColor=fill, strokeColor=COMP_BLUE,
                       strokeWidth=0.8, rx=3, ry=3))
            lw = len(label) * 6.2
            d.add(String(bx + bw/2 - lw/2, by + bh/2 - 3, label,
                         fontSize=9, fontName='DV-B', fillColor=WHITE))
            sub_y = by - 12
            for sl in sub:
                sw = len(sl) * 4.6
                d.add(String(bx + bw/2 - sw/2, sub_y, sl,
                             fontSize=7, fontName='DV-I', fillColor=GREY_TEXT))
                sub_y -= 10
            if i < n - 1:
                ax1, ax2 = bx + bw + 1, bx + bw + gap - 1
                amid = by + bh/2
                d.add(Line(ax1, amid, ax2, amid, strokeColor=COMP_BLUE, strokeWidth=1.5))
                d.add(Line(ax2-4, amid-3, ax2, amid, strokeColor=COMP_BLUE, strokeWidth=1.5))
                d.add(Line(ax2-4, amid+3, ax2, amid, strokeColor=COMP_BLUE, strokeWidth=1.5))

    # No internal title string: the ccaption below the diagram carries it.
    return validate_drawing(d, dh, 'tsnap_chain_diagram')

def axioms_table():
    """AX-B1 / AX-G1 / AX-G2 table."""
    hdr = [Paragraph('Commitment', CS['tbl_hdr']),
           Paragraph('Statement', CS['tbl_hdr'])]
    rows = [
        ['AX-B1',
         'Binary Existence. A state either exists or it does not. No third option. '
         'The framework&#8217;s ONE substantive modelling commitment: that the outcome space is DISCRETE rather than a continuum. The two states being distinct is decidable; the choice of a discrete alphabet is not, and the real numbers are where it fails.'],
        ['AX-G1',
         'Initial Object Exists, and No Terminal Object. There is a starting point that reaches everything in exactly one way, '
         'and no end point that everything reaches in exactly one way. '
         'The starting point is not a novel commitment — it is grounded in ⊥ as the bottom element of the ZP-A '
         'semilattice. The absence of an end point is ZP-G&#8217;s own commitment: in ZP-A it is an optional '
         'hypothesis, which ZP-A&#8217;s two-state carriers do not satisfy.'],
        ['AX-G2',
         'Source Asymmetry. Nothing returns to the initial object. '
         'The origin is unreachable from outside. '
         'Not a novel commitment — follows from ZP-A antisymmetry and ZP-B C3.'],
    ]
    data = [hdr] + [[Paragraph(fix(r[0]), CS['tbl_cell']),
                     Paragraph(fix(r[1]), CS['tbl_cell'])] for r in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  COMP_BLUE),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, colors.HexColor('#F0F8F8')]),
        ('BOX',           (0,0),(-1,-1), 0.5, COMP_BLUE),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, COMP_BLUE),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 5), ('BOTTOMPADDING',(0,0),(-1,-1), 5),
        ('LEFTPADDING',   (0,0),(-1,-1), 7), ('RIGHTPADDING', (0,0),(-1,-1), 7),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW*0.18, TW*0.82])
    t.setStyle(ts); return t

VERSION = '1.27'
FIRST_RELEASED = 'April 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-E_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-E Companion  |  Bridge Document')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-E Illustrated Companion', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    # Header banner
    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),COMP_BLUE),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-E Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('Four frameworks, one event —\nthe causality axiom is retired, and the shape of the snap becomes a theorem',
                    CS['title']),
          Paragraph('Bridge Document | DA-1 / T-SNAP Update | &#8220;One event&#8221; is the framework&#8217;s reading, not a theorem', CS['subtitle']),
          Paragraph('ZP Companion | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
          Paragraph(
              'This companion explains the ideas in plain language with diagrams and real-world '
              'examples. It is not the formal document — every claim here restates a result '
              'already proved in the corresponding technical document. Consult that document for '
              'the authoritative mathematics.', CS['disc'])]

    # What Is ZP-E Doing?
    E.append(Paragraph('What Is ZP-E Doing?', CS['h1']))
    E.append(cbody(
        'ZP-E is the cross-framework synthesis. Written last — after ZP-A through ZP-D are each '
        'internally closed — its job is to show how each of the four frameworks describes '
        'the Binary Snap from its own mathematical vantage point. Each description is proved within its own '
        'framework, from that framework&#8217;s own premises (ZP-D&#8217;s include its design premise DP-1). ZP-H T-H3 '
        '(th3_snap_all_functors) is their conjunction, four domain facts joined by &#8220;and&#8221;, with no functor or morphism in '
        'its statement; ZP-H&#8217;s modelling commitment is the identification, under its functors, of the objects each framework located independently. '
        'Reading the four as one event is the framework&#8217;s interpretation, not a theorem. The bottoms the four '
        'descriptions start from form a family (the bottom family, MC-1), not one object: an identity across the '
        'frameworks is retired as ill-typed, because their objects live in different mathematical types.'))
    E.append(cbody(
        'ZP-E does not re-derive anything. It imports closed results from each sub-document and '
        'shows their consistency. Where a cross-framework connection requires an assumption, '
        'that assumption is named explicitly as a bridge axiom — not hidden inside the argument.'))
    E.append(sp(4))

    # Four Descriptions
    E.append(Paragraph('Four Descriptions of the Binary Snap', CS['h1']))
    E.append(cbody(
        'The Binary Snap — the transition from nothing (⊥) to the first state above it (ε₀, in the discrete state chart) — looks '
        'different depending on which mathematical language you use. ZP-E\'s central result is '
        'that the four descriptions are consistent, each proved in its own framework. Reading them as one '
        'event seen from four angles is the framework&#8217;s interpretation, not a theorem.'))
    E.append(cbody(
        'The symbol ε₀ has two charts, and they are not merged. In the ordinal chart, ε₀ is the '
        'proof-theoretic ordinal of Peano Arithmetic, the minimum ordinal up to which PA '
        'cannot prove transfinite induction. Goodstein\'s theorem is the standard witness: every '
        'Goodstein sequence eventually terminates, but PA cannot prove this; the proof requires '
        'transfinite induction up to ε₀. That ordinal is at once the least fixed point of the map '
        'α ↦ ω^α and the supremum of the tower ω, ω^ω, ω^(ω^ω), …, and neither face replaces the other. '
        'In that chart the snap does land on it: closing ⊥ under α ↦ ω^α gives ε₀ in one step. '
        'In the discrete state chart, ε₀ names the first state above ⊥, with nothing in between, while '
        'infinitely many ordinals lie between 0 and the ordinal ε₀. The formal ZP-E treats the shared '
        'symbol as an analogy (Remark R-ε₀) and claims no embedding of one chart into the other.'))
    E.append(four_framework_diagram())
    E.append(ccaption(
        'The Binary Snap (amber center) described simultaneously in all four frameworks. '
        'Each arrow represents one framework\'s mathematical description of the Snap; that the four '
        'describe one event is the framework\'s reading, not a theorem.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — A car crash described by four witnesses', [
        'An engineer (forces), a doctor (injuries), a lawyer (liability), and a physicist '
        '(energy) each describe the same crash completely within their own discipline. '
        'ZP-E reads the four mathematical frameworks as standing in this relationship to '
        'the Binary Snap: each description is proved in its own framework, and that they describe '
        'one event is the framework&#8217;s interpretation.',
    ]))
    E.append(remember_box(
        'Remember: The car crash illustrates what it means to describe one event in multiple '
        'frameworks. The Zero Paradox is not about car crashes — the car crash is an analogy '
        'for the first transition from &#8869; to &#949;&#8320; — a transition the framework commits to, '
        'rather than one any join-semilattice compels. A join-semilattice in which T-SNAP holds and '
        'nothing moves is exhibited in the Lean source.'))
    E.append(sp(6))

    # AX-1 → T-SNAP
    E.append(Paragraph('The Central Advance: AX-1 Retired, T-SNAP Proves the Shape', CS['h1']))
    E.append(cbody(
        'In earlier versions, the Binary Snap causality was listed as AX-1 — an axiom: a '
        'foundational assumption, taken without derivation. The claim was: when P₀ is reached, '
        'the Snap happens. Why? Because AX-1 says so. That claim bundled two things: the shape of '
        'the Snap (what a step off ⊥ looks like) and its occurrence (that the step is taken). '
        'AX-1 is now retired, and its content was split in two: T-SNAP proves the shape, and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2).'))
    E.append(cbody(
        'The DA-1 insert puts an argument where "Because AX-1 says so" stood, and the occurrence '
        'commitment stays in place. The argument runs as follows. The occurrence commitment says instantiation '
        'occurs as a running configuration: the configuration reaching P₀ is a running machine&#8217;s current '
        'configuration, not an inert string. That is a commitment, not a theorem (formal ZP-E, T-SNAP Step 2). '
        'Given it, the machine has left c₀ and is at c₁, by the definition of the first running configuration (D7); '
        'DA-1 (closed given DP-2) uses that commitment and does not supply it. Any running configuration passes through c₁ '
        '(definition). c₁ is not ⊥ (L-RUN). No program avoids this (TQ-IH). A state change from '
        '⊥ to any state other than ⊥ is the Binary Snap (ZP-A D2). The Snap is derived, and that sentence has '
        'two true readings. The Lean proof is a fact about a fixed two-state machine type and takes no assumptions: '
        'it fixes the shape of the step, not that the step happens. The argument about the framework&#8217;s own '
        'sequence uses commitments, among them AX-B1 (existence is binary: a state exists or it does not) and '
        'CC-1 (the sequence starts at ⊥); that the step actually happens rests further on DA-1, which is closed '
        'only given DP-2, and on the framework&#8217;s commitment that instantiation occurs. The formal ZP-E '
        'states these premises under Premises of T-SNAP, and the Lean t_snap_given takes two of them as its hypotheses: '
        'the start at ⊥ and the first step being taken.'))
    E.append(cbody(
        'DA-1 is a Derived Proposition, closed given DP-2, as the next paragraph explains. That a '
        'configuration at P₀ is executing is not part of what it derives: that is DP-2&#8217;s precondition, '
        'and it is what the occurrence commitment asserts. ZP-A CC-2, '
        '⊥ = {⊥}, itself a commitment (argued, not proved), motivates it. The bottom element ⊥ '
        'is a Quine atom, a self-containing object with no external position from which it '
        'could be interpreted as a static description. So if ⊥ executes at all, nothing outside '
        'it can be the executor; the executor is ⊥ itself. That rules out an external executor, '
        'not an inert ⊥: the two-state machine type in the Lean source has a Quine-atom bottom '
        'and also admits a dynamics in which nothing moves. That the configuration reaching P₀ is running is the occurrence '
        'commitment, not a consequence of ⊥ = {⊥}.'))
    E.append(cbody(
        '<b>The two-layer structure of DA-1:</b> DA-1 rests on two explicit layers. '
        'The first is the formal conditional: DP-2 (Execution Distinguishability) establishes '
        'that machine states carry execution history independently of output values. From DP-2, '
        'Lean 4 can derive <i>da1_minimal_path</i> — a proof that the configurations before and after instantiation '
        'produce the same output value (c₀) while their machine states differ (c₀ before, c₁ after). '
        'It takes no assumption and does not say the step is taken; that comes from the precondition below. '
        '`#print axioms` confirms zero axiom dependencies. This is the first Lean formalization '
        'of the core DA-1 claim, not just the surrounding algebra. '
        'The second layer asks: is DP-2\'s precondition met, that is, is the configuration reaching P₀ '
        'running rather than inert? That precondition is what the occurrence commitment asserts. Three '
        'arguments bear on it, and none derives it.'))
    E.append(cbody(
        '<b>Three arguments for the precondition:</b> '
        '(1) CC-2/R3 (ZP-A): ⊥ = {⊥} is a Quine atom — it interprets itself, leaving no '
        'external position from which it could be read as a static description. As shown above, '
        'that rules out an external executor, not an inert ⊥. '
        '(2) L-INF (ZP-C): the surprisal of ⊥ diverges to infinity — no finite static '
        'distribution can represent ⊥. That rules out a finite static description; the step from '
        'there to executing is a bridge principle of its own, a missing principle and not a missing proof, '
        'which the framework does not adopt and which is separate from the occurrence commitment. '
        '(3) Computational (incompressibility as self-description): at the incompressibility threshold P₀, the configuration c₁ '
        'is maximally incompressible — K(c₁|n)/|c₁| = 1 — so no shorter external program generates it. '
        'That rules out a shorter external generator, not an inert string: an incompressible string '
        'written down and never run has no shorter generator and is still not executing. So executing '
        'is not derivable from incompressibility; that the configuration reaching P₀ '
        'is running, not inert, is what the occurrence commitment asserts. '
        'All three share D7\'s static/executing dichotomy as background and none is circular '
        'with DP-2.'))
    E.append(cbody(
        '<b>What Lean checks (ZP-K):</b> ZP-K adds a KleeneStructure instance for MachinePhase '
        '(machinePhaseKleene). Path 1&#8217;s Lean counterpart (AFA self-containment) is <i>da1_closed_concrete</i>, '
        'which proves IsQuineAtom(&#8869; : MachinePhase) and nothing computational; Path 3&#8217;s Lean counterpart '
        'is the machinePhaseKleene instance&#8217;s botCode_is_quine field, a KleeneStructure requirement that '
        'constant codes also meet, not a witness of execution and not a second independent proof. The two are '
        'carried together by da1_paths_unified as a conjunction; that they name one structural fact is the '
        'framework&#8217;s reading. Neither Path 2 (unbounded surprisal) nor Path 3 (incompressibility) derives '
        'executing: the step from unbounded surprisal to executing is a bridge principle of its own, a missing principle that the '
        'framework does not adopt and that is separate from the occurrence commitment, and Path 3 shows that '
        'executing is not derivable from incompressibility. '
        'The formal grounding of DA-1 is therefore DP-2, through da1_minimal_path.'))
    # The caption is kept on the same page as its diagram (it was orphaned onto the next page).
    E.append(KeepTogether([tsnap_chain_diagram(), ccaption(
        'The T-SNAP derivation chain. The chain uses commitments, '
        'among them AX-B1 and CC-1 (S₀ = ⊥), and fixes the shape of the Snap; that the Snap occurs rests further on '
        'the occurrence commitment (instantiation occurs), whose content is DA-1&#8217;s precondition, and on DA-1 (closed given DP-2), '
        'which consumes it. AX-1 is retired: its shape is now a '
        'theorem (T-SNAP, amber), and that the Snap occurs is stated separately, following from that commitment together with DA-1.')]))
    E.append(sp(4))
    E.append(example_box('Real-world example — A legal case proved in part', [
        'A charge can bundle two claims: "the defendant was at the scene" and "the defendant acted." '
        'Surveillance footage can prove the first while the second still rests on testimony the court '
        'chooses to accept. AX-1 bundled two claims in the same way. T-SNAP proves the first, the shape '
        'of the Snap, which was once assumed. The second, that the Snap happens, was not proved along with '
        'it: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2).',
    ]))
    E.append(sp(8))

    # Remaining Commitments
    E.append(Paragraph('What the Framework Still Assumes', CS['h1']))
    E.append(cbody(
        'After T-SNAP, the framework states three named axioms:'))
    E.append(axioms_table())
    E.append(sp(6))
    E.append(cbody(
        'AX-1 is not on this list: it is retired, and its shape is Theorem T-SNAP. Further commitments are not axioms and are stated where they are used, '
        'among them the occurrence commitment (that instantiation occurs; together with DA-1 it gives that the Snap happens), CC-1 (S₀ = ⊥, a ZP-A Conditional Claim), the choice of starting point that T-SNAP is derived given, '
        'and CC-2 (⊥ = {⊥}, a ZP-A Forced Metatheoretic Commitment), which motivates DA-1&#8217;s precondition; DA-1 itself is closed given DP-2. '
        'The framework makes no stronger claim than it has to.'))
    E.append(sp(8))
    E.append(remember_box(
        'Remember: The structural results — monotonicity, clopen separation, '
        'informational singularity, orthogonal shifts — hold in any instantiation of the '
        'framework. The framework makes no claims about which physical theory, if any, '
        'instantiates it.'))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
