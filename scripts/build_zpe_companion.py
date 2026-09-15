"""
Build ZP-E Illustrated Companion
Version 1.17 | September 2026
v1.17: DECISION BATCH REMEDIATION AFTER GATE ROUND 2 (2026-09-15), companion sync with ZP-E v3.33: the T-SNAP chain diagram drew DA-1 on the shape chain while its caption puts DA-1 on the occurrence side; it now has two rows, Shape (L-RUN, TQ-IH, ZP-A D2, T-SNAP) and Occurrence (P0, DA-1, the Snap occurs with the occurrence commitment), with fixed row positions and validate_drawing.
v1.16: DECISION BATCH REMEDIATION (Tim, 2026-09-15): companion sync with ZP-E v3.31: the legal-case box says the Snap happening follows from the occurrence commitment together with DA-1 (closed given DP-2), not that it 'remains a commitment'; the T-SNAP chain diagram and its caption are kept together (the caption was orphaned onto the next page).
v1.15: OCCURRENCE COMMITMENT DEFINED, T5 RESTATED, T-SNAP RESIDUE (Tim decision batch, 2026-09-14), companion sync with ZP-E v3.30: the occurrence commitment is instantiation occurs, and that the Snap occurs follows from it together with DA-1 (closed given DP-2). The Central Advance paragraph carries the canonical AX-1 sentence; the chain caption no longer says the Snap occurring 'is that commitment'; the axioms-list paragraph glosses the occurrence commitment as instantiation occurs, not as 'that the Snap happens'. The Four Descriptions paragraph identified 'the first state (eps0)' with Peano Arithmetic's proof-theoretic ordinal and named only its least-fixed-point face; it now keeps two charts: in the ordinal chart eps0 is least fixed point AND tower supremum and the snap nucleus closes bottom to it in one step (snapNucleus_bot), in the discrete state chart eps0 names the first state above bottom, and ZP-E Remark R-eps0 claims no embedding. The name 'Binary Snap causality' here names the retired AX-1 only, so T-SNAP's name gloss is not placed in this companion.
v1.14: T-SNAP PREMISES POINT AT LEAN, companion sync with ZP-E v3.29. The p2 paragraph said the formal ZP-E 'states these premises once'; it now names Premises of T-SNAP and the Lean t_snap_given, which takes the start at bottom and the step being taken as hypotheses. The derivation-chain caption said 'six steps' against the formal seven and left the occurrence commitment out of what the Snap occurring rests on; both fixed. The legal-case box said AX-1 'is now proven (T-SNAP)'; it now scopes that to the shape of the Snap and names occurrence as a commitment. The meta line hard-coded 'April 2026'; it now uses version_line with FIRST_RELEASED = April 2026 (first commit of the companion, 2026-04-17), and the footer no longer carries a date. ROUND 1 GATES (FAIL-BEDROCK, D1) + TIM'S AX-1 SPLIT (Tim, 2026-09-14: 'Both: split it'): AX-1 bundled the SHAPE of the Snap with its OCCURRENCE. The shape half is Theorem T-SNAP; the occurrence half was never retired and is a commitment. The heading, the p2 AX-1 gloss (kept as history, now saying which half T-SNAP proves), the chain diagram string ('derived, not assumed'), the caption ('AX-1 (amber) is now a theorem'), the legal-case box (whose 'the assumption becomes a proven fact' inverted for the half that stays assumed) and the axioms-list paragraph now carry the split. t_snap_given takes TWO of the premises, the start at bottom and the FIRST step being taken. The caption no longer says 'with the definition of a Turing machine', which no box in the diagram shows. FOUR-FRAMEWORK DIAGRAM (ZPE-COMP-FOURFRAME-OVERFLOW): its internal caption string ran past the right page edge and duplicated the caption set directly beneath the diagram, so it is dropped; the framework boxes are widened from 1.35in to 1.6in, since 'ZP-C: Info Theory' measured wider than its box and was clipped; cy is fixed at 115 rather than derived from dh, dh goes from 3.4in to 3.2in, and the diagram now calls validate_drawing. AX-1 WORDING CORRECTED (Tim, 2026-09-14): retired, split into T-SNAP (shape, proved) and the occurrence commitment (stated separately); the earlier 'occurrence half was never retired' was a paraphrase error. ROUND 2 GATES (Tim rulings: title, ZP-C label, DA-1 credit): the page-1 title said 'the main causality axiom becomes a theorem', which put AX-1 whole, occurrence included, on the theorem side; it is now Tim's text, 'the causality axiom is retired, and the shape of the snap becomes a theorem'. 'The DA-1 insert changes this.' had lost its referent ('Because AX-1 says so') to the inserted split sentences and read as DA-1 overturning the occurrence commitment; it now says the insert puts an argument where 'Because AX-1 says so' stood and the occurrence commitment stays in place. The chain diagram's internal title string duplicated the caption and is dropped (R-DIAGRAM).
v1.13: T-SNAP PREMISES SYNC with ZP-E v3.28 (Tim, 2026-09-13: fold ZPE-TSNAP-PREMISES into the CC-1 arc). The chain caption said T-SNAP needs 'no axioms beyond AX-B1', and the DA-1 insert ended 'The Snap is derived - not assumed'; the informal argument also uses CC-1 (S0 = bottom) for its starting point, so both now say derived given the commitments AX-B1 and CC-1. The DA-1 paragraph said DA-1 'follows from ZP-A CC-2' and the commitment 'has become a derivation', dropping that CC-2 is itself a Forced Metatheoretic Commitment (argued, not proved); it now says the derivation is from that commitment. The Lean t_snap_derived is unaffected: no hypotheses, no axioms. ADVERSARY ROUND 3 (FAIL-BEDROCK, D1): 'What the Framework Still Assumes' still said the framework 'rests on exactly three commitments - none of them novel starting assumptions' (AX-B1, AX-G1, AX-G2), contradicting this version's own p.2 (the Snap derived given CC-1, the starting point) and p.3 (CC-2 a commitment); the formal ZP-E twin row already adds CC-1. It now says three named axioms, and names CC-1 and CC-2 as further commitments stated where they are used. CLAIM-REVIEW ROUND 3 (FAIL-BEDROCK, D1): 'The Snap is derived, given two commitments: AX-B1 and CC-1' and the caption's 'given the commitments AX-B1 and CC-1' were each one short - the chain starts at DA-1, closed only given DP-2, and occurrence is a commitment (tsnap_holds_but_nothing_moves satisfies both and never moves). Both now name the split: the Lean proof fixes the shape with no assumptions; the argument uses commitments among them AX-B1 and CC-1, and that the step happens rests further on DA-1 and the occurrence commitment; the formal ZP-E states the premises once (Premises of T-SNAP). The AX-B1 gloss 'two distinct states exist' (the decidable half) is now 'existence is binary'.
v1.12: FORCING OVERCLAIM RETRACTED. The document asserted that T-SNAP establishes the snap OCCURS. It does not: T-SNAP fixes the transition's shape, and Order/Snap.lean's NO-GO gauge tsnap_holds_but_nothing_moves proves T-SNAP holds in a model where nothing moves. Occurrence is a framework commitment (Information/Surprisal.lean's l_inf docstring is the designated honest stopping point). Prose only; no claim gains support and none is withdrawn beyond this one. The car-crash analogy described 'the forced first transition in any join-semilattice' - refuted by the gauge itself, whose MachinePhase IS a join-semilattice in which nothing moves.
v1.11: Add Goodstein/proof-theoretic context for ε₀ in Four Descriptions section.
v1.10: Strip version number from companion footer.
v1.9: Strip version numbers from DA-1 historical narrative in body prose.
v1.7: Title "AX-1 becomes a theorem" → "the main causality axiom becomes a theorem"; remember
box 1 "emergence of any state from a null condition" → scoped to ⊥→ε₀ transition; remember
box 2 "universal ontology of state emergence" removed — replaced with scoped no-claims statement.
v1.6: Disclaimer updated — "formal ontology" replaced with "formal document"; "proven" → "proved".
v1.5: four_framework_diagram: "0 is isolated" label in ZP-B box replaced with "Clopen structure".
v1.4: "topological isolation" in the closing remember box replaced with "clopen separation" —
consistent with ZP-B/D fixes; "topological isolation" evokes isolated-point topology, which is
incorrect for 0 in Q2. The correct structural property is clopen-ball separation.
v1.3: DA-1 formally closed via ZP-K noted — Paths 1 and 3 now IN LEAN SCOPE;
da1_closed_concrete : IsQuineAtom(⊥ : MachinePhase) proved in Lean 4. Formal doc at v3.7.
v1.2: AIT bridge added as third DA-1 motivating path; DP-2 two-layer structure explained;
da1_minimal_path Lean verification noted. Formal doc at v3.0.
v1.1: DA-1 diagram label updated (no longer D7-based); DA-1 status clarified as Derived Proposition
grounded in ZP-A CC-2 (⊥ = {⊥}), not a freestanding design commitment.
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
    """Two rows. Shape: L-RUN -> TQ-IH -> ZP-A D2 -> T-SNAP. Occurrence: P0 -> DA-1 -> the Snap occurs.

    DA-1 sits on the occurrence row, matching the caption: that the Snap occurs follows from the
    occurrence commitment together with DA-1 (closed given DP-2); T-SNAP fixes the shape.
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
            ('L-RUN',   ('Exec =', 'non-null'), COMP_BLUE),
            ('TQ-IH',   ('No null-only', 'trace'), COMP_BLUE),
            ('ZP-A D2', ('State change', '= Snap'), COMP_BLUE),
            ('T-SNAP',  ('Derived', 'theorem'), COMP_AMBER),
        ]),
        (38, 'Occurrence', [
            ('P₀',          ('Incomp.', 'threshold'), COMP_BLUE),
            ('DA-1',        ('⊥={⊥}: no', 'extl. interp.'), COMP_BLUE),
            ('Snap occurs', ('with the occurrence', 'commitment'), COMP_SLATE),
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
         'Initial Object Exists. There is a starting point that reaches everything. '
         'Not a novel commitment — grounded in ⊥ as the bottom element of the ZP-A semilattice.'],
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

VERSION = '1.17'
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
          Paragraph('Bridge Document | DA-1 / T-SNAP Update', CS['subtitle']),
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
        'internally closed — its job is to show that the four independent frameworks all describe '
        'the same event: the Binary Snap, from four different mathematical vantage points.'))
    E.append(cbody(
        'ZP-E does not re-derive anything. It imports closed results from each sub-document and '
        'shows their consistency. Where a cross-framework connection requires an assumption, '
        'that assumption is named explicitly as a bridge axiom — not hidden inside the argument.'))
    E.append(sp(4))

    # Four Descriptions
    E.append(Paragraph('The Four Descriptions of the Same Event', CS['h1']))
    E.append(cbody(
        'The Binary Snap — the transition from nothing (⊥) to the first state above it (ε₀, in the discrete state chart) — looks '
        'different depending on which mathematical language you use. ZP-E\'s central result is '
        'that all four descriptions are consistent: one event, four angles.'))
    E.append(cbody(
        'The symbol ε₀ has two charts, and they are not merged. In the ordinal chart, ε₀ is the '
        'proof-theoretic ordinal of Peano Arithmetic, the minimum ordinal whose '
        'well-ordering PA cannot prove. Goodstein\'s theorem is the standard witness: every '
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
        'Each arrow represents an independent mathematical description of the same event.'))
    E.append(sp(4))
    E.append(example_box('Real-world example — A car crash described by four witnesses', [
        'An engineer (forces), a doctor (injuries), a lawyer (liability), and a physicist '
        '(energy) each describe the same crash completely within their own discipline. '
        'ZP-E shows the four mathematical frameworks are in exactly this relationship to '
        'the Binary Snap.',
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
        'foundational assumption that could not be derived. The claim was: when P₀ is reached, '
        'the Snap happens. Why? Because AX-1 says so. That claim bundled two things: the shape of '
        'the Snap (what a step off ⊥ looks like) and its occurrence (that the step is taken). '
        'AX-1 is now retired, and its content was split in two: T-SNAP proves the shape, and that the Snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2).'))
    E.append(cbody(
        'The DA-1 insert puts an argument where "Because AX-1 says so" stood, and the occurrence '
        'commitment stays in place. The argument is now complete: reaching P₀ means a '
        'live machine configuration exists (DA-1). Any live configuration passes through c₁ '
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
        'DA-1 is now a Derived Proposition rather than a freestanding Design Principle. '
        'Previously DA-1 was an honest but freestanding commitment: "a configuration at P₀ '
        'is necessarily executing." Now it follows from ZP-A CC-2, ⊥ = {⊥}, which is itself a commitment '
        '(argued, not proved). The bottom element ⊥ '
        'is a Quine atom — a self-containing object with no external position from which it '
        'could be interpreted as a static description. A thing that interprets itself cannot '
        'be waiting for an external interpreter. So ⊥ at P₀ is necessarily executing. '
        'The design commitment has become a derivation from that commitment.'))
    E.append(cbody(
        '<b>The two-layer structure of DA-1:</b> DA-1 rests on two explicit layers. '
        'The first is the formal conditional: DP-2 (Execution Distinguishability) establishes '
        'that machine states carry execution history independently of output values. From DP-2, '
        'Lean 4 can derive <i>da1_minimal_path</i> — a proof that before and after instantiation '
        'produce the same output value (c₀) while the machine state changes (c₀ → c₁). '
        '`#print axioms` confirms zero axiom dependencies. This is the first Lean formalization '
        'of the core DA-1 claim, not just the surrounding algebra. '
        'The second layer asks: does ⊥ actually satisfy DP-2\'s precondition? '
        'That case rests on three converging arguments.'))
    E.append(cbody(
        '<b>Three paths to the precondition:</b> '
        '(1) CC-2/R3 (ZP-A): ⊥ = {⊥} is a Quine atom — it interprets itself, leaving no '
        'external position from which it could be read as a static description (above). '
        '(2) L-INF (ZP-C): the surprisal of ⊥ diverges to infinity — no finite static '
        'distribution can represent ⊥. '
        '(3) AIT bridge: at the incompressibility threshold P₀, the description of ⊥ '
        'is maximally incompressible — K(c₁|n)/|c₁| = 1. A string that cannot be compressed '
        'beyond itself must be its own execution; a static-description reading is ruled out by '
        'information theory alone. '
        'All three share D7\'s static/executing dichotomy as background and none is circular '
        'with DP-2.'))
    E.append(cbody(
        '<b>Lean 4 formal closure (ZP-K):</b> The three paths are not only conceptually '
        'convincing — two of them are now machine-checked. ZP-K adds a KleeneStructure instance '
        'for MachinePhase: it provides a concrete computational Quine (a code that is its own '
        'program, via Kleene\'s second recursion theorem), and proves that this Quine and the '
        'AFA self-containment argument are the same structural fact in two different languages. '
        'The result is <i>da1_closed_concrete</i>: in Lean 4, '
        'IsQuineAtom(&#8869; : MachinePhase) is a proved theorem. '
        'Path 1 (AFA self-execution) and Path 3 (computational Kleene fixed point) are now '
        'formally IN LEAN SCOPE. Path 2 (informational bridge — unbounded surprisal → necessarily '
        'executing) remains a structural claim outside current Lean formalization. '
        'The formal grounding of DA-1 is therefore: DP-2 plus two Lean-verified structural paths.'))
    # The caption is kept on the same page as its diagram (it was orphaned onto the next page).
    E.append(KeepTogether([tsnap_chain_diagram(), ccaption(
        'The T-SNAP derivation chain. The chain uses commitments, '
        'among them AX-B1 and CC-1 (S₀ = ⊥), and fixes the shape of the Snap; that the Snap occurs rests further on '
        'DA-1 (closed given DP-2) and on the commitment that instantiation occurs. AX-1 is retired: its shape is now a '
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
        'and CC-2 (⊥ = {⊥}, a ZP-A Forced Metatheoretic Commitment), which DA-1 follows from. '
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
