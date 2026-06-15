"""
Build ZP-J Illustrated Companion
Version 1.25 | June 2026
v1.25: §6 "future work" bridge sentence retired — the 2-adic valuation argument is now formalized (ZPJ_ScaleBridge wired into the maintained build); §7 gains the common-ancestor (ValBridge) framing — the abstract lattice track and ℤ₂ are instances of one minimal typeclass; §8 adds ℤ₂ as a third concrete model. The ℤ₂ instance is flagged as inheriting Classical.choice from Mathlib's p-adic library (unlike the axiom-free core T-EXEC).
v1.24: Directed-graph (APG) diagram added for the Quine atom (self-loop + well-founded chain ending at ∅); arithmetic analogy scoped (it cannot show ⊥={⊥} — routed to mirror/graph); "depth" rephrased from "how far from ⊥" to intrinsic descent/valuation (Dan feedback 2026-06-15). Fixed latent null glyph scaleᵏ (&#7503; → <sup>k</sup>).
v1.23: "his question" pronoun fixed; abstraction chain direction clarified; remember_box leads with analogy; p-adic removed from disclaimer (future work); "Not three separate" prose replaced; T-EXEC antecedent named (ER/AR fixes).
v1.22: "ZP lattice" replaced with structural description; "bounded semilattice" corrected to join-semilattice; AFAStructure typeclass used directly; Aczel specific claims replaced with generic AFA fixed-point framing (ER/AR fixes).
v1.21: ZP-A semilattice replaced with standard structural description; section heading scoped; AFA/ZP-J framing clarified; "uniqueness half" hedged as analogous (AR fixes).
v1.20: Aczel attribution removed; open question stated without attribution (AR fix).
v1.19: Plain-meaning table corrected; AFA/ZP-J scope clarified; sorry note added to key result box (AR/ER fixes).
v1.18: Three residual em-dashes in three_way_table() removed (ER fix).
v1.17: Em-dashes removed; Quine Atom added to tagline; 2-adic analogy caveat moved to front (AR/ER fixes).
v1.16: Title reverted to "The Self-Containing Null".
v1.15: Title changed to "The Quine Atom" (standard AFA term).
v1.14: "full AFA decoration" scoped to finite APGs; Aczel quote paraphrased; sorry-free claim scoped (ER fixes).
v1.13: Disclaimer leads with AFA math before brand name (AR fix).
v1.12: "Zero Paradox" expanded in disclaimer; "Really" dropped from subtitle (AR fix).
v1.11: Em-dashes removed from subtitle and first body paragraph; opening paragraph
       rewritten to lead with AFA mathematical content (AR/ER fix).
v1.10: Header banner color corrected INDIGO → COMP_BLUE (matches all other companions).
v1.9: Cover and disclaimer updated to reflect that this companion serves both
      ZP-J Self-Reference and ZP-J AFA Addendum.
v1.8: quine_atom_diagram — replace HTML entities (&#8869;) with literal ⊥ in
      String() drawing primitives; entities render literally there, not as glyphs.
v1.7: vocab fix: ZP-J v2.0 → ZP-J.
v1.6: Five new sections added for ZP-J content — the valuation argument,
      the abstraction chain, two concrete models, Aczel's DC question, and
      APG decoration uniqueness. Key result box updated.
v1.5: Strip version number from companion footer.
v1.4: Strip version number from disclaimer cross-reference to ZP-J formal document.
v1.3: Disclaimer updated — "formal ontology" replaced with "formal document". Opening paragraph
      revised — DA-1 glossed on first use instead of using internal label alone.
v1.2: quine_atom_diagram: dh increased (2.0 → 2.8 in), cy changed to fixed 110 so the
      "⊥ = {⊥}" label (cy - r_outer - 18) no longer falls at y=-18 below the drawing box.
v1.1: Corrected CC-2 status to metatheoretic commitment within ZF+AFA; commitment shifts
to the AFA setting itself. CC-1 remains fully discharged axiom-free. Aligns with R-J.0.
v1.0: Initial release. Covers T-EXEC (Quine atom = ⊥), the three-way equivalence,
and the closure of CC-1 and CC-2 as derived theorems rather than freestanding commitments.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Path
from reportlab.graphics import renderPDF

def quine_atom_diagram():
    """Diagram showing ⊥ ∈ ⊥ — the self-containing bottom element."""
    dw, dh = TW, 2.8 * inch
    d = Drawing(dw, dh)

    cx = dw / 2
    cy = 110  # fixed — do not derive from dh; label at cy-r_outer-18 = 20 > 0

    # Outer circle (the set {⊥})
    r_outer = 72
    d.add(Circle(cx, cy, r_outer, fillColor=INDIGO_LITE,
                 strokeColor=INDIGO, strokeWidth=1.5))
    d.add(String(cx - 22, cy + r_outer - 18, '{',
                 fontSize=28, fontName='DV', fillColor=INDIGO))
    d.add(String(cx + 4,  cy + r_outer - 18, '}',
                 fontSize=28, fontName='DV', fillColor=INDIGO))

    # Inner circle (⊥ as element)
    r_inner = 28
    d.add(Circle(cx, cy, r_inner, fillColor=INDIGO,
                 strokeColor=INDIGO, strokeWidth=0))
    d.add(String(cx - 9, cy - 6, '⊥',
                 fontSize=16, fontName='DV-B', fillColor=WHITE))

    # Label: ⊥ = {⊥}
    d.add(String(cx - 28, cy - r_outer - 18, '⊥  =  {⊥}',
                 fontSize=13, fontName='DV-B', fillColor=INDIGO))

    # Self-membership arrow
    ax, ay = cx, cy + r_inner + 2
    bx, by = cx, cy + r_outer - 4
    d.add(Line(ax, ay, bx, by, strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(bx - 5, by - 6, bx, by, strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(bx + 5, by - 6, bx, by, strokeColor=INDIGO, strokeWidth=1.5))

    d.add(String(14, 10,
                 'The Quine atom: ⊥ is a member of itself. '
                 'The outer ring is the set {⊥}; the inner disk is ⊥ as an element.',
                 fontSize=7.5, fontName='DV-I', fillColor=GREY_TEXT))
    return d


def quine_graph_diagram():
    """Directed-graph (APG) view: ordinary chains end at ∅; ⊥ loops on itself."""
    dw, dh = TW, 2.5 * inch  # 180 pts; content top ~152, bottom ~63
    d = Drawing(dw, dh)
    cy = 105

    # LEFT — well-founded chain  a -> b -> ∅
    d.add(Circle(60, cy, 15, fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1.3))
    d.add(String(56, cy - 5, 'a', fontSize=12, fontName='DV-B', fillColor=INDIGO))
    d.add(Circle(130, cy, 15, fillColor=INDIGO_LITE, strokeColor=INDIGO, strokeWidth=1.3))
    d.add(String(126, cy - 5, 'b', fontSize=12, fontName='DV-B', fillColor=INDIGO))
    d.add(Circle(196, cy, 13, fillColor=WHITE, strokeColor=INDIGO, strokeWidth=1.3))
    d.add(String(191, cy - 5, '∅', fontSize=12, fontName='DV', fillColor=INDIGO))
    d.add(Line(76, cy, 113, cy, strokeColor=GREY_TEXT, strokeWidth=1.2))
    d.add(Line(107, cy + 4, 113, cy, strokeColor=GREY_TEXT, strokeWidth=1.2))
    d.add(Line(107, cy - 4, 113, cy, strokeColor=GREY_TEXT, strokeWidth=1.2))
    d.add(Line(146, cy, 181, cy, strokeColor=GREY_TEXT, strokeWidth=1.2))
    d.add(Line(175, cy + 4, 181, cy, strokeColor=GREY_TEXT, strokeWidth=1.2))
    d.add(Line(175, cy - 4, 181, cy, strokeColor=GREY_TEXT, strokeWidth=1.2))
    d.add(String(46, cy - 42, 'well-founded: the chain ends at ∅',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))

    # RIGHT — Quine atom ⊥ with a self-loop (dashed: exits right, re-enters the top)
    qx = 365
    d.add(Circle(qx, cy, 18, fillColor=INDIGO, strokeColor=INDIGO, strokeWidth=0))
    d.add(String(qx - 9, cy - 6, '⊥', fontSize=16, fontName='DV-B', fillColor=WHITE))
    loop = Path(strokeColor=INDIGO, strokeWidth=1.4, fillColor=None,
                strokeDashArray=[2.5, 2.5])
    loop.moveTo(qx + 18, cy)                       # exit the right edge
    loop.curveTo(qx + 55, cy, qx, cy + 50, qx, cy + 18)  # arc up and back into the top
    d.add(loop)
    # solid arrowhead at the top entry, pointing down into the ball
    d.add(Line(qx - 5, cy + 25, qx, cy + 18, strokeColor=INDIGO, strokeWidth=1.4))
    d.add(Line(qx + 5, cy + 25, qx, cy + 18, strokeColor=INDIGO, strokeWidth=1.4))
    d.add(String(qx - 42, cy - 42, '⊥ = {⊥}: the chain loops on itself',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))
    return d


def three_way_table():
    """Three-way equivalence: Quine atom = bottom element = join identity."""
    hdr = [Paragraph('Language', CS['tbl_hdr']),
           Paragraph('What ⊥ satisfies', CS['tbl_hdr']),
           Paragraph('Plain meaning', CS['tbl_hdr'])]
    rows = [
        ['Set theory (AFA)',
         '&#8869; &#8712; &#8869;  (i.e. &#8869; = {&#8869;})',
         '⊥ contains exactly one element: itself - the unique self-membership condition in AFA'],
        ['Order theory (ZP-A)',
         '&#8869; &#8804; x  for all x',
         '⊥ is below everything - the universal starting point'],
        ['Algebra (ZP-A A4)',
         '&#8869; &#8744; x = x  for all x',
         '⊥ contributes nothing to any join - the additive zero'],
    ]
    data = [hdr] + [[Paragraph(fix(r[0]), CS['tbl_cell']),
                     Paragraph(fix(r[1]), CS['tbl_cell']),
                     Paragraph(fix(r[2]), CS['tbl_cell'])] for r in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  INDIGO),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, INDIGO_LITE]),
        ('BOX',           (0,0),(-1,-1), 0.5, INDIGO),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, INDIGO),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 5), ('BOTTOMPADDING',(0,0),(-1,-1), 5),
        ('LEFTPADDING',   (0,0),(-1,-1), 6), ('RIGHTPADDING', (0,0),(-1,-1), 6),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW*0.22, TW*0.28, TW*0.50])
    t.setStyle(ts); return t


def abstraction_chain_table():
    """Three-level abstraction chain."""
    hdr = [Paragraph('Typeclass', CS['tbl_hdr']),
           Paragraph('What you commit to', CS['tbl_hdr']),
           Paragraph('What you get for free', CS['tbl_hdr'])]
    rows = [
        ['ValuationStructure',
         'A scale operation + a depth measure that increases by 1 at each non-⊥ step',
         'unique_fp as a theorem: ⊥ is the only fixed point of scale'],
        ['AbstractSelfApp',
         'A self-application with ⊥ as fixed point and ⊥ as the only fixed point',
         'All three AFA fields (selfMem, bot_self_mem, quine_unique) as theorems'],
        ['AFAStructure',
         'selfMem, bot_self_mem, quine_unique directly as typeclass fields',
         'T-EXEC, J1, CC-1 as proved theorems'],
    ]
    data = [hdr] + [[Paragraph(fix(r[0]), CS['tbl_cell']),
                     Paragraph(fix(r[1]), CS['tbl_cell']),
                     Paragraph(fix(r[2]), CS['tbl_cell'])] for r in rows]
    ts = TableStyle([
        ('BACKGROUND',    (0,0),(-1,0),  INDIGO),
        ('ROWBACKGROUNDS',(0,1),(-1,-1), [WHITE, INDIGO_LITE]),
        ('BOX',           (0,0),(-1,-1), 0.5, INDIGO),
        ('LINEBELOW',     (0,0),(-1,0),  0.5, INDIGO),
        ('INNERGRID',     (0,1),(-1,-1), 0.3, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0),(-1,-1), 5), ('BOTTOMPADDING',(0,0),(-1,-1), 5),
        ('LEFTPADDING',   (0,0),(-1,-1), 6), ('RIGHTPADDING', (0,0),(-1,-1), 6),
        ('VALIGN',        (0,0),(-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW*0.22, TW*0.38, TW*0.40])
    t.setStyle(ts); return t


VERSION = '1.25'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-J_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-J Companion  |  Self-Reference  |  June 2026')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-J Illustrated Companion', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),COMP_BLUE),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-J Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('The Self-Containing Null', CS['title']),
          Paragraph('What &#8869; = {&#8869;} Means, and Why It Matters', CS['subtitle']),
          Paragraph('ZP Companion | Version ' + VERSION + ' | The Quine Atom | June 2026', CS['meta']),
          Paragraph(
              'This companion explains in plain language the proof that &#8869; = {&#8869;} '
              '(the Quine atom of AFA set theory) is the unique bottom element of a lattice. '
              'This is one result in the Zero Paradox project (ZP-J), connecting '
              'AFA set theory, p-adic topology, and lattice algebra. '
              'It covers both '
              'ZP-J Self-Reference and the ZP-J AFA Addendum. Every formal result stated '
              'here restates a theorem already proved in those technical documents. '
              'Informal analogies and illustrative parallels are included to build '
              'intuition, not as proof claims. Consult the technical documents for '
              'the authoritative mathematics.', CS['disc'])]

    # ── What Is ZP-J Doing? ──────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-J Doing?', CS['h1']))
    E.append(cbody(
        'In AFA set theory, the Quine atom &#8869; = {&#8869;} is provably the unique '
        'bottom element of the join-semilattice structure defined in ZP-A. This turns what ZP-E carried as a modelling '
        'assumption into a derived theorem. ZP-J is the document that proves it, using '
        'the valuation structure of Q&#8322; and the AFA uniqueness result. '
        'The structural argument: nothing external to &#8869; can execute &#8869;, '
        'so &#8869; must execute itself, which forces &#8869; = {&#8869;} '
        '(see ZP-E for the full three-path argument).'))
    E.append(cbody(
        'ZP-J makes that argument formal. It proves, in Lean 4 with no axioms beyond the '
        'standard mathematical infrastructure, that in any join-semilattice with a bottom element '
        'carrying an AFAStructure typeclass (in the ZF+AFA setting), '
        'the unique self-containing set  - the Quine atom  - '
        'is provably the bottom element &#8869;. CC-2 (&#8869; = {&#8869;}) is no longer a '
        'freestanding modelling assumption  - within ZF+AFA, it is a derived consequence '
        'of T-EXEC, not a choice. CC-1 (S&#8320; = &#8869;) is a derived consequence of '
        'the algebra with no additional axioms.'))
    E.append(cbody(
        'ZP-J extends the T-EXEC result in four directions: it shows that '
        'the proof requires no appeal to the axiom of Dependent Choice; it reduces the '
        'typeclass commitments layer by layer down to a pure valuation argument; it '
        'demonstrates the structure on two concrete types; and it proves a '
        'decoration uniqueness theorem for finite APGs.'))
    E.append(sp(4))

    # ── What Is a Quine Atom? ────────────────────────────────────────────────
    E.append(Paragraph('What Is a Quine Atom?', CS['h1']))
    E.append(cbody(
        'In ordinary set theory (ZF with the Foundation axiom), every set has a "rank"  - '
        'a measure of how deeply nested its membership is. A set like {{{&#8709;}}} has rank 3 '
        'because you have to unwrap three layers to reach the empty set. Importantly, no '
        'set under Foundation can be a member of itself: that would create an infinite '
        'descending chain &#8869; &#8715; &#8869; &#8715; &#8869; &#8715; &#8230; with no bottom.'))
    E.append(cbody(
        'Anti-Foundation (AFA) drops that prohibition. It allows non-well-founded sets  - '
        'sets that can be members of themselves. The simplest such object is the Quine atom: '
        'a set x satisfying x = {x}. It contains exactly one element: itself. Unwrapping it '
        'gives x again, not &#8709;. There is no bottom to the chain  - it loops back. '
        'Under AFA, the unique decoration theorem guarantees exactly one such set exists.'))
    E.append(quine_atom_diagram())
    E.append(ccaption(
        'The Quine atom ⊥ = {⊥}: ⊥ is the sole member of itself. '
        'The outer ring is the set {⊥} and the inner disk is ⊥ as an element. '
        'They are the same object.'))
    E.append(sp(6))
    E.append(quine_graph_diagram())
    E.append(ccaption(
        'A second way to see it - as a directed graph (an "accessible pointed graph", or APG, '
        'the structure Aczel\'s anti-foundation axiom decorates). Each arrow points from a set '
        'to one of its members. Ordinary sets are well-founded: following the arrows always ends, '
        'here at the empty set ∅. The bottom ⊥ is the lone exception - its arrow loops straight '
        'back to itself. That self-loop is exactly ⊥ = {⊥}, the Quine atom: a membership chain '
        'that never bottoms out.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy  - A mirror facing a mirror', [
        'Hold two mirrors facing each other. Each reflection contains the other mirror, '
        'which contains another reflection, which contains another mirror &#8230; infinitely. '
        'The image is self-referential: the full scene is visible inside itself at every '
        'level. The Quine atom &#8869; = {&#8869;} has this structure  - &#8869; is inside '
        'itself, not as a smaller copy, but as the same object.',
    ]))
    E.append(sp(8))

    # ── T-EXEC ───────────────────────────────────────────────────────────────
    E.append(Paragraph('T-EXEC: The Quine Atom Is Uniquely &#8869;', CS['h1']))
    E.append(cbody(
        'The central theorem of ZP-J is T-EXEC (Executability of Self-Reference). It states:'))
    E.append(key_result_box(
        'Theorem T-EXEC',
        'In any type carrying the AFAStructure typeclass (in the ZF+AFA setting), an element q is a Quine atom '
        '(q = {q}, i.e. q ∈ q) if and only if q = ⊥. '
        'The Quine atom property uniquely identifies the bottom element. '
        'Proved axiom-free in Lean 4 (ZeroParadox.ZPJ.t_exec).'))
    E.append(sp(6))
    E.append(cbody(
        '<b>Quine atom &#8594; &#8869;:</b> Suppose q = {q}. AFA uniqueness says there is '
        'exactly one such set. The bottom element &#8869; satisfies bot_self_mem  - '
        'it is self-containing by the typeclass field. Applying uniqueness: q = &#8869;.'))
    E.append(cbody(
        '<b>&#8869; &#8594; Quine atom:</b> &#8869; is self-containing (bot_self_mem). '
        'Any other self-containing x equals &#8869; by quine_unique. So &#8869; is the unique '
        'self-containing element  - the Quine atom.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: T-EXEC does not say ⊥ is physically self-referential. It says the '
        'mathematical structure requires that the bottom element, properly grounded under AFA, '
        'satisfies the same uniqueness condition as the Quine atom. The two notions identify '
        'the same object.'))
    E.append(sp(8))

    # ── Three Languages, One Object ──────────────────────────────────────────
    E.append(Paragraph('Three Languages, One Object', CS['h1']))
    E.append(cbody(
        'T-EXEC establishes a three-way identification. &#8869; is the same object described '
        'in three different mathematical languages:'))
    E.append(three_way_table())
    E.append(sp(4))
    E.append(cbody(
        'These are not three separate properties that happen to coincide. They are three '
        'descriptions of the same structural role. T-EXEC makes this explicit and '
        'machine-checked.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy  - Zero in arithmetic (partial)', [
        '0 in arithmetic wears more than one hat at once: it is the additive identity '
        '(x + 0 = x) and the smallest non-negative integer (0 ≤ n for all n ∈ ℕ). '
        'Those two line up cleanly with ⊥ as join identity and ⊥ as minimum. '
        'But arithmetic has no honest way to show the third hat - ⊥ as the Quine atom '
        '(⊥ = {⊥}, "zero inside zero"): ordinary numbers simply do not contain themselves. '
        'For that self-containing property the right pictures are the mirror-facing-a-mirror '
        'analogy and the directed graph above, not arithmetic.',
    ]))
    E.append(sp(8))

    # ── Two Assumptions That Became Theorems ─────────────────────────────────
    E.append(Paragraph('Two Assumptions That Became Theorems', CS['h1']))
    E.append(cbody(
        'Before ZP-J, the framework carried two Conditional Claims  - honest admissions '
        'that certain structural facts were assumed rather than derived:'))
    E.append(cbody(
        '<b>CC-2 (&#8869; = {&#8869;}):</b> Previously a modelling commitment in ZP-A. '
        'ZP-J T-EXEC changes the nature of the claim. Within ZF+AFA, &#8869; = {&#8869;} is '
        'a proved consequence of the ZP-A axioms  - forced, not assumed. The commitment '
        'shifts one level up: it is the AFA setting itself.'))
    E.append(cbody(
        '<b>CC-1 (S&#8320; = &#8869;):</b> ZP-J proves <i>cc1_derived</i> in Lean 4: '
        'given T-EXEC and A4, the initial state that admits no external interpreter is '
        'uniquely the bottom. S&#8320; = &#8869; is derived, not assumed.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: ZP-J does not prove that ⊥ is self-referential by definition. '
        'It proves that the standard axioms of the semilattice, combined with the AFA '
        'setting, force the bottom element to be self-containing. '
        'The conclusion is derived; the axioms are standard.'))
    E.append(sp(8))

    # ── The Valuation Argument ───────────────────────────────────────────────
    E.append(Paragraph('Why Only &#8869; Can Be Self-Applying', CS['h1']))
    E.append(cbody(
        'T-EXEC uses the AFA typeclass fields directly. But there is a deeper question: '
        '<i>why</i> is &#8869; the unique fixed point? The valuation argument answers this, '
        'and it is the insight behind ZP-J\'s abstraction chain.'))
    E.append(cbody(
        'Imagine every element carries a "depth"  - a value in the extended naturals '
        '{0, 1, 2, &#8230;, &#8734;} given by how many times you can descend through its '
        'structure before bottoming out. Ordinary elements bottom out '
        'in finitely many steps, so their depth is finite; &#8869; never bottoms out  - it '
        'contains itself  - so its depth is &#8734;. Applying scale  - the self-application '
        'operation  - raises depth by exactly 1 at every non-&#8869; element. '
        'So if scale(x) = x, then depth(x) = depth(x) + 1  - an equation with no finite '
        'solution. Only &#8869;, whose depth is already &#8734; (and &#8734; + 1 = &#8734; in '
        'the extended naturals), can satisfy it. &#8869; is the only fixed point.'))
    E.append(cbody(
        'This same argument runs in 2-adic arithmetic, and there it is formalized in Lean. '
        'Multiplication by 2 is the scale operation, '
        'the 2-adic valuation v&#8322;(x) measures how many times 2 divides x (a kind of depth), '
        'and v&#8322;(2x) = v&#8322;(x) + 1 for any x &#8800; 0. '
        'So 2x = x forces v&#8322;(x) = v&#8322;(x) + 1 - impossible for finite valuation. '
        'Only 0, with v&#8322;(0) = &#8734;, satisfies 2 &#215; 0 = 0. '
        'The 2-adic integers &#8484;&#8322; are a machine-checked instance of exactly this '
        'valuation argument (see the models below). Unlike the axiom-free core (T-EXEC), this '
        'instance inherits the axiom of choice from Mathlib\'s p-adic library.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy  - The elevator that only goes up', [
        'Imagine an elevator that, when you press a button, moves one floor higher  - '
        'unless you are already at the top floor, in which case it stays put. '
        'The top floor is the only "fixed point": pressing the button leaves you there. '
        'Every other floor gets nudged upward. In the &#8469;&#8734; model, &#8869; is the '
        'top floor (&#8734;, the largest extended natural)  - the only value where '
        'adding 1 changes nothing. The ZP lattice order runs in the opposite direction '
        'to the usual number line, so this largest value is simultaneously the lattice bottom.',
    ]))
    E.append(sp(8))

    # ── The Abstraction Chain ────────────────────────────────────────────────
    E.append(Paragraph('The Abstraction Chain: Peeling Back the Layers', CS['h1']))
    E.append(cbody(
        'AFAStructure has three typeclass fields  - three things you must prove for '
        'your lattice before ZP-J\'s results apply. ZP-J shows that these three fields '
        'can themselves be derived from something simpler, in two steps:'))
    E.append(abstraction_chain_table())
    E.append(sp(6))
    E.append(cbody(
        'Reading the table bottom-up: AFAStructure requires the most direct commitment. '
        'AbstractSelfApp requires less  - its selfApp operation with fixed_bot and '
        'unique_fp together are sufficient to derive all three AFA fields as theorems. '
        'ValuationStructure requires even less  - four axioms about a depth measure, '
        'from which unique_fp becomes a theorem and AbstractSelfApp follows.'))
    E.append(cbody(
        'Each layer of the chain removes one more thing you have to assume. At the bottom '
        'of the chain, you are left with the valuation argument: scale increases depth by 1, '
        'so the only fixed point is the element with infinite depth.'))
    E.append(cbody(
        'There is one more layer underneath. Those four valuation axioms never use the join '
        'operation - so the full lattice was more structure than the argument needs. Keeping '
        'only the four axioms, with &#8869; as a plain element, gives a minimal common '
        'ancestor (called ValBridge in the Lean source). Both the abstract lattice track and '
        'the concrete 2-adic integers &#8484;&#8322; are instances of it, so one Lean proof '
        'establishes the unique-bottom result for both at once. This is what genuinely ties '
        'the abstract framework and the 2-adic model together: not an analogy between them, '
        'but a single theorem they both inherit.'))
    E.append(sp(8))

    # ── Two Concrete Models ──────────────────────────────────────────────────
    E.append(Paragraph('Three Concrete Models', CS['h1']))
    E.append(cbody(
        'The abstract chain is only useful if real types can actually run it. ZP-J '
        'demonstrates three concrete instances, taking different paths through the chain.'))
    E.append(cbody(
        '<b>&#8469;&#8734; (the extended naturals):</b> Take the natural numbers extended '
        'with a point at infinity  - the set {0, 1, 2, 3, &#8230;, &#8734;}. '
        'Join two elements by taking their minimum. The bottom element is &#8734; (since '
        'min(&#8734;, x) = x for all x). Scale is add-one: &#8734; + 1 = &#8734; '
        '(the infinity absorbs), and n + 1 &#8800; n for any finite n. '
        'The unique fixed point of "add 1" is &#8734;  - the bottom. '
        'This is the full ValuationStructure path.'))
    E.append(cbody(
        '<b>OntologicalStates ({null, exist}):</b> ZP-B\'s two-element state space is too '
        'small for the valuation argument  - there is no room to increase depth step by '
        'step in a two-element type. Instead it takes the direct path to AbstractSelfApp: '
        'the self-application operation maps every element to null. Null maps to itself '
        '(fixed point). Exist maps to null and is therefore not a fixed point. '
        'Null is the unique fixed point  - the AFA content follows immediately.'))
    E.append(cbody(
        '<b>&#8484;&#8322; (the 2-adic integers):</b> The number system from ZP-B, with '
        'scale = multiply-by-2 and depth = the 2-adic valuation v&#8322;. The bottom element '
        'is 0, whose valuation is &#8734;. This is the full valuation route again, but on a '
        'genuine number system rather than an abstract lattice  - in fact &#8484;&#8322; is a '
        'ring, not a lattice at all, which is what showed the lattice structure was more than '
        'the argument needs. The unique fixed point of multiply-by-2 is 0. Machine-checked in '
        'Lean, though (unlike the axiom-free core) it inherits the axiom of choice from '
        'Mathlib\'s p-adic library.'))
    E.append(sp(4))
    E.append(remember_box(
        'Three types, one destination. &#8469;&#8734; and the 2-adic integers &#8484;&#8322; '
        'take the full valuation route; OntologicalStates bypasses the valuation step and '
        'connects directly to AbstractSelfApp. All three deliver the same conclusion: the '
        'unique self-containing element is the bottom. '
        'The architecture is sound because each type takes the path the mathematics allows.'))
    E.append(sp(8))

    # ── Aczel's Open Question ────────────────────────────────────────────────
    E.append(Paragraph('Aczel\'s DC Question  - Closed for Self-Membership', CS['h1']))
    E.append(cbody(
        'In proving that J&#934; is the largest fixed point of a set-continuous operator, '
        'Aczel (Non-Well-Founded Sets, 1988, ch. 6, p. 77) used the axiom of Dependent Choice (DC) '
        'to construct an &#969;-chain. He noted explicitly: '
        '"I do not know if this use of the axiom of dependent choices was essential." '
        'Whether DC is essential to arguments of this type in general remains open.'))
    E.append(cbody(
        'ZP-J answers this question for the self-membership case: DC is not essential. '
        'The proof is one step, not a sequence. Once you know there is at most one '
        'self-containing element (quine_unique), you do not need to construct anything  - '
        'you identify. The self-containing set is {&#8869;}, and you know this immediately '
        'from the uniqueness field. The &#969;-chain that DC was needed to build is simply '
        'never constructed. (Whether DC can be eliminated for other fixed-point operators '
        'remains open  - see the scope note in the formal document.)'))
    E.append(sp(4))
    E.append(example_box('Plain language  - When you know there\'s only one answer', [
        'If you are asked to find the only even prime number, you do not need to search '
        'through a sequence of candidates. You know immediately: it is 2. The uniqueness '
        'of the answer eliminates the need for a construction. ZP-J\'s DC-free proof '
        'works the same way: quine_unique tells you there is exactly one self-containing '
        'element, so you identify it directly rather than constructing a chain.',
    ]))
    E.append(sp(4))
    E.append(cbody(
        'This applies specifically to the self-membership operator. Whether DC can be '
        'eliminated for all fixed-point constructions depends on whether uniqueness holds '
        'in each case  - an open question that Aczel\'s observation still stands for '
        'in the general setting.'))
    E.append(sp(8))

    # ── APG Decoration Uniqueness ────────────────────────────────────────────
    E.append(Paragraph('Graphs That Decorate Themselves', CS['h1']))
    E.append(cbody(
        'An Accessible Pointed Graph (APG) is a directed graph with a special root vertex '
        'from which every other vertex can be reached by following arrows. AFA proves '
        'that every APG has a unique valid "decoration"  - a way of '
        'labelling each vertex so that the label at each vertex is assembled from the labels '
        'of all its immediate successors. AFA itself proves existence plus uniqueness for all APGs '
        'using AFA\'s axioms directly.'))
    E.append(cbody(
        'ZP-J proves something different: a uniqueness-only result for abstract DecorationUniverses  - '
        'types carrying the ValuationStructure and a collect operation, without importing AFA axioms. '
        'The result: for any <b>finite</b> APG, any two valid decorations must agree at every vertex. '
        'Existence is not proved; the ZP-J result is a constraint, not a construction.'))
    E.append(cbody(
        'The proof follows the same two-direction logic as T-EXEC:'))
    E.append(cbody(
        '<b>Cyclic vertices:</b> If a vertex lies on a directed cycle of length k, '
        'then composing the decoration equation around the cycle gives d(v) = scale<sup>k</sup>(d(v)). '
        'The valuation argument forces d(v) = &#8869;: any other label would require '
        'depth(d(v)) = depth(d(v)) + k, which is impossible. So on cycles, '
        'any two decorations must both assign &#8869;. They agree trivially.'))
    E.append(cbody(
        '<b>Acyclic vertices:</b> Vertices with no cycle through them are handled by '
        'induction. If two decorations agree on all the children of a vertex, they must '
        'agree on the vertex itself  - because the label is assembled from the children\'s '
        'labels and the assembly rule is the same. The induction terminates because the '
        'set of reachable vertices strictly shrinks at each child.'))
    E.append(sp(4))
    E.append(remember_box(
        'decoration_unique is the ZP version of AFA\'s central uniqueness theorem. '
        'It does not construct a decoration or prove one exists  - it proves that '
        'any two valid decorations must be identical. This is the uniqueness half of AFA\'s '
        'decoration theorem, proved here for abstract DecorationUniverses without importing '
        'set-theoretic AFA axioms.'))
    E.append(sp(8))

    # ── Key Result Box ───────────────────────────────────────────────────────
    E.append(key_result_box(
        'Key Results  - ZP-J',
        'T-EXEC (axiom-free, Lean 4): IsQuineAtom(q) &#8596; q = &#8869;. '
        'The Quine atom, the order minimum, and the join identity are the same element. '
        'CC-1 (S&#8320; = &#8869;) is a derived theorem  - axiom-free in Lean 4. '
        'CC-2 (&#8869; = {&#8869;}) is proved within ZF+AFA: forced by T-EXEC, not assumed. '
        'DC-free: the self-containing set {&#8869;} is identified in one step, '
        'with no Dependent Choice. '
        'Abstraction chain: ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure  - '
        'each more specialized layer\'s results follow from the simpler layers beneath it. '
        'Concrete instances: &#8469;&#8734; satisfies the full ValuationStructure chain; '
        'OntologicalStates connects at the AbstractSelfApp level directly. '
        'decoration_unique: any two valid decorations of a finite APG agree. '
        'All stated results sorry-free in Lean 4 '
        '(decoration_unique proved via strong induction on reach cardinality; '
        'an auxiliary acyclic_decoration_unique in ZPJ_APG.lean is sorry\'d and commented out  - '
        'it is not used by decoration_unique). &#10003;'))
    E.append(sp(6))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
