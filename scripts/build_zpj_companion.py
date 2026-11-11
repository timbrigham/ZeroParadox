"""
Build ZP-J Illustrated Companion
Version 1.45 | November 2026
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle, Path
from reportlab.graphics import renderPDF

def quine_atom_diagram():
    """Diagram showing ⊥ ∈ ⊥ — the self-containing bottom element."""
    dw, dh = TW, 2.9 * inch  # 208.8 pts; content top ~192 (the braces), bottom ~10 (caption)
    d = Drawing(dw, dh)

    cx = dw / 2
    cy = 110  # fixed, not derived from dh; Q = {Q} label at cy-r_outer-18 = 20, caption at y = 10

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
    d.add(String(cx - 6, cy - 6, 'Q',
                 fontSize=16, fontName='DV-B', fillColor=WHITE))

    # Label: Q = {Q} (the AFA set; the lattice's occupant of the role is a separate theorem)
    d.add(String(cx - 28, cy - r_outer - 18, 'Q  =  {Q}',
                 fontSize=13, fontName='DV-B', fillColor=INDIGO))

    # Self-membership arrow
    ax, ay = cx, cy + r_inner + 2
    bx, by = cx, cy + r_outer - 4
    d.add(Line(ax, ay, bx, by, strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(bx - 5, by - 6, bx, by, strokeColor=INDIGO, strokeWidth=1.5))
    d.add(Line(bx + 5, by - 6, bx, by, strokeColor=INDIGO, strokeWidth=1.5))

    d.add(String(14, 10,
                 'The Quine atom (CC-2) in AFA: Q is its own sole member. '
                 'The outer ring is the set {Q}; the inner disk is Q as an element.',
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
    d.add(String(qx - 6, cy - 6, 'Q', fontSize=16, fontName='DV-B', fillColor=WHITE))
    loop = Path(strokeColor=INDIGO, strokeWidth=1.4, fillColor=None,
                strokeDashArray=[2.5, 2.5])
    loop.moveTo(qx + 18, cy)                       # exit the right edge
    loop.curveTo(qx + 55, cy, qx, cy + 50, qx, cy + 18)  # arc up and back into the top
    d.add(loop)
    # solid arrowhead at the top entry, pointing down into the ball
    d.add(Line(qx - 5, cy + 25, qx, cy + 18, strokeColor=INDIGO, strokeWidth=1.4))
    d.add(Line(qx + 5, cy + 25, qx, cy + 18, strokeColor=INDIGO, strokeWidth=1.4))
    d.add(String(qx - 42, cy - 42, 'Q = {Q}: the chain loops on itself',
                 fontSize=8, fontName='DV-I', fillColor=GREY_TEXT))
    return d


def three_way_table():
    """Three-way equivalence: Quine atom = bottom element = join identity."""
    hdr = [Paragraph('Language', CS['tbl_hdr']),
           Paragraph('What ⊥ satisfies', CS['tbl_hdr']),
           Paragraph('Plain meaning', CS['tbl_hdr'])]
    rows = [
        ['Membership host (the QuineAtomHost an AFAStructure on L builds)',
         'is the occupant of the Quine-atom role in that host, '
         'the role the set Q = {Q} plays in AFA set theory (quineAtomHost_quine_role_iff with '
         'afaStructure_isQuineAtomHost)',
         'In AFA the set Q = {Q} contains exactly one element: itself. AFA allows at most one set that is its own '
         'sole member (x = {x}); bare self-membership is not unique there (see the T-EXEC box above). '
         'The Lean requirement: QuineAtomHost, ZeroParadox/Settheory/QuineHost.lean &#167; VII'],
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
    t = Table(data, colWidths=[TW*0.22, TW*0.38, TW*0.40])
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
         'bot_self_mem and quine_unique as theorems; selfMem supplied as a definition (data)'],
        ['AFAStructure',
         'selfMem, bot_self_mem, quine_unique directly as typeclass fields',
         'T-EXEC, J1, and CC-1 in conditional form as proved theorems'],
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


VERSION = '1.45'
FIRST_RELEASED = 'April 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-J_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-J Companion  |  Self-Reference  |  ' + version_date())
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
          Paragraph('What the Quine Atom Means, and Why It Matters', CS['subtitle']),
          Paragraph('ZP Companion | The Quine Atom | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
          Paragraph(
              'This companion explains in plain language what the Quine atom (CC-2; in AFA set theory '
              'the set Q = {Q}) means, and the proof that whatever plays that role in a lattice '
              'is its unique bottom element. '
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
        'In AFA set theory the Quine atom is the set Q satisfying Q = {Q}. The framework treats the '
        'Quine atom (CC-2) as a ROLE: a point that steps to itself and to nothing else, here along '
        'membership. Each setting has its own occupant, proved there: Q in AFA set theory; none in '
        'Mathlib\'s sets, which obey Foundation (zfset_quine_role_unoccupied, '
        'ZeroParadox/Settheory/Wall.lean); and &#8869; in a lattice carrying the role '
        '(quineAtomHost_quine_role_iff, ZeroParadox/Settheory/QuineDichotomy.lean). No equation between '
        '&#8869; and Q is written, because it would compare an element of a lattice with a set. '
        'ZP-E argues, informally, that '
        'nothing external to &#8869; can execute &#8869;, so if &#8869; executes at all, the executor is '
        '&#8869; itself, and reads that as &#8869; occupying the Quine-atom role. That rules out an external executor, not an '
        'inert &#8869; (see ZP-E for the full three-path argument).'))
    E.append(cbody(
        'ZP-J formalises the structural part of that picture. The Quine atom becomes a ROLE, not a '
        'fixed value: the AFAStructure typeclass describes it, and its field bot_self_mem places '
        '&#8869; in it. ZP-J proves, in Lean 4 with no axioms, that in any join-semilattice carrying '
        'that typeclass, whatever fills the role  - its own sole member, and the only such '
        'element  - is the bottom element &#8869;; its later sections add a valuation argument, '
        'also machine-checked for the 2-adic integers, that derives the typeclass laws in '
        'carriers that have a depth measure. '
        'CC-2, the Quine atom, remains a commitment (ZP-A calls it a Forced Metatheoretic '
        'Commitment); at the lattice level it is read as that role, and T-EXEC identifies the role\'s occupant. In AFA set theory the set '
        'Q = {Q} exists and is unique, a consequence of the axiom (Aczel 1988, Example 1.3); adopting AFA '
        'for the set setting is the commitment, argued rather than chosen freely, and not a '
        'Lean theorem, and no equation between &#8869; and Q is claimed. CC-1 (S&#8320; = &#8869;) is restated, not forced: in any lattice carrying the '
        'typeclass, a state sequence starts at a Quine atom exactly when it starts at &#8869;, and on a '
        'lattice with a second point a valid sequence can start above &#8869;, at a point that is not a '
        'Quine atom, so the choice of starting point is expressed through the role rather than removed.'))
    E.append(cbody(
        'ZP-J extends the T-EXEC result in four directions: it identifies the set of '
        'self-containing elements as {&#8869;} without the axiom of choice; it derives the '
        'typeclass laws from stronger structures, ending in a valuation argument; it '
        'demonstrates the structure on two concrete types; and it proves '
        'decoration uniqueness and existence for every directed graph, finite or not, into abstract '
        'DecorationUniverses, with a separate graph-side proof of uniqueness for finite APGs.'))
    E.append(sp(4))

    # ── What Is a Quine Atom? ────────────────────────────────────────────────
    E.append(Paragraph('What Is a Quine Atom?', CS['h1']))
    E.append(cbody(
        'In ordinary set theory (ZF with the Foundation axiom), every set has a "rank"  - '
        'a measure of how deeply nested its membership is. A set like {{{&#8709;}}} has rank 3 '
        'because you have to unwrap three layers to reach the empty set. Importantly, no '
        'set under Foundation can be a member of itself: that would create an infinite '
        'descending chain x &#8715; x &#8715; x &#8715; &#8230; with no end.'))
    E.append(cbody(
        'Anti-Foundation (AFA) drops that prohibition. It allows non-well-founded sets  - '
        'sets that can be members of themselves. The simplest such object is the Quine atom: '
        'a set x satisfying x = {x}. It contains exactly one element: itself. Unwrapping it '
        'gives x again, not &#8709;. There is no bottom to the chain  - it loops back. '
        'AFA is an axiom saying every graph has exactly one decoration, and applied to a single '
        'self-loop it guarantees exactly one such set exists.'))
    E.append(quine_atom_diagram())
    E.append(ccaption(
        'The Quine atom (CC-2), pictured as a set in AFA set theory: Q is the sole member of itself. '
        'The outer ring is the set {Q} and the inner disk is Q as an element. '
        'They are the same set. In a lattice the role\'s only occupant is &#8869; (T-EXEC); no equation '
        'between &#8869; and Q is written.'))
    E.append(sp(6))
    E.append(quine_graph_diagram())
    E.append(ccaption(
        'A second way to see it - as a directed graph (an "accessible pointed graph", or APG, '
        'the structure Aczel\'s anti-foundation axiom decorates). Each arrow points from a set '
        'to one of its members. Ordinary sets are well-founded: following the arrows always ends, '
        'here at the empty set ∅. The Quine atom Q is the lone exception - its arrow loops straight '
        'back to itself. That self-loop is exactly Q = {Q}: a membership chain '
        'that never bottoms out.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy  - A mirror facing a mirror', [
        'Hold two mirrors facing each other. Each reflection contains the other mirror, '
        'which contains another reflection, which contains another mirror &#8230; infinitely. '
        'The image is self-referential: the full scene is visible inside itself at every '
        'level. The Quine atom Q = {Q} has this structure  - Q is inside '
        'itself, not as a smaller copy, but as the same object.',
    ]))
    E.append(sp(8))

    # ── T-EXEC ───────────────────────────────────────────────────────────────
    E.append(Paragraph('T-EXEC: The Quine Atom Is Uniquely &#8869;', CS['h1']))
    E.append(cbody(
        'The central theorem of ZP-J is T-EXEC (Executability of Self-Reference). It states:'))
    E.append(key_result_box(
        'Theorem T-EXEC',
        'In any ZP-A semilattice carrying the AFAStructure typeclass, an element q is a Quine atom '
        '(the structural encoding of q = {q}: q is its own sole member, and no other element is; '
        'bare self-membership is weaker, since under AFA the set 0* = {&#8709;, 0*} contains itself '
        'and is not the Quine atom) '
        'if and only if q = ⊥. '
        'The Quine atom property uniquely identifies the bottom element. '
        'Proved axiom-free in Lean 4: ZeroParadox.t_exec gives the direction Quine atom → ⊥, '
        'and ZeroParadox.t_exec_iff the equivalence.'))
    E.append(sp(6))
    E.append(cbody(
        '<b>Quine atom &#8594; &#8869;:</b> Suppose q is a Quine atom: q plays the selfMem role '
        '(its own sole member, x = {x}), and every element playing that role equals q. The bottom '
        'element &#8869; plays it by the typeclass field bot_self_mem. So &#8869; equals q.'))
    E.append(cbody(
        '<b>&#8869; &#8594; Quine atom:</b> &#8869; plays the selfMem role (bot_self_mem). '
        'Any other x playing it equals &#8869; by quine_unique. So &#8869; is the unique '
        'element in that role  - the Quine atom.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: T-EXEC does not say ⊥ is physically self-referential. It says that '
        'whatever plays the Quine-atom role in a lattice is the bottom element, and that the '
        'bottom element plays it. The two notions identify the same object.'))
    E.append(sp(8))

    # ── Three Languages, One Element of the Lattice ───────────────────────────
    E.append(Paragraph('Three Languages, One Element of the Lattice', CS['h1']))
    E.append(cbody(
        'T-EXEC establishes a three-way identification within one lattice: in a lattice L carrying '
        'AFAStructure, the Quine-atom predicate, the least element and the join identity pick out one '
        'element of L, &#8869; of L (t_exec_triple_iff with da2_bottom_characterization), described in three different mathematical '
        'languages:'))
    E.append(three_way_table())
    E.append(sp(4))
    E.append(cbody(
        'These are not three separate properties that happen to coincide. They are three '
        'descriptions of the same structural role. T-EXEC machine-checks that the three roles '
        'have one occupant (t_exec_triple_iff with da2_bottom_characterization), and quineAtomHost_quine_role_iff at '
        'afaStructure_isQuineAtomHost does so for the membership-host row; that row is the Lean chart whose AFA '
        'reading is the set Q = {Q}; that reading is not a Lean statement.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy  - Zero in arithmetic (partial)', [
        '0 in arithmetic wears more than one hat at once: it is the additive identity '
        '(x + 0 = x) and the smallest non-negative integer (0 ≤ n for all n ∈ ℕ). '
        'Those two line up cleanly with ⊥ as join identity and ⊥ as minimum. '
        'But arithmetic has no honest way to show the third hat - ⊥ as the Quine atom '
        '(the role the AFA set Q = {Q} plays, "zero inside zero"): ordinary numbers simply do not contain themselves. '
        'For that self-containing property the right pictures are the mirror-facing-a-mirror '
        'analogy and the directed graph above, not arithmetic.',
    ]))
    E.append(sp(8))

    # ── Two Assumptions, Revisited ───────────────────────────────────────────
    # ⚠ THE IMPLICATION USED TO RUN BACKWARDS HERE (editorial O-7, 2026-09-13, Tim: match the
    #   Lean). This section said the ZP-A axioms "force the bottom element to be self-containing".
    #   In SetTheoryAFA.lean the self-containment of bottom is the class FIELD bot_self_mem, an
    #   INPUT; t_exec consumes it and proves any Quine atom equals bottom.
    #   ⚠ ROUND 2 (editorial B-1): this section was the only one corrected, so the page contradicted
    #   itself. Every CC-2 site in this file now uses the corpus's settled reading, Tim's words: "Bot
    #   is a role not a fixed value" (SetTheoryAFA.lean's NO-GO gauge: "the class encodes the role").
    E.append(Paragraph('Two Assumptions, Revisited', CS['h1']))
    E.append(cbody(
        'Before ZP-J, the framework carried two Conditional Claims  - honest admissions '
        'that certain structural facts were assumed rather than derived. ZP-J restates both in '
        'terms of a role, and neither commitment disappears:'))
    E.append(cbody(
        '<b>CC-2 (the Quine atom):</b> In ZP-A, a Forced Metatheoretic Commitment with two '
        'halves: that any set theory hosting a self-membered bottom gives up Foundation is proved in '
        'Lean (wf_no_selfloop, ZeroParadox/Settheory/Wall.lean  - no well-founded relation admits a '
        'self-loop; the QuineHost-specific case is its corollary quineHost_not_wellFounded, and '
        'zfSet_no_quine_bottom is the ZFSet instance, both ZeroParadox/Settheory/QuineHost.lean), and '
        'that a unique Quine atom is the right requirement is argued. ZP-J reads '
        'its structural content as a ROLE, not a fixed value: the Quine-atom role, which the '
        'AFAStructure typeclass encodes, with its field bot_self_mem placing &#8869; in it. T-EXEC '
        'proves that whatever fills that role is &#8869;. In AFA set theory the equation Q = {Q} is '
        'itself a theorem, with exactly one solution (Aczel 1988, Example 1.3); what is not derived is '
        'the adoption of AFA for the set setting, which is the commitment. No equation between &#8869; '
        'and Q is written: each setting\'s occupant of the role is that setting\'s own theorem.'))
    E.append(cbody(
        '<b>CC-1 (S&#8320; = &#8869;):</b> ZP-J proves <i>cc1_derived</i> in Lean 4: if a '
        'state sequence starts at a Quine atom, it starts at &#8869;, because T-EXEC identifies '
        'the Quine atom with &#8869;. The converse holds too (t_exec_iff), so the two starting '
        'conditions are the same. What is proved is that equivalence; the choice to start there '
        'is restated, not forced, since on a lattice with a second point a valid sequence can start '
        'above &#8869;.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: the Quine atom here is a role, not a fixed value, and placing ⊥ in it is an '
        'input, not the output. T-EXEC takes that input as the field bot_self_mem (the abstraction chain below '
        'derives that field from the stronger AbstractSelfApp structure, through fixed_bot). What '
        'T-EXEC proves is the identification: any Quine atom, the element that is its own sole '
        'member and shares that with nothing else, is ⊥.'))
    E.append(sp(8))

    # ── The Valuation Argument ───────────────────────────────────────────────
    E.append(Paragraph('Why Only &#8869; Can Be Self-Applying', CS['h1']))
    E.append(cbody(
        'T-EXEC uses the AFA typeclass fields directly. But there is a deeper question: '
        '<i>why</i> is &#8869; the unique fixed point? In carriers that have a depth measure, the '
        'valuation argument answers this, and it is the insight behind ZP-J\'s abstraction chain.'))
    E.append(cbody(
        'Imagine every element carries a "depth"  - a value in the extended naturals '
        '{0, 1, 2, &#8230;, &#8734;} given by how many times you can descend through its '
        'structure before bottoming out. Ordinary elements bottom out '
        'in finitely many steps, so their depth is finite; &#8869; of the lattice never bottoms '
        'out  - its depth is &#8734;, the field val_bot (val &#8869; = &#8868;) of '
        'ValuationStructure. Applying scale  - the self-application '
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
        'instance uses the axiom of choice: Mathlib&#8217;s 2-adic integers carry it already, and the '
        'valuation used here adds a classical test for x = 0 of its own.'))
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
    E.append(Paragraph('The Abstraction Chain: Where the Laws Come From', CS['h1']))
    E.append(cbody(
        'AFAStructure has three typeclass fields, but they are not three things you must '
        'prove: `selfMem` is DATA  - a predicate you supply, saying which elements count as '
        'self-containing  - and the other two are laws an instance must prove. Every ZP-A '
        'semilattice can supply all three trivially (selfMem as equality with &#8869;), so '
        'carrying the class is not a test a lattice can fail. ZP-J shows that the two laws '
        'can themselves be derived from other structures, in two steps, with selfMem supplied '
        'by a definition:'))
    E.append(abstraction_chain_table())
    E.append(sp(6))
    E.append(cbody(
        'Reading the table top-down, each row yields the one below it: a ValuationStructure '
        'gives an AbstractSelfApp, and an AbstractSelfApp gives an AFAStructure, with the two '
        'AFA LAWS as theorems and selfMem supplied as a definition rather than proved. So the '
        'upper rows are the STRONGER assumptions, not the weaker ones. AFAStructure and '
        'AbstractSelfApp ask nothing of a lattice: every ZP-A semilattice carries both, using the '
        'map that sends everything to &#8869;. ValuationStructure asks the most: four laws about '
        'a depth measure, and a carrier with any element besides &#8869; must then be infinite '
        '(valuationStructure_forces_infinite), which is why the two-element OntologicalStates '
        'below cannot carry one.'))
    E.append(cbody(
        'What the upper rows buy is an explanation, not fewer assumptions. Where a carrier has a '
        'depth measure, the reason &#8869; is the only fixed point is the valuation argument: '
        'scale increases depth by 1, so the only fixed point is the element with infinite depth.'))
    E.append(cbody(
        'One more structure sits beside the chain rather than in it. Those four valuation axioms never use the join '
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
        'is 0, whose valuation is &#8734;. This runs the same valuation argument on a genuine '
        'number system, through ValBridge: the variant that keeps the four valuation axioms and '
        'drops the lattice, since no lattice on &#8484;&#8322; is registered in the corpus as of 2026-09-28. That '
        'the argument goes through without one is what showed the lattice structure was more than '
        'the argument needs. The unique fixed point of multiply-by-2 is 0. Machine-checked in '
        'Lean, though (unlike the axiom-free core) it uses the axiom of choice: Mathlib&#8217;s '
        '2-adic integers carry it already, and the valuation used here adds a classical test for '
        'x = 0 of its own.'))
    E.append(sp(4))
    E.append(remember_box(
        'Three types, three routes. &#8469;&#8734; takes the full valuation route; '
        'OntologicalStates bypasses the valuation step and connects directly to AbstractSelfApp; '
        'the 2-adic integers &#8484;&#8322; run the valuation argument through ValBridge. The '
        'first two reach the AFAStructure conclusion that the unique element in the selfMem role '
        '(its own sole member, x = {x}) is the bottom. For &#8484;&#8322; the registered model reaches its shadow: 0 is the only fixed point '
        'of multiply-by-2. The full route exists too, as an existence statement: '
        'ZeroParadox/Valuation/Scale.lean &#167; V proves &#8484;&#8322; admits a lattice carrying a '
        'valuation structure, though none is registered. '
        'The architecture is sound because each type takes the path the mathematics allows.'))
    E.append(sp(8))

    # ── Aczel's Open Question ────────────────────────────────────────────────
    E.append(Paragraph('Aczel\'s DC Question, and Why ZP-J Does Not Answer It', CS['h1']))
    E.append(cbody(
        'Aczel (Non-Well-Founded Sets, 1988, ch. 6, pp. 76-77) proved that J&#934; is the largest '
        'fixed point of a set-continuous operator. In one step of that proof he used the axiom of '
        'Dependent Choice (DC) to build an infinite sequence of sets, and noted: '
        '"I do not know if this use of the axiom of dependent choices was essential."'))
    E.append(cbody(
        'ZP-J proves something that looks similar and is not the same. In the lattice encoding, '
        'the set of self-containing elements is {&#8869;}, and the proof is one step: there is at '
        'most one self-containing element (quine_unique), and &#8869; is one (bot_self_mem). Lean '
        'reports that this uses no axiom of choice. That is a fact about a predicate on a lattice. '
        'Aczel\'s use of DC comes from building his fixed point out of sets inside set theory, and '
        'the lattice version never builds anything that way, so it never meets that step. It removes '
        'nothing from Aczel\'s proof, and ZP-J takes no position on whether his use of DC was '
        'essential.'))
    E.append(sp(4))
    E.append(example_box('Plain language  - When you know there\'s only one answer', [
        'If you are asked to find the only even prime number, you do not need to search '
        'through a sequence of candidates. You know immediately: it is 2. ZP-J identifies '
        '{&#8869;} the same way: quine_unique says there is at most one self-containing element '
        'and bot_self_mem says &#8869; is one, so nothing has to be constructed. That is also why '
        'the result says nothing about Aczel\'s proof, which has to construct its fixed point.',
    ]))
    E.append(sp(8))

    # ── APG Decoration Uniqueness ────────────────────────────────────────────
    E.append(Paragraph('Graphs That Decorate Themselves', CS['h1']))
    E.append(cbody(
        'An Accessible Pointed Graph (APG) is a directed graph with a special root vertex '
        'from which every other vertex can be reached by following arrows. AFA is an axiom, '
        'not a theorem: it asserts that every graph has exactly one valid "decoration"  - a way of '
        'labelling each vertex so that the label at each vertex is assembled from the labels '
        'of all its immediate successors. Existence and uniqueness are both part of what the '
        'axiom asserts (Aczel, Non-Well-Founded Sets, 1988, ch. 1 p. 6). Two theorems sit beside '
        'it: that every APG pictures a unique set follows from the axiom (p. 6), and for graphs with '
        'no infinite descending path the same uniqueness holds without it, by Corollary 1.1 (p. 5), '
        'which follows from Mostowski\'s Collapsing Lemma (p. 4).'))
    E.append(cbody(
        'ZP-J proves something different: analogues of both halves, for abstract DecorationUniverses  - '
        'types carrying the ValuationStructure and a collect operation, without importing AFA axioms. '
        'Uniqueness: on <b>any</b> directed graph, finite or infinite, any two valid decorations '
        'must agree at every vertex (decoration_unique_of_val). For finite APGs a separate, '
        'graph-side proof gives the same (decoration_unique). '
        'Existence: every directed graph has a valid decoration (exists_decoration), so it has '
        'exactly one (existsUnique_decoration).'))
    E.append(cbody(
        'The finite, graph-side proof follows the same two-direction logic as T-EXEC:'))
    E.append(cbody(
        '<b>Cyclic vertices:</b> Collecting a set of children always raises depth by at least 1, '
        'so a vertex is at least one step deeper than each of its children. Walk once around a '
        'cycle through v and that rule makes depth(d(v)) at least depth(d(v)) plus the length '
        'of the cycle  - a bound no finite depth can meet. So d(v) has infinite depth, which only '
        '&#8869; has. This is a bound, not an equation: nothing is assumed about how many '
        'children a vertex has. So on cycles, any two decorations must both assign &#8869;. '
        'They agree trivially.'))
    E.append(cbody(
        '<b>Acyclic vertices:</b> Vertices with no cycle through them are handled by '
        'induction. If two decorations agree on all the children of a vertex, they must '
        'agree on the vertex itself  - because the label is assembled from the children\'s '
        'labels and the assembly rule is the same. The induction terminates because the '
        'set of reachable vertices strictly shrinks at each child. Counting those vertices is '
        'what needs the graph to be finite.'))
    E.append(cbody(
        '<b>The other reading:</b> instead of sorting vertices into cyclic and acyclic, sort '
        'the labels by depth. A label of finite depth n is assembled from children whose labels '
        'have depth below n, so induction on n settles it; the only label of infinite depth is '
        '&#8869; of the decorating type. Think of a recursion that terminates on the size of its '
        'output rather than its input: nothing about the graph is counted, so the graph may be '
        'infinite (decoration_unique_of_val). This adapts a result Aczel sets '
        'as an exercise, that the Foundation axiom gives every graph at most one decoration (Aczel, '
        'Non-Well-Founded Sets, 1988, Exercise 2.1, p. 20), and the argument he indicates on p. 19 '
        'that equality between well-founded sets is uniquely determined, by transfinite induction on '
        'the membership relation. One difference is that this version admits the single '
        'label of infinite depth. The two readings are linked one way: under any valid decoration, a cyclic '
        'vertex gets infinite depth, and nothing is claimed in reverse.'))
    E.append(cbody(
        '<b>Existence:</b> build the decoration by recursion on the accessible vertices, those where every '
        'chain of children ends; that recursion is total, because it runs only where the chains end. '
        'There the label is computed from the '
        'children&#8217;s labels as usual; everywhere else no recursion applies and the label is &#8869; of the decorating type, the one label of infinite '
        'depth, which absorbs any collection it enters, like a strict function returning '
        'divergence. The construction never tests whether a vertex is accessible: it collects, for each '
        'child, the recursive value if the child is accessible or &#8869; of the decorating type if it is not, and the proof then '
        'inspects the depth of the result, which is plain data. One direction only: a vertex that '
        'is not accessible gets &#8869; of the decorating type (decoration_eq_bot_of_not_acc), but an accessible vertex '
        'with children of every finite height gets &#8869; of the decorating type too (fan_root_acc_and_eq_bot).'))
    E.append(sp(4))
    E.append(remember_box(
        'decoration_unique_of_val is the ZP analogue of the uniqueness clause of AFA, which is an axiom: '
        'any two valid decorations must be identical. exists_decoration is the analogue of the '
        'existence clause: a valid decoration exists. Together, existsUnique_decoration: exactly one. '
        'They are analogues of what AFA asserts, not its clauses themselves: they are proved for '
        'abstract DecorationUniverses over every graph, finite or not, without importing '
        'set-theoretic AFA axioms. decoration_unique is a finite form of uniqueness: a graph-side '
        'proof for finite APGs.'))
    E.append(sp(8))

    # ── Key Result Box ───────────────────────────────────────────────────────
    E.append(key_result_box(
        'Key Results  - ZP-J',
        'T-EXEC (axiom-free, Lean 4): IsQuineAtom(q) &#8596; q = &#8869;. '
        'In a lattice L carrying AFAStructure, the Quine-atom predicate, the order minimum and the '
        'join identity pick out one element of L (t_exec_triple_iff with da2_bottom_characterization). '
        'CC-1 (S&#8320; = &#8869;): a state sequence starts at a Quine atom exactly when it starts '
        'at &#8869; (cc1_derived with t_exec_iff)  - axiom-free in Lean 4; the starting point is '
        'restated through the role, not forced (on a lattice with a second point a valid sequence can start above &#8869;). '
        'CC-2 (the Quine atom): its structural content is a role, the Quine-atom role that AFAStructure encodes, and T-EXEC proves whatever fills that role is &#8869; (axiom-free); in AFA set theory Q = {Q} has exactly one solution, a theorem of that theory; adopting AFA for the set setting is the commitment, not a Lean theorem, and no equation between &#8869; and Q is written. '
        'Choice-free: the set of self-containing elements, {&#8869;}, is identified in one step '
        'with no axiom of choice; this does not address Aczel\'s question about Dependent Choice. '
        'Abstraction chain: ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure  - '
        'each arrow is an instance, running from the stronger structure to the weaker; the '
        'valuation layer explains the AFA laws where a carrier has a depth measure and does not '
        'reduce what must be assumed. '
        'Concrete instances: &#8469;&#8734; satisfies the full ValuationStructure chain; '
        'OntologicalStates connects at the AbstractSelfApp level directly. '
        'decoration_unique_of_val: any two valid decorations of any graph, finite or not, into a '
        'DecorationUniverse agree, with no finiteness hypothesis. '
        'decoration_unique: the same for a finite APG, by a graph-side proof. '
        'exists_decoration: every graph, finite or not, has a valid decoration into a '
        'DecorationUniverse, so it has exactly one (existsUnique_decoration). '
        'All stated results sorry-free in Lean 4 '
        '(decoration_unique proved via strong induction on reach cardinality, '
        'decoration_unique_of_val via strong induction on the depth of the decorating value; '
        'an auxiliary acyclic_decoration_unique in ZeroParadox/Settheory/APG.lean is sorry\'d and commented out  - '
        'it is not used by decoration_unique). &#10003;'))
    E.append(sp(6))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
