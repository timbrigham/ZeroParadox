"""
Build ZP-J Illustrated Companion
Version 1.8 | May 2026
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
Formal doc: ZP-J Self-Reference v1.1.
v1.0: Initial release. Covers T-EXEC (Quine atom = ⊥), the three-way equivalence,
and the closure of CC-1 and CC-2 as derived theorems rather than freestanding commitments.
"""

import os
from zp_utils import *
from reportlab.graphics.shapes import Drawing, Line, String, Rect, Circle
from reportlab.graphics import renderPDF

def quine_atom_diagram():
    """Diagram showing ⊥ ∈ ⊥ — the self-containing null state."""
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


def three_way_table():
    """Three-way equivalence: Quine atom = bottom element = join identity."""
    hdr = [Paragraph('Language', CS['tbl_hdr']),
           Paragraph('What ⊥ satisfies', CS['tbl_hdr']),
           Paragraph('Plain meaning', CS['tbl_hdr'])]
    rows = [
        ['Set theory (AFA)',
         '&#8869; &#8712; &#8869;  (i.e. &#8869; = {&#8869;})',
         '⊥ contains itself — self-referential, no external interpreter possible'],
        ['Order theory (ZP-A)',
         '&#8869; &#8804; x  for all x',
         '⊥ is below everything — the universal starting point'],
        ['Algebra (ZP-A A4)',
         '&#8869; &#8744; x = x  for all x',
         '⊥ contributes nothing to any join — the additive zero'],
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


VERSION = '1.8'


def build():
    out_path = os.path.join(PROJECT_ROOT,
                            'ZP-J_Illustrated_Companion.pdf')

    def footer_cb(canvas, doc):
        canvas.saveState(); canvas.setFont('DV-I', 8)
        canvas.setFillColor(colors.grey)
        canvas.drawCentredString(LETTER[0]/2, 0.6*inch,
            'Zero Paradox ZP-J Companion  |  Self-Reference  |  May 2026')
        canvas.restoreState()

    doc = SimpleDocTemplate(out_path, pagesize=LETTER,
                            leftMargin=LM, rightMargin=RM, topMargin=TM, bottomMargin=BM,
                            title='ZP-J Illustrated Companion', author='Zero Paradox Project',
                            onFirstPage=footer_cb, onLaterPages=footer_cb)
    E = []

    hdr_ts = TableStyle([('BACKGROUND',(0,0),(-1,-1),INDIGO),
                         ('TOPPADDING',(0,0),(-1,-1),8),('BOTTOMPADDING',(0,0),(-1,-1),8),
                         ('LEFTPADDING',(0,0),(-1,-1),10)])
    hdr = Table([[Paragraph('ZP-J Illustrated Companion',
                            ParagraphStyle('hdr',fontName='DV-B',fontSize=11,textColor=WHITE))]],
                colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E += [hdr, sp(6),
          Paragraph('The Self-Containing Null', CS['title']),
          Paragraph('What &#8869; = {&#8869;} Really Means &#8212; and Why It Matters', CS['subtitle']),
          Paragraph('ZP Companion | Version ' + VERSION + ' | May 2026', CS['meta']),
          Paragraph(
              'This companion explains the ideas in plain language. It is not the formal '
              'document &#8212; every claim here restates a result already proved in the technical '
              'document ZP-J Self-Reference. Consult that document for the authoritative '
              'mathematics.', CS['disc'])]

    # ── What Is ZP-J Doing? ──────────────────────────────────────────────────
    E.append(Paragraph('What Is ZP-J Doing?', CS['h1']))
    E.append(cbody(
        'ZP-E established that DA-1 &#8212; the claim that instantiating a configuration '
        'constitutes an execution event &#8212; rests on three converging arguments. '
        'The structural argument says: nothing external to &#8869; can execute &#8869;, '
        'therefore &#8869; must execute itself, which forces &#8869; = {&#8869;}. '
        'ZP-E cited this as a "Conditional Claim."'))
    E.append(cbody(
        'ZP-J makes that argument formal. It proves, in Lean 4 with no axioms beyond the '
        'standard mathematical infrastructure, that in any ZP-A semilattice with '
        'anti-foundation grounding, the unique self-containing set &#8212; the Quine atom &#8212; '
        'is provably the bottom element &#8869;. CC-2 (&#8869; = {&#8869;}) is no longer a '
        'freestanding modelling assumption &#8212; within ZF+AFA, it is a derived consequence '
        'of T-EXEC, not a choice. CC-1 (S&#8320; = &#8869;) is a derived consequence of '
        'the algebra with no additional axioms.'))
    E.append(cbody(
        'Version 2.0 of ZP-J extends the original result in four directions: it shows that '
        'the proof requires no appeal to the axiom of Dependent Choice; it reduces the '
        'typeclass commitments layer by layer down to a pure valuation argument; it '
        'demonstrates the structure on two concrete types; and it proves the full '
        'AFA decoration uniqueness theorem for finite graphs.'))
    E.append(sp(4))

    # ── What Is a Quine Atom? ────────────────────────────────────────────────
    E.append(Paragraph('What Is a Quine Atom?', CS['h1']))
    E.append(cbody(
        'In ordinary set theory (ZF with the Foundation axiom), every set has a "rank" &#8212; '
        'a measure of how deeply nested its membership is. A set like {{{&#8709;}}} has rank 3 '
        'because you have to unwrap three layers to reach the empty set. Importantly, no '
        'set under Foundation can be a member of itself: that would create an infinite '
        'descending chain &#8869; &#8715; &#8869; &#8715; &#8869; &#8715; &#8230; with no bottom.'))
    E.append(cbody(
        'Anti-Foundation (AFA) drops that prohibition. It allows non-well-founded sets &#8212; '
        'sets that can be members of themselves. The simplest such object is the Quine atom: '
        'a set x satisfying x = {x}. It contains exactly one element: itself. Unwrapping it '
        'gives x again, not &#8709;. There is no bottom to the chain &#8212; it loops back. '
        'Under AFA, the unique decoration theorem guarantees exactly one such set exists.'))
    E.append(quine_atom_diagram())
    E.append(ccaption(
        'The Quine atom ⊥ = {⊥}: ⊥ is the sole member of itself. '
        'The outer ring is the set {⊥} and the inner disk is ⊥ as an element. '
        'They are the same object.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy &#8212; A mirror facing a mirror', [
        'Hold two mirrors facing each other. Each reflection contains the other mirror, '
        'which contains another reflection, which contains another mirror &#8230; infinitely. '
        'The image is self-referential: the full scene is visible inside itself at every '
        'level. The Quine atom &#8869; = {&#8869;} has this structure &#8212; &#8869; is inside '
        'itself, not as a smaller copy, but as the same object.',
    ]))
    E.append(sp(8))

    # ── T-EXEC ───────────────────────────────────────────────────────────────
    E.append(Paragraph('T-EXEC: The Quine Atom Is Uniquely &#8869;', CS['h1']))
    E.append(cbody(
        'The central theorem of ZP-J is T-EXEC (Executability of Self-Reference). It states:'))
    E.append(key_result_box(
        'Theorem T-EXEC',
        'In any ZP-A semilattice with AFA grounding, an element q is a Quine atom '
        '(q = {q}, i.e. q ∈ q) if and only if q = ⊥. '
        'The Quine atom property uniquely identifies the bottom element. '
        'Proved axiom-free in Lean 4 (ZeroParadox.ZPJ.t_exec).'))
    E.append(sp(6))
    E.append(cbody(
        '<b>Quine atom &#8594; &#8869;:</b> Suppose q = {q}. AFA uniqueness says there is '
        'exactly one such set. The bottom element &#8869; satisfies bot_self_mem &#8212; '
        'it is self-containing by the typeclass field. Applying uniqueness: q = &#8869;.'))
    E.append(cbody(
        '<b>&#8869; &#8594; Quine atom:</b> &#8869; is self-containing (bot_self_mem). '
        'Any other self-containing x equals &#8869; by quine_unique. So &#8869; is the unique '
        'self-containing element &#8212; the Quine atom.'))
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
    E.append(example_box('Real-world analogy &#8212; Zero in arithmetic', [
        '0 is the additive identity (x + 0 = x), the smallest non-negative integer '
        '(0 ≤ n for all n ∈ ℕ), and the unique fixed point of negation (−0 = 0). '
        'These are three descriptions of the same object. '
        'T-EXEC is the Zero Paradox equivalent: ⊥ as Quine atom = ⊥ as minimum = ⊥ as '
        'join identity are three descriptions of the same bottom element.',
    ]))
    E.append(sp(8))

    # ── Two Assumptions That Became Theorems ─────────────────────────────────
    E.append(Paragraph('Two Assumptions That Became Theorems', CS['h1']))
    E.append(cbody(
        'Before ZP-J, the framework carried two Conditional Claims &#8212; honest admissions '
        'that certain structural facts were assumed rather than derived:'))
    E.append(cbody(
        '<b>CC-2 (&#8869; = {&#8869;}):</b> Previously a modelling commitment in ZP-A. '
        'ZP-J T-EXEC changes the nature of the claim. Within ZF+AFA, &#8869; = {&#8869;} is '
        'a proved consequence of the ZP-A axioms &#8212; forced, not assumed. The commitment '
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
        'Imagine every element of the lattice has a "depth" &#8212; a value in the extended '
        'naturals {0, 1, 2, &#8230;, &#8734;} measuring how far it is from &#8869;. '
        '&#8869; itself has depth &#8734;. Applying scale &#8212; the self-application '
        'operation &#8212; increases depth by exactly 1 at every non-&#8869; element. '
        'So if scale(x) = x, then depth(x) = depth(x) + 1. '
        'That equation has no finite solution. Only &#8869;, whose depth is already &#8734; '
        '(and &#8734; + 1 = &#8734; in the extended naturals), can satisfy it. '
        '&#8869; is the only fixed point.'))
    E.append(cbody(
        'The same argument appears in 2-adic arithmetic. Multiplication by 2 is the scale '
        'operation. The 2-adic valuation v&#8322;(x) measures how many times 2 divides x &#8212; '
        'a kind of depth. v&#8322;(2x) = v&#8322;(x) + 1 for any x &#8800; 0. So 2x = x '
        'forces v&#8322;(x) = v&#8322;(x) + 1 &#8212; impossible for finite valuation. '
        'Only 0, with v&#8322;(0) = &#8734;, satisfies 2 &#215; 0 = 0. '
        'The proof structure is the same in both cases; the formal bridge connecting '
        'the 2-adic type to the abstract ZPSemilattice framework is identified as future work.'))
    E.append(sp(4))
    E.append(example_box('Real-world analogy &#8212; The elevator that only goes up', [
        'Imagine an elevator that, when you press a button, moves one floor higher &#8212; '
        'unless you are already at the top floor, in which case it stays put. '
        'The top floor is the only "fixed point": pressing the button leaves you there. '
        'Every other floor gets nudged upward. In the &#8469;&#8734; model, &#8869; is the '
        'top floor (&#8734;, the largest extended natural) &#8212; the only value where '
        'adding 1 changes nothing. The ZP lattice order runs in the opposite direction '
        'to the usual number line, so this largest value is simultaneously the lattice bottom.',
    ]))
    E.append(sp(8))

    # ── The Abstraction Chain ────────────────────────────────────────────────
    E.append(Paragraph('The Abstraction Chain: Peeling Back the Layers', CS['h1']))
    E.append(cbody(
        'AFAStructure has three typeclass fields &#8212; three things you must prove for '
        'your lattice before ZP-J\'s results apply. ZP-J shows that these three fields '
        'can themselves be derived from something simpler, in two steps:'))
    E.append(abstraction_chain_table())
    E.append(sp(6))
    E.append(cbody(
        'Reading the table bottom-up: AFAStructure requires the most direct commitment. '
        'AbstractSelfApp requires less &#8212; its selfApp operation with fixed_bot and '
        'unique_fp together are sufficient to derive all three AFA fields as theorems. '
        'ValuationStructure requires even less &#8212; four axioms about a depth measure, '
        'from which unique_fp becomes a theorem and AbstractSelfApp follows.'))
    E.append(cbody(
        'Each layer of the chain removes one more thing you have to assume. At the bottom '
        'of the chain, you are left with the valuation argument: scale increases depth by 1, '
        'so the only fixed point is the element with infinite depth.'))
    E.append(sp(8))

    # ── Two Concrete Models ──────────────────────────────────────────────────
    E.append(Paragraph('Two Concrete Models', CS['h1']))
    E.append(cbody(
        'The abstract chain is only useful if real types can actually run it. ZP-J '
        'demonstrates two concrete instances, taking different paths through the chain.'))
    E.append(cbody(
        '<b>&#8469;&#8734; (the extended naturals):</b> Take the natural numbers extended '
        'with a point at infinity &#8212; the set {0, 1, 2, 3, &#8230;, &#8734;}. '
        'Join two elements by taking their minimum. The bottom element is &#8734; (since '
        'min(&#8734;, x) = x for all x). Scale is add-one: &#8734; + 1 = &#8734; '
        '(the infinity absorbs), and n + 1 &#8800; n for any finite n. '
        'The unique fixed point of "add 1" is &#8734; &#8212; the bottom. '
        'This is the full ValuationStructure path.'))
    E.append(cbody(
        '<b>OntologicalStates ({null, exist}):</b> ZP-B\'s two-element state space is too '
        'small for the valuation argument &#8212; there is no room to increase depth step by '
        'step in a two-element type. Instead it takes the direct path to AbstractSelfApp: '
        'the self-application operation maps every element to null. Null maps to itself '
        '(fixed point). Exist maps to null and is therefore not a fixed point. '
        'Null is the unique fixed point &#8212; the AFA content follows immediately.'))
    E.append(sp(4))
    E.append(remember_box(
        'Two paths, one destination. ℕ∞ takes the full valuation route. OntologicalStates '
        'bypasses the valuation step and connects directly to AbstractSelfApp. Both deliver '
        'the same conclusion: the unique self-containing element is the bottom. '
        'The architecture is sound because each type takes the path the mathematics allows.'))
    E.append(sp(8))

    # ── Aczel's Open Question ────────────────────────────────────────────────
    E.append(Paragraph('Aczel\'s Open Question &#8212; Closed', CS['h1']))
    E.append(cbody(
        'In 1988, Peter Aczel proved that the set of self-containing elements &#8212; '
        'J&#934; in his notation &#8212; is the largest pre-fixed-point of the self-membership '
        'operator. His proof used the axiom of Dependent Choice (DC) to build a sequence '
        'of approximations converging to the fixed point. He then noted: '
        '"I do not know if this use of the axiom of dependent choices was essential."'))
    E.append(cbody(
        'ZP-J answers his question for the self-membership case: DC is not essential. '
        'The proof is one step, not a sequence. Once you know there is at most one '
        'self-containing element (quine_unique), you do not need to construct anything &#8212; '
        'you identify. The self-containing set is {&#8869;}, and you know this immediately '
        'from the uniqueness field. The &#969;-chain that DC was needed to build is simply '
        'never constructed. (Whether DC can be eliminated for other fixed-point operators '
        'remains open &#8212; see the scope note in the formal document.)'))
    E.append(sp(4))
    E.append(example_box('Plain language &#8212; When you know there\'s only one answer', [
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
        'in each case &#8212; an open question that Aczel\'s observation still stands for '
        'in the general setting.'))
    E.append(sp(8))

    # ── APG Decoration Uniqueness ────────────────────────────────────────────
    E.append(Paragraph('Graphs That Decorate Themselves', CS['h1']))
    E.append(cbody(
        'An Accessible Pointed Graph (APG) is a directed graph with a special root vertex '
        'from which every other vertex can be reached by following arrows. AFA\'s central '
        'theorem states that every APG has a unique valid "decoration" &#8212; a way of '
        'labelling each vertex so that the label at each vertex is assembled from the labels '
        'of all its immediate successors.'))
    E.append(cbody(
        'ZP-J proves this for abstract DecorationUniverses &#8212; types that carry '
        'the ValuationStructure and a collect operation. The result: for any '
        '<b>finite</b> APG, any two valid decorations must agree at every vertex.'))
    E.append(cbody(
        'The proof follows the same two-direction logic as T-EXEC:'))
    E.append(cbody(
        '<b>Cyclic vertices:</b> If a vertex lies on a directed cycle of length k, '
        'then composing the decoration equation around the cycle gives d(v) = scale&#7503;(d(v)). '
        'The valuation argument forces d(v) = &#8869;: any other label would require '
        'depth(d(v)) = depth(d(v)) + k, which is impossible. So on cycles, '
        'any two decorations must both assign &#8869;. They agree trivially.'))
    E.append(cbody(
        '<b>Acyclic vertices:</b> Vertices with no cycle through them are handled by '
        'induction. If two decorations agree on all the children of a vertex, they must '
        'agree on the vertex itself &#8212; because the label is assembled from the children\'s '
        'labels and the assembly rule is the same. The induction terminates because the '
        'set of reachable vertices strictly shrinks at each child.'))
    E.append(sp(4))
    E.append(remember_box(
        'decoration_unique is the ZP version of AFA\'s central uniqueness theorem. '
        'It does not construct a decoration or prove one exists &#8212; it proves that '
        'any two valid decorations must be identical. This is the uniqueness half of AFA, '
        'proved for abstract DecorationUniverses without importing set-theoretic AFA axioms.'))
    E.append(sp(8))

    # ── Key Result Box ───────────────────────────────────────────────────────
    E.append(key_result_box(
        'Key Results &#8212; ZP-J',
        'T-EXEC (axiom-free, Lean 4): IsQuineAtom(q) &#8596; q = &#8869;. '
        'The Quine atom, the order minimum, and the join identity are the same element. '
        'CC-1 (S&#8320; = &#8869;) is a derived theorem &#8212; axiom-free in Lean 4. '
        'CC-2 (&#8869; = {&#8869;}) is proved within ZF+AFA: forced by T-EXEC, not assumed. '
        'DC-free: the self-containing set {&#8869;} is identified in one step, '
        'with no Dependent Choice. '
        'Abstraction chain: ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure &#8212; '
        'each layer derives the fields of the one above it. '
        'Concrete instances: &#8469;&#8734; satisfies the full ValuationStructure chain; '
        'OntologicalStates connects at the AbstractSelfApp level directly. '
        'decoration_unique: any two valid decorations of a finite APG agree. '
        'All results sorry-free in Lean 4. &#10003;'))
    E.append(sp(6))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
