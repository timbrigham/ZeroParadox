"""
Build ZP-J Illustrated Companion
Version 1.32 | September 2026
v1.32: CC-1 STATUS SYNC with ZP-J v2.8. The abstraction-chain table cell 'T-EXEC, J1, CC-1 as proved theorems' collapsed CC-1 to its proved half; it now reads 'CC-1 in conditional form'. cc1_derived proves the conditional (a Quine-atom start is a bottom start) and t_exec_iff the converse; the starting-point choice is restated, not forced, since a valid state sequence can start above bottom. GATE ROUND 2 (ordinary, carried): the 'not forced' reason needs its scope - on a ONE-point lattice every sequence starts at bottom, so the countermodel is stated for a lattice with a second point, and the OntBridge.lean example now also shows the start is not a Quine atom. Editorial O1: p1 said CC-2 is 'no longer a freestanding modelling assumption'; it remains ZP-A's Forced Metatheoretic Commitment, read at the lattice level as the role. Key Results: T-EXEC proves whatever fills the role is bottom (t_exec), not 'only occupant'.
v1.31: COMPANION SYNC WITH ZP-J v2.7 (ZPJ-ITER, ZPJ-AFA-THM). "Graphs That Decorate Themselves" said composing the decoration equation around a cycle gives d(v) = scale^k(d(v)); cyclic_decoration_eq_bot never forms that equation, and it holds only at single-child vertices. The cyclic paragraph now gives the depth BOUND in plain language. AFA was called a theorem at four sites ("the unique decoration theorem", "AFA proves", "AFA's central uniqueness theorem", "AFA's decoration theorem"); Aczel ch. 1 p. 6 states it as an axiom over every graph, and each site now says so. Also, measured 2026-09-13: the Z_[2] model's Classical.choice was attributed to Mathlib alone at two sites; Mathlib's 2-adic structures carry it already in the statements (a type probe over Mathlib's multiplication reports it), and the valuation q2Val adds its own route through instDecidableEqZ2 := Classical.decEq, so both sites name both routes. And the opening said ZP-J proves T-EXEC "using the valuation structure of Q2 and the AFA uniqueness result"; t_exec is (hq.2 bot AFAStructure.bot_self_mem).symm and uses no valuation, which enters later as the explanation of uniqueness. EDITORIAL ROUND 1, Tim's call on the claim ("match the Lean"): the section formerly headed "Two Assumptions That Became Theorems" ran an implication BACKWARDS - it said the ZP-A axioms "force the bottom element to be self-containing", but bot_self_mem is a class FIELD that t_exec consumes; CC-2 now reads as an input plus an argued commitment and CC-1 as cc1_derived actually binds it (a state sequence starting at a Quine atom). Also: the T-EXEC box cited the one-direction t_exec for an iff and equated q = {q} with q in q; the Z_[2] model was presented as the full AFA route when it runs through ValBridge and reaches only the fixed-point shadow; and "these three fields can be derived" now names the two laws. EDITORIAL ROUND 2 (FAIL-BEDROCK): round 1 corrected the CC-2 section only, so four other sites still said the reverse ("a derived consequence of T-EXEC at the structural level", "T-EXEC proves the structural self-containment fixed point", "ZP-J makes that argument formal" after "which forces bottom = {bottom}", and "T-EXEC makes this explicit" under the set-membership row) - a half-applied fix turning a consistent error into a self-contradiction. Tim: "Bot is a role not a fixed value... I thought we had this worked out long ago?" It was: SetTheoryAFA.lean's NO-GO gauge says the class encodes the ROLE. Every CC-2 site now says that T-EXEC identifies the occupant of the Quine-atom role and the literal set fact is the ZF+AFA commitment. Also: T-EXEC was credited to the quine_unique field it does not use (it uses bot_self_mem and the uniqueness half of its own hypothesis); "bottom in bottom, i.e. bottom = {bottom}" reversed to the true direction; CC-1's hypothesis restored; decoration uniqueness scoped to DecorationUniverses; "the uniqueness half of what AFA asserts" is now an analogue. EDITORIAL ROUND 3 (FAIL-BEDROCK): the disclaimer and the opening still said bottom = {bottom} is "provably the unique bottom element" and "a derived theorem" two sentences before the corrected paragraph denied it. Restated to Wheel.lean's CC-2 convention: the set identity is stated only of AFA set theory, where it is well-typed, and the lattice-level statement is the role and its occupant. The Remember box and Key Results no longer call bottom both the role and the occupant; "the self-containing set is {bottom}" now says the SET OF self-containing elements is {bottom}; the Quine-atom diagram caption says the picture is of the AFA set. ADVERSARY ROUND 4 (FAIL-BEDROCK, D1): the section headed "Aczel's DC Question - Closed for Self-Membership" said "ZP-J answers this question for the self-membership case: DC is not essential". The Lean identifies the set of self-containing elements in a lattice with no Classical.choice; it defines no set-continuous operator and never meets the step of Aczel's proof that uses DC, so it answers nothing about that proof. This is the recurrence of the v1.20/v1.22 AR fixes, which had removed the Aczel-specific claim. Retitled and restated; the intro and Key Results no longer say "no Dependent Choice". TIM'S CALL ON ROUND 4 (carrier): CC-1 restated as an equivalence - given AFAStructure, starting at a Quine atom and starting at bottom are the same condition (cc1_derived, and t_exec_iff for the converse), so CC-1 is restated through the role, not forced; the opening, the Two Assumptions section and Key Results say so, and that section no longer says the claims "became theorems". ROUND-4 ORDINARY RESIDUE: the T-EXEC box no longer places a Lean theorem "in the ZF+AFA setting" and says ZP-A semilattice, not "any type"; the Remember box no longer says "properly grounded under AFA" (a condition no bottom fails); the abstraction-chain paragraph now says every ZP-A semilattice supplies the class trivially; CC-2 is ZP-A's argued metatheoretic commitment, not "previously a modelling commitment". ADVERSARY ROUND 5 (FAIL-BEDROCK, D1): the abstraction-chain section ran the implication BACKWARDS - "AbstractSelfApp requires less", "ValuationStructure requires even less", "Each layer of the chain removes one more thing you have to assume" - one sentence after saying every ZP-A semilattice carries AFAStructure trivially. toAbstractSelfApp and toAFAStructure are instances, so ValuationStructure is the STRONGEST assumption: every lattice carries AbstractSelfApp and AFAStructure, and valuationStructure_forces_infinite makes any nontrivial ValuationStructure carrier infinite, which is why OntologicalStates has none. The section now reads the table top-down with the stronger rows on top, says the stronger rows buy an explanation rather than fewer assumptions, and is retitled from "Peeling Back the Layers"; ValBridge (weaker than ValuationStructure, and not a route to AFAStructure) now sits "beside the chain" rather than "one more layer underneath"; the opening, the "four directions" summary, the valuation-argument lead-in and Key Results no longer say the chain reduces the commitments. TWO-POLE AUDIT RESTORATIONS (Tim: restore all): (L2) CC-2 is ZP-A's Forced Metatheoretic Commitment with a proved half (Foundation-freeness) and an argued half; (L3) the opening, Two Assumptions and Key Results no longer say the set equation is "not derived" - in AFA set theory Q = {Q} is a theorem with exactly one solution (Aczel Ex. 1.3) and the commitment is that the framework's bottom is that set; (L5) the Z_[2] remember box keeps that Scale.lean section V proves Z_[2] admits the full chain as an existence statement; (L8) the APG section keeps that "every APG pictures a unique set" follows from AFA and that Mostowski gives the well-founded case without it. Also the Quine atom is "its own sole member" rather than "self-containing" (0* = {empty, 0*} is self-membered and not the Quine atom, Aczel Ex. 1.5); the opening's "in that setting" for a Lean equivalence; and "a simpler input, fixed_bot" (pre-round-5 polarity; the structure carrying fixed_bot is the stronger one).
v1.30: FIELD-COUNT SLIP CORRECTED (companion sync with ZP-J v2.6). "AFAStructure has three typeclass fields - three things you must prove" counted the DATA field as an obligation: SetTheoryAFA.lean:80 declares `selfMem : L -> Prop`, a predicate you SUPPLY, alongside two laws you prove. Same slip the formal document carried for DecorationUniverse, where counting `collect` as a law is what made two laws read as three.
v1.29: rendered Lean citations synced to post-reorg files/namespaces the earlier passes missed (bare ZPx.lean / ZeroParadox.ZPx.* / ZPx.<decl>; SSOT-driven).
v1.28: rendered Lean-file citations synced to post-reorg basenames (namespace de-scar); docstring changelog above kept as the historical record.
v1.26: FMC precision (sweep Step 4) — Key Results box and the T-EXEC body line now split the proved structural fixed point (axiom-free) from the argued set-membership reading (the ZF+AFA setting itself).
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
         '&#8869; = {&#8869;}  (so &#8869; &#8712; &#8869;)',
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


VERSION = '1.32'
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
          Paragraph('What &#8869; = {&#8869;} Means, and Why It Matters', CS['subtitle']),
          Paragraph('ZP Companion | The Quine Atom | ' + version_line(FIRST_RELEASED, VERSION), CS['meta']),
          Paragraph(
              'This companion explains in plain language what &#8869; = {&#8869;} (the Quine atom '
              'of AFA set theory) means, and the proof that whatever plays that role in a lattice '
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
        'In AFA set theory the Quine atom is the set Q satisfying Q = {Q}, and the framework '
        'identifies the bottom element &#8869; with it. That identification is a statement about '
        'sets; a lattice cannot state it directly, because it would compare an element with a set '
        'of elements. ZP-E argues, informally, that '
        'nothing external to &#8869; can execute &#8869;, so &#8869; must execute itself, and '
        'reads that as &#8869; = {&#8869;} (see ZP-E for the full three-path argument).'))
    E.append(cbody(
        'ZP-J formalises the structural part of that picture. The Quine atom becomes a ROLE, not a '
        'fixed value: the AFAStructure typeclass describes it, and its field bot_self_mem places '
        '&#8869; in it. ZP-J proves, in Lean 4 with no axioms, that in any join-semilattice carrying '
        'that typeclass, whatever fills the role  - its own sole member, and the only such '
        'element  - is the bottom element &#8869;; its later sections add a valuation argument, '
        'also machine-checked for the 2-adic integers, that derives the typeclass laws in '
        'carriers that have a depth measure. '
        'CC-2 (&#8869; = {&#8869;}) remains a commitment (ZP-A calls it a Forced Metatheoretic '
        'Commitment); at the lattice level it is read as that role, and T-EXEC identifies the role\'s occupant. In AFA set theory the set '
        'Q = {Q} exists and is unique, a consequence of the axiom (Aczel 1988, Example 1.3); that the '
        'framework\'s &#8869; is that set is the commitment, argued rather than chosen freely, and not a '
        'Lean theorem. CC-1 (S&#8320; = &#8869;) is restated, not forced: in any lattice carrying the '
        'typeclass, a state sequence starts at a Quine atom exactly when it starts at &#8869;, and on a '
        'lattice with a second point a valid sequence can start above &#8869;, at a point that is not a '
        'Quine atom, so the choice of starting point is expressed through the role rather than removed.'))
    E.append(cbody(
        'ZP-J extends the T-EXEC result in four directions: it identifies the set of '
        'self-containing elements as {&#8869;} without the axiom of choice; it derives the '
        'typeclass laws from stronger structures, ending in a valuation argument; it '
        'demonstrates the structure on two concrete types; and it proves a '
        'decoration uniqueness theorem for finite APGs into abstract DecorationUniverses.'))
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
        'AFA is an axiom saying every graph has exactly one decoration, and applied to a single '
        'self-loop it guarantees exactly one such set exists.'))
    E.append(quine_atom_diagram())
    E.append(ccaption(
        'The Quine atom ⊥ = {⊥}, pictured as a set in AFA set theory: ⊥ is the sole member of itself. '
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
        '<b>Quine atom &#8594; &#8869;:</b> Suppose q is a Quine atom: q is self-containing, '
        'and every self-containing element equals q. The bottom element &#8869; is '
        'self-containing by the typeclass field bot_self_mem. So &#8869; equals q.'))
    E.append(cbody(
        '<b>&#8869; &#8594; Quine atom:</b> &#8869; is self-containing (bot_self_mem). '
        'Any other self-containing x equals &#8869; by quine_unique. So &#8869; is the unique '
        'self-containing element  - the Quine atom.'))
    E.append(sp(4))
    E.append(remember_box(
        'Remember: T-EXEC does not say ⊥ is physically self-referential. It says that '
        'whatever plays the Quine-atom role in a lattice is the bottom element, and that the '
        'bottom element plays it. The two notions identify the same object.'))
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
        'descriptions of the same structural role. T-EXEC machine-checks that the three roles '
        'have one occupant (t_exec_triple_iff); the set-theory row is the AFA reading of the '
        'first role, not a Lean statement.'))
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
        '<b>CC-2 (&#8869; = {&#8869;}):</b> In ZP-A, a Forced Metatheoretic Commitment with two '
        'halves: that any set theory hosting a self-membered bottom gives up Foundation is proved in '
        'Lean, and that a unique Quine atom is the right requirement is argued. ZP-J reads '
        'its structural content as a ROLE, not a fixed value: the Quine-atom role, which the '
        'AFAStructure typeclass encodes, with its field bot_self_mem placing &#8869; in it. T-EXEC '
        'proves that whatever fills that role is &#8869;. In AFA set theory the equation Q = {Q} is '
        'itself a theorem, with exactly one solution (Aczel 1988, Example 1.3); what is not derived is '
        'that the framework\'s &#8869; is that set, which is the commitment.'))
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
        'drops the lattice, since no lattice on &#8484;&#8322; is registered in the corpus. That '
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
        'first two reach the AFA conclusion that the unique self-containing element is the '
        'bottom. For &#8484;&#8322; the registered model reaches its shadow: 0 is the only fixed point '
        'of multiply-by-2. The full route exists too, as an existence statement: '
        'ZeroParadox/Valuation/Scale.lean &#167; V proves &#8484;&#8322; admits a lattice carrying this '
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
        'no infinite descending path the same uniqueness holds without it, by Mostowski\'s Collapsing '
        'Lemma (p. 4).'))
    E.append(cbody(
        'ZP-J proves something different: a uniqueness-only result for abstract DecorationUniverses  - '
        'types carrying the ValuationStructure and a collect operation, without importing AFA axioms. '
        'The result: for any <b>finite</b> APG, any two valid decorations must agree at every vertex. '
        'Existence is not proved; the ZP-J result is a constraint, not a construction.'))
    E.append(cbody(
        'The proof follows the same two-direction logic as T-EXEC:'))
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
        'set of reachable vertices strictly shrinks at each child.'))
    E.append(sp(4))
    E.append(remember_box(
        'decoration_unique is the ZP analogue of the uniqueness clause of AFA, which is an axiom. '
        'It does not construct a decoration or prove one exists  - it proves that '
        'any two valid decorations must be identical. It is an analogue of the uniqueness half '
        'of what AFA asserts, not that clause itself: it is proved for abstract '
        'DecorationUniverses over finite graphs, without importing set-theoretic AFA axioms.'))
    E.append(sp(8))

    # ── Key Result Box ───────────────────────────────────────────────────────
    E.append(key_result_box(
        'Key Results  - ZP-J',
        'T-EXEC (axiom-free, Lean 4): IsQuineAtom(q) &#8596; q = &#8869;. '
        'The Quine atom, the order minimum, and the join identity are the same element. '
        'CC-1 (S&#8320; = &#8869;): a state sequence starts at a Quine atom exactly when it starts '
        'at &#8869; (cc1_derived with t_exec_iff)  - axiom-free in Lean 4; the starting point is '
        'restated through the role, not forced (on a lattice with a second point a valid sequence can start above &#8869;). '
        'CC-2 (&#8869; = {&#8869;}): its structural content is a role, the Quine-atom role that AFAStructure encodes, and T-EXEC proves whatever fills that role is &#8869; (axiom-free); in AFA set theory Q = {Q} has exactly one solution, a theorem of that theory, and that the framework\'s &#8869; is that set is the commitment, not a Lean theorem. '
        'Choice-free: the set of self-containing elements, {&#8869;}, is identified in one step '
        'with no axiom of choice; this does not address Aczel\'s question about Dependent Choice. '
        'Abstraction chain: ValuationStructure &#8594; AbstractSelfApp &#8594; AFAStructure  - '
        'each arrow is an instance, running from the stronger structure to the weaker; the '
        'valuation layer explains the AFA laws where a carrier has a depth measure and does not '
        'reduce what must be assumed. '
        'Concrete instances: &#8469;&#8734; satisfies the full ValuationStructure chain; '
        'OntologicalStates connects at the AbstractSelfApp level directly. '
        'decoration_unique: any two valid decorations of a finite APG into a DecorationUniverse agree. '
        'All stated results sorry-free in Lean 4 '
        '(decoration_unique proved via strong induction on reach cardinality; '
        'an auxiliary acyclic_decoration_unique in APG.lean is sorry\'d and commented out  - '
        'it is not used by decoration_unique). &#10003;'))
    E.append(sp(6))

    print(f'Building: {out_path}')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')

if __name__ == '__main__':
    build()
