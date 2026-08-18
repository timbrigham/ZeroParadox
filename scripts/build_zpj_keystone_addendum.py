"""
Zero Paradox — ZP-J Keystone Addendum: The Diagonal Fixed Point, the Lawvere Face-Split, and the Well-Foundedness Boundary
Version 1.5 | August 2026
v1.5: THE v1.4 FIX WAS PARTIAL, AND THAT MADE THINGS WORSE. v1.4 corrected the two sites carrying the literal strings "modeling commitment" and "offered", and missed a THIRD stating the same claim in different words - Section II's closing sentence, "The one-object identification remains the MC-1 commitment." The result was a document saying the identity was retired on page 1 and live on page 2. Before v1.4 it was uniformly stale, i.e. self-consistent; a partial fix to a self-consistent error manufactures a self-contradiction, which is worse than not fixing it. The cause was grepping the three forbidden PHRASES rather than the CLAIM. Section II now states what MC-1 does carry: family membership proved per domain, with the choice of criteria the design commitment. Found independently by both gates at FAIL-BEDROCK. A FOURTH site then turned up - one neither gate flagged - found only by sweeping the rendered text for the CLAIM (any sentence pairing an identity notion with a live-status verb) rather than for the phrases: Section III called MC-1 an "existing identification", and its "bottom/epsilon-zero identification" wording could be read as equating the two endpoints, which epsilon0_ne_bot forbids. Now stated as a role assignment, with the endpoints' distinctness named. Also: the endnote's Lean sources upgraded to full repository paths.
v1.3: CITATION SCOPE. Section III called the biconditional "the General Recursion Theorem". AMM's Thm 7.2 (p. 27) is the FORWARD direction only; their section 8 is titled "The Converse of the General Recursion Theorem". That converse always asks the ENDOFUNCTOR to preserve inverse images and then takes one of several routes - the CATEGORY having universally smooth monos with the functor carrying a pre-fixed point (Thm 8.1), or the category having a subobject classifier (Thm 8.6, Taylor's), or a third route for functors on vector spaces which have neither (Thm 8.12). The smooth-mono and subobject-classifier conditions are the CATEGORY's; preserving inverse images and carrying a pre-fixed point are the ENDOFUNCTOR's; and the routes are not exhaustive. Cor 8.2 lists five equivalent conditions, including the initial-algebra leg, under Thm 8.1's assumptions specifically. Taylor's necessity result is scoped as he scopes it - IN A TOPOS (Prop 111, p. 6), which he states rather than proves - and his forward half is Thm 36, p. 15. The "one cannot recurse through the bottom" reading is marked as this framework's gloss: Prop 111 names no bottom element. Also: the next-time operator is no longer listed as missing machinery, having been built in ZeroParadox/Category/NextTimeCategorical.lean; the remaining Mathlib absences are dated rather than asserted. All locators read from source.
v1.4: MC-1 framing brought to the ratified form. THREE rendered sites carried the retired identity; v1.4 fixed two of them and v1.5 the third. They called the cross-category identity a live "modeling commitment" and said it was "offered" - the identity was RETIRED AS ILL-TYPED (an equation across distinct categories is not a well-formed proposition), and CLAIMS.md already says so, so the PDF disagreed with the ledger. Now: family membership proved per domain, criteria a design principle, identity retired, members provably distinct. R2-4 (Taylor cited page-precisely with no year or venue) is NOT fixed here: the on-disk copy carries neither, and inventing them is worse than the gap. It stays open pending a verified bibliographic record.
v1.2: rendered Lean-file citations synced to post-reorg basenames (namespace de-scar); docstring changelog above kept as the historical record.
v1.1: Honest-scope precision — the single-carrier "snap is one crossing" carries no NEW commitment; it rests on the framework's existing ⊥/ε₀ identification (MC-1 / OQ-E2), endpoints proved (floor non-wf via real ⊥, axiom-free).
v1.0: Initial release. A thin addendum recording two machine-checked investigations into the
      keystone (⊥ as the diagonal fixed point): (1) the Lawvere face-split (ZPJ_Lawvere.lean) —
      in Set no face is a Lawvere instance (Cantor), the computability face is genuine; and
      (2) the well-foundedness boundary (ZPJ_Boundary.lean, ZPJ_BoundaryBridge.lean) — the snap
      as a ν→μ crossing, relation-level + QPF bridge (best-effort; full Taylor coalgebraic = open).
      Honest fences carried throughout: probe/best-effort, MC-1 family membership (identity
      retired as ill-typed), open Rung-C.
Reads after ZP-J Self-Reference.
"""

import os
from zp_utils import *

VERSION = '1.6'
FIRST_RELEASED = 'June 2026'

# ── fix() guard: route all bare Paragraph() text through Unicode-to-entity conversion ──
_Paragraph_orig = Paragraph
def Paragraph(text, style):
    return _Paragraph_orig(fix(text) if isinstance(text, str) else text, style)


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-J_Keystone_Addendum.pdf')
    print(f'[build_zpj_keystone_addendum] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-J Keystone Addendum',
                   'ZP-J Keystone Addendum', 'Version ' + VERSION)
    E = []

    # ── Header banner ──────────────────────────────────────────────────────────
    hdr_ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,-1), COMP_BLUE),
        ('TOPPADDING',    (0,0), (-1,-1), 8),
        ('BOTTOMPADDING', (0,0), (-1,-1), 8),
        ('LEFTPADDING',   (0,0), (-1,-1), 10),
    ])
    hdr = Table([[Paragraph('ZP-J Keystone Addendum',
                            ParagraphStyle('hdr', fontName='DV-B', fontSize=11,
                                           textColor=WHITE))]], colWidths=[TW])
    hdr.setStyle(hdr_ts)
    E.append(hdr)
    E.append(sp(6))

    print('[build_zpj_keystone_addendum] Building title block...')
    E += [
        sp(4),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-J Keystone Addendum', S['title']),
        Paragraph('The Diagonal Fixed Point: the Lawvere Face-Split and the Well-Foundedness Boundary',
                  S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        sp(10),
        hr(),
        sp(4),
    ]

    # ── Preamble ───────────────────────────────────────────────────────────────
    print('[build_zpj_keystone_addendum] Building preamble...')
    E.append(body(
        'The keystone of the Zero Paradox is that &#8869; is the same self-referential '
        '(diagonal) fixed point in every framework: the Quine atom &#8869; = {&#8869;} in set '
        'theory, the Kleene quine in computation, the point v<sub>2</sub>(0) = &#8734; in '
        'valuation, and the initial object in category theory. Their shared membership in that '
        'family (MC-1) is proved per domain; the choice of criteria is a design principle; and '
        'the claim that the faces are <i>numerically one object</i> is <b>retired as '
        'ill-typed</b> &#8212; an equation across distinct categories is not a well-formed '
        'proposition, and the members are provably distinct. This addendum is a thin, '
        'honest record of two machine-checked investigations into the structure of that '
        'keystone &#8212; both probe-level, both fenced as to exactly what they prove.'))
    E.append(body(
        'The first asks whether the keystone is a literal instance of <b>Lawvere\'s '
        'fixed-point theorem</b> (the recognized home of the diagonal family). The answer is '
        'face-dependent and machine-checked. The second gives the keystone\'s structural home '
        'in <b>well-founded coalgebra theory</b> (Taylor; Ad&#225;mek&#8211;Milius&#8211;Moss): '
        'the snap &#8869; &#8594; &#949;<sub>0</sub> as a crossing of the well-foundedness '
        'boundary. Neither investigation is claimed beyond what Lean verifies; the deeper '
        'category-theoretic result is cited, not re-proved.'))
    E.append(hr())

    # ── Section I: The keystone ────────────────────────────────────────────────
    print('[build_zpj_keystone_addendum] Building Section I...')
    E += [
        Paragraph('Section I: The Keystone and its Recognized Home', S['h1']),
        hr(),
    ]
    E.append(body(
        'The unification of self-referential fixed points across fields is not new with the '
        'Zero Paradox. <b>Lawvere</b> (Diagonal Arguments and Cartesian Closed Categories, '
        '1969) showed that Cantor\'s diagonal, Russell\'s paradox, G&#246;del\'s incompleteness '
        'lemma, and the recursion theorem are one move; <b>Yanofsky</b> (A Universal Approach '
        'to Self-Referential Paradoxes, Incompleteness and Fixed Points, Bull. Symbolic Logic '
        '9(3), 2003) restated this in plain set-and-function terms across logic and '
        'computation. Those faces are prior art, cited and not claimed.'))
    E.append(remark_box(
        'What the Zero Paradox adds (and what it does not)',
        [
            'Adds: candidate faces outside the classical scheme &#8212; the 2-adic valuation '
            'v<sub>2</sub>(0) = &#8734;, &#949;<sub>0</sub>, the wheel of fractions &#8212; '
            'each with a machine-checked axiom footprint; and the <i>location</i> claim, that '
            'the fixed point sits at the floor &#8869; (the G&#246;del inversion), a framing.',
            'Does not add: the unification itself (Lawvere/Yanofsky), nor any identification of '
            'the four faces as one object &#8212; that identity is <b>retired as ill-typed</b>, '
            'since an equation across distinct categories is not a well-formed proposition. What '
            'MC-1 carries is family membership, proved per domain, with the members provably '
            'distinct.',
        ]
    ))
    E.append(sp(6))

    # ── Section II: The Lawvere face-split ─────────────────────────────────────
    print('[build_zpj_keystone_addendum] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: The Lawvere Face-Split (machine-checked)', S['h1']),
        hr(),
    ]
    E.append(body(
        'Lawvere\'s theorem (Mathlib\'s Function.exists_fixed_point_of_surjective) says a '
        'point-surjection &#945; &#8594; (&#945; &#8594; &#946;) &#8212; the diagonal '
        'hypothesis &#8212; forces <i>every</i> endofunction of &#946; to have a fixed point. '
        'The keystone\'s fixed points are posited (the self-application has &#8869; as its '
        'fixed point); Lawvere\'s are <i>derived</i> from a surjection. So the question is '
        'whether each face supplies that surjection. The verdict is face-dependent.'))
    E.append(result_box(
        'In Set: no face is a Lawvere instance (Lawvere.lean)',
        [
            'For any nontrivial type, a Lawvere witness cannot exist: it would force every '
            'endofunction to have a fixed point, impossible once there are two distinct '
            'elements (Cantor).',
            'nontrivial_lattice_no_witness &#8212; the lattice / set-theoretic face: no witness '
            'on a nontrivial &#8869;-pointed lattice.',
            'q2_no_witness &#8212; the 2-adic face: no witness on &#8474;<sub>2</sub>.',
            'So in Set the keystone\'s &#8869; is a <i>posited</i> fixed point of one specific '
            'self-map, not a Lawvere-derived one. The "diagonal fixed point" name is an analogy '
            'at this face.',
            'fixedPoint_of_witness, no_witness_of_fixedPointFree: fully axiom-free.',
        ]
    ))
    E.append(sp(4))
    E.append(result_box(
        'In computability: a genuine instance (Lawvere.lean)',
        [
            'computability_face_fixedPoint &#8212; every <i>computable</i> self-map on codes '
            'has a fixed point <i>up to eval</i>: two codes computing the same function. This wraps '
            'Mathlib\'s Nat.Partrec.Code.fixed_point (Rogers / Kleene\'s recursion theorem).',
            'The qualifier is load-bearing. A literal fixed point is not on offer &#8212; c &#8614; '
            'pair(c, c) is total, computable, and returns its own input for no c. The escape from the '
            'Cantor obstruction is that eval lands in the partial functions, not in the codes, so the '
            'Set refutation never applied to it. This is ZP-K\'s face (the Kleene quine).',
            'Footprint: [propext, Classical.choice, Quot.sound], inherited from Mathlib.',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        '<b>The verdict, plainly:</b> the test is category-relative. In Set no face is a '
        'Lawvere instance; in the effective (computability) category the recursion theorem is '
        'a genuine one. The keystone therefore unifies a <i>shape</i> (the diagonal), not a '
        'single mechanism. What MC-1 carries is family membership, proved per domain, with the '
        'choice of criteria the design commitment.'))
    E.append(sp(6))

    # ── Section III: The well-foundedness boundary ─────────────────────────────
    print('[build_zpj_keystone_addendum] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Well-Foundedness Boundary', S['h1']),
        hr(),
    ]
    E.append(body(
        'The keystone\'s structural home is well-founded coalgebra theory. A relation is '
        'encoded as a powerset coalgebra; <b>well-founded</b> means no infinite descending '
        'chain &#8212; no cycle. The Quine atom &#8869; = {&#8869;} is exactly the minimal '
        '<i>non</i>-well-founded coalgebra: the self-loop &#8869; &#8712; &#8869;, the back '
        'edge. <b>Taylor</b> (Well-founded coalgebras and recursion) proves well-founded '
        '&#8658; recursive as his Recursion Theorem (Thm 36, p. 15), and states the converse '
        '<i>in a topos</i> &#8212; there well-foundedness is <i>necessary</i> for recursion '
        '(Prop 111, p. 6). <b>Ad&#225;mek&#8211;Milius&#8211;Moss</b> (On Well-Founded and '
        'Recursive Coalgebras, 2020, arXiv:1910.09401v2) prove the forward direction as the '
        '<b>General Recursion Theorem</b> (Thm 7.2, p. 27). Their converse (&#167;&#160;8) always '
        'asks the <i>endofunctor</i> to preserve inverse images, and then takes one of several '
        'routes: the <i>category</i> may have universally smooth monomorphisms with the functor '
        'carrying a pre-fixed point (Thm 8.1), or the category may have a subobject classifier '
        '(Thm 8.6, which is Taylor\'s); a third covers functors on vector spaces, which have '
        'neither (Thm 8.12). Under Thm 8.1\'s assumptions the characterizations coincide &#8212; '
        'well-founded &#8660; recursive &#8660; a morphism to the initial algebra (Cor 8.2). '
        'Reading the necessity direction as <i>one cannot recurse '
        'through</i> &#8869; is this framework\'s gloss, not Taylor\'s: Prop 111 names no '
        'bottom element.'))
    E.append(body(
        'In that language the binary snap &#8869; &#8594; &#949;<sub>0</sub> is a crossing of '
        'the well-foundedness boundary: from the non-well-founded floor (&#8869;, the '
        'self-loop, where recursion cannot reach) to the well-founded ascent (the &#949;<sub>0</sub> '
        'ordinal tower, recursively generated). The Zero Paradox formalizes this at two levels.'))
    E.append(result_box(
        'Relation level (Boundary.lean)',
        [
            'floor_not_wellFounded &#8212; the self-application floor is non-well-founded '
            '(&#8869; self-loops under selfApp). Fully axiom-free.',
            'ascent_wellFounded &#8212; the ordinal ascent is well-founded (Ordinal.lt_wf).',
            'snap_crossing &#8212; on a single carrier, the floor is the <i>sole</i> '
            'non-accessible point; every post-snap state is accessible. The snap exits the '
            'unique non-well-founded point into the well-founded ascent.',
        ]
    ))
    E.append(sp(4))
    E.append(result_box(
        'Categorical bridge (BoundaryBridge.lean)',
        [
            'snap_boundary_two_registers &#8212; the crossing witnessed in two registers at '
            'once: the relation/carrier level above, and ZP-P\'s categorical &#956;/&#957; '
            'fork (categorical_fork_strict: the initial algebra empty, the final coalgebra '
            'inhabited &#8212; the self-referential element lives in &#957;, not &#956;).',
        ]
    ))
    E.append(sp(4))
    E.append(remark_box(
        'Honest scope &#8212; what is proved, and what is committed',
        [
            'Proved: the relation-level boundary and the QPF &#956;/&#957; bridge above '
            '(floor_not_wellFounded is axiom-free; the rest carry Classical.choice from '
            'Mathlib\'s ordinal and QPF machinery).',
            'No new commitment: that the snap <i>is</i> this crossing is a faithful model whose '
            'content is the two proven endpoints, plus the reading of those endpoints as ZP\'s own '
            '&#8869; and &#949;<sub>0</sub> respectively &#8212; a role assignment the framework '
            'already carries (MC-1 family membership; the &#949;<sub>0</sub> type bridge open under '
            'OQ-E2), not a fresh one. The two endpoints stay distinct: '
            '&#949;<sub>0</sub> &#8800; &#8869; (epsilon0_ne_bot). The floor endpoint '
            'is tied to the real &#8869; of ZP (floor_not_wellFounded, axiom-free); the single-carrier '
            'Phase is the illustrative toy model, where non-well-foundedness localizes at the floor by '
            'construction.',
        ]
    ))
    E.append(sp(6))

    # ── Section IV: Scope, openness, open contribution point ───────────────────
    print('[build_zpj_keystone_addendum] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: What Is Not Formalized (and an Open Invitation)', S['h1']),
        hr(),
    ]
    E.append(body(
        'The <b>full</b> Taylor coalgebraic statement &#8212; &#8869; as a non-well-founded '
        '<i>coalgebra</i> in the broken-pullback sense, with the General Recursion Theorem '
        '<i>and its converse</i> &#8212; is deliberately <i>not</i> formalized here. Searched '
        'as of August 2026, the pinned Mathlib carries neither Pataraia\'s fixed-point theorem '
        'nor a recursion theorem for well-founded coalgebras; the <b>next-time operator</b> on '
        'subobject lattices is no longer missing, having since been built in this project '
        '(ZeroParadox/Category/NextTimeCategorical.lean), though it is not upstreamed. The '
        'depth result is '
        'therefore cited (Taylor; Ad&#225;mek&#8211;Milius&#8211;Moss), not re-proved. What is '
        'given here is the relation-level boundary and the QPF bridge: a best effort that names '
        'its own boundary.'))
    E.append(remark_box(
        'Open contribution point',
        [
            'Formalizing the machinery still missing &#8212; Pataraia\'s fixed-point theorem '
            'and the General Recursion Theorem &#8212; would upgrade this best-effort bridge to '
            'the full coalgebraic statement, and would be a reusable Lean contribution '
            'independent of the Zero Paradox. Upstreaming the next-time operator, already built '
            'here, is a third. Contributions are welcome, to this project and to Mathlib as a '
            'whole; the precise missing pieces are named above.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This document is an addendum to ZP-J Self-Reference and reads after it. ZP-J '
        'established the porthole (v<sub>2</sub>(&#8869;) = &#8734;, &#8869; = {&#8869;}); this '
        'addendum records two machine-checked probes into the keystone\'s structure &#8212; the '
        'Lawvere face-split and the well-foundedness boundary &#8212; each fenced as to exactly '
        'what it proves. Lean sources: ZeroParadox/Category/Lawvere.lean, '
        'ZeroParadox/Multihomed/Boundary.lean, ZeroParadox/Multihomed/BoundaryBridge.lean, '
        'all sorry-free in Lean 4 as of June 2026.',
        S['endnote']))

    print(f'[build_zpj_keystone_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
