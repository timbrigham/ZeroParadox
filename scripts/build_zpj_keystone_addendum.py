"""
Zero Paradox — ZP-J Keystone Addendum: The Diagonal Fixed Point, the Lawvere Face-Split, and the Well-Foundedness Boundary
Version 1.1 | June 2026
v1.1: Honest-scope precision — the single-carrier "snap is one crossing" carries no NEW commitment; it rests on the framework's existing ⊥/ε₀ identification (MC-1 / OQ-E2), endpoints proved (floor non-wf via real ⊥, axiom-free).
v1.0: Initial release. A thin addendum recording two machine-checked investigations into the
      keystone (⊥ as the diagonal fixed point): (1) the Lawvere face-split (ZPJ_Lawvere.lean) —
      in Set no face is a Lawvere instance (Cantor), the computability face is genuine; and
      (2) the well-foundedness boundary (ZPJ_Boundary.lean, ZPJ_BoundaryBridge.lean) — the snap
      as a ν→μ crossing, relation-level + QPF bridge (best-effort; full Taylor coalgebraic = open).
      Honest fences carried throughout: probe/best-effort, modeling commitment, open Rung-C.
Reads after ZP-J Self-Reference.
"""

import os
from zp_utils import *

VERSION = '1.1'
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
        'valuation, and the initial object in category theory. That these faces are <i>one '
        'object</i> is a modeling commitment (MC-1), not a theorem. This addendum is a thin, '
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
            'Does not add: the unification itself (Lawvere/Yanofsky), nor a proof that the four '
            'faces are numerically one object &#8212; that is the MC-1 commitment, offered to '
            'these communities, not imposed on them.',
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
        'In Set: no face is a Lawvere instance (ZPJ_Lawvere.lean)',
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
        'In computability: a genuine instance (ZPJ_Lawvere.lean)',
        [
            'computability_face_fixedPoint &#8212; every <i>computable</i> self-map on codes '
            'has a fixed point. This wraps Mathlib\'s Nat.Partrec.Code.fixed_point (Rogers / '
            'Kleene\'s recursion theorem).',
            'The escape from the Cantor obstruction is computability: the fixed-point-free '
            'diagonal is not a computable endomap, so the witness can exist in the effective '
            'category. This is ZP-K\'s face (the Kleene quine).',
            'Footprint: [propext, Classical.choice, Quot.sound], inherited from Mathlib.',
        ]
    ))
    E.append(sp(4))
    E.append(body(
        '<b>The verdict, plainly:</b> the test is category-relative. In Set no face is a '
        'Lawvere instance; in the effective (computability) category the recursion theorem is '
        'a genuine one. The keystone therefore unifies a <i>shape</i> (the diagonal), not a '
        'single mechanism. The one-object identification remains the MC-1 commitment.'))
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
        'edge. <b>Taylor</b> (Well-founded coalgebras and recursion) proved that well-founded '
        '&#8658; recursive, and (Prop 111) that well-foundedness is <i>necessary</i> for '
        'recursion: one cannot recurse through &#8869;. <b>Ad&#225;mek&#8211;Milius&#8211;Moss</b> '
        '(On Well-Founded and Recursive Coalgebras, 2020, arXiv:1910.09401) give the modern '
        'characterizations (well-founded &#8660; recursive &#8660; a morphism to the initial '
        'algebra).'))
    E.append(body(
        'In that language the binary snap &#8869; &#8594; &#949;<sub>0</sub> is a crossing of '
        'the well-foundedness boundary: from the non-well-founded floor (&#8869;, the '
        'self-loop, where recursion cannot reach) to the well-founded ascent (the &#949;<sub>0</sub> '
        'ordinal tower, recursively generated). The Zero Paradox formalizes this at two levels.'))
    E.append(result_box(
        'Relation level (ZPJ_Boundary.lean)',
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
        'Categorical bridge (ZPJ_BoundaryBridge.lean)',
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
            'content is the two proven endpoints plus an identification &#8212; and that identification '
            'is the framework&#8217;s <i>existing</i> &#8869;/&#949;<sub>0</sub> identification (MC-1, and '
            'the &#949;<sub>0</sub> identity already open under OQ-E2), not a fresh one. The floor endpoint '
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
        '(well-founded &#8660; recursive) &#8212; is deliberately <i>not</i> formalized here. '
        'Mathlib currently lacks the required machinery: the next-time operator on subobject '
        'lattices, Pataraia\'s fixed-point theorem, and the recursion theorem for well-founded '
        'coalgebras. The depth result is therefore cited (Taylor; Ad&#225;mek&#8211;Milius&#8211;Moss), '
        'not re-proved. What is given here is the relation-level boundary and the QPF bridge: a '
        'best effort that names its own boundary.'))
    E.append(remark_box(
        'Open contribution point',
        [
            'Formalizing the missing machinery &#8212; the next-time operator, Pataraia\'s '
            'fixed-point theorem, and the General Recursion Theorem &#8212; would upgrade this '
            'best-effort bridge to the full coalgebraic statement, and would be a reusable Lean '
            'contribution independent of the Zero Paradox. Contributions are welcome, to this '
            'project and to Mathlib as a whole; the precise missing pieces are named above.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph(
        'Endnote: This document is an addendum to ZP-J Self-Reference and reads after it. ZP-J '
        'established the porthole (v<sub>2</sub>(&#8869;) = &#8734;, &#8869; = {&#8869;}); this '
        'addendum records two machine-checked probes into the keystone\'s structure &#8212; the '
        'Lawvere face-split and the well-foundedness boundary &#8212; each fenced as to exactly '
        'what it proves. Lean sources: ZPJ_Lawvere.lean, ZPJ_Boundary.lean, '
        'ZPJ_BoundaryBridge.lean, all sorry-free in Lean 4 as of June 2026.',
        S['endnote']))

    print(f'[build_zpj_keystone_addendum] Assembling document ({len(E)} elements)...')
    doc.build(E)
    print(f'Done. File size: {os.path.getsize(out_path) // 1024} KB')


if __name__ == '__main__':
    build()
