"""
Build ZP-F: The Counterexamples (v1.18)
"""

import os
from zp_utils import *

VERSION = '1.18'
FIRST_RELEASED = 'April 2026'

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-F_The_Counterexamples.pdf')
    doc = make_doc(out_path, 'ZP-F: The Counterexamples', 'ZP-F', 'Version ' + VERSION)
    E = []

    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-F: The Counterexamples', S['subtitle']),
          Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
          sp(10),
          body('This document is self-contained within ordered field theory. No p-adic '
               'topology, no information theory, and no Hilbert space machinery is required. '
               'All results follow from the axioms of a linearly ordered field alone.'),
          body('<i>Illustrated Companion: A paired ZP-F Illustrated Companion provides '
               'plain-language explanation and motivation for the results here. '
               'Examples and intuitions are kept separate from the formal layers '
               'to distinguish illustrative material from proofs.</i>'),
          sp()]

    # ── I. Purpose and Scope ──────────────────────────────────────────────────
    E.append(Paragraph('I. Purpose and Scope', S['h1']))
    E.append(body(
        'The Zero Paradox framework requires a metric space in which a minimal first '
        'departure from &#8869; has a structurally forced SHAPE — the Binary Snap. '
        'What is derived is that shape, not that the departure is taken: a join-semilattice in '
        'which T-SNAP holds and nothing moves is exhibited in the Lean source '
        '(tsnap_holds_but_nothing_moves). '
        'This document establishes the negative result: no linearly ordered field can '
        'serve as that substrate. The real numbers &#8477; are the canonical and most '
        'familiar instance; the theorem applies to any field carrying a compatible '
        'linear order.'))
    E.append(body(
        'The blocking mechanism is elementary: in any such field, for any positive '
        'element &#949;, the element &#949;/2 exists, is positive, and is strictly '
        'smaller. There is no floor. The Binary Snap requires a floor. Therefore '
        'the snap is structurally impossible in any linearly ordered field.'))
    E.append(body(
        'This result contextualises the choice of Q&#8322; in ZP-B. Among all completions '
        'of &#8474;, Ostrowski\'s theorem identifies exactly two kinds: Archimedean completions '
        '(&#8477;, a densely ordered field, so no element has a first step) and '
        'non-Archimedean completions (&#8474;<sub>p</sub>, where v<sub>p</sub>(0) = +&#8734; while '
        'every nonzero element has a finite valuation). Q&#8322; is the non-Archimedean completion at p&#160;=&#160;2, '
        'the prime fixed by ZP-B Theorem T0 from binary existence (AX-B1) together with the minimality '
        'principle MP-1, a design commitment (its arithmetic steps: t0_no_prime_below_two, t0_two_is_prime, '
        't0_redundancy in ZeroParadox/Valuation/Padic.lean; MP-1 is stated in ZP-B\'s prose, not as a '
        'Lean hypothesis). '
        'In both kinds zero is a metric limit of nonzero elements (for Q&#8322;, '
        'floor_reach_separates_mu_nu), so being a limit point does not separate them. The '
        'topology does: Q&#8322; is totally disconnected (ZP-B, t5_totallyDisconnected), while '
        '&#8477; is connected (place_topological_signature), so not totally disconnected '
        '(real_no_snap). The order separates '
        'them globally, not at zero: at 0 neither has a first step (&#8477; in its field order, '
        'Q&#8322; in its norm preorder), and globally &#8477; is '
        'densely ordered (axb1_fails_everywhere_iff_dense), in its norm preorder as in its field '
        'order, while Q&#8322;\'s norm preorder is not dense (the &#167; ROLE examples in '
        'ZeroParadox/BottomCannotBe.lean). '
        'That zero has valuation +&#8734; is set by definition, not produced by the completion: '
        'Mathlib\'s Padic.addValuationDef assigns &#8868; to 0 by an explicit case. What holds in '
        'Q&#8322; is that only 0 has infinite valuation (padic_addVal_eq_top_iff).'))
    E.append(sp(4))

    # ── II. The General Result ────────────────────────────────────────────────
    E.append(Paragraph('II. The General Result', S['h1']))
    E.append(body(
        'The following results hold for any type F carrying a field structure, a '
        'linear order, and the IsStrictOrderedRing property — the standard Mathlib '
        'replacement for the deprecated LinearOrderedField typeclass (deprecated '
        'October 2025). All proofs are machine-verified in Lean 4.'))
    E.append(sp(4))

    E.append(label_box('Theorem F-DENSITY', [
        '&#8704; &#949; : F,  0 < &#949;  &#8594;  0 < &#949;/2  &#8743;  &#949;/2 < &#949;',
        'For any positive element &#949; in a linearly ordered field F, the element '
        '&#949;/2 is also positive and strictly smaller than &#949;.',
        'Proof: half_pos gives 0 < &#949;/2; half_lt_self gives &#949;/2 < &#949;. '
        'Both follow from the ordered field axioms. Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Theorem F-NO-MIN', [
        '&#172;&#8707; &#949; : F,  0 < &#949;  &#8743;  &#8704; &#948; : F,  0 < &#948;  &#8594;  &#949; &#8804; &#948;',
        'No linearly ordered field has a minimal positive element.',
        'Proof: Suppose such &#949; exists. By F-DENSITY, 0 < &#949;/2 < &#949;. '
        'Then &#949; &#8804; &#949;/2 (by minimality) contradicts &#949;/2 < &#949;. '
        'Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Theorem F-SNAP-BLOCKED', [
        '&#8704; &#949;&#8320; : F,  0 < &#949;&#8320;  &#8594;  &#8707; &#948; : F,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'Any candidate first step &#949;&#8320; > 0 from 0 in a linearly ordered field '
        'is blocked: &#949;&#8320;/2 is a smaller positive element, so &#949;&#8320; '
        'cannot be a genuine first step.',
        'Proof: Take &#948; = &#949;&#8320;/2. F-DENSITY gives 0 < &#948; < &#949;&#8320;. '
        'Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Theorem F-SNAP-IMPOSSIBLE', [
        '&#172;&#8707; &#949;&#8320; : F,  0 < &#949;&#8320;  &#8743;  &#172;&#8707; &#948; : F,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'The Binary Snap cannot occur in any linearly ordered field.',
        'A snap requires a minimal first departure from 0 with nothing below it. '
        'F-SNAP-BLOCKED shows such a floor never exists in a linearly ordered field.',
        'Proof: Direct from F-SNAP-BLOCKED. Status: DERIVED. &#10003;',
    ]))
    E.append(sp(4))

    # ── III. The Real Numbers — Canonical Instance ────────────────────────────
    E.append(Paragraph('III. The Real Numbers — Canonical Instance', S['h1']))
    E.append(body(
        'The following are corollaries of the general results above, instantiated '
        'at F = &#8477;. They are stated explicitly because &#8477; is the most '
        'familiar and intuitive case, and because the ZP-F companion document is '
        'written around &#8477; as its primary example.'))
    E.append(sp(4))

    E.append(label_box('Corollary R-DENSITY', [
        '&#8704; &#949; : &#8477;,  0 < &#949;  &#8594;  0 < &#949;/2  &#8743;  &#949;/2 < &#949;',
        'Density at zero for &#8477;. Follows from F-DENSITY at F = &#8477;. '
        'Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Corollary R-NO-MIN', [
        '&#172;&#8707; &#949; : &#8477;,  0 < &#949;  &#8743;  &#8704; &#948; : &#8477;,  0 < &#948;  &#8594;  &#949; &#8804; &#948;',
        '&#8477; has no minimal positive element. Follows from F-NO-MIN at F = &#8477;. '
        'Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Corollary R-SNAP-BLOCKED', [
        '&#8704; &#949;&#8320; : &#8477;,  0 < &#949;&#8320;  &#8594;  &#8707; &#948; : &#8477;,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'Any candidate first step in &#8477; can be halved. '
        'Follows from F-SNAP-BLOCKED at F = &#8477;. Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    E.append(label_box('Corollary R-SNAP-IMPOSSIBLE', [
        '&#172;&#8707; &#949;&#8320; : &#8477;,  0 < &#949;&#8320;  &#8743;  &#172;&#8707; &#948; : &#8477;,  0 < &#948;  &#8743;  &#948; < &#949;&#8320;',
        'The Binary Snap cannot occur in &#8477;. '
        'Follows from F-SNAP-IMPOSSIBLE at F = &#8477;. Status: DERIVED (corollary). &#10003;',
    ]))
    E.append(sp(4))

    # ── IV. Axiom Profile ────────────────────────────────────────────────────
    E.append(Paragraph('IV. Axiom Profile', S['h1']))
    E.append(body(
        'All eight results (F-DENSITY, F-NO-MIN, F-SNAP-BLOCKED, F-SNAP-IMPOSSIBLE '
        'and their &#8477; corollaries) verify under #print axioms with the profile: '
        'propext, Classical.choice, Quot.sound. This is the standard profile for '
        'Mathlib field and order results. No snap-specific axioms are introduced.'))
    E.append(sp(4))

    # ── V. Relationship to the Framework ─────────────────────────────────────
    E.append(Paragraph('V. Relationship to the Framework', S['h1']))
    E.append(body(
        'ZP-F is self-contained and does not feed formally into any other layer. '
        'It is the negative complement to ZP-B: where ZP-B establishes that Q&#8322; '
        'removes the topological obstruction to the snap (its 2-adic topology is totally '
        'disconnected, t5_totallyDisconnected, with clopen balls), ZP-F establishes that &#8477; — and any linearly ordered field — '
        'cannot host it. Neither supplies the first step AX-B1 commits to, a cover of &#8869; on '
        'the state carrier, the set of states a run S moves through, ordered as in ZP-A '
        '(HasFirstStep). t_snap_given_cover assumes the run\'s first step is a cover (hcov); '
        'with CC-1, the commitment that the run starts at &#8869; (S 0 = &#8869;), that step is '
        'a cover of &#8869;. MachinePhase meets the commitment: its state c&#8321; covers its '
        '&#8869;, c&#8320;.'))
    E.append(body(
        'The dependency order of the framework places ZP-F as independent:'))
    E.append(data_table(
        ['Layer', 'Role', 'Dependency'],
        [['ZP-B', 'p-Adic topology — Q&#8322; removes the topological obstruction', 'ZP-A'],
         ['ZP-F', 'Counterexample — &#8477; and ordered fields cannot host the snap', 'None (self-contained)'],
         ['ZP-G', 'Category theory', 'Self-contained; ZP-E conceptually']],
        [0.8*inch, 3.5*inch, 2.2*inch]
    ))
    E.append(sp(4))

    # ── VI. A Philosophical Note: The Wrong Setting ───────────────────────────
    E.append(Paragraph('VI. A Philosophical Note: The Wrong Setting', S['h1']))
    E.append(body(
        'The real numbers are the most natural and familiar number line precisely because '
        'they fill every gap. Density — the property established in F-DENSITY: for any '
        '&#949; > 0 there exists &#948; with 0 < &#948; < &#949; — is not a deficiency in '
        '&#8477;; it is one of &#8477;\'s defining virtues. The counterexample above shows '
        'that this virtue is exactly what disqualifies &#8477; as a host for the Binary Snap. '
        'The exclusion is not a matter of degree: density follows from the ordered field axioms, '
        'so every linearly ordered field is ruled out by exactly the same argument. '
        'Familiarity here misleads: the setting that feels most natural '
        'for foundational mathematics is precisely the wrong one.'))
    E.append(body(
        'The exclusion of &#8477; is not an isolated fact about one number system. '
        'F-SNAP-IMPOSSIBLE applies to any linearly ordered field. By Ostrowski\'s theorem, '
        'every completion of &#8474; falls into exactly one of two classes: Archimedean '
        '(including &#8477;) or non-Archimedean (the p-adic fields &#8474;<sub>p</sub>). '
        'The theorems of this document eliminate the entire Archimedean class. '
        'What remains is the non-Archimedean class, every &#8474;<sub>p</sub>, not Q&#8322; alone. '
        'Among these, ZP-B Theorem T0 fixes p&#160;=&#160;2 from binary existence (AX-B1) together '
        'with the minimality principle MP-1, a design commitment. So Q&#8322; is not chosen against '
        '&#8477;: ruling out &#8477; and every Archimedean completion leaves the p-adic fields, and '
        'T0 then selects Q&#8322; among them.'))
    E.append(body(
        'The structural difference can be stated directly. It has two fences, the order and the '
        'topology, and the order separates &#8477; from Q&#8322; globally, not at zero. '
        'AX-B1 commits the point the snap leaves to having a first step: an element directly above '
        'it with nothing strictly between, a cover (HasFirstStep). A cover of a least '
        'element is what order theory calls an atom (Mathlib bot_covBy_iff). An ordered field has no '
        'bottom element; its 0, which plays that role here, has no first step '
        '(axb1_fails_in_ordered_field). That is one instance of a stronger fact: an order is '
        'dense if and only if no element at all has a first step '
        '(axb1_fails_everywhere_iff_dense). The equivalence quantifies over every element, so '
        'density rules out a first step at 0, and one element without a first step does not '
        'make an order dense. In the metric chart zero is a limit point of the nonzero elements, '
        'in &#8477; and equally in Q&#8322;; so being a limit point does not decide the snap. '
        'Q&#8322;\'s zero is a floor of the limit kind: the doubling orbit of a nonzero element '
        'converges to 0 and does not reach it in finite time, while counting down in &#8469; '
        'reaches 0 in finitely many steps (floor_reach_separates_mu_nu). In the valuation chart '
        'zero sits at the other end: v(0) = +&#8734;, the greatest value, and no nonzero element '
        'shares it (padic_addVal_eq_top_iff). Neither fact is a first step. No order instance '
        'on Q&#8322; synthesizes in Mathlib (LT &#8474;_[2] does not). Take instead the norm '
        'preorder of the &#167; ROLE examples in ZeroParadox/BottomCannotBe.lean '
        '(Preorder.lift of the norm). At zero the order does not separate the two: 0 is least and '
        'has no first step, as in &#8477;\'s field order, since between 0 and any nonzero a lies an '
        'element of strictly smaller nonzero norm; that holds in every nontrivially normed field, '
        '&#8477;\'s norm preorder included (the &#167; ROLE example stating it for every such field). '
        'Globally the order does: Q&#8322;\'s norm preorder is not dense, since every nonzero norm is '
        'an integer power of 2 (Padic.padicNormE.image) and so 2 is covered by 1, its norms being '
        '1/2 and 1 (the &#167; ROLE example stating that cover), while &#8477; is densely ordered in '
        'its field order and in its norm preorder alike (the &#167; ROLE example stating both). In '
        'the standard terms this is a discrete group of norm values against a dense one; Mathlib\'s '
        'name for the dense side is DenselyNormedField, &#8477; is an instance '
        '(Real.denselyNormedField), and its density lemma is NormedField.exists_lt_norm_lt. In the '
        'valuation order 0 is greatest, v(0) = &#8868; (addVal_bot). '
        'The first step AX-B1 commits to is a cover of &#8869; on the state carrier, in ZP-A\'s '
        'induced order (HasFirstStep), a commitment. t_snap_given_cover '
        '(ZeroParadox/Order/Snap.lean) assumes the run\'s first step is a cover (hcov); with '
        'CC-1, the run\'s start at &#8869;, that step is a cover of &#8869;. The converse fails: a '
        'run can start at a &#8869; that has a cover while its own first step is not one '
        '(ZeroParadox/Order/SnapCannotBe.lean). MachinePhase meets the commitment (the '
        'MachinePhase example in ZeroParadox/Order/Snap.lean stating that c&#8321; covers its '
        '&#8869;). In neither ordering of Q&#8322; does its 0 have a first step: in the norm '
        'preorder it has none, and in the valuation order nothing lies above it. '
        'The snap does not fail in &#8477; by accident. In the order it fails because &#8477; '
        'is densely ordered, and in a dense order no element has a first step, 0 included; in '
        'the topology &#8477; is connected (place_topological_signature), so not totally '
        'disconnected (real_no_snap), a second and separate fence.'))
    E.append(sp(4))

    E.append(remark_box(
        'Remark: The Dual Limit Condition',
        [
            'The results of §II–§III and ZP-L together admit an informal '
            'structural account of why the snap is domain-specific.',
            'In any dense ordered field, 0 has no nearest neighbour from above: for any '
            '&#949; > 0 there exists &#948; with 0 < &#948; < &#949; (F-DENSITY). Zero is '
            'a topological limit point from above with no minimum positive element. AX-B1 '
            'commits the point the snap leaves to a first step (HasFirstStep); density forbids '
            'a first step at every element, 0 included (axb1_fails_everywhere_iff_dense), so '
            'the block is global, not located at 0. This is the blocking condition established '
            'in this document.',
            '&#949;&#8320; of Ordinal (the snap threshold in the ordinal chart, ZP-L) is the least fixed '
            'point of &#945; &#8614; &#969;^&#945;: it is not reachable by any finite '
            'iteration of the &#969;^(&#183;) operation, only by the limit of the tower '
            '&#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230; It has no predecessor in '
            'the ordinal hierarchy: no ordinal &#945; satisfies &#945; + 1 = &#949;&#8320;.',
            'Both cases are limit-type conditions: the field case is a topological limit '
            'point with no minimum positive neighbour above 0; the ordinal case is a limit '
            'ordinal (specifically, the least fixed point of &#945; &#8614; &#969;^&#945;) '
            'with no predecessor below &#949;&#8320;. The analogy is structural &#8212; '
            'both describe a boundary approached but not reachable by finite steps on one '
            'side &#8212; but it is not a proved identification. The two structures live in '
            'different mathematical categories.',
            'In the ordinal chart the snap meets two conditions at once, at '
            'opposite ends of the crossing: (1) below the landing, the boundary is a limit with '
            'no immediate predecessor (as &#949;&#8320; is approached by the tower and no '
            '&#945; has &#945; + 1 = &#949;&#8320; &#8212; what makes the threshold '
            'non-arbitrary) and (2) above the point left, the crossing is discrete: that point '
            'has a first step, a cover (HasFirstStep). Condition (1) is not required of every '
            'host: in the two-state carrier MachinePhase, where T-SNAP holds (t_snap_derived), '
            'the landing c&#8321; covers the bottom c&#8320; (the MachinePhase example in '
            'ZeroParadox/Order/Snap.lean stating that c&#8321; covers &#8869;), so it has an immediate '
            'predecessor. Dense ordered fields fail condition (2) '
            'at every element (axb1_fails_everywhere_iff_dense). Their 0 also lacks an immediate '
            'predecessor, for the same reason, and without (2) that does not help. '
            'In the non-standard naturals *&#8469; with '
            'the order topology, every element has an immediate predecessor, so there is '
            'no limit point at infinity in the order-topology sense; condition (1) fails '
            'informally. (This *&#8469; observation is informal &#8212; not a proved result '
            'of this document or ZP-L.)',
            'The tower images cnfToZp2(towerNONote n) converge to 0 in &#8484;&#8322; '
            'as n &#8594; &#8734; (proved in ZP-L), and &#949;&#8320; is the minimal '
            'snap threshold in the ordinal setting (proved in ZP-L). cnf_bridge_type_boundary '
            '(ZeroParadox/Ordinal/CnfBridge.lean) states these as co-witnesses, and not as an identity, '
            'in three conjuncts: &#949;&#8320; is the least fixed point of &#945; &#8614; '
            '&#969;^&#945; at or above the bottom of the ordinals; the images cnfToZp2(towerNONote n) '
            'converge to the 2-adic 0; and each towerNONote n represents the n-th stage of the '
            '&#969;-tower (towerNONote_repr). cnfToZp2 maps the &#969;-tower into &#8484;&#8322;. '
            '&#949;&#8320; &#8800; 0, with 0 the ordinal zero, is a theorem in the '
            'ordinals (epsilon0_ne_zero). An equation between &#949;&#8320; and the 2-adic 0 does '
            'not type-check, with no coercion between the ordinals and &#8484;&#8322; in either '
            'direction; a Lean guard in that file detects the failure (MC-1 / ZP-P). Under cnfToZp2 the 2-adic 0 is '
            'the image of the seed stage towerNONote 0, whose ordinal value is the bottom of the '
            'ordinals, and the limit of the stages\' images; &#949;&#8320; has no image there, since '
            'every ordinal notation in the map\'s domain denotes an ordinal below &#949;&#8320; '
            '(repr_lt_epsilon0, ZeroParadox/Ordinal/PricedInterface.lean). Through another map &#949;&#8320; does land on that 0: the canonical threshold map sends '
            '&#949;&#8320; to c&#8321; and snapEmbed sends c&#8321; to 0 (snap_state_zp2_is_zero, '
            'ZP-M), a map value, not an identity (see ZP-L, The Bridge: What Is Formal and What Is '
            'Assumed).',
            'This is an observation, not a proved theorem. The blocking result '
            '(F-SNAP-IMPOSSIBLE) is proved here; the threshold and convergence results '
            'are proved in ZP-L. The claim that both conditions reflect a common structural '
            'property is interpretive &#8212; it does not follow from their conjunction '
            'alone. The *&#8469; example above is informal.',
            'The dual-approach structure recurs across the ZP layers: in ZP-L, '
            '&#949;&#8320; is located from above as the least fixed point of '
            '&#945; &#8614; &#969;^&#945; and from below as the limit of the CNF tower; '
            'in ZP-M, the computability and ordinal fixed points are argued to converge to the '
            'same 2-adic limit. This recurrence is not coincidental. The snap is the point '
            'where a domain\'s own measurement framework exhausts itself; no single framework '
            'can locate it from inside because the framework runs out exactly there. '
            'This suggests a dual approach is required in each case: each framework reaches the '
            'boundary from its own direction, and the snap is the point they agree on. '
            'No general theorem to this effect is established here.',
            'The surreal numbers (No) satisfy both conditions &#8212; non-Archimedean '
            'structure (containing &#949;&#8320; as an ordinal) and genuine limit ordinals '
            '&#8212; and are the natural boundary test case for any duality theorem. Whether '
            'the surreals admit a snap-like result, or whether a third structural condition '
            'is required to exclude them, has not been determined. '
            '(Informal &#8212; not a result of this document.)',
            'Development path toward a formal theorem: prove the two conditions as '
            'independent Lean results (density impossibility established here; &#949;&#8320; '
            'a limit ordinal, the Order.IsSuccLimit example in '
            'ZeroParadox/Order/SnapCannotBe.lean), then prove they agree on the same structural '
            'point. The surreal case is the critical test of whether two conditions are '
            'jointly sufficient.',
        ]
    ))
    E.append(sp(4))

    # ── VII. Validation Status ────────────────────────────────────────────────
    E.append(Paragraph('VII. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['F-DENSITY', 'DERIVED — Lean-verified; general case'],
         ['F-NO-MIN', 'DERIVED — Lean-verified; general case'],
         ['F-SNAP-BLOCKED', 'DERIVED — Lean-verified; general case'],
         ['F-SNAP-IMPOSSIBLE', 'DERIVED — Lean-verified; general case'],
         ['R-DENSITY', 'DERIVED — Corollary of F-DENSITY at F = &#8477;'],
         ['R-NO-MIN', 'DERIVED — Corollary of F-NO-MIN at F = &#8477;'],
         ['R-SNAP-BLOCKED', 'DERIVED — Corollary of F-SNAP-BLOCKED at F = &#8477;'],
         ['R-SNAP-IMPOSSIBLE', 'DERIVED — Corollary of F-SNAP-IMPOSSIBLE at F = &#8477;']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
