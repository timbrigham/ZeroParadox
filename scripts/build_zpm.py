"""
Zero Paradox — ZP-M: Kleene-Ordinal Bridge PDF Builder
Version 1.19 | November 2026
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.19'
FIRST_RELEASED = 'May 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-M_Kleene_Ordinal_Bridge.pdf')
    print(f'[build_zpm] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-M: Kleene-Ordinal Bridge',
                   'ZP-M: Kleene-Ordinal Bridge', 'Version ' + VERSION)
    E = []

    print('[build_zpm] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-M: Kleene&#8211;Ordinal Bridge', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>Synthesis bridge. '
            'All theorems §I&#8211;§IV proved sorry-free in Lean 4. '
            'Closes the hfp free hypothesis (ZP-L) and the snapEmbed type bridge. '
            'Axiom footprint: at most [propext, Classical.choice, Quot.sound], per declaration below.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'ZP-M bridges the two prior layers — ZP-K (computational grounding via Kleene\'s '
        'second recursion theorem) and ZP-L (ordinal snap threshold at &#949;&#8320;) — '
        'with two formal results. First, the free hypothesis hfp in '
        'snap_exactly_at_epsilon_zero (ZP-L §VI) is proved to follow from a minimal '
        'alignment hypothesis plus monotonicity: hfp is not an independent condition. '
        'Second, the canonical type bridge snapEmbed : MachinePhase &#8594; &#8484;&#8322; '
        'formalizes the structural triangle connecting the pre-snap state c&#8320; '
        '(&#8869; of MachinePhase; reading it as the Kleene quine is not an equation, since a Code and a MachinePhase state '
        'are different types, and that it runs is the occurrence commitment), the ordinal snap at &#949;&#8320; (ZP-L), and the '
        '2-adic limit 0 (ZP-B).'))
    E.append(body(
        'The closing result (§IV) proves two existence statements together: a code c with eval c n = eval c (encode c + n) '
        'for every n (a periodicity condition, proved via the recursion theorem, which constant codes also meet) and the least '
        'ordinal fixed point &#949;&#8320; = &#969;^&#949;&#8320;. '
        'It is a conjunction of two existence proofs over different types. The two domains — computability '
        'theory (codes and Gödel numbers) and ordinal theory (&#969;-tower iteration) — use no shared '
        'mathematical machinery; reading them as one pattern is the framework&#8217;s interpretation, not '
        'what the theorem proves (Remark R-M.1). R-M.1 also tracks what this means for DA-1 Path 2.'))
    E.append(hr())

    # ── Section I: The snapEmbed Morphism ──────────────────────────────────────
    print('[build_zpm] Building Section I...')
    E += [
        Paragraph('Section I: The snapEmbed Morphism', S['h1']),
        hr(),
    ]

    E.append(body(
        'snapEmbed is the canonical type bridge from ZP-E\'s machine-phase state space '
        'to ZP-B\'s 2-adic integers. The pre-snap state c&#8320; maps to 1 (a 2-adic unit); '
        'the snap state c&#8321; maps to 0 (the 2-adic limit of the tower images). '
        'Under multiplication on &#8484;&#8322;, 0 is absorbing — mirroring exactly the '
        'join structure on MachinePhase, where c&#8321; is the absorbing element.'))
    E.append(body(
        'No equation between a MachinePhase state and a 2-adic integer is stated; they are different types. '
        'What c&#8321; and 0 share is a role, the die&#8217;s Motion.SelfOnlyAt (ZeroParadox/Die.lean): a point that '
        'steps to itself and to nothing else; in each carrier its occupant is proved for the step chosen there. '
        'Two pairings, each through the map snapEmbed, stand in place of an identity (Incompleteness.lean &#167;I-b). Under the join step a &#8594; join a z, only '
        'c&#8321; occupies the role (machineJoinMotion_selfOnlyAt_iff); under the multiplication step x &#8594; x&#183;w '
        'on &#8484;&#8322;, only 0 does (z2MulMotion_selfOnlyAt_iff); snapEmbed is a map of these two motions '
        '(snapEmbedHom). Its back clause fails at c&#8320; (1 steps to 2, and no state maps to 2), so the general '
        'transport of the role along such maps does not apply; at c&#8321; the role does carry over, because 0 has only '
        'itself as successor (snapEmbed_selfOnlyAt_c1, from Motion.selfOnlyAt_relHom). Under doubling on &#8484;&#8322;, '
        'only 0 occupies the role (z2_double_selfOnlyAt_iff), and 0 is divisible by every power of 2 (snapEmbed_c1_dvd); but snapEmbed '
        'carries no motion with a step at c&#8320; into doubling steps (snapEmbed_doubling_noStepAt): the snap '
        'c&#8320; &#8594; c&#8321; goes to 1 &#8594; 0, which is not a doubling step.'))

    E.append(def_box(
        'Definition: snapEmbed (Incompleteness.lean §I)',
        [
            'snapEmbed : MachinePhase &#8594; &#8484;&#8322;',
            '  snapEmbed c&#8320; = 1    (pre-snap: 2-adic unit)',
            '  snapEmbed c&#8321; = 0    (snap state: 2-adic zero = 2-adic limit of tower)',
            '',
            'The morphism property: join on MachinePhase (c&#8321; is absorbing under join) '
            'corresponds to multiplication on &#8484;&#8322; (0 is absorbing under &#215;). '
            'In the die this is a map of motions, from a &#8594; join a z on MachinePhase to '
            'x &#8594; x&#183;w on &#8484;&#8322; (snapEmbedHom, &#167;I-b).',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: snapEmbed_injective (Incompleteness.lean §I)',
        [
            'Function.Injective snapEmbed',
            'c&#8320; and c&#8321; map to distinct 2-adic integers (1 &#8800; 0 in &#8484;&#8322;).',
            'Proof: case split on MachinePhase; simp_all closes each case.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: snapEmbed_mul_morphism (Incompleteness.lean §I)',
        [
            '&#8704; a b : MachinePhase,  snapEmbed (join a b) = snapEmbed a &#215; snapEmbed b',
            'snapEmbed sends the join operation to multiplication.',
            'Under this map, the absorbing-element structure is preserved:',
            '  join c&#8321; x = c&#8321; for all x  &#8596;  0 &#215; y = 0 for all y &#8712; &#8484;&#8322;.',
            'Proof: case split; simp [snapEmbed].',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: snapEmbed_c0_val (Incompleteness.lean §I)',
        [
            '(snapEmbed c&#8320;).valuation = 0',
            'c&#8320; maps to a 2-adic unit: valuation 0, norm 1.',
            'Proof: simp via PadicInt.valuation_one.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: snapEmbed_c1_dvd (Incompleteness.lean §I)',
        [
            '&#8704; n : &#8469;,  (2 : &#8484;&#8322;)^n &#8739; snapEmbed c&#8321;',
            'c&#8321; maps to 0, which is divisible by all powers of 2.',
            '0 &#8712; &#8484;&#8322; is divisible by 2^n for every n &#8212; infinite 2-adic depth.',
            'Proof: simp [snapEmbed_c1].',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Results: snapEmbed in the die (Incompleteness.lean §I-b)',
        [
            'machineJoinMotion_selfOnlyAt_iff: under a &#8594; join a z, y steps to itself and to nothing else iff y = c&#8321;. '
            'Lean purity: [propext].',
            'z2MulMotion_selfOnlyAt_iff: under x &#8594; x&#183;w on &#8484;&#8322;, y steps to itself and to nothing else iff y = 0. '
            'Lean purity: [propext, Classical.choice, Quot.sound].',
            'snapEmbedHom: snapEmbed is a strict map between these two motions (steps to steps, from snapEmbed_mul_morphism). '
            'An example beside it shows the back clause fails at c&#8320; (1 steps to 2, and no state maps to 2). '
            'Lean purity: [propext, Classical.choice, Quot.sound].',
            'snapEmbed_selfOnlyAt_c1: the image of c&#8321; steps to itself only in the multiplication motion, carried along '
            'snapEmbedHom&#8217;s steps by Motion.selfOnlyAt_relHom. Lean purity: [propext, Classical.choice, Quot.sound].',
            'z2_double_selfOnlyAt_iff: under doubling on &#8484;&#8322;, y steps to itself and to nothing else iff y = 0. '
            'Lean purity: [propext, Classical.choice, Quot.sound].',
            'snapEmbed_doubling_noStepAt: if snapEmbed sends every step of a motion M on MachinePhase to a doubling step, '
            'c&#8320; has no step in M. Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark: snapEmbed and the bottom role',
        [
            'snapEmbed establishes the morphism property (join &#8614; &#215;) and the '
            'absorbing-element correspondence. Relative to the ordinals\' floor, the bottom-role '
            'occupant 0 and the &#949;&#8320; occupant differ (epsilon0_ne_bot); against the '
            '2-adic 0 an identity with &#949;&#8320; is not a well-formed statement '
            '(it fails to elaborate, Ordinal vs &#8484;&#8322;), and the link runs '
            'through maps: snapEmbed sends c&#8321; to 0, the bottom-role occupant of the Scale.lean chart, '
            'whose join with &#8869; = 0 is chosen (ZeroParadox/Valuation/Scale.lean &#167;V). The canonical threshold '
            'map Ordinal &#8594; MachinePhase is order-non-decreasing in ZP-A\'s join order '
            '(snap_map_mono), and no map Ordinal &#8594; MachinePhase is compatible with the '
            'CNF &#8594; &#8484;&#8322; map along the tower: for every g : MachinePhase &#8594; '
            '&#8484;&#8322; the square fails, because MachinePhase has two values and the images of stages 1, 2, 3 '
            'have three distinct 2-adic valuations (the example after '
            'c1_epsilon_zero_identification in ZeroParadox/Ordinal/Gentzen.lean); through snapEmbed '
            'it fails at every stage n &#8805; 1, because snapEmbed takes only the values 1 and 0, '
            'and stage n &#8805; 1 maps to 2^n, which is neither '
            '(ZeroParadox/Ordinal/Incompleteness.lean &#167; II).',
            'What the bridge achieves: c&#8321; (the snap state assigned at &#949;&#8320;) '
            'maps to 0 (the 2-adic limit) under snapEmbed. The triangle is formally exhibited. '
            'Whether Classical.choice is forced by the ZP metric collapse is a separate open '
            'question (ZeroParadox/Ordinal/SyntacticCollapse.md).',
        ]
    ))
    E.append(sp(6))

    # ── Section II: Closing the hfp Gap ────────────────────────────────────────
    print('[build_zpm] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: Closing the hfp Gap', S['h1']),
        hr(),
    ]

    E.append(body(
        'snap_exactly_at_epsilon_zero (ZP-L §VI) carries a free hypothesis hfp asserting '
        'that for any map &#981; : Ordinal &#8594; MachinePhase, every fixed point of '
        '&#969;^&#183; maps to c&#8321;. This hypothesis is required for the upper-bound '
        'direction of the minimality argument (&#949;&#8320; is the first snap point). '
        'The canonical witness in epsilon_zero_snap_canonical (ZP-L §VII) satisfies hfp '
        'directly by case analysis, but hfp is not derived from the structural axioms.'))
    E.append(body(
        'ZP-M §II closes this gap. Given monotonicity and &#981; &#949;&#8320; = c&#8321; '
        'as a minimal alignment hypothesis, hfp follows. The argument: for any fixed point '
        '&#945; of &#969;^&#183;, epsilonZero_le_fixedPoint gives &#949;&#8320; &#8804; &#945;; '
        'monotonicity then chains &#981; &#949;&#8320; &#8804; &#981; &#945;; substituting '
        'c&#8321; and using c&#8321;\'s absorbing property gives &#981; &#945; = c&#8321;.'))

    E.append(result_box(
        'Theorem: hfp_from_epsilon_zero (Incompleteness.lean §II)',
        [
            'For any &#981; : Ordinal &#8594; MachinePhase satisfying:',
            '  hmono: &#8704; &#945; &#8804; &#946;, join (&#981; &#945;) (&#981; &#946;) = &#981; &#946;',
            '  h&#949;&#8320;: &#981; epsilonZero = c&#8321;',
            'we have: &#8704; &#945;, &#969;^&#945; = &#945; &#8594; &#981; &#945; = c&#8321;.',
            '',
            'Proof: epsilonZero_le_fixedPoint gives &#949;&#8320; &#8804; &#945;; '
            'hmono gives join c&#8321; (&#981; &#945;) = &#981; &#945;; '
            'join c&#8321; x = c&#8321; for all x (absorbing property of c&#8321;), '
            'so c&#8321; = &#981; &#945;.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: snap_unconditional (Incompleteness.lean §II)',
        [
            'For any &#981; satisfying hmono, h0 (tower stages &#8614; c&#8320;), '
            'and h&#949;&#8320; (&#981; &#949;&#8320; = c&#8321;):',
            '  &#981; &#949;&#8320; = c&#8321;  &#8743;  '
            '&#8704; &#945;, &#981; &#945; = c&#8321; &#8594; &#949;&#8320; &#8804; &#945;.',
            '&#949;&#8320; is the minimal snap threshold under minimal hypotheses.',
            'Proof: snap_exactly_at_epsilon_zero with hfp supplied by hfp_from_epsilon_zero.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(callout(
        'What §II achieves: hfp is no longer a free hypothesis in the minimality theorem. '
        'Given &#981; &#949;&#8320; = c&#8321; (the alignment condition: the map snaps at '
        '&#949;&#8320;) plus monotonicity and every tower stage sent to c&#8320; (h0), the full '
        'minimality result follows (snap_unconditional). hfp is a derived consequence, not an additional commitment.',
        bg=GREEN_LITE, border=GREEN
    ))
    E.append(sp(6))

    # ── Section III: The Kleene-Ordinal Triangle ────────────────────────────────
    print('[build_zpm] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Kleene&#8211;Ordinal Triangle', S['h1']),
        hr(),
    ]

    E.append(body(
        'ZP-K established: c&#8320; = &#8869; is a Quine atom '
        '(da1_closed_concrete : IsQuineAtom (&#8869; : MachinePhase)). '
        'ZP-L established: the canonical snap map assigns c&#8321; exactly at &#949;&#8320;, '
        'with tower images in &#8484;&#8322; converging to 0. '
        'The triangle connects all three objects formally:'))

    E.append(data_table(
        headers=['Edge', 'Objects connected', 'Formal content'],
        rows_data=[
            ['A &#8596; C  (ordinal snap)',
             '&#949;&#8320; &#8596; c&#8321;',
             'Canonical snap map: stages below &#949;&#8320; &#8614; c&#8320;; '
             '&#949;&#8320; &#8614; c&#8321; (ZP-L §VII)'],
            ['A &#8596; B  (2-adic convergence)',
             'Tower &#8594; 0 &#8712; &#8484;&#8322;',
             'cnfToZp2(towerNONote n) &#8594; 0 in &#8484;&#8322; (ZP-L §IV)'],
            ['B &#8596; C  (type bridge)',
             'c&#8321; &#8596; 0 &#8712; &#8484;&#8322;',
             'snapEmbed c&#8321; = 0 (§I above)'],
        ],
        col_widths=[TW * 0.20, TW * 0.22, TW * 0.58],
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: snap_state_zp2_is_zero (Incompleteness.lean §III)',
        [
            'snapEmbed ((&#955; &#945; : Ordinal, if &#945; < &#949;&#8320; then c&#8320; else c&#8321;) '
            '&#949;&#8320;) = 0',
            'The canonical snap map assigns c&#8321; at &#949;&#8320;; snapEmbed sends c&#8321; to 0.',
            'The snap state at the ordinal threshold maps to the 2-adic zero.',
            'Proof: simp (the if-condition evaluates to False at &#945; = &#949;&#8320;).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: zpm_triangle (Incompleteness.lean §III)',
        [
            'All three edges of the triangle, co-proved:',
            '(A &#8596; C)  &#8704; n : &#8469;, fundamentalSeq n < &#949;&#8320;',
            '(A &#8596; C)  (&#955; &#945;, if &#945; < &#949;&#8320; then c&#8320; else c&#8321;) '
            '&#949;&#8320; = c&#8321;',
            '(A &#8596; B)  Filter.Tendsto (&#955; n, cnfToZp2 (towerNONote n)) '
            'Filter.atTop (nhds 0)',
            '(B &#8596; C)  snapEmbed (&#955; &#945;, if &#945; < &#949;&#8320; then c&#8320; '
            'else c&#8321;) &#949;&#8320; = 0',
            'Proof: &#10216;epsilonZero_tower_lt, if_neg (lt_irrefl &#949;&#8320;), '
            'tower_converges_to_zero, snap_state_zp2_is_zero&#10217;.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Section IV: The Kleene and Ordinal Fixed Points ─────────────────────────────
    print('[build_zpm] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: The Kleene and Ordinal Fixed Points', S['h1']),
        hr(),
    ]

    E.append(body(
        'The Kleene recursion theorem (ZP-K) gives a code fixed up to evaluation, and &#949;&#8320; (ZP-L) is '
        'the least fixed point of &#969;^&#183;; the two come from different constructions. In computability theory the construction '
        'is a diagonal argument over codes and their Gödel numbers. In ordinal theory &#949;&#8320; is '
        'reached by iterating the normal function &#945; &#8614; &#969;^&#945; from 0 and taking the '
        'supremum (&#949;&#8320; = nfp (&#969;^&#183;) 0, epsilonZero_eq_nfp in ZeroParadox/Ordinal/Gentzen.lean), the '
        'fixed-point lemma for normal functions rather than a diagonal argument. The two domains share no '
        'mathematical machinery. The theorem below records the ordinal fixed point and, on the computability side, '
        'the computability fixed point the recursion theorem yields: a code c with eval c = selfApply c '
        '(IsComputationalQuine), a predicate constant codes also satisfy, so it does not pin self-reference '
        '(Remark R-M.1).'))

    E.append(data_table(
        headers=['Domain', 'Operation', 'Fixed point'],
        rows_data=[
            ['Computability (ZP-K)',
             'eval c = selfApply c  (c runs on its own Gödel number)',
             '&#8707; c : Code, IsComputationalQuine c'],
            ['Ordinal theory (ZP-L)',
             '&#969;^&#945; = &#945;  (&#945; is a fixed point of &#969;-exponentiation)',
             '&#949;&#8320; = nfp (&#969;^&#183;) 0, the least such &#945;'],
        ],
        col_widths=[TW * 0.23, TW * 0.42, TW * 0.35],
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: both_fixed_points_exist (Incompleteness.lean §IV)',
        [
            '(&#8707; c : Code, &#8704; n, eval c n = eval c (encode c + n))  &#8743;',
            '(&#8707; &#945; : Ordinal, &#969;^&#945; = &#945; &#8743; '
            '&#8704; &#946;, &#969;^&#946; = &#946; &#8594; &#945; &#8804; &#946;)',
            'Two existence statements, co-proved in one formal context.',
            'Left: a code periodic with period its own Gödel number, via computational_quine_exists; '
            'constant codes also satisfy it, so the left conjunct alone does not pin self-reference.',
            'Right: &#949;&#8320; = &#969;^&#949;&#8320;, minimal; via epsilonZero_fixedPoint '
            'and epsilonZero_le_fixedPoint.',
            'The co-existence is the formal content: two existence statements, two domains, '
            'one theorem.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R-M.1: DA-1 Path 2 and the Limits of the Diagonalization Frame',
        [
            'both_fixed_points_exist records, on one side, a code periodic with period its own Gödel number '
            '(obtained by Kleene diagonalization, though constant codes also meet the condition) and, on the other, '
            'the ordinal &#949;&#8320; = &#969;^&#949;&#8320;, the least fixed point and the supremum of the iterates '
            'of &#969;^&#183; from 0. The statement is a '
            'conjunction of two existentials, so it establishes that both exist, not that they are one '
            'structural pattern; reading them as the same pattern is the framework&#8217;s interpretation, '
            'and no equation between a Code and an Ordinal is well-formed. The Kleene fixed point comes from '
            'a diagonal argument (Lawvere 1969; Yanofsky 2003, Theorem 5, places the recursion theorem under that schema); &#949;&#8320; comes from the fixed-point lemma for normal functions, by '
            'iteration to a supremum.',
            'The informational argument has two charts. Depth chart, ZP-C L-INF: surprisal is unbounded above in the '
            'ball-hierarchy depth, each value finite (l_inf). Point chart: at 0 of Q<sub>2</sub>, the one point in every '
            'ball of the chain centred at 0, the 2-adic additive valuation is &#8868; (padic_addVal_bot), the point to '
            'which c&#8320;, &#8869; of MachinePhase, corresponds in ZP-C. As of 2026-11-01 no single declared map from '
            'MachinePhase into &#8484;<sub>2</sub> or &#8474;<sub>2</sub> sends c&#8320; to 0: searching the .lean files under '
            'ZeroParadox/ for both type names finds snapEmbed (ZeroParadox/Ordinal/Incompleteness.lean) and two negative '
            'examples (ZeroParadox/Ordinal/Gentzen.lean, ZeroParadox/Valuation/SemilatticeInstance.lean). A composite does: '
            'the order isomorphism from MachinePhase onto the two-point Pole (c&#8320; to zero), exhibited in an anonymous '
            'example in ZeroParadox/DieCannotBe.lean and read there as order shape only, followed by poleToSphere '
            '(ZeroParadox/Valuation/PoleCornersBridge.lean), which sends zero to 0 of &#8474;<sub>2</sub> in its one-point '
            'compactification; that composite is not declared. '
            '&#167; I&#8217;s snapEmbed is a different map, sending c&#8320; to 1 and c&#8321; to 0; the two are not '
            'composed. L-INF is structurally analogous to the Kleene fixed point. Whether it '
            'fits Kleene&#8217;s diagonalization schema formally is the open question this remark tracks.',
            'L-INF stays formally unconnected. It is a measure-theoretic statement '
            '(surprisal under a probability measure on ZP-B&#8217;s binary space), while the Kleene quine '
            'is a computability-theoretic statement (partial recursive functions, Gödel encoding), '
            'and neither this remark nor both_fixed_points_exist links them. ZP-C uses the surprisal '
            'measure and Kolmogorov complexity as two separate arguments (ZP-C Remark R-BRIDGE).',
            'DA-1 Path 2 is a different matter. In ZP-E (DA-1 insert &#167; IV) it is the step from '
            'unbounded surprisal to executing: a bridge principle of its own, a missing principle and '
            'not a missing proof, which the framework does not adopt and which is not the occurrence '
            'commitment (ZeroParadox/Ordinal/Incompleteness.md, Remark R-M.1).',
        ]
    ))
    E.append(sp(6))

    # ── Theorem Table ───────────────────────────────────────────────────────────
    print('[build_zpm] Building theorem table...')
    E += [
        hr(),
        Paragraph('Theorem Summary', S['h1']),
        hr(),
    ]

    E.append(data_table(
        headers=['Theorem', 'Section', 'Status'],
        rows_data=[
            ['snapEmbed_injective', '§I', 'Proved ✓'],
            ['snapEmbed_mul_morphism', '§I', 'Proved ✓'],
            ['snapEmbed_c0_val', '§I', 'Proved ✓'],
            ['snapEmbed_c1_dvd', '§I', 'Proved ✓'],
            ['hfp_from_epsilon_zero', '§II', 'Proved ✓'],
            ['snap_unconditional', '§II', 'Proved ✓'],
            ['snap_state_zp2_is_zero', '§III', 'Proved ✓'],
            ['zpm_triangle', '§III', 'Proved ✓'],
            ['both_fixed_points_exist', '§IV', 'Proved ✓'],
            ['machineJoinMotion_selfOnlyAt_iff', '§I-b', 'Proved ✓'],
            ['z2MulMotion_selfOnlyAt_iff', '§I-b', 'Proved ✓'],
            ['snapEmbedHom', '§I-b', 'Defined ✓'],
            ['snapEmbed_selfOnlyAt_c1', '§I-b', 'Proved ✓'],
            ['z2_double_selfOnlyAt_iff', '§I-b', 'Proved ✓'],
            ['snapEmbed_doubling_noStepAt', '§I-b', 'Proved ✓'],
        ],
        col_widths=[TW * 0.55, TW * 0.15, TW * 0.30],
    ))
    E.append(sp(4))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'Axiom footprint: at most [propext, Classical.choice, Quot.sound], per declaration (machineJoinMotion and machineJoinMotion_selfOnlyAt_iff carry [propext] only).',
            'These are standard Mathlib infrastructure axioms, inherited from ordinal theory '
            '(ZP-L), 2-adic analysis (ZP-B), and computability theory (ZP-K).',
            'Classical.choice is carried by the statements of the ordinal fixed-point (nfp) results as '
            'written (the statement controls printed in ZeroParadox/Ordinal/Epsilon0MinMax.lean; '
            'ZeroParadox/Category/ChoiceCannotBe.md), '
            'and present in '
            'the computability fixed-point (Kleene\'s theorem). ZP-K Section IV tabulates the '
            'per-declaration measurements.',
            'The footprints listed here are copies; to re-measure one, run #print axioms on the named '
            'declaration.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-M | Kleene&#8211;Ordinal Bridge | '
            'snapEmbed type bridge | hfp gap closed | zpm_triangle co-proved | '
            'both_fixed_points_exist | R-M.1: DA-1 Path 2 boundary | '
            'All Incompleteness.lean theorems verified. Axioms: at most [propext, Classical.choice, Quot.sound], per declaration.</i>',
            S['endnote']),
    ]

    print('[build_zpm] Building document...')
    doc.build(E)
    print(f'[build_zpm] Done: {out_path}')


if __name__ == '__main__':
    build()
