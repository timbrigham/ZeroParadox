"""
Zero Paradox — ZP-M: Kleene-Ordinal Bridge PDF Builder
Version 1.1 | June 2026
v1.1: Rendered version changelog removed (C1 sweep — no version changelogs in rendered PDF content).
v1.0: Initial release. All theorems §I–§IV proved sorry-free in Lean 4.
Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.
Closes the two gaps left by ZP-K (hfp free hypothesis) and ZP-L (type bridge).
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.1'


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
        Paragraph('Version ' + VERSION + ' | May 2026', S['subtitle']),
        Paragraph(
            '<i>Synthesis bridge. '
            'All theorems §I&#8211;§IV proved sorry-free in Lean 4. '
            'Closes the hfp free hypothesis (ZP-L) and the snapEmbed type bridge. '
            'Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.</i>',
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
        '(Kleene quine, ZP-K), the ordinal snap at &#949;&#8320; (ZP-L), and the '
        '2-adic limit 0 (ZP-B).'))
    E.append(body(
        'The closing result (§IV) records that both the Kleene recursion theorem and '
        'the ordinal fixed-point &#949;&#8320; = &#969;^&#949;&#8320; are instances of '
        'the same diagonalization pattern: a self-referential operation produces a forced '
        'fixed point. The two domains — computability theory (codes and Gödel numbers) '
        'and ordinal theory (&#969;-tower iteration) — use no shared mathematical machinery, '
        'but the structural schema is identical. Remark R-M.1 tracks what this means for '
        'DA-1 Path 2 and the boundary of the diagonalization frame.'))
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
        'the snap state c&#8321; maps to 0 (the 2-adic limit of the tower encodings). '
        'Under multiplication on &#8484;&#8322;, 0 is absorbing — mirroring exactly the '
        'join structure on MachinePhase, where c&#8321; is the absorbing element.'))
    E.append(body(
        'Within the ZP framework, 0 &#8712; &#8484;&#8322; plays the role of &#8869; — '
        'it is the 2-adic valuation limit and the fixed point of multiplication by 2. '
        'snapEmbed makes this modelling commitment concrete: c&#8321; maps to 0 because '
        'c&#8321; IS the object at infinite 2-adic depth. This is a modelling commitment, '
        'not a ring-theoretic theorem.'))

    E.append(def_box(
        'Definition: snapEmbed (ZPM.lean §I)',
        [
            'snapEmbed : MachinePhase &#8594; &#8484;&#8322;',
            '  snapEmbed c&#8320; = 1    (pre-snap: 2-adic unit)',
            '  snapEmbed c&#8321; = 0    (snap state: 2-adic zero = 2-adic limit of tower)',
            '',
            'The morphism property: join on MachinePhase (c&#8321; is absorbing under join) '
            'corresponds to multiplication on &#8484;&#8322; (0 is absorbing under &#215;). '
            'Both structures share the absorbing-element pattern — the bridge is structural, '
            'not incidental.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: snapEmbed_injective (ZPM.lean §I)',
        [
            'Function.Injective snapEmbed',
            'c&#8320; and c&#8321; map to distinct 2-adic integers (1 &#8800; 0 in &#8484;&#8322;).',
            'Proof: case split on MachinePhase; simp_all closes each case.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: snapEmbed_mul_morphism (ZPM.lean §I)',
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
        'Lemma: snapEmbed_c0_val (ZPM.lean §I)',
        [
            '(snapEmbed c&#8320;).valuation = 0',
            'c&#8320; maps to a 2-adic unit: valuation 0, norm 1.',
            'Proof: simp via PadicInt.valuation_one.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Lemma: snapEmbed_c1_dvd (ZPM.lean §I)',
        [
            '&#8704; n : &#8469;,  (2 : &#8484;&#8322;)^n &#8739; snapEmbed c&#8321;',
            'c&#8321; maps to 0, which is divisible by all powers of 2.',
            '0 &#8712; &#8484;&#8322; is divisible by 2^n for every n &#8212; infinite 2-adic depth.',
            'This is the formal signature of &#8869; = {&#8869;}: infinite 2-adic valuation.',
            'Proof: simp [snapEmbed_c1].',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark: snapEmbed vs the Identification Conjecture',
        [
            'snapEmbed establishes the morphism property (join &#8614; &#215;) and the '
            'absorbing-element correspondence. It does not derive the identification '
            '&#949;&#8320; &#8596; &#8869; as a type-theoretic theorem: establishing '
            'that snap_exactly_at_epsilon_zero\'s threshold IS 0 &#8712; &#8484;&#8322; '
            'via an order-preserving embedding would require ZPSemilattice morphisms '
            'between Ordinal and MachinePhase, which are not defined in this library.',
            'What the bridge achieves: c&#8321; (the snap state assigned at &#949;&#8320;) '
            'maps to 0 (the 2-adic limit) under snapEmbed. The triangle is formally exhibited. '
            'The conjectured stronger bridge &#8212; Classical.choice forced by ZP metric '
            'collapse &#8212; is deferred to §V (future work).',
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
        'Theorem: hfp_from_epsilon_zero (ZPM.lean §II)',
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
        'Theorem: snap_unconditional (ZPM.lean §II)',
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
        '&#949;&#8320;) plus monotonicity, the full minimality result follows from the ordinal '
        'structure alone. hfp is a derived consequence, not an additional commitment.',
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
        'with tower encodings in &#8484;&#8322; converging to 0. '
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
        'Theorem: snap_state_zp2_is_zero (ZPM.lean §III)',
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
        'Theorem: zpm_triangle (ZPM.lean §III)',
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

    # ── Section IV: Shared Diagonalization Pattern ─────────────────────────────
    print('[build_zpm] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Shared Diagonalization Pattern', S['h1']),
        hr(),
    ]

    E.append(body(
        'Both the Kleene recursion theorem (ZP-K) and the ordinal fixed-point &#949;&#8320; '
        '(ZP-L) arise from the same structural schema: a self-referential operation has a '
        'forced fixed point. In computability theory, the diagonal applies to codes and '
        'their Gödel numbers. In ordinal theory, the diagonal applies to the tower iteration '
        '&#945; &#8614; &#969;^&#945;. The two domains share no mathematical machinery, '
        'but the diagonalization pattern is identical.'))

    E.append(data_table(
        headers=['Domain', 'Self-referential operation', 'Forced fixed point'],
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
        'Theorem: both_fixed_points_exist (ZPM.lean §IV)',
        [
            '(&#8707; c : Code, &#8704; n, eval c n = eval c (encode c + n))  &#8743;',
            '(&#8707; &#945; : Ordinal, &#969;^&#945; = &#945; &#8743; '
            '&#8704; &#946;, &#969;^&#946; = &#946; &#8594; &#945; &#8804; &#946;)',
            'Both diagonalization patterns produce fixed points, co-proved in one formal context.',
            'Left: Kleene quine (period = Gödel number of c), via computational_quine_exists.',
            'Right: &#949;&#8320; = &#969;^&#949;&#8320;, minimal; via epsilonZero_fixedPoint '
            'and epsilonZero_le_fixedPoint.',
            'The co-existence is the formal content: two forced fixed points, two domains, '
            'one theorem.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R-M.1: DA-1 Path 2 and the Limits of the Diagonalization Frame',
        [
            'both_fixed_points_exist establishes that Kleene diagonalization (a code on '
            'its own Gödel number) and ordinal diagonalization (&#949;&#8320; = &#969;^&#949;&#8320;, '
            'least fixed point) are the same structural pattern in two domains. Both are '
            'textbook instances of the diagonalization schema.',
            'L-INF (ZP-C §II: &#8869; has divergent surprisal — unbounded information content, '
            'incompressible by any finite description) is structurally analogous. Whether it '
            'fits the same diagonalization schema formally is the open question.',
            'The formally unconnected instance is L-INF. This gap is DA-1 Path 2 — the '
            'informational bridge. The reason Path 2 resisted formalization is now visible '
            'from this layer: L-INF is a measure-theoretic statement (Shannon entropy, '
            'probability distributions) while the Kleene quine is a computability-theoretic '
            'statement (partial recursive functions, Gödel encoding). The two frameworks '
            'share no mathematical machinery.',
            'The diagonalization frame established here provides the common conceptual ground, '
            'but the formal bridge requires the Kolmogorov complexity connection: '
            'incompressibility is the concept that lives in both worlds simultaneously. '
            'That bridge is outside the current Lean scope, pending AIT infrastructure '
            'not yet in Mathlib.',
            'DA-1 Path 2 was recharacterized in ZP-E/ZP-K as a foundational commitment '
            'rather than a missing proof. The diagonalization frame here makes the boundary '
            'precise: the gap is not a skipped proof step but a genuine framework separation — '
            'measure-theoretic surprisal on one side, computability-theoretic encoding on the '
            'other, with no shared machinery in current Mathlib.',
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
        ],
        col_widths=[TW * 0.55, TW * 0.15, TW * 0.30],
    ))
    E.append(sp(4))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'All theorems carry axiom footprint: [propext, Classical.choice, Quot.sound].',
            'These are standard Mathlib infrastructure axioms, inherited from ordinal theory '
            '(ZP-L), 2-adic analysis (ZP-B), and computability theory (ZP-K).',
            'Classical.choice is load-bearing in both the computability fixed-point '
            '(Kleene\'s theorem) and the ordinal fixed-point (nfp). Its presence is '
            'expected and documented.',
            'Zero sorry in ZPM.lean. Verified: lake build, May 2026.',
        ]
    ))
    E.append(sp(6))

    E += [
        hr(),
        Paragraph(
            '<i>End of ZP-M | Kleene&#8211;Ordinal Bridge | '
            'snapEmbed type bridge | hfp gap closed | zpm_triangle co-proved | '
            'both_fixed_points_exist | R-M.1: DA-1 Path 2 boundary | '
            'All ZPM.lean theorems verified. Axioms: [propext, Classical.choice, Quot.sound].</i>',
            S['endnote']),
    ]

    print('[build_zpm] Building document...')
    doc.build(E)
    print(f'[build_zpm] Done: {out_path}')


if __name__ == '__main__':
    build()
