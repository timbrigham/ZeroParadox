"""
Zero Paradox — ZP-L: Incomputability Convergence PDF Builder
Version 1.28 | October 2026
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.28'
FIRST_RELEASED = 'May 2026'


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-L_Incomputability_Convergence.pdf')
    print(f'[build_zpl] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-L: Incomputability Convergence',
                   'ZP-L: Incomputability Convergence', 'Version ' + VERSION)
    E = []

    print('[build_zpl] Building title block...')
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-L: Incomputability Convergence', S['title']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
        Paragraph(
            '<i>All theorems §I&#8211;§VII proved sorry-free in Lean 4. '
            'Axiom footprint: [propext, Classical.choice, Quot.sound] throughout this '
            'document&#8217;s own Lean file (Gentzen.lean). Across the ZP layers the '
            'footprints are not uniform &#8212; ZP-K Section IV tabulates them.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'ZP-L establishes four results connecting the formal axioms of the ZP framework '
        'to standard results in ordinal theory and computability. '
        'First, the axiom footprints of the layers tabulated in Section I are surveyed, and '
        'they are not uniform; ZP-K Section IV tabulates the measured footprints. '
        'Second, Rogers\' fixed-point theorem for a total '
        'computable transformation (Mathlib fixed_point; inter-derivable with Kleene\'s second '
        'recursion theorem, fixed_point&#8322;) is formalized as a wrapper, formalizing the '
        'computational fixed-point structure. Third, the ordinal &#949;&#8320; is fully '
        'characterized as the first fixed point of &#945; &#8614; &#969;^&#945; and the '
        'limit of the tower &#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230;. '
        'Fourth, cnfToZp2 maps ordinals below &#949;&#8320; into &#8484;&#8322; by recursion '
        'on their Cantor normal form. From tower stage 1 on, the 2-adic valuation of the '
        'image climbs with ordinal height toward &#8734; while the 2-adic norm falls toward 0; '
        'the images converge to 0 = &#8869;, the point the seed stage 0 itself maps to '
        '(snap_arc_z2_loop, ZeroParadox/Ordinal/CnfBridge.lean).'))
    E.append(body(
        'The central result (§VII) is the canonical snap map: '
        '&#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321; '
        'simultaneously satisfies all five conditions — monotone, tower-aligned, '
        'fixed-point-respecting, snapping at &#949;&#8320;, and &#949;&#8320; minimal. '
        'All conditions are verified without free hypotheses for this witness. '
        'Proved sorry-free, axiom footprint [propext, Classical.choice, '
        'Quot.sound] throughout ZeroParadox/Ordinal/Gentzen.lean, measured.'))
    E.append(hr())

    # ── Section I: Axiom Footprint Convergence ─────────────────────────────────
    print('[build_zpl] Building Section I...')
    E += [
        Paragraph('Section I: Axiom Footprint Convergence', S['h1']),
        hr(),
    ]

    E.append(body(
        'Non-constructibility appears across the layers listed below. The axiom footprints '
        'are not uniform: ZP-K Section IV tabulates the measured footprints, and the ZPJ/K '
        'row below names a witness on each side — bot_self_mem, '
        'which measures no axioms, and botCode, which carries them.'))

    E.append(data_table(
        headers=['Layer', 'Formal Language', 'Expression of non-constructibility'],
        rows_data=[
            ['ZPB', 'Topology', 'C3: no continuous path &#8869; &#8594; x &#8800; &#8869;'],
            ['ZPC', 'Information Theory', 'L-INF: infinite surprisal at &#8869;'],
            ['ZPJ/K', 'Set Theory + Computation', 'bot_self_mem (AFA); botCode (Kleene)'],
            ['ZPI', 'Algorithmic IT', 'K uncomputable; the K-ratio bridge is refuted, '
             'counterexample S<sub>n</sub> = 2<sup>n</sup> (ZP-I &#167; II.B)'],
        ],
        col_widths=[50, 100, 280],
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark: K is not computed in Lean',
        [
            'Kolmogorov complexity K is not computed in Lean in this framework. '
            'The AFA/Kleene route reaches the same fixed-point structure via a path whose '
            'Kleene step is a KleeneStructure requirement, without requiring K to be explicitly computed.',
            'Axiom footprint evidence — the following ZP-K theorems all carry '
            '[propext, Classical.choice, Quot.sound]:',
            '  t_comp (T-COMP three-way equivalence; the computational face is an assumption, not a clause)',
            '  da1_paths_unified',
            '  isComputationalQuine_undecidable',
            '  infinite_quine_family',
            'Gentzen.lean carries that footprint throughout, measured &#8212; and it is not '
            'inherited from the theorems above. Mathlib\'s ordinal theory carries it on its '
            'own: Ordinal.nfp and Ordinal.epsilon_zero_eq_nfp each measure [propext, '
            'Classical.choice, Quot.sound] with no computability module in scope. ZP-K '
            'Section IV tabulates the measured footprints for the computability side.',
        ]
    ))
    E.append(sp(6))

    # ── Section II: Rogers Fixed-Point Stability ─────────────────────────────────
    print('[build_zpl] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: Rogers Fixed-Point Stability', S['h1']),
        hr(),
    ]

    E.append(body(
        'Rogers\' fixed-point theorem (Mathlib fixed_point; inter-derivable with Kleene\'s second '
        'recursion theorem, fixed_point&#8322;) states that any total computable transformation of a '
        'code has a behavioral fixed point: '
        'a code c such that running f(c) and running c produce the same partial function. '
        'For any computable transformation, at least one fixed-point code exists.'))

    E.append(result_box(
        'Theorem: roger_fixed_point_stability (Gentzen.lean §II)',
        [
            'For any computable f : Code &#8594; Code,',
            '&#8203;  &#8707; c : Code, eval (f c) = eval c',
            'Proof: wrapper around roger_fixed_point_exists.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
            'Note: this is an existential result. The specific code c is not '
            'constructively produced. ZP-K Section IV tabulates the measured footprints.',
        ]
    ))
    E.append(sp(6))

    # ── Section III: Ordinal ε₀ ─────────────────────────────────────────────────
    print('[build_zpl] Building Section III...')
    E += [
        hr(),
        Paragraph('Section III: The Ordinal &#949;&#8320;', S['h1']),
        hr(),
    ]

    E.append(body(
        'The ordinal &#949;&#8320; is the smallest fixed point of the map '
        '&#945; &#8614; &#969;^&#945;. It is the supremum of the tower '
        '0, 1, &#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230; — '
        'each stage is strictly below &#949;&#8320;, and &#949;&#8320; is '
        'not reached by any finite iteration. This section is entirely within Lean scope '
        'via Mathlib\'s ordinal machinery.'))

    E.append(def_box(
        'Definitions (Gentzen.lean §III)',
        [
            'epsilonZero : Ordinal  :=  Ordinal.epsilon 0  (= nfp (&#969;^&#183;) 0 = veblen 1 0)',
            'fundamentalSeq : &#8469; &#8594; Ordinal  :=  fun n &#8614; (&#945; &#8614; &#969;^&#945;)^[n] 0',
            'Explicit stages:',
            '  fundamentalSeq 0 = 0',
            '  fundamentalSeq 1 = 1',
            '  fundamentalSeq 2 = &#969;',
            '  fundamentalSeq 3 = &#969;^&#969;',
            '  fundamentalSeq (n+1) = &#969;^(fundamentalSeq n)',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: epsilonZero_fixedPoint',
        [
            '&#969;^&#949;&#8320; = &#949;&#8320;',
            'Proof: Ordinal.omega0_opow_epsilon 0 (Mathlib).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: epsilonZero_eq_nfp',
        [
            '&#949;&#8320; = nfp (&#969;^&#183;) 0',
            'Proof: Ordinal.epsilon_zero_eq_nfp (Mathlib).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: epsilonZero_eq_iSup',
        [
            '&#949;&#8320; = &#8852; n : &#8469;, fundamentalSeq n',
            'Proof: iSup_iterate_eq_nfp (Mathlib).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: epsilonZero_tower_lt',
        [
            '&#8704; n : &#8469;, fundamentalSeq n < &#949;&#8320;',
            'Every finite stage of the tower is strictly below &#949;&#8320;.',
            'Proof: Ordinal.iterate_omega0_opow_lt_epsilon_zero (Mathlib).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: epsilonZero_le_fixedPoint',
        [
            '&#8704; b : Ordinal, &#969;^b = b &#8594; &#949;&#8320; &#8804; b',
            '&#949;&#8320; is the least fixed point of &#969;^&#183; above 0.',
            'Proof: Ordinal.epsilon_zero_le_of_omega0_opow_le (Mathlib).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: fundamentalSeq_strictMono',
        [
            '&#8704; n : &#8469;, fundamentalSeq n < fundamentalSeq (n + 1)',
            'The tower is strictly monotone.',
            'Proof: by induction; successor step uses isNormal_opow.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R-L.1: Proof-Theoretic Alignment',
        [
            'Two results pin &#949;&#8320; as the proof-theoretic ordinal of '
            'Peano Arithmetic &#8212; the limit of how far PA\'s proofs of '
            'transfinite induction reach &#8212; and they run in opposite '
            'directions. Gentzen reports, crediting Hilbert-Bernays, that '
            'transfinite induction up to any ordinal strictly below '
            '&#949;&#8320; is provable in PA. And transfinite induction up to '
            '&#949;&#8320; itself is not provable in PA, which Gentzen proved '
            'directly in 1943. Neither half alone locates the boundary: a '
            'ceiling with no witnesses beneath it pins nothing, and witnesses '
            'with no ceiling pin nothing either. A third result stands behind '
            'them &#8212; transfinite induction up to &#949;&#8320; suffices '
            'to prove PA consistent (1936) &#8212; and it is also the '
            'indirect route to the unprovability half, via G&#246;del\'s '
            'theorem together with that 1936 result. This is not claimed or '
            'proved here.',
            'ZP-L shares its &#949;&#8320; with proof theory: it is Mathlib\'s Ordinal.epsilon 0 '
            '(epsilonZero, ZeroParadox/Ordinal/Gentzen.lean), and the ordinals below it are written in '
            'Cantor normal form, the notation ordinal analysis also uses (Gentzen 1943, &#167;1). What is ZP-L\'s own is the snap: '
            'a monotone map sending the tower\'s stages to c&#8320; fires nowhere below &#949;&#8320; '
            '(snap_threshold_is_epsilon_zero), and its firing at &#949;&#8320; is the hypothesis '
            'h&#949;&#8320; (ZeroParadox/Ordinal/Incompleteness.lean &#167; II). '
            'That the snap\'s least possible firing point is the ordinal of Gentzen\'s consistency proof is offered as a structural observation, not as a link between the two results.',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R-L.2: Surreal Numbers',
        [
            'Every ordinal is a surreal number (Conway, 1976), so &#949;&#8320; lives in '
            'the surreal number field No. No satisfies the axioms of a real-closed field, '
            'and by Tarski\'s completeness theorem for the theory of real-closed fields, '
            'every first-order sentence in the language of ordered fields that holds in '
            '&#8477; also holds in No, and vice versa.',
            'ZP-F (The Counterexamples) proves that the Binary Snap &#8212; the transition from &#8869; to the first non-null ordinal threshold (&#949;&#8320;, '
            'established in §V&#8211;§VII above) &#8212; cannot occur in any linearly ordered '
            'field. This result applies directly to No considered as a linearly ordered field. '
            'Note the scope: what is derived is the transition&#8217;s SHAPE and its impossibility in an ordered field.',
            'The surreals therefore contain &#949;&#8320; as an ordinal while simultaneously '
            'satisfying the density condition that blocks the Binary Snap in their ordered '
            'field structure. Both structures coexist in No: &#949;&#8320; is present as an '
            'ordinal, and the field density that blocks the snap is present in the field '
            'structure. The two results apply to different structural aspects of No.',
        ]
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark R-L.3: Hyperreals and &#321;o&#347;\'s Theorem',
        [
            'The hyperreals *&#8477; = &#8477;&#8319;/U (ultrafilter U on &#8469;) satisfy '
            'a transfer result: by &#321;o&#347;\'s theorem, every first-order sentence '
            'true in &#8477; holds in *&#8477;. &#321;o&#347;\'s theorem applies to the '
            'full first-order theory, so any first-order property of &#8477; &#8212; '
            'including field density &#8212; transfers.',
            'Field density transfers: between any two hyperreals there is another. The '
            'density condition that blocks the Binary Snap in &#8477; (proved in ZP-F) '
            'therefore holds in *&#8477; as well.',
            'The non-standard naturals *&#8469; contain infinite elements, but every '
            'infinite H &#8712; *&#8469; has a predecessor H&#8722;1 in *&#8469;. '
            '&#949;&#8320; is a limit ordinal: it has no predecessor and is the supremum '
            'of the tower below it. *&#8469; cannot host the Binary Snap not only because '
            'of field density, but because its infinite elements are successor-like rather '
            'than limit-like. The snap requires genuine limit ordinal structure.',
            'The monad of 0 in *&#8477; &#8212; the external set {&#949; : |&#949;| < 1/n '
            'for all standard n} &#8212; is external to the ultrapower. Between any two '
            'distinct elements of the monad there is another (their arithmetic mean in '
            '*&#8477;), so no discrete jump at 0 is possible in *&#8477;.',
            'Field density is an internal property of the ordered field structure of *&#8477; '
            'and transfers by &#321;o&#347;\'s theorem. Limit ordinal structure is '
            'set-theoretic and is not preserved by the ultrapower construction: *&#8469; '
            'contains only successor-like infinite elements, not limit-like ones. '
            'The two results &#8212; transfer of density, failure of limit-ordinal structure '
            '&#8212; come from different theorems.',
        ]
    ))
    E.append(sp(6))

    # ── Section IV: Cantor Normal Form Bridge ──────────────────────────────────
    print('[build_zpl] Building Section IV...')
    E += [
        hr(),
        Paragraph('Section IV: Cantor Normal Form Bridge', S['h1']),
        hr(),
    ]

    E.append(body(
        'Every ordinal below &#949;&#8320; has a unique Cantor normal form — a finite '
        'sum &#969;^e&#8321;&#183;a&#8321; + &#969;^e&#8322;&#183;a&#8322; + &#8230; '
        'with strictly decreasing exponents e&#8321; > e&#8322; > &#8230; and each '
        'coefficient a nonzero natural number (a nonzero ordinal strictly below &#969;). In Lean: '
        'NONote (Mathlib.SetTheory.Ordinal.Notation). '
        'The map cnfToZp2 sends each such ordinal to &#8484;&#8322; by structural '
        'recursion on the Cantor normal form. From tower stage 1 on, the 2-adic valuation '
        'of the image tracks ordinal height (tower_orders_agree, '
        'ZeroParadox/Ordinal/CnfBridge.lean).'))

    E.append(def_box(
        'Definition: cnfToZp2 (Gentzen.lean §IV)',
        [
            'cnfToZp2 : NONote &#8594; &#8484;&#8322;',
            'Base: cnfToZp2(0) = 0',
            'Recursive: cnfToZp2(&#969;^e &#183; n + a) = '
            '2^(v&#8322;(cnfToZp2(e)) + 1) &#183; n + cnfToZp2(a)   [n : &#8469;&#8314;]',
            'where v&#8322; denotes Lean\'s PadicInt.valuation, which sets v&#8322;(0) = 0; the recursion uses that value.',
            'Valuation of the n-th tower stage:',
            '  cnfToZp2(towerNONote 0) = 0           (Lean: PadicInt.valuation 0 = 0; the standard 2-adic valuation of 0 is +&#8734;)',
            '  cnfToZp2(towerNONote 1) = 2            (valuation 1)',
            '  cnfToZp2(towerNONote 2) = 4            (valuation 2)',
            '  cnfToZp2(towerNONote n) = 2^n          (valuation n; n &#8805; 1)',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: cnfToZp2_tower_valuation',
        [
            '&#8704; n : &#8469;, (cnfToZp2 (towerNONote n)).valuation = n',
            'The 2-adic valuation of the image of the n-th tower stage equals n (at n = 0, by Lean\'s convention PadicInt.valuation 0 = 0).',
            'Proof: by induction; successor step uses PadicInt.valuation_pow.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: cnfToZp2_valuation_unbounded',
        [
            '&#8704; k : &#8469;, &#8707; &#945; : NONote, k &#8804; (cnfToZp2 &#945;).valuation',
            'The 2-adic valuation is unbounded across ordinals below &#949;&#8320;.',
            'Proof: towerNONote k witnesses the bound.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: tower_converges_to_zero',
        [
            'Filter.Tendsto (fun n &#8614; cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0)',
            'The images of the tower stages converge to 0 = &#8869; in &#8484;&#8322;.',
            'Proof: each stage&#8217;s image cnfToZp2(towerNONote (n+1)) = 2^(n+1) in &#8484;&#8322;, '
            'so its 2-adic norm is &#8214;2&#8214;^(n+1) = (1/2)^(n+1) &#8594; 0. '
            'Uses Metric.tendsto_atTop and exists_pow_lt_of_lt_one.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Section V: Ordinal Tower Limit and Snap Threshold ──────────────────────
    print('[build_zpl] Building Section V...')
    E += [
        hr(),
        Paragraph('Section V: Ordinal Tower Limit and Snap Threshold', S['h1']),
        hr(),
    ]

    E.append(body(
        'This section connects the ordinal tower to the ZPE machine-phase snap. '
        'The cofinality theorem shows that the fundamental sequence approaches &#949;&#8320; '
        'from below. The lower-bound theorem shows that any monotone tower-aligned map '
        'must assign c&#8320; to all pre-&#949;&#8320; ordinals. A canonical witness '
        'snapping exactly at &#949;&#8320; is exhibited.'))

    E.append(import_box(
        'What this does NOT claim (§V)',
        [
            'That &#949;&#8320; is the proof-theoretic ordinal of '
            'PA (not claimed &#8212; see Remark R-L.1).',
            'Any statement about formal provability in PA.',
            'That &#949;&#8320; is the UNIQUE minimal snap boundary: '
            'snap_threshold_is_epsilon_zero shows no ordinal below &#949;&#8320; '
            'works (for maps satisfying the stated hypotheses), but does not rule out '
            'maps that snap at some ordinal strictly above &#949;&#8320;.',
            'That the snap threshold result applies to all maps Ordinal &#8594; MachinePhase '
            'regardless of the monotonicity and tower-alignment hypotheses.',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: fundamentalSeq_cofinal',
        [
            '&#8704; &#945; : Ordinal, &#945; < &#949;&#8320; &#8594; '
            '&#8707; n : &#8469;, &#945; < fundamentalSeq n',
            'The fundamental sequence is cofinal in &#949;&#8320;: for any ordinal '
            'below &#949;&#8320;, some tower stage exceeds it.',
            'Proof: &#949;&#8320; = nfp (&#969;^&#183;) 0 (epsilonZero_eq_nfp), '
            'and lt_nfp_iff gives a < nfp f b &#8596; &#8707; n, a < f^[n] b.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: snap_threshold_is_epsilon_zero',
        [
            'For any &#981; : Ordinal &#8594; MachinePhase satisfying:',
            '  (a) hmono: &#8704; &#945; &#8804; &#946;, join (&#981; &#945;) (&#981; &#946;) = &#981; &#946;  '
            '(order-non-decreasing in the ZPSemilattice sense: &#981; &#945; &#8804; &#981; &#946;)',
            '  (b) h0: &#8704; n : &#8469;, &#981; (fundamentalSeq n) = c&#8320;',
            'we have: &#8704; &#945; < &#949;&#8320;, &#981; &#945; = c&#8320;',
            'This is a lower bound: no ordinal below &#949;&#8320; is a snap point for '
            'maps satisfying (a) and (b). "Minimal" not "unique."',
            'Proof: cofinality gives a stage above &#945;; monotonicity chains '
            '&#981; &#945; &#8804; &#981;(stage) = c&#8320;; c&#8320; = &#8869; forces &#981; &#945; = c&#8320;.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: c1_epsilon_zero_identification',
        [
            '&#8707; &#981; : Ordinal &#8594; MachinePhase,',
            '  (&#8704; n : &#8469;, &#981; (fundamentalSeq n) = c&#8320;) &#8743; &#981; &#949;&#8320; = c&#8321;',
            'Witness: &#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321;.',
            'One specific map sends all tower stages to c&#8320; and &#949;&#8320; to c&#8321;.',
            'The witness map is order-non-decreasing in ZP-A\'s join order (snap_map_mono), and '
            'no map Ordinal &#8594; MachinePhase is compatible with the CNF &#8594; &#8484;&#8322; '
            'map along the tower: for every g : MachinePhase &#8594; &#8484;&#8322; the square fails, '
            'because MachinePhase has two values and the images of stages 1, 2, 3 have three distinct 2-adic '
            'valuations (the example after c1_epsilon_zero_identification in '
            'ZeroParadox/Ordinal/Gentzen.lean); through snapEmbed it fails at every stage n &#8805; 1, '
            'because snapEmbed takes only the values 1 and 0, and stage n &#8805; 1 maps to 2^n, '
            'which is neither (ZeroParadox/Ordinal/Incompleteness.lean &#167; II).',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Section VI: Kleene-Ordinal Fixed-Point Bridge ──────────────────────────
    print('[build_zpl] Building Section VI...')
    E += [
        hr(),
        Paragraph('Section VI: Kleene-Ordinal Fixed-Point Bridge', S['h1']),
        hr(),
    ]

    E.append(body(
        'The ordinal fixed-point structure (&#949;&#8320; = nfp (&#969;^&#183;) 0, '
        '&#969;^&#949;&#8320; = &#949;&#8320;) and the computational fixed-point structure '
        '(Kleene\'s recursion theorem, roger_fixed_point_stability) both carry '
        'Classical.choice in the proofs recorded here — parallel structure, not a '
        'proved isomorphism. The hypothesis hfp encodes that ordinal fixed points of &#969;^&#183; '
        'map to the snap state c&#8321;. Under this hypothesis plus monotonicity and tower '
        'alignment, &#949;&#8320; is the minimal snap threshold.'))

    E.append(result_box(
        'Theorem: snap_exactly_at_epsilon_zero',
        [
            'For any &#981; : Ordinal &#8594; MachinePhase satisfying:',
            '  (a) hmono: order-non-decreasing (join (&#981; &#945;) (&#981; &#946;) = &#981; &#946; for &#945; &#8804; &#946;)',
            '  (b) h0: every tower stage maps to c&#8320;',
            '  (c) hfp: every fixed point of &#969;^&#183; maps to c&#8321;',
            'we have: &#981; &#949;&#8320; = c&#8321; AND &#8704; &#945;, &#981; &#945; = c&#8321; &#8594; &#949;&#8320; &#8804; &#945;',
            '&#949;&#8320; is the minimal snap threshold: &#981; assigns c&#8321; first at &#949;&#8320;.',
            'Note: "minimal" not "unique." A map satisfying these hypotheses could '
            'also assign c&#8321; to ordinals above &#949;&#8320;; what is ruled out '
            'is any snap strictly before &#949;&#8320;.',
            'Proof: upper bound from hfp + epsilonZero_fixedPoint; lower bound from '
            'snap_threshold_is_epsilon_zero.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: kleene_ordinal_snap_bridge',
        [
            '&#8707; &#981; : Ordinal &#8594; MachinePhase,',
            '  (&#8704; n : &#8469;, &#981; (fundamentalSeq n) = c&#8320;) &#8743;',
            '  (&#8704; &#945;, &#969;^&#945; = &#945; &#8594; &#981; &#945; = c&#8321;) &#8743;',
            '  &#981; &#949;&#8320; = c&#8321; &#8743;',
            '  &#8704; &#945;, &#981; &#945; = c&#8321; &#8594; &#949;&#8320; &#8804; &#945;',
            'Witness: &#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321;.',
            'Note: the theorem name refers to the informal §VI conceptual parallel '
            'between Kleene recursion fixed points and ordinal fixed points of &#969;^&#183;. '
            'The theorem itself is purely ordinal — no Code or eval appears.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Section VII: Canonical Snap Map — Full Closure ─────────────────────────
    print('[build_zpl] Building Section VII...')
    E += [
        hr(),
        Paragraph('Section VII: Canonical Snap Map — Full Closure', S['h1']),
        hr(),
    ]

    E.append(body(
        'The canonical threshold map &#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321; '
        'satisfies all three conditions of snap_exactly_at_epsilon_zero (hmono, h0, hfp). '
        'For this specific map, the snap identification is unconditional: all five conditions '
        'are simultaneously verified without free hypotheses.'))

    E.append(result_box(
        'Theorem: snap_map_mono',
        [
            '&#8704; &#945; &#946; : Ordinal, &#945; &#8804; &#946; &#8594;',
            '  join (if &#945; < &#949;&#8320; then c&#8320; else c&#8321;)',
            '       (if &#946; < &#949;&#8320; then c&#8320; else c&#8321;) =',
            '  if &#946; < &#949;&#8320; then c&#8320; else c&#8321;',
            'The canonical map is order-non-decreasing.',
            'Proof: four cases (&#945;/&#946; vs &#949;&#8320;). The case &#945; &#8805; &#949;&#8320; '
            'with &#946; < &#949;&#8320; is impossible by &#945; &#8804; &#946;. '
            'Each live case closes by rfl from the MachinePhase join definition.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: epsilon_zero_snap_canonical',
        [
            '&#8707; &#981; : Ordinal &#8594; MachinePhase,',
            '  (&#8704; &#945; &#946;, &#945; &#8804; &#946; &#8594; join (&#981; &#945;) (&#981; &#946;) = &#981; &#946;) &#8743;   [hmono]',
            '  (&#8704; n : &#8469;, &#981; (fundamentalSeq n) = c&#8320;) &#8743;              [h0]',
            '  (&#8704; &#945;, &#969;^&#945; = &#945; &#8594; &#981; &#945; = c&#8321;) &#8743;          [hfp]',
            '  &#981; &#949;&#8320; = c&#8321; &#8743;                                           [snap]',
            '  &#8704; &#945;, &#981; &#945; = c&#8321; &#8594; &#949;&#8320; &#8804; &#945;                  [minimality]',
            'All five conditions verified for the explicit witness '
            '&#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321;, with no free hypotheses.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(4))

    E.append(result_box(
        'Theorem: snap_zp2_correspondence',
        [
            'Four independent facts about the same tower sequence:',
            '  (i)   &#8704; n : &#8469;, fundamentalSeq n < &#949;&#8320;',
            '  (ii)  &#8704; n : &#8469;, &#981; (fundamentalSeq n) = c&#8320;   where &#981; is the canonical map',
            '  (iii) Filter.Tendsto (fun n &#8614; cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0)',
            '  (iv)  &#981; &#949;&#8320; = c&#8321;',
            'The same tower sequence witnesses both the ordinal approach to &#949;&#8320; '
            'and the 2-adic approach to 0. This is a co-witness, not an identity '
            '(cnf_bridge_type_boundary, ZeroParadox/Ordinal/CnfBridge.lean): &#949;&#8320; and the '
            '&#8484;&#8322; zero live in different types with no coercion between them, so an '
            'identity between them fails to elaborate.',
            'Proof: &#10216;epsilonZero_tower_lt, fun n &#8614; if_pos &#8230;, '
            'tower_converges_to_zero, if_neg (lt_irrefl &#949;&#8320;)&#10217;',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Remaining Gap ───────────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('The Bridge: What Is Formal and What Is Assumed', S['h1']),
        hr(),
    ]

    E.append(import_box(
        'What the Bridge Supplies',
        [
            'c&#8321; is a MachinePhase state and &#949;&#8320; an ordinal, so an identity between them '
            'is not a well-formed statement; the formal link runs through maps: a canonical map '
            'Ordinal &#8594; MachinePhase and snapEmbed : MachinePhase &#8594; &#8484;&#8322;.',
            'What is proved: a canonical map Ordinal &#8594; MachinePhase assigns c&#8321; '
            'exactly at &#949;&#8320; and nowhere earlier.',
            'Two of the three pieces a type bridge from the ordinals through MachinePhase to '
            '&#8484;&#8322; was expected to need are built, in ZPM '
            '(ZeroParadox/Ordinal/Incompleteness.lean &#167;I&#8211;&#167;II), and the third is '
            'not supplied by them:',
            '  (1) snapEmbed : MachinePhase &#8594; &#8484;&#8322; exists, sending c&#8320; '
            '&#8614; 1 and c&#8321; &#8614; 0 &#8212; the snap state to 2-adic zero, the pre-snap '
            'state to a unit (snapEmbed_c0, snapEmbed_c1, both by rfl)',
            '  (2) snapEmbed_mul_morphism proves snapEmbed (join a b) = snapEmbed a &#215; '
            'snapEmbed b, carrying join to multiplication because c&#8321; absorbs joins as 0 '
            'absorbs products. That is an absorbing-element morphism, and it does not send '
            'bottom to bottom in the Scale.lean chart (&#8869; = 0): there the bottom role is '
            'filled by 0 (a ZPSemilattice on &#8484;&#8322; with &#8869; = 0 is built in '
            'ZeroParadox/Valuation/Scale.lean &#167; V), and snapEmbed sends c&#8320; to 1 '
            '(snapEmbed_c0); in the multiplicative reading snapEmbed c&#8320; = 1 is the identity '
            '(1 &#183; x = x), as c&#8320; is the identity of join, and that reading is not a '
            'ZPSemilattice, since multiplication on &#8484;&#8322; is not idempotent '
            '(2 &#183; 2 &#8800; 2)',
            '  (3) not supplied &#8212; for a map &#981; sending the tower&#8217;s stages to c&#8320; (h0), '
            'continuity of snapEmbed &#8728; &#981; along the tower would '
            'force &#981; &#949;&#8320; = c&#8320;, the opposite (the examples after snap_unconditional, '
            'ZeroParadox/Ordinal/Incompleteness.lean &#167; II), while the cnfToZp2 images of the stages '
            'do tend to snapEmbed c&#8321; = 0; the placement enters as h&#949;&#8320;.',
            'So hfp is derived rather than assumed: hfp_from_epsilon_zero obtains it from '
            'monotonicity together with h&#949;&#8320; : &#981; &#949;&#8320; = c&#8321;, and '
            'snap_unconditional uses it in place of the free hypothesis of '
            'snap_exactly_at_epsilon_zero. h&#949;&#8320; (&#981; &#949;&#8320; = c&#8321;; in the '
            '&#8484;&#8322; chart, snapEmbed (&#981; &#949;&#8320;) = 0) is the snap&#8217;s occurrence at '
            '&#949;&#8320;, taken as a hypothesis: of the infinitely many admissible firing points that '
            'monotonicity and tower alignment (every tower stage sent to c&#8320;) leave open, '
            'h&#949;&#8320; selects the least, and so fixes &#981; uniquely '
            '(ZeroParadox/Ordinal/Incompleteness.lean &#167; II). Whether Classical.choice is forced by '
            'the metric collapse is a separate open question (ZeroParadox/Ordinal/SyntacticCollapse.md). '
            'The canonical witness (epsilon_zero_snap_canonical) '
            'satisfies all five conditions without any such type bridge.',
        ]
    ))
    E.append(sp(6))

    # ── Theorem Table ───────────────────────────────────────────────────────────
    print('[build_zpl] Building theorem table...')
    E += [
        hr(),
        Paragraph('Theorem Summary', S['h1']),
        hr(),
    ]

    E.append(data_table(
        headers=['Theorem', 'Section', 'Status'],
        rows_data=[
            ['roger_fixed_point_stability', '§II', 'Proved ✓'],
            ['epsilonZero_fixedPoint', '§III', 'Proved ✓'],
            ['epsilonZero_eq_nfp', '§III', 'Proved ✓'],
            ['epsilonZero_eq_iSup', '§III', 'Proved ✓'],
            ['epsilonZero_tower_lt', '§III', 'Proved ✓'],
            ['epsilonZero_le_fixedPoint', '§III', 'Proved ✓'],
            ['fundamentalSeq_strictMono', '§III', 'Proved ✓'],
            ['tower_stage_zero / _one / _two', '§III', 'Proved ✓'],
            ['towerNONote_repr', '§IV', 'Proved ✓'],
            ['cnfToZp2_tower_valuation', '§IV', 'Proved ✓'],
            ['cnfToZp2_valuation_unbounded', '§IV', 'Proved ✓'],
            ['fundamentalSeq_zp2_converges', '§IV', 'Proved ✓'],
            ['tower_converges_to_zero', '§IV', 'Proved ✓'],
            ['zpe_snap_ordinal_correspondence', '§V', 'Proved ✓'],
            ['epsilonZero_tower_bound', '§V', 'Proved ✓'],
            ['c1_epsilon_zero_identification', '§V', 'Proved ✓'],
            ['fundamentalSeq_cofinal', '§V', 'Proved ✓'],
            ['snap_threshold_is_epsilon_zero', '§V', 'Proved ✓'],
            ['snap_exactly_at_epsilon_zero', '§VI', 'Proved ✓'],
            ['kleene_ordinal_snap_bridge', '§VI', 'Proved ✓'],
            ['snap_map_mono', '§VII', 'Proved ✓'],
            ['epsilon_zero_snap_canonical', '§VII', 'Proved ✓'],
            ['snap_zp2_correspondence', '§VII', 'Proved ✓'],
        ],
        col_widths=[220, 60, 150],
    ))
    E.append(sp(4))

    E.append(axiom_box(
        'Axiom Purity',
        [
            'Every theorem in the Theorem Summary above carries axiom footprint: '
            '[propext, Classical.choice, Quot.sound]. Section I\'s table and ZP-K Section IV '
            'record where the ZP layers differ &#8212; Section I\'s own ZPJ/K row names '
            'bot_self_mem, which measures no axioms.',
            'These are standard Mathlib infrastructure axioms (ordinal theory, p-adic '
            'analysis, computability). They are not ZP-L commitments.',
            'The footprints across the ZP layers are not uniform; ZP-K Section IV tabulates the '
            'measurements. In the computability layer, Rogers\' fixed-point theorem as Mathlib '
            'states it carries Classical.choice in its statement, through Mathlib\'s numbering of '
            'program codes (the Denumerable Code instance; ZeroParadox/Computability/Kleene.md '
            '§ VIII). ZP-K\'s machinePhaseKleene also picks botCode with Classical.choose, which is '
            'what makes that instance noncomputable.',
            'Zero sorry in Gentzen.lean.',
        ]
    ))
    E.append(sp(6))

    print('[build_zpl] Building document...')
    doc.build(E)
    print(f'[build_zpl] Done: {out_path}')


if __name__ == '__main__':
    build()
