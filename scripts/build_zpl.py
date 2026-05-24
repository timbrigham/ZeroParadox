"""
Zero Paradox — ZP-L: Incomputability Convergence PDF Builder
Version 1.0 | May 2026
v1.0: Initial release. All §I–§VII theorems proved sorry-free in Lean 4.
Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.0'


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
        Paragraph('Version ' + VERSION + ' | May 2026', S['subtitle']),
        Paragraph(
            '<i>v1.0: Initial release. '
            'All theorems §I&#8211;§VII proved sorry-free in Lean 4. '
            'Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.</i>',
            S['note']),
        sp(10),
        hr(),
        sp(4),
    ]

    E.append(body(
        'ZP-L establishes four results connecting the formal axioms of the ZP framework '
        'to standard results in ordinal theory and computability. '
        'First, Classical.choice appears at the non-constructive diagonal step in each '
        'of the four mathematical settings of the ZP framework — topology, information '
        'theory, set theory, and computation. Second, Roger\'s fixed-point theorem '
        '(Kleene\'s second recursion theorem) is formalized as a wrapper, formalizing the '
        'computational fixed-point structure. Third, the ordinal &#949;&#8320; is fully '
        'characterized as the first fixed point of &#945; &#8614; &#969;^&#945; and the '
        'limit of the tower &#969;, &#969;^&#969;, &#969;^&#969;^&#969;, &#8230;. '
        'Fourth, ordinals below &#949;&#8320; encode into &#8484;&#8322; via their Cantor '
        'normal form, and as the tower stages approach &#949;&#8320;, their 2-adic '
        'encodings converge to 0 = &#8869;.'))
    E.append(body(
        'The central result (§VII) is the canonical snap map: '
        '&#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321; '
        'simultaneously satisfies all five conditions — monotone, tower-aligned, '
        'fixed-point-respecting, snapping at &#949;&#8320;, and &#949;&#8320; minimal. '
        'All conditions are verified without free hypotheses for this witness. '
        '24 theorems proved, zero sorry, axiom footprint [propext, Classical.choice, '
        'Quot.sound] throughout.'))
    E.append(hr())

    # ── Section I: Axiom Footprint Convergence ─────────────────────────────────
    print('[build_zpl] Building Section I...')
    E += [
        Paragraph('Section I: Axiom Footprint Convergence', S['h1']),
        hr(),
    ]

    E.append(body(
        'Non-constructibility appears in four mathematical settings across the ZP framework. '
        'Classical.choice is required at each diagonal step in these proofs — '
        'a constructive alternative was not found in any of the four settings.'))

    E.append(data_table(
        headers=['Layer', 'Formal Language', 'Expression of non-constructibility'],
        rows_data=[
            ['ZPB', 'Topology', 'C3: no continuous path &#8869; &#8594; x &#8800; &#8869;'],
            ['ZPC', 'Information Theory', 'L-INF: infinite surprisal at &#8869;'],
            ['ZPJ/K', 'Set Theory + Computation', 'bot_self_mem (AFA); botCode (Kleene)'],
            ['ZPI', 'Algorithmic IT', 'K(S&#8345;|n)/|S&#8345;| &#8594; 1; K uncomputable'],
        ],
        col_widths=[50, 100, 280],
    ))
    E.append(sp(6))

    E.append(remark_box(
        'Remark: Why K is Absent from Lean',
        [
            'Kolmogorov complexity K is not computed in Lean in this framework. '
            'Its existence as a total function requires Classical.choice — '
            'exactly the axiom Nat.Partrec.Code.fixed_point&#8322; already uses in ZP-K. '
            'The AFA/Kleene route reaches the same fixed-point structure via a provable '
            'path without requiring K to be explicitly computed.',
            'Axiom footprint evidence — the following ZP-K theorems all carry '
            '[propext, Classical.choice, Quot.sound]:',
            '  ZPK.t_comp (T-COMP four-way equivalence)',
            '  ZPK.da1_paths_unified',
            '  ZPK.isComputationalQuine_undecidable',
            '  ZPK.infinite_quine_family',
            'The Classical.choice entry is the computational expression of the diagonal. '
            'ZP-L inherits this footprint throughout.',
        ]
    ))
    E.append(sp(6))

    # ── Section II: Roger Fixed-Point Stability ─────────────────────────────────
    print('[build_zpl] Building Section II...')
    E += [
        hr(),
        Paragraph('Section II: Roger Fixed-Point Stability', S['h1']),
        hr(),
    ]

    E.append(body(
        'Roger\'s fixed-point theorem (also known as Kleene\'s second recursion theorem) '
        'states that any computable transformation of a code has a behavioral fixed point: '
        'a code c such that running f(c) and running c produce the same partial function. '
        'For any computable transformation, at least one fixed-point code exists.'))

    E.append(result_box(
        'Theorem: roger_fixed_point_stability (ZPL.lean §II)',
        [
            'For any computable f : Code &#8594; Code,',
            '&#8203;  &#8707; c : Code, eval (f c) = eval c',
            'Proof: wrapper around ZPK.roger_fixed_point_exists.',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
            'Note: this is an existential result. The specific code c is not '
            'constructively produced; Classical.choice selects it. This is the '
            'same non-constructive step that appears across all ZP layers (§I).',
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
        'Definitions (ZPL.lean §III)',
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
            'Gentzen\'s theorem (1936) establishes that &#949;&#8320; is the '
            'proof-theoretic ordinal of Peano Arithmetic: PA can prove transfinite '
            'induction for any ordinal strictly below &#949;&#8320;, but not for '
            '&#949;&#8320; itself. This is not claimed or proved here.',
            'ZP-L derives &#949;&#8320; as the snap threshold from ordinal fixed-point '
            'structure, independently of proof theory. Both derivations locate the same '
            'boundary: the ordinal where &#969;-tower self-iteration becomes self-limiting. '
            'No claim is made that this alignment is more than a structural observation.',
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
        'expression a&#8321;&#183;&#969;^e&#8321; + a&#8322;&#183;&#969;^e&#8322; + &#8230; + a&#8345;&#183;&#969;^e&#8345; '
        'with e&#8321; > e&#8322; > &#8230; > e&#8345; and a&#7522; < &#969;. In Lean: '
        'NONote (Mathlib.SetTheory.Ordinal.Notation). '
        'The encoding cnfToZp2 maps each such ordinal to &#8484;&#8322; via structural '
        'recursion on the Cantor normal form.'))

    E.append(def_box(
        'Definition: cnfToZp2 (ZPL.lean §IV)',
        [
            'cnfToZp2 : NONote &#8594; &#8484;&#8322;',
            'Base: cnfToZp2(0) = 0',
            'Recursive: cnfToZp2(&#969;^e &#183; n + a) = '
            '2^(v&#8322;(cnfToZp2(e)) + 1) &#183; n + cnfToZp2(a)',
            'where v&#8322; denotes the 2-adic valuation.',
            'Valuation of the n-th tower stage:',
            '  cnfToZp2(towerNONote 0) = 0           (valuation 0)',
            '  cnfToZp2(towerNONote 1) = 2            (valuation 1)',
            '  cnfToZp2(towerNONote 2) = 4            (valuation 2)',
            '  cnfToZp2(towerNONote n) = 2^n          (valuation n)',
        ]
    ))
    E.append(sp(6))

    E.append(result_box(
        'Theorem: cnfToZp2_tower_valuation',
        [
            '&#8704; n : &#8469;, (cnfToZp2 (towerNONote n)).valuation = n',
            'The 2-adic valuation of the n-th tower stage encoding equals n.',
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
            'The tower encodings converge to 0 = &#8869; in &#8484;&#8322;.',
            'Proof: each stage cnfToZp2(towerNONote (n+1)) = 2^(n+1) in &#8484;&#8322;, '
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
            'Gentzen\'s theorem: that &#949;&#8320; is the proof-theoretic ordinal of '
            'PA (not claimed — see Remark R-L.1).',
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
            'The stronger structural claim — an order-preserving morphism '
            'Ordinal &#8594;&#8338; MachinePhase compatible with the CNF &#8594; &#8484;&#8322; '
            'encoding — remains outside Lean scope: no type bridge between Ordinal '
            'and MachinePhase is defined in this library.',
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
        '(Kleene\'s recursion theorem, roger_fixed_point_stability) both require '
        'Classical.choice at their non-constructive step — parallel structure, not a '
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
            'and the 2-adic approach to 0. The full structural identification '
            '(&#949;&#8320; &#8596; &#8869; via a type bridge) remains outside Lean scope — see §V.',
            'Proof: &#10216;epsilonZero_tower_lt, fun n &#8614; if_pos &#8230;, '
            'tower_converges_to_zero, if_neg (lt_irrefl &#949;&#8320;)&#10217;',
            'Lean purity: [propext, Classical.choice, Quot.sound]. ✓',
        ]
    ))
    E.append(sp(6))

    # ── Remaining Gap ───────────────────────────────────────────────────────────
    E += [
        hr(),
        Paragraph('Remaining Formal Gap', S['h1']),
        hr(),
    ]

    E.append(import_box(
        'The Remaining Gap',
        [
            'The identification of ZPE\'s MachinePhase element c&#8321; with the ordinal '
            '&#949;&#8320; via a formal type bridge remains outside Lean scope.',
            'What is proved: a canonical map Ordinal &#8594; MachinePhase assigns c&#8321; '
            'exactly at &#949;&#8320; and nowhere earlier. What is not proved: a canonical '
            'ZPSemilattice morphism MachinePhase &#8594; &#8484;&#8322; that would connect '
            'ZPE\'s &#8869; = c&#8320; to ZPB\'s &#8869; = 0 formally.',
            'Such a bridge would require:',
            '  (1) snapEmbed : MachinePhase &#8594; &#8484;&#8322; mapping c&#8320; &#8614; 0, c&#8321; &#8614; 1',
            '  (2) proof that snapEmbed is join-preserving',
            '  (3) a bridge theorem deriving hfp from tower_converges_to_zero via snapEmbed',
            'This would make hfp a theorem rather than a hypothesis in '
            'snap_exactly_at_epsilon_zero. The canonical witness (epsilon_zero_snap_canonical) '
            'satisfies all five conditions without this bridge; the bridge would close '
            'the gap between the two formal instances of &#8869; across ZPE and ZPB.',
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
            'All 23 theorems carry axiom footprint: [propext, Classical.choice, Quot.sound].',
            'These are standard Mathlib infrastructure axioms (ordinal theory, p-adic '
            'analysis, computability). They are not ZP-L commitments.',
            'Classical.choice is load-bearing: it is the formal non-constructivity '
            'appearing at the diagonal step in each ZP layer (§I). Its presence is '
            'expected and documented, not incidental.',
            'Zero sorry in ZPL.lean. Verified: lake build, May 2026.',
        ]
    ))
    E.append(sp(6))

    print('[build_zpl] Building document...')
    doc.build(E)
    print(f'[build_zpl] Done: {out_path}')


if __name__ == '__main__':
    build()
