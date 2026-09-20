"""
Zero Paradox — ZP-L: Incomputability Convergence PDF Builder
Version 1.14 | September 2026
v1.14 / comp v1.9: GATE ROUNDS 3-4 REMEDIATION (2026-09-19). ⚠ The first attempt at the Axiom Purity fix wrote "That is uniform within this document", which the document contradicts twice - the abstract and Section I, whose ZPJ/K row names bot_self_mem, measured at no axioms. Anchoring an unanchored referent produced the opposite one-chart sentence, which is R-TWOPOLE's measured shape. The box now states only what was measured (every theorem in the Theorem Summary carries the triple) and points at where the layers differ, naming that row. The Axiom Purity box's "Every theorem in the summary above carries the triple" sat three lines from "the footprints are not uniform", both true but with unanchored referents, reading as self-retraction; the first is now anchored to the Theorem Summary and the second to the ZP layers. Page 1's "axiom footprint [...] throughout" had the same unanchored shape and now names Gentzen.lean. Companion: "Every ZP-L theorem carries the triple" was an unscoped universal while the paragraph set scope wider than ZP-L's own file - ZP-L cites Snap.lean, whose t_snap_derived is axiom-free - and is now scoped to Gentzen.lean and names it. ⚠ v1.13's content changed after its version was cut and the PDFs were rebuilt without an increment; this bump is that correction (R-REGISTER: a hash mismatch means the bump was skipped, not that a rebuild is needed).
v1.13 / comp v1.8: ZPK-BED-2, BEDROCK IN A DEPOSITED PDF (Tim ruling, 2026-09-19). Sites in this document and its companion asserted one axiom footprint across all the settings, and the Section I table refutes that: its ZPJ/K cell names bot_self_mem (AFA), which measures no axioms, beside botCode (Kleene), which carries them. "Required" is a necessity claim no #print axioms run can earn - necessity takes a reduction to a taboo (ChoiceCannotBe.lean § IV) - and "a constructive alternative was not found" is false, the alternative being the row's own AFA witness. Sites here POINT at ZP-K Section IV, which holds a dated measurement table rather than a rule (Tim ruling, 2026-09-19), instead of restating anything. Also removed: the "Why K is Absent from Lean" reason (uncomputability does not explain absence from Lean - the corpus carries ~200 noncomputable declarations, two of them in Gentzen.lean), a theorem count that counted table ROWS, and "24 theorems proved" on page 1. Prose no longer enumerates the settings (Tim ruling) - the table defines them, and three prose sites had enumerated them three different ways while every claim was quantified over the set. The table is unchanged, per the ruling. ⚠ SCOPE OF THE SEARCH, stated instead of a count (R-NOTINLIB): check_paths.py --full --claim over .md + .lean + tracked .py + the 40 rendered PDFs, phrasings varied by POLARITY, PART OF SPEECH and VOCABULARY. Post-mortem: .claude-local/notes/axiom_footprint_measured_2026-09-19.md.
v1.12: CLASSICAL.CHOICE MODAL (Tim ruling, gate round 5, 2026-09-15): the Axiom Purity box's 'Its presence is expected and documented, not incidental.' read as a necessity claim beside 'essential is not measured'; it now reads 'Its presence is expected and documented.'
v1.11: CLASSICAL.CHOICE PROVENANCE (Tim ruling, gate round 5, 2026-09-15): the Axiom Purity box said the computability layer's choice belongs to ZP-K's instance. Measured: Classical.choice is carried by the statements' types through Mathlib's Denumerable Code, and a computable constant-code instance carries it too; Classical.choose is what makes machinePhaseKleene noncomputable; essentiality is not measured. The box now says that.
v1.10: DA-1/KLEENE CLASS, GATE ROUND 4 SECOND PASS (Tim rulings, 2026-09-15): Section II's body still equated Rogers' fixed-point theorem with Kleene's second recursion theorem and dropped 'total'; it now names Mathlib fixed_point, inter-derivable with fixed_point2, for any total computable transformation. The verification box said Classical.choice is load-bearing; in the computability layer the choice belongs to ZP-K's instance (its choice of botCode), and a computable instance with a constant code also exists.
v1.9: DA-1/KLEENE CLASS, GATE ROUND 4 (Tim rulings, 2026-09-15): the overview equated Rogers' fixed-point theorem with Kleene's second recursion theorem; it now names Rogers' theorem as Mathlib fixed_point, for a total computable transformation, inter-derivable with Kleene's second recursion theorem (fixed_point2), as Gentzen.lean section II already records. Remark 'Why K is Absent' said the AFA/Kleene route is 'a provable path'; its Kleene step is a KleeneStructure requirement, and it now says so.
v1.8: DECISION BATCH REMEDIATION AFTER GATE ROUND 2 (2026-09-15): the surreals note (Remark R-L.2) sits in the ordered-field setting, where the snap is proved impossible (f_snap_impossible); the clause saying what occurrence follows from is removed there, and the sentence says only what is derived: the shape and its impossibility in an ordered field.
v1.7: DECISION BATCH REMEDIATION ROUND 2 (Tim rulings, 2026-09-15): the surreals note said 'occurrence is a framework commitment'; now the Snap occurring follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2).
v1.6: FORCING OVERCLAIM RETRACTED. The document described the snap as a forced transition without ever hedging occurrence. T-SNAP fixes the transition's SHAPE; Order/Snap.lean's tsnap_holds_but_nothing_moves proves it holds in a model where nothing moves, so occurrence is a framework commitment. Prose only.
v1.5: axiom-footprint list label corrected - t_comp described as a four-way equivalence; it proves three, the computational face being an assumption rather than a clause. Footprint figures themselves unchanged (measured, not quoted).
v1.4: "Rogers' fixed-point theorem" corrected from "Roger's" (Hartley Rogers) — Section II heading and prose.
v1.3: rendered Lean citations synced to post-reorg files/namespaces the earlier passes missed (bare ZPx.lean / ZeroParadox.ZPx.* / ZPx.<decl>; SSOT-driven).
v1.1: Rendered version changelog removed (C1 sweep). Fixed 3 null glyphs — subscript-letter entities
&#8345; (ₙ) and &#8338; (ₒ) bypass fix() and are absent from STIX; replaced with <sub> markup.
v1.0: Initial release. All §I–§VII theorems proved sorry-free in Lean 4.
Axiom footprint: [propext, Classical.choice, Quot.sound] throughout.
Follows all rules in scripts/PDF_Rendering_Standards.md.
"""

import os
from zp_utils import *

VERSION = '1.14'
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
        'Fourth, ordinals below &#949;&#8320; encode into &#8484;&#8322; via their Cantor '
        'normal form, and as the tower stages approach &#949;&#8320;, their 2-adic '
        'encodings converge to 0 = &#8869;.'))
    E.append(body(
        'The central result (§VII) is the canonical snap map: '
        '&#981; &#945; = if &#945; < &#949;&#8320; then c&#8320; else c&#8321; '
        'simultaneously satisfies all five conditions — monotone, tower-aligned, '
        'fixed-point-respecting, snapping at &#949;&#8320;, and &#949;&#8320; minimal. '
        'All conditions are verified without free hypotheses for this witness. '
        'Proved sorry-free, axiom footprint [propext, Classical.choice, '
        'Quot.sound] throughout.'))
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
            ['ZPI', 'Algorithmic IT', 'K(S<sub>n</sub>|n)/|S<sub>n</sub>| &#8594; 1; K uncomputable'],
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
            'ZP-L inherits that footprint throughout. Where it enters is recorded in '
            'ZP-K Section IV.',
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
        'sum a&#8321;&#183;&#969;^e&#8321; + a&#8322;&#183;&#969;^e&#8322; + &#8230; '
        'with strictly decreasing exponents e&#8321; > e&#8322; > &#8230; and each '
        'coefficient a nonzero natural number (a nonzero ordinal strictly below &#969;). In Lean: '
        'NONote (Mathlib.SetTheory.Ordinal.Notation). '
        'The encoding cnfToZp2 maps each such ordinal to &#8484;&#8322; via structural '
        'recursion on the Cantor normal form.'))

    E.append(def_box(
        'Definition: cnfToZp2 (Gentzen.lean §IV)',
        [
            'cnfToZp2 : NONote &#8594; &#8484;&#8322;',
            'Base: cnfToZp2(0) = 0',
            'Recursive: cnfToZp2(&#969;^e &#183; n + a) = '
            '2^(v&#8322;(cnfToZp2(e)) + 1) &#183; n + cnfToZp2(a)   [n : &#8469;&#8314;]',
            'where v&#8322; denotes the 2-adic valuation.',
            'Valuation of the n-th tower stage:',
            '  cnfToZp2(towerNONote 0) = 0           (Lean: PadicInt.valuation 0 = 0; standard: v&#8322;(0) = +&#8734;)',
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
            'Ordinal &#8594;<sub>o</sub> MachinePhase compatible with the CNF &#8594; &#8484;&#8322; '
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
            'Every theorem in the Theorem Summary above carries axiom footprint: '
            '[propext, Classical.choice, Quot.sound]. Section I\'s table and ZP-K Section IV '
            'record where the ZP layers differ &#8212; Section I\'s own ZPJ/K row names '
            'bot_self_mem, which measures no axioms.',
            'These are standard Mathlib infrastructure axioms (ordinal theory, p-adic '
            'analysis, computability). They are not ZP-L commitments.',
            'The footprints are not uniform; ZP-K Section IV tabulates the measurements. '
            'In the computability layer Classical.choice is reached through '
            'Mathlib\'s numbering of program codes '
            '(Denumerable Code): it is present even in a computable instance with a constant '
            'code. ZP-K\'s machinePhaseKleene also picks botCode with Classical.choose, which is '
            'what makes that instance noncomputable. Whether the numbering\'s footprint is '
            'essential is not measured. Its presence is expected and documented.',
            'Zero sorry in Gentzen.lean. Verified: lake build, May 2026.',
        ]
    ))
    E.append(sp(6))

    print('[build_zpl] Building document...')
    doc.build(E)
    print(f'[build_zpl] Done: {out_path}')


if __name__ == '__main__':
    build()
