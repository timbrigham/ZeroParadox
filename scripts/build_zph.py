"""
Zero Paradox — ZP-H: Categorical Bridge PDF Builder
Version 1.47 | November 2026
"""

import os
from zp_utils import *

VERSION = '1.47'
FIRST_RELEASED = 'April 2026'


def label_box_status(title, status_line, rows_list):
    """Box with blue header, italic status sub-row, then content rows."""
    data = [
        [Paragraph(fix(title), S['label'])],
        [Paragraph(fix(status_line), S['cellI'])],
    ]
    for r in rows_list:
        data.append([Paragraph(fix(r), S['cell'])])
    ts = TableStyle([
        ('BACKGROUND',    (0,0), (-1,0),  BLUE),
        ('BACKGROUND',    (0,1), (-1,1),  BLUE_LITE),
        ('BACKGROUND',    (0,2), (-1,-1), GREY_LITE),
        ('TEXTCOLOR',     (0,0), (-1,0),  WHITE),
        ('BOX',           (0,0), (-1,-1), 0.5, BLUE),
        ('LINEBELOW',     (0,0), (-1,0),  0.5, BLUE),
        ('LINEBELOW',     (0,1), (-1,-2), 0.5, colors.HexColor('#CCCCCC')),
        ('TOPPADDING',    (0,0), (-1,-1), 5),
        ('BOTTOMPADDING', (0,0), (-1,-1), 5),
        ('LEFTPADDING',   (0,0), (-1,-1), 8),
        ('RIGHTPADDING',  (0,0), (-1,-1), 8),
        ('VALIGN',        (0,0), (-1,-1), 'TOP'),
    ])
    t = Table(data, colWidths=[TW], repeatRows=1)
    t.setStyle(ts)
    return t


def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-H_Categorical_Bridge.pdf')
    print(f'[build_zph] Output: {out_path}')
    doc = make_doc(out_path, 'ZP-H: Categorical Bridge', 'ZP-H: Categorical Bridge',
                   'Version ' + VERSION)
    E = []

    print('[build_zph] Building title block...')
    # ── TITLE BLOCK ──────────────────────────────────────────────────────────
    E += [
        sp(12),
        Paragraph('THE ZERO PARADOX', S['title']),
        Paragraph('ZP-H: Categorical Bridge', S['subtitle']),
        Paragraph(version_line(FIRST_RELEASED, VERSION), S['bodyI']),
        sp(8),
        hr(),
        sp(4),
    ]

    E += [
        body('This document connects ZP-G (Category Theory) to ZP-A through ZP-E. Its function is '
             'exactly analogous to ZP-E\'s role in the original framework: ZP-E connected the four '
             'domain documents to each other; ZP-H connects the categorical generalization back to '
             'those four domain documents. Every cross-framework claim is traced to a theorem in '
             'ZP-G or ZP-A through ZP-E, plus an explicit bridge axiom where required. No floating '
             'connections.'),
        body('ZP-H inherits all open items from ZP-G with their original labels. The four open '
             'questions from ZP-G — OQ-G1 through OQ-G4 — are the primary targets of this document. '
             'OQ-G2, OQ-G3, and OQ-G4 are resolved here. OQ-G1 is resolved in ZP-G via '
             'D7\' and I-KC. All four OQ-G items are now closed.'),
        body('Sequencing note: ZP-H introduces one new definition (D-H1: the morphisms of C) that '
             'was deliberately omitted from ZP-G to keep that document domain-independent. This '
             'definition belongs here because it is instantiation-specific: the morphisms of C are '
             'defined by what the functor constructions require, not by the abstract category itself.'),
        sp(4),
        hr(),
    ]

    print('[build_zph] Building Section I: Imported Results...')
    # ── I. IMPORTED RESULTS ──────────────────────────────────────────────────
    E.append(Paragraph('I. Imported Results', S['h1']))
    E.append(Paragraph('1.1 From ZP-G', S['h2']))

    E.append(label_box_status(
        'Import Registry IR-G — Closed Results from ZP-G v1.1',
        'Status: Valid — Received',
        [
            'D1: Category (objects, morphisms, composition, identity, associativity, unit laws)',
            'D2: Morphism uniqueness notation (&#8707;!)',
            'D3: Initial object 0 — unique morphism &#953;<sub>X</sub>: 0 &#8594; X for all X',
            'D4: Terminal object — defined for exclusion only',
            'D5: Morphism chain from 0',
            'D6: Functor — object map, morphism map, preservation of composition and identity',
            'D7\': Native categorical surprisal I(f) = K(x<sub>B</sub>|x<sub>A</sub>) via I-KC (replaces D7/BA-G1 from v1.0)',
            'I-KC: Conditional Kolmogorov complexity K(x|y) imported from ZP-C — named dependency, not bridge axiom',
            'AX-G1: Asymmetry Axiom — C has initial object 0, no terminal object',
            'AX-G2: Source Asymmetry — hom(X, 0) = <font name="DV">&#8709;</font> for X not isomorphic to 0',
            'R-BA: Leinster categorical entropy characterization [Remark — BA-G1 demoted from Bridge Axiom in ZP-G v1.1. No longer a theorem premise.]',
            'T1: Initial object unique up to unique isomorphism',
            'T2: Universal Constituent — &#8704;X &#8712; ob(C), &#8707;! &#953;<sub>X</sub>: 0 &#8594; X',
            'T3: Unreachability — hom(X, 0) = <font name="DV">&#8709;</font> for X not isomorphic to 0',
            'T4: Chains are forward-only — no chain returns to 0',
            'T5: Functors preserve initial objects [OQ-G2 closed in ZP-H T-H1]',
            'T6: Informational singularity of 0 — outward surprisal accumulates; inward undefined [rebuilt in ZP-G v1.1 on D7\'; BA-G1 not a dependency]',
            'T7: Categorical Zero Paradox — closing theorem of ZP-G',
            'OQ-G1: Closed in ZP-G v1.1 via D7\' (native categorical surprisal) and I-KC (Kolmogorov import from ZP-C). BA-G1 demoted to remark R-BA.',
        ]
    ))
    E.append(sp(8))

    E.append(Paragraph('1.2 From ZP-A through ZP-E', S['h2']))

    E.append(label_box_status(
        'Import Registry IR-ZP — Closed Results from ZP-A through ZP-E',
        'Status: Valid — Received',
        [
            'From ZP-A: Join-semilattice (L, &#8744;, &#8869;). &#8869; is the unique additive identity. '
            '&#8869; &#8804; x for all x &#8712; L (T2). State sequences are monotone (T3). No subtraction operator.',
            'From ZP-B: Q<sub>2</sub> with ultrametric d. AX-B1 (binary existence). MP-1 (minimality principle). '
            'p = 2 derived (T0). Every ball is clopen (T2). Q<sub>2</sub> totally disconnected (T5). '
            'Clopen separation of 0 from all nonzero elements (T3). Snap irreversibility (C3).',
            'From ZP-C: Incompressibility threshold P<sub>0</sub> (D1). RP-1 (representation principle). '
            'State representations derived from AX-B1 (T1). JSD = 1 bit (T1b). Discrete surprisal operator DF (D5, D6). '
            'Non-conservatism of DF on infinite sequences approaching 0 (T2). L-RUN (c<sub>0</sub> &#8800; c<sub>1</sub>, so the step from &#8869; of MachinePhase (c<sub>0</sub>) to c<sub>1</sub> is a state change off it). '
            'TQ-IH (the same fact read from c<sub>1</sub>). '
            'T-BUF / T-SNAP: Binary Snap derived as theorem.',
            'From ZP-D: H = &#8450;<sup>n</sup> (D1). T: Q<sub>2</sub> &#8594; H constructed by basis assignment (T2). '
            'T unique up to unitary equivalence (T3). Snap produces orthogonal shift (T4). '
            'Monotone sequences map to non-decreasing norms, all equal to 1 by D2(v) (T5). DP-1 (orthogonality design commitment).',
            'From ZP-E: Universal constituent cross-framework (T1). Hamming/JSD consistency (T2). '
            'Landauer bridge BA-1. Processing bounds T3. Unified Snap description T4. '
            'Iterative forcing T5. State representations T6. Zero Paradox T7. '
            'T-SNAP: the shape of the Binary Snap is a derived theorem — AX-1 is retired, and that the Snap occurs is stated separately: it follows from the occurrence commitment together with DA-1 (closed given DP-2). The occurrence commitment is stated in two charts, execution and slot, in the header of ZeroParadox/Order/Snap.lean (indexed in ZeroParadox/Order/SnapCannotBe.lean &#167; II and CLAIMS.md), the slot chart as the hypothesis hw of t_snap_of_fires_once, that the tape fires at some stage, beside the theorem trials_fires_once that, for independent stages each firing with probability p, 0 &lt; p &#8804; 1, firing at some stage has probability one, which names no tape (ZeroParadox/Information/CrossingTrials.lean &#167; VIII).',
        ]
    ))
    E.append(sp(8))

    E.append(label_box_status(
        'Inherited Labels Registry IR-2 — Open Items Carried into ZP-H',
        'Status: Structural — labels preserved without laundering',
        [
            'OQ-G1 [Closed in ZP-G v1.1]: Native derivation of categorical surprisal without importing Shannon entropy. '
            'Closed by D7\' (conditional Kolmogorov complexity K(B|A)) and I-KC. BA-G1 demoted to remark R-BA.',
            'OQ-G2 [Resolved in Section IV]: Left adjoint verification for instantiation functors.',
            'OQ-G3 [Resolved in Section III]: Explicit construction of four instantiation functors.',
            'OQ-G4 [Resolved in Section V]: Reconciliation of categorical and ZP-C singularity characterizations.',
        ]
    ))

    print('[build_zph] Building Section II: Morphisms of C...')
    # ── II. THE MORPHISMS OF C ────────────────────────────────────────────────
    E.append(Paragraph('II. The Morphisms of C — New Definition', S['h1']))
    E += [
        body('ZP-G defined C abstractly: objects, morphisms, composition, identity, satisfying the '
             'category axioms plus AX-G1 and AX-G2. The morphisms of C were left unspecified '
             'because the abstract results (T1 through T7) require only the categorical axioms, not a '
             'concrete description of what morphisms are. That abstraction was correct for ZP-G.'),
        body('ZP-H requires concreteness. To construct the instantiation functors, we must specify '
             'what morphisms of C are, so that we can say what the functor maps them to. That '
             'specification belongs here, not in ZP-G.'),
    ]

    E.append(label_box_status(
        'Definition D-H1 — Morphisms of C — State Transitions',
        'Status: Definition — instantiation-specific',
        [
            'A morphism f: A &#8594; B in C is a state transition: a structure-preserving map from state A to state B satisfying:',
            '(i) Forward direction: Every morphism f: A &#8594; B represents a net addition of informational content. '
            'No morphism reduces state.',
            '(ii) Compatibility with AX-G2: For any non-initial object X (not isomorphic to 0), no morphism X &#8594; 0 exists. D-H1(i) '
            'and AX-G2 are consistent: a net-additive transition cannot return to the minimal state 0.',
            '(iii) Composition: Composition of morphisms corresponds to sequential state accumulation. f: A &#8594; B '
            'followed by g: B &#8594; C produces a state at least as large as B.',
            'Status note: D-H1 is a design commitment, not a derivation. It is the choice that makes the '
            'instantiation functors well-defined. A different choice of morphism structure would yield different '
            'functors. D-H1 is the choice that maps correctly to all four ZP domain documents.',
        ]
    ))

    print('[build_zph] Building Section III: Instantiation Functors...')
    # ── III. CONSTRUCTION OF THE INSTANTIATION FUNCTORS ──────────────────────
    E.append(Paragraph('III. Construction of the Instantiation Functors [OQ-G3: PDF Constructions Complete]', S['h1']))
    E += [
        body('ZP-G Remark R3 claimed the existence of four functors F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub> without '
             'constructing them. This section constructs all four. Each construction must specify the '
             'object map, the morphism map, and verify preservation of composition and identity. Each '
             'must also show that AX-G1 and AX-G2 are respected.'),
    ]

    E.append(Paragraph('3.1 F<sub>A</sub>: C &#8594; SLat (Join-Semilattices)', S['h2']))
    E.append(label_box_status(
        'Construction C-H1 — Functor FA: C → SLat',
        'Status: Derived as a PDF construction — Lean: no functor term (witness: natZPCategory, 0 initial in &#8469;)',
        [
            'Object map: F<sub>A</sub> sends each object X &#8712; ob(C) to the state S<sub>X</sub> &#8712; L in the '
            'join-semilattice (L, &#8744;, &#8869;) of ZP-A. The initial object 0 maps to &#8869;: F<sub>A</sub>(0) = &#8869;.',
            'Morphism map: F<sub>A</sub> sends each morphism f: A &#8594; B to the join operation that witnesses the '
            'transition: F<sub>A</sub>(f) = (S<sub>A</sub> &#8744; &#945;) for some &#945; &#8712; L such that S<sub>A</sub> &#8744; &#945; = S<sub>B</sub>. '
            'By ZP-A D2, every valid state transition is a join.',
            'Preservation of composition: For f: A &#8594; B and g: B &#8594; C, F<sub>A</sub>(g &#8728; f) = S<sub>A</sub> &#8744; &#945;<sub>f</sub> &#8744; &#945;<sub>g</sub> = '
            'F<sub>A</sub>(g) &#8728; F<sub>A</sub>(f) by associativity of &#8744; (ZP-A A1). <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>A</sub>(id<sub>A</sub>) = S<sub>A</sub> &#8744; &#8869; = S<sub>A</sub> by ZP-A A4 (additive identity). <font name="DV">&#10003;</font>',
            'AX-G1 respected on a carrier with no top element: F<sub>A</sub>(0) = &#8869; is the global minimum of L (ZP-A T2). '
            'Having no top element is the optional ZP-A hypothesis HasNoTop (ZeroParadox/Order/Lattice.lean), not a property of every '
            'carrier: ZP-A\'s two-state carriers have a top. Where it holds, every element has something strictly above it, so no element '
            'is terminal (the last example of &#167; I-b in ZeroParadox/Category/Category.lean). The Lean witness is &#8469; with &#8804;, '
            'which has no greatest element (natZPCategory, ZeroParadox/Multihomed/CategoricalBridge.lean). <font name="DV">&#10003;</font>',
            'AX-G2 respected: No join operation in L can return to &#8869; from a strictly larger state (ZP-A T3, '
            'monotonicity). Therefore F<sub>A</sub> sends no non-initial morphism to a map terminating at &#8869;. '
            'Note: this verification depends on CC-1 / DA-2 for F<sub>A</sub> to send C\'s initial object 0 to L\'s &#8869;. '
            'CC-1 is restated in ZP-J, not forced: given AFAStructure, starting at a Quine atom and starting at &#8869; are the same condition (cc1_derived, t_exec_iff, Lean 4). The choice of starting point remains a ZP-A modelling commitment, so this check holds given CC-1. <font name="DV">&#10003;</font>',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('3.2 F<sub>B</sub>: C &#8594; pTop (p-Adic Topological Spaces)', S['h2']))
    E.append(label_box_status(
        'Construction C-H2 — Functor FB: C → pTop',
        'Status: PDF construction complete — Lean: full functor (fb_functor, sorry-free)',
        [
            'Object map: F<sub>B</sub> sends each object X &#8712; ob(C) to an element x &#8712; Q<sub>2</sub>. The initial object 0 maps to '
            'the element 0 &#8712; Q<sub>2</sub>: F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub>. pTop is the informal name of the target: in Lean, '
            'F<sub>B</sub> is realized in TopCat, the category of all topological spaces (fB_functor, ZeroParadox/Valuation/TopFunctor.lean), '
            'and its &#8469;-indexed stand-in is Q&#8322;BallDepth (fb_functor, ZeroParadox/Multihomed/CategoricalBridge.lean).',
            'Morphism map: F<sub>B</sub> sends each morphism f: A &#8594; B to the discrete jump from x<sub>A</sub> to x<sub>B</sub> '
            'in Q<sub>2</sub>. By ZP-B T2, any two distinct elements of Q<sub>2</sub> lie in disjoint clopen balls. The jump is across a clopen '
            'boundary — a well-defined topological transition.',
            'Preservation of composition: Sequential discrete jumps in Q<sub>2</sub> compose by transitivity of the ball '
            'structure. x<sub>A</sub> &#8594; x<sub>B</sub> &#8594; x<sub>C</sub> is a valid sequence of clopen transitions. <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>B</sub>(id<sub>A</sub>) is the trivial jump x<sub>A</sub> &#8594; x<sub>A</sub>, which is the identity on Q<sub>2</sub>. <font name="DV">&#10003;</font>',
            'In Q<sub>2</sub>, F<sub>B</sub>(0) = 0 is clopen-separated from all nonzero elements (ZP-B T3).',
            'AX-G1 respected in the stand-in category: the Lean functor fb_functor lands in Q&#8322;BallDepth, the &#8469;-indexed ball-depth '
            'category, which has no terminal object because the depth index has no maximum: n + 1 &gt; n (q2BallZPCat, '
            'ZeroParadox/Multihomed/CategoricalBridge.lean). <font name="DV">&#10003;</font>',
            'AX-G1 fails in TopCat: TopCat has a terminal object, the one-point space (the example after kleisli_bottom_not_terminal in '
            'ZeroParadox/Category/TreeSeam.lean). The TopCat realization fB_functor presents 0 as the limit of the shrinking balls, and that '
            'floor {0} is itself a one-point space, so it is terminal and not initial (padic_bottom_isTerminal and padic_bottom_not_initial, '
            'ZeroParadox/Multihomed/TreeObstructions.lean).',
            'AX-G2 respected in the stand-in category: in Q&#8322;BallDepth a morphism m &#8594; 0 means m &#8804; 0, so m = 0 by antisymmetry '
            '(q2BallZPCat). ZP-B C3, that no continuous path in Q<sub>2</sub> returns to 0 from any non-zero element, is the domain analogue of '
            'this stand-in, proved in its own layer. <font name="DV">&#10003;</font>',
            'AX-G2 in TopCat is stated at the initial object, which is not the floor {0}. TopCat\'s initial object is the empty space, and it '
            'satisfies the AX-G2 shape: a space with a morphism into the empty space is empty, so it is isomorphic to it (the example '
            'after padic_bottom_isTerminal in ZeroParadox/Multihomed/TreeObstructions.lean).',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('3.3 F<sub>C</sub>: C &#8594; InfoSp (Information-Theoretic Spaces)', S['h2']))
    E.append(label_box_status(
        'Construction C-H3 — Functor FC: C → InfoSp',
        'Status: PDF construction complete — Lean: full functor (fc_functor, sorry-free)',
        [
            'Object map: in Lean, with C realized as &#8469;, object n goes to depth n of InfoDepth (fc_functor.obj n) and to the finite type '
            'Fin n of KleisliCat PMF (fC_functor.obj n). The initial object 0 maps to depth 0 of InfoDepth and to Fin 0, the empty type, which is '
            'initial in KleisliCat PMF (fC_zero_isInitial). ZP-C\'s information model reads the non-existence state of BinaryState as its point mass, '
            'the distribution P = (1, 0) over {0, 1} (derived from AX-B1 and RP-1 in ZP-C T1); no distribution lives on the empty type '
            '(the proof of fC_no_return), so the two models differ at 0. InfoSp is '
            'the informal name of the target: in Lean, F<sub>C</sub> is realized in KleisliCat PMF, the Kleisli category of the probability monad '
            '(fC_functor, ZeroParadox/Multihomed/InfoFunctor.lean), and its &#8469;-indexed stand-in is InfoDepth (fc_functor, '
            'ZeroParadox/Multihomed/CategoricalBridge.lean).',
            'Morphism map: F<sub>C</sub> sends each morphism f: A &#8594; B to the informational transition from P<sub>A</sub> to P<sub>B</sub>, '
            'with informational work E = JSD(P<sub>A</sub> &#8741; P<sub>B</sub>) &#8805; 0. The fundamental transition (0 &#8594; first non-initial '
            'object) maps to JSD(P &#8741; Q) = 1 bit (ZP-C T1b).',
            'Preservation of composition: In the binary framework (two outcome states), only two point-mass distributions exist: '
            'P = (1, 0) and Q = (0, 1). The snap f: 0 &#8594; &#949;<sub>0</sub> is the unique morphism mapping P &#8594; Q at cost '
            'JSD(P &#8741; Q) = 1 bit. All successor morphisms g: &#949;<sub>n</sub> &#8594; &#949;<sub>n+1</sub> map Q &#8594; Q (Q-stability of the '
            'post-snap codomain), giving F<sub>C</sub>(g) = JSD(Q &#8741; Q) = 0. Therefore F<sub>C</sub>(g &#8728; f) = 1 bit = '
            'F<sub>C</sub>(g) + F<sub>C</sub>(f) = 0 + 1 bit. Composition is preserved exactly by Q-stability, not by '
            'subadditivity. (Note: JSD subadditivity is an inequality and does not establish this — '
            'the equality holds here as a structural consequence of the binary framework.) <font name="DV">&#10003;</font>',
            'Preservation of identity: F<sub>C</sub>(id<sub>A</sub>) = JSD(P<sub>A</sub> &#8741; P<sub>A</sub>) = 0. No informational work is done by a trivial transition. <font name="DV">&#10003;</font>',
            'The point masses P = (1, 0) and Q = (0, 1) are exactly the distributions of zero entropy (Mathlib Real.binEntropy_eq_zero: binEntropy p = 0 &#8596; p = 0 &#8744; p = 1).',
            'AX-G1 respected in the stand-in category: the Lean functor fc_functor lands in InfoDepth, the &#8469;-indexed surprisal-depth '
            'category, which has no terminal object because the depth index has no maximum: n + 1 &gt; n (infoDepthZPCat, '
            'ZeroParadox/Multihomed/CategoricalBridge.lean). <font name="DV">&#10003;</font>',
            'AX-G1 fails in KleisliCat PMF: the one-point type is a terminal object (the example after kleisli_bottom_not_terminal in '
            'ZeroParadox/Category/TreeSeam.lean). In ZP-A, having no top element is the optional hypothesis HasNoTop '
            '(ZeroParadox/Order/Lattice.lean), which ZP-A\'s two-state carriers do not satisfy.',
            'AX-G2 respected in the stand-in category: in InfoDepth a morphism m &#8594; 0 means m &#8804; 0, so m = 0 by antisymmetry '
            '(infoDepthZPCat). Its domain analogue: JSD &#8805; 0, and a transition returning to P = (1, 0) from any Q &#8800; P would require '
            'JSD(Q &#8741; P) = 0, which holds only if Q = P. <font name="DV">&#10003;</font>',
            'In KleisliCat PMF, no stage n &gt; 0 of the realization has a morphism into stage 0 (fC_no_return, '
            'ZeroParadox/Multihomed/InfoFunctor.lean): the AX-G2 shape on the functor\'s image.',
            'Inherited label: The distributions P = (1, 0) and Q = (0, 1) are derived from AX-B1 and RP-1 (ZP-C T1, ZP-E T6). '
            'All results depending on F<sub>C</sub> inherit the AX-B1 and RP-1 labels.',
        ]
    ))
    E.append(sp(6))

    E.append(Paragraph('3.4 F<sub>D</sub>: C &#8594; Hilb (Hilbert Spaces)', S['h2']))
    E.append(label_box_status(
        'Construction C-H4 — Functor FD: C → Hilb',
        'Status: PDF construction complete — Lean: full functor (fd_functor, sorry-free)',
        [
            'Object map: F<sub>D</sub> sends each object of C to a state space: in Lean, with C realized as &#8469;, object n goes to depth n of '
            'HilbDimDepth (fd_functor.obj n) and to the module StateSpace n of ModuleCat &#8450; (fD_functor.obj n). The initial object 0 maps to F<sub>D</sub>(0): depth 0 of HilbDimDepth '
            '(fd_functor.obj 0) and the zero module &#8450;<sup>0</sup> (fD_functor.obj 0). ZP-D\'s vector model reads a point x of Q<sub>2</sub> as the '
            'vector T(x) &#8712; H = &#8450;<sup>n</sup>, through the transition operator T: Q<sub>2</sub> &#8594; H constructed in ZP-D (T2); there 0 of '
            'Q<sub>2</sub> is read as the unit vector T(0) = e<sub>0</sub> (ZP-D D2(i), met by T2), which &#8450;<sup>0</sup> does not contain, so the two '
            'models differ at 0. '
            'Hilb is the informal name of the target: in Lean, F<sub>D</sub> is realized in ModuleCat &#8450;, the category of &#8450;-modules '
            '(fD_functor, ZeroParadox/State/HilbFunctor.lean), and its &#8469;-indexed stand-in is HilbDimDepth (fd_functor, '
            'ZeroParadox/Multihomed/CategoricalBridge.lean).',
            'Morphism map: F<sub>D</sub> sends each morphism f: A &#8594; B to the orthogonal extension from T(x<sub>A</sub>) to T(x<sub>B</sub>) '
            'in H. By ZP-D D2(iii) and D2(iv) (DP-1), points in different cells of the level-k partition P<sub>k</sub> map to orthogonal basis vectors under T, '
            'and points in one cell share one vector, so the transition is an orthogonal step when x<sub>A</sub> and x<sub>B</sub> lie in different cells and the trivial step when they share a cell.',
            'Preservation of composition: F<sub>D</sub>(g &#8728; f) = F<sub>D</sub>(g) &#8728; F<sub>D</sub>(f) is the functor law map_comp of the Lean functors, '
            'fd_functor.map_comp and fD_functor.map_comp. <font name="DV">&#10003;</font>',
            'Remark (ZP-D T5, not composition): every state vector is a unit vector by ZP-D D2(v), so along T(x<sub>A</sub>) &#8594; T(x<sub>B</sub>) &#8594; '
            'T(x<sub>C</sub>) the norms are all 1 and ZP-D T5\'s non-decreasing norms hold with equality.',
            'Preservation of identity: F<sub>D</sub>(id<sub>A</sub>) is the identity on F<sub>D</sub>(A), the functor law map_id of the Lean functors, fd_functor.map_id and fD_functor.map_id; in the vector model it is the trivial extension T(x<sub>A</sub>) &#8594; T(x<sub>A</sub>). <font name="DV">&#10003;</font>',
            'In the vector model, T(0) = e<sub>0</sub> (ZP-D D2(i), met by T2) is the anchor vector from which all other state vectors are orthogonal extensions.',
            'AX-G1 respected in the stand-in category: the Lean functor fd_functor lands in HilbDimDepth, the &#8469;-indexed dimension-depth '
            'category, which has no terminal object because the depth index has no maximum: n + 1 &gt; n (hilbDimZPCat, '
            'ZeroParadox/Multihomed/CategoricalBridge.lean). <font name="DV">&#10003;</font>',
            'AX-G1 fails in ModuleCat &#8450;: the realization fD_functor sends 0 to the zero module fD_functor.obj 0, which is a zero object '
            'of ModuleCat &#8450;, initial and terminal at once (hilbert_bottom_isZero, ZeroParadox/Category/TreeSeam.lean).',
            'AX-G2 respected in the stand-in category: in HilbDimDepth a morphism m &#8594; 0 means m &#8804; 0, so m = 0 by antisymmetry '
            '(hilbDimZPCat). ZP-D T4, that the Snap produces an orthogonal shift (proved in ZP-D), and ZP-A Remark R1 (no subtraction) are '
            'the domain analogues of this stand-in. <font name="DV">&#10003;</font>',
            'AX-G2 fails in ModuleCat &#8450;: the zero module fD_functor.obj 0 is a zero object, every stage has a morphism into it (the zero '
            'map, fD_has_return, ZeroParadox/Category/Heterogeneous.lean) and stage 1 is not a zero object (leaf_not_isZero, '
            'ZeroParadox/Category/SeamNotColimit.lean).',
            'Design commitment inherited: DP-1 (orthogonality as representation of clopen separation) is a '
            'design commitment in ZP-D v1.2. F<sub>D</sub> inherits this label. T4 and T5-b of ZP-D depend on DP-1 as a premise.',
        ]
    ))

    print('[build_zph] Building Section IV: Left Adjoint Verification...')
    # ── IV. LEFT ADJOINT VERIFICATION ────────────────────────────────────────
    E.append(Paragraph('IV. Left Adjoint Verification [OQ-G2 Closed]', S['h1']))
    E += [
        body('ZP-G T5 stated that functors preserve initial objects, but marked it conditional on OQ-G2: '
             'verifying that the instantiation functors are left adjoints (or otherwise preserve the '
             'universal property of 0 fully, not just for objects in their image). This section closes OQ-G2.'),
    ]

    E.append(label_box_status(
        'Theorem T-H1 — Each Instantiation Functor Preserves the Initial Object',
        'Status: Derived — OQ-G2 closed',
        [
            'Claim: For each functor F &#8712; {F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub>} as constructed in Section III, F(0) is an initial object in the codomain category (for F<sub>B</sub>, in its stand-in). The Lean coverage is narrower and is stated in the conclusion.',
            'Strategy: Rather than proving each functor is a left adjoint in full generality (which would require '
            'establishing adjoint pairs for SLat, pTop, InfoSp, and Hilb), we verify the universal property '
            'directly for each functor. The universal property of the initial object requires: for every object Y in '
            'the codomain, &#8707;! morphism F(0) &#8594; Y.',
            'F<sub>A</sub>: F<sub>A</sub>(0) = &#8869;. For any S<sub>Y</sub> &#8712; L, the unique morphism &#8869; &#8594; S<sub>Y</sub> is the join &#8869; &#8744; S<sub>Y</sub> = S<sub>Y</sub> (ZP-A A4). '
            'Uniqueness: &#8869; is the global minimum (ZP-A T2), so the only order-preserving map from &#8869; to S<sub>Y</sub> is the join with S<sub>Y</sub>. <font name="DV">&#10003;</font>',
            'F<sub>B</sub>: F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub>. For any x &#8712; Q<sub>2</sub>, the unique morphism 0 &#8594; x is the discrete jump from 0 to x '
            'across the clopen boundary. Uniqueness: 0 is clopen-separated from all nonzero elements (ZP-B T3); the only clopen-respecting transition from 0 to x is the direct jump. '
            'This leg holds in the stand-in Q&#8322;BallDepth (fb_preserves_initial, ZeroParadox/Multihomed/CategoricalBridge.lean). In TopCat it '
            'does not: the floor {0} is a one-point space, so it is terminal and not initial there (padic_bottom_isTerminal and padic_bottom_not_initial, '
            'ZeroParadox/Multihomed/TreeObstructions.lean). <font name="DV">&#10003;</font>',
            'F<sub>C</sub>: F<sub>C</sub>(0) is depth 0 of InfoDepth (fc_functor.obj 0) and the empty type Fin 0 of KleisliCat PMF '
            '(fC_functor.obj 0), not the distribution P = (1, 0) of ZP-C\'s model (C-H3: the two models differ at 0). '
            'Uniqueness of the morphism out of it is a fact about the codomain category: from the empty type there is exactly one '
            'stochastic map to each object, the empty one (fC_zero_isInitial), and in the stand-in InfoDepth every hom-set out of '
            'depth 0 has exactly one element (infoDepthHom0Unique), so fc_functor sends 0 to an initial object (fc_preserves_initial, '
            'ZeroParadox/Multihomed/CategoricalBridge.lean). That JSD takes '
            'one value on each pair of distributions is a fact about a number, not about morphisms, and is not used here. <font name="DV">&#10003;</font>',
            'F<sub>D</sub>: F<sub>D</sub>(0) is depth 0 of HilbDimDepth (fd_functor.obj 0) and the zero module &#8450;<sup>0</sup> of ModuleCat &#8450; '
            '(fD_functor.obj 0); ZP-D\'s vector model reads 0 of Q<sub>2</sub> as the base vector T(0) = e<sub>0</sub> (ZP-D D2(i)), and reads the morphism '
            'from F<sub>D</sub>(0) to the object of x as the orthogonal extension from e<sub>0</sub> to e<sub>k</sub> (the basis vector assigned to x). '
            'Uniqueness of that morphism is a fact about the codomain category, '
            'not about T: in the stand-in HilbDimDepth every hom-set out of depth 0 has exactly one element (hilbDimHom0Unique), so fd_functor sends 0 '
            'to an initial object (fd_preserves_initial, ZeroParadox/Multihomed/CategoricalBridge.lean). In ModuleCat &#8450; the realization fD_functor '
            'sends 0 to the zero module, a zero object and so initial (hilbert_bottom_isZero, ZeroParadox/Category/TreeSeam.lean). ZP-D T3 (T unique up to a '
            'unitary) concerns the vectors T(x) up to a unitary, not the morphisms between objects, and is not used here. <font name="DV">&#10003;</font>',
            'Conclusion: OQ-G2 is closed in this sense. On paper, the universal property of 0 &#8712; ob(C) is verified directly for each of the four '
            'constructions of Section III, for F<sub>B</sub> in its stand-in. In Lean, fb_functor, fc_functor and fd_functor send 0 to an initial '
            'object of their &#8469;-indexed stand-ins (fb_preserves_initial, fc_preserves_initial, fd_preserves_initial, each IsInitial.ofUnique 0); '
            'F<sub>A</sub> has no functor term, and its witness is 0 initial in &#8469;\'s order category (natSLat_initial_grounding). '
            'ZP-G T5\'s OQ-G2 condition is discharged for these and not beyond them: in TopCat the F<sub>B</sub> floor is terminal and not initial '
            '(padic_bottom_not_initial). <font name="DV">&#10003;</font>',
        ]
    ))

    print('[build_zph] Building Section V: Singularity Reconciliation...')
    # ── V. SINGULARITY RECONCILIATION ────────────────────────────────────────
    E.append(Paragraph('V. Singularity Reconciliation [OQ-G4 Closed]', S['h1']))
    E += [
        body('ZP-G T6 characterized the informational singularity of 0 as an undefined domain: the '
             'categorical surprisal I(X &#8594; 0) is undefined because no such morphism exists. ZP-C '
             'established the singularity as infinite accumulation: the discrete surprisal DF diverges '
             'along infinite sequences approaching 0 in Q<sub>2</sub>. ZP-G R4 claimed these are compatible but '
             'did not prove it. This section closes OQ-G4.'),
    ]

    E.append(label_box_status(
        'Theorem T-H2 — Compatibility of Singularity Characterizations',
        'Status: Derived — OQ-G4 closed',
        [
            'Claim: The categorical singularity (undefined domain: hom(X, 0) = <font name="DV">&#8709;</font> for X not isomorphic to 0, '
            'ZP-G Lemma T3, on which ZP-G T6 Part II rests) and the ZP-C singularity (infinite '
            'accumulation, ZP-C Theorem T2) hold together: a conjunction of the two, and the '
            'proof uses neither to prove the other.',
            'Setup (motivation only; th2_singularity_compatibility involves neither F<sub>C</sub> nor F<sub>B</sub>): Let {X<sub>n</sub>} be a sequence of objects in C, with F<sub>C</sub>(X<sub>n</sub>) the finite type '
            'Fin n of KleisliCat PMF (fC_obj; F<sub>C</sub>(0) is the empty type Fin 0, C-H3). Under F<sub>B</sub>, the corresponding '
            'sequence {x<sub>n</sub>} in Q<sub>2</sub> approaches 0 &#8712; Q<sub>2</sub>.',
            'ZP-C side: By ZP-C T2, the discrete surprisal DF along the infinite sequence {x<sub>n</sub>} approaching 0 in '
            'Q<sub>2</sub> is non-conservative: the accumulated surprisal &#8721; DF(x<sub>k</sub> &#8594; x<sub>k+1</sub>) diverges as n &#8594; &#8734;. The singularity is infinite accumulation.',
            'ZP-G side: By ZP-G T6(ii), I(X &#8594; 0) is undefined for all X not isomorphic to 0 because hom(X, 0) = <font name="DV">&#8709;</font> (AX-G2). The singularity is undefined domain.',
            'Reconciliation: The two characterizations are compatible: both hold. '
            'In ZP-C, we ask: what happens to surprisal as we approach 0 along an infinite sequence? The '
            'answer is divergence — the accumulation is unbounded. In ZP-G, we ask: can we reach 0 by a '
            'morphism from outside? The answer is no — the morphism does not exist. Read informally, if the '
            'accumulation required to reach 0 is infinite, then no finite morphism can accomplish it; that link '
            'runs from divergence toward absence and is a reading, not a theorem.',
            'Lean: th2_singularity_compatibility pairs t3_unreachability (the ZP-G side) with t2_diverges (the '
            'ZP-C side): the proof term is the pair of these two separately proved results, ZP-G Lemma T3 and ZP-C Theorem T2, and it uses neither to prove the other. '
            'OQ-G4 is closed in that sense. <font name="DV">&#10003;</font>',
        ]
    ))

    E.append(remark_box(
        'Remark R-FORCING — Structural Forcing vs. Re-Description',
        [
            'Each of the four instantiation settings of Sections III-V (F<sub>A</sub>, F<sub>B</sub>, F<sub>C</sub>, '
            'F<sub>D</sub>) has a domain fact proved in its own layer. None is derived from a functor, and no Lean '
            'declaration pairs any of them with fb_functor, fc_functor or fd_functor (F<sub>A</sub> has no functor term): '
            'ZP-A shows the lattice join c<sub>0</sub> &#8744; c<sub>1</sub> = c<sub>1</sub> in MachinePhase, which places '
            'c<sub>1</sub> above c<sub>0</sub>, the &#8869; of MachinePhase (machinePhaseZPS); ZP-B shows the 2-adic topology '
            'admits no continuous path in Q<sub>2</sub> from a nonzero point back to 0 (C3; it does not supply a departure '
            '&#8212; ZP-B cannot force the snap, and the first step is AX-B1); ZP-C shows JSD(P, Q) = log 2, one bit (T1b); '
            'ZP-D shows two basis vectors of the state space are orthogonal (T4).',
            'The four facts are sorry-free in Lean 4: the lattice conjunct join c<sub>0</sub> c<sub>1</sub> = c<sub>1</sub> of '
            'th3_snap_all_functors; fb_snap_q2_grounded, which restates C3 for points of the depth-1 ball and names no '
            'morphism; and fc_snap_info_grounded and fd_snap_hilb_grounded, each of which only pairs the stand-in morphism '
            '0 &#8594; 1 of its target with T1b or T4 and relates neither to the other. No fact is derived from another either. '
            'On the framework\'s reading, each fact constrains the shape a transition can take in its own domain, so a '
            'transition of the snap\'s shape in each of the four canonical languages for state description is more than '
            're-description. That reading is not a theorem, and neither is the further reading that the '
            'four are one structural singularity. That the transition is taken follows from the occurrence commitment together with DA-1 (closed given DP-2), not from '
            'any of the four.',
        ]
    ))

    print('[build_zph] Building Section VI: Binary Snap...')
    # ── VI. THE BINARY SNAP — CATEGORICAL DESCRIPTION ────────────────────────
    E.append(Paragraph('VI. The Binary Snap — Categorical Description', S['h1']))

    E.append(label_box_status(
        'Theorem T-H3 — The Binary Snap: Four Domain Facts, Conjoined',
        'Status: Derived — a conjunction of four domain facts; no cross-domain tie',
        [
            'Setup: The Binary Snap is the transition from 0 &#8712; ob(C) to the first non-initial object '
            '&#949;<sub>0</sub> &#8712; ob(C), driven by the incompressibility threshold P<sub>0</sub> (ZP-C D1) under '
            'T-SNAP (Binary Snap — Derived Theorem, ZP-E v2.0).',
            'In C (ZP-G): The Snap is the morphism &#953;<sub>&#949;0</sub>: 0 &#8594; &#949;<sub>0</sub>. By D3, this morphism is unique. '
            'By T4, no chain returns from &#949;<sub>0</sub> to 0. The Snap is categorically irreversible.',
            'Statement (th3_snap_all_functors): four separately proved facts, conjoined. (1) join c<sub>0</sub> c<sub>1</sub> = c<sub>1</sub> '
            'in MachinePhase (T-SNAP); (2) no continuous path in Q<sub>2</sub> runs from a '
            'nonzero point to 0 (ZP-B C3); (3) JSD(P, Q) = log 2, one bit (ZP-C T1b); (4) indices 0 and 1 of transitionOp n are orthogonal '
            'in StateSpace n, n &#8805; 2 (ZP-D T4). No functor occurs in its type, and no conjunct is used to prove another.',
            'Readings, not part of the statement: '
            'the four lines below are how the framework reads the Snap in each instantiation '
            'setting. They are interpretation, and no Lean declaration states them.',
            'Reading under F<sub>A</sub> (ZP-A): F<sub>A</sub>(&#953;<sub>&#949;0</sub>) = &#8869; &#8744; &#949;<sub>0</sub> = S<sub>1</sub>. The Snap is the first join. Monotone and irreversible by ZP-A T3. '
            'T-SNAP is a derived theorem (ZP-E v2.0); inherited here with derived status.',
            'Reading under F<sub>B</sub> (ZP-B): F<sub>B</sub>(&#953;<sub>&#949;0</sub>) is the discrete jump 0 &#8594; &#949;<sub>0</sub> &#8712; Q<sub>2</sub> across a clopen boundary (ZP-B T2). '
            'Topologically irreversible by ZP-B C3.',
            'Reading under F<sub>C</sub> (ZP-C): F<sub>C</sub>(&#953;<sub>&#949;0</sub>) is the informational transition P &#8594; Q with E = JSD(P &#8741; Q) = 1 bit (ZP-C '
            'T1b). Irreversible: JSD(Q &#8741; P) = 1 bit &#8800; 0.',
            'Reading under F<sub>D</sub> (ZP-D): F<sub>D</sub>(&#953;<sub>&#949;0</sub>) is the orthogonal shift T(0) = e<sub>0</sub> &#8594; T(&#949;<sub>0</sub>) = e<sub>1</sub>. '
            '&#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0 (ZP-D T4). Both vectors have norm 1 (ZP-D D2(v)), so ZP-D T5\'s non-decreasing norms hold with equality. DP-1 is a design premise.',
            'Lean: th3_snap_all_functors (ZeroParadox/Multihomed/CategoricalBridge.lean) conjoins four '
            'separately proved domain facts; its type names no functor and relates no conjunct to another, '
            'so a reading of one snap seen under four functors is not what it states. Independence of null-analog discovery: each '
            'framework located its null-analog through its own domain logic — &#8869; through A4 (ZP-A), '
            '0 &#8712; Q<sub>2</sub> through T3 (ZP-B), P = (1,0) through D1/RP-1 (ZP-C) — prior to and without '
            'reference to the others. ZP-D\'s e<sub>0</sub> is not independent in this sense: it is reached by transport '
            'of ZP-B\'s 0 along T (ZP-D D2(i), T(0) = e<sub>0</sub>). No identification of these objects is '
            'made, under the functors or otherwise: they live in different types, and an equation across them '
            'is ill-typed (MC-1, the bottom family). Where a shared role is checked, it is checked in one '
            'framework at a time, and the occupant depends on the step chosen there. In the die '
            '(ZeroParadox/Die.lean) the role Motion.SelfOnlyAt is a point that steps to itself and to nothing '
            'else. In ZP-A, under a self-application map supplied by AbstractSelfApp, &#8869; is its only '
            'occupant by that class&#8217;s own fields (selfApp_quine_role_iff, '
            'ZeroParadox/Settheory/QuineDichotomy.lean), which the constant map onto &#8869; also meets. In ZP-B, '
            'under doubling, 0 is its only occupant, on the 2-adic integers (z2_double_selfOnlyAt_iff, '
            'ZeroParadox/Ordinal/Incompleteness.lean) and on Q<sub>2</sub> (the doubling example after '
            'c_t_iz_null_balance, ZeroParadox/Valuation/SemilatticeInstance.lean). For ZP-C&#8217;s P = (1,0) and ZP-D&#8217;s e<sub>0</sub> no die '
            'statement was located as of 2026-11-03 (searched: every file under ZeroParadox/ for Motion, '
            'SelfOnlyAt, NoStepAt and LeavesAt beside those objects). What the categorical bridge checks for '
            'F<sub>C</sub> and F<sub>D</sub> is a different role, initiality: they send the initial object 0 to '
            'the empty type Fin 0 and the zero module (fC_zero_isInitial, fD_zero_isInitial). On the empty type '
            'no point occupies the die role at all (the control in ZeroParadox/Category/SeamComparisonMap.lean); '
            'on the zero module, which has one point, every endomorphism has exactly one point that steps to itself '
            'only (hilbert_zero_seam_role_unique), which restates that it is a zero object. '
            'This is not the claim that any domain forced the others&#8217; choices. Read side by side, the framework takes the four '
            'facts as coherence across mathematical representations, not external replication; that is a reading, and T-H3 itself relates none of them to another. '
            'T-SNAP (Binary Snap Causality) is a derived '
            'theorem in ZP-E v2.0 and is inherited here with derived status. &#8220;Causality&#8221; in this name refers to the shape of the step, not to its occurrence. DP-1 remains the only design premise. <font name="DV">&#10003;</font>',
        ]
    ))

    print('[build_zph] Building Section VII: Traceability Register...')
    # ── VII. FULL TRACEABILITY REGISTER ──────────────────────────────────────
    E.append(Paragraph('VII. Full Traceability Register', S['h1']))
    E += [
        body('Every cross-framework claim in ZP-H is traced here to its grounding theorem and any required bridge axiom.'),
    ]

    trace_rows = [
        ['F<sub>A</sub>(0) = &#8869;',                'ZP-A T2; C-H1',               'None',        'Valid — Derived'],
        ['F<sub>A</sub> preserves composition',        'ZP-A A1; C-H1',               'None',        'Valid — Derived'],
        ['F<sub>A</sub> respects AX-G1, AX-G2',       'ZP-A T2, T3; natZPCategory; C-H1', 'HasNoTop (no-terminal half)', 'Valid on a carrier with no top'],
        ['F<sub>B</sub>(0) = 0 &#8712; Q<sub>2</sub>','ZP-B T3; C-H2',               'None',        'Valid — Derived'],
        ['F<sub>B</sub> preserves composition',        'ZP-B T2; C-H2',               'None',        'Valid — Derived'],
        ['F<sub>B</sub> respects AX-G1, AX-G2',       'q2BallZPCat (stand-in); C-H2; ZP-B C3 beside it, not used', 'None', 'Valid in the stand-in — TopCat has a terminal object'],
        ['F<sub>C</sub>(0) = depth 0, Fin 0; P = (1,0) in ZP-C\'s model', 'fC_zero_isInitial; ZP-C T1; ZP-E T6; C-H3', 'AX-B1, RP-1 (for P = (1,0) only)', 'Valid — Fin 0 by construction; P from AX-B1, RP-1; the two models differ at 0'],
        ['F<sub>C</sub> preserves composition',        'Q-stability of post-snap codomain; C-H3', 'None', 'Valid — Derived (binary framework; Q-stability, not subadditivity)'],
        ['F<sub>C</sub> respects AX-G1, AX-G2',       'infoDepthZPCat (stand-in); C-H3; ZP-C T1b beside it, not used','AX-B1, RP-1 (for ZP-C T1b; the stand-in proofs use neither)', 'Valid in the stand-in — KleisliCat PMF has a terminal object'],
        ['F<sub>D</sub>(0) = depth 0, &#8450;<sup>0</sup>; T(0) = e<sub>0</sub> in ZP-D\'s vector model', 'ZP-D D2(i), T2; C-H4', 'None (D2(i), by assignment)', 'Valid — by construction'],
        ['F<sub>D</sub> preserves composition',        'fd_functor.map_comp, fD_functor.map_comp; C-H4', 'None', 'Valid — Derived (functor law)'],
        ['F<sub>D</sub> respects AX-G1, AX-G2',       'hilbDimZPCat (stand-in); C-H4; ZP-D T4 beside it, not used','DP-1 (for ZP-D T4; the stand-in proofs do not use it)', 'Valid in the stand-in — both fail in ModuleCat &#8450;'],
        ['T-H1: universal property preserved',         'fb/fc/fd_preserves_initial (IsInitial.ofUnique 0); natZPCategory for F<sub>A</sub>', 'None', 'Valid — OQ-G2 closed, in the stand-ins'],
        ['T-H2: singularity compatibility',            'ZP-G T3, T6; ZP-C T2; C-H3', 'None',        'Valid — OQ-G4 closed'],
        ['T-H3: four separately proved domain facts, conjoined', 'ZP-E T-SNAP; ZP-B C3; ZP-C T1b; ZP-D T4', 'DP-1', 'Valid — a conjunction; none derived from another or from a functor'],
        ['D-H1: morphisms of C',                       'ZP-A D2; ZP-B T2; ZP-C; ZP-D', 'None',      'Design Commitment'],
    ]
    E.append(data_table(
        ['Claim', 'Grounded In', 'Bridge Axiom?', 'Status'],
        trace_rows,
        [TW*0.25, TW*0.35, TW*0.17, TW*0.23]
    ))

    print('[build_zph] Building Section VIII: Open Items Register...')
    # ── VIII. OPEN ITEMS REGISTER ─────────────────────────────────────────────
    E.append(Paragraph('VIII. Open Items Register', S['h1']))

    oq_rows = [
        ['OQ-G1',
         'Closed — ZP-G v1.1\nD7\', T6',
         'Native derivation of categorical surprisal without importing Shannon entropy. '
         'Closed in ZP-G v1.1 by D7\' (native categorical surprisal K(B|A)) and I-KC '
         '(Kolmogorov import from ZP-C). BA-G1 demoted to remark R-BA. '
         'No bridge axiom remains as a theorem premise.'],
        ['OQ-G2',
         'Closed — T-H1',
         'Left adjoint verification for instantiation functors. Resolved in Section IV by '
         'direct verification of the universal property for each of the four PDF constructions (for F<sub>B</sub>, in its stand-in). '
         'In Lean: fb_functor, fc_functor and fd_functor in their stand-ins (fb/fc/fd_preserves_initial), and for F<sub>A</sub>, '
         'which has no functor term, 0 initial in natZPCategory (natSLat_initial_grounding).'],
        ['OQ-G3',
         'Closed — PDF: all\nfour; Lean: three\nfunctor terms\n(F<sub>B</sub>, F<sub>C</sub>, F<sub>D</sub>)',
         'PDF-level constructions of all four instantiation functors complete (Section III). '
         'F<sub>B</sub>, F<sub>C</sub> and F<sub>D</sub> have concrete Lean Functor terms (sorry-free); '
         'F<sub>A</sub> has no functor term, and its Lean witness is the ZPCategory instance natZPCategory on &#8469; with 0 initial (natSLat_initial_grounding). '
         'F<sub>B</sub>: fb_functor (Functor &#8469; Q&#8322;BallDepth), beside C3. '
         'F<sub>C</sub>: fc_functor (Functor &#8469; InfoDepth), beside T1b. '
         'F<sub>D</sub>: fd_functor (Functor &#8469; HilbDimDepth), beside T4. '
         'Each functor is n &#8614; &#10216;n&#10217; between thin categories, and neither its type nor its definition uses the domain fact beside it. '
         'Each of the three stand-in types has a distinct ZPCategory instance and preserves_initial definition. '
         'OQ-G3 closed in this sense.'],
        ['OQ-G4',
         'Closed — T-H2',
         'Reconciliation of categorical (undefined domain) and ZP-C (infinite accumulation) '
         'singularity characterizations. Resolved in Section V. The two characterizations '
         'are shown to hold together: the proof pairs ZP-G Lemma T3 with ZP-C Theorem T2 and uses '
         'neither to prove the other.'],
        ['AX-1',
         'Retired —\nshape: T-SNAP\n(ZP-E v2.0);\nthe snap occurs\ngiven the occurrence\ncommitment and DA-1',
         'Binary Snap Causality. AX-1 is retired. Its content was split in two: the shape of the Snap is '
         'proved, as Theorem T-SNAP (from L-RUN, TQ-IH and the bottom law, with no Lean axioms), and that the Snap '
         'occurs is stated separately: it follows from the occurrence commitment together with DA-1 (closed given DP-2). '
         '(tsnap_holds_but_nothing_moves shows T-SNAP does not carry occurrence.) T-H3 inherits T-SNAP as a derived result. Not a gap.'],
        ['AX-G1',
         'Axiom —\ninitial half\nnot novel',
         'Asymmetry: initial object 0, no terminal object. Inherited from ZP-G. '
         'The initial-object half is not a novel commitment — it is grounded in ⊥ as the bottom element of the ZP-A semilattice. '
         'The no-terminal half is ZP-G\'s own commitment: in ZP-A, having no top element is the optional hypothesis HasNoTop, which '
         'ZP-A\'s two-state carriers do not satisfy. It holds in the &#8469;-indexed depth categories ZP-H\'s Lean functors land in, '
         'and fails in TopCat, ModuleCat &#8450; and KleisliCat PMF, each of which has a terminal object (the example after '
         'kleisli_bottom_not_terminal in ZeroParadox/Category/TreeSeam.lean). Not a gap.'],
        ['AX-G2',
         'Axiom —\nnot novel\nwhere it holds',
         'Source asymmetry: hom(X, 0) = ∅ for X not isomorphic to 0. Inherited from ZP-G. '
         'Not a novel commitment where it holds: in a category built from a partial order with a least element, such as ZP-A\'s '
         'semilattice order and the &#8469;-indexed depth categories ZP-H\'s Lean functors land in, a morphism X &#8594; 0 means X &#8804; 0, '
         'so X = 0 by antisymmetry (for the depth categories, the ax_g2 fields of q2BallZPCat, infoDepthZPCat and hilbDimZPCat in '
         'ZeroParadox/Multihomed/CategoricalBridge.lean; for a partial order in general, the two antisymmetry examples at the end of '
         'ZeroParadox/Category/AxG2Reduce.lean). ZP-B C3 (no continuous path in Q<sub>2</sub> returns to 0) is the domain analogue of the '
         'Q<sub>2</sub> stand-in, proved in its own layer. '
         'AX-G2 does not hold in every category: in ModuleCat &#8450; the zero module fD_functor.obj 0 is a zero object, every stage has a '
         'morphism into it (the zero map, fD_has_return, ZeroParadox/Category/Heterogeneous.lean) and stage 1 is not a zero object '
         '(leaf_not_isZero, ZeroParadox/Category/SeamNotColimit.lean), so AX-G2 fails there. At an initial object, AX-G2 in its isomorphism '
         'form (no morphism into 0 from an object not isomorphic to 0) is equivalent to strict initiality (ax_g2_from_strict_initial and the '
         'converse example after it, ZeroParadox/Category/AxG2Reduce.lean). Not a gap.'],
        ['R-BA',
         'Remark —\nBA-G1 demoted\n(ZP-G v1.1)',
         'Leinster Shannon entropy characterization. BA-G1 demoted from Bridge Axiom '
         'in ZP-G v1.0 to Remark R-BA in ZP-G v1.1. '
         'Not derivable from D7\': the coding theorem gives a one-sided bound, not an equivalence. Not a gap.'],
        ['D-H1',
         'Design\nCommitment —\nintentional',
         'Morphisms of C defined as state transitions. This is a design choice that makes '
         'the instantiation functors well-defined. A different morphism structure would yield '
         'different functors. Explicitly stated and not laundered as a derivation.'],
        ['DP-1',
         'Design\nCommitment —\ninherited',
         'Orthogonality as representation of clopen separation. Inherited from ZP-D v1.1. '
         'F<sub>D</sub> and T-H3 depend on it as a premise.'],
    ]

    E.append(data_table(
        ['Item', 'Status', 'Description'],
        oq_rows,
        [TW*0.12, TW*0.18, TW*0.70]
    ))

    print('[build_zph] Building Section IX: Validation Status...')
    # ── IX. VALIDATION STATUS ─────────────────────────────────────────────────
    E.append(Paragraph('IX. Validation Status', S['h1']))

    val_rows = [
        ['IR-G: ZP-G v1.1 results imported',
         'Valid — all ZP-G v1.1 closed results received; labels preserved. '
         'BA-G1 demoted to R-BA; I-KC noted as named dependency.'],
        ['IR-ZP: ZP-A through ZP-E imported',
         'Valid — all closed results received from ZP-A through ZP-E; labels preserved. '
         'T-SNAP (ZP-E v2.0) noted: AX-1 is retired; its shape is derived, not axiomatic, and the snap occurs given the occurrence commitment and DA-1.'],
        ['IR-2: Inherited labels preserved',
         'Valid — OQ-G1 closed in ZP-G v1.1; OQ-G2, OQ-G3, OQ-G4 resolved here; '
         'BA-G1 updated to R-BA; AX-1 updated to retired, its shape to T-SNAP (Derived) and its occurrence to the occurrence commitment together with DA-1.'],
        ['D-H1: Morphisms of C',
         'Design Commitment — explicitly stated; required for functor construction'],
        ['C-H1: F<sub>A</sub>: C &#8594; SLat',
         'Valid — Derived as a PDF construction. Object map, morphism map, composition, identity all checked on paper. '
         'Lean: no functor term; the witness is natZPCategory, 0 initial in &#8469; (natSLat_initial_grounding). <font name="DV">&#10003;</font>'],
        ['C-H2: F<sub>B</sub>: C &#8594; pTop',
         'Valid — all four requirements verified; AX-G1 and AX-G2 checked in the stand-in Q&#8322;BallDepth (TopCat has a terminal object). '
         'Lean: full functor (fb_functor, sorry-free). <font name="DV">&#10003;</font>'],
        ['C-H3: F<sub>C</sub>: C &#8594; InfoSp',
         'Valid — from AX-B1, RP-1; all four requirements verified; AX-G1 and AX-G2 checked in the stand-in InfoDepth (KleisliCat PMF has a '
         'terminal object). Lean: full functor (fc_functor, sorry-free). <font name="DV">&#10003;</font>'],
        ['C-H4: F<sub>D</sub>: C &#8594; Hilb',
         'Valid — the object map at 0 by assignment (ZP-D D2(i)), the morphism map from ZP-D D2(iii) and D2(iv), D2(iv) under DP-1; all four requirements verified; AX-G1 and AX-G2 checked in the stand-in HilbDimDepth (both fail in ModuleCat '
         '&#8450;). Lean: full functor (fd_functor, sorry-free). <font name="DV">&#10003;</font>'],
        ['T-H1: Universal property preserved',
         'Valid — OQ-G2 closed. fb_functor, fc_functor and fd_functor send 0 to an initial object of their stand-in targets '
         '(fb_preserves_initial, fc_preserves_initial, fd_preserves_initial, each IsInitial.ofUnique 0, using none of the th1_* domain facts); '
         'for F<sub>A</sub>, 0 is initial in natZPCategory. <font name="DV">&#10003;</font>'],
        ['T-H2: Singularity reconciliation',
         'Valid — OQ-G4 closed. Categorical (undefined domain) and ZP-C (infinite accumulation) '
         'shown to hold together: the proof pairs ZP-G Lemma T3 with ZP-C Theorem T2 and uses neither '
         'to prove the other. <font name="DV">&#10003;</font>'],
        ['T-H3: four separately proved domain facts, conjoined',
         'Valid — Derived as a conjunction of four separately proved domain facts; no conjunct relates to another or is derived from a functor. T-SNAP inherited as derived theorem (ZP-E v2.0). '
         'DP-1 labelled as design premise. <font name="DV">&#10003;</font>'],
        ['Traceability register',
         'Valid — Complete. Every cross-framework claim traced to source theorem and bridge axiom. No floating connections.'],
        ['OQ-G1: Native surprisal derivation',
         'Closed in ZP-G v1.1 via D7\' and I-KC. No bridge axiom remains as a theorem premise.'],
        ['AX-1 (Binary Snap Causality)',
         'Retired — the shape is derived as T-SNAP in ZP-E v2.0 and is no longer an axiom; '
         'T-H3 and all downstream results inherit the derived status for the shape. '
         'That the Snap occurs is stated separately: it follows from the occurrence commitment together with DA-1 (closed given DP-2).'],
        ['AX-G1, AX-G2',
         'AX-G2 and the initial-object half of AX-G1 are grounded, not novel: AX-G2 by antisymmetry in categories built from a partial '
         'order with a least element, and it fails in ModuleCat &#8450; (see the Open Items register). The no-terminal half of AX-G1 is '
         'ZP-G\'s own commitment; it holds in the &#8469;-indexed stand-ins and fails in TopCat, ModuleCat &#8450; and KleisliCat PMF. '
         'Stated as local axioms in ZP-G for self-containment. Not gaps.'],
        ['R-BA, D-H1, DP-1',
         'Remark / Design Commitments — intentional. Explicitly stated. Not laundered.'],
    ]

    E.append(data_table(
        ['Component', 'Status / Notes'],
        val_rows,
        [TW*0.35, TW*0.65]
    ))

    E += [
        sp(12),
        Paragraph(
            '<i>End of ZP-H | Four instantiation functors constructed in this document | '
            'OQ-G1 through OQ-G4 closed | '
            'Three functors have concrete Lean Functor terms (sorry-free): '
            'fb_functor (Q&#8322;BallDepth), fc_functor (InfoDepth), fd_functor (HilbDimDepth); F<sub>A</sub> has the NatSLat ZPCategory instance, no functor term | '
            'OQ-G3 closed: PDF constructions for all four, Lean functor terms for three | '
            'T-SNAP inherited as derived theorem | '
            'T-H3 independence-of-discovery note: the null-analogs of ZP-A, ZP-B and ZP-C located independently, ZP-D&#8217;s e<sub>0</sub> by transport of ZP-B&#8217;s 0 | '
            'AX-G2 and the initial-object half of AX-G1 are grounded in prior layers where they hold, and the no-terminal half of '
            'AX-G1 is ZP-G\'s own commitment; AX-B1 is the framework\'s one '
        'substantive modelling commitment &#8212; discrete Boolean existence rather than a '
        'continuum of partial states. The <i>decide</i> proof only checks the two states are '
        'distinct GIVEN the two-element type; it does not verify the commitment</i>',
            S['note']),
    ]

    print(f'[build_zph] Calling doc.build() with {len(E)} elements...')
    doc.build(E)
    print(f'[build_zph] Written: {out_path}')


if __name__ == '__main__':
    build()
