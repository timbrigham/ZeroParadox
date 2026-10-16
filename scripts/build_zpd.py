"""
Build ZP-D: State Layer (Hilbert Space) (v1.18)
"""

import os
from zp_utils import *

VERSION = '1.18'
FIRST_RELEASED = 'April 2026'

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-D_State_Layer.pdf')
    doc = make_doc(out_path, 'ZP-D: State Layer (Hilbert Space)', 'ZP-D', 'Version ' + VERSION)
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-D: State Layer (Hilbert Space)', S['subtitle']),
          Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
          sp(10),
          body('This document operates within functional analysis. It imports from ZP-A and ZP-B and constructs the Hilbert space state layer on top of them. No information theory from ZP-C is imported. Cross-framework synthesis is deferred to ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-D Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
          sp()]

    E.append(Paragraph('I. Imported Structure', S['h1']))
    E.append(Paragraph('1.1  From ZP-A: Algebraic Structure of States', S['h2']))
    E.append(label_box('Import I-A — From ZP-A: Lattice Algebra', [
        '(L, &#8744;, &#8869;): join-semilattice with bottom. Axioms A1&#8211;A4.',
        '&#8804; partial order: x &#8804; y :&#10234; x &#8744; y = y (D1, T1).',
        '&#8869; is the global minimum: &#8869; &#8804; x for all x &#8712; L (T2).',
        'State transitions are joins: f(x) = x &#8744; &#945; (D2).',
        'State sequences are monotone: S<sub>n</sub> &#8804; S<sub>n+1</sub> (T3).',
        'CC-1: S<sub>0</sub> = &#8869; — Conditional Claim; modelling commitment.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('1.2  From ZP-B: Topological Domain', S['h2']))
    E.append(label_box('Import I-B — From ZP-B: p-Adic Topology', [
        'AX-B1: Binary Existence Axiom.',
        'MP-1: Minimality Principle.',
        'T0: p = 2 derived from AX-B1 and MP-1.',
        'Q<sub>2</sub> with 2-adic metric d (D1, D2).',
        'T1: Ultrametric (strong triangle inequality).',
        'T2: Every ball is clopen.',
        'T3: Clopen gap at 0.',
        'T5: Q<sub>2</sub> is totally disconnected.',
        'C3: Snap is topologically irreversible (corollary of T5).',
        '&#949;<sub>0</sub>: Minimum viable deviation, universe-contingent parameter (D5).',
    ]))

    E.append(Paragraph('II. The Hilbert Space State Layer', S['h1']))
    E.append(label_box('Definition D1 — State Layer H', [
        'H = &#8450;<super>n</super> is a complex Hilbert space with orthonormal basis {e<sub>0</sub>, e<sub>1</sub>, &#8230;}.',
        'The foundational minimum is n = 2, corresponding to the two ontological states of the framework: '
        '&#8869; of OntologicalStates (mapped to e<sub>0</sub>) and &#949;<sub>0</sub>, the state off &#8869; of OntologicalStates (mapped to e<sub>1</sub>). '
        'These two orthogonal vectors express the binary existence/non-existence distinction that is the '
        'framework\'s central object. All further states are derived from this pair as joins in (L, &#8744;, &#8869;) '
        '&#8212; they require no additional foundational dimension.',
        'The orthogonality &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0 that T4 uses is a fact about H alone and holds at n = 2. '
        'T4 and T5 as stated are about T: Q<sub>2</sub> &#8594; H, so they hold at a level only where T exists (T2). The level-k partition P<sub>k</sub> of Q<sub>2</sub> has n = 2<super>k</super> + 1 '
        'cells: the 2<super>k</super> balls of radius 2<super>&#8722;k</super> that make up Z<sub>2</sub>, '
        'the 2-adic integers, and the one clopen set Q<sub>2</sub> \\ Z<sub>2</sub>. Level 0 gives n = 2: '
        'Z<sub>2</sub> and its complement. By T2 a map T exists at level 0 exactly when v<sub>2</sub>(&#949;<sub>0</sub>) &lt; 0, '
        'that is, when &#949;<sub>0</sub> lies outside Z<sub>2</sub>; otherwise T needs a level k &gt; v<sub>2</sub>(&#949;<sub>0</sub>) '
        'and n = 2<super>k</super> + 1.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R1 — Decoupling of Topological and State Layers', [
        'Q<sub>2</sub> and H are categorically distinct structures. Q<sub>2</sub> is a topological field; H is a Hilbert space over &#8450;. They share no operations.',
        'The transition operator T: Q<sub>2</sub> &#8594; H is the only bridge. It is constructed explicitly in T2.',
        'No operation in H is assumed to inherit a topological property of Q<sub>2</sub> without proof. Every cross-layer claim must go through T.',
    ]))

    E.append(Paragraph('III. The Transition Operator T: Q₂ &#8594; H', S['h1']))
    E.append(Paragraph('3.1  The Design Commitment — Orthogonality', S['h2']))
    E.append(label_box('Design Principle DP-1 — Orthogonality as the Representation of Clopen Separation', [
        'Clopen separation in Q<sub>2</sub> (ZP-B T3: 0 is clopen-separated from all nonzero elements; clopen balls are mutually separated) is represented in H by orthogonality: at the chosen level k, points in different cells of the clopen partition P<sub>k</sub> (D1) map to orthogonal vectors in H. Any two distinct points of Q<sub>2</sub> lie in disjoint balls, so the same requirement stated over all disjoint balls would make the images of every two distinct points orthogonal; with nonzero images, as D2(v) requires, that is an orthogonal family indexed by all of Q<sub>2</sub>, which no finite-dimensional H holds (an orthonormal family in &#8450;<super>n</super> is finite; the example after dp1_orthogonality in ZeroParadox/State/StateSpace.lean). Without the nonzero premise the zero map would meet it. P<sub>k</sub> is the finite partition it is stated over.',
        'Motivation: Orthogonality in H is the natural algebraic analogue of topological separation. &#10216;e<sub>i</sub>, e<sub>j</sub>&#10217; = 0 for i &#8800; j; two clopen balls are maximally distinct in the topological sense.',
        'Status: DESIGN PRINCIPLE — DP-1 is chosen, not derived. It is the natural and consistent choice, stated explicitly. T4 and T5 below depend on DP-1 as a premise.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.2  The Construction Target', S['h2']))
    E.append(label_box('Definition D2 — Transition Operator T (Requirements)', [
        'T: Q<sub>2</sub> &#8594; H must satisfy:',
        '(i)   T(0) = e<sub>0</sub>   (0 of Q<sub>2</sub>, read as &#8869;, maps to the designated base vector)',
        '(ii)  T(&#949;<sub>0</sub>) = e<sub>1</sub>   (minimum deviation maps to the first non-base vector)',
        '(iii) T is constant on each cell of P<sub>k</sub>, and points in different cells have different images',
        '(iv)  If x and y lie in different cells of P<sub>k</sub>, then &#10216;T(x), T(y)&#10217; = 0   (DP-1)',
        '(v)   &#8214;T(x)&#8214; = 1 for all x   (unit norm)',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.3  Existence of T', S['h2']))
    E.append(label_box('Theorem T2 — Existence of T (Basis Assignment)', [
        'At each level k with k &gt; v<sub>2</sub>(&#949;<sub>0</sub>), and at no other level, there exists a function T: Q<sub>2</sub> &#8594; H, with n = 2<super>k</super> + 1, satisfying all five requirements of D2 relative to P<sub>k</sub>.',
        'Proof: Construct T by basis assignment. P<sub>k</sub> has 2<super>k</super> + 1 cells (D1). Assign e<sub>0</sub> to the cell containing 0, e<sub>1</sub> to the cell containing &#949;<sub>0</sub>, and the remaining basis vectors to the remaining cells, one each. T(x) = e<sub>i</sub> where i is the index of the cell containing x; every x outside Z<sub>2</sub> maps to the one vector assigned to Q<sub>2</sub> \\ Z<sub>2</sub>. The cell of 0 is the ball 2<super>k</super>Z<sub>2</sub>, the points of valuation at least k, and &#949;<sub>0</sub> is a point of Q<sub>2</sub> at rung v<sub>2</sub>(&#949;<sub>0</sub>) (ZP-B D5), so it lies in that cell exactly when v<sub>2</sub>(&#949;<sub>0</sub>) &#8805; k. So 0 and &#949;<sub>0</sub> lie in different cells exactly when k &gt; v<sub>2</sub>(&#949;<sub>0</sub>). Otherwise no T satisfies D2 at level k: 0 and &#949;<sub>0</sub> share a cell, so D2(iii) forces T(0) = T(&#949;<sub>0</sub>), while D2(i) and D2(ii) require T(0) = e<sub>0</sub> and T(&#949;<sub>0</sub>) = e<sub>1</sub> &#8800; e<sub>0</sub>. When &#949;<sub>0</sub> lies outside Z<sub>2</sub>, every level k &#8805; 0 qualifies, level 0 included.',
        '(i) 0 maps to e<sub>0</sub> by assignment. <font name="DV">&#10003;</font>  (ii) &#949;<sub>0</sub> maps to e<sub>1</sub> by assignment, its cell differing from that of 0. <font name="DV">&#10003;</font>  (iii) T is constant on each cell by construction, and distinct cells &#8594; distinct basis vectors. <font name="DV">&#10003;</font>  (iv) Different cells &#8594; orthogonal basis vectors. <font name="DV">&#10003;</font>  (v) Every basis vector has norm 1. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R3 — Topological Type of T', [
        'T is locally constant: it is constant on each cell of P<sub>k</sub>, and each cell is clopen in '
        'Q<sub>2</sub>. This is required by D2(iii), and the construction in T2 meets it: T does not interpolate between basis '
        'vectors across cell boundaries.',
        'Continuity: T is continuous from (Q<sub>2</sub>, 2-adic topology) to H. The image of T is a '
        'discrete set of basis vectors {e<sub>0</sub>, e<sub>1</sub>, &#8230;}. Each preimage T<super>&#8722;1</super>(e<sub>i</sub>) '
        'is a cell of P<sub>k</sub>, either a ball inside Z<sub>2</sub> or the set Q<sub>2</sub> \\ Z<sub>2</sub>, '
        'and each is open in the 2-adic topology. Therefore preimages of '
        'open sets in H are open in Q<sub>2</sub>, and T is continuous. &#10003;',
        'Note on connected spaces: Q<sub>2</sub> is totally disconnected; H = &#8450;<super>n</super> with the norm '
        'topology is path-connected. A continuous map from a totally disconnected space to a '
        'connected space need not be constant &#8212; it must only have a totally disconnected image. '
        'T\'s image is a discrete (hence totally disconnected) set of basis vectors, '
        'which is consistent with both the total disconnectedness of Q<sub>2</sub> and the '
        'path-connectedness of H as a whole.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.4  Uniqueness of T', S['h2']))
    E.append(label_box('Proposition T3 — Uniqueness of T up to Unitary Equivalence', [
        'Any two operators T, T\': Q<sub>2</sub> &#8594; H satisfying D2 at the same level k, with n = 2<super>k</super> + 1, are related by a unitary transformation U: H &#8594; H such that T\' = U &#8728; T.',
        'Proof: By D2(iii), T and T\' are each constant on every cell of P<sub>k</sub>, so each is a map from the 2<super>k</super> + 1 cells into H. By D2(iv) and D2(v), each sends distinct cells to orthogonal unit vectors, so each image set is an orthonormal basis of H = &#8450;<super>n</super>. The linear map U sending T(c) to T\'(c) for every cell c is unitary, and T\' = U &#8728; T. Lean: t3_uniqueness relates any cell-indexed map with unit-norm, pairwise-orthogonal values to the basis assignment transitionOp; the two-sided form above follows by composing two such unitaries (the example after t3_uniqueness, ZeroParadox/State/StateSpace.lean). <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — What T Is Not', [
        'T is not a ring homomorphism. Q<sub>2</sub> has field operations; H does not. T does not preserve addition or multiplication from Q<sub>2</sub>.',
        'T is not a topological embedding. The topology of H is the norm topology; the topology of Q<sub>2</sub> is the 2-adic ultrametric. T is a structure-preserving assignment: ontological distinctions (clopen separation in Q<sub>2</sub>) map to algebraic distinctions (orthogonality in H), as specified by DP-1.',
    ]))
    E.append(sp(4))
    E.append(remark_box('Remark R-PA — What T Is, in Standard Terms (Prior Art)', [
        'Representing the clopen-ball structure of Q<sub>2</sub> by orthogonal unit vectors in a Hilbert space is the standard p-adic construction, not a ZP novelty. In L<super>2</super> of the Haar measure, the indicator functions of two disjoint balls of one level are orthogonal and of equal length, so the normalized indicators of the balls of one level form an orthonormal system. T\'s basis assignment (T2) follows that pattern on the 2<super>k</super> level-k balls of Z<sub>2</sub>, and adds one further orthogonal vector for the cell Q<sub>2</sub> \\ Z<sub>2</sub>, which has infinite Haar measure, so its indicator is not in L<super>2</super>. Indicators of nested balls are not orthogonal, since the smaller ball has positive measure. One orthonormal basis of L<super>2</super>(Q<sub>p</sub>) built on balls is Kozyrev\'s p-adic wavelet basis, the analog of the Haar basis and an eigenbasis of the Vladimirov operator (Kozyrev, 2002). The van der Put basis, also made of ball indicators, expands every continuous function from Z<sub>p</sub> to Q<sub>p</sub> as a series; its balls nest, so it is not an orthonormal system in L<super>2</super>. It is orthonormal in the non-Archimedean sense, as a basis of the Banach space of continuous functions from Z<sub>p</sub> to Q<sub>p</sub> under the supremum norm (Schikhof, Ultrametric Calculus (1984), Theorem 62.2; see Bolivar-Barbosa, Le&#243;n-Cardenal and Rodr&#237;guez-Vega (2022), Theorem 2.1).',
        'ZP-D\'s contribution is not the embedding itself but the specific reading in DP-1 &#8212; clopen separation &#8614; orthogonality &#8212; that carries the Binary Snap into the state layer. On the balls of Z<sub>2</sub>, T is an instance of the recognized construction; the one further vector, for the cell Q<sub>2</sub> \\ Z<sub>2</sub>, is added by T2 and corresponds to no normalized indicator in L<super>2</super>.',
    ]))

    E.append(Paragraph('IV. The Binary Snap in H', S['h1']))
    E.append(label_box('Theorem T4 — Snap Produces Orthogonal Shift in H', [
        'The Binary Snap 0 &#8594; &#949;<sub>0</sub> in Q<sub>2</sub> maps to an orthogonal shift in H: T(0) = e<sub>0</sub> and T(&#949;<sub>0</sub>) = e<sub>1</sub>, and &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0.',
        'Proof: By D2(i), T(0) = e<sub>0</sub>. By D2(ii), T(&#949;<sub>0</sub>) = e<sub>1</sub>. Since 0 and &#949;<sub>0</sub> lie in different cells of P<sub>k</sub> at a level k &gt; v<sub>2</sub>(&#949;<sub>0</sub>) (T2), D2(iv) and DP-1 give &#10216;T(0), T(&#949;<sub>0</sub>)&#10217; = &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0. <font name="DV">&#10003;</font>',
        'Status: Derived — unconditional theorem given DP-1.',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T5 — Monotone Sequences Map to Non-Decreasing Norms', [
        'Let (S<sub>n</sub>) be a monotone state sequence in L (ZP-A T3). Then &#8214;T(S<sub>n</sub>)&#8214; &#8804; &#8214;T(S<sub>n+1</sub>)&#8214; for all n.',
        'Reading of T(S<sub>n</sub>): T is a map on Q<sub>2</sub>, and S<sub>n</sub> is a state of L. Here each state is read through a chosen assignment &#963; of states of L to cells of P<sub>k</sub>, a modelling choice that this document does not derive, and T(S<sub>n</sub>) is the vector T assigns to the cell &#963;(S<sub>n</sub>). The Lean takes the cell indices directly, a sequence S: &#8469; &#8594; Fin n.',
        'T5 norm result: Derived — immediate from D2(v). '
        'Note: by D2(v), every T-image is a unit vector — all norms equal 1. '
        'The norm inequality &#8214;T(S<sub>n</sub>)&#8214; &#8804; &#8214;T(S<sub>n+1</sub>)&#8214; is therefore satisfied trivially (1 &#8804; 1). '
        'The Lean proof (t5_monotone_norms) verifies this tautology; it does not verify the ball-boundary argument. '
        '<font name="DV">&#10003;</font>',
        'T5-b — Strict Orthogonality (non-trivial content, Lean-verified): For any state sequence whose consecutive states are assigned distinct cells, &#963;(S<sub>n</sub>) &#8800; &#963;(S<sub>n+1</sub>), consecutive T-images are orthogonal: '
        '&#10216;T(S<sub>n</sub>), T(S<sub>n+1</sub>)&#10217; = 0. When &#963; is injective, S<sub>n</sub> &#8800; S<sub>n+1</sub> suffices; when it is not, two distinct states in one cell share one vector and the conclusion fails. '
        'Proof: by DP-1, distinct cells map to orthogonal basis vectors. Therefore T(S<sub>n</sub>) &#8869; T(S<sub>n+1</sub>). '
        'Lean: t5_strict_orthogonal (uses DP-1 via t2_orthogonal; #print axioms: propext, Classical.choice, Quot.sound). <font name="DV">&#10003;</font>',
        'T5-b is the load-bearing result: it captures the genuine content of the ball-boundary structure and is the Hilbert-space expression of ZP-B C3 (topological irreversibility) applied to consecutive states.',
    ]))

    E.append(Paragraph('V. Open Items Register', S['h1']))
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        [['DP-1: Orthogonality commitment', 'Design Principle — explicit', 'Reclassified from Theorem T1. Orthogonality is chosen, not derived. Content unchanged.'],
         ['T2: Existence of T', 'Closed', 'Basis assignment construction at each level k &gt; v<sub>2</sub>(&#949;<sub>0</sub>), and no T at any other level. All five requirements verified.'],
         ['T3: Uniqueness of T', 'Closed', 'Unique up to unitary equivalence.'],
         ['T4: Snap &#8594; orthogonal shift', 'Closed — unconditional', 'Proven from T2 and ZP-B T3. Depends on DP-1 as premise.'],
         ['T5: Monotone norms + T5-b: Strict orthogonality', 'Closed — T5 from D2(v); T5-b given DP-1',
          'T5 norm result: trivially satisfied (all norms = 1 by D2(v)). '
          'T5-b: consecutive states in distinct cells produce orthogonal T-images — non-trivial, Lean-verified (t5_strict_orthogonal).']],
        [1.6*inch, 1.5*inch, 3.4*inch]
    ))

    E.append(Paragraph('VI. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['H = &#8450;<super>n</super> (D1)', 'Valid — Defined; foundational minimum n = 2 (binary existence/non-existence); '
          'level-k partition P<sub>k</sub> gives n = 2<super>k</super> + 1 (level 0 gives n = 2, carrying T exactly when v<sub>2</sub>(&#949;<sub>0</sub>) &lt; 0)'],
         ['Decoupling of Q<sub>2</sub> and H (R1)', 'Valid — Structural; Q<sub>2</sub> and H are categorically distinct; T is the bridge'],
         ['Import I-A from ZP-A', 'Valid — Received; CC-1 reclassification noted'],
         ['Import I-B from ZP-B', 'Valid — Received; MP-1 included; C3 noted'],
         ['DP-1: Orthogonality', 'Valid — Design Principle; reclassified from T1; well-motivated and explicit'],
         ['D2: T requirements', 'Valid — Defined; five requirements stated; all satisfied by T2'],
         ['T2: Existence of T', 'Valid — Derived; basis assignment at each level k &gt; v<sub>2</sub>(&#949;<sub>0</sub>), none at other levels; all five requirements verified; '
          'R3 names topological type: locally constant, continuous'],
         ['T3: Uniqueness of T', 'Valid — Proposition; derived; unique up to unitary equivalence'],
         ['T4: Snap &#8594; orthogonal shift', 'Valid — Theorem; derived; unconditional; depends on DP-1'],
         ['T5 / T5-b: Monotone norms + strict orthogonality',
          'Valid — T5 norm result: tautology of D2(v) (all norms = 1); Lean: t5_monotone_norms. '
          'T5-b: non-trivial Lean-verified result — consecutive states in distinct cells produce orthogonal T-images via DP-1; Lean: t5_strict_orthogonal (#print axioms: propext, Classical.choice, Quot.sound).']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
