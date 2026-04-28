"""
Build ZP-D: State Layer (Hilbert Space) (v1.6)
v1.6: R3 added — topological type of T stated explicitly: locally constant, continuous from
      (Q2, 2-adic topology) to H; connected-space concern addressed.
v1.5: D1 updated — n = 2 foundational minimum; higher n derived, not foundational.
v1.4: T5 proof corrected — ball-boundary argument replaces D2(v) citation.
"""

import os
from zp_utils import *

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-D_State_Layer_v1_6.pdf')
    doc = make_doc(out_path, 'ZP-D: State Layer (Hilbert Space)', 'ZP-D', 'Version 1.6')
    E = []
    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-D: State Layer (Hilbert Space)', S['subtitle']),
          Paragraph('Version 1.6  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.5  |  R3 added: topological type of T stated explicitly — '
                    'locally constant; continuous from (Q<sub>2</sub>, 2-adic topology) to H; '
                    'totally-disconnected/connected-space concern addressed</i>', S['subtitle']),
          Paragraph('<i>v1.5: D1 updated — n = 2 foundational minimum. '
                    'v1.4: T5 proof corrected — ball-boundary argument.</i>', S['subtitle']),
          sp(10),
          body('This document operates within functional analysis. It imports from ZP-A and ZP-B and constructs the Hilbert space state layer on top of them. No information theory from ZP-C is imported. Cross-framework synthesis is deferred to ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-D Illustrated Companion provides concrete examples and visual intuitions for the results here. Examples are kept separate from the formal layers to distinguish illustrative material from proofs.</i>'),
          body('<i>Version 1.4 change: T5 proof corrected. Prior proof cited D2(v) (global lower bound ‖T(x)‖ ≥ ‖T(0)‖) as justification for sequence monotonicity — this does not follow. Correct proof uses ball-boundary argument: norm is non-decreasing because T maps each clopen ball to a single basis vector; crossing a ball boundary adds a component (strict increase); staying within a ball gives equality. T5 is renamed "Non-Decreasing Norms" to reflect this precisely.</i>'),
          body('<i>Version 1.3 change: Theorem/Proposition hierarchy applied. T3 relabelled Proposition. T5 relabelled Proposition. T2 and T4 retain Theorem labels.</i>'),
          body('<i>Version 1.2 change: Theorem T1 is reclassified as Design Principle DP-1. Orthogonality is a design commitment — well-motivated and explicit — but chosen, not derived.</i>'),
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
        'T3: Topological isolation of 0.',
        'T5: Q<sub>2</sub> is totally disconnected.',
        'C3: Snap is topologically irreversible (corollary of T5).',
        '&#949;<sub>0</sub>: Minimum viable deviation, universe-contingent parameter (D5).',
    ]))

    E.append(Paragraph('II. The Hilbert Space State Layer', S['h1']))
    E.append(label_box('Definition D1 — State Layer H', [
        'H = &#8450;<super>n</super> is a complex Hilbert space with orthonormal basis {e<sub>0</sub>, e<sub>1</sub>, &#8230;}.',
        'The foundational minimum is n = 2, corresponding to the two ontological states of the framework: '
        '&#8869; (null state, mapped to e<sub>0</sub>) and &#949;<sub>0</sub> (first atomic state, mapped to e<sub>1</sub>). '
        'These two orthogonal vectors express the binary existence/non-existence distinction that is the '
        'framework\'s central object. All further states are derived from this pair as joins in (L, &#8744;, &#8869;) '
        '&#8212; they require no additional foundational dimension.',
        'The framework\'s core claims (T4: snap produces orthogonal shift; T5: monotone norms) are '
        'established at n = 2. Extensions to higher n are consistent and natural: for level-k '
        'approximations using the clopen ball partition of Q<sub>2</sub> at depth k, n = 2<super>k</super>. '
        'No foundational claim of the framework requires n &gt; 2.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R1 — Decoupling of Topological and State Layers', [
        'Q<sub>2</sub> and H are categorically distinct structures. Q<sub>2</sub> is a topological field; H is a Hilbert space over &#8450;. They share no operations.',
        'The transition operator T: Q<sub>2</sub> &#8594; H is the only bridge. It is constructed explicitly in T2.',
        'No operation in H is assumed to inherit a topological property of Q<sub>2</sub> without proof. Every cross-layer claim must go through T.',
    ]))

    E.append(Paragraph('III. The Transition Operator T: Q₂ &#8594; H', S['h1']))
    E.append(Paragraph('3.1  The Design Commitment — Orthogonality', S['h2']))
    E.append(label_box('Design Principle DP-1 — Orthogonality as the Representation of Topological Isolation  [reclassified from T1 in v1.1]', [
        'Topological isolation in Q<sub>2</sub> (T3: 0 is isolated; clopen balls are mutually separated) is represented in H by orthogonality: elements that are topologically isolated in Q<sub>2</sub> map to orthogonal vectors in H.',
        'Motivation: Orthogonality in H is the natural algebraic analogue of topological separation. &#10216;e<sub>i</sub>, e<sub>j</sub>&#10217; = 0 for i &#8800; j; two clopen balls are maximally distinct in the topological sense.',
        'Status: DESIGN PRINCIPLE — DP-1 is chosen, not derived. It is the natural and consistent choice, stated explicitly. T4 and T5 below depend on DP-1 as a premise.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.2  The Construction Target', S['h2']))
    E.append(label_box('Definition D2 — Transition Operator T (Requirements)', [
        'T: Q<sub>2</sub> &#8594; H must satisfy:',
        '(i)   T(0) = e<sub>0</sub>   (null state maps to the designated base vector)',
        '(ii)  T(&#949;<sub>0</sub>) = e<sub>1</sub>   (minimum deviation maps to the first non-base vector)',
        '(iii) T is injective on the clopen ball partition',
        '(iv)  If x and y are in disjoint clopen balls, then &#10216;T(x), T(y)&#10217; = 0   (DP-1)',
        '(v)   &#8214;T(x)&#8214; &#8805; &#8214;T(0)&#8214; for all x   (norm-increasing: additive ontology preserved)',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.3  Existence of T', S['h2']))
    E.append(label_box('Theorem T2 — Existence of T (Basis Assignment)', [
        'There exists a function T: Q<sub>2</sub> &#8594; H satisfying all five requirements of D2.',
        'Proof: Construct T by basis assignment. The clopen ball partition of Q<sub>2</sub> at level k consists of 2<super>k</super> disjoint clopen balls. Assign each ball to a distinct basis vector of H. T(x) = e<sub>i</sub> where i is the index of the ball containing x.',
        '(i) 0 maps to e<sub>0</sub> by assignment. <font name="DV">&#10003;</font>  (ii) &#949;<sub>0</sub> maps to e<sub>1</sub> by assignment. <font name="DV">&#10003;</font>  (iii) Distinct balls &#8594; distinct basis vectors. <font name="DV">&#10003;</font>  (iv) Disjoint balls &#8594; orthogonal basis vectors. <font name="DV">&#10003;</font>  (v) All basis vectors have norm 1 &#8805; &#8214;e<sub>0</sub>&#8214; = 1. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R3 — Topological Type of T', [
        'T is locally constant: it is constant on each clopen ball of Q<sub>2</sub>. This follows directly from '
        'DP-1 — topological isolation maps to orthogonality, so T does not interpolate between basis '
        'vectors across ball boundaries.',
        'Continuity: T is continuous from (Q<sub>2</sub>, 2-adic topology) to H. The image of T is a '
        'discrete set of basis vectors {e<sub>0</sub>, e<sub>1</sub>, &#8230;}. Each preimage T<super>&#8722;1</super>(e<sub>i</sub>) '
        'is a clopen ball of Q<sub>2</sub>, which is open in the 2-adic topology. Therefore preimages of '
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
        'Any two operators T, T\': Q<sub>2</sub> &#8594; H satisfying D2 are related by a unitary transformation U: H &#8594; H such that T\' = U &#8728; T.',
        'Proof: T and T\' both assign e<sub>0</sub> to the image of 0, which is the unique additive identity (A4). The ball structure of Q<sub>2</sub> is fixed; only the labelling of basis vectors varies. A unitary map U taking T(0) to T\'(0) and preserving orthogonality relations defines the equivalence. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — What T Is Not', [
        'T is not a ring homomorphism. Q<sub>2</sub> has field operations; H does not. T does not preserve addition or multiplication from Q<sub>2</sub>.',
        'T is not a topological embedding. The topology of H is the norm topology; the topology of Q<sub>2</sub> is the 2-adic ultrametric. T is a structure-preserving assignment: ontological distinctions (topological isolation in Q<sub>2</sub>) map to algebraic distinctions (orthogonality in H), as specified by DP-1.',
    ]))

    E.append(Paragraph('IV. The Binary Snap in H', S['h1']))
    E.append(label_box('Theorem T4 — Snap Produces Orthogonal Shift in H', [
        'The Binary Snap 0 &#8594; &#949;<sub>0</sub> in Q<sub>2</sub> maps to an orthogonal shift in H: T(0) = e<sub>0</sub> and T(&#949;<sub>0</sub>) = e<sub>1</sub>, and &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0.',
        'Proof: By D2(i), T(0) = e<sub>0</sub>. By D2(ii), T(&#949;<sub>0</sub>) = e<sub>1</sub>. Since 0 and &#949;<sub>0</sub> are in disjoint clopen balls of Q<sub>2</sub> (T3), D2(iv) and DP-1 give &#10216;T(0), T(&#949;<sub>0</sub>)&#10217; = &#10216;e<sub>0</sub>, e<sub>1</sub>&#10217; = 0. <font name="DV">&#10003;</font>',
        'Status: Derived — unconditional theorem given DP-1.',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T5 — Monotone Sequences Map to Non-Decreasing Norms', [
        'Let (S<sub>n</sub>) be a monotone state sequence in L (ZP-A T3). Then &#8214;T(S<sub>n</sub>)&#8214; &#8804; &#8214;T(S<sub>n+1</sub>)&#8214; for all n.',
        'Proof: By ZP-A T3, S<sub>n</sub> &#8804; S<sub>n+1</sub>. T maps each clopen ball of Q<sub>2</sub> to a single basis vector (D2). '
        'If S<sub>n</sub> and S<sub>n+1</sub> lie in different clopen balls, T(S<sub>n+1</sub>) carries an additional basis component, giving &#8214;T(S<sub>n+1</sub>)&#8214; > &#8214;T(S<sub>n</sub>)&#8214;. '
        'If they lie in the same ball, T(S<sub>n</sub>) = T(S<sub>n+1</sub>), giving equality. '
        'In both cases &#8214;T(S<sub>n</sub>)&#8214; &#8804; &#8214;T(S<sub>n+1</sub>)&#8214;. '
        'Note: D2(v) gives a global lower bound &#8214;T(x)&#8214; &#8805; &#8214;T(0)&#8214; — this does not imply sequence monotonicity; the ball-boundary argument above is the correct proof. <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('V. Open Items Register for ZP-D v1.6', S['h1']))
    E.append(data_table(
        ['Item', 'Status', 'Description'],
        [['DP-1: Orthogonality commitment', 'Design Principle — explicit', 'Reclassified from Theorem T1. Orthogonality is chosen, not derived. Content unchanged.'],
         ['T2: Existence of T', 'Closed', 'Basis assignment construction. All five requirements verified.'],
         ['T3: Uniqueness of T', 'Closed', 'Unique up to unitary equivalence.'],
         ['T4: Snap &#8594; orthogonal shift', 'Closed — unconditional', 'Proven from T2 and ZP-B T3. Depends on DP-1 as premise.'],
         ['T5: Monotone norms', 'Closed — unconditional', 'Proven from T2 and ZP-A T3.']],
        [1.6*inch, 1.5*inch, 3.4*inch]
    ))

    E.append(Paragraph('VI. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['H = &#8450;<super>n</super> (D1)', 'Valid — Defined; foundational minimum n = 2 (binary existence/non-existence); '
          'extensions to n = 2<super>k</super> consistent; no core claim requires n &gt; 2'],
         ['Decoupling of Q<sub>2</sub> and H (R1)', 'Valid — Structural; Q<sub>2</sub> and H are categorically distinct; T is the bridge'],
         ['Import I-A from ZP-A', 'Valid — Received; CC-1 reclassification noted'],
         ['Import I-B from ZP-B', 'Valid — Received; MP-1 included; C3 noted'],
         ['DP-1: Orthogonality', 'Valid — Design Principle; reclassified from T1; well-motivated and explicit'],
         ['D2: T requirements', 'Valid — Defined; five requirements stated; all satisfied by T2'],
         ['T2: Existence of T', 'Valid — Derived; basis assignment; all five requirements verified; '
          'R3 (v1.6) names topological type: locally constant, continuous'],
         ['T3: Uniqueness of T', 'Valid — Proposition; derived; unique up to unitary equivalence'],
         ['T4: Snap &#8594; orthogonal shift', 'Valid — Theorem; derived; unconditional; depends on DP-1'],
         ['T5: Monotone norms', 'Valid — Proposition; derived; unconditional; from T2 and ZP-A T3']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
