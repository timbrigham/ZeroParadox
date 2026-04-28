"""
Build ZP-A: Lattice Algebra (v1.11)
v1.11: ZF+AFA metatheoretic declaration added before Section I; plain English preface added
immediately before CC-1 (§4.2). No mathematical content changed.
v1.10: CC-1 box title updated — "Conditional Claim CC-1" replaced with "CC-1 (Derived/Conditional)"
to avoid reading inconsistency for readers of ZP-A in isolation. The status row inside the box
already accurately states the dual status; the title now reflects it at first glance.
v1.9: CC-1 status updated — now derived as a structural consequence in AFAStructure lattices
via ZP-J T-EXEC (IsQuineAtom(⊥) is unique; S₀ = ⊥ follows structurally). Status line and
validation table updated. Remains a modelling commitment at the ZP-A level without AFAStructure.
v1.8: CC-2 cross-framework note added — Foundation incompatibility with R3 and L-INF noted;
AFA identified as forced rather than chosen. Foundation note in Section V updated accordingly.
Cross-reference to ZP-E Remark R-AFA.
v1.7: R3 dependency note added — the inference "no external interpreter → necessarily executing"
requires D7's exhaustive static/executing dichotomy (ZP-E) as background. R3 supplies the
structural route to eliminating the static-description state; D7 supplies the exhaustiveness.
All three DA-1 paths share D7 as background; independence is among their arguments, not from D7.
"""

import os
from zp_utils import *

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-A_Lattice_Algebra_v1_11.pdf')
    doc = make_doc(out_path, 'ZP-A: Lattice Algebra', 'ZP-A', 'Version 1.11')
    E = []

    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-A: Lattice Algebra', S['subtitle']),
          Paragraph('Version 1.11  |  April 2026', S['subtitle']),
          Paragraph('<i>Supersedes v1.10  |  v1.11: ZF+AFA metatheoretic declaration added before Section I; plain English preface added immediately before CC-1 (&#167;4.2). No mathematical content changed. | v1.10: CC-1 box title updated &#8212; "Conditional Claim CC-1" replaced with "CC-1 (Derived/Conditional)" to reflect dual status at first glance for ZP-A-only readers. | v1.9: CC-1 status updated &#8212; derived as structural consequence in AFAStructure lattices via ZP-J T-EXEC; modelling commitment at ZP-A level without AFAStructure assumption.</i>', S['subtitle']),
          sp(10),
          body('This document is self-contained within abstract algebra. No topology, probability, or Hilbert space is imported. Every claim is provable using only the tools of semilattice theory. Cross-framework connections are deferred to ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-A Illustrated Companion document provides concrete examples and visual intuitions for the results in this document. Examples are kept separate from the formal layers to distinguish illustrative material from proofs. The companion is a reading aid; no proof-critical judgements should be drawn from examples alone.</i>'),
          body('<i>Version 1.9 changes: CC-1 status updated — ZP-J T-EXEC establishes IsQuineAtom(&#8869;) as the unique structural identity in any AFAStructure lattice; S<sub>0</sub> = &#8869; follows structurally. Status line in CC-1 block, Validation Status table, and Boundary Conditions table updated to reflect this derivation. At the ZP-A level (no AFAStructure assumed within this document), CC-1 remains a modelling commitment; the derivation is noted as a cross-framework result.</i>'),
          body('<i>Version 1.8 changes: CC-2 block updated with a cross-framework note: the replacement of Foundation by AFA is not arbitrary — ZF + Foundation is incompatible with R3 (a well-founded &#8869; admits an external interpreter, contradicting CC-2) and with ZP-C L-INF (bounded &#8712;-depth contradicts unbounded surprisal). AFA is forced rather than chosen; the Quine atom form is the minimal commitment within AFA. Foundation note in Section V updated to reflect this. Cross-reference to ZP-E Remark R-AFA added within CC-2.</i>'),
          body('<i>Version 1.7 changes: R3 dependency note added. The inference from "no external interpreter" (CC-2) to "necessarily executing" (DA-1) uses D7&#8217;s exhaustive static/executing dichotomy (ZP-E) as background. R3 supplies the structural argument for eliminating &#8869;&#8217;s static-description state; it does not independently derive DA-1 without D7. All three DA-1 paths in ZP-E share D7 as background; they provide independent structural, informational, and AIT-based routes to eliminating the static-description alternative. Section V intro and R3 text updated to make this dependency explicit. Boundary Conditions table row for CC-2/R3 updated accordingly.</i>'),
          body('<i>Version 1.6 changes: CC-2 (Self-Containment of &#8869;) added as a new modeling commitment: &#8869; = {&#8869;} is a Quine atom under ZF + AFA (Aczel&#8217;s Anti-Foundation Axiom). R3 added immediately following CC-2. Foundation note added: the framework is stated over ZF + AFA; the Axiom of Choice is not assumed. Section V dedicated to self-containment of &#8869;; OQ-A1 renumbered VI, Boundary Conditions VII, Validation Status VIII.</i>'),
          body('<i>Version 1.5 changes: (1) Theorem/Proposition/Lemma hierarchy applied throughout: T1 relabelled Proposition (partial order properties are infrastructure), T2 relabelled Lemma (the global minimum result is a stepping stone for CC-1 and T3). T3 retains Theorem (monotonicity is the primary result of ZP-A). (2) Remark R2 added after D3 connecting the term "state sequence" to the standard order-theory term "ascending chain". (3) CC-1 corollary reworded to make explicit that T2 gives &#8869; &#8804; S&#8320; for any initialisation; CC-1 strengthens this to equality.</i>'),
          body('<i>Version 1.4 change: OQ-A1 section heading and box label corrected from "Open Question" to "CLOSED". The resolution was already recorded in the status line (closed by ZP-E T5 via AX-B1) but the section header was misleading. Status line expanded to answer both sub-questions explicitly.</i>'),
          body('<i>Version 1.3 changes: (1) Definition D2: the equivalence statement now makes explicit that &#945; depends on x — "for each x &#8712; L, f(x) = x &#8744; &#945; for some &#945; &#8712; L". (2) Theorem T3 proof: replaced the single spelled-out "iff" with &#10234; for consistency. (3) CC-1: removed circular conditional framing; reframed as a direct modelling commitment; corrected the consequence chain to S&#8320; = &#8869; &#8804; S&#8321; &#8804; &#8230;; replaced informal "constituent" with direct T2 reference.</i>'),
          body('<i>Version 1.2 changes: (1) Definition D1: the notation :&#10234; (non-standard) replaced by the standard definitional framing "define the relation &#8804; by". (2) Definition D2: the equivalence between x &#8804; f(x) and f(x) = x &#8744; &#945; is now accompanied by an explicit two-line proof of both directions.</i>'),
          body('<i>Version 1.1 change: Theorem T4 reclassified as Conditional Claim CC-1. The v1.0 label "Theorem" was imprecise: the result holds only given the assumption that the state sequence is initialised at the minimum of L. This assumption is not derived from A1&#8211;A4 — it is a modelling commitment.</i>'),
          sp()]

    E.append(label_box('Metatheoretic Declaration — ZF + AFA', [
        'This document is stated over ZF + AFA (Zermelo&#8211;Fraenkel set theory with Aczel&#8217;s Anti-Foundation Axiom). AFA replaces the classical Axiom of Foundation and permits self-containing sets &#8212; in particular, sets satisfying x = {x}.',
        'Scope: This declaration affects only CC-2 (Section V), which asserts ⊥ = {⊥}. All algebraic results in Sections I&#8211;IV are independent of AFA and hold in standard ZF.',
        'Standard concrete models (power sets ordered by inclusion, real intervals ordered by max, etc.) satisfy A1&#8211;A4 but do not satisfy ⊥ = {⊥}. This is expected &#8212; they are models of the algebraic structure, not instantiations of the ZF + AFA metatheory. The self-containment of ⊥ is a set-theoretic claim about what ⊥ is, not an algebraic one.',
        'The Axiom of Choice is not assumed. AFA is forced rather than chosen &#8212; see Section V and ZP-E Remark R-AFA for the argument.',
    ]))
    E.append(sp(8))

    E.append(Paragraph('I. Primitives and Axioms', S['h1']))
    E.append(Paragraph('1.1  Signature', S['h2']))
    E.append(body('The algebraic signature of the Zero Paradox state space is a triple: <b>(L, &#8744;, &#8869;)</b>'))
    E.append(body('L is a non-empty set (the carrier set of states). &#8744;&nbsp;:&nbsp;L&nbsp;&#215;&nbsp;L&nbsp;&#8594;&nbsp;L is a binary operation called <i>join</i>. &#8869; &#8712; L is a distinguished constant called the <i>bottom element</i>.'))
    E.append(sp(4))
    E.append(label_box('Axiom Block A — Join-Semilattice with Bottom', [
        'A1 — Associativity:   (x &#8744; y) &#8744; z = x &#8744; (y &#8744; z)   for all x, y, z &#8712; L',
        'A2 — Commutativity:  x &#8744; y = y &#8744; x   for all x, y &#8712; L',
        'A3 — Idempotency:    x &#8744; x = x   for all x &#8712; L',
        'A4 — Identity (Additive):   &#8869; &#8744; x = x   for all x &#8712; L',
    ]))
    E.append(sp(4))
    E.append(body('<b>A4 is the load-bearing axiom.</b> It makes &#8869; the additive identity of the algebra: the element that contributes nothing to a join and is therefore present in every state as the neutral constituent.'))

    E.append(Paragraph('II. The Induced Partial Order', S['h1']))
    E.append(Paragraph('2.1  Definition of &#8804;', S['h2']))
    E.append(label_box('Definition D1 — Lattice Order', [
        'For x, y &#8712; L, define the relation &#8804; by:',
        'x &#8804; y   &#10234;   x &#8744; y = y',
    ]))
    E.append(sp(4))
    E.append(label_box('Proposition T1 — &#8804; is a Partial Order', [
        'Reflexivity: x &#8804; x — by A3, x &#8744; x = x. <font name="DV">&#10003;</font>',
        'Antisymmetry: if x &#8804; y and y &#8804; x, then x &#8744; y = y and y &#8744; x = x. By A2, y = x &#8744; y = y &#8744; x = x. <font name="DV">&#10003;</font>',
        'Transitivity: if x &#8804; y and y &#8804; z, then x &#8744; z = x &#8744; (y &#8744; z) = (x &#8744; y) &#8744; z = y &#8744; z = z, so x &#8804; z. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(Paragraph('2.2  &#8869; is the Least Element', S['h2']))
    E.append(label_box('Lemma T2 — &#8869; is a Global Minimum under &#8804;', [
        'For all x &#8712; L:   &#8869; &#8804; x',
        'Proof: By A4, &#8869; &#8744; x = x. By D1, this is the definition of &#8869; &#8804; x. <font name="DV">&#10003;</font>',
    ]))
    E.append(sp(4))
    E.append(body('T2 is the algebraic statement of the foundational claim: &#8869; is not a void that states depart from — it is the minimum element that every state sits above. Since &#8869; &#8804; x for all x, and join accumulates from the bottom, &#8869; is algebraically present in every element of L.'))

    E.append(Paragraph('III. The Additive Ontology', S['h1']))
    E.append(Paragraph('3.1  No Subtraction Operator', S['h2']))
    E.append(label_box('Remark R1 — Join-Semilattice vs. Lattice', [
        'A full lattice (L, &#8744;, &#8743;, &#8869;, &#8868;) includes a meet operator &#8743; and a top element &#8868;. The Zero Paradox restricts to the join-semilattice with bottom. The meet operator is excluded because it would allow state reduction — the removal of informational content from a state. The additive ontology requires that no operation decreases informational content.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('3.2  Join is the Only State Transition', S['h2']))
    E.append(label_box('Definition D2 — State Transition', [
        'A state transition is any function f: L &#8594; L such that x &#8804; f(x) for all x &#8712; L.',
        'Equivalently, for each x &#8712; L, f(x) = x &#8744; &#945; for some &#945; &#8712; L.',
        'Proof of equivalence:',
        '(&#8658;) If x &#8804; f(x), then x &#8744; f(x) = f(x) by D1. Take &#945; = f(x): then f(x) = x &#8744; &#945;. <font name="DV">&#10003;</font>',
        '(&#8656;) If f(x) = x &#8744; &#945; for some &#945; &#8712; L, then x &#8744; f(x) = x &#8744; (x &#8744; &#945;) = (x &#8744; x) &#8744; &#945; = x &#8744; &#945; = f(x) by A1, A3. By D1, x &#8804; f(x). <font name="DV">&#10003;</font>',
    ]))

    E.append(Paragraph('IV. Monotonicity of State Sequences', S['h1']))
    E.append(Paragraph('4.1  State Sequences', S['h2']))
    E.append(label_box('Definition D3 — State Sequence', [
        'A state sequence is a function S: &#8469; &#8594; L, written (S<sub>0</sub>, S<sub>1</sub>, S<sub>2</sub>, &#8230;), such that:',
        'S<sub>n+1</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub>   for some &#945;<sub>n</sub> &#8712; L, for all n &#8712; &#8469;',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R2 — Terminology: State Sequence and Ascending Chain', [
        'In the order-theory literature, a sequence (S<sub>n</sub>) satisfying S<sub>n</sub> &#8804; S<sub>n+1</sub> for all n is called an <i>ascending chain</i>. The term "state sequence" is used here in place of "ascending chain" to align with the state-transition framing of ZP-D and ZP-E, where the same structure is introduced as sequences of system states. The two terms denote the same mathematical object. Readers familiar with order theory should read "state sequence" as "ascending chain". For concrete illustrations, see the ZP-A Illustrated Companion.',
    ]))
    E.append(sp(4))
    E.append(label_box('Theorem T3 — State Sequences are Monotone', [
        'For any state sequence (S<sub>n</sub>) satisfying D3:   S<sub>n</sub> &#8804; S<sub>n+1</sub>   for all n &#8712; &#8469;',
        'Proof: By D3, S<sub>n+1</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub>. By D1, S<sub>n</sub> &#8804; S<sub>n</sub> &#8744; &#945;<sub>n</sub> &#10234; S<sub>n</sub> &#8744; (S<sub>n</sub> &#8744; &#945;<sub>n</sub>) = S<sub>n</sub> &#8744; &#945;<sub>n</sub>. By A1, (S<sub>n</sub> &#8744; S<sub>n</sub>) &#8744; &#945;<sub>n</sub> = S<sub>n</sub> &#8744; &#945;<sub>n</sub>. By A3, S<sub>n</sub> &#8744; S<sub>n</sub> = S<sub>n</sub>. Therefore S<sub>n</sub> &#8744; &#945;<sub>n</sub> = S<sub>n+1</sub>. <font name="DV">&#10003;</font>',
        'Monotonicity is a theorem, not a postulate. It is derived from A1&#8211;A3 via D3.',
    ]))
    E.append(sp(4))
    E.append(Paragraph('4.2  The Initial State', S['h2']))
    E.append(body('Every state sequence begins somewhere. T2 establishes ⊥ ≤ S₀ for any initialisation &#8212; the bottom element is always below the starting point, whatever that starting point is. But T2 does not fix where S₀ sits; a sequence could legitimately begin above ⊥. CC-1 closes this gap: we commit to initialising at the minimum. This is a modelling choice at ZP-A scope. In the AFAStructure lattices of ZP-J, T-EXEC derives it as a structural consequence rather than an assumption.'))
    E.append(label_box('CC-1 — S₀ = ⊥  |  Derived in AFAStructure lattices (ZP-J T-EXEC); conditional at ZP-A scope', [
        'We commit to initialising every state sequence at the minimum of L: S<sub>0</sub> = &#8869;. This is not derived from A1&#8211;A4 — it is a modelling choice.',
        'Under CC-1 and T3:   S<sub>0</sub> = &#8869; &#8804; S<sub>1</sub> &#8804; S<sub>2</sub> &#8804; &#8230;',
        'Note: By T2, &#8869; &#8804; S<sub>0</sub> for any initialisation — this holds unconditionally from A4. CC-1 strengthens this to equality: S<sub>0</sub> = &#8869;. The commitment is not needed to establish &#8869; &#8804; S<sub>0</sub>; it is needed to fix the starting point precisely.',
        'Status: DERIVED (given AFAStructure grounding) — ZP-J T-EXEC establishes IsQuineAtom(&#8869;) as the unique structural identity; S<sub>0</sub> = &#8869; follows as a structural consequence in any AFAStructure lattice. Modelling commitment at the ZP-A level (no AFAStructure assumption is made within this document).',
    ]))

    E.append(sp(4))

    E.append(Paragraph('V. The Self-Containment of &#8869;', S['h1']))
    E.append(Paragraph('5.1  Foundational Characterisation', S['h2']))
    E.append(body('The axioms A1&#8211;A4 establish &#8869; as the additive identity and algebraic minimum of L. The following conditional claim characterises its set-theoretic nature. R3 provides a structural route to DA-1 in ZP-E: CC-2 establishes that &#8869; has no external interpreter position, which — conditional on D7&#8217;s exhaustive static/executing dichotomy (ZP-E) as background — eliminates the static-description state for &#8869;. See R3 for the full dependency note.'))
    E.append(body('<i>Foundation note: The framework is stated over ZF + AFA (Zermelo&#8211;Fraenkel set theory with Aczel&#8217;s Anti-Foundation Axiom). The classical Axiom of Foundation is replaced by AFA, which permits self-containing sets. This replacement is not an arbitrary modelling choice: ZF + Foundation is incompatible with CC-2 (a well-founded &#8869; would admit an external interpreter, contradicting R3) and with ZP-C L-INF (bounded &#8712;-rank contradicts unbounded surprisal of &#8869;). See ZP-E Remark R-AFA for the full cross-framework argument. The Axiom of Choice is not assumed.</i>'))
    E.append(sp(4))
    E.append(label_box('Conditional Claim CC-2 — Self-Containment of &#8869;', [
        'The null state &#8869; is its own extension: the collection of all objects bearing the structural property of &#8869; is &#8869; itself.',
        'Formally: &#8869; = {&#8869;}',
        'Under ZF + AFA, &#8869; is a Quine atom — a set satisfying x = {x}. By set extensionality, any infinite collection of objects all indistinguishable under the structural property of &#8869; collapses to &#8869; itself. There is no multiplicity, only &#8869;.',
        'This is a modeling commitment. It is not derived from A1&#8211;A4. It requires replacing the classical Axiom of Foundation with AFA in the metatheory.',
        'Status: CONDITIONAL CLAIM — modeling commitment over ZF + AFA; not derived from A1&#8211;A4.',
        'Cross-framework note: The replacement of Foundation by AFA is not an arbitrary choice — ZF + Foundation is ruled out by R3 (a well-founded &#8869; would admit an external interpreter, contradicting CC-2) and by ZP-C L-INF (bounded &#8712;-rank contradicts unbounded surprisal of &#8869;). AFA is the forced metatheoretic replacement; the specific form &#8869; = {&#8869;} is the minimal Quine atom consistent with A4. See ZP-E Remark R-AFA for the full cross-framework argument.',
        'Lean 4 scope: ZPA.lean verifies the algebraic structure A1&#8211;A4 and all derived results (T1&#8211;T3, CC-1). CC-2 is a metatheoretic commitment at the set-theoretic level. Lean&#8217;s bot field is a term of an abstract typeclass — a structural proxy for the algebraic role of &#8869;. Lean&#8217;s type theory (CIC) is well-founded by construction; Quine atoms cannot be realized as Lean terms. The set-theoretic content of CC-2 is stated as a prose-level commitment in ZF + AFA and is outside the scope of the Lean verification.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R3 — CC-2 Eliminates the Static-Description State for &#8869;', [
        'A self-containing object has no external interpreter by structure: &#8869; = {&#8869;} is its own interpretation. A description requires a describer distinct from the thing described; CC-2 admits no such distinction for &#8869;. Under the Turing model framework (D7, ZP-E), which partitions machine configurations into static-description states and executing states, the absence of any external interpreter position means &#8869; cannot occupy D7&#8217;s static-description category.',
        'Dependency note: The inference from "no external interpreter" to "necessarily executing" uses D7&#8217;s exhaustiveness in the final step — that static-description and executing are the only two categories. D7 (ZP-E) supplies this exhaustiveness as the shared background framework. R3 provides the structural argument for why &#8869; engages D7&#8217;s transition; it does not independently derive DA-1 without D7. All three DA-1 paths in ZP-E share D7 as background. Their independence is among their arguments — CC-2/R3 (structural), L-INF (informational), K-incompressibility (AIT) — not from D7 itself.',
    ]))
    E.append(sp())

    E.append(Paragraph('VI. OQ-A1 — Sufficiency of Monotonicity', S['h1']))
    E.append(label_box('OQ-A1 — Sufficiency of Monotonicity  [CLOSED — ZP-E T5]', [
        'Is the monotonicity constraint (T3) sufficient to characterise all valid state sequences, or are additional axioms required?',
        'OQ-A1a: Is there algebraic reason to restrict &#945;<sub>n</sub> to join-irreducible elements (not expressible as joins of strictly smaller elements)?',
        'OQ-A1b: Does the open-ended semilattice (without top element &#8868;) permit unbounded ascending chains?',
        'Status: CLOSED — Both sub-questions resolved by ZP-E Theorem T5 (Iterative Forcing Theorem) via AX-B1 from ZP-B. OQ-A1a: &#945;<sub>n</sub> = &#949;(S<sub>n</sub>), the minimum viable deviation. OQ-A1b: AX-B1\'s binary constraint bounds ascending chains.',
    ]))

    E.append(Paragraph('VII. Boundary Conditions', S['h1']))
    E.append(data_table(
        ['Export', 'Status / Receiving Document'],
        [['(L, &#8744;, &#8869;) as join-semilattice', 'Derived (A1&#8211;A4) — ZP-D: algebraic structure of state space'],
         ['&#8804; partial order (D1, T1)', 'Derived — ZP-D: ordering on states'],
         ['Monotonicity of state sequences (T3)', 'Derived from A1&#8211;A3 — ZP-D: state layer ordering'],
         ['&#8869; as global minimum (T2, CC-1)', 'Derived / Conditional — ZP-E: ontological grounding claim. CC-1 now derived in AFAStructure lattices via ZP-J T-EXEC.'],
         ['&#8869; = {&#8869;} self-containment (CC-2, R3)', 'Conditional / Remark — ZP-E: structural route to eliminating static-description state for &#8869;, given D7 exhaustiveness as background'],
         ['No subtraction / additive ontology (R1)', 'Structural — ZP-C: no operation may reduce informational content'],
         ['OQ-A1 — increment selection', 'Open within ZP-A; closed by ZP-E T5']],
        [2.5*inch, 4.0*inch]
    ))

    E.append(Paragraph('VIII. Validation Status', S['h1']))
    E.append(data_table(
        ['Component', 'Status / Notes'],
        [['A1&#8211;A4 join-semilattice axioms', 'Valid — Axioms; self-contained'],
         ['&#8804; partial order (D1, T1)', 'Valid — Derived from A1&#8211;A3'],
         ['&#8869; as least element (T2)', 'Valid — Derived from A4 and D1'],
         ['Additive ontology / no subtraction (R1)', 'Valid — Structural; signature restriction'],
         ['State transition as join (D2)', 'Valid — Defined; consistent with signature'],
         ['Monotonicity of state sequences (T3)', 'Valid — Derived from A1&#8211;A3 and D3'],
         ['CC-1: S<sub>0</sub> = &#8869;', 'DERIVED (given AFAStructure grounding, ZP-J T-EXEC) — structural consequence in any AFAStructure lattice. Modelling commitment at ZP-A level without AFAStructure assumption.'],
         ['CC-2: &#8869; = {&#8869;}', 'Conditional Claim — modeling commitment over ZF + AFA; not derived from A1&#8211;A4'],
         ['ZF + AFA foundation (no AC)', 'Meta-theoretic — framework-wide; required for CC-2'],
         ['OQ-A1: Sufficiency of monotonicity', 'Open within ZP-A; closed by ZP-E T5']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
