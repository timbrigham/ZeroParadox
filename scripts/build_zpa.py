"""
Build ZP-A: Lattice Algebra (v1.29)
v1.29: DECISION BATCH REMEDIATION AFTER GATE ROUND 3 (Tim rulings, 2026-09-15): each face of epsilon-0 is credited with its own direction. The OQ-A1a second paragraph said nothing below epsilon-0 fires 'because epsilon-0 is at once the supremum of the tower's stages and the least fixed point'; the proof of that direction uses the supremum face only (fundamentalSeq_cofinal), and the least-fixed-point face gives the other direction, that every fixed point of alpha -> omega^alpha fires (hfp_from_epsilon_zero). The paragraph and the minimal-element note now state both directions, each with its face, and say the open question is deriving h-eps0 from the 2-adic structure. The box title and both table cells name the monotone map sending the tower's stages to c0 and epsilon-0 sent to c1 beside h-eps0. OQ-A1a: 'not the states reached' is 'not the set of reachable states'; Birkhoff cited as Birkhoff 1937 via Chakir-Pouzet, arXiv:0812.2300, Thm 2.1(c).
v1.28: ADVERSARY GATE ROUND 3 (bedrock, D1): the OQ-A1a second paragraph said 'given h-eps0, nothing below epsilon-0 fires', dropping two of snap_unconditional's three hypotheses (monotonicity, and the tower stages sent to c0); a monotone map with h-eps0 can fire at 1. It now names the monotone map sending the tower's stages to c0, as the minimal-element note already did.
v1.27: DECISION BATCH REMEDIATION AFTER GATE ROUND 2, SECOND PASS (Tim ruling, 2026-09-15): the placement of the step in the ordinal tower was pointed at OQ-E2, the wrong object (ZP-E's OQ-E2 is the cardinality-semilattice correspondence). The box title, both tables, the OQ-A1a second paragraph and the minimal-element note now say the placement is the alignment hypothesis h-eps0 (ZeroParadox/Ordinal/Incompleteness.lean), whose derivation is open as the Classical.choice inversion conjecture.
v1.26: DECISION BATCH REMEDIATION AFTER GATE ROUND 2 (Tim rulings, 2026-09-15): OQ-A1a restated in two parts: no algebraic reason to restrict increments to join-irreducibles (vacuous on a chain, not on a branching carrier, and in a well-founded carrier every increment is a finite join of join-irreducibles, exists_supIrred_decomposition), and separately the placement in the ordinal tower is conditional on OQ-E2 (given h-eps0 nothing below epsilon-0 fires, both faces, snap_unconditional and epsilon0_min_eq_max). The 'answered by crossing charts' label is removed from the box title and both tables. The minimal-element note states both faces of epsilon-0 and that the placement is the alignment open as OQ-E2. The finite-step sentence is scoped short of a top. The Reading gets an antecedent. Join written as vee. Page 1 scopes 'every claim' to claims proved here.
v1.25: DECISION BATCH REMEDIATION ROUND 2 (Tim rulings, 2026-09-15): the OQ-A1a paragraph cites snap_unconditional (whose hypothesis is hε₀), not snap_exactly_at_epsilon_zero; the minimal-element note's 'That existence rests on the same binary existence commitment (AX-B1), not on a further result' is now charted: AX-B1 in the lattice chart, and in the ordinal chart epsilon-0 is the least fixed point of alpha -> omega^alpha (epsilon0_min_eq_max) where, given that the step occurs, a monotone map places the lattice step (snap_unconditional).
v1.24: DECISION BATCH REMEDIATION (Tim, 2026-09-15): OQ-A1's box status is Tim's confirmed text: OQ-A1b CLOSED by A1-A4 (yes; the natural numbers under max are a model with a first distinct state n + 1 above every n, so first steps do not give the ascending chain condition), and OQ-A1a answered by crossing charts (snap_exactly_at_epsilon_zero; isLeastFixedPointFrom_nfp; succession_succ; on an arbitrary lattice nothing restricts which increment is taken). The T5 iteration clause is replaced by 'No step is guaranteed' (T3, R1, t_snap_irreversible, tsnap_holds_but_nothing_moves), with epsilon-0 read as the least-fixed-point/supremum pair (epsilon0_min_eq_max). Removed: the closure 'a consequence of ZP's binary existence commitment and the occurrence commitment', 'its discreteness gives a minimum step above each state', the MachinePhase bound parenthetical, and the 'closed within ZP given AX-B1 and the occurrence commitment' title and table cells.
v1.23: OCCURRENCE COMMITMENT DEFINED, T5 RESTATED, T-SNAP RESIDUE (Tim decision batch, 2026-09-14): ZP-E now restates T5 (Iterative Forcing Theorem) split the way AX-1 was, selection a Conditional Claim given AX-B1's discreteness at every state and iteration the occurrence commitment at each step, so OQ-A1 is 'closed within ZP given AX-B1 and the occurrence commitment' in its box and both table rows, where it read 'closed by ZP-E T5'. OQ-A1b said 'Within ZP, AX-B1's binary constraint bounds ascending chains via T5', and the minimal-element note said the closure 'establishes that ascending chains are bounded within ZP'. MEASURED FALSE (Lean probe, exit 0): on the natural numbers every n has a first step above it (HasFirstStep n, via Order.covBy_add_one) and the identity chain is strictly increasing with no upper bound; on (N, max, 0) HasNoTop and IsStrictStateSequence id both hold; and Bool has a first step above its bottom with every chain bounded. Discreteness bounds the step from below, not the chain's length. OQ-A1b is now answered yes, with what AX-B1 does give (a minimum step above each state) and occurrence named as what makes a chain take every step; the note no longer says the chains are bounded.
v1.22: CC-1 STATUS SYNC (Tim, 2026-09-13: everything in one arc). "CC-1 derived / closed / no longer a freestanding commitment" collapsed two readings: cc1_derived proves the CONDITIONAL (a state sequence starting at a Quine atom starts at bottom), and with t_exec_iff the converse holds, so the starting-point choice is RESTATED through the Quine-atom role, not forced; every ZP-A lattice carries AFAStructure trivially. Every site now keeps both halves, matching ZP-J v2.7. CC-1's box title, status line, § intro sentence and both table cells now read Conditional Claim at ZP-A scope, restated in ZP-J. ROUND 1 (editorial + claim-review + adversary FAIL-BEDROCK; prior-art PASS): the sync first gave the wrong REASON for "not forced" ("every ZP-A lattice carries AFAStructure trivially, so ..."), which does not follow; the reason is that a valid state sequence can start above bottom (T2 fixes only bottom <= S0; an example on OntologicalStates in OntBridge.lean). Also the CC-2 box's Lean-scope item no longer calls the AFAStructure results 'conditional on AFA as ambient': the typeclass is a hypothesis every ZP-A lattice supplies trivially. GATE ROUND 2 (ordinary, carried): the 'not forced' reason needs its scope - on a ONE-point lattice every sequence starts at bottom, so the countermodel is stated for a lattice with a second point, and the OntBridge.lean example now also shows the start is not a Quine atom.
v1.21: OQ-A1b minimal-element note corrected (bedrock, cross-document attribution) — struck "that existence is a metric result, established by ZP-B's 2-adic structure". ZP-B proves no such result and cannot: the 2-adic norm values accumulate at 0 (‖2ⁿ‖₂ = 2⁻ⁿ), so ℚ₂ supplies no closest non-zero element, and ZP-B's own eps0 = 2ᵏ is parameterized by a chosen maximum accessible valuation (value contingent by its own definition). The note re-attributed to ZP-B's METRIC what the preceding paragraph already correctly attributes to ZP-B's AXIOM — an axiom-mistaken-for-result, and the two paragraphs contradicted each other. Minimality now rests on AX-B1 (consistent with CLAIMS.md, which classifies it as the framework's one substantive modeling commitment); what ZP-B proves at 0 is stated instead (clopen gap T3, irreversible return C3); and the dense counterexample now points at ZP-F, where it is proved for every ordered field and stated as the direct negation of AX-B1 (axb1_fails_in_ordered_field). No algebraic content changed.
v1.20: R-AFA false premise corrected (bedrock, same class as ZP-E v3.24) — struck BOTH legs of the Foundation-vs-AFA squeeze: the "well-founded ⊥ would admit an external interpreter" leg (well-founded ⇏ finitely interpretable; ω) and the "bounded ∈-rank contradicts unbounded surprisal" leg (∈-rank and surprisal are orthogonal; ∅ has ∈-rank 0 yet v₂(0)=∞, so both co-inhabit ⊥). Foundation-incompatibility now rests on the self-membership of ⊥={⊥} (Regularity, no_quine_atom); R3 and L-INF demoted to corroboration; forcing stated machine-checked (QuineHost); falsifier narrowed to the requirements-choice; now consistent with the corrected ZP-E R-AFA it references.
v1.19: rendered Lean citations synced to post-reorg files/namespaces (SSOT-driven); C8 dual-date templating (hardcoded month removed).
v1.18: rendered Lean-file citation synced to post-reorg basename (ZPJ_ScaleBridge -> ScaleBridge).
v1.17: C8 dual-date — subtitle templated via version_line (First released / This version); hardcoded month removed.
v1.16: FMC uniformity (sweep Step 4b) — residual AFA-necessity assertions softened to "argued": metatheoretic declaration, R-AFA cross-framework note, CC-2 validation-table cell.
v1.15: FMC precision (sweep Step 4, against fmc.md) — CC-2 box: "structurally required" / "ruled out" / "incompatible" softened to "argued"; named falsifier added; status line marked argued, not a derivation.
v1.14: CC-2 label updated — "Conditional Claim" → "Forced Metatheoretic Commitment".
Metatheoretic choice of ZF+AFA over Foundation is not free: ruled out by R3 and ZP-C L-INF.
Lean 4 scope note extended — ZPJ_ScaleBridge formally verifies the fixed-point content
(selfMem_eq_singleton_free, z2_selfMem_singleton) in ZFC; set-theoretic interpretation
remains outside Lean scope. Both validation tables updated. No algebraic content changed.
v1.13: OQ-A1b note added distinguishing bounded chains from existence of minimal element
above ⊥. Bounded chains (closed by ZP-E T5 via AX-B1) do not guarantee ε₀ exists as a
minimal non-null element — that is a metric result established by ZP-B, not A1-A4. No
algebraic content changed.
v1.12: OQ-A1b dual-status clarification. The closure note now distinguishes between the
ZP-specific result (bounded by AX-B1 via T5) and the general semilattice case (unbounded
chains are permitted in a bare join-semilattice without AX-B1). Section header updated to
"CLOSED within ZP". No algebraic content changed.
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

VERSION = '1.29'
FIRST_RELEASED = 'April 2026'

def build():
    out_path = os.path.join(PROJECT_ROOT, 'ZP-A_Lattice_Algebra.pdf')
    doc = make_doc(out_path, 'ZP-A: Lattice Algebra', 'ZP-A', 'Version ' + VERSION)
    E = []

    E += [Paragraph('THE ZERO PARADOX', S['title']),
          Paragraph('ZP-A: Lattice Algebra', S['subtitle']),
          Paragraph(version_line(FIRST_RELEASED, VERSION), S['subtitle']),
          sp(10),
          body('This document is self-contained within abstract algebra. No topology, probability, or Hilbert space is imported. Every claim proved here is provable using only the tools of semilattice theory; the status of OQ-A1 points to other documents. Cross-framework connections are deferred to ZP-E.'),
          body('<i>Illustrated Companion: A paired ZP-A Illustrated Companion document provides concrete examples and visual intuitions for the results in this document. Examples are kept separate from the formal layers to distinguish illustrative material from proofs. The companion is a reading aid; no proof-critical judgements should be drawn from examples alone.</i>'),
          sp()]

    E.append(label_box('Metatheoretic Declaration — ZF + AFA', [
        'This document is stated over ZF + AFA (Zermelo&#8211;Fraenkel set theory with Aczel&#8217;s Anti-Foundation Axiom). AFA replaces the classical Axiom of Foundation and permits self-containing sets &#8212; in particular, sets satisfying x = {x}.',
        'Scope: This declaration affects only CC-2 (Section V), which asserts ⊥ = {⊥}. All algebraic results in Sections I&#8211;IV are independent of AFA and hold in standard ZF.',
        'Standard concrete models (power sets ordered by inclusion, real intervals ordered by max, etc.) satisfy A1&#8211;A4 but do not satisfy ⊥ = {⊥}. This is expected &#8212; they are models of the algebraic structure, not instantiations of the ZF + AFA metatheory. The self-containment of ⊥ is a set-theoretic claim about what ⊥ is, not an algebraic one.',
        'The Axiom of Choice is not assumed. AFA is argued to be forced rather than chosen &#8212; see Section V and ZP-E Remark R-AFA for the argument.',
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
    E.append(body('Every state sequence begins somewhere. T2 establishes ⊥ ≤ S₀ for any initialisation &#8212; the bottom element is always below the starting point, whatever that starting point is. But T2 does not fix where S₀ sits; a sequence could legitimately begin above ⊥. CC-1 closes this gap: we commit to initialising at the minimum. This is a modelling choice at ZP-A scope. ZP-J restates it rather than removing it: in any AFAStructure lattice a sequence starts at a Quine atom exactly when it starts at &#8869; (cc1_derived and t_exec_iff), so the choice of starting point is expressed through the Quine-atom role. It is still not forced: on any lattice with a point above &#8869; (as AX-B1 supplies) a valid sequence can begin there, as the OntologicalStates example in ZeroParadox/Settheory/OntBridge.lean shows; on a one-point lattice every sequence starts at &#8869;.'))
    E.append(label_box('Conditional Claim CC-1 — S₀ = ⊥  |  restated as an equivalence in ZP-J, not forced', [
        'We commit to initialising every state sequence at the minimum of L: S<sub>0</sub> = &#8869;. This is not derived from A1&#8211;A4 — it is a modelling choice.',
        'Under CC-1 and T3:   S<sub>0</sub> = &#8869; &#8804; S<sub>1</sub> &#8804; S<sub>2</sub> &#8804; &#8230;',
        'Note: By T2, &#8869; &#8804; S<sub>0</sub> for any initialisation — this holds unconditionally from A4. CC-1 strengthens this to equality: S<sub>0</sub> = &#8869;. The commitment is not needed to establish &#8869; &#8804; S<sub>0</sub>; it is needed to fix the starting point precisely.',
        'Status: CONDITIONAL CLAIM — a modelling commitment at ZP-A scope. ZP-J restates it: given AFAStructure, cc1_derived proves that a state sequence starting at a Quine atom starts at &#8869;, and t_exec_iff gives the converse, so the two starting conditions are one. On a lattice with a point above &#8869; a state sequence can begin there (T2 fixes only &#8869; &#8804; S<sub>0</sub>; witness in ZeroParadox/Settheory/OntBridge.lean), so the equivalence does not remove the choice of starting point; it expresses it through the Quine-atom role.',
    ]))

    E.append(sp(4))

    E.append(Paragraph('V. The Self-Containment of &#8869;', S['h1']))
    E.append(Paragraph('5.1  Foundational Characterisation', S['h2']))
    E.append(body('The axioms A1&#8211;A4 establish &#8869; as the additive identity and algebraic minimum of L. The following forced metatheoretic commitment characterises its set-theoretic nature. R3 provides a structural route to DA-1 in ZP-E: CC-2 establishes that &#8869; has no external interpreter position, which — conditional on D7&#8217;s exhaustive static/executing dichotomy (ZP-E) as background — eliminates the static-description state for &#8869;. See R3 for the full dependency note.'))
    E.append(body('<i>Foundation note: The framework is stated over ZF + AFA (Zermelo&#8211;Fraenkel set theory with Aczel&#8217;s Anti-Foundation Axiom). The classical Axiom of Foundation is replaced by AFA, which permits self-containing sets. This replacement is not an arbitrary modelling choice: &#8869; = {&#8869;} is a member of itself (&#8869; &#8712; &#8869;), which the Axiom of Foundation (Regularity) forbids &#8212; under a well-founded membership relation no set is self-membered (no_quine_atom, ZeroParadox/Settheory/Wall.lean) &#8212; so a Foundation universe cannot host &#8869;, and AFA is the anti-foundation setting that permits it. R3 and ZP-C L-INF corroborate the non-well-founded character of &#8869; rather than independently prove the exclusion. See ZP-E Remark R-AFA for the full cross-framework argument. The Axiom of Choice is not assumed.</i>'))
    E.append(sp(4))
    E.append(label_box('Forced Metatheoretic Commitment CC-2 — Self-Containment of &#8869;', [
        'The null state &#8869; is its own extension: the collection of all objects bearing the structural property of &#8869; is &#8869; itself.',
        'Formally: &#8869; = {&#8869;}',
        'Under ZF + AFA, &#8869; is a Quine atom — a set satisfying x = {x}. By set extensionality, any infinite collection of objects all indistinguishable under the structural property of &#8869; collapses to &#8869; itself. There is no multiplicity, only &#8869;.',
        'This is a Forced Metatheoretic Commitment, not a freely chosen modeling decision. Foundation cannot host &#8869; = {&#8869;}: the bottom is a member of itself, and Regularity forbids self-membership (no_quine_atom). The Foundation-freeness of any host of &#8869; is forced and machine-checked (QuineHost; see ZP-E Remark R-AFA); what remains a commitment rather than a theorem is only that a Quine atom and its uniqueness are the right requirements to demand — this is not derived from A1&#8211;A4 at the algebraic level. The named falsifier is correspondingly narrow: a differently-motivated requirement set that hosts &#8869; without demanding a unique Quine atom would reopen that choice; it would not touch the forcing, which is settled.',
        'Status: FORCED METATHEORETIC COMMITMENT — Foundation-freeness of any host of &#8869; is forced and machine-checked (QuineHost); only the requirements-choice (a unique Quine atom) remains a commitment, not a derivation. Algebraic fixed-point content formally verified in ZFC by ZP-J (ScaleBridge); the literal set-membership &#8869; &#8712; &#8869; is outside Lean scope (metatheoretic).',
        'Cross-framework note: The replacement of Foundation by AFA is not an arbitrary choice — &#8869; = {&#8869;} is a member of itself (&#8869; &#8712; &#8869;), which Regularity forbids (no_quine_atom), so ZF + Foundation cannot host it. Foundation and AFA are dual framings of the same object: Foundation excludes the Quine atom; AFA uniquely permits it. AFA is the forced metatheoretic replacement; the specific form &#8869; = {&#8869;} is the minimal Quine atom consistent with A4. R3 and ZP-C L-INF corroborate &#8869;\'s non-well-founded character; they are not independent proofs of the exclusion. See ZP-E Remark R-AFA for the full cross-framework argument.',
        'Lean 4 scope — three distinct layers. (1) Set-theoretic: the claim &#8869; = {&#8869;} as a set cannot be realized in Lean&#8217;s type theory (CIC is well-founded by construction). This remains a prose-level commitment in ZF + AFA. (2) AFAStructure context (the typeclass taken as a hypothesis): ZP-J defines IsQuineAtom as the lattice-theoretic analog — IsQuineAtom q := selfMem q &#8743; &#8704; x, selfMem x &#8594; x = q. Within an AFAStructure instance, t_exec_iff proves IsQuineAtom q &#8596; q = &#8869; (SetTheoryAFA.lean); ZP-K&#8217;s da1_closed_concrete closes this concretely on MachinePhase. These results take the AFAStructure typeclass as a hypothesis, which every ZP-A lattice can supply trivially, so the hypothesis carries no AFA set-theoretic content of its own. (3) ZFC-clean (no AFA import): ScaleBridge.lean proves the fixed-point content in standard ZFC — selfMem_eq_singleton_free and z2_selfMem_singleton establish {x : &#8484;&#8322; | 2x = x} = {0}. This result is loop-free from AFA. The set-theoretic interpretation connecting layer 3 to layer 1 remains outside Lean scope.',
    ]))
    E.append(sp(4))
    E.append(label_box('Remark R3 — CC-2 Eliminates the Static-Description State for &#8869;', [
        'A self-containing object has no external interpreter by structure: &#8869; = {&#8869;} is its own interpretation. A description requires a describer distinct from the thing described; CC-2 admits no such distinction for &#8869;. Under the Turing model framework (D7, ZP-E), which partitions machine configurations into static-description states and executing states, the absence of any external interpreter position means &#8869; cannot occupy D7&#8217;s static-description category.',
        'Dependency note: The inference from "no external interpreter" to "necessarily executing" uses D7&#8217;s exhaustiveness in the final step — that static-description and executing are the only two categories. D7 (ZP-E) supplies this exhaustiveness as the shared background framework. R3 provides the structural argument for why &#8869; engages D7&#8217;s transition; it does not independently derive DA-1 without D7. All three DA-1 paths in ZP-E share D7 as background. Their independence is among their arguments — CC-2/R3 (structural), L-INF (informational), K-incompressibility (AIT) — not from D7 itself.',
    ]))
    E.append(sp())

    E.append(Paragraph('VI. OQ-A1 — Sufficiency of Monotonicity', S['h1']))
    E.append(label_box('OQ-A1 — Sufficiency of Monotonicity  [OQ-A1b CLOSED by A1&#8211;A4; OQ-A1a: no reason to restrict to join-irreducibles (well-founded carriers); placement in the ordinal tower, for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, conditional on the alignment hypothesis h&#949;<sub>0</sub> (&#949;<sub>0</sub> sent to c<sub>1</sub>)]', [
        'Is the monotonicity constraint (T3) sufficient to characterise all valid state sequences, or are additional axioms required?',
        'OQ-A1a: Is there algebraic reason to restrict &#945;<sub>n</sub> to join-irreducible elements (not expressible as joins of strictly smaller elements)?',
        'OQ-A1b: Does the open-ended semilattice (without top element &#8868;) permit unbounded ascending chains?',
        'Status: OQ-A1b CLOSED by A1&#8211;A4: yes. The natural numbers under max are a model, and every n has a first distinct state n + 1 there, so first steps do not give the ascending chain condition. (On the two-state carrier every chain is bounded; that is a fact about that carrier.)',
        'OQ-A1a: no algebraic reason to restrict &#945;<sub>n</sub> to join-irreducible elements. On a chain the restriction is vacuous (every element above &#8869; is join-irreducible); on a branching carrier it is not (the top of the subsets of a two-element set is the join of two smaller states); and in a well-founded carrier every increment is a finite join of join-irreducibles (Birkhoff 1937; see Chakir&#8211;Pouzet, arXiv:0812.2300, Thm 2.1(c); exists_supIrred_decomposition), so restricting changes the number of steps, not the set of reachable states. Beyond well-founded carriers this is not measured.',
        'Separately, where the step is placed in the ordinal tower is conditional on the alignment hypothesis: for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, given h&#949;<sub>0</sub> (&#949;<sub>0</sub> sent to c<sub>1</sub>), nothing below &#949;<sub>0</sub> fires, because &#949;<sub>0</sub> is the supremum of the stages, and every fixed point of &#945; &#8614; &#969;<super>&#945;</super> fires, because &#949;<sub>0</sub> is the least of them (snap_unconditional, hfp_from_epsilon_zero, epsilon0_min_eq_max); deriving h&#949;<sub>0</sub> from the 2-adic structure is open, as the Classical.choice inversion conjecture.',
        'No step is guaranteed. A state sequence moves only upward (T3) and never returns (R1, t_snap_irreversible). Where the next increment is already absorbed (S<sub>n</sub> &#8744; &#945;<sub>n</sub> = S<sub>n</sub>), the state stays the same, which T-SNAP permits (tsnap_holds_but_nothing_moves); different runs need not reach the same height. If from some step x on every new increment is already absorbed, then S<sub>x</sub> is the supremum of the run: the value that run reaches in the limit. Short of a top, reaching it cannot be confirmed at any finite step; a run that reaches a top state (c<sub>1</sub> on the two-state carrier) is known there to stay.',
        'Reading: &#949;<sub>0</sub> is both at once for the ordinal tower: the least fixed point of &#945; &#8614; &#969;<super>&#945;</super> and the supremum of its stages (epsilon0_min_eq_max).',
        'Note on minimal element above &#8869;: Bounded chains do not in themselves guarantee a minimal element above &#8869;. In a dense structure, for any &#949; > 0, &#949;/2 also exists &#8212; chains may be bounded yet have no first step. That is not a hypothetical: it is ZP-F, where the halving argument is proved for every field carrying a compatible linear order (f_snap_impossible, ZeroParadox/Reals/OrderedField.lean), and is stated there as the direct negation of AX-B1 (axb1_fails_in_ordered_field). The closure of OQ-A1b does not bound ascending chains, and a bound would not establish that &#949;&#8320; exists as a specific minimal non-null element either. In the lattice chart that existence rests on the same binary existence commitment (AX-B1); in the ordinal chart &#949;<sub>0</sub> is proved to be both the least fixed point of &#945; &#8614; &#969;<super>&#945;</super> and the supremum of the tower&#8217;s stages (epsilon0_min_eq_max), and a monotone map that sends those stages to c<sub>0</sub> and &#949;<sub>0</sub> to c<sub>1</sub> fires nowhere below &#949;<sub>0</sub>, by the supremum face, and at every fixed point, by the least-fixed-point face (snap_unconditional, hfp_from_epsilon_zero); the placement at &#949;<sub>0</sub> is the alignment hypothesis, whose derivation from the 2-adic structure is open. ZP-B&#8217;s 2-adic structure places 0 at infinite valuation and every non-zero element at finite valuation; what it proves there is that the gap at 0 is clopen (T3) and the return across it irreversible (C3). The non-zero elements still come arbitrarily close to 0 (&#8214;2&#8319;&#8214;&#8322; = 2&#8315;&#8319;), so there is no closest non-zero element to serve as a first step. This is outside the scope of A1&#8211;A4.',
    ]))

    E.append(Paragraph('VII. Boundary Conditions', S['h1']))
    E.append(data_table(
        ['Export', 'Status / Receiving Document'],
        [['(L, &#8744;, &#8869;) as join-semilattice', 'Derived (A1&#8211;A4) — ZP-D: algebraic structure of state space'],
         ['&#8804; partial order (D1, T1)', 'Derived — ZP-D: ordering on states'],
         ['Monotonicity of state sequences (T3)', 'Derived from A1&#8211;A3 — ZP-D: state layer ordering'],
         ['&#8869; as global minimum (T2, CC-1)', 'Derived (T2) / Conditional (CC-1) — ZP-E: ontological grounding claim. CC-1 is restated in ZP-J as an equivalence (cc1_derived, t_exec_iff), not forced.'],
         ['&#8869; = {&#8869;} self-containment (CC-2, R3)', 'Forced Metatheoretic / Remark — ZP-E: structural route to eliminating static-description state for &#8869;, given D7 exhaustiveness as background. Fixed-point content verified in ZFC by ZP-J.'],
         ['No subtraction / additive ontology (R1)', 'Structural — ZP-C: no operation may reduce informational content'],
         ['OQ-A1 — increment selection', 'OQ-A1b CLOSED by A1&#8211;A4; OQ-A1a: no reason to restrict to join-irreducibles (well-founded carriers); placement in the ordinal tower, for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, conditional on the alignment hypothesis h&#949;<sub>0</sub> (&#949;<sub>0</sub> sent to c<sub>1</sub>)']],
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
         ['CC-1: S<sub>0</sub> = &#8869;', 'CONDITIONAL CLAIM — modelling commitment at ZP-A scope. ZP-J restates it as an equivalence (a Quine-atom start is a &#8869; start: cc1_derived, t_exec_iff); the starting-point choice is not forced.'],
         ['CC-2: &#8869; = {&#8869;}', 'Forced Metatheoretic Commitment — AFA over Foundation argued to be structurally required; fixed-point content verified in ZFC by ScaleBridge'],
         ['ZF + AFA foundation (no AC)', 'Meta-theoretic — framework-wide; required for CC-2'],
         ['OQ-A1: Sufficiency of monotonicity', 'OQ-A1b CLOSED by A1&#8211;A4; OQ-A1a: no reason to restrict to join-irreducibles (well-founded carriers); placement in the ordinal tower, for a monotone map sending the tower&#8217;s stages to c<sub>0</sub>, conditional on the alignment hypothesis h&#949;<sub>0</sub> (&#949;<sub>0</sub> sent to c<sub>1</sub>)']],
        [2.5*inch, 4.0*inch]
    ))

    doc.build(E)
    print(f'Built: {out_path}  ({os.path.getsize(out_path) // 1024} KB)')


if __name__ == '__main__':
    build()
