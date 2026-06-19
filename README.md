# The Zero Paradox
**April 2026**

*A Lean 4 proof that the bottom element of a join-semilattice forces a minimal non-bottom state, using only the standard semilattice axioms.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For plain-language introduction, illustrated companions, and reading paths, see [GUIDE](GUIDE.md).

---

## Contents

- [The Central Result](#the-central-result)
- [The Framework](#the-framework)
  - [Formal Verification (Lean 4)](#formal-verification-lean-4)
  - [Formal Framework Documents](#formal-framework-documents)
- [Axiomatic Commitments](#axiomatic-commitments)
- [Question Register](#question-register)
- [Version History](#version-history)
- [License](#license) · [Citation](#citation) · [Contact](#contact)

---

## The Central Result

The forced transition from the bottom element ⊥ to the minimum nonzero state ε₀ (the **Binary Snap**, this project's shorthand) is a **theorem**, not an axiom.

The existence of a minimum nonzero element is not assumed - it follows from the structure of the bottom element itself, using only the standard bottom-element axiom of join-semilattice theory. The derivation is machine-verified in Lean 4 - independent reviewers can check the conclusion mechanically, without relying on the argument's prose presentation.

The identification of ⊥ across the framework's layers - algebraic, topological, information-theoretic, and categorical - is a modeling commitment, detailed in [Axiomatic Commitments](#axiomatic-commitments). The relationship between the framework's ε₀ and the proof-theoretic ordinal of PA (Gentzen 1936) is addressed in the [Question Register](#question-register).

This framework adds no axioms specific to the result. It follows from the standard bottom-element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x) alone. The remaining commitments are either directly verifiable by computation or restatements of structure established in earlier layers; the full labelled account is in [Axiomatic Commitments](#axiomatic-commitments).

More than that, the central theorem is machine-verified to depend on **no axioms at all** - not the Axiom of Choice, not even propositional extensionality. `Classical.choice` enters elsewhere only where the framework builds on Mathlib's classically-built analysis, order, and computability libraries - the layers that realize the snap inside standard analytic structures (p-adic topology, Hilbert space, ordinals, category theory) and the auxiliary constructions on them - not in the core result itself. The axiom profile of the core, with an honest contrast showing exactly where choice does appear, is a checkable artifact: [AxiomProfile.lean](ZeroParadox/AxiomProfile.lean).

**Scope of the claim**

The internal coherence is formally established - the central theorem and the supporting layer theorems are verified in Lean 4 given the explicitly stated commitments. The author believes the formalism faithfully captures the structural notion of zero it sets out to model, but that is a question Lean cannot answer from inside, and is what this repository invites external review on. Lean answers "do these conclusions follow from these commitments." Whether the commitments are the right ones, and whether the formalism tracks the intended structural notion, are open questions for outside readers. The framework has been developed in public from the start for exactly this reason: to invite inquiry throughout the process rather than only at its conclusion.

The forced transition is also irreversible: the p-adic topology layer (ZP-B) establishes, Lean-verified, that there is no continuous path from any nonzero state back to ⊥. This follows from the ultrametric structure of Q₂: its total disconnectedness makes any return path discontinuous. The connection to the lattice layer relies on identifying ⊥ with the 2-adic zero, detailed in [Axiomatic Commitments](#axiomatic-commitments).

<details>
<summary><b>The derivation chain</b> - the step-by-step formal skeleton - click to expand</summary>

**P₀** (incompressibility threshold, ZP-C D1)  
→ **DA-1** (instantiation of a configuration at P₀ constitutes an execution event, ZP-E)  
→ **D7** (machine configuration definition, ZP-C)  
→ **L-RUN** (execution is a nonzero state change, ZP-C)  
→ **TQ-IH** (no program outputs ⊥ without a nonzero intermediate state, ZP-C)  
→ **ZP-A D2** (a nonzero state change from ⊥ is a join - the Binary Snap)  
→ **T-SNAP** (Binary Snap follows from A4, the standard bottom element axiom; AX-1 was redundant)

</details>

---

## The Framework

### Formal Verification (Lean 4)

Machine-checked proofs of the formal documents using Lean 4 + Mathlib. Source lives under `ZeroParadox/` in this repository. The full theorem-by-theorem detail is in each source file. An **axiom-profile artifact**, [AxiomProfile.lean](ZeroParadox/AxiomProfile.lean), collects the axiom dependencies of the core results in one place: the central theorem T-SNAP depends on no axioms, the choice-free core (lattice, Quine-atom self-reference) is listed, and an honest contrast shows where `Classical.choice` enters (the analytic realizations). Build it with `lake build ZeroParadox.AxiomProfile`. The same finding is written up in [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf).

| Document | Lean Source | Verifies | Build |
|----------|-------------|----------|-------|
| ZP-A Lattice Algebra | [ZPA.lean](ZeroParadox/ZPA.lean) | Partial order, ⊥ as the minimum, monotonicity of state change | Clean - April 2026 |
| ZP-B p-Adic Topology | [ZPB.lean](ZeroParadox/ZPB.lean) | p = 2 forced; Q₂ ultrametric, clopen balls, total disconnectedness, snap irreversibility | Clean - April 2026 |
| ZP-C Information Theory | [ZPC.lean](ZeroParadox/ZPC.lean) | Distinct state distributions, 1-bit divergence, execution as a nonzero change, unbounded surprisal at ⊥ | Clean - April 2026 |
| ZP-D State Layer | [ZPD.lean](ZeroParadox/ZPD.lean) | Transition operator into Hilbert space: existence, uniqueness up to unitary, orthogonality under the snap | Clean - April 2026 |
| ZP-E Bridge Document | [ZPE.lean](ZeroParadox/ZPE.lean) | The snap as a derived theorem (T-SNAP); instantiation succession; axiom-free minimal path | Clean - April 2026 |
| ZP-F The Counterexamples | [ZPF.lean](ZeroParadox/ZPF.lean) | The snap cannot occur in any ordered field (ℝ, ℚ as instances) | Clean - May 2026 |
| ZP-G Category Theory | [ZPG.lean](ZeroParadox/ZPG.lean) | Initial object and its universal property; forward-only structure; the informational singularity | Clean - April 2026 |
| ZP-H Categorical Bridge | [ZPH.lean](ZeroParadox/ZPH.lean) | The snap under all four domain functors; singularity reconciliation | Clean - April 2026 |
| ZP-H Native Categories | [ZPH_TopFunctor.lean](ZeroParadox/ZPH_TopFunctor.lean), [ZPH_HilbFunctor.lean](ZeroParadox/ZPH_HilbFunctor.lean), [ZPH_InfoFunctor.lean](ZeroParadox/ZPH_InfoFunctor.lean), [ZPH_MC1.lean](ZeroParadox/ZPH_MC1.lean) | The snap floor realized in real Mathlib categories: ⊥ as inverse limit in TopCat, initial object in ModuleCat ℂ and KleisliCat PMF; mc1_correspondence bundle | Clean - June 2026 |
| ZP-I Inside Zero | [ZPI.lean](ZeroParadox/ZPI.lean) | Every maximal chain is Cauchy and converges to its own successor ⊥ (Inside Zero) | Clean - April 2026 |
| ZP-J Self-Reference (Core) | [ZPJ.lean](ZeroParadox/ZPJ.lean) | The Quine atom is ⊥ (executable self-reference); CC-1 derived axiom-free | Clean - April 2026 |
| ZP-J AFA Derivation Chain | [ZPJ_AczelConn.lean](ZeroParadox/ZPJ_AczelConn.lean), [ZPJ_SelfApp.lean](ZeroParadox/ZPJ_SelfApp.lean), [ZPJ_Scale.lean](ZeroParadox/ZPJ_Scale.lean), [ZPJ_OntBridge.lean](ZeroParadox/ZPJ_OntBridge.lean), [ZPJ_Model.lean](ZeroParadox/ZPJ_Model.lean), [ZPJ_ScaleBridge.lean](ZeroParadox/ZPJ_ScaleBridge.lean) | ValuationStructure → AbstractSelfApp → AFAStructure; DC-free Aczel uniqueness; ValBridge common ancestor unifying the lattice track and ℤ₂; concrete ℤ₂ and ℕ∞ instances | Clean - June 2026 |
| ZP-J APG Decoration Uniqueness | [ZPJ_APG.lean](ZeroParadox/ZPJ_APG.lean) | Decoration uniqueness for finite accessible pointed graphs, by induction on reachable size | Clean - May 2026 |
| ZP-J Wheel of Fractions | [ZPJ_Wheel.lean](ZeroParadox/ZPJ_Wheel.lean), [ZPJ_WheelFrac.lean](ZeroParadox/ZPJ_WheelFrac.lean) | The wheel of fractions is a wheel (Carlström Def 1.1), choice-free; ∞ ≠ ⊥ | Clean - June 2026 |
| ZP-K Computational Grounding | [ZPK.lean](ZeroParadox/ZPK.lean) | Computational grounding via a Kleene fixed point; the snap closed concretely | Clean - April 2026 |
| ZP-L Incomputability Convergence | [ZPL.lean](ZeroParadox/ZPL.lean) | ε₀ as the exact snap threshold; the ordinal tower converges 2-adically to 0 (24 theorems) | Clean - May 2026 |
| ZP-M Kleene-Ordinal Bridge | [ZPM.lean](ZeroParadox/ZPM.lean) | Type bridge MachinePhase → ℤ₂; Kleene quine and ε₀ fixed point co-witnessed | Clean - May 2026 |
| ZP-P The Fixed-Point Fork | [ZPP.lean](ZeroParadox/ZPP.lean), [ZPP_Ostrowski.lean](ZeroParadox/ZPP_Ostrowski.lean), [ZPP_Coalgebra.lean](ZeroParadox/ZPP_Coalgebra.lean) | The least/greatest fixed-point fork collapses iff the operator has a unique fixed point (choice-free); number-system instance ℝ vs ℚ₂ via Ostrowski; categorical-parent instance (Fix empty / Cofix inhabited) via QPF | Clean - June 2026 |

**Purity note**

All proofs are machine-checked. The classical axioms that appear (`Classical.choice`) come from Mathlib's computability, analysis, and ordinal libraries - they are infrastructure dependencies, not Zero Paradox commitments, and `Classical.choice` in Lean is distinct from the set-theoretic Axiom of Choice. Whether it is structurally forced by the snap geometry or merely incidental to Mathlib's implementation is an open question (see [Question Register](#question-register)).

<details>
<summary><b>Per-file axiom footprint</b> - click to expand</summary>

ZP-H, ZP-I, ZP-J (extension files), ZP-K, ZP-L, and ZP-M use `Classical.choice` via Mathlib computability, analysis, and ordinal infrastructure (Kleene's theorem, Roger's fixed-point theorem, metric space completion, ordinal arithmetic, and p-adic valuation). `Classical.choice` is the Lean kernel axiom that grounds classical excluded middle; it does not introduce non-constructive selection over infinite families of sets. The `#print axioms` check reports `[propext, Classical.choice, Quot.sound]` across ZP-I, ZP-K, ZP-L, ZP-M, and the ZP-J extension files (ZPJ_Scale, ZPJ_Model, ZPJ_APG); the classical axioms enter through Code/Partrec, analysis machinery, ordinal fixed-point theory, and p-adic library infrastructure, not through the ZPSemilattice or AFAStructure fields. The ZP-J core file (ZPJ.lean) and ZPJ_AczelConn, ZPJ_SelfApp, ZPJ_OntBridge, and ZPJ_WheelFrac are `Classical.choice`-free. ZP-A through ZP-G are `Classical.choice`-free except where standard Mathlib theorems require it.

</details>

### Formal Framework Documents

| File | Document | Version | Focus |
|------|----------|---------|-------|
| [ZP-A Lattice Algebra](ZP-A_Lattice_Algebra.pdf) | ZP-A | v1.14 | The lattice-algebra foundation: the bottom element ⊥ and the order it induces. |
| [ZP-B pAdic Topology](ZP-B_pAdic_Topology.pdf) | ZP-B | v1.10 | The 2-adic topology: why p = 2, and why departure from ⊥ is irreversible. |
| [ZP-C Information Theory](ZP-C_Information_Theory.pdf) | ZP-C | v1.18 | The information layer: state distributions, 1-bit cost, unbounded surprisal at ⊥. |
| [ZP-D State Layer](ZP-D_State_Layer.pdf) | ZP-D | v1.12 | The Hilbert-space layer: the snap as an orthogonal shift between states. |
| [ZP-E Bridge Document](ZP-E_Bridge_Document.pdf) | ZP-E | v3.21 | The bridge: the snap assembled as a derived theorem across the layers. |
| [ZP-F The Counterexamples](ZP-F_The_Counterexamples.pdf) | ZP-F | v1.4 | The counterexamples: ordered fields (ℝ, ℚ) where the snap cannot occur. |
| [ZP-G Category Theory](ZP-G_Category_Theory.pdf) | ZP-G | v1.12 | The categorical layer: ⊥ as initial object, the informational singularity. |
| [ZP-H Categorical Bridge](ZP-H_Categorical_Bridge.pdf) | ZP-H | v1.16 | The categorical bridge: the snap holding under all four domain functors. |
| [ZP-H Native Categories Addendum](ZP-H_Native_Categories_Addendum.pdf) | ZP-H Native Categories Addendum | v1.0 | The snap floor realized inside each framework's native Mathlib category (TopCat, ModuleCat ℂ, KleisliCat PMF). Reads after ZP-H. |
| [ZP-I Inside Zero](ZP-I_Inside_Zero.pdf) | ZP-I | v1.11 | Inside zero: each maximal chain converging to its own successor ⊥. |
| [ZP-J Self-Reference](ZP-J_Self_Reference.pdf) | ZP-J | v2.2 | Self-reference: ⊥ as the Quine atom, and the AFA structure it forces. |
| [ZP-J AFA Addendum](ZP-J_AFA_Addendum.pdf) | ZP-J AFA Addendum | v1.3 | Decoration uniqueness for finite graphs from the valuation structure alone. Reads after ZP-J. |
| [ZP-J Wheel Addendum](ZP-J_Wheel_Addendum.pdf) | ZP-J Wheel Addendum | v1.0 | The wheel of fractions as a wheel: division by zero made total. Reads after ZP-J. |
| [ZP-K Computational Grounding](ZP-K_Computational_Grounding.pdf) | ZP-K | v1.7 | Computational grounding: the snap as a Kleene fixed point. |
| [ZP-L Incomputability Convergence](ZP-L_Incomputability_Convergence.pdf) | ZP-L | v1.1 | ε₀ as the exact ordinal threshold where the snap occurs. |
| [ZP-M Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf) | ZP-M | v1.1 | The bridge between the Kleene quine and the ε₀ fixed point. |
| [ZP-P The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) | ZP-P | v1.1 | Synthesis layer: the least-vs-greatest fixed-point fork, generalizing the Foundation/AFA orthogonal-contact-point claim across frameworks. |
| [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf) | Choice-Free Core | v1.0 | Framework-wide note: the central results are choice-free (T-SNAP is axiom-free); Classical.choice appears only in the analytic realizations, inherited from Mathlib. Anchored on AxiomProfile.lean. |

---

## Axiomatic Commitments

A commitment marked "not a novel commitment" means its content is formally grounded in prior layers and derivable from results established there. It is stated as a local axiom only for the self-containment of that layer - the same pattern by which AX-1 was stated as an axiom before being formally derived as T-SNAP in ZP-E.

**Metatheoretic note**

This framework is stated over ZF + AFA (Zermelo-Fraenkel with Anti-Foundation Axiom), not standard ZFC, and AFA permits self-containing sets (x = {x}). This affects only one commitment, the Quine atom (CC-2); the remaining results do not depend on non-well-founded sets. The Axiom of Choice is not assumed. The move to AFA is not a free choice - it is forced by the framework's own results. What "forced" means here, and the discipline every such claim must meet, is defined in [Forced Metatheoretic Commitment](fmc.md).

<details>
<summary><b>Why AFA, and why it is forced</b> - click to expand</summary>

Standard ZFC is incompatible with CC-2: a well-founded ⊥ would admit an external interpreter, contradicting the self-execution argument. The forcing comes from the framework's results: ZP-A R3 and ZP-C L-INF together establish that ⊥ admits no finite external description, which is incompatible with the Foundation axiom's well-foundedness requirement (no infinite descending ∈-chains). The full argument for why AFA specifically is the appropriate extension - rather than simply removing Foundation - is developed in ZP-E Remark R-AFA.

</details>

**AX-1 (Binary Snap Causality) is no longer an axiom.** It is Theorem T-SNAP, derived in ZP-E from A4 - the standard bottom element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x). AX-1 was redundant: any join-semilattice with bottom already has this property. The snap is not imposed on the algebraic structure - it is a consequence of it.

**The single bottom (MC-1)**

The bottom elements across the layers - the algebraic ⊥, the 0 of Q₂, the Turing initial configuration c₀, and the categorical initial object - are identified as one object, the same self-referential (diagonal) fixed point in each framework. This identification splits into a correspondence half, now formally realized in Lean, and an identity half - that the four are numerically one object - which remains a modeling commitment rather than a proven identity. Its faces are the Quine atom (⊥ = {⊥}) in set theory, the Kleene quine in computation, the point v₂(0) = ∞ in valuation, and the initial object in category theory. This identification is substantially grounded rather than stipulated: each domain locates its own bottom through its own logic first, and the cross-layer agreement is then enforced formally (the ZP-E typeclass instance ties ZP-A ⊥ to ZP-C c₀; AX-G1 grounds the categorical initial in ZP-A ⊥; ZP-H T-H3 proves snap consistency across all four functors). The categorical correspondence is now realized in the standard domain categories of Mathlib: the snap floor is the inverse limit in `TopCat`, the initial object in `ModuleCat ℂ`, and the initial object in the Kleisli category of the probability monad `KleisliCat PMF` - with no morphism returning to it in the stochastic case (the bundled witness is `mc1_correspondence`). What remains is the interpretive choice to call these one object.

<details>
<summary><b>The supporting commitments</b> (label, type, statement) - click to expand</summary>

| Label | Type | Statement |
|-------|------|-----------|
| **AX-B1** | Directly Verifiable | A state either exists or it does not. Directly verifiable by computation (OntologicalStates derives DecidableEq; ax_b1_distinct proved by `decide` without classical axioms) - not a novel commitment of this framework. |
| **AX-G1** | Axiom | An initial object exists in the category C. The bottom element ⊥ is the universal origin of all structure: a unique object from which every other object is reachable, and to which no morphism returns. Not a novel commitment - ⊥'s existence as the bottom element of the ZP-A semilattice already guarantees this; ZP-G names it in categorical language. |
| **AX-G2** | Axiom | Source asymmetry: hom(X, 0) = ∅ for X ≠ 0. Once something emerges, it cannot return to nothing. Not a novel commitment - follows from antisymmetry of the ZP-A partial order and is independently confirmed by ZP-B C3 (topological irreversibility). |
| **MP-1** | Principle | The representational base is the minimum sufficient base for AX-B1. Derives p = 2. |
| **RP-1** | Principle | The probabilistic representation of a state in the two-element state space is a point-mass distribution. |
| **DP-1** | Design Commitment | Clopen separation in Q₂ is represented by orthogonality in H. |

</details>

---

## Question Register

The open and partially-resolved questions:

| Item | Status |
|------|--------|
| DA-3: Perspective-relative cardinality | Closed (definitional) / Candidate (DA-3-C1) - ZP-E DA-3 (definitional closure via D7 exhaustiveness; formal cardinality derivation deferred to OQ-E2) |
| OQ-E2: Cardinality-semilattice correspondence | **Partially closed - ZP-I T-IZ** - ordinal indexing Omega = omega forced by countable binary substrate (ZP-C D4, Q2 separability, binary alphabet). Internal/external perspective relativity is ordinal, not set-theoretically free. Formal connection between specific semilattice structures and specific CH instances remains open. |
| ε₀ / proof-theoretic ordinal | **Partially closed - ZP-L May 2026.** c1_epsilon_zero_identification establishes the canonical snap map (MachinePhase → Ordinal) with ε₀ as the exact transition point. snap_zp2_correspondence proves the four-way conjunction (ordinal bound, phase assignment, p-adic convergence, snap assignment). Structural alignment with Gentzen's proof-theoretic ordinal (PA consistency) documented in ZP-L Remark R-L.1. Full type-theoretic identity across type universes (MachinePhase vs. Ordinal) is outside Lean scope and deferred pending OQ-E2. |
| Classical.choice necessity | **Core is choice-free (verified); analytic-layer necessity is Open.** The central results carry no Classical.choice - T-SNAP depends on no axioms at all, and the lattice (ZP-A), the Quine-atom self-reference (ZP-J), and the structural floor are choice-free (checkable in [AxiomProfile.lean](ZeroParadox/AxiomProfile.lean)). Classical.choice appears elsewhere only where the framework builds on Mathlib's classically-built topology / analysis / ordinal / computability libraries - the analytic realization layers (e.g. ZP-B, ZP-D, ZP-L, the ZP-H functors) and auxiliary constructions on them. Whether that inherited dependence is structurally forced or merely incidental is the open question; the one layer classified so far (ZPB_PadicTree, the choice-probe experiment) found it mostly incidental and routable. Testable via constructive ordinal fixed-point theory over ONote/NONote; future ZP-N (constructive validation layer). |

**Verification status:** ZP-A through ZP-M and ZP-P, plus the ZP-H native-category functors and `mc1_correspondence`, are machine-verified in Lean 4 (see the Formal Verification table above). A second-prover cross-check (e.g. Rocq) is not yet done.

### Design Commitments

Choices the framework adopts as explicit, motivated commitments - not open questions, and not derived theorems. They are listed here so the register above holds only genuinely unresolved questions. (The commitments specifically grounding the single bottom - AX-G1, AX-G2, MP-1, RP-1, DP-1 - appear under "The single bottom (MC-1)" above.)

| Commitment | Nature |
|------------|--------|
| Temperature T (BA-1) | A universe-contingent parameter; the specific value is irrelevant to the framework's structure - a deliberate scale choice, not an open question. |
| DP-2 (Execution Distinguishability) | The modeling commitment DA-1 rests on; motivated by ZP-C D7, not freely chosen. DA-1 is closed given DP-2 (see Resolved questions). |
| MC-1 identity | Reading the four domain bottoms as numerically one object. The correspondence half - each is its own category's categorical bottom - is a theorem (`mc1_correspondence`); the identity half is this chosen identification. |

<details>
<summary><b>Resolved questions</b> (closed) - click to expand</summary>

| Item | Status |
|------|--------|
| OQ-A1: Increment selection | Closed - ZP-E T5 (Iterative Forcing Theorem) |
| OQ-B1: p = 2 justification | Closed - ZP-B T0 (derived from AX-B1 + MP-1) |
| S1: Distribution stipulation | Closed - ZP-C T1 (derived from AX-B1 + RP-1) |
| OQ-C1: Non-conservatism of DF | Closed - ZP-C T2 (rebuilt within extended D6) |
| CC-1 (S₀ = ⊥) derivability | **Closed - ZP-J cc1_derived (axiom-free, Lean)** - was ZP-A Conditional Claim; now derived via ZP-J T-EXEC in any AFAStructure lattice; ZP-A v1.11 declaration and preface added for clarity |
| CC-2 (⊥ = {⊥}, the Quine atom) as commitment | **Closed - ZP-J T-EXEC** - ⊥ = {⊥} is structurally forced by self-execution argument; not a freestanding modelling choice |
| AX-1: Binary Snap Causality | **Closed - ZP-E T-SNAP (derived theorem)** |
| OQ-E1: Sequence vs. tree structure | Closed - ZP-E DA-2 (directed instantiation tree; branching mandatory via T-SNAP) |
| DA-2: Instantiation succession | Closed - ZP-E DA-2 (terminal state of I_n satisfies ⊥ role for I_n+1; C-DA2 derives that each instantiation produces a provably distinct ⊥) |
| DA-1: Instantiation alignment | **Closed given DP-2 - ZP-E / ZP-K.** da1_minimal_path proved axiom-free in Lean; Paths 1 and 3 closed via da1_closed_concrete (ZP-K). The former Path 2 (the AIT bridge between ZP-C and computability) is a foundational commitment, carried by DP-2's motivational grounding (see Design Commitments) - a chosen principle rather than a proof gap, the same kind of standing residual as MC-1's identity half. |
| OQ-G1: Native categorical surprisal | Closed - ZP-G D7' and I-KC (Kolmogorov import; BA-G1 demoted to compatibility remark R-BA) |
| OQ-G2: Left adjoint verification | Closed - ZP-H T-H1 (initial-object universal property verified for all four domain instantiations: F_A via NatSLat; F_B/C/D via ℝ≥0 proxy witness) |
| OQ-G3: Functor construction | **Closed - ZP-H functor files, June 2026.** F_A (NatSLat) plus sorry-free Lean functors into the standard Mathlib categories: fB_functor into TopCat (⊥ = inverse limit of the clopen-ball tower), fD_functor into ModuleCat ℂ (⊥ = StateSpace 0, the initial zero object), fC_functor into KleisliCat PMF (⊥ = Fin 0 initial; fC_no_return = AX-G2 as a theorem); bundled as mc1_correspondence. The ℕ-shaped depth proxies are superseded. The cross-category identity residual is a design commitment (MC-1 identity, above). |
| OQ-G4: Singularity reconciliation | Closed - ZP-H T-H2 (categorical and ZP-C characterizations shown to be same obstruction) |
| T-IZ: Inside Zero Theorem | **Fully derived - Lean, April 2026** - every maximal ascending chain converges to its own successor null. R-IZ-A closed: h_strict_from_r1_t3 derives v2(S(n)) strictly increasing from IsDepthChain + IsStrictStateSequence (ZP-A lattice axioms) - no longer a construction-level hypothesis. t_iz_complete formally chains all four T-IZ steps: Cauchy convergence (t_iz_cauchy), DA-2 successor null identification (t_iz_limit_is_new_null), DA-1 via AFA/Kleene (da1_computational, ZP-K), T-SNAP (bot_join). Kolmogorov complexity bridge superseded. |
| Null balance | **Closed - T-IZ + DA-2** - exact and derived: every branch starts at ⊥, ascends omega state changes (T3), generates a successor ⊥ at the ordinal limit (T-IZ + T-SNAP + DA-2). |

</details>

Open questions are discussed publicly in the [GitHub Discussions Open Questions category](https://github.com/timbrigham/ZeroParadox/discussions/categories/open-questions).

---

## Version History

Hosted at [timbrigham/ZeroParadox](https://github.com/timbrigham/ZeroParadox). Previous document versions are in [historical/](historical/). See [GUIDE.md](GUIDE.md) for development notes and process documentation.

---

## License

All conceptual development, structure, and authorship originate with the human creator.

This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License (CC BY-NC-ND 4.0).

You may share the work with attribution, but you may not modify it or use it commercially. See [LICENSE](LICENSE) for full details.

---

## Citation

If referencing this work, please cite:

> Brigham, Timothy. The Zero Paradox (April 2026). https://github.com/timbrigham/ZeroParadox

---

## Contact

For inquiries, discussion, or collaboration, reach out by email at [timbrigham@zeroparadox.org](mailto:timbrigham@zeroparadox.org) or open an issue on [GitHub](https://github.com/timbrigham/ZeroParadox).

---

*Zero Paradox | April 2026*
