# The Zero Paradox
**April 2026 | Closed Formalism**

*A formal mathematical proof that the emergence of something from nothing is not a starting assumption — it can be derived.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham)

---

## Contents

- [What This Is](#what-this-is)
- [The Central Result](#the-central-result)
- [What This Is Not](#what-this-is-not)
- [The Framework](#the-framework)
  - [Entry Point](#entry-point)
  - [Formal Ontology Documents](#formal-ontology-documents)
  - [Illustrated Companion Documents](#illustrated-companion-documents-general-reader)
  - [Supporting Documents](#supporting-documents)
  - [Formal Verification (Lean 4)](#formal-verification-lean-4)
- [Axiomatic Commitments](#axiomatic-commitments)
- [Question Register](#question-register)
- [Reading Order](#reading-order)
- [Notes on Development](#notes-on-development)
- [License](#license) · [Citation](#citation) · [Contact](#contact)

---

## What This Is

The Zero Paradox is a rigorous multi-framework mathematical ontology addressing a single question: can the emergence of state from a null condition be given a formally complete, cross-disciplinary account?

The answer developed here is yes. The proof is distributed across eight self-contained mathematical layers, each internally closed before any cross-framework claim is made.


---

## The Central Result

The **Binary Snap** (the first transition from nothing to something) - the transition from the Null State ⊥ to the first atomic state ε₀ - is a **theorem**, not an axiom.

The symbol ⊥ is not overloaded by analogy: the framework identifies logical falsum, order-theoretic bottom, and the ontological null state as a single object. These are three descriptions of the same null state. This cross-framework identification is a modeling commitment (MC-1) — the foundational design choice that makes multi-layer synthesis possible. It is not derived; it is chosen. See [Axiomatic Commitments](#axiomatic-commitments). Similarly, ε₀ is intentionally identified with the Cantor/Gentzen proof-theoretic ordinal (least fixed point of α ↦ ω^α; the proof-theoretic strength of Peano Arithmetic) - both name the minimal threshold that transcends finite iteration. This identification is named and motivated in ZP-E; formal embedding of the framework's state lattice into ordinal theory is deferred pending OQ-E2 (see Question Register).

Most frameworks for describing the first emergence of something assume it. This framework does not. The Binary Snap is not a starting assumption - it is a structural consequence of standard mathematical commitments of the kind any model of additive states would adopt independently. No snap-specific axioms appear anywhere in the framework. The Binary Snap is the moment the transition is forced: when the mathematics demands that something emerge from the null state.

The derivation chain is:

**P₀** (incompressibility threshold, ZP-C D1)  
→ **DA-1** (instantiation of a configuration at P₀ constitutes an execution event, ZP-E)  
→ **D7** (machine configuration definition, ZP-C)  
→ **L-RUN** (execution is a non-null state change, ZP-C)  
→ **TQ-IH** (no program outputs ⊥ without a non-null intermediate state, ZP-C)  
→ **ZP-A D2** (a non-null state change from ⊥ is a join - the Binary Snap)  
→ **T-SNAP** (Binary Snap follows from A4, the standard bottom element axiom; AX-1 was redundant)

This framework introduces no snap-specific axioms. T-SNAP follows from A4 — the standard bottom element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x) — a natural axiom for modeling additive state accumulation, not an assumption crafted to produce the snap. Every other commitment is either directly verifiable by computation (AX-B1) or a categorical restatement of structure established in prior layers (AX-G1, AX-G2). See [Axiomatic Commitments](#axiomatic-commitments) for the full account.

---

## What This Is Not

- **Not a physical theory** - the framework is instantiation-independent; physical theories are recovered by fixing ε₀
- **Not a claim about consciousness or the hard problem** - the framework is silent on these questions
- **Not a claim that zero is paradoxical in all of mathematics** - the paradox is local to this framework's structure
- **Not a logical contradiction** - no theorem in ZP-A through ZP-D contradicts any other

---

## The Framework

### Entry Point

| File | Description |
|------|-------------|
| [Zero Paradox Foreword](Zero_Paradox_Foreword.pdf) | Plain-language introduction for any reader. Start here. |

### Formal Ontology Documents

| File | Document | Version | Contents |
|------|----------|---------|----------|
| [ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_11.pdf) | ZP-A | v1.11 | Join-semilattice (L, ∨, ⊥). Axioms A1-A4. Monotonicity. Additive ontology. CC-2: ⊥ = {⊥} (Quine atom, ZF + AFA). R3: CC-2 eliminates static-description state for ⊥, given D7 exhaustiveness (ZP-E) as background. v1.11: ZF+AFA metatheoretic declaration added before Section I; plain English preface added immediately before CC-1. v1.10: CC-1 box title updated — "Conditional Claim CC-1" replaced with "CC-1 (Derived/Conditional)" to reflect dual status at first glance. v1.9: CC-1 status updated — DERIVED (given AFAStructure grounding, ZP-J T-EXEC); structural consequence in any AFAStructure lattice; modelling commitment at ZP-A level. |
| [ZP-B pAdic Topology](ZP-B_pAdic_Topology_v1_4.pdf) | ZP-B | v1.4 | AX-B1. MP-1 (design commitment). T0: p=2 derived given MP-1. Q₂ ultrametric. Clopen balls. Total disconnectedness. Topological irreversibility. |
| [ZP-C Information Theory](ZP-C_Information_Theory_v1_9.pdf) | ZP-C | v1.9 | P₀. State representations from AX-B1. JSD = 1 bit. Discrete surprisal field. **L-RUN. TQ-IH. T-BUF** (AX-1 derivability pathway complete within ZP-C; closed as T-SNAP in ZP-E). CC-2: c₀ = ⊥ labeled as modeling commitment. RP-2: branching measure labeled as representational commitment. L-INF grounded from two directions: informational extremity (D4, T2) and structural self-containment (ZP-A CC-2, R3). v1.8: Remark R-BRIDGE added — explicit statement that K (Kolmogorov complexity) and I(n) (2-adic surprisal) are distinct measures that coincide at P₀ from independent directions; independence preserved by design. |
| [ZP-D State Layer](ZP-D_State_Layer_v1_6.pdf) | ZP-D | v1.6 | Hilbert space H = ℂⁿ, foundational minimum n = 2. Transition operator T: Q₂ → H — locally constant, continuous (R3 v1.6). DP-1. Existence and uniqueness of T. Snap → orthogonal shift. Non-decreasing norms. |
| [ZP-E Bridge Document](ZP-E_Bridge_Document_v3_10.pdf) | ZP-E | v3.10 | **DA-1** (instantiation = execution; DP-2 (Execution Distinguishability) — TrackedOutput separates output value from machine state; da1_minimal_path proved axiom-free in Lean. Three informal paths explicitly framed as corroboration of DP-2's precondition, not parallel proofs). **T-SNAP** (Binary Snap derived). **DA-2** (instantiation succession, directed tree). **DA-3** (perspective-relative cardinality). Remark R-ε₀ (informal structural analogy — now leads with disclaimer). Remark R-AFA (Foundation ruled out; AFA forced). v3.10: Forward references to "ZP-PQ" replaced with "The Philosophical Question That Started This" — that document already contained the dissolution argument. v3.9: R-ε₀ reframed — remark leads with explicit informal-analogy disclaimer; "structural correspondence" changed to "structural analogy". v3.8: DA-1 Path 2 recharacterized — foundational commitment, a missing principle not a missing proof; forward paths: new axiom, Chalmers' implementation, The Philosophical Question That Started This. DA-1 does not depend on Path 2. v3.7: DA-1 formally closed via ZP-K — da1_closed_concrete : IsQuineAtom(⊥ : MachinePhase) proved in Lean 4; Paths 1 and 3 IN LEAN SCOPE. Full traceability register. |
| [ZP-G Category Theory](ZP-G_Category_Theory_v1_5.pdf) | ZP-G | v1.5 | Category C. Initial object. AX-G1, AX-G2. Universal property. R2 (v1.3): connecting note linking initial object structure (T2 + AX-G2) to ZP-A CC-2 (⊥ = {⊥}). v1.5: Lean scope disclosure for T6-b/T6-c strengthened — Lean proofs verify only Nat.zero_le _ (non-negativity by type; verifies nothing about K); T6-b strict inequality and T6-c subadditivity are NOT Lean-verified; status lines and validation table updated explicitly. T6 Part II (undefined domain via AX-G2) remains fully Lean-verified. |
| [ZP-H Categorical Bridge](ZP-H_Categorical_Bridge_v1_7.pdf) | ZP-H | v1.7 | Instantiation maps FA-FD (F_A: full construction via NatSLat; F_B/C/D: PDF constructions complete; Lean: one shared witness nnreal_initial_grounding, domain facts C3/T1b/T4 proved separately - full abstract functors future work). F_C composition by Q-stability (not JSD subadditivity). Singularity reconciliation. T-H3: Snap under all four instantiations. T-SNAP inherited as derived theorem. v1.7: T-H3 consistency note strengthened — independence of null-analog discovery foregrounded; each domain located its null-analog through its own logic prior to cross-framework identification. |
| [ZP-I Inside Zero](ZP-I_Inside_Zero_v1_5.pdf) | ZP-I | v1.5 | **T-IZ (Inside Zero):** every maximal ascending chain is a Cauchy sequence converging to its own successor null in Q2. Formal spine: Step 1 (t_iz_cauchy, axiom-free) + Step 6 (t_iz_limit_is_new_null, axiom-free via DA-2). Both proved in Lean with no new axioms. Valuation-complexity bridge demoted to informational context — DA-1 formally closed by ZP-K/Kleene, no Kolmogorov complexity required. OQ-E2 partially closed — ordinal indexing Omega = omega forced by countable binary substrate. v1.5: Section V "Complete Cycle" and Null Balance callout updated — "framework closure" now explicitly conditional on R-IZ-A (v2(S(n)) >= n construction-level hypothesis). v1.4: Remark R-IZ-A added — v2(S(n)) >= n hypothesis acknowledged as construction-level assumption. |
| [ZP-J Self-Reference](ZP-J_Self_Reference_v1_1.pdf) | ZP-J | v1.1 | **T-EXEC (Executability of Self-Reference):** in any ZP-A lattice with AFA grounding, the unique Quine atom Q = {Q} is provably the bottom element ⊥. CC-1 (S₀ = ⊥) derived as theorem (cc1_derived, axiom-free). CC-2 (⊥ = {⊥}) structurally forced. Three-way equivalence: Quine atom = ⊥ = join-identity element. All theorems verified axiom-free in Lean 4. v1.1: Remark R-J.0 added — bot_self_mem := rfl in MachinePhase is a structural analogy (CIC encoding), not a ZF+AFA set-theoretic derivation; AFAStructure concrete instances item CLOSED (ZP-K machinePhaseAFA). |
| [ZP-K Computational Grounding](ZP-K_Computational_Grounding_v1_3.pdf) | ZP-K | v1.3 | **T-COMP (Computational Grounding):** (1)-(3) equivalent by T-EXEC (Quine atom = ⊥ = join identity); (4) Kleene fixed point combined by KleeneStructure typeclass requirement. KleeneStructure typeclass bridges AFAStructure to computability. MachinePhase instances: machinePhaseAFA + machinePhaseKleene. **DA-1 closed concretely:** da1_closed_concrete : IsQuineAtom(⊥ : MachinePhase). selfApply_partrec proved via Kleene's second recursion theorem. v1.3: Forward references to "ZP-PQ" replaced with "The Philosophical Question That Started This" — that document already contained the dissolution argument. v1.2: DA-1 Path 2 recharacterized — foundational commitment, not missing proof; Open Items Register updated from OPEN to FOUNDATIONAL COMMITMENT. v1.1: Remark R-K.0 added — four-way equivalence clarified. |

### Illustrated Companion Documents (General Reader)

One companion per formal document. Plain language, diagrams, real-world examples.

> **Note (April 2026):** The companion documents are currently behind the formal layers. The formal documents (ZP-A through ZP-H) have undergone significant structural revisions - including the addition of DA-1's Lean formalization (DP-2, ZP-E v3.0), the ZF+AFA foundation note (ZP-A v1.7), and Lean scope clarifications in ZP-G and ZP-H. Companion updates are in progress. Until then, treat the companions as introductions to the framework's structure rather than authoritative statements of current result labels or claim statuses.

| File | For Document | Key Diagrams |
|------|-------------|--------------|
| [ZP-A Illustrated Companion](ZP-A_Illustrated_Companion.pdf) | ZP-A | Hasse diagram, one-directional transitions |
| [ZP-B Illustrated Companion](ZP-B_Illustrated_Companion.pdf) | ZP-B | Nested clopen balls, disjoint ball separation |
| [ZP-C Illustrated Companion](ZP-C_Illustrated_Companion.pdf) | ZP-C | Surprisal field singularity, 1-bit Snap cost, L-RUN execution trace |
| [ZP-D Illustrated Companion](ZP-D_Illustrated_Companion.pdf) | ZP-D | T map: topology → orthogonality |
| [ZP-E Illustrated Companion](ZP-E_Illustrated_Companion.pdf) | ZP-E | Four-framework convergence, T-SNAP derivation chain |
| [ZP-G Illustrated Companion](ZP-G_Illustrated_Companion.pdf) | ZP-G | Category and functor concepts, initial object, informational singularity |
| [ZP-H Illustrated Companion](ZP-H_Illustrated_Companion.pdf) | ZP-H | Four-functor convergence, T-SNAP derivation chain, Binary Snap across all frameworks |
| [ZP-I Illustrated Companion](ZP-I_Illustrated_Companion.pdf) | ZP-I | 2-adic depth diagram, three closed doors + Cauchy passage, complete cycle diagram |
| [ZP-J Illustrated Companion](ZP-J_Illustrated_Companion.pdf) | ZP-J | Quine atom diagram (⊥ = {⊥}), three-way equivalence table, CC-1/CC-2 as derived theorems |
| [ZP-K Illustrated Companion](ZP-K_Illustrated_Companion.pdf) | ZP-K | Four-way equivalence diagram, computational Quine, DA-1 formal closure |

### Supporting Documents

| File | Description |
|------|-------------|
| [The Philosophical Question That Started This](ZP_Philosophical_Question.pdf) | The question that motivated the entire framework - why does something exist rather than nothing? - and what the mathematics discovered about it, including what it dissolves and what it snaps. |
| [ZP Tools and Methods](ZP_Tools_and_Methods.pdf) | How the framework was developed: Claude's role, what formal tools were and were not used (Rocq, Lean, etc.), the PDF rendering pipeline. |

### Formal Verification (Lean 4)

Machine-checked proofs of the formal documents using Lean 4 + Mathlib. Source lives under `ZeroParadox/` in this repository.

| Document | Lean Source | Theorems Verified | Build |
|----------|-------------|-------------------|-------|
| ZP-A Lattice Algebra | [ZeroParadox/ZPA.lean](ZeroParadox/ZPA.lean) | T1 (partial order), T2 (⊥ minimum), D2 equivalence, T3 (monotonicity), CC-1 (conditional) | Clean - April 2026 |
| ZP-B p-Adic Topology | [ZeroParadox/ZPB.lean](ZeroParadox/ZPB.lean) | AX-B1, T0 (p=2 unique), T1 (ultrametric), C1 (isosceles), T2 (clopen balls), C2 (no path), T3 (isolation of 0), T5 (totally disconnected), C3 (Snap irreversible) | Clean - April 2026 |
| ZP-C Information Theory | [ZeroParadox/ZPC.lean](ZeroParadox/ZPC.lean) | T1 (distinct distributions), T1b (KL/JSD = log 2), D5 (DF antisymmetry), T2 (telescoping + divergent circulation), L-RUN (execution non-null), TQ-IH, L-INF (informational extremity) | Clean - April 2026 |
| ZP-D State Layer | [ZeroParadox/ZPD.lean](ZeroParadox/ZPD.lean) | DP-1 (orthogonality), T2 (existence of T: injective, orthogonal, norm-preserving), T3 (uniqueness up to unitary equivalence), T4 (Snap → orthogonal shift in H), T5 (non-decreasing norms) | Clean - April 2026 |
| ZP-E Bridge Document | [ZeroParadox/ZPE.lean](ZeroParadox/ZPE.lean) | MachinePhase ZPSemilattice instance, T-SNAP (join + machine + derived + irreversibility + accessible proper subset), DA-2 (bottom characterization + novelty corollary), DA-3-D1 (accessible cardinality definition), DP-2 (TrackedOutput + da1_minimal_path axiom-free) | Clean - April 2026 |
| ZP-G Category Theory | [ZeroParadox/ZPG.lean](ZeroParadox/ZPG.lean) | ZPCategory class (AX-G1 + AX-G2), ZPSurprisal class (I-KC / D7'), T1 (initial uniqueness), T2 (universal constituent), T3 (unreachability), T4 (forward-only chains), T6-a/b/c (surprisal), T6 (informational singularity), T7 (Categorical Zero Paradox), ForkCat (concrete ZPCategory instance) | Clean - April 2026 |
| ZP-H Categorical Bridge | [ZeroParadox/ZPH.lean](ZeroParadox/ZPH.lean) | T-H1 (F_A initial object proved; F_B/F_C/F_D domain facts cited), T-H2 (singularity compatibility: ZPG unreachability ∧ ZPC divergence), T-H3 (Binary Snap under all four functors: join ∧ topological ∧ 1-bit ∧ orthogonal); nnreal_initial_grounding (single shared categorical witness for F_B/C/D) | Clean - April 2026 |
| ZP-I Inside Zero | [ZeroParadox/ZPI.lean](ZeroParadox/ZPI.lean) | t_iz_norm_tendsto_zero, t_iz_conv_zero, t_iz_cauchy (Cauchy core), t_iz_r1_t3_geometric_bound (R1+T3 → geometric bound), **t_iz_valuation_unbounded** (sup v₂ = ∞ — proof obligation row 3 closed), t_iz_limit_is_new_null (axiom-free), c_t_iz_null_balance, t_iz_c3_compatible | Clean - April 2026 |
| ZP-J Self-Reference | [ZeroParadox/ZPJ.lean](ZeroParadox/ZPJ.lean) | T-EXEC (Quine atom = ⊥, axiom-free), J1 (join-identity derived from T-EXEC + A4), cc1_derived (CC-1 as theorem), bot_is_quine_atom, t_exec_iff (full biconditional), bot_unique | Clean - April 2026 |
| ZP-K Computational Grounding | [ZeroParadox/ZPK.lean](ZeroParadox/ZPK.lean) | IsKleeneFixedPoint, selfApply_partrec (Kleene's second recursion theorem — Mathlib fixed_point₂), computational_quine_exists, KleeneStructure typeclass, T-COMP (four-way equivalence), kleene_quine_is_bot, da1_computational, da1_paths_unified, description_instantiation_gap_closed, machinePhaseAFA, machinePhaseKleene, da1_closed_concrete | Clean - April 2026 |

**Purity note:** ZP-H and ZP-K use `Classical.choice` (via Mathlib computability infrastructure — Kleene's theorem and Roger's fixed-point theorem). These are Mathlib infrastructure dependencies, not Zero Paradox commitments. The `#print axioms` check reports `[propext, Classical.choice, Quot.sound]` for ZP-K; the classical axioms enter through Code/Partrec machinery, not through the ZPSemilattice or AFAStructure fields. ZP-A through ZP-G are `Classical.choice`-free except where standard Mathlib theorems require it.

---

## Axiomatic Commitments

A commitment marked "not a novel commitment" means its content is formally grounded in prior layers and provable without additional assumptions. It is stated as a local axiom only for the self-containment of that layer — the same pattern by which AX-1 was stated as an axiom before being formally derived as T-SNAP in ZP-E.

**Metatheoretic note:** This framework is stated over ZF + AFA (Zermelo-Fraenkel with Anti-Foundation Axiom), not standard ZFC. AFA permits self-containing sets (x = {x}). This affects only CC-2 below - all other results hold in standard ZF. Standard ZFC is incompatible with CC-2: a well-founded ⊥ would admit an external interpreter, contradicting the self-execution argument. The Axiom of Choice is not assumed.

| Label | Type | Statement |
|-------|------|-----------|
| **AX-B1** | Decidable | A state either exists or it does not. Directly verifiable by computation (decidable equality on Fin 2 via `decide`) — not a novel commitment of this framework. |
| **AX-G1** | Axiom | An initial object exists in the category C. The null state is the universal origin of all structure: a unique object from which every other object is reachable, and to which no morphism returns. Not a novel commitment — ⊥'s existence as the bottom element of the ZP-A semilattice already guarantees this; ZP-G names it in categorical language. |
| **AX-G2** | Axiom | Source asymmetry: hom(X, 0) = ∅ for X ≠ 0. Once something emerges, it cannot return to nothing. Not a novel commitment — follows from antisymmetry of the ZP-A partial order and is independently confirmed by ZP-B C3 (topological irreversibility). |
| **MP-1** | Principle | The representational base is the minimum sufficient base for AX-B1. Derives p = 2. |
| **RP-1** | Principle | The probabilistic representation of a binary ontological state is a point-mass distribution. |
| **DP-1** | Design Commitment | Topological isolation in Q₂ is represented by orthogonality in H. |
| **MC-1** | Modeling Commitment | The null states across all framework layers — algebraic ⊥, the 0 of Q₂, the Turing initial configuration c₀, and the categorical initial object — are identified as a single object. This is the foundational cross-framework identification that makes multi-layer synthesis possible. It is not derived; it is chosen. |

**AX-1 (Binary Snap Causality) is no longer an axiom.** It is Theorem T-SNAP, derived in ZP-E from A4 — the standard bottom element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x). AX-1 was redundant: any join-semilattice with bottom already has this property. The snap is not imposed on the algebraic structure — it is a consequence of it.

---

## Question Register

| Item | Status |
|------|--------|
| OQ-A1: Increment selection | Closed - ZP-E T5 (Iterative Forcing Theorem) |
| OQ-B1: p = 2 justification | Closed - ZP-B T0 (derived from AX-B1 + MP-1) |
| S1: Distribution stipulation | Closed - ZP-C T1 (derived from AX-B1 + RP-1) |
| OQ-C1: Non-conservatism of DF | Closed - ZP-C T2 (rebuilt within extended D6) |
| DA-1: Instantiation alignment | Closed - ZP-E DA-1 v3.8 / ZP-K (Derived Proposition: DP-2 formal core — da1_minimal_path proved axiom-free in Lean; Paths 1 and 3 formally closed via ZP-K — da1_closed_concrete : IsQuineAtom(⊥ : MachinePhase); KleeneStructure MachinePhase instance; Path 2 recharacterized as foundational commitment — a missing principle not a missing proof; forward resolution: The Philosophical Question That Started This) |
| CC-1 (S₀ = ⊥) derivability | **Closed - ZP-J cc1_derived (axiom-free, Lean)** — was ZP-A Conditional Claim; now derived via ZP-J T-EXEC in any AFAStructure lattice; ZP-A v1.11 declaration and preface added for clarity |
| CC-2 (⊥ = {⊥}) as commitment | **Closed - ZP-J T-EXEC** — ⊥ = {⊥} is structurally forced by self-execution argument; not a freestanding modelling choice |
| AX-1: Binary Snap Causality | **Closed - ZP-E T-SNAP (derived theorem)** |
| OQ-E1: Sequence vs. tree structure | Closed - ZP-E DA-2 (directed instantiation tree; branching mandatory via T-SNAP) |
| DA-2: Instantiation succession | Closed - ZP-E DA-2 (terminal state of I_n satisfies ⊥ role for I_n+1; C-DA2 derives ontological novelty of each ⊥) |
| DA-3: Perspective-relative cardinality | Closed (definitional) / Candidate (DA-3-C1) - ZP-E DA-3 (Skolem, CH independence, Russell accounted for structurally; formal derivation deferred to OQ-E2) |
| OQ-E2: Cardinality-semilattice correspondence | **Partially closed - ZP-I T-IZ v1.5** - ordinal indexing Omega = omega forced by countable binary substrate (ZP-C D4, Q2 separability, binary alphabet). Internal/external perspective relativity is ordinal, not set-theoretically free. Formal connection between specific semilattice structures and specific CH instances remains open. |
| OQ-G1: Native categorical surprisal | Closed - ZP-G v1.1 D7' and I-KC (Kolmogorov import; BA-G1 demoted to compatibility remark R-BA) |
| OQ-G2: Left adjoint verification | Closed - ZP-H T-H1 (initial-object universal property verified for all four domain instantiations: F_A via NatSLat; F_B/C/D via ℝ≥0 proxy witness) |
| OQ-G3: Functor construction | Closed (concrete witness) / Open (full construction) - F_A: strong closure via NatSLat appendix (ℕ with max/0 as ZPCategory; 0 is categorical initial; genuine ZPA connection). F_B/C/D: shared ℝ≥0 proxy witness (NNRealZPCat appendix); domain facts C3, T1b, T4 cited. Full abstract Lean Functor terms to pTop/InfoSp/Hilb as CategoryTheory categories remain future work. |
| OQ-G4: Singularity reconciliation | Closed - ZP-H T-H2 (categorical and ZP-C characterizations shown to be same obstruction) |
| ε₀ / proof-theoretic ordinal | Open - formal documentation. The framework's ε₀ (first post-Snap state at P₀) is intentionally identified with the Cantor/Gentzen proof-theoretic ordinal ε₀ = sup{ω, ω^ω, ...}. Both name the minimal threshold transcending finite iteration; the symbol collision is not incidental. Formal embedding of L into ordinals deferred pending OQ-E2. |
| Temperature T in BA-1 | Parameter - intentional; universe-contingent |
| T-IZ: Inside Zero Theorem | **Derived - ZP-I v1.5** - every maximal ascending chain converges to its own successor null (conditional on R-IZ-A: v2(S(n)) >= n construction-level hypothesis). Formal spine Steps 1+6 both proved axiom-free (t_iz_cauchy + t_iz_limit_is_new_null). Valuation-complexity bridge demoted to informational context; DA-1 closed by ZP-K/Kleene. v1.5: Section V framework-closure language now explicitly conditional on R-IZ-A. |
| Null balance: 0 + x + (-x) = 0 | **Closed - T-IZ + DA-2** - exact and derived: every branch starts at bottom, ascends omega state changes (T3), generates successor null at ordinal limit (T-IZ + T-SNAP + DA-2). |
| Formal verification (Lean/Rocq) | ZP-A through ZP-K verified; ZP-K DA-1 formally closed (da1_closed_concrete, machinePhaseKleene) - April 2026 |

---

## Reading Order

**General reader:** [The Philosophical Question](ZP_Philosophical_Question.pdf) → [Foreword](Zero_Paradox_Foreword.pdf) → any [Illustrated Companion](#illustrated-companion-documents-general-reader) → [ZP-E Companion](ZP-E_Illustrated_Companion.pdf) → [ZP-I Companion](ZP-I_Illustrated_Companion.pdf) (framework closure)

**Mathematician:** [ZP-A](ZP-A_Lattice_Algebra_v1_11.pdf) → [ZP-B](ZP-B_pAdic_Topology_v1_4.pdf) → [ZP-C](ZP-C_Information_Theory_v1_9.pdf) → [ZP-D](ZP-D_State_Layer_v1_6.pdf) → [ZP-E](ZP-E_Bridge_Document_v3_10.pdf) → [ZP-J](ZP-J_Self_Reference_v1_1.pdf) → [ZP-K](ZP-K_Computational_Grounding_v1_3.pdf) → [ZP-I](ZP-I_Inside_Zero_v1_5.pdf) (framework closure)

**For the category theory extension:** [ZP-G](ZP-G_Category_Theory_v1_5.pdf) → [ZP-H](ZP-H_Categorical_Bridge_v1_7.pdf) (self-contained; after ZP-E)

**For process/methods:** [ZP Tools and Methods](ZP_Tools_and_Methods.pdf)

---

## Notes on Development

This framework was developed by a human researcher in collaboration with Claude (Anthropic, April 2026). Claude served as research assistant, formal scribe, and gap identifier. All mathematical content and theoretical direction originated with the researcher. See `ZP_Tools_and_Methods.pdf` for a complete account.

The PDF build tooling is publicly available in the [`scripts/`](scripts/) folder. Those scripts were generated by Claude and are included for transparency about how the documents were produced.

If you find this work valuable and would like to support its continued development, you can do so via [GitHub Sponsors](https://github.com/sponsors/timbrigham).

---

## Repository and Version History

This project is hosted on GitHub at [timbrigham/ZeroParadox](https://github.com/timbrigham/ZeroParadox). The repository uses Git for version control, allowing you to explore the evolution of the theorems and documents over time.

To view older versions of this README or the associated documents as the framework progressed:
- **Via GitHub web interface**: Navigate to the repository, click on the file, then "History" to browse commits.
- **Locally**: Use `git log` to see commit history and `git checkout <commit-hash>` to view specific versions.
- **Branches**: The main branch is the canonical public version; earlier stages are visible in commit history.

This ensures transparency in the development of the Zero Paradox.

**Previous versions of documents** are also kept in the [historical/](historical/) folder for reference, making the development process visible without requiring Git access.

---

## Purpose of This Repository

This project exists to:
- Provide a stable, versioned archive of the Zero Paradox
- Make the framework accessible to readers, researchers, and critics
- Document the evolution of the ontology and associated theorems
- Preserve formal and narrative expressions of the framework

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
