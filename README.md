# The Zero Paradox
**April 2026**

*A Lean 4 proof that the bottom element of a join-semilattice forces a minimal non-bottom state - without snap-specific axioms.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

For plain-language introduction, illustrated companions, and reading paths, see [GUIDE](GUIDE.md).

---

## Contents

- [The Central Result](#the-central-result)
- [The Framework](#the-framework)
  - [Formal Framework Documents](#formal-framework-documents)
  - [Formal Verification (Lean 4)](#formal-verification-lean-4)
- [Axiomatic Commitments](#axiomatic-commitments)
- [Question Register](#question-register)
- [Version History](#version-history)
- [License](#license) · [Citation](#citation) · [Contact](#contact)

---

## The Central Result

The **Binary Snap** - the forced transition from the bottom element ⊥ to the minimum nonzero state ε₀ - is a **theorem**, not an axiom.

The existence of a minimum nonzero element is not assumed - it follows from the structure of the bottom element itself, using only the standard bottom-element axiom of join-semilattice theory. The derivation is machine-verified in Lean 4 - independent reviewers can check the conclusion mechanically, without relying on the argument's prose presentation.

The identification of ⊥ across the framework's layers - algebraic, topological, information-theoretic, and categorical - is a modeling commitment, detailed in [Axiomatic Commitments](#axiomatic-commitments). The relationship between the framework's ε₀ and the proof-theoretic ordinal of PA (Gentzen 1936) is addressed in the [Question Register](#question-register).

The derivation chain is:

**P₀** (incompressibility threshold, ZP-C D1)  
→ **DA-1** (instantiation of a configuration at P₀ constitutes an execution event, ZP-E)  
→ **D7** (machine configuration definition, ZP-C)  
→ **L-RUN** (execution is a nonzero state change, ZP-C)  
→ **TQ-IH** (no program outputs ⊥ without a nonzero intermediate state, ZP-C)  
→ **ZP-A D2** (a nonzero state change from ⊥ is a join - the Binary Snap)  
→ **T-SNAP** (Binary Snap follows from A4, the standard bottom element axiom; AX-1 was redundant)

The snap is also irreversible: ZP-B C3 (Lean-verified) establishes that there is no continuous path from any nonzero state back to ⊥. This follows from the ultrametric structure of Q₂: the total disconnectedness of Q₂ (established via the clopen ball structure in C3) makes any return path discontinuous. The connection to the lattice layer relies on the MC-1 identification of ⊥ with the 2-adic zero, detailed in [Axiomatic Commitments](#axiomatic-commitments).

This framework introduces no snap-specific axioms. T-SNAP follows from A4 - the standard bottom element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x). Every other commitment is either directly verifiable by computation (AX-B1) or a categorical restatement of structure established in prior layers (AX-G1, AX-G2). See [Axiomatic Commitments](#axiomatic-commitments) for the full account.

**Scope of the claim.** The internal coherence is formally established - T-SNAP and the supporting layer theorems are verified in Lean 4 given the explicitly stated commitments. The author believes the formalism faithfully captures the structural notion of zero it sets out to model, but that is a question Lean cannot answer from inside, and is what this repository invites external review on. Lean answers "do these conclusions follow from these commitments." Whether the commitments are the right ones, and whether the formalism tracks the intended structural notion, are open questions for outside readers. The framework has been developed in public from the start for exactly this reason: to invite inquiry throughout the process rather than only at its conclusion.

---

## The Framework

### Formal Framework Documents

| File | Document | Version | Contents |
|------|----------|---------|----------|
| [ZP-A Lattice Algebra](ZP-A_Lattice_Algebra.pdf) | ZP-A | v1.14 | Join-semilattice (L, ∨, ⊥). Axioms A1-A4. Monotonicity. CC-2: ⊥ = {⊥} (Quine atom, ZF + AFA, Forced Metatheoretic Commitment). R3: CC-2 eliminates static-description state for ⊥, given D7 exhaustiveness (ZP-E) as background. |
| [ZP-B pAdic Topology](ZP-B_pAdic_Topology.pdf) | ZP-B | v1.9 | AX-B1. MP-1 (design commitment). T0: p=2 derived given MP-1. Q₂ ultrametric. Clopen balls. Total disconnectedness. Topological irreversibility (C3). |
| [ZP-C Information Theory](ZP-C_Information_Theory.pdf) | ZP-C | v1.17 | P₀. State representations from AX-B1. JSD = 1 bit. Discrete surprisal field. **L-RUN. TQ-IH. T-BUF** (AX-1 derivability pathway complete within ZP-C; closed as T-SNAP in ZP-E). CC-2: c₀ = ⊥ labeled as modeling commitment. RP-2: branching measure labeled as representational commitment. L-INF grounded from two directions: unbounded surprisal (D4, T2) and structural self-containment (ZP-A CC-2, R3). |
| [ZP-D State Layer](ZP-D_State_Layer.pdf) | ZP-D | v1.11 | Hilbert space H = ℂⁿ, foundational minimum n = 2. Transition operator T: Q₂ → H - locally constant, continuous. DP-1. Existence and uniqueness of T. Snap → orthogonal shift. Non-decreasing norms. T5-b: distinct consecutive states produce orthogonal T-images (Lean-verified). |
| [ZP-E Bridge Document](ZP-E_Bridge_Document.pdf) | ZP-E | v3.19 | **DA-1** (instantiation = execution; DP-2 (Execution Distinguishability) - TrackedOutput separates output value from machine state; da1_minimal_path proved axiom-free in Lean). **T-SNAP** (Binary Snap derived from A4). **DA-2** (instantiation succession, directed tree). **DA-3** (perspective-relative cardinality). Remark R-AFA (Foundation ruled out; AFA forced). |
| [ZP-F The Counterexamples](ZP-F_The_Counterexamples.pdf) | ZP-F | v1.4 | Formal negative result: the Binary Snap cannot occur in any linearly ordered field. General case proved for any [Field F] [LinearOrder F] [IsStrictOrderedRing F]; ℝ and ℚ given as canonical instances. Self-contained - no dependencies on other ZP layers. All results Lean-verified. |
| [ZP-G Category Theory](ZP-G_Category_Theory.pdf) | ZP-G | v1.11 | Category C. Initial object. AX-G1, AX-G2. Universal property. R2: connecting note linking initial object structure (T2 + AX-G2) to ZP-A CC-2 (⊥ = {⊥}). T6 (informational singularity). T7 (Categorical Zero Paradox). Note: T6-b and T6-c are not Lean-verified; T6 Part II (undefined domain via AX-G2) is fully Lean-verified. |
| [ZP-H Categorical Bridge](ZP-H_Categorical_Bridge.pdf) | ZP-H | v1.15 | Instantiation maps FA-FD (F_A: full construction via NatSLat; F_B/C/D: concrete Functor terms fc_functor/fd_functor sorry-free in Lean). F_C composition by Q-stability. Singularity reconciliation. T-H3: Snap under all four instantiations. T-SNAP inherited as derived theorem. |
| [ZP-I Inside Zero](ZP-I_Inside_Zero.pdf) | ZP-I | v1.10 | **T-IZ (Inside Zero):** every maximal ascending chain is a Cauchy sequence converging to its own successor null in Q₂. h_strict_from_r1_t3 derives strict valuation growth from ZP-A R1 + T3 via the IsDepthChain modeling commitment. **t_iz_complete** chains all four formal T-IZ steps (Cauchy convergence, DA-2, DA-1 via Kleene, T-SNAP) in a single theorem. OQ-E2 partially closed - ordinal indexing forced by countable binary substrate. |
| [ZP-J Self-Reference](ZP-J_Self_Reference.pdf) | ZP-J | v2.1 | **T-EXEC (Executability of Self-Reference):** Quine atom Q = {Q} is provably ⊥. CC-1 derived (cc1_derived, axiom-free). CC-2 structurally forced. ZFC/AFA orthogonality: v₂(0) = ∞ is the shared contact point; AFA adds interpretive weight, not new computation. DC-free Aczel connection (ZPJ_AczelConn). Full ValuationStructure→AbstractSelfApp→AFAStructure abstraction chain with four concrete instances (ℤ_[2], ℕ∞, OntologicalStates). APG decoration uniqueness proved via strong induction on reachable set cardinality (ZPJ_APG). All theorems Lean-verified sorry-free. |
| [ZP-J AFA Addendum](ZP-J_AFA_Addendum.pdf) | ZP-J AFA Addendum | v1.2 | **Formal presentation of the AFA derivation chain** from ZP-J's extension files. Derives decoration_unique (any two valid decorations of a finite Accessible Pointed Graph agree) from ValuationStructure alone, without importing set-theoretic AFA axioms. Typeclass chain: ValuationStructure → AbstractSelfApp → AFAStructure. Cyclic vertices handled by the iterated valuation argument (val_iterate); acyclic vertices by strong induction on reach cardinality (acyclic_induction_step). All results Lean-verified sorry-free. Reads after ZP-J Self-Reference. |
| [ZP-K Computational Grounding](ZP-K_Computational_Grounding.pdf) | ZP-K | v1.7 | **T-COMP (Computational Grounding):** (1)-(3) equivalent by T-EXEC (Quine atom = ⊥ = join identity); (4) Kleene fixed point via KleeneStructure typeclass. MachinePhase instances: machinePhaseAFA + machinePhaseKleene. **DA-1 closed concretely:** da1_closed_concrete : IsQuineAtom(⊥ : MachinePhase). selfApply_partrec proved via Kleene's second recursion theorem. |
| [ZP-L Incomputability Convergence](ZP-L_Incomputability_Convergence.pdf) | ZP-L | v1.0 | Axiom footprint convergence across ZP-A/B/C/E. Roger fixed-point stability (roger_fixed_point_stability). ε₀ as snap threshold: fundamentalSeq cofinal below ε₀; c1_epsilon_zero_identification establishes the canonical snap map. CNF bridge: towerNONote sequence converges p-adically to 0. Kleene-ordinal bridge: snap occurs exactly at ε₀ in Ordinal space. Canonical snap map: snap_map_mono (order-preserving) + epsilon_zero_snap_canonical (existential minimality) + snap_zp2_correspondence (four-way conjunction). Remark R-L.1: structural alignment with Gentzen's proof-theoretic ordinal. All 24 theorems Lean-verified. |
| [ZP-M Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf) | ZP-M | v1.0 | **snapEmbed** type bridge (MachinePhase → ℤ_[2]): c₀ ↦ 1, c₁ ↦ 0; injective, join-to-multiply morphism. **hfp_from_epsilon_zero**: closes the free hypothesis gap in ZP-L - hfp follows from monotonicity + φ(ε₀) = c₁ alone. **zpm_triangle**: ordinal snap, 2-adic convergence, and type bridge co-proved in one theorem. **both_fixed_points_exist**: Kleene quine and ε₀ = ω^ε₀ co-witnessed in same formal context. Remark R-M.1: DA-1 Path 2 boundary made precise - AIT bridge is framework separation, not missing proof step. All 9 theorems Lean-verified. |

### Formal Verification (Lean 4)

Machine-checked proofs of the formal documents using Lean 4 + Mathlib. Source lives under `ZeroParadox/` in this repository.

| Document | Lean Source | Theorems Verified | Build |
|----------|-------------|-------------------|-------|
| ZP-A Lattice Algebra | [ZPA.lean](ZeroParadox/ZPA.lean) | T1 (partial order), T2 (⊥ minimum), D2 equivalence, T3 (monotonicity), CC-1 (derived in ZP-J) | Clean - April 2026 |
| ZP-F The Counterexamples | [ZPF.lean](ZeroParadox/ZPF.lean) | F-DENSITY, F-NO-MIN, F-SNAP-BLOCKED, F-SNAP-IMPOSSIBLE (general ordered field); R-DENSITY, R-NO-MIN, R-SNAP-BLOCKED, R-SNAP-IMPOSSIBLE (ℝ corollaries) | Clean - May 2026 |
| ZP-B p-Adic Topology | [ZPB.lean](ZeroParadox/ZPB.lean) | AX-B1, T0 (p=2 unique), T1 (ultrametric), C1 (isosceles), T2 (clopen balls), C2 (no path), T3 (clopen gap at 0), T5 (totally disconnected), C3 (Snap irreversible) | Clean - April 2026 |
| ZP-C Information Theory | [ZPC.lean](ZeroParadox/ZPC.lean) | T1 (distinct distributions), T1b (KL/JSD = log 2), D5 (DF antisymmetry), T2 (telescoping + divergent circulation), L-RUN (execution nonzero), TQ-IH, L-INF (unbounded surprisal at ⊥) | Clean - April 2026 |
| ZP-D State Layer | [ZPD.lean](ZeroParadox/ZPD.lean) | DP-1 (orthogonality), T2 (existence of T: injective, orthogonal, norm-preserving), T3 (uniqueness up to unitary equivalence), T4 (Snap → orthogonal shift in H), T5 (non-decreasing norms) | Clean - April 2026 |
| ZP-E Bridge Document | [ZPE.lean](ZeroParadox/ZPE.lean) | MachinePhase ZPSemilattice instance, T-SNAP (join + machine + derived + irreversibility + accessible proper subset), DA-2 (bottom characterization + novelty corollary), DA-3-D1 (accessible cardinality definition), DP-2 (TrackedOutput + da1_minimal_path axiom-free) | Clean - April 2026 |
| ZP-G Category Theory | [ZPG.lean](ZeroParadox/ZPG.lean) | ZPCategory class (AX-G1 + AX-G2), ZPSurprisal class (I-KC / D7'), T1 (initial uniqueness), T2 (universal constituent), T3 (unreachability), T4 (forward-only chains), T6-a/b/c (surprisal), T6 (informational singularity), T7 (Categorical Zero Paradox), ForkCat (concrete ZPCategory instance) | Clean - April 2026 |
| ZP-H Categorical Bridge | [ZPH.lean](ZeroParadox/ZPH.lean) | T-H1 (F_A initial object proved; F_B/F_C/F_D domain facts cited), T-H2 (singularity compatibility: ZPG unreachability ∧ ZPC divergence), T-H3 (Binary Snap under all four functors: join ∧ topological ∧ 1-bit ∧ orthogonal); nnreal_initial_grounding (single shared categorical witness for F_B/C/D) | Clean - April 2026 |
| ZP-I Inside Zero | [ZPI.lean](ZeroParadox/ZPI.lean) | t_iz_norm_tendsto_zero, t_iz_conv_zero, t_iz_cauchy (Cauchy core), t_iz_r1_t3_geometric_bound (R1+T3 → geometric bound), **t_iz_valuation_unbounded** (sup v₂ = ∞), **h_strict_from_r1_t3** (R-IZ-A closed - h_strict derived from IsDepthChain + IsStrictStateSequence, not assumed), nat_strict_of_strict_state_seq, t_iz_limit_is_new_null (axiom-free), c_t_iz_null_balance, t_iz_c3_compatible, **t_iz_complete** (all four T-IZ steps formal: Cauchy + DA-2 + DA-1/Kleene + T-SNAP) | Clean - April 2026 |
| ZP-J Self-Reference (Core) | [ZPJ.lean](ZeroParadox/ZPJ.lean) | T-EXEC (Quine atom = ⊥, axiom-free), J1 (join-identity derived from T-EXEC + A4), cc1_derived (CC-1 as theorem), bot_is_quine_atom, t_exec_iff (full biconditional), bot_unique | Clean - April 2026 |
| ZP-J AFA Derivation Chain | [ZPJ_AczelConn.lean](ZeroParadox/ZPJ_AczelConn.lean), [ZPJ_SelfApp.lean](ZeroParadox/ZPJ_SelfApp.lean), [ZPJ_Scale.lean](ZeroParadox/ZPJ_Scale.lean), [ZPJ_OntBridge.lean](ZeroParadox/ZPJ_OntBridge.lean), [ZPJ_Model.lean](ZeroParadox/ZPJ_Model.lean), [ZPJ_ScaleBridge.lean](ZeroParadox/ZPJ_ScaleBridge.lean) | **AczelConn:** singleton_from_unique_witness (DC-free uniqueness), J_self_eq_singleton_bot (Aczel Thm 6.5 without DC). **SelfApp:** AbstractSelfApp typeclass, toAFAStructure (selfMem/bot_self_mem/quine_unique as theorems), 2-adic parallel (q2_selfMem_singleton). **Scale:** ValuationStructure typeclass, scale_ne_fixed, scale_unique_fp, toAbstractSelfApp, val_selfMem_singleton, ℤ_[2] standalone axiom checks. **OntBridge:** instOntZPS + instOntSelfApp (OntologicalStates → AFA content, no AFA import). **Model:** instNatInfZPS + instNatInfVal (ℕ∞ concrete ValuationStructure instance, natInf_selfMem_singleton). **ScaleBridge:** ValBridge typeclass (ZPSemilattice-free), instZ2ValBridge (ℤ_[2] formal AFA instance), toValBridge unification, z2_selfMem_singleton | Clean - May 2026 |
| ZP-J APG Decoration Uniqueness | [ZPJ_APG.lean](ZeroParadox/ZPJ_APG.lean) | APG structure (Quiver + root + accessibility), DecorationUniverse typeclass (collect + collect_singleton + collect_val_ge), val_iterate (val(scale^k x) = val x + k for x ≠ ⊥), scale_iterate_unique_fp (scale^k x = x → x = ⊥, all k-cycle cases), pureSelfLoop_decoration_eq_bot, cyclic_decoration_eq_bot (val chain via path_val_chain), **decoration_unique** (any two valid decorations of a finite APG are equal - proved by strong induction on reach cardinality, no SCC decomposition) | Clean - May 2026 |
| ZP-K Computational Grounding | [ZPK.lean](ZeroParadox/ZPK.lean) | IsKleeneFixedPoint, selfApply_partrec (Kleene's second recursion theorem - Mathlib fixed_point₂), computational_quine_exists, KleeneStructure typeclass, T-COMP (four-way equivalence), kleene_quine_is_bot, da1_computational, da1_paths_unified, description_instantiation_gap_closed, machinePhaseAFA, machinePhaseKleene, da1_closed_concrete | Clean - April 2026 |
| ZP-L Incomputability Convergence | [ZPL.lean](ZeroParadox/ZPL.lean) | axiom_footprint_convergence, roger_fixed_point_stability, epsilonZero definitions, epsilonZero_tower_lt, tower_converges_to_zero, fundamentalSeq_cofinal, snap_threshold_is_epsilon_zero, c1_epsilon_zero_identification, snap_exactly_at_epsilon_zero, kleene_ordinal_snap_bridge, snap_map_mono, epsilon_zero_snap_canonical, snap_zp2_correspondence (all 24 theorems) | Clean - May 2026 |
| ZP-M Kleene-Ordinal Bridge | [ZPM.lean](ZeroParadox/ZPM.lean) | snapEmbed (MachinePhase → ℤ_[2], canonical type bridge), snapEmbed_injective, snapEmbed_mul_morphism (absorbing-element morphism), hfp_from_epsilon_zero (closes ZPL hfp gap: φ ε₀ = c₁ + monotonicity → all fixed points snap), snap_unconditional, snap_state_zp2_is_zero, zpm_triangle (ordinal snap ∧ 2-adic convergence ∧ type bridge formally co-proved), both_fixed_points_exist (Kleene quine ∧ ε₀ = ω^ε₀ least fixed point in same formal context) | Clean - May 2026 |

**Purity note:** ZP-H, ZP-I, ZP-J (extension files), ZP-K, ZP-L, and ZP-M use `Classical.choice` (via Mathlib computability, analysis, and ordinal infrastructure - Kleene's theorem, Roger's fixed-point theorem, metric space completion, ordinal arithmetic, and p-adic valuation). These are Mathlib infrastructure dependencies, not Zero Paradox commitments. `Classical.choice` in Lean is the kernel axiom that grounds classical excluded middle - it is distinct from the set-theoretic Axiom of Choice (AC) in ZFC and does not introduce non-constructive selection over infinite families of sets. The `#print axioms` check reports `[propext, Classical.choice, Quot.sound]` across ZP-I, ZP-K, ZP-L, ZP-M, and the ZP-J extension files (ZPJ_Scale, ZPJ_Model, ZPJ_APG); the classical axioms enter through Code/Partrec, analysis machinery, ordinal fixed-point theory, and p-adic library infrastructure, not through the ZPSemilattice or AFAStructure fields. The ZP-J core file (ZPJ.lean) and ZPJ_AczelConn, ZPJ_SelfApp, ZPJ_OntBridge are `Classical.choice`-free. ZP-A through ZP-G are `Classical.choice`-free except where standard Mathlib theorems require it. Whether `Classical.choice` is structurally forced by the ZP snap geometry or merely incidental to Mathlib's ordinal implementation is an open question (see Question Register).

---

## Axiomatic Commitments

A commitment marked "not a novel commitment" means its content is formally grounded in prior layers and derivable from results established there. It is stated as a local axiom only for the self-containment of that layer - the same pattern by which AX-1 was stated as an axiom before being formally derived as T-SNAP in ZP-E.

**Metatheoretic note:** This framework is stated over ZF + AFA (Zermelo-Fraenkel with Anti-Foundation Axiom), not standard ZFC. AFA permits self-containing sets (x = {x}). This affects only CC-2 below - the remaining results do not depend on non-well-founded sets. Standard ZFC is incompatible with CC-2: a well-founded ⊥ would admit an external interpreter, contradicting the self-execution argument. The Axiom of Choice is not assumed. The move to AFA is not a free choice - it is forced by the framework's own results: ZP-A R3 and ZP-C L-INF together establish that ⊥ admits no finite external description, which is incompatible with the Foundation axiom's well-foundedness requirement (no infinite descending ∈-chains). The full argument for why AFA specifically is the appropriate extension - rather than simply removing Foundation - is developed in ZP-E Remark R-AFA.

| Label | Type | Statement |
|-------|------|-----------|
| **AX-B1** | Directly Verifiable | A state either exists or it does not. Directly verifiable by computation (OntologicalStates derives DecidableEq; ax_b1_distinct proved by `decide` without classical axioms) - not a novel commitment of this framework. |
| **AX-G1** | Axiom | An initial object exists in the category C. The bottom element ⊥ is the universal origin of all structure: a unique object from which every other object is reachable, and to which no morphism returns. Not a novel commitment - ⊥'s existence as the bottom element of the ZP-A semilattice already guarantees this; ZP-G names it in categorical language. |
| **AX-G2** | Axiom | Source asymmetry: hom(X, 0) = ∅ for X ≠ 0. Once something emerges, it cannot return to nothing. Not a novel commitment - follows from antisymmetry of the ZP-A partial order and is independently confirmed by ZP-B C3 (topological irreversibility). |
| **MP-1** | Principle | The representational base is the minimum sufficient base for AX-B1. Derives p = 2. |
| **RP-1** | Principle | The probabilistic representation of a state in the two-element state space is a point-mass distribution. |
| **DP-1** | Design Commitment | Clopen separation in Q₂ is represented by orthogonality in H. |
| **MC-1** | Modeling Commitment (Substantially Derived) | The bottom elements across all framework layers - algebraic ⊥, the 0 of Q₂, the Turing initial configuration c₀, and the categorical initial object - are identified as a single object. Substantially grounded by independent formal work: each domain locates its bottom element through its own logic prior to identification (ZP-H v1.7); ZP-E typeclass instance enforces ZP-A ⊥ ↔ ZP-C c₀; AX-G1 grounds the categorical initial in ZP-A ⊥; ZP-H T-H3 proves Binary Snap consistency across all four functors. What remains is the interpretive choice to unify the four under one name. |

**AX-1 (Binary Snap Causality) is no longer an axiom.** It is Theorem T-SNAP, derived in ZP-E from A4 - the standard bottom element axiom of join-semilattice theory (∀ x, ⊥ ∨ x = x). AX-1 was redundant: any join-semilattice with bottom already has this property. The snap is not imposed on the algebraic structure - it is a consequence of it.

---

## Question Register

| Item | Status |
|------|--------|
| OQ-A1: Increment selection | Closed - ZP-E T5 (Iterative Forcing Theorem) |
| OQ-B1: p = 2 justification | Closed - ZP-B T0 (derived from AX-B1 + MP-1) |
| S1: Distribution stipulation | Closed - ZP-C T1 (derived from AX-B1 + RP-1) |
| OQ-C1: Non-conservatism of DF | Closed - ZP-C T2 (rebuilt within extended D6) |
| DA-1: Instantiation alignment | **Closed - ZP-E / ZP-K** - DA-1 formally grounded in DP-2 (Execution Distinguishability); da1_minimal_path proved axiom-free in Lean. Paths 1 and 3 closed via da1_closed_concrete (ZP-K). Path 2 (AIT bridge between ZP-C and computability) is an open foundational question, explicitly flagged as such - the framework locates the boundary but does not close it. |
| CC-1 (S₀ = ⊥) derivability | **Closed - ZP-J cc1_derived (axiom-free, Lean)** - was ZP-A Conditional Claim; now derived via ZP-J T-EXEC in any AFAStructure lattice; ZP-A v1.11 declaration and preface added for clarity |
| CC-2 (⊥ = {⊥}) as commitment | **Closed - ZP-J T-EXEC** - ⊥ = {⊥} is structurally forced by self-execution argument; not a freestanding modelling choice |
| AX-1: Binary Snap Causality | **Closed - ZP-E T-SNAP (derived theorem)** |
| OQ-E1: Sequence vs. tree structure | Closed - ZP-E DA-2 (directed instantiation tree; branching mandatory via T-SNAP) |
| DA-2: Instantiation succession | Closed - ZP-E DA-2 (terminal state of I_n satisfies ⊥ role for I_n+1; C-DA2 derives that each instantiation produces a provably distinct ⊥) |
| DA-3: Perspective-relative cardinality | Closed (definitional) / Candidate (DA-3-C1) - ZP-E DA-3 (definitional closure via D7 exhaustiveness; formal cardinality derivation deferred to OQ-E2) |
| OQ-E2: Cardinality-semilattice correspondence | **Partially closed - ZP-I T-IZ** - ordinal indexing Omega = omega forced by countable binary substrate (ZP-C D4, Q2 separability, binary alphabet). Internal/external perspective relativity is ordinal, not set-theoretically free. Formal connection between specific semilattice structures and specific CH instances remains open. |
| OQ-G1: Native categorical surprisal | Closed - ZP-G D7' and I-KC (Kolmogorov import; BA-G1 demoted to compatibility remark R-BA) |
| OQ-G2: Left adjoint verification | Closed - ZP-H T-H1 (initial-object universal property verified for all four domain instantiations: F_A via NatSLat; F_B/C/D via ℝ≥0 proxy witness) |
| OQ-G3: Functor construction | Closed (concrete witness) / Open (full construction) - F_A: strong closure via NatSLat appendix (ℕ with max/0 as ZPCategory; 0 is categorical initial; genuine ZPA connection). F_B/C/D: shared ℝ≥0 proxy witness (NNRealZPCat appendix); domain facts C3, T1b, T4 cited. Full abstract Lean Functor terms to pTop/InfoSp/Hilb as CategoryTheory categories remain future work. |
| OQ-G4: Singularity reconciliation | Closed - ZP-H T-H2 (categorical and ZP-C characterizations shown to be same obstruction) |
| ε₀ / proof-theoretic ordinal | **Partially closed - ZP-L May 2026.** c1_epsilon_zero_identification establishes the canonical snap map (MachinePhase → Ordinal) with ε₀ as the exact transition point. snap_zp2_correspondence proves the four-way conjunction (ordinal bound, phase assignment, p-adic convergence, snap assignment). Structural alignment with Gentzen's proof-theoretic ordinal (PA consistency) documented in ZP-L Remark R-L.1. Full type-theoretic identity across type universes (MachinePhase vs. Ordinal) is outside Lean scope and deferred pending OQ-E2. |
| Temperature T in BA-1 | Parameter - intentional; universe-contingent |
| T-IZ: Inside Zero Theorem | **Fully derived - Lean, April 2026** - every maximal ascending chain converges to its own successor null. R-IZ-A closed: h_strict_from_r1_t3 derives v2(S(n)) strictly increasing from IsDepthChain + IsStrictStateSequence (ZP-A lattice axioms) - no longer a construction-level hypothesis. t_iz_complete formally chains all four T-IZ steps: Cauchy convergence (t_iz_cauchy), DA-2 successor null identification (t_iz_limit_is_new_null), DA-1 via AFA/Kleene (da1_computational, ZP-K), T-SNAP (bot_join). Kolmogorov complexity bridge superseded. |
| Null balance | **Closed - T-IZ + DA-2** - exact and derived: every branch starts at ⊥, ascends omega state changes (T3), generates a successor ⊥ at the ordinal limit (T-IZ + T-SNAP + DA-2). |
| Formal verification (Lean/Rocq) | ZP-A through ZP-M verified; ZP-M adds snapEmbed type bridge (MachinePhase → ℤ_[2]), hfp closure, zpm_triangle (ordinal-2adic-phase triangle), both_fixed_points_exist (Kleene-ordinal structural homology) - May 2026 |
| Classical.choice necessity | **Open** - ZP-L and ZP-M inherit Classical.choice via Mathlib ordinal and analysis infrastructure. Whether the dependency is structurally forced by ZP snap geometry or incidental to Mathlib's implementation is an open question. Testable via constructive ordinal fixed-point theory over ONote/NONote (Lean 4 CNF notation). Future ZP-N (constructive validation layer). |

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
