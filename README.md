# The Zero Paradox
**April 2026**

*A Lean 4 formalization: one diagonal fixed point at the bottom of five mathematical fields - the snap off it a theorem, the recurrence machine-verified, the boundary proved.*

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

Followed a link that broke after the v3.0 source reorganization? The old→new file and declaration map is in [`ssot.json`](ssot.json); report anything we missed in the [v3.0 reorg link-integrity thread](https://github.com/timbrigham/ZeroParadox/discussions/120).

---

**The same family of objects sits at the bottom of every framework it touches.** In order theory, p-adic valuation, category theory, computability, and set theory, each domain's bottom element ⊥ is the same *kind* of thing: a diagonal fixed point - the point that is its own image under the domain's self-map. This project machine-verifies that recurrence and proves exactly how far it reaches.

That the classical self-reference arguments (Cantor, Russell, Gödel, Kleene) share one diagonal fixed point is **Lawvere's (1969)**. What this framework adds is checkable and specific:

- **It is located at the floor, not the ceiling** - the Gödel inversion. The concrete instance, the **Binary Snap** (the forced exit ⊥ → ε₀), is a theorem, not an axiom; its core snap is even Lean-kernel-axiom-free (not even choice - choice enters only at the separate identification of the ceiling with the ordinal ε₀).
- **The recurrence is verified across *heterogeneous* domains** - the computability face is a genuine Lawvere/Kleene fixed point; the lattice and 2-adic faces are proved fixed points of their own self-maps ([`q2_unique_fp`](ZeroParadox/Computability/SelfApp.lean), [`scale_unique_fp`](ZeroParadox/Valuation/Scale.lean)), carrying the shape but not genuine Lawvere instances - Cantor forbids the Set-level witness.
- **The boundary is proved, not assumed** - there is no single cross-category theorem folding the domains into one object (`x = y` across distinct categories is not a well-formed proposition); a Cantor/Lawvere obstruction establishes the impossibility. The framework proves where the shape recurs, and where it stops.

## Where to Start

- **Mathematician or reviewer** - the formal index is below: [Lean verification](#formal-verification-lean-4), the [document table](#formal-framework-documents), and the [reading order by specialty](#reading-order-by-specialty). Claim-by-claim status, with Lean witnesses and exact axiom profiles, is in the [Claims Ledger](CLAIMS.md).
- **General reader** - [Guide](GUIDE.md): plain language, illustrated companions, and reading paths for every audience.
- **Just want the object** - [The Bottom Element (⊥)](BOTTOMELEMENT.md) and [The Binary Snap (⊥ → ε₀)](SNAP.md): dictionaries and maps of ⊥ and the transition off it, most characterizations carrying a machine-checked Lean witness.
- **See it** - [The Bottom Family](bottom-family-tree.html): an interactive map of ⊥ across the fields - hover any node for why it sits where it does, with the Lean witness to check.

---

## The Result

The forced transition ⊥ → ε₀ - the **Binary Snap**, this project's shorthand - is a **theorem, not an axiom**. The existence of a minimum non-⊥ state is the **atom** above ⊥ - what the framework calls the *first atomic state* - and it does **not** follow from A4 alone: a bounded join-semilattice can be dense and atom-free (ℝ≥0 under `max` is one), and the framework proves the snap fails exactly there ([`f_snap_impossible`](ZeroParadox/Reals/OrderedField.lean)). What supplies the atom is the framework's discrete state model - the ontological states are atomic, not a continuum (AX-B1) - with A4 (∀ x, ⊥ ∨ x = x) giving only the join structure of the transition. The assembly is machine-verified in Lean 4 (`t_snap_derived`). The framework adds no *snap-specific* axiom (the redundant AX-1 was retired), and `t_snap_derived` - the snap from ⊥ to the first atomic state - depends on **no Lean kernel axioms at all**: not the Axiom of Choice, not even propositional extensionality (the discreteness is carried by the finite state type and checked constructively, not invoked as a classical axiom). Identifying that ceiling with the *proof-theoretic ordinal* ε₀ is a separate step, and that is where `Classical.choice` enters - as it does wherever the framework builds on Mathlib's classically-built analysis, order, and computability libraries (p-adic topology, Hilbert space, ordinals, category theory), never in the core snap itself. The honest contrast, showing exactly where choice appears, is a checkable artifact: [AxiomProfile.lean](ZeroParadox/AxiomProfile.lean).

**Every part of the transition is forced - its occurrence, its destination, and its form - each by a mechanism with its own requirement and its own Lean witness:**

- **Information** - ⊥ is the *degenerate* distribution (a point mass, zero information); a non-degenerate state provably needs at least two outcomes, so the minimal non-⊥ structure is binary, with no "half state." *Requires:* states are probability distributions. *Witnesses:* [`pmf_subsingleton_isPure`](ZeroParadox/Information/Surprisal.lean) (fewer than two outcomes forces the point mass), [`binaryState_exhaustive`](ZeroParadox/Information/Surprisal.lean) (no third state, axiom-free); the two point masses are exactly 1 bit apart ([`t1b_jsd`](ZeroParadox/Information/Surprisal.lean)).
- **Order** - given two distinct states, the transition ⊥ → first atomic state is a join. *Requires:* the bottom-element axiom A4. *Witness:* [`t_snap_derived`](ZeroParadox/Order/Snap.lean).
- **Self-execution** - nothing external can execute ⊥, so ⊥ must execute itself, and execution is a non-null state change. *Requires:* ⊥ admits no external interpreter. *Witness:* [`da1_closed_concrete`](ZeroParadox/Computability/Kleene.lean) (⊥ is a Quine atom).
- **Incompressibility** - ⊥ has no finite description: its surprisal is unbounded. *Requires:* the information measure. *Witness:* [`l_inf`](ZeroParadox/Information/Surprisal.lean). This is what grounds self-execution - a descriptionless ⊥ cannot be held by any external interpreter.

These force *different aspects*, not the same proposition four times: incompressibility grounds self-execution, so the snap must **occur**; the information mechanism fixes its **destination** as the minimal binary state; and A4 gives it a **join** form. Together they leave no part of ⊥ → first-atomic-state unforced. The single substantive commitment underneath is that states are **discrete** - a state exists or it does not, a distribution over atomic outcomes, not a continuum - which is exactly what the reals lack, and why the snap provably fails there ([`f_snap_impossible`](ZeroParadox/Reals/OrderedField.lean)).

The bottoms across the layers form one characterized **family** (MC-1): per-domain membership is proved (the categorical criterion is [`mc1_correspondence`](ZeroParadox/Multihomed/MC1Bridge.lean)), while the reading that they are numerically *one object* is retired as ill-typed - the members are provably distinct (the walls). ε₀ is chosen as the proof-theoretic ordinal of PA (Gentzen 1936) - a cited classical fact the framework invokes, not one it re-proves; its role as the exact snap threshold is machine-verified, and the one open residue is the type-level identity across universes (OQ-E2), not the Gentzen relationship itself. The full labelled account is in [Axiomatic Commitments](#axiomatic-commitments).

The snap is also **irreversible**: the p-adic topology layer (ZP-B) establishes, Lean-verified, that there is no continuous path from any nonzero state back to ⊥ - the total disconnectedness of Q₂ makes any return path discontinuous.

**Scope of the claim.** The internal coherence is formally established - the central theorem and the supporting layer theorems are verified in Lean 4 given the explicitly stated commitments. Whether those commitments are the right ones, and whether the formalism faithfully tracks the structural notion of zero it sets out to model, are questions Lean cannot answer from inside; they are what this repository invites external review on. The framework has been developed in public from the start for exactly this reason.

<details markdown="1">
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

Machine-checked proofs of the formal documents using Lean 4 + Mathlib, with source under `ZeroParadox/` in this repository. Every push and pull request to `main` is re-verified from scratch by [a continuous-integration build that runs the full `lake build`](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml), so the published state is always one that compiles. An **axiom-profile artifact**, [AxiomProfile.lean](ZeroParadox/AxiomProfile.lean), collects the axiom dependencies of the core results in one place: the central theorem T-SNAP depends on no axioms, the choice-free core (lattice, Quine-atom self-reference) is listed, and an honest contrast shows where `Classical.choice` enters (the analytic realizations). The full claim-by-claim status - every result with its Lean witness and exact axiom footprint, the by-document verification table, and the per-file axiom profile - is in the **[Claims Ledger](CLAIMS.md)**.

**Browse the source tree:** the full Lean sources are navigable on GitHub at [`ZeroParadox/`](https://github.com/timbrigham/ZeroParadox/tree/main/ZeroParadox) (GitHub renders each file with syntax highlighting and provides the directory listing); individual files also resolve directly under `ZeroParadox/` on this site.

### Reproducing the Verification

An independent re-check is three commands: `git clone https://github.com/timbrigham/ZeroParadox && cd ZeroParadox && lake build`. `elan` reads the pinned compiler from [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.30.0-rc2`) automatically, and Mathlib is fetched as a pinned dependency via `lake-manifest.json`; a clean `lake build` means every theorem in `ZeroParadox/` type-checks against the Lean kernel. To inspect the core axiom profile directly: `lake env lean ZeroParadox/AxiomProfile.lean`.

### Formal Framework Documents

| File | Document | Version | Focus |
|------|----------|---------|-------|
| [Lattice Algebra](ZP-A_Lattice_Algebra.pdf) | ZP-A | v1.19 | The lattice-algebra foundation: the bottom element ⊥ and the order it induces. |
| [p-adic Topology](ZP-B_pAdic_Topology.pdf) | ZP-B | v1.11 | The 2-adic topology: why p = 2, and why departure from ⊥ is irreversible. |
| [Information Theory](ZP-C_Information_Theory.pdf) | ZP-C | v1.20 | The information layer: state distributions, 1-bit cost, unbounded surprisal at ⊥. |
| [State Layer](ZP-D_State_Layer.pdf) | ZP-D | v1.15 | The Hilbert-space layer: the snap as an orthogonal shift between states. |
| [Bridge Document](ZP-E_Bridge_Document.pdf) | ZP-E | v3.23 | The bridge: the snap assembled as a derived theorem across the layers. |
| [The Counterexamples](ZP-F_The_Counterexamples.pdf) | ZP-F | v1.5 | The counterexamples: ordered fields (ℝ, ℚ) where the snap cannot occur. |
| [Category Theory](ZP-G_Category_Theory.pdf) | ZP-G | v1.15 | The categorical layer: ⊥ as initial object, the informational singularity. |
| [Categorical Bridge](ZP-H_Categorical_Bridge.pdf) | ZP-H | v1.17 | The categorical bridge: the snap holding under all four domain functors. |
| [Native Categories Addendum](ZP-H_Native_Categories_Addendum.pdf) | ZP-H Native Categories Addendum | v1.2 | The snap floor realized inside each framework's native Mathlib category (TopCat, ModuleCat ℂ, KleisliCat PMF). Reads after ZP-H. |
| [Inside Zero](ZP-I_Inside_Zero.pdf) | ZP-I | v1.13 | Inside zero: each maximal chain converging to its own successor ⊥. |
| [Self-Reference](ZP-J_Self_Reference.pdf) | ZP-J | v2.5 | Self-reference: ⊥ as the Quine atom, and the AFA structure it requires. |
| [AFA Addendum](ZP-J_AFA_Addendum.pdf) | ZP-J AFA Addendum | v1.6 | Decoration uniqueness for finite graphs from the valuation structure alone. Reads after ZP-J. |
| [Wheel Addendum](ZP-J_Wheel_Addendum.pdf) | ZP-J Wheel Addendum | v1.3 | The wheel of fractions as a wheel: division by zero made total. Reads after ZP-J. |
| [Keystone Addendum](ZP-J_Keystone_Addendum.pdf) | ZP-J Keystone Addendum | v1.2 | The diagonal-fixed-point keystone: the Lawvere face-split (machine-checked) and the snap as a well-foundedness boundary crossing. Reads after ZP-J. |
| [Computational Grounding](ZP-K_Computational_Grounding.pdf) | ZP-K | v1.9 | Computational grounding: the snap as a Kleene fixed point. |
| [Incomputability Convergence](ZP-L_Incomputability_Convergence.pdf) | ZP-L | v1.3 | ε₀ as the exact ordinal threshold where the snap occurs. |
| [Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf) | ZP-M | v1.3 | The bridge between the Kleene quine and the ε₀ fixed point. |
| [The Constructive Snap](ZP-N_The_Constructive_Snap.pdf) | ZP-N | v1.0 | The choice-free constructive companion to ZP-L: the ε₀ snap from below on ordinal notations. The three snap results are choice-free (propext only); ZP-L's Classical.choice at ε₀ is representational, not intrinsic. |
| [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) | ZP-P | v1.5 | Synthesis layer: the least-vs-greatest fixed-point fork, generalizing the Foundation/AFA orthogonal-contact-point claim across frameworks. |
| [The Frame-Change](ZP-Q_The_Frame_Change.pdf) | ZP-Q | v1.0 | Synthesis layer (ZP-P sequel): ⊥ → ε₀ as a change of point of view. The order-theoretic frame-flip universal is proved; the categorical Lawvere universal meets a proven Cantor wall; the cross-domain identity is a type boundary. |
| [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf) | Choice-Free Core | v1.3 | Framework-wide note: the central results are choice-free (T-SNAP is axiom-free); Classical.choice appears only in the analytic realizations, inherited from Mathlib. Anchored on AxiomProfile.lean. |

### Reading Order (by Specialty)

The framework is not a line. Several fields each reach a bottom, and those bottoms all play the same structural role, the diagonal fixed point ⊥; the documents above are the spokes into it. Start at the hub, then follow your own field. A document that appears in more than one field's route is a bridge, and the overlap is the point: the fields' bottoms share one structural shape. Whether they are literally one object is a type boundary, not a theorem (see [The Frame-Change](ZP-Q_The_Frame_Change.pdf)).

**Start here (the hub, for everyone):** two companion maps - [The Bottom Element (⊥)](BOTTOMELEMENT.md), the map of the object ⊥, and [The Binary Snap (⊥ → ε₀)](SNAP.md), the map of the transition off it - each with what is proved versus open → [Bridge Document](ZP-E_Bridge_Document.pdf), the snap assembled as a derived theorem → [The Frame-Change](ZP-Q_The_Frame_Change.pdf), the snap read as a change of point of view and why every field's bottom plays the same structural role. Keep the [Claims Ledger](CLAIMS.md) beside you for proved-versus-conjectural status.

**Then follow your field:**

- **Number theory and valuation (p-adic):** [p-adic Topology](ZP-B_pAdic_Topology.pdf) → [The Counterexamples](ZP-F_The_Counterexamples.pdf) → [The Frame-Change](ZP-Q_The_Frame_Change.pdf) (the p-adic Riemann sphere)
- **Proof theory and ordinals:** [Incomputability Convergence](ZP-L_Incomputability_Convergence.pdf) → [Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf) → [The Constructive Snap](ZP-N_The_Constructive_Snap.pdf)
- **Computability and recursion:** [Computational Grounding](ZP-K_Computational_Grounding.pdf) → [Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf)
- **Set theory and foundations (AFA):** [Self-Reference](ZP-J_Self_Reference.pdf), with the [AFA](ZP-J_AFA_Addendum.pdf) and [Keystone](ZP-J_Keystone_Addendum.pdf) addenda → [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf)
- **Category theory:** [Category Theory](ZP-G_Category_Theory.pdf) → [Categorical Bridge](ZP-H_Categorical_Bridge.pdf), with the [Native Categories](ZP-H_Native_Categories_Addendum.pdf) addendum → [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) and [The Frame-Change](ZP-Q_The_Frame_Change.pdf)
- **Order, lattice, and state:** [Lattice Algebra](ZP-A_Lattice_Algebra.pdf) → [Inside Zero](ZP-I_Inside_Zero.pdf), then the state layers [Information Theory](ZP-C_Information_Theory.pdf) and [State Layer](ZP-D_State_Layer.pdf)

Each spoke is the same three beats: your field, then the bridge that carries it out, then back to ⊥. Read your own layers, then the synthesis layer they feed ([The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) or [The Frame-Change](ZP-Q_The_Frame_Change.pdf)), then the hub, and you will see your field's bottom is doing the same structural work as every other field's.

**The spine (the argument itself, no field assumed):** [The Bottom Element (⊥)](BOTTOMELEMENT.md) → [Bridge Document](ZP-E_Bridge_Document.pdf) → [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) → [The Frame-Change](ZP-Q_The_Frame_Change.pdf). This is the through-line, and it replaces the old single linear reading order, which tried to send every reader through all of the documents in one sequence.

**Orientation and general readers:** [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf) records the axiom profile; the [Foreword](Zero_Paradox_Foreword.pdf) and [The Philosophical Question](ZP_Philosophical_Question.pdf) give context; plain-language companions and a general-reader path are in [Guide](GUIDE.md). The [Wheel Addendum](ZP-J_Wheel_Addendum.pdf) (division by zero made total) is a self-contained aside off the set-theory route.

---

## Axiomatic Commitments

This framework adds no axioms specific to the result: the central theorem follows from the standard bottom-element axiom of join-semilattice theory alone, and **AX-1 (Binary Snap Causality) is no longer an axiom** - it is Theorem T-SNAP, derived in ZP-E. The remaining commitments are either directly verifiable by computation or restatements of structure established in earlier layers.

The framework is stated over ZF + AFA (not ZFC), but the commitment is not the *adoption of AFA specifically*: it is a set of requirements on the host theory - that the bottom is a self-containing Quine atom (⊥ = {⊥}), and that this atom is unique - of which AFA is the canonical example. Those requirements are a checkable object, the `QuineHost` typeclass (`ZeroParadox/Settheory/QuineHost.lean`): Foundation-freeness is *forced* by the Quine atom (`quineHost_not_wellFounded`); ZFC + Foundation is excluded in-kernel about Mathlib's real `ZFSet` (`zfSet_no_quine_bottom`); Boffa's permissiveness - it admits a proper class of Quine atoms, not one - is what fails (Z), witnessed by a toy model (`boffa_fails_unique`) rather than an in-kernel fact about that theory; and AFA satisfies all three (`afaStructure_isQuineHost`). Only "these are the right requirements to demand" remains argued (and where AFA-specific results are used elsewhere, they are proved separately, not assumed from full AFA); the discipline every such claim must meet is defined in [Forced Metatheoretic Commitment](fmc.md). The bottoms across the layers form one **family** (MC-1): per-domain membership is proved (its correspondence half is `mc1_correspondence`), and the reading that they are numerically *one object* is retired as ill-typed.

The full labelled account - the supporting commitments (AX-B1, AX-G1, AX-G2, MP-1, RP-1, DP-1), the metatheoretic stance and the host-theory requirements (where AFA fits), and the bottom-family (MC-1) account in full - is in the **[Claims Ledger](CLAIMS.md)** (Tiers 4-5).

---

## Question Register

The framework's open questions, design commitments, and resolved questions are tracked in the **[Claims Ledger](CLAIMS.md)** - Tier 6 (open: the `Classical.choice` necessity question, OQ-E2, the Lawvere conjecture), Tier 5 (chosen commitments), and the Resolved-questions list.

**Verification status:** ZP-A through ZP-N, ZP-P, and ZP-Q, plus the ZP-H native-category functors and `mc1_correspondence`, are machine-verified in Lean 4. A second-prover cross-check (e.g. Rocq) is not yet done.

Open questions are discussed publicly in the [GitHub Discussions Open Questions category](https://github.com/timbrigham/ZeroParadox/discussions/categories/open-questions).

---

## Version History

Hosted at [timbrigham/ZeroParadox](https://github.com/timbrigham/ZeroParadox). Previous document versions are preserved in the repository's git history and in each release's Zenodo/DOI snapshot. See [Guide](GUIDE.md) for development notes and process documentation.

---

## License

All conceptual development, structure, and authorship originate with the human creator.

This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License (CC BY-NC-ND 4.0).

You may share the work with attribution, but you may not modify it or use it commercially. See [License](LICENSE) for full details.

---

## Citation

If referencing this work, please cite:

> Brigham, Timothy. The Zero Paradox (April 2026). https://github.com/timbrigham/ZeroParadox

---

## Contact

For inquiries, discussion, or collaboration, reach out by email at [timbrigham@zeroparadox.org](mailto:timbrigham@zeroparadox.org) or open an issue on [GitHub](https://github.com/timbrigham/ZeroParadox).
