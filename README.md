# The Zero Paradox

*A Lean 4 formalization: one diagonal fixed point at the bottom of five mathematical fields - the snap off it a theorem, the recurrence machine-verified, the boundary proved.*

[![Minimal Core](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/minimal_core.yml) [![Complete Project](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml) [![Sponsor](https://img.shields.io/badge/Sponsor-%E2%9D%A4-ff69b4?logo=githubsponsors&logoColor=white)](https://github.com/sponsors/timbrigham) [![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20060860.svg)](https://doi.org/10.5281/zenodo.20060860)

---

## Where to Start

- **Start here (the shortest path)** - [The Minimal Core](MINIMAL_CORE.md): the whole shape the framework is built on - engine, wall, floor, the snap in both directions, the fan-out - in one self-contained Lean file, on the smallest objects that can carry it, checkable in one command. The compact front door for either a mathematician or a general reader.
- **General reader** - [Guide](GUIDE.md): plain language, illustrated companions, and reading paths for every audience.
- **Mathematician or reviewer** - the formal index is below: [Lean verification](#formal-verification-lean-4), the [document table](#formal-framework-documents), and the [reading order by specialty](#reading-order-by-specialty). Claim-by-claim status, with Lean witnesses and exact axiom profiles, is in the [Claims Ledger](CLAIMS.md).
- **Just want the object** - [The Bottom Element (⊥)](BOTTOMELEMENT.md) and [The Binary Snap (⊥ → ε₀)](SNAP.md): dictionaries and maps of ⊥ and the transition off it, most characterizations carrying a machine-checked Lean witness.
- **See it** - three interactive maps: [The Bottom Family](bottom-family-tree.html) (⊥ across the fields), [The Diagonal Family](diagonal-family.html) (the self-reference arguments as one fixed point, forked into walls and floors), and [The Snap Loop](snap-loop.html) (the ⊥ → ε₀ snap-arc as one 2-adic loop through 0) - hover any node for why it lands where it does, with the Lean witness to check.

---

**The same family of objects sits at the bottom of every framework it touches.** In order theory, p-adic valuation, category theory, computability, and set theory, each domain's bottom element ⊥ is the same *kind* of thing: a diagonal fixed point - the point that is its own image under the domain's self-map. This project machine-verifies that recurrence and proves exactly how far it reaches.

That the classical self-reference arguments share one diagonal fixed point is prior art, not this framework's: **Lawvere (1969)** for Cantor, Russell, Gödel and Tarski, **Yanofsky (2003)** for Turing and the recursion theorem. What this framework adds is checkable and specific:

- **It is located at the floor, not the ceiling** - the Gödel inversion. The concrete instance, the **Binary Snap** (⊥ → ε₀), is a theorem, not an axiom; the core snap `t_snap_derived` is Lean-kernel-axiom-free - not even choice. Choice enters elsewhere in the framework, including at the separate identification of that first step with the ordinal ε₀; see The Result below for where.
- **The recurrence is verified across *heterogeneous* domains** - the computability face is a genuine Lawvere/Kleene fixed point; the lattice and 2-adic faces are proved fixed points of their own self-maps ([`q2_unique_fp`](ZeroParadox/Computability/SelfApp.lean), [`scale_unique_fp`](ZeroParadox/Valuation/Scale.lean)), carrying the shape but not genuine Lawvere instances - Cantor forbids the Set-level witness.
- **The boundary is proved, not assumed** - there is no single cross-category theorem folding the domains into one object (`x = y` across distinct categories is not a well-formed proposition); a Cantor/Lawvere obstruction establishes the impossibility. The framework proves where the shape recurs, and where it stops.

---

## The Result

The transition ⊥ → ε₀ - the **Binary Snap**, this project's shorthand - is a **theorem, not an axiom**. The existence of a minimum non-⊥ state is the **atom** above ⊥ - what the framework calls the *first atomic state* - and it does **not** follow from A4 alone: a bounded join-semilattice can be dense and atom-free (ℝ≥0 under `max` is one), and the framework proves the snap fails exactly there ([`f_snap_impossible`](ZeroParadox/Reals/OrderedField.lean)). What supplies the atom is the framework's discrete state model - the states are atomic, not a continuum (AX-B1) - with A4 (∀ x, ⊥ ∨ x = x) giving only the join structure of the transition. The assembly is machine-verified in Lean 4 (`t_snap_derived`). The framework adds no *snap-specific* axiom (the redundant AX-1 was retired), and `t_snap_derived` - the snap from ⊥ to the first atomic state - depends on **no Lean kernel axioms at all**: not the Axiom of Choice, not even propositional extensionality (the discreteness is carried by the finite state type and checked constructively, not invoked as a classical axiom). Identifying that first step with the *proof-theoretic ordinal* ε₀ is a separate step, and that is where `Classical.choice` enters - as it does wherever the framework builds on Mathlib's classically-built analysis, order, and computability libraries (p-adic topology, Hilbert space, ordinals), never in the core snap itself. The category-theory face is the exception worth naming: its choice is the framework's own (a bare `classical` in [`Lawvere.lean`](ZeroParadox/Category/Lawvere.lean)), and it is *essential* rather than incidental - a separate axis from where the choice comes from - `wem_of_fixedPointFree` reduces the general fixed-point-free principle to weak excluded middle, so no choice-free re-proof exists. The honest contrast, showing exactly where choice appears, is a checkable artifact: [AxiomProfile.lean](ZeroParadox/AxiomProfile.lean).

**The transition's destination and form are forced - each by a mechanism with its own requirement and its own Lean witness. That it OCCURS is a framework commitment, not a derivation (see the closing note below):**

- **Information** - ⊥ is the *degenerate* distribution (a point mass, zero information); a non-degenerate state provably needs at least two outcomes, so the minimal non-⊥ structure is binary, with no "half state." *Requires:* states are probability distributions. *Witnesses:* [`pmf_subsingleton_isPure`](ZeroParadox/Information/Surprisal.lean) (fewer than two outcomes forces the point mass), [`binaryState_exhaustive`](ZeroParadox/Information/Surprisal.lean) (no third state, axiom-free); the two point masses are exactly 1 bit apart ([`t1b_jsd`](ZeroParadox/Information/Surprisal.lean)).
- **Order** - given two distinct states, the transition ⊥ → first atomic state is a join. *Requires:* the bottom-element axiom A4. *Witness:* [`t_snap_derived`](ZeroParadox/Order/Snap.lean).
- **Self-execution** - nothing external can execute ⊥, so ⊥ must execute itself, and execution is a non-null state change. *Requires:* ⊥ admits no external interpreter, and the step from that to *forced execution*, which is a framework commitment rather than a consequence. *Witness (structural half only):* [`da1_closed_concrete`](ZeroParadox/Computability/Kleene.lean) proves `IsQuineAtom (bot : MachinePhase)` - it mentions no code and no execution.
- **Incompressibility** - ⊥ has no finite description: its surprisal is unbounded. *Requires:* the information measure. *Witness:* [`l_inf`](ZeroParadox/Information/Surprisal.lean). This is what motivates the self-execution reading - a descriptionless ⊥ cannot be held by any external interpreter - and `l_inf`'s own scope note states that the step from unbounded surprisal to forced execution is an ontological bridge, not a mathematical consequence.

These force *different aspects*, not the same proposition four times: incompressibility is what motivates the self-execution reading, and the framework commits that the snap must **occur** (that step is a commitment, not a consequence - see the bullet above); the information mechanism fixes its **destination** as the minimal binary state; and A4 gives it a **join** form. Together they constrain every aspect of ⊥ → first-atomic-state except that it fires, which is committed rather than derived. The single substantive commitment underneath is that states are **discrete** - a state exists or it does not, a distribution over atomic outcomes, not a continuum - which is exactly what the reals lack, and why the snap provably fails there ([`f_snap_impossible`](ZeroParadox/Reals/OrderedField.lean)).

The bottoms across the layers form one characterized **family** (MC-1): per-domain membership is proved (the categorical criterion is [`mc1_correspondence`](ZeroParadox/Multihomed/MC1Bridge.lean)), while the reading that they are numerically *one object* is retired as ill-typed - the members are provably distinct (the walls). ε₀ is chosen as the proof-theoretic ordinal of PA (Gentzen 1936) - a cited classical fact the framework invokes, not one it re-proves; its role as the exact snap threshold is machine-verified, and the one open residue is the type-level identity across universes (OQ-E2), not the Gentzen relationship itself. The full labelled account is in [Axiomatic Commitments](#axiomatic-commitments).

The snap is also **irreversible**: the p-adic topology layer (ZP-B) establishes, Lean-verified, that there is no continuous path from any nonzero state back to ⊥ - the total disconnectedness of Q₂ makes any return path discontinuous. This is a claim about the carrier rather than about the snap alone - it holds in Q₂ and fails in ℝ, which is connected (`Statement:` CARRIER, this project's label for a property that holds in one carrier and fails in another).

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

**The checks on the prose are published too.** Beyond the Lean build, this repository gates its own writing: a set of deterministic checkers in [`tools/verify/`](https://github.com/timbrigham/ZeroParadox/tree/main/tools/verify) refuses a commit or a push that adds an unmeasured modal claim, an undated artifact count, a point-of-view claim with no declared kind, a requirements class with no degeneracy verdict, or a prose block over its cap. `python tools/verify/ci_report.py` runs the suite and prints what passed, what is grandfathered debt, and what was skipped. ⚠ The checkers gate a commit and a push through git hooks, which git cannot version-control - a fresh clone has none until `python tools/verify/install_hooks.py` installs them, and `--check` reports whether they are armed. The review briefs the human-judgement gates are run from are in [`.claude/commands/`](https://github.com/timbrigham/ZeroParadox/tree/main/.claude/commands). ⚠ Those briefs are readable but **not runnable from a clone**: they reference a private working folder (`.claude-local/`) holding session notes, correspondence and the defect ledger, and four of them hand you commands that live there. The method is public; some of the material it operates on is not, and that is stated here rather than left to be discovered. Neither is needed to build the Lean sources or the documents - they are published so the "check it yourself" claim covers the writing as well as the mathematics.

### Reproducing the Verification

An independent re-check is three commands: `git clone https://github.com/timbrigham/ZeroParadox && cd ZeroParadox && lake build`. `elan` reads the pinned compiler from [lean-toolchain](lean-toolchain) (`leanprover/lean4:v4.30.0-rc2`) automatically, and Mathlib is fetched as a pinned dependency via `lake-manifest.json`; a clean `lake build` means every theorem in `ZeroParadox/` type-checks against the Lean kernel. To inspect the core axiom profile directly: `lake env lean ZeroParadox/AxiomProfile.lean`.

### Formal Framework Documents

| File | Document | Version | Focus |
|------|----------|---------|-------|
| [Lattice Algebra](ZP-A_Lattice_Algebra.pdf) | ZP-A | v1.21 | The lattice-algebra foundation: the bottom element ⊥ and the order it induces. |
| [p-adic Topology](ZP-B_pAdic_Topology.pdf) | ZP-B | v1.14 | The 2-adic topology: why p = 2, and why departure from ⊥ is irreversible. |
| [Information Theory](ZP-C_Information_Theory.pdf) | ZP-C | v1.21 | The information layer: state distributions, 1-bit cost, unbounded surprisal at ⊥. |
| [State Layer](ZP-D_State_Layer.pdf) | ZP-D | v1.15 | The Hilbert-space layer: the snap as an orthogonal shift between states. |
| [Bridge Document](ZP-E_Bridge_Document.pdf) | ZP-E | v3.27 | The bridge: the snap assembled as a derived theorem across the layers. |
| [The Counterexamples](ZP-F_The_Counterexamples.pdf) | ZP-F | v1.6 | The counterexamples: ordered fields (ℝ, ℚ) where the snap cannot occur. |
| [Category Theory](ZP-G_Category_Theory.pdf) | ZP-G | v1.15 | The categorical layer: ⊥ as initial object, the informational singularity. |
| [Categorical Bridge](ZP-H_Categorical_Bridge.pdf) | ZP-H | v1.19 | The categorical bridge: the snap holding under all four domain functors. |
| [Native Categories Addendum](ZP-H_Native_Categories_Addendum.pdf) | ZP-H Native Categories Addendum | v1.2 | The snap floor realized inside each framework's native Mathlib category (TopCat, ModuleCat ℂ, KleisliCat PMF). Reads after ZP-H. |
| [Inside Zero](ZP-I_Inside_Zero.pdf) | ZP-I | v1.22 | Inside zero: each maximal chain that strictly ascends at every step, with its 2-adic valuation tracking the depth index, converges to 0 in the 2-adics; reading that limit as an occupant of the ⊥ role, and then as a successor ⊥′, are two further commitments. |
| [Self-Reference](ZP-J_Self_Reference.pdf) | ZP-J | v2.6 | Self-reference: ⊥ as the Quine atom, and the AFA structure it requires. |
| [AFA Addendum](ZP-J_AFA_Addendum.pdf) | ZP-J AFA Addendum | v1.15 | Decoration uniqueness for finite graphs from the valuation structure alone. Reads after ZP-J. |
| [Wheel Addendum](ZP-J_Wheel_Addendum.pdf) | ZP-J Wheel Addendum | v1.3 | The wheel of fractions as a wheel: division by zero made total. Reads after ZP-J. |
| [Keystone Addendum](ZP-J_Keystone_Addendum.pdf) | ZP-J Keystone Addendum | v1.7 | The diagonal-fixed-point keystone: the Lawvere face-split (machine-checked) and the snap as a well-foundedness boundary crossing. Reads after ZP-J. |
| [Computational Grounding](ZP-K_Computational_Grounding.pdf) | ZP-K | v1.14 | Computational grounding: the bottom's structural self-containment, with the computational reading carried as a commitment. |
| [Incomputability Convergence](ZP-L_Incomputability_Convergence.pdf) | ZP-L | v1.6 | ε₀ as the exact ordinal threshold the snap is keyed to. (Occurrence is a framework commitment, not a theorem.) |
| [Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf) | ZP-M | v1.3 | The bridge between the Kleene quine and the ε₀ fixed point. |
| [The Constructive Snap](ZP-N_The_Constructive_Snap.pdf) | ZP-N | v2.0 | The constructive companion to ZP-L: the ε₀ snap from below on ordinal notations, choice-free (propext only). Locates ZP-L's classical dependency in Mathlib's order instance and shows it load-bearing - comparing arbitrary well-orders implies excluded middle (a known taboo, cited to Kraus/Nordvall Forsberg/Xu). Adds a carrier sized to ε₀ whose crossing into Ordinal is one named map with a measured price. Whether ZP-L's ε₀ results are eliminable remains UNCLASSIFIED. |
| [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) | ZP-P | v1.24 | Synthesis layer: the least-vs-greatest fixed-point fork, generalizing the Foundation/AFA orthogonal-contact-point claim across frameworks. |
| [The Frame-Change](ZP-Q_The_Frame_Change.pdf) | ZP-Q | v1.10 | Synthesis layer (ZP-P sequel): the bottom read as both 0 and ∞, and what that does not settle. The order-theoretic frame-flip universal is proved; the categorical Lawvere universal meets a proven Cantor wall; the cross-domain identity is a type boundary. |
| [Cross-Category Fixed Point](ZP-R_Cross_Category_Fixed_Point.pdf) | ZP-R | v1.6 | Synthesis / placement layer: locates and realizes the framework's self-application fixed point ⊥ as a Lawvere fixed point across three faces: refuted in Set (Cantor), a fork (not a reflexive object) in the monotone/domain regime, and realized in the computability face (Rogers/Kleene, the crossing). Existence-as-Lawvere, uniqueness, and location are each proved but face-local and non-composable; the global identification is a fenced conjecture. |
| [Diagonal Family Addendum](ZP-R_Diagonal_Family_Addendum.pdf) | ZP-R Diagonal Family Addendum | v1.1 | The complete roster of the self-referential relationship at ⊥, by the μ/ν fork: wall faces (Cantor, Russell, Turing, Tarski, Curry) where self-reference cannot close, and floor faces (Quine atom, Kleene quine, Löb / Gödel 2nd, Rice) where it does. Every variant Lean-witnessed and tied to ⊥. Reads after ZP-R. |
| [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf) | Choice-Free Core | v1.9 | Framework-wide note: the central results are choice-free (T-SNAP is axiom-free); the framework is not choice-free as a whole - most of its choice is inherited from Mathlib in the analytic realizations, and the category-theory face carries the framework's own. Two dependences are provably essential, one of each provenance, and *essential* scopes to the general statement over arbitrary types: the same construction is `[propext]` once the carrier has decidable equality. See CLAIMS.md. Anchored on AxiomProfile.lean. |

### Reading Order (by Specialty)

The framework is not a line. Several fields each reach a bottom, and those bottoms all play the same structural role, the diagonal fixed point ⊥; the documents above are the spokes into it. Start at the hub, then follow your own field. A document that appears in more than one field's route is a bridge, and the overlap is the point: the fields' bottoms share one structural shape. Whether they are literally one object is a type boundary, not a theorem (see [The Frame-Change](ZP-Q_The_Frame_Change.pdf)).

**Start here (the hub, for everyone):** two companion maps - [The Bottom Element (⊥)](BOTTOMELEMENT.md), the map of the object ⊥, and [The Binary Snap (⊥ → ε₀)](SNAP.md), the map of the transition off it - each with what is proved versus open → [Bridge Document](ZP-E_Bridge_Document.pdf), the snap assembled as a derived theorem → [The Frame-Change](ZP-Q_The_Frame_Change.pdf), the bottom read as both 0 and ∞, and why every field's bottom plays the same structural role. Keep the [Claims Ledger](CLAIMS.md) beside you for proved-versus-conjectural status.

**Then follow your field:**

- **Number theory and valuation (p-adic):** [p-adic Topology](ZP-B_pAdic_Topology.pdf) → [The Counterexamples](ZP-F_The_Counterexamples.pdf) → [The Frame-Change](ZP-Q_The_Frame_Change.pdf) (the p-adic Riemann sphere)
- **Proof theory and ordinals:** [Incomputability Convergence](ZP-L_Incomputability_Convergence.pdf) → [Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf) → [The Constructive Snap](ZP-N_The_Constructive_Snap.pdf)
- **Computability and recursion:** [Computational Grounding](ZP-K_Computational_Grounding.pdf) → [Kleene-Ordinal Bridge](ZP-M_Kleene_Ordinal_Bridge.pdf)
- **Set theory and foundations (AFA):** [Self-Reference](ZP-J_Self_Reference.pdf), with the [AFA](ZP-J_AFA_Addendum.pdf) and [Keystone](ZP-J_Keystone_Addendum.pdf) addenda → [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf)
- **Category theory:** [Category Theory](ZP-G_Category_Theory.pdf) → [Categorical Bridge](ZP-H_Categorical_Bridge.pdf), with the [Native Categories](ZP-H_Native_Categories_Addendum.pdf) addendum → [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) and [The Frame-Change](ZP-Q_The_Frame_Change.pdf)
- **Order, lattice, and state:** [Lattice Algebra](ZP-A_Lattice_Algebra.pdf) → [Inside Zero](ZP-I_Inside_Zero.pdf), then the state layers [Information Theory](ZP-C_Information_Theory.pdf) and [State Layer](ZP-D_State_Layer.pdf)

Each spoke is the same three beats: your field, then the bridge that carries it out, then back to ⊥. Read your own layers, then the synthesis layer they feed ([The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) or [The Frame-Change](ZP-Q_The_Frame_Change.pdf)), then the hub, and you will see your field's bottom is doing the same structural work as every other field's.

**The spine (the argument itself, no field assumed):** [The Bottom Element (⊥)](BOTTOMELEMENT.md) → [Bridge Document](ZP-E_Bridge_Document.pdf) → [The Fixed-Point Fork](ZP-P_The_Fixed_Point_Fork.pdf) → [The Frame-Change](ZP-Q_The_Frame_Change.pdf) → [Cross-Category Fixed Point](ZP-R_Cross_Category_Fixed_Point.pdf). This is the through-line, and it replaces the old single linear reading order, which tried to send every reader through all of the documents in one sequence.

**Orientation and general readers:** [The Choice-Free Core](ZP_Choice_Free_Core_Addendum.pdf) records the axiom profile; the [Foreword](Zero_Paradox_Foreword.pdf) and [The Philosophical Question](ZP_Philosophical_Question.pdf) give context; plain-language companions and a general-reader path are in [Guide](GUIDE.md). The [Wheel Addendum](ZP-J_Wheel_Addendum.pdf) (division by zero made total) is a self-contained aside off the set-theory route.

---

## Axiomatic Commitments

This framework adds no axioms specific to the result: the central theorem follows from the standard bottom-element axiom of join-semilattice theory alone, and **AX-1 (Binary Snap Causality) is no longer an axiom** - it is Theorem T-SNAP, derived in ZP-E.

Of the remaining commitments, most are restatements of structure established in earlier layers (AX-G1 and AX-G2 are grounded in ZP-A's bottom element and ZP-A antisymmetry with ZP-B C3). **One is substantive and is not reducible to computation: AX-B1**, that existence is discrete rather than a continuum of partial states. The `decide` proof (`ax_b1_distinct`) checks that the two states are distinct *given* a two-element type; choosing a discrete alphabet over a continuum is the commitment itself, and is not what `decide` verifies. See the [Claims Ledger](CLAIMS.md) for the full statement.

The framework is stated over ZF + AFA (not ZFC), but the commitment is not the *adoption of AFA specifically*: it is a set of requirements on the host theory - that the bottom is a self-containing Quine atom (⊥ = {⊥}), and that this atom is unique - of which AFA is the canonical example. Those requirements are a checkable object, the `QuineHost` typeclass (`ZeroParadox/Settheory/QuineHost.lean`): Foundation-freeness is *forced* by the Quine atom (`quineHost_not_wellFounded`); ZFC + Foundation is excluded in-kernel about Mathlib's real `ZFSet` (`zfSet_no_quine_bottom`); Boffa's permissiveness - it admits a proper class of Quine atoms, not one - is what fails (Z), witnessed by a toy model (`boffa_fails_unique`) rather than an in-kernel fact about that theory; and AFA satisfies all three (`afaStructure_isQuineHost`). Only "these are the right requirements to demand" remains argued (and where AFA-specific results are used elsewhere, they are proved separately, not assumed from full AFA); the discipline every such claim must meet is defined in [Forced Metatheoretic Commitment](fmc.md). The bottoms across the layers form one **family** (MC-1): per-domain membership is proved (its correspondence half is `mc1_correspondence`), and the reading that they are numerically *one object* is retired as ill-typed.

The full labelled account - the supporting commitments (AX-B1, AX-G1, AX-G2, MP-1, RP-1, DP-1), the metatheoretic stance and the host-theory requirements (where AFA fits), and the bottom-family (MC-1) account in full - is in the **[Claims Ledger](CLAIMS.md)** (Tiers 4-5).

---

## Question Register

The framework's open questions, design commitments, and resolved questions are tracked in the **[Claims Ledger](CLAIMS.md)** - Tier 6 (open: the `Classical.choice` necessity question, OQ-E2, the Lawvere conjecture), Tier 5 (chosen commitments), and the Resolved-questions list.

**Verification status:** ZP-A through ZP-N, ZP-P, ZP-Q, and ZP-R, plus the ZP-H native-category functors and `mc1_correspondence`, are machine-verified in Lean 4. A second-prover cross-check (e.g. Rocq) is not yet done.

Open questions are discussed publicly in the [GitHub Discussions Open Questions category](https://github.com/timbrigham/ZeroParadox/discussions/categories/open-questions).

---

## Version History

Hosted at [timbrigham/ZeroParadox](https://github.com/timbrigham/ZeroParadox). Previous document versions are preserved in the repository's git history and in each release's Zenodo/DOI snapshot. See [Guide](GUIDE.md) for development notes and process documentation.

---

## License

All conceptual development, structure, and authorship originate with the human creator.

This work is licensed under the Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International License (CC BY-NC-ND 4.0, except the fonts in `scripts/fonts/`, which are third-party and remain under their own licences (DejaVu/Bitstream Vera; STIX Two under SIL OFL 1.1), shipped beside them).

You may share the work with attribution, but you may not modify it or use it commercially. See [License](LICENSE) for full details.

---

## Citation

If referencing this work, please cite:

> Brigham, Timothy. The Zero Paradox (2026). https://github.com/timbrigham/ZeroParadox

---

## Contact

For inquiries, discussion, or collaboration, reach out by email at [timbrigham@zeroparadox.org](mailto:timbrigham@zeroparadox.org) or open an issue on [GitHub](https://github.com/timbrigham/ZeroParadox).
