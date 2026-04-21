# The Zero Paradox - Project Index
**April 2026 | Final Formalism**

[![Lean Action CI](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/timbrigham/ZeroParadox/actions/workflows/lean_action_ci.yml)

## What This Is

The Zero Paradox is a rigorous multi-framework mathematical ontology addressing a single question: can the emergence of state from a null condition be given a formally complete, cross-disciplinary account?

The answer developed here is yes. The proof is distributed across seven self-contained mathematical layers, each internally closed before any cross-framework claim is made.


---

## The Central Result

The **Binary Snap** - the transition from the Null State ⊥ to the first atomic state ε₀ - is a **theorem**, not an axiom.

The derivation chain is:

**P₀** (incompressibility threshold, ZP-C D1)  
→ **DA-1** (instantiation of a configuration at P₀ constitutes an execution event, ZP-E)  
→ **D7** (machine configuration definition, ZP-C)  
→ **L-RUN** (execution is a non-null state change, ZP-C)  
→ **TQ-IH** (no program outputs ⊥ without a non-null intermediate state, ZP-C)  
→ **ZP-A D2** (a non-null state change from ⊥ is a join - the Binary Snap)  
→ **T-SNAP** (Binary Snap is derived; AX-1 is retired as an axiom)

The three remaining intentional axioms: **AX-B1** (binary existence), **AX-G1** (initial object exists), **AX-G2** (source asymmetry).

---

## What This Is Not

- **Not a physical theory** - the framework is instantiation-independent; physical theories are recovered by fixing ε₀
- **Not a claim about consciousness or the hard problem** - the framework is silent on these questions
- **Not a claim that zero is paradoxical in all of mathematics** - the paradox is local to this framework's structure
- **Not a logical contradiction** - no theorem in ZP-A through ZP-D contradicts any other

---

## Document Index

### Entry Point

| File | Description |
|------|-------------|
| [README](README.md) | This file - project index |
| [Zero Paradox Foreword](Zero_Paradox_Foreword.pdf) | Plain-language introduction for any reader. Start here. |

### Formal Ontology Documents

| File | Document | Version | Contents |
|------|----------|---------|----------|
| [ZP-A Lattice Algebra](ZP-A_Lattice_Algebra_v1_2.pdf) | ZP-A | v1.2 | Join-semilattice (L, ∨, ⊥). Axioms A1-A4. Monotonicity. Additive ontology. |
| [ZP-B pAdic Topology](ZP-B_pAdic_Topology_v1_2.pdf) | ZP-B | v1.2 | AX-B1. MP-1. Derivation of p=2. Q₂ ultrametric. Clopen balls. Total disconnectedness. Topological irreversibility. |
| [ZP-C Information Theory](ZP-C_Information_Theory_v1_4.pdf) | ZP-C | v1.4 | P₀. State representations from AX-B1. JSD = 1 bit. Discrete surprisal field. **L-RUN. TQ-IH. T-BUF.** AX-1 promoted to Candidate Theorem. |
| [ZP-D State Layer](ZP-D_State_Layer_v1_2.pdf) | ZP-D | v1.2 | Hilbert space H = ℂⁿ. Transition operator T: Q₂ → H. DP-1. Existence and uniqueness of T. Snap → orthogonal shift. |
| [ZP-E Bridge Document](ZP-E_Bridge_Document_v2_0.pdf) | ZP-E | v2.0 | **DA-1** (instantiation = execution). **T-SNAP** (Binary Snap derived). **DA-2** (instantiation succession, directed tree). **DA-3** (perspective-relative cardinality). Accounts for Skolem, CH independence, Russell. Full traceability register. |
| [ZP-G Category Theory](ZP-G_Category_Theory_v1_1.pdf) | ZP-G | v1.1 | Category C. Initial object. AX-G1, AX-G2. Universal property. |
| [ZP-H Categorical Bridge](ZP-H_Categorical_Bridge_v1_1.pdf) | ZP-H | v1.1 | Functors FA-FD. Singularity reconciliation. T-H3: Snap under all four functors. T-SNAP inherited as derived theorem. |

### Illustrated Companion Documents (General Reader)

One companion per formal document. Plain language, diagrams, real-world examples.

| File | For Document | Key Diagrams |
|------|-------------|--------------|
| [ZP-A Illustrated Companion](ZP-A_Illustrated_Companion.pdf) | ZP-A | Hasse diagram, one-directional transitions |
| [ZP-B Illustrated Companion](ZP-B_Illustrated_Companion.pdf) | ZP-B | Nested clopen balls, disjoint ball separation |
| [ZP-C Illustrated Companion](ZP-C_Illustrated_Companion.pdf) | ZP-C | Surprisal field singularity, 1-bit Snap cost, L-RUN execution trace |
| [ZP-D Illustrated Companion](ZP-D_Illustrated_Companion.pdf) | ZP-D | T map: topology → orthogonality |
| [ZP-E Illustrated Companion](ZP-E_Illustrated_Companion.pdf) | ZP-E | Four-framework convergence, T-SNAP derivation chain |
| [ZP-G Illustrated Companion](ZP-G_Illustrated_Companion.pdf) | ZP-G | Category and functor concepts, initial object, informational singularity |
| [ZP-H Illustrated Companion](ZP-H_Illustrated_Companion.pdf) | ZP-H | Four-functor convergence, T-SNAP derivation chain, Binary Snap across all frameworks |

### Supporting Documents

| File | Description |
|------|-------------|
| [ZP Tools and Methods](ZP_Tools_and_Methods.pdf) | How the framework was developed: Claude's role, what formal tools were and were not used (Rocq, Lean, etc.), the PDF rendering pipeline. |

### Formal Verification (Lean 4)

Machine-checked proofs of the formal documents using Lean 4 + Mathlib. Source lives on the `lake_testing` branch under `ZeroParadox/`.

| Document | Lean Source | Theorems Verified | Build | Proof Doc |
|----------|-------------|-------------------|-------|-----------|
| ZP-A Lattice Algebra | [ZeroParadox/ZPA.lean](ZeroParadox/ZPA.lean) | T1 (partial order), T2 (⊥ minimum), D2 equivalence, T3 (monotonicity), CC-1 (conditional) | Clean - April 2026 | [↗](proofs/ZP-A_Lean4.md) |
| ZP-B p-Adic Topology | [ZeroParadox/ZPB.lean](ZeroParadox/ZPB.lean) | AX-B1, T0 (p=2 unique), T1 (ultrametric), C1 (isosceles), T2 (clopen balls), C2 (no path), T3 (isolation of 0), T5 (totally disconnected), C3 (Snap irreversible) | Clean - April 2026 | [↗](proofs/ZP-B_Lean4.md) |
| ZP-C Information Theory | [ZeroParadox/ZPC.lean](ZeroParadox/ZPC.lean) | T1 (distinct distributions), T1b (KL/JSD = log 2), D5 (DF antisymmetry), T2 (telescoping + divergent circulation), L-RUN (execution non-null), TQ-IH | Clean - April 2026 | [↗](proofs/ZP-C_Lean4.md) |
| ZP-D State Layer | [ZeroParadox/ZPD.lean](ZeroParadox/ZPD.lean) | DP-1 (orthogonality), T2 (existence of T: injective, orthogonal, norm-preserving), T4 (Snap → orthogonal shift in H), T5 (monotone norms) | Clean - April 2026 | [↗](proofs/ZP-D_Lean4.md) |
| ZP-E Bridge Document | [ZeroParadox/ZPE.lean](ZeroParadox/ZPE.lean) | MachinePhase ZPSemilattice instance, T-SNAP (join + machine + derived + irreversibility), DA-2 (bottom characterization + novelty corollary), DA-3-D1 (accessible cardinality definition) | Clean - April 2026 | [↗](proofs/ZP-E_Lean4.md) |
| ZP-G Category Theory | [ZeroParadox/ZPG.lean](ZeroParadox/ZPG.lean) | ZPCategory class (AX-G1 + AX-G2), ZPSurprisal class (I-KC / D7'), T1 (initial uniqueness), T2 (universal constituent), T3 (unreachability), T4 (forward-only chains), T6-a/b/c (surprisal), T6 (informational singularity), T7 (Categorical Zero Paradox) | Clean - April 2026 | [↗](proofs/ZP-G_Lean4.md) |
| ZP-H Categorical Bridge | [ZeroParadox/ZPH.lean](ZeroParadox/ZPH.lean) | T-H1 (F_A initial object proved; F_B/F_C/F_D domain facts cited), T-H2 (singularity compatibility: ZPG unreachability ∧ ZPC divergence), T-H3 (Binary Snap under all four functors: join ∧ topological ∧ 1-bit ∧ orthogonal) | Clean - April 2026 | [↗](proofs/ZP-H_Lean4.md) |

---

## Axiomatic Commitments

| Label | Type | Statement |
|-------|------|-----------|
| **AX-B1** | Axiom | A state either exists or it does not. Binary, no third option. |
| **AX-G1** | Axiom | An initial object exists in the category C. |
| **AX-G2** | Axiom | Source asymmetry: hom(X, 0) = ∅ for X ≠ 0. No morphism returns to the initial object. |
| **MP-1** | Principle | The representational base is the minimum sufficient base for AX-B1. Derives p = 2. |
| **RP-1** | Principle | The probabilistic representation of a binary ontological state is a point-mass distribution. |
| **DP-1** | Design Commitment | Topological isolation in Q₂ is represented by orthogonality in H. |

**AX-1 (Binary Snap Causality) is no longer an axiom.** It is Theorem T-SNAP, derived in ZP-E.

---

## Status of All Major Open Questions

| Item | Status |
|------|--------|
| OQ-A1: Increment selection | Closed - ZP-E T5 (Iterative Forcing Theorem) |
| OQ-B1: p = 2 justification | Closed - ZP-B T0 (derived from AX-B1 + MP-1) |
| S1: Distribution stipulation | Closed - ZP-C T1 (derived from AX-B1 + RP-1) |
| OQ-C1: Non-conservatism of DF | Closed - ZP-C T2 (rebuilt within extended D6) |
| DA-1: Instantiation alignment | Closed - ZP-E DA-1 (D7 configurations are live by definition) |
| AX-1: Binary Snap Causality | **Closed - ZP-E T-SNAP (derived theorem)** |
| OQ-E1: Sequence vs. tree structure | Closed - ZP-E DA-2 (directed instantiation tree; branching mandatory via T-SNAP) |
| DA-2: Instantiation succession | Closed - ZP-E DA-2 (terminal state of I_n satisfies ⊥ role for I_n+1; C-DA2 derives ontological novelty of each ⊥) |
| DA-3: Perspective-relative cardinality | Closed (definitional) / Candidate (DA-3-C1) - ZP-E DA-3 (Skolem, CH independence, Russell accounted for structurally; formal derivation deferred to OQ-E2) |
| OQ-E2: Cardinality-semilattice correspondence | **Open** - do specific semilattice structures correspond to specific cardinality regimes? |
| Temperature T in BA-1 | Parameter - intentional; universe-contingent |
| Formal verification (Lean/Rocq) | ZP-A through ZP-H complete (April 2026) |

---

## Reading Order

**General reader:** [Foreword](Zero_Paradox_Foreword.pdf) → any [Illustrated Companion](#illustrated-companion-documents-general-reader) → [ZP-E Companion](ZP-E_Illustrated_Companion.pdf)

**Mathematician:** [ZP-A](ZP-A_Lattice_Algebra_v1_2.pdf) → [ZP-B](ZP-B_pAdic_Topology_v1_2.pdf) → [ZP-C](ZP-C_Information_Theory_v1_4.pdf) → [ZP-D](ZP-D_State_Layer_v1_2.pdf) → [ZP-E](ZP-E_Bridge_Document_v2_0.pdf) (in dependency order)

**For the category theory extension:** [ZP-G](ZP-G_Category_Theory_v1_1.pdf) → [ZP-H](ZP-H_Categorical_Bridge_v1_0.pdf) (self-contained; after ZP-E)

**For process/methods:** [ZP Tools and Methods](ZP_Tools_and_Methods.pdf)

---

## Notes on Development

This framework was developed by a human researcher in collaboration with Claude (Anthropic, April 2026). Claude served as research assistant, formal scribe, gap identifier, and PDF renderer. All mathematical content and theoretical direction originated with the researcher. See `ZP_Tools_and_Methods.pdf` for a complete account.

The PDF build tooling is publicly available in the [`scripts/`](scripts/) folder. Those scripts were generated by Claude and are included for transparency about how the documents were produced.

---

## Repository and Version History

This project is hosted on GitHub at [timbrigham/ZeroParadox](https://github.com/timbrigham/ZeroParadox). The repository uses Git for version control, allowing you to explore the evolution of the theorems and documents over time.

To view older versions of this README or the associated documents as the framework progressed:
- **Via GitHub web interface**: Navigate to the repository, click on the file, then "History" to browse commits.
- **Locally**: Use `git log` to see commit history and `git checkout <commit-hash>` to view specific versions.
- **Branches**: Different branches may contain snapshots at various stages (e.g., compare "main" vs. "illustrated" branches).

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

For inquiries, discussion, or collaboration, please open an issue on [GitHub](https://github.com/timbrigham/ZeroParadox) or reach out through the repository.

---

*Zero Paradox | Project Index | April 2026*
