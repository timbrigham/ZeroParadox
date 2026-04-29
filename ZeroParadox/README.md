# Zero Paradox — Lean 4 Source

Lean 4 + Mathlib proofs for the Zero Paradox framework. The central result is **T-SNAP** (Binary Snap: `join c₀ c₁ = c₁`), derived from standard join-semilattice axioms. For full project context see [README.md](../README.md) at the repository root.

## Build

```
lake build
```

Clean build: zero errors, zero warnings across all files. Some files set `maxHeartbeats 400000` due to heavy import chains (p-adics + Hilbert space machinery).

## File Overview and Dependency Order

### Core chain

| File | Key result | Depends on |
|------|------------|------------|
| `ZPA.lean` | `ZPSemilattice` typeclass (A1–A4); partial order (T1); ⊥ minimum (T2); monotonicity (T3) | — |
| `ZPB.lean` | `Q₂BallDepth`; AX-B1 (binary decidability); ultrametric (T1); clopen balls (T2); topological irreversibility (C3) | ZPA |
| `ZPC.lean` | `DiscreteStateSpace`; L-RUN (execution is non-null); TQ-IH (no program avoids non-null state); L-INF (informational extremity at ⊥) | ZPA, ZPB |
| `ZPD.lean` | `TransitionMap`; transition operator T: Q₂ → ℂⁿ; orthogonal snap shift (T4); non-decreasing norms (T5) | ZPA, ZPB |
| `ZPE.lean` | `MachinePhase` ZPSemilattice instance; **T-SNAP** (`join c₀ c₁ = c₁`); DA-2 (successor null); `da1_minimal_path` (axiom-free) | ZPA–ZPD |
| `ZPJ.lean` | `AFAStructure` typeclass; **T-EXEC** (Quine atom = ⊥, axiom-free); `cc1_derived` (CC-1 as theorem); three-way equivalence: Quine atom = ⊥ = join-identity | ZPA |
| `ZPK.lean` | `KleeneStructure` typeclass; `selfApply_partrec` (Kleene's second recursion theorem); T-COMP (four-way equivalence); **`da1_closed_concrete : IsQuineAtom(⊥ : MachinePhase)`** | ZPE, ZPJ |
| `ZPI.lean` | **`t_iz_complete`** (all four T-IZ steps: Cauchy convergence + DA-2 + DA-1/Kleene + T-SNAP); `h_strict_from_r1_t3` (strict valuation growth derived, not assumed) | ZPA, ZPB, ZPE, ZPK |

### Categorical extension (self-contained; depends on ZPE conceptually, not formally)

| File | Key result | Depends on |
|------|------------|------------|
| `ZPG.lean` | `ZPCategory` and `ZPSurprisal` typeclasses; T6 (informational singularity); T7 (Categorical Zero Paradox); `ForkCat` concrete instance | ZPA |
| `ZPH.lean` | Four functors F_A–F_D; T-H2 (singularity compatibility); T-H3 (Binary Snap under all four functors); `nnreal_initial_grounding` shared witness | ZPG, ZPC, ZPD |

## Axiom Profile

Each file contains a `section PurityCheck ... end PurityCheck` block with `#print axioms` for key theorems.

- **ZPA–ZPG:** `propext`, `Quot.sound` only, or fully axiom-free for computable results (e.g. `l_run` proved by `decide`)
- **ZPH, ZPK:** `[propext, Classical.choice, Quot.sound]` — `Classical.choice` enters through Mathlib's Kleene/computability machinery (`Code`, `Partrec`), not through `ZPSemilattice` or `AFAStructure`

## Honest Scope Boundaries

The framework is explicit about what is and is not Lean-verified. Two boundaries are worth noting upfront:

**ZPG.lean T6-b/c** — The Lean proofs for T6-b (strict surprisal inequality) and T6-c (subadditivity along chains) verify only `Nat.zero_le _` (non-negativity by type). The mathematical content — which requires Kolmogorov complexity results not yet in Mathlib — is **not** Lean-verified. This is stated explicitly in the file's inline scope note and in the PDF validation table.

**ZPE.lean / ZPC.lean — DA-1 Path 2** — L-INF formally proves that surprisal is unbounded at ⊥. The inference from unbounded surprisal to "necessarily executing" is an ontological bridge claim, not a mathematical consequence of L-INF alone. ZPC.lean's L-INF docstring states this explicitly: "L-INF supplies the formal premise; DA-1 supplies the ontological bridge." DA-1 is formally closed through independent paths (AFA/self-containment and Kleene fixed point) in ZPK.lean.

Findings that engage these boundaries without reading the inline disclosures first are likely already addressed.
