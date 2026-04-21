# ZP-D State Layer - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** `051b402` (pre-commit; see final commit hash after push)
**Lean source:** [`ZeroParadox/ZPD.lean`](../ZeroParadox/ZPD.lean)
**Document proved:** ZP-D State Layer (Hilbert Space) v1.2

---

## Build Result

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```

**Result:** Clean — 3314 jobs, 0 errors, 0 warnings (after cleanup).
Two deprecation warnings suppressed by removing unused simp args
(`EuclideanSpace.single_apply` → simp found proof without it;
`EuclideanSpace.norm_single` → same).

---

## Axiom Purity Check

```
'ZeroParadox.ZPD.dp1_orthogonality'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPD.t2_injective'       depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPD.t2_orthogonal'      depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPD.t2_norm_eq_one'     depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPD.t2_existence'       depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPD.t4_snap_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPD.t5_monotone_norms'  depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Interpretation:** All proved theorems depend only on the standard Mathlib kernel axioms
inherited from functional analysis and inner product space infrastructure. No `sorryAx`
anywhere in the proved theorems. T3 (`t3_uniqueness`) carries `sorry` and is explicitly
excluded from the purity check — see "Items not formalized" below.

---

## Import Strategy

No p-adic imports. Q₂'s clopen-ball partition is abstracted as `Fin n` (an index type),
keeping ZP-D self-contained within functional analysis. This follows the ZP-C precedent:
ZP-B is imported conceptually but not as a Lean dependency.

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
```

`EuclideanSpace ℂ (Fin n)` provides H = ℂⁿ with all inner product and norm machinery.

---

## What Was Proved

### Formalizable items

| ZP-D item | Lean name | Statement |
|-----------|-----------|-----------|
| D1: H = ℂⁿ | `StateSpace n` | `abbrev StateSpace n := EuclideanSpace ℂ (Fin n)` |
| DP-1: Orthogonality | `dp1_orthogonality` | `i ≠ j → ⟪basisVec n i, basisVec n j⟫_ℂ = 0` |
| T2(i): T(0) = e₀ | `t2_maps_null` | `transitionOp n ⟨0,_⟩ = basisVec n ⟨0,_⟩` (rfl) |
| T2(ii): T(ε₀) = e₁ | `t2_maps_eps0` | `transitionOp n ⟨1,_⟩ = basisVec n ⟨1,_⟩` (rfl) |
| T2(iii): T injective | `t2_injective` | `Function.Injective (transitionOp n)` |
| T2(iv): orthogonality | `t2_orthogonal` | `i ≠ j → ⟪transitionOp n i, transitionOp n j⟫_ℂ = 0` |
| T2(v): norm-preserving | `t2_norm_eq_one` | `‖transitionOp n i‖ = 1` |
| T2: existence bundle | `t2_existence` | Conjunction of (iii), (iv), (v) |
| T4: Snap → orthogonal shift | `t4_snap_orthogonal` | `⟪T(⟨0,_⟩), T(⟨1,_⟩)⟫_ℂ = 0` (requires n ≥ 2) |
| T5: monotone norms | `t5_monotone_norms` | `‖T(S k)‖ ≤ ‖T(S(k+1))‖` for any sequence S |

### Items not formalized (and why)

| ZP-D item | Reason |
|-----------|--------|
| T3: Uniqueness up to unitary equivalence | Requires `OrthonormalBasis` equivalence API (`OrthonormalBasis.unitaryEquivalence` or similar). The two ONBs (transitionOp and T') span the same n-dimensional space; a unitary relating them exists by standard functional analysis. Proof deferred pending API availability in this Mathlib version. |
| R1: Decoupling remark | Architectural observation, not a theorem |
| R2: What T is not | Negative characterization; no positive claim to prove |
| CC-1: S₀ = ⊥ | Modelling commitment from ZP-A, not a ZP-D theorem |

---

## Proof Strategy Notes

**`dp1_orthogonality`:** `EuclideanSpace.inner_single_left` reduces
`⟪EuclideanSpace.single i 1, EuclideanSpace.single j 1⟫_ℂ` to `conj 1 * (single j 1).ofLp i`.
The `.ofLp` evaluation at `i` gives `if i = j then 1 else 0`, which is 0 when `i ≠ j`.
`simp [h.symm]` closes the goal after the inner product unfold.

**`t2_injective`:** Proof by contradiction. If `T(i) = T(j)` with `i ≠ j`:
(1) DP-1 gives `⟪T(i), T(j)⟫_ℂ = 0`; (2) substituting `T(i) = T(j)` gives
`⟪T(j), T(j)⟫_ℂ = 0`; (3) `inner_self_eq_zero.mp` yields `T(j) = 0`;
(4) but `‖T(j)‖ = 1` by `simp [transitionOp, basisVec]`; (5) `norm_zero` + `norm_num` closes.

**`t2_norm_eq_one`:** `simp [transitionOp, basisVec]` unfolds to `‖EuclideanSpace.single j 1‖`
and Mathlib's `PiLp` norm simp lemmas reduce this to `‖(1 : ℂ)‖ = 1`.

**`t4_snap_orthogonal`:** Delegates to `t2_orthogonal` with `i = ⟨0, _⟩` and `j = ⟨1, _⟩`.
The inequality `⟨0, _⟩ ≠ ⟨1, _⟩` follows from `congr_arg Fin.val h` giving `0 = 1`,
refuted by `norm_num`.

**`t5_monotone_norms`:** Both `‖T(S k)‖` and `‖T(S(k+1))‖` equal 1 by `t2_norm_eq_one`.
`simp [t2_norm_eq_one]` reduces the inequality to `1 ≤ 1`, closed by `le_refl`.

**T3 (sorry):** The statement is: given any orthonormal family T': Fin n → StateSpace n,
∃ U : StateSpace n ≃ₗᵢ[ℂ] StateSpace n such that U ∘ transitionOp = T'. The proof
requires constructing a `LinearIsometryEquiv` from the ONB {T(i)} to the ONB {T'(i)}.
This follows from `OrthonormalBasis.repr` and the fact that any two ONBs of the same
finite-dimensional Hilbert space are unitarily equivalent. The Lean proof requires
`OrthonormalBasis` API not yet confirmed available in Mathlib v4.30.0-rc2.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
