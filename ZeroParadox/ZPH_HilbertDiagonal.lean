import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeSeam
import ZeroParadox.ZPH_MC1_TC37
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H: ⊥ is the unique finite-dimensional fixed point of the biproduct-diagonal

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file proves the **genuine** version of the diagonal-self-reference statement that TC37
(`seam_unit_iff_isZero`) could only state degenerately. The honest categorical "diagonal" on
`ModuleCat ℂ` is the biproduct-double `X ↦ X ⊞ X` (`⊞ = CategoryTheory.Limits.biprod`). We ask:
which objects are their own diagonal double, `X ≅ X ⊞ X`?

**Theorem `biprod_diagonal_only_zero`.** For a *finite-dimensional* `X : ModuleCat ℂ`, any
isomorphism `X ≅ X ⊞ X` forces `IsZero X`. So among finite-dimensional objects, the zero object
⊥ is the *unique* fixed point of the biproduct-diagonal — the honest "⊥ is its own diagonal
double, and nothing else is" statement.

Proof: a `ModuleCat` iso gives a ℂ-`LinearEquiv` on carriers (`Iso.toLinearEquiv`), and
`X ⊞ X` has carrier ℂ-linearly equivalent to `X × X` (`ModuleCat.biprodIsoProd`). `finrank` is a
linear-equiv invariant, so `finrank X = finrank (X × X) = finrank X + finrank X`
(`Module.finrank_prod`), giving `finrank X = 0`, hence (finite-dim) `Subsingleton X`
(`Module.finrank_zero_iff`), hence `IsZero X` (`ModuleCat.isZero_of_subsingleton`).

**Honest scope.** This is the GENUINE implication `X ≅ X ⊞ X → IsZero X` for finite-dim `X` —
the content TC37's `seam_unit_iff_isZero` lacked (its backward direction discards the iso and just
re-invokes `hilbert_bottom_isZero`). **FENCE: finite-dimensionality is essential — the statement
is FALSE for infinite-dim modules** (`ℂ^ℕ ≅ ℂ^ℕ ⊕ ℂ^ℕ`, the **Eilenberg–Mazur swindle**; this is the
standard reason K-theory restricts to finitely-generated objects). No mathematical novelty is claimed:
the finite-dim implication is the standard dimension-count, and the value here is placement (the zero
object as the unique finite-dim self-double, with finite-dim named as load-bearing). This is the
self-reference witness for
the Hilbert bottom in the *diagonal-self-similarity* sense (⊥ is its own diagonal double, uniquely
among finite-dim objects), NOT the Kleene-quine computational sense.

**Corollary `seam_is_diagonal_fixpoint`.** The concrete Hilbert bottom `seam = fD_functor.obj 0`
is finite-dimensional and `Nonempty (seam ≅ seam ⊞ seam)` (it `IsZero`, so it is its own biproduct
double via `isoBiprodZero`); applying the theorem recovers `IsZero seam`. The point: the seam is a
*witness* that finite-dim diagonal fixed points exist, and the theorem says they are exactly the
zero objects — so ⊥ = the unique finite-dim diagonal fixed point, made concrete at the Hilbert
bottom.

## Structure

- § I   `biprod_diagonal_only_zero` — the genuine uniqueness theorem.
- § II  `seam_is_diagonal_fixpoint` — concrete witness at the Hilbert bottom.
-/

namespace ZeroParadox.HilbertDiagonal

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_MC1_TreeSeam ZeroParadox.ZPH_MC1_TC37

/-! ### § I  The genuine uniqueness theorem -/

/-- **Theorem.** In `ModuleCat ℂ`, a finite-dimensional object isomorphic to its own
    biproduct-double is a zero object. ⊥ is the unique finite-dimensional fixed point of the
    biproduct-diagonal `X ↦ X ⊞ X`.

    FENCE: finite-dimensionality is essential — false for infinite-dim modules
    (`ℂ^ℕ ≅ ℂ^ℕ ⊕ ℂ^ℕ`). -/
theorem biprod_diagonal_only_zero (X : ModuleCat ℂ) [Module.Finite ℂ X]
    (h : Nonempty (X ≅ X ⊞ X)) : IsZero X := by
  obtain ⟨i⟩ := h
  -- ℂ-linear equiv on carriers: X ≃ₗ X ⊞ X, then X ⊞ X ≃ₗ X × X.
  have e : X ≃ₗ[ℂ] (X × X) :=
    (i.toLinearEquiv).trans (ModuleCat.biprodIsoProd X X).toLinearEquiv
  -- finrank is a linear-equiv invariant.
  have hfin : Module.finrank ℂ X = Module.finrank ℂ (X × X) := LinearEquiv.finrank_eq e
  rw [Module.finrank_prod] at hfin
  -- finrank X = finrank X + finrank X ⟹ finrank X = 0.
  have hzero : Module.finrank ℂ X = 0 := by omega
  -- finite-dim + finrank 0 ⟹ Subsingleton carrier ⟹ IsZero.
  haveI : Subsingleton X := Module.finrank_zero_iff.1 hzero
  exact ModuleCat.isZero_of_subsingleton X

/-! ### § II  Concrete witness at the Hilbert bottom -/

/-- The Hilbert bottom `seam = fD_functor.obj 0` is finite-dimensional. Its carrier is
    `StateSpace 0 = EuclideanSpace ℂ (Fin 0)`, finite-dim over the finite index `Fin 0`. -/
instance : Module.Finite ℂ (fD_functor.obj 0) := by
  show Module.Finite ℂ (ZeroParadox.ZPD.StateSpace 0)
  infer_instance

/-- **Corollary.** The concrete Hilbert bottom `seam = fD_functor.obj 0` is a finite-dimensional
    object that is its own biproduct double, and is therefore (by `biprod_diagonal_only_zero`) a
    zero object — the concrete witness that ⊥ is the unique finite-dim diagonal fixed point. -/
theorem seam_is_diagonal_fixpoint :
    Nonempty (seam ≅ seam ⊞ seam) ∧ IsZero seam := by
  have hfix : Nonempty (seam ≅ seam ⊞ seam) :=
    ⟨isoBiprodZero (Y := seam) hilbert_bottom_isZero⟩
  exact ⟨hfix, biprod_diagonal_only_zero seam hfix⟩

end ZeroParadox.HilbertDiagonal

/-! ## Axiom Purity Check

Both theorems carry the standard Mathlib library footprint `[propext, Classical.choice, Quot.sound]`.
`Classical.choice` enters through the `ModuleCat` / `EuclideanSpace` / `finrank` machinery — the same
library dependency already carried by the ZP-D / ZP-H Hilbert layer (`fD_functor`, `finrank_prod`,
`biprodIsoProd`), not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.HilbertDiagonal

#print axioms biprod_diagonal_only_zero
#print axioms seam_is_diagonal_fixpoint

end PurityCheck
