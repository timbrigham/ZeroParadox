import ZeroParadox.ZPD
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Hilbert Functor: F_D into the real category `ModuleCat ℂ` (MC-1 remediation)

## Engineer's Take

Dimensions grow from zero by adding an additional point along the new orthogonal direction,
indexed starting at zero. A bare 0 itself is the initial point.

---

## Formal Overview (AI-assisted)

ZP-H proves the snap floor ⊥ is the categorical initial object inside the *proxy* category
`HilbDimDepth` (a wrapper around ℕ). This file does the stronger, honest thing for the Hilbert
domain: it realizes the snap chain as a genuine functor into a *real* Mathlib category.

Mathlib has no category of Hilbert spaces, so the honest real target is `ModuleCat ℂ` (route 2a):
each state space `StateSpace n = EuclideanSpace ℂ (Fin n)` is a ℂ-module, and the snap step is a
ℂ-linear isometric embedding `StateSpace n ↪ StateSpace m` (zero-padding the extra coordinates).
`ModuleCat ℂ` forgets the inner product at the category level, so the isometry content travels as
a side lemma (`fD_embed_inner`).

Unlike `TopCat`, `ModuleCat ℂ` has a *zero object*, and `StateSpace 0` (the empty-index, hence
subsingleton, state space) **is** that zero object — so here ⊥ is the genuine categorical
**initial object** of the real category (`fD_zero_isInitial`), a stronger statement than F_B's
"⊥ is the limit".

- `fD_embed` — the ℂ-linear zero-padding embedding `StateSpace n →ₗ[ℂ] StateSpace m` (`n ≤ m`).
- `fD_embed_inner` — the embedding preserves the inner product (Hilbert structure side lemma).
- `fD_functor : ℕ ⥤ ModuleCat ℂ` — the snap chain as a real diagram of ℂ-modules (direct system).
- `fD_zero_isInitial` — ⊥ = `StateSpace 0` is the initial object of `ModuleCat ℂ`.

This is the F_D half of the OQ-G3 upgrade (MC-1 correspondence into the real domain categories).
-/

namespace ZeroParadox.ZPHHilb

open ZeroParadox.ZPD
open CategoryTheory

/-- The ℂ-linear zero-padding embedding `StateSpace n ↪ StateSpace m` for `n ≤ m`:
    keep the first `n` coordinates, pad the rest with 0. -/
noncomputable def fD_embed {n m : ℕ} (_h : n ≤ m) :
    StateSpace n →ₗ[ℂ] StateSpace m where
  toFun v := WithLp.toLp 2 (fun i : Fin m => if hi : (i : ℕ) < n then v.ofLp ⟨i, hi⟩ else 0)
  map_add' v w := by
    apply WithLp.ofLp_injective
    funext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]
  map_smul' c v := by
    apply WithLp.ofLp_injective
    funext i
    by_cases hi : (i : ℕ) < n <;> simp [hi]

/-- The embedding preserves the inner product: the Hilbert structure that `ModuleCat ℂ`
    forgets travels as this side lemma. -/
theorem fD_embed_inner {n m : ℕ} (h : n ≤ m) (x y : StateSpace n) :
    @inner ℂ (StateSpace m) _ (fD_embed h x) (fD_embed h y)
      = @inner ℂ (StateSpace n) _ x y := by
  classical
  set H : ℕ → ℂ := fun k =>
    if hk : k < n then @inner ℂ ℂ _ (x.ofLp ⟨k, hk⟩) (y.ofLp ⟨k, hk⟩) else 0 with hHdef
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have hL : (∑ i : Fin m, @inner ℂ ℂ _ ((fD_embed h x) i) ((fD_embed h y) i))
      = ∑ k ∈ Finset.range m, H k := by
    rw [← Fin.sum_univ_eq_sum_range H m]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hi : (i : ℕ) < n <;> simp [hHdef, fD_embed, hi]
  have hR : (∑ j : Fin n, @inner ℂ ℂ _ (x j) (y j)) = ∑ k ∈ Finset.range n, H k := by
    rw [← Fin.sum_univ_eq_sum_range H n]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : (j : ℕ) < n := j.2
    simp [hHdef, hj]
  rw [hL, hR]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) h)
  · intro k _ hk
    have hkn : ¬ k < n := by simpa [Finset.mem_range] using hk
    simp [hHdef, hkn]

/-- F_D: the snap chain realized as a genuine functor into the real category `ModuleCat ℂ`.
    Direct system (dimension increases). Object `n ↦ StateSpace n`, morphism = ℂ-linear embedding. -/
noncomputable def fD_functor : ℕ ⥤ ModuleCat ℂ where
  obj n := ModuleCat.of ℂ (StateSpace n)
  map f := ModuleCat.ofHom (fD_embed (leOfHom f))
  map_id n := by
    ext v i
    simp [fD_embed]
  map_comp {X Y Z} f g := by
    have hXY : X ≤ Y := leOfHom f
    ext v i
    by_cases hX : (i : ℕ) < X
    · have hY : (i : ℕ) < Y := lt_of_lt_of_le hX hXY
      simp [fD_embed, hX, hY]
    · by_cases hY : (i : ℕ) < Y <;> simp [fD_embed, hX, hY]

/-- ⊥ = `StateSpace 0` is the genuine initial (zero) object of `ModuleCat ℂ`.
    `StateSpace 0 = EuclideanSpace ℂ (Fin 0)` is a subsingleton, hence a zero object. -/
noncomputable def fD_zero_isInitial : Limits.IsInitial (fD_functor.obj 0) := by
  haveI : Subsingleton (StateSpace 0) := ⟨fun a b => by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i⟩
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ (StateSpace 0))).isInitial

end ZeroParadox.ZPHHilb

/-! ## Axiom Purity Check

`Classical.choice` is expected here: it enters through Mathlib's `ModuleCat` / inner-product /
`EuclideanSpace` library — the same dependency carried by the ZP-D Hilbert layer. It is a library
dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPHHilb

#print axioms fD_embed
#print axioms fD_embed_inner
#print axioms fD_functor
#print axioms fD_zero_isInitial

end PurityCheck

