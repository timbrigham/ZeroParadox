import ZeroParadox.ZPB
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Top Functor: F_B into the real category `TopCat` (MC-1 remediation)

## Engineer's Take

TODO (Tim): your own words.

---

## Formal Overview (AI-assisted)

ZP-H proves the snap floor ⊥ is the categorical initial object inside the *proxy*
category `Q₂BallDepth` (a wrapper around ℕ engineered so depth-0 is initial). This file
does the stronger, honest thing: it realizes the snap chain as a genuine functor into the
*real* category of topological spaces, `TopCat`, with each step an actual clopen ball
`B(0, 2⁻ⁿ) ⊆ Q₂` and each morphism an actual continuous inclusion.

Because `TopCat` has a terminal object (the one-point space), it is **not** a `ZPCategory`,
so "preserves the initial object" is the wrong frame here. The shrinking clopen balls form
an **inverse system**, and the honest statement of "⊥ is the bottom" is that the intersection
(the limit of the system) is exactly `{0}` — the snap floor — `fB_bottom_is_limit`.

- `fB_functor : ℕᵒᵖ ⥤ TopCat` — the snap chain as a real diagram of topological spaces.
  `ℕᵒᵖ` because the balls shrink as the index grows (an inverse system).
- `fB_faithful` — the realization is faithful (no collapse of distinct snap steps).
- `fB_bottom_is_limit` — `⋂ n, B(0, 2⁻ⁿ) = {0}`: ⊥ is the limit of the chain.

This is the F_B half of the OQ-G3 upgrade (MC-1 correspondence into the real domain
categories). F_C (information) and F_D (Hilbert) are separate, gated files.

STUB: proof bodies are `sorry` pending the stub-first clean build.
-/

namespace ZeroParadox.ZPHTop

open ZeroParadox.ZPB
open CategoryTheory Topology

/-- The clopen ball at depth `n`: `B(0, 2⁻ⁿ) ⊆ Q₂`. Shrinks as `n` grows. -/
noncomputable def q2Ball (n : ℕ) : Set Q₂ :=
  Metric.closedBall 0 (2 ^ (-(n : ℤ)))

/-- Bigger index ⇒ smaller ball: `m ≤ n → q2Ball n ⊆ q2Ball m`. -/
theorem q2Ball_antitone {m n : ℕ} (h : m ≤ n) : q2Ball n ⊆ q2Ball m := by
  simp only [q2Ball]
  apply Metric.closedBall_subset_closedBall
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (by omega : -(↑n : ℤ) ≤ -(↑m : ℤ))

/-- Object map: depth `n` ↦ the ball `B(0, 2⁻ⁿ)` as a topological subspace of Q₂. -/
noncomputable def fBObj (n : ℕ) : TopCat :=
  TopCat.of ↥(q2Ball n)

/-- The continuous inclusion `q2Ball n ↪ q2Ball m` when `m ≤ n` (smaller ball into larger). -/
noncomputable def fBIncl {m n : ℕ} (h : m ≤ n) : C(↥(q2Ball n), ↥(q2Ball m)) :=
  ⟨Set.inclusion (q2Ball_antitone h), continuous_inclusion (q2Ball_antitone h)⟩

/-- F_B: the snap chain realized as a genuine inverse system of topological spaces in `TopCat`.
    Source `ℕᵒᵖ` (balls shrink as the index grows). Object `n ↦ B(0, 2⁻ⁿ)`,
    morphism = continuous inclusion. -/
noncomputable def fB_functor : ℕᵒᵖ ⥤ TopCat where
  obj n := fBObj n.unop
  map f := TopCat.ofHom (fBIncl (leOfHom f.unop))
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- F_B is faithful. NOTE: this is automatic, not load-bearing — the source `ℕᵒᵖ` is a thin
    (preorder) category, so every hom-set is a subsingleton and any functor out of it is faithful
    for free. The genuine content of "F_B realizes the snap chain without collapse" lives in
    `fB_bottom_is_limit` (the chain's limit is exactly the snap floor `{0}`) and in the morphisms
    being actual continuous inclusions of distinct subspaces (`fBIncl`), not in faithfulness. -/
theorem fB_faithful : fB_functor.Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- The payload. ⊥ is the limit of the inverse system: the intersection of all the
    shrinking clopen balls is exactly the snap floor `{0}`. This is the real-category
    analogue of "⊥ is the initial object" — honest for a category with a terminal object. -/
theorem fB_bottom_is_limit : (⋂ n, q2Ball n) = {(0 : Q₂)} := by
  simp only [q2Ball]
  ext x
  simp only [Set.mem_iInter, Metric.mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    -- the radii 2⁻ⁿ tend to 0, and dist x 0 ≤ 2⁻ⁿ for every n, so dist x 0 ≤ 0
    have htend : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) Filter.atTop (nhds 0) := by
      simp only [zpow_neg, zpow_natCast]
      exact tendsto_inv_atTop_zero.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
    have hle : dist x 0 ≤ 0 := ge_of_tendsto' htend (fun n => h n)
    exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)
  · rintro rfl n
    simp

end ZeroParadox.ZPHTop

/-! ## Axiom Purity Check

`Classical.choice` is expected here: it enters through Mathlib's topology/metric library
(`TopCat`, `continuous_inclusion`, `Metric.closedBall`, limit arguments) — the same dependency
carried by the ZP-B topology layer (e.g. `c3_irreversible`). It is a library dependency, not a
new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPHTop

#print axioms q2Ball_antitone
#print axioms fB_functor
#print axioms fB_faithful
#print axioms fB_bottom_is_limit

end PurityCheck

