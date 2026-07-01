import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The p-adic Riemann sphere: inversion swaps the floor 0 and its antipode ∞

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file builds the **topological Riemann sphere over ℚ₂** — the one-point compactification
`OnePoint ℚ_[2]` — and the inversion map on it: `∞ ↦ 0`, `0 ↦ ∞`, and `x ↦ x⁻¹` otherwise. The central
result `rInvHomeo` is that this map is a **homeomorphism** of the sphere, and `rInv_swaps` is that it
**swaps the floor `0` with the point at infinity `∞`** (the 0=∞ antipodality, made literal).

The content is genuinely beyond Mathlib's field inversion, which uses `0⁻¹ = 0` and is therefore
*discontinuous at 0*; adjoining `∞` and sending `0 ↦ ∞` is exactly what *repairs* that discontinuity.
The real work is the two continuity proofs at the special points (as `x → 0`, `x⁻¹ → ∞`; symmetrically at
`∞`), which go through `OnePoint`'s neighborhood-of-∞ API (`nhds_infty_eq`, the cocompact filter) and the
fact that `ℚ_[2]` is a `ProperSpace` (closed balls compact, so leaving every compact ⟺ norm → ∞).

**Honest scope.** This is a TOPOLOGICAL homeomorphism — the p-adic Riemann sphere, the framework's
originating intuition (0 and ∞ antipodal under `z ↦ 1/z`). It is a standalone result. It is **NOT** the
cross-construction "inversion = passing to Cᵒᵖ" unification, which a prior-art check
(`.claude-local/notes/inv_cop_prior_art_2026-06-30.md`) recorded as non-buildable (no common type; the
abstract ⊥↔⊤ swap is already Mathlib's `compl_bot`/`compl_top`). Do not read this as that.

## Structure
- § I   `rInv` — the inversion map on `OnePoint ℚ₂`, and its computation rules.
- § II  `rInv_involutive` — it is its own inverse.
- § III `continuous_rInv` — continuity (the work is at `0` and `∞`).
- § IV  `rInvHomeo`, `rInv_swaps` — the homeomorphism and the 0↔∞ swap.
-/

namespace ZeroParadox.RiemannSphere

open OnePoint Filter Topology
-- ℚ_[2] has no `DecidableEq` (it is a completion), so the `0 ↦ ∞` case split in `rInv` needs a classical
-- decidability instance. Provided locally (rather than `open Classical`, which the linter discourages).
-- This is a topological result, not the choice-free core; the purity check notes the footprint.
attribute [local instance] Classical.propDecidable

/-- The 2-adic Riemann sphere: the one-point compactification of ℚ₂. -/
abbrev Sphere : Type := OnePoint ℚ_[2]

/-- Riemann-sphere inversion: `∞ ↦ 0`, `0 ↦ ∞`, and `x ↦ x⁻¹` on the nonzero affine points. -/
noncomputable def rInv : Sphere → Sphere
  | (∞ : Sphere) => OnePoint.some (0 : ℚ_[2])
  | OnePoint.some x => if x = 0 then (∞ : Sphere) else OnePoint.some (x⁻¹ : ℚ_[2])

@[simp] theorem rInv_infty : rInv ∞ = OnePoint.some (0 : ℚ_[2]) := rfl

@[simp] theorem rInv_zero : rInv (OnePoint.some (0 : ℚ_[2])) = ∞ := by
  simp only [rInv, if_pos]

theorem rInv_coe_ne {x : ℚ_[2]} (hx : x ≠ 0) :
    rInv (OnePoint.some x) = OnePoint.some (x⁻¹ : ℚ_[2]) := by
  simp only [rInv, if_neg hx]

/-- Inversion is its own inverse: `rInv (rInv s) = s`. -/
theorem rInv_involutive : Function.Involutive rInv := by
  intro s
  induction s using OnePoint.rec with
  | infty => simp [rInv]
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [rInv]
    · rw [rInv_coe_ne hx, rInv_coe_ne (inv_ne_zero hx), inv_inv]

/-- Inversion is continuous on the sphere. The affine-nonzero part is `tendsto_inv₀`; the genuine work is
    the two special points — at `0` the image leaves every compact (`‖x⁻¹‖ → ∞`), so it tends to `∞`, and
    symmetrically at `∞`. Uses `OnePoint.nhds_infty_eq` and `ProperSpace ℚ_[2]`. -/
theorem continuous_rInv : Continuous rInv := by
  rw [OnePoint.continuous_iff]
  refine ⟨?_, ?_⟩
  · -- Tendsto at ∞: as x leaves every compact, x⁻¹ → 0, so rInv ↑x → ↑0.
    rw [rInv_infty, Filter.coclosedCompact_eq_cocompact,
      ← Metric.cobounded_eq_cocompact]
    have hcong : (fun x : ℚ_[2] => (OnePoint.some (x⁻¹) : Sphere)) =ᶠ[Bornology.cobounded ℚ_[2]]
        (fun x : ℚ_[2] => rInv ↑x) := by
      filter_upwards [Bornology.isBounded_def.mp (Bornology.isBounded_singleton (x := (0 : ℚ_[2])))]
        with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      rw [rInv_coe_ne hx0]
    refine Filter.Tendsto.congr' hcong ?_
    exact (OnePoint.continuous_coe.tendsto _).comp tendsto_inv₀_cobounded
  · -- Continuity of g x = rInv ↑x everywhere.
    rw [continuous_iff_continuousAt]
    intro a
    by_cases ha : a = 0
    · -- At 0: g 0 = ∞, and g → ∞ as x → 0.
      subst ha
      have hval : rInv (OnePoint.some (0 : ℚ_[2])) = ∞ := rInv_zero
      show ContinuousAt (fun x : ℚ_[2] => rInv ↑x) 0
      rw [ContinuousAt, hval]
      -- Tendsto (fun x => rInv ↑x) (𝓝 0) (𝓝 ∞).
      have hpunct : Filter.Tendsto (fun x : ℚ_[2] => rInv ↑x) (𝓝[≠] 0) (𝓝 (∞ : Sphere)) := by
        have hcong : (fun x : ℚ_[2] => (OnePoint.some (x⁻¹) : Sphere)) =ᶠ[𝓝[≠] 0]
            (fun x : ℚ_[2] => rInv ↑x) := by
          filter_upwards [self_mem_nhdsWithin] with x hx
          have hx0 : x ≠ 0 := hx
          rw [rInv_coe_ne hx0]
        refine Filter.Tendsto.congr' hcong ?_
        have hto : Filter.Tendsto (Inv.inv : ℚ_[2] → ℚ_[2]) (𝓝[≠] 0)
            (Filter.coclosedCompact ℚ_[2]) := by
          rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
          exact tendsto_inv₀_nhdsNE_zero
        exact OnePoint.tendsto_coe_infty.comp hto
      -- Combine punctured nhds with the point value (= ∞).
      have hpure : Filter.Tendsto (fun x : ℚ_[2] => rInv ↑x) (pure (0 : ℚ_[2])) (𝓝 (∞ : Sphere)) := by
        rw [Filter.tendsto_pure_left]
        intro s hs
        have : rInv (OnePoint.some (0 : ℚ_[2])) = ∞ := rInv_zero
        simpa [this] using mem_of_mem_nhds hs
      rw [← nhdsNE_sup_pure (0 : ℚ_[2])]
      exact Filter.Tendsto.sup hpunct hpure
    · -- Away from 0: g = ↑(·⁻¹) near a, continuous via continuousAt_inv₀.
      have hcong : (fun x : ℚ_[2] => (OnePoint.some (x⁻¹) : Sphere)) =ᶠ[𝓝 a]
          (fun x : ℚ_[2] => rInv ↑x) := by
        filter_upwards [compl_singleton_mem_nhds ha] with x hx
        have hx0 : x ≠ 0 := by simpa using hx
        rw [rInv_coe_ne hx0]
      have hca : ContinuousAt (fun x : ℚ_[2] => (OnePoint.some (x⁻¹) : Sphere)) a :=
        OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ ha)
      exact hca.congr hcong

/-- The p-adic Riemann-sphere inversion as a homeomorphism (a continuous involution is its own continuous
    inverse). -/
noncomputable def rInvHomeo : Sphere ≃ₜ Sphere where
  toFun := rInv
  invFun := rInv
  left_inv := rInv_involutive
  right_inv := rInv_involutive
  continuous_toFun := continuous_rInv
  continuous_invFun := continuous_rInv

/-- **The 0=∞ antipodality, literal:** the Riemann-sphere homeomorphism swaps the floor `0` and the point
    at infinity `∞`. -/
theorem rInv_swaps :
    rInvHomeo (OnePoint.some (0 : ℚ_[2])) = ∞ ∧ rInvHomeo ∞ = OnePoint.some (0 : ℚ_[2]) :=
  ⟨rInv_zero, rInv_infty⟩

end ZeroParadox.RiemannSphere

/-! ## Axiom Purity Check (enable per theorem once proved) -/
section PurityCheck
open ZeroParadox.RiemannSphere
#print axioms rInv_involutive
#print axioms continuous_rInv
#print axioms rInv_swaps
end PurityCheck
