import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
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

namespace ZeroParadox

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

/-! ### § V. The maps that FIX the pole-pair, and why that makes it an AXIS

`rInv` **exchanges** `0` and `∞`. The scalings `x ↦ 2 ^ n * x` hold both still and translate along the
pole-pair additively in `n`, which is what makes it an *axis* rather than a bare pair.

⭐ **PRIOR ART — these declarations INSTANTIATE `OnePoint.instGLAction`, they do not extend it.** The
two `example`s closing this section are the identification, elaborated rather than asserted. What is
ours is the TOPOLOGY, not the algebra. Prior art, the loxodromic vocabulary and the stabiliser fence
are in `ZeroParadox/Valuation/RiemannSphere.md`, beside this file. -/


/-- Scaling by `2 ^ n` on the sphere: `∞ ↦ ∞` and `x ↦ 2 ^ n * x`. -/
noncomputable def rScale (n : ℤ) : Sphere → Sphere
  | (∞ : Sphere) => (∞ : Sphere)
  | OnePoint.some x => OnePoint.some ((2 : ℚ_[2]) ^ n * x)

@[simp] theorem rScale_infty (n : ℤ) : rScale n ∞ = ∞ := rfl

@[simp] theorem rScale_coe (n : ℤ) (x : ℚ_[2]) :
    rScale n (OnePoint.some x) = OnePoint.some ((2 : ℚ_[2]) ^ n * x) := rfl

/-- `Statement:` every `rScale n` sends `0` to `0` and `∞` to `∞`.
    `Reading:` **INVARIANT** — the pole-pair is fixed POINTWISE, not merely setwise, which is what
    separates an axis from the bare pair that `rInv_swaps` exchanges. -/
theorem rScale_fixes_poles (n : ℤ) :
    rScale n (OnePoint.some (0 : ℚ_[2])) = OnePoint.some (0 : ℚ_[2]) ∧ rScale n ∞ = ∞ :=
  ⟨by simp, rfl⟩

/-- `Statement:` scaling by ANY nonzero `u` fixes `0` and `∞` pointwise, not just by a power of `2`.
    `Reading:` **INVARIANT** — the NO-GO gauge for § V: a whole `ℚ₂ˣ`-indexed family of pole-fixing
    maps, of which `rScale` is one cyclic subgroup. ⚠ An INCLUSION, not an identification — that the
    stabiliser IS the diagonal torus is not proved here. -/
theorem stabiliser_is_bigger (u : ℚ_[2]) (hu : u ≠ 0) :
    (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ u hu)) (OnePoint.some (0 : ℚ_[2]))
        = OnePoint.some (0 : ℚ_[2]) ∧
    (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ u hu)) (∞ : Sphere) = ∞ :=
  ⟨by simp, rfl⟩

/-- **The parameter is additive.** The scalings compose by adding `n`, so `n` is a translation
    coordinate along the `0`–`∞` axis rather than a label attached to it. ⚠ The content is
    `2 ^ (m + n) = 2 ^ m * 2 ^ n` — that `n ↦ 2 ^ n` is a homomorphism `ℤ → ℚ₂ˣ`, so the family is
    the INFINITE CYCLIC `2 ^ ℤ`. It is not a "one-parameter subgroup": that is archimedean-Lie
    vocabulary and `ℚ₂ˣ` is totally disconnected. -/
theorem rScale_add (m n : ℤ) (z : Sphere) : rScale m (rScale n z) = rScale (m + n) z := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => simp [zpow_add₀ h2, mul_assoc]

/-- **The swap reverses the translation:** conjugating a scaling by the pole-exchanging inversion
    negates its parameter. This is the one statement that needs BOTH maps, and it is why they belong
    in one file: `rInv` is not merely another self-map of the sphere, it acts on the translations. -/
theorem rInv_conj_rScale (n : ℤ) (z : Sphere) :
    rInv (rScale n (rInv z)) = rScale (-n) z := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
      by_cases hx : x = 0
      · subst hx; simp
      · have hz : (2 : ℚ_[2]) ^ n * x⁻¹ ≠ 0 :=
          mul_ne_zero (zpow_ne_zero _ h2) (inv_ne_zero hx)
        rw [rInv_coe_ne hx, rScale_coe, rInv_coe_ne hz, rScale_coe, mul_inv, inv_inv,
          ← zpow_neg]

/-- `rScale` IS the Mathlib action of `diag(2 ^ n, 1)`. Anonymous: it declares nothing and owes no
    purity entry, and it stops compiling if the identification ever fails. -/
example (n : ℤ) (z : Sphere) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(2 : ℚ_[2]) ^ n, 0; 0, 1]
      (by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, ne_eq]
          exact zpow_ne_zero _ (by norm_num))) • z = rScale n z := by
  induction z using OnePoint.rec with
  | infty =>
      rw [OnePoint.smul_infty_eq_ite]
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, rScale]
  | coe x =>
      rw [OnePoint.smul_some_eq_ite]
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, rScale]

/-- `rInv` IS the Mathlib action of the Weyl element, `0 ↦ ∞` branch included. -/
example (z : Sphere) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℚ_[2]), 1; 1, 0]
      (by simp [Matrix.det_fin_two_of])) • z = rInv z := by
  induction z using OnePoint.rec with
  | infty =>
      rw [OnePoint.smul_infty_eq_ite]
      simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, rInv]
  | coe x =>
      rw [OnePoint.smul_some_eq_ite]
      by_cases hx : x = 0
      · subst hx; simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, rInv]
      · rw [rInv_coe_ne hx]
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, hx, one_div]

/-! ### § VI. The parameter is a COORDINATE, and the scalings are a group action

`rScale_add` makes the parameter additive under composition. This section is why that parameter is a
*coordinate on the carrier* rather than a label on the maps: it moves the 2-adic valuation one for
one. ⚠ `Padic.valuation` is the NEGATIVE logarithm of the norm (`Padic.norm_eq_zpow_neg_valuation`:
`‖x‖ = p ^ (-x.valuation)`), so valuation rises exactly as the norm falls.

Mathlib supplies the arithmetic; the axiom-footprint fence is in
`ZeroParadox/Valuation/RiemannSphere.md`. -/

/-- **The scaling shifts the valuation by exactly `n`** — what makes `n` a coordinate read off the
    carrier rather than a label on the map. The choice-free twin on ℕ is `v2_scale_nat`
    (`ZeroParadox/Valuation/PricedPadicInterface.lean`); the axiom-footprint fence and the unguarded
    `Padic.addValuation` variant are in `ZeroParadox/Valuation/RiemannSphere.md`. -/
theorem rScale_valuation (n : ℤ) {x : ℚ_[2]} (hx : x ≠ 0) :
    ((2 : ℚ_[2]) ^ n * x).valuation = n + x.valuation := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  rw [Padic.valuation_mul (zpow_ne_zero _ h2) hx, Padic.valuation_zpow]
  norm_num

/-- `rScale 0` is the identity. With `rScale_add` this makes the scalings a genuine `ℤ`-indexed
    group action on the sphere rather than a mere family of maps. -/
theorem rScale_zero : rScale 0 = id := by
  funext z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => simp

/-- The scaling as a homeomorphism, mirroring `rInvHomeo`. Continuity is inherited through
    `onePointCongr`; unlike `rInv` no work is needed at `∞`, which it never receives a finite point at. -/
noncomputable def rScaleHomeo (n : ℤ) : Sphere ≃ₜ Sphere :=
  Homeomorph.onePointCongr (Homeomorph.mulLeft₀ ((2 : ℚ_[2]) ^ n) (zpow_ne_zero _ (by norm_num)))

theorem rScaleHomeo_apply (n : ℤ) (z : Sphere) : rScaleHomeo n z = rScale n z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => rfl

theorem continuous_rScale (n : ℤ) : Continuous (rScale n) := by
  have h : ⇑(rScaleHomeo n) = rScale n := funext (rScaleHomeo_apply n)
  exact h ▸ (rScaleHomeo n).continuous

end ZeroParadox

/-! ## Axiom Purity Check (enable per theorem once proved) -/
section PurityCheck
open ZeroParadox
#print axioms rInv_involutive
#print axioms continuous_rInv
#print axioms rInv_swaps
-- § V: the pole-FIXING maps. `rScale_add` is the infinite-cyclic property; `rInv_conj_rScale` is the
-- only statement here that consumes both maps at once; `stabiliser_is_bigger` is the NO-GO gauge.
#print axioms rScale
#print axioms rScale_infty
#print axioms rScale_coe
#print axioms rScale_fixes_poles
#print axioms stabiliser_is_bigger
#print axioms rScale_add
#print axioms rInv_conj_rScale
-- § VI: the parameter as a COORDINATE, and the action packaged.
#print axioms rScale_valuation
#print axioms rScale_zero
#print axioms rScaleHomeo
#print axioms rScaleHomeo_apply
#print axioms continuous_rScale
end PurityCheck
