import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.NumberTheory.Padics.ProperSpace
import ZeroParadox.Die
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
- Opening (unheaded) `rInv`, `continuous_rInv`, `rInvHomeo`, `rInv_swaps` — inversion, the 0↔∞ swap.
- § V–VI `rScale`, `rInv_conj_rScale`, `rScale_valuation` — pole-fixing scalings, a valuation coordinate.
- § VII–VIII `sNorm`, `rInvRelIso`, `unitDouble_reach_iff` — the norm preorder; unit and doubling moves.
- § IX `upV`, `downV`, `upClosure`, `rInv_conj_upV` — rounding the valuation to a landing; the flip.
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

/-! ### § VII. A norm view of the sphere, and `rInv` as the change to the reversed view -/

/-- `Statement:` the extended norm on the sphere: `‖x‖₊` at `x`, and ⊤ of `ℝ≥0∞` at `∞`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's extended norm `‖·‖ₑ` is defined on normed
-- types, and `OnePoint ℚ_[2]` carries no norm; the dated search is in `LEAN_CUSTOM_REGISTRY.md`.
noncomputable def sNorm : Sphere → ENNReal
  | (∞ : Sphere) => ⊤
  | OnePoint.some x => (‖x‖₊ : ENNReal)

/-- `Statement:` `sNorm (rInv s) = (sNorm s)⁻¹` at every point of the sphere, `0` and `∞` included. -/
theorem sNorm_rInv (s : Sphere) : sNorm (rInv s) = (sNorm s)⁻¹ := by
  induction s using OnePoint.rec with
  | infty => simp [sNorm, rInv_infty]
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [sNorm, rInv_zero]
    · rw [rInv_coe_ne hx]
      simp only [sNorm, nnnorm_inv]
      rw [ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hx)]

/-- `Statement:` `rInv` reverses the preorder lifted along `sNorm`. -/
theorem rInv_reverses (a b : Sphere) : sNorm (rInv a) ≤ sNorm (rInv b) ↔ sNorm b ≤ sNorm a := by
  rw [sNorm_rInv, sNorm_rInv, ENNReal.inv_le_inv]

/-- `Statement:` `rInvHomeo` as a Mathlib `RelIso` from the preorder lifted along `sNorm` to its
    reverse. -/
noncomputable def rInvRelIso :
    (fun a b : Sphere => sNorm a ≤ sNorm b) ≃r (fun a b : Sphere => sNorm b ≤ sNorm a) where
  toEquiv := rInvHomeo.toEquiv
  map_rel_iff' := by
    intro a b
    show sNorm (rInv b) ≤ sNorm (rInv a) ↔ sNorm a ≤ sNorm b
    exact rInv_reverses b a

/-- `Statement:` in the preorder lifted along `sNorm`, `0` is least and `∞` greatest; `0 ≠ ∞`; and
    `rInv` exchanges them. -/
theorem sphere_exchange :
    @IsBot Sphere (Preorder.lift sNorm).toLE (OnePoint.some 0) ∧
    @IsTop Sphere (Preorder.lift sNorm).toLE ∞ ∧
    (OnePoint.some (0 : ℚ_[2]) : Sphere) ≠ ∞ ∧
    rInv (OnePoint.some 0) = ∞ ∧ rInv ∞ = OnePoint.some 0 :=
  ⟨fun s => by show sNorm (OnePoint.some 0) ≤ sNorm s; simp [sNorm],
   fun s => by show sNorm s ≤ sNorm ∞; simp [sNorm],
   OnePoint.coe_ne_infty 0, rInv_zero, rInv_infty⟩

/-- `Statement:` for every motion on the sphere (`ZeroParadox/Die.lean`), OVER raises in the preorder
    lifted along `sNorm ∘ rInv` iff it lowers in the preorder lifted along `sNorm`. -/
theorem sphere_polarity_swap (M : Motion Sphere) :
    @Motion.StepRaises Sphere M (Preorder.lift (sNorm ∘ rInv)).toLE ↔
      @Motion.StepLowers Sphere M (Preorder.lift sNorm).toLE :=
  Motion.stepRaises_iff_of_dual (Preorder.lift sNorm).toLE (Preorder.lift (sNorm ∘ rInv)).toLE
    (fun x y => rInv_reverses x y) M

/-! ### § VIII. Sideways, and up by valuation: unit multiplication and doubling on ℚ₂

`Reading:` **CARRIER** — on nonzero points the mutually reachable classes of `unitDoubleStep` are the
valuation shells (`unitDouble_mutual_iff`), ordered one way by valuation (`unitDouble_reach_iff`);
every move fixes `0` of `ℚ_[2]`, its own one-point class (`unitDouble_zero_own_class`). Doubling raises
valuation and halves the norm: down toward `0` of `ℚ_[2]` in the `sNorm` preorder (§ VII).

Standard frame, on nonzero points only: the divisibility order of a discrete valuation ring; at `0`
of `ℚ_[2]` the two orders part. Both are the `example`s after `unitDouble_zero_own_class`. -/

/-- `Statement:` one move multiplies by a unit (norm `1`) or by `2`. -/
def unitDoubleStep (x y : ℚ_[2]) : Prop := (∃ u : ℚ_[2], ‖u‖ = 1 ∧ y = u * x) ∨ y = 2 * x

/-- `Statement:` from a nonzero `x`, every point reachable by `unitDoubleStep` is nonzero and has
    valuation at least `x.valuation`. -/
theorem unitDouble_reach_mono {x y : ℚ_[2]} (hx : x ≠ 0)
    (h : Relation.ReflTransGen unitDoubleStep x y) : y ≠ 0 ∧ x.valuation ≤ y.valuation := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hv2 : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2); exact_mod_cast this
  induction h with
  | refl => exact ⟨hx, le_rfl⟩
  | tail _ hm ih =>
    obtain ⟨hb, hv⟩ := ih
    rcases hm with ⟨u, hu, rfl⟩ | rfl
    · have hu0 : u ≠ 0 := by rintro rfl; simp at hu
      have huv : u.valuation = 0 := by
        have h1 := (Padic.norm_le_one_iff_val_nonneg u).1 hu.le
        have h2 := (Padic.norm_le_one_iff_val_nonneg u⁻¹).1 (by rw [norm_inv, hu, inv_one])
        rw [Padic.valuation_inv] at h2; omega
      refine ⟨mul_ne_zero hu0 hb, ?_⟩
      rw [Padic.valuation_mul hu0 hb, huv]; omega
    · refine ⟨mul_ne_zero h2 hb, ?_⟩
      rw [Padic.valuation_mul h2 hb, hv2]; omega

/-- `Statement:` on nonzero points, `y` is reachable from `x` iff `x.valuation ≤ y.valuation`. -/
theorem unitDouble_reach_iff {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    Relation.ReflTransGen unitDoubleStep x y ↔ x.valuation ≤ y.valuation := by
  refine ⟨fun h => (unitDouble_reach_mono hx h).2, fun h => ?_⟩
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hv2 : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2); exact_mod_cast this
  have hdbl : ∀ n : ℕ, Relation.ReflTransGen unitDoubleStep x (2 ^ n * x) := by
    intro n
    induction n with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ n ih => exact ih.tail (Or.inr (by rw [pow_succ]; ring))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, y.valuation = x.valuation + n :=
    ⟨(y.valuation - x.valuation).toNat, by omega⟩
  set u := y / (2 ^ n * x) with hu_def
  have hd : (2 : ℚ_[2]) ^ n * x ≠ 0 := mul_ne_zero (pow_ne_zero _ h2) hx
  have huv : u.valuation = 0 := by
    rw [hu_def, div_eq_mul_inv, Padic.valuation_mul hy (inv_ne_zero hd), Padic.valuation_inv,
      Padic.valuation_mul (pow_ne_zero _ h2) hx, Padic.valuation_pow, hv2, hn]; ring
  have hu0 : u ≠ 0 := div_ne_zero hy hd
  have hun : ‖u‖ = 1 := by rw [Padic.norm_eq_zpow_neg_valuation hu0, huv]; simp
  exact (hdbl n).tail (Or.inl ⟨u, hun, by rw [hu_def, div_mul_cancel₀ _ hd]⟩)

/-- `Statement:` two nonzero points reach each other iff they have the same valuation. -/
theorem unitDouble_mutual_iff {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (Relation.ReflTransGen unitDoubleStep x y ∧ Relation.ReflTransGen unitDoubleStep y x) ↔
      x.valuation = y.valuation := by
  rw [unitDouble_reach_iff hx hy, unitDouble_reach_iff hy hx]; omega

/-- `Statement:` no nonzero point reaches `0` of `ℚ_[2]`, and `0` reaches only itself. -/
theorem unitDouble_zero_own_class (x : ℚ_[2]) :
    (x ≠ 0 → ¬ Relation.ReflTransGen unitDoubleStep x 0) ∧
      (Relation.ReflTransGen unitDoubleStep 0 x → x = 0) := by
  refine ⟨fun hx h => (unitDouble_reach_mono hx h).1 rfl, fun h => ?_⟩
  induction h with
  | refl => rfl
  | tail _ hm ih =>
    subst ih
    rcases hm with ⟨u, _, rfl⟩ | rfl <;> simp

-- Statement: on nonzero points `x` reaches `y` iff `y / x` is a 2-adic integer, the divisibility
-- order of the discrete valuation ring `ℤ_[2]` (Mathlib `IsDiscreteValuationRing.addVal_le_iff_dvd`,
-- `PadicInt.unitCoeff_spec`).
example {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    Relation.ReflTransGen unitDoubleStep x y ↔ ‖y / x‖ ≤ 1 := by
  rw [unitDouble_reach_iff hx hy, Padic.norm_le_one_iff_val_nonneg, div_eq_mul_inv,
    Padic.valuation_mul hy (inv_ne_zero hx), Padic.valuation_inv]; omega

-- Statement: control, at `0` of `ℚ_[2]` the orders part: `1` divides `0` in `ℤ_[2]` and `0 / 1` is a
-- 2-adic integer, yet `1` does not reach `0`: divisibility puts `0` on top, reachability in its own
-- class (`unitDouble_zero_own_class`).
example :
    (1 : ℤ_[2]) ∣ 0 ∧ ‖(0 : ℚ_[2]) / 1‖ ≤ 1 ∧ ¬ Relation.ReflTransGen unitDoubleStep 1 0 :=
  ⟨dvd_zero 1, by simp, (unitDouble_zero_own_class 1).1 one_ne_zero⟩

/-- `Statement:` on nonzero points, `x` reaches `y` iff `y⁻¹` reaches `x⁻¹`.
    `Reading:` **INVERSION** — reachability is the valuation order (`unitDouble_reach_iff`) and field
    inversion negates valuation, so it reverses the order, as any valuation-negating map would. On
    nonzero points field inversion agrees with `rInv` (`rInv_coe_ne`); compare `rInv_conj_rScale`. -/
theorem unitDouble_reach_inv {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    Relation.ReflTransGen unitDoubleStep x y ↔ Relation.ReflTransGen unitDoubleStep y⁻¹ x⁻¹ := by
  rw [unitDouble_reach_iff hx hy, unitDouble_reach_iff (inv_ne_zero hy) (inv_ne_zero hx),
    Padic.valuation_inv, Padic.valuation_inv]
  omega

-- Statement: control, with the unit leg alone, nonzero `x` reaches nonzero `y` iff they have equal
-- valuation; compare `unitDouble_reach_iff`, where the doubling leg adds the climb between shells.
example {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    Relation.ReflTransGen (fun a b : ℚ_[2] => ∃ u : ℚ_[2], ‖u‖ = 1 ∧ b = u * a) x y ↔
      x.valuation = y.valuation := by
  constructor
  · intro h
    suffices ∀ z, Relation.ReflTransGen (fun a b : ℚ_[2] => ∃ u : ℚ_[2], ‖u‖ = 1 ∧ b = u * a) x z →
        z ≠ 0 ∧ z.valuation = x.valuation from (this y h).2.symm
    intro z hz
    induction hz with
    | refl => exact ⟨hx, rfl⟩
    | tail _ hm ih =>
      obtain ⟨hb, hv⟩ := ih
      obtain ⟨u, hu, rfl⟩ := hm
      have hu0 : u ≠ 0 := by rintro rfl; simp at hu
      have huv : u.valuation = 0 := by
        have h1 := (Padic.norm_le_one_iff_val_nonneg u).1 hu.le
        have h2 := (Padic.norm_le_one_iff_val_nonneg u⁻¹).1 (by rw [norm_inv, hu, inv_one])
        rw [Padic.valuation_inv] at h2; omega
      refine ⟨mul_ne_zero hu0 hb, ?_⟩
      rw [Padic.valuation_mul hu0 hb, huv]; omega
  · intro h
    have hd : y / x ≠ 0 := div_ne_zero hy hx
    have hv : (y / x).valuation = 0 := by
      rw [div_eq_mul_inv, Padic.valuation_mul hy (inv_ne_zero hx), Padic.valuation_inv]; omega
    exact Relation.ReflTransGen.single
      ⟨y / x, by rw [Padic.norm_eq_zpow_neg_valuation hd, hv]; simp, (div_mul_cancel₀ y hx).symm⟩

/-! #### The mirror: the unit ball against its image under inversion -/

-- Statement: level 0, for nonzero `x`, `x` and `x⁻¹` both have valuation `≥ 0` iff `x.valuation = 0`.
-- The proof does not consume `x ≠ 0`; at `0` of `ℚ_[2]` it would hold only by `Padic.valuation 0 = 0`.
example {x : ℚ_[2]} (_hx : x ≠ 0) :
    (0 ≤ x.valuation ∧ 0 ≤ (x⁻¹).valuation) ↔ x.valuation = 0 := by
  rw [Padic.valuation_inv]; omega

-- Statement: control, for nonzero `x`, moving the ball to level `k > 0` without moving the inversion
-- empties the overlap. The proof does not consume `x ≠ 0`, for the reason above.
example (k : ℤ) (hk : 0 < k) {x : ℚ_[2]} (_hx : x ≠ 0) :
    ¬ (k ≤ x.valuation ∧ k ≤ (x⁻¹).valuation) := by
  rw [Padic.valuation_inv]; omega

-- Statement: control, at level `k < 0` the same overlap holds both `2 ^ k` and `1`, two valuations.
example (k : ℤ) (hk : k < 0) :
    (k ≤ ((2 : ℚ_[2]) ^ k).valuation ∧ k ≤ (((2 : ℚ_[2]) ^ k)⁻¹).valuation) ∧
    (k ≤ (1 : ℚ_[2]).valuation ∧ k ≤ ((1 : ℚ_[2])⁻¹).valuation) := by
  have h := rScale_valuation k (one_ne_zero : (1 : ℚ_[2]) ≠ 0)
  rw [mul_one] at h
  rw [Padic.valuation_inv, Padic.valuation_inv, h]
  simp; omega

-- Statement: moving the ball AND conjugating the inversion by `2 ^ k`, the overlap on nonzero points
-- is exactly the valuation-`k` shell.
example (k : ℤ) {x : ℚ_[2]} (hx : x ≠ 0) :
    (k ≤ x.valuation ∧ k ≤ ((2 : ℚ_[2]) ^ k * ((2 : ℚ_[2]) ^ (-k) * x)⁻¹).valuation) ↔
      x.valuation = k := by
  have h2k : (2 : ℚ_[2]) ^ (-k) ≠ 0 := zpow_ne_zero _ (by norm_num)
  rw [rScale_valuation k (inv_ne_zero (mul_ne_zero h2k hx)), Padic.valuation_inv,
    rScale_valuation (-k) hx]
  omega

/-! ### § IX. Rounding to landings: UP, DOWN, and the flip

Order: the reverse of § VII's `sNorm` preorder, `0` of `ℚ_[2]` on top and `∞` of `Sphere` at the
bottom (on nonzero points, higher valuation higher); along `sNorm` itself up and down exchange.
`upClosure` is UP as a `ClosureOperator` there. Cell width `2`: the landings, UP's fixed points, are
`0` of `ℚ_[2]`, `∞` of `Sphere` and nonzero points of even valuation (`example` after `downV`).

Standard frame: on valuations UP is ceiling and DOWN floor onto the even integers (UP: `example`
after `downV`); `rInv_conj_upV` carries Mathlib's `Int.ceil_neg` / `Int.floor_neg` through `rInv`. -/

/-- `Statement:` UP: `∞ ↦ ∞` and `x ↦ 2 ^ (v mod 2) * x`, with `v` the valuation of `x`. -/
noncomputable def upV : Sphere → Sphere
  | (∞ : Sphere) => ∞
  | OnePoint.some x => OnePoint.some ((2 : ℚ_[2]) ^ (x.valuation % 2) * x)

/-- `Statement:` DOWN: `∞ ↦ ∞` and `x ↦ 2 ^ (-(v mod 2)) * x`, with `v` the valuation of `x`. -/
noncomputable def downV : Sphere → Sphere
  | (∞ : Sphere) => ∞
  | OnePoint.some x => OnePoint.some ((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x)

-- Statement: the fixed points of UP are exactly `∞` of `Sphere`, `0` of `ℚ_[2]`, and the nonzero
-- points of even valuation.
example (z : Sphere) : upV z = z ↔
    z = ∞ ∨ z = OnePoint.some 0 ∨ ∃ x : ℚ_[2], x ≠ 0 ∧ x.valuation % 2 = 0 ∧ z = OnePoint.some x := by
  induction z using OnePoint.rec with
  | infty => simp [upV]
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV]
    · constructor
      · intro h
        refine Or.inr (Or.inr ⟨x, hx, ?_, rfl⟩)
        have h' : (2 : ℚ_[2]) ^ (x.valuation % 2) * x = x := OnePoint.coe_injective h
        have := congrArg Padic.valuation h'
        rw [rScale_valuation _ hx] at this; omega
      · rintro (h | h | ⟨y, -, hv, h⟩)
        · exact absurd h (OnePoint.coe_ne_infty x)
        · exact absurd (OnePoint.coe_injective h) hx
        · obtain rfl := OnePoint.coe_injective h
          show OnePoint.some ((2 : ℚ_[2]) ^ (x.valuation % 2) * x) = _
          rw [hv, zpow_zero, one_mul]

-- Statement: on nonzero `x`, UP sends the valuation `v` to `2 * ⌈v / 2⌉`, the ceiling onto the even
-- integers.
example {x : ℚ_[2]} (hx : x ≠ 0) :
    ((2 : ℚ_[2]) ^ (x.valuation % 2) * x).valuation = 2 * ⌈(x.valuation : ℚ) / 2⌉ := by
  rw [rScale_valuation _ hx]
  have : ⌈(x.valuation : ℚ) / 2⌉ = (x.valuation + 1) / 2 := by
    rw [Int.ceil_eq_iff]
    constructor
    · rw [lt_div_iff₀ (by norm_num)]
      have : (((x.valuation + 1) / 2 : ℤ) - 1) * 2 < x.valuation := by omega
      exact_mod_cast this
    · rw [div_le_iff₀ (by norm_num)]
      have : x.valuation ≤ ((x.valuation + 1) / 2 : ℤ) * 2 := by omega
      exact_mod_cast this
  rw [this]; omega

-- Statement: on nonzero `x`, UP lands on an even valuation at or above `v`, and DOWN on one at or below.
example {x : ℚ_[2]} (hx : x ≠ 0) :
    ((2 : ℚ_[2]) ^ (x.valuation % 2) * x).valuation % 2 = 0 ∧
    x.valuation ≤ ((2 : ℚ_[2]) ^ (x.valuation % 2) * x).valuation ∧
    ((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x).valuation % 2 = 0 ∧
    ((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x).valuation ≤ x.valuation := by
  rw [rScale_valuation _ hx, rScale_valuation _ hx]; omega

/-- `Statement:` `rInv (upV (rInv z)) = downV z` at every point of `Sphere`.
    `Reading:` **INVERSION** — conjugating the round-up map by `rInv`, valuation-negating on nonzero
    points and order-reversing on the reverse `sNorm` preorder (§ IX head), gives the round-down map;
    compare `rInv_conj_rScale`. -/
theorem rInv_conj_upV (z : Sphere) : rInv (upV (rInv z)) = downV z := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  induction z using OnePoint.rec with
  | infty => simp [upV, downV]
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV, downV]
    · have hy : (2 : ℚ_[2]) ^ ((x⁻¹).valuation % 2) * x⁻¹ ≠ 0 :=
        mul_ne_zero (zpow_ne_zero _ h2) (inv_ne_zero hx)
      rw [rInv_coe_ne hx]
      show rInv (OnePoint.some ((2 : ℚ_[2]) ^ ((x⁻¹).valuation % 2) * x⁻¹)) =
        OnePoint.some ((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x)
      rw [rInv_coe_ne hy, Padic.valuation_inv, Int.neg_emod_two, mul_inv, inv_inv, ← zpow_neg]

/-- `Statement:` `upV z = downV (rScale 1 z)` at every point of `Sphere`. -/
theorem upV_eq_downV_rScale_one (z : Sphere) : upV z = downV (rScale 1 z) := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV, downV]
    · show OnePoint.some ((2 : ℚ_[2]) ^ (x.valuation % 2) * x) =
        OnePoint.some ((2 : ℚ_[2]) ^ (-(((2 : ℚ_[2]) ^ (1 : ℤ) * x).valuation % 2)) *
          ((2 : ℚ_[2]) ^ (1 : ℤ) * x))
      rw [rScale_valuation _ hx, ← mul_assoc, ← zpow_add₀ h2,
        show -(((1 : ℤ) + x.valuation) % 2) + 1 = x.valuation % 2 by omega]

/-- `Statement:` UP fixes every output of DOWN. -/
theorem upV_downV (z : Sphere) : upV (downV z) = downV z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV, downV]
    · show OnePoint.some ((2 : ℚ_[2]) ^ (((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x).valuation % 2) *
          ((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x)) =
        OnePoint.some ((2 : ℚ_[2]) ^ (-(x.valuation % 2)) * x)
      rw [rScale_valuation _ hx, show (-(x.valuation % 2) + x.valuation) % 2 = 0 by omega,
        zpow_zero, one_mul]

/-- `Statement:` DOWN fixes every output of UP. -/
theorem downV_upV (z : Sphere) : downV (upV z) = upV z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV, downV]
    · show OnePoint.some ((2 : ℚ_[2]) ^ (-(((2 : ℚ_[2]) ^ (x.valuation % 2) * x).valuation % 2)) *
          ((2 : ℚ_[2]) ^ (x.valuation % 2) * x)) =
        OnePoint.some ((2 : ℚ_[2]) ^ (x.valuation % 2) * x)
      rw [rScale_valuation _ hx, show (x.valuation % 2 + x.valuation) % 2 = 0 by omega,
        neg_zero, zpow_zero, one_mul]

/-- `Statement:` on nonzero points, `sNorm x ≤ sNorm y` iff `y.valuation ≤ x.valuation`. -/
theorem sNorm_coe_le_iff {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    sNorm (OnePoint.some x) ≤ sNorm (OnePoint.some y) ↔ y.valuation ≤ x.valuation := by
  show ((‖x‖₊ : NNReal) : ENNReal) ≤ ((‖y‖₊ : NNReal) : ENNReal) ↔ _
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm,
    Padic.norm_eq_zpow_neg_valuation hx, Padic.norm_eq_zpow_neg_valuation hy,
    zpow_le_zpow_iff_right₀ (by norm_num), neg_le_neg_iff]

/-- `Statement:` UP as a Mathlib `ClosureOperator` (monotone, extensive, idempotent) on the reverse
    of § VII's `sNorm` preorder, where `0` of `ℚ_[2]` is top and `∞` of `Sphere` bottom.
    `Reading:` **INVERSION** — through an order-reversing map a closure conjugates to a closure on
    the order dual (`ClosureOperator.conjBy`), the corpus's kernel form (`keepAboveKernel`,
    `pruneKernel`); `rInv_conj_upV` has that shape. -/
noncomputable def upClosure :
    @ClosureOperator Sphere (Preorder.lift (fun s => OrderDual.toDual (sNorm s))) :=
  letI : Preorder Sphere := Preorder.lift (fun s => OrderDual.toDual (sNorm s))
  { toFun := upV
    monotone' := by
      intro a b hab
      change sNorm b ≤ sNorm a at hab
      change sNorm (upV b) ≤ sNorm (upV a)
      induction a using OnePoint.rec with
      | infty => exact le_top
      | coe x =>
        induction b using OnePoint.rec with
        | infty => exact absurd (top_le_iff.mp hab) (by simp [sNorm])
        | coe y =>
          by_cases hy : y = 0
          · subst hy; simp [upV, sNorm]
          by_cases hx : x = 0
          · subst hx
            exfalso; apply hy
            simpa [sNorm] using hab
          · rw [sNorm_coe_le_iff hy hx] at hab
            show sNorm (OnePoint.some ((2 : ℚ_[2]) ^ (y.valuation % 2) * y)) ≤
              sNorm (OnePoint.some ((2 : ℚ_[2]) ^ (x.valuation % 2) * x))
            rw [sNorm_coe_le_iff (mul_ne_zero (zpow_ne_zero _ (by norm_num)) hy)
              (mul_ne_zero (zpow_ne_zero _ (by norm_num)) hx),
              rScale_valuation _ hx, rScale_valuation _ hy]
            omega
    le_closure' := by
      intro a
      change sNorm (upV a) ≤ sNorm a
      induction a using OnePoint.rec with
      | infty => exact le_rfl
      | coe x =>
        by_cases hx : x = 0
        · subst hx; simp [upV]
        · show sNorm (OnePoint.some ((2 : ℚ_[2]) ^ (x.valuation % 2) * x)) ≤ sNorm (OnePoint.some x)
          rw [sNorm_coe_le_iff (mul_ne_zero (zpow_ne_zero _ (by norm_num)) hx) hx,
            rScale_valuation _ hx]
          omega
    idempotent' := fun a => by
      show upV (upV a) = upV a
      rw [← downV_upV a, upV_downV] }

/-- `Statement:` UP commutes with `rScale 2`, a zoom by one full cell. -/
theorem upV_rScale_two (z : Sphere) : upV (rScale 2 z) = rScale 2 (upV z) := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV]
    · show OnePoint.some ((2 : ℚ_[2]) ^ (((2 : ℚ_[2]) ^ (2 : ℤ) * x).valuation % 2) *
          ((2 : ℚ_[2]) ^ (2 : ℤ) * x)) =
        OnePoint.some ((2 : ℚ_[2]) ^ (2 : ℤ) * ((2 : ℚ_[2]) ^ (x.valuation % 2) * x))
      rw [rScale_valuation _ hx, show ((2 : ℤ) + x.valuation) % 2 = x.valuation % 2 by omega,
        mul_left_comm]

/-- `Statement:` on every output of UP, one `rScale 1` followed by UP equals `rScale 2`. -/
theorem upV_rScale_one_upV (z : Sphere) : upV (rScale 1 (upV z)) = rScale 2 (upV z) := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    by_cases hx : x = 0
    · subst hx; simp [upV]
    · have hy : (2 : ℚ_[2]) ^ (x.valuation % 2) * x ≠ 0 := mul_ne_zero (zpow_ne_zero _ h2) hx
      show OnePoint.some ((2 : ℚ_[2]) ^
          (((2 : ℚ_[2]) ^ (1 : ℤ) * ((2 : ℚ_[2]) ^ (x.valuation % 2) * x)).valuation % 2) *
          ((2 : ℚ_[2]) ^ (1 : ℤ) * ((2 : ℚ_[2]) ^ (x.valuation % 2) * x))) =
        OnePoint.some ((2 : ℚ_[2]) ^ (2 : ℤ) * ((2 : ℚ_[2]) ^ (x.valuation % 2) * x))
      rw [rScale_valuation _ hy, rScale_valuation _ hx,
        show ((1 : ℤ) + (x.valuation % 2 + x.valuation)) % 2 = 1 by omega,
        ← mul_assoc, ← zpow_add₀ h2]
      norm_num

-- Statement: control, UP does not commute with `rScale 1`: at `1` of `ℚ_[2]` the two composites
-- differ.
example : upV (rScale 1 (OnePoint.some 1)) ≠ rScale 1 (upV (OnePoint.some 1)) := by
  have hv : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2); exact_mod_cast this
  show OnePoint.some ((2 : ℚ_[2]) ^ (((2 : ℚ_[2]) ^ (1 : ℤ) * 1).valuation % 2) *
      ((2 : ℚ_[2]) ^ (1 : ℤ) * 1)) ≠
    OnePoint.some ((2 : ℚ_[2]) ^ (1 : ℤ) * ((2 : ℚ_[2]) ^ ((1 : ℚ_[2]).valuation % 2) * 1))
  simp only [mul_one, zpow_one, Padic.valuation_one, EuclideanDomain.zero_mod, zpow_zero, hv]
  intro h
  have := OnePoint.coe_injective h
  norm_num at this

-- Statement: control, UP does not commute with `rInv`: at `2` of `ℚ_[2]` the two composites
-- differ.
example : upV (rInv (OnePoint.some 2)) ≠ rInv (upV (OnePoint.some 2)) := by
  have hv : (2 : ℚ_[2]).valuation = 1 := by
    have := Padic.valuation_p (p := 2); exact_mod_cast this
  have h4 : (2 : ℚ_[2]) ^ ((1 : ℤ) % 2) * 2 ≠ 0 := by norm_num
  rw [rInv_coe_ne (by norm_num)]
  show OnePoint.some ((2 : ℚ_[2]) ^ (((2 : ℚ_[2])⁻¹).valuation % 2) * (2 : ℚ_[2])⁻¹) ≠
    rInv (OnePoint.some ((2 : ℚ_[2]) ^ ((2 : ℚ_[2]).valuation % 2) * 2))
  rw [Padic.valuation_inv, hv, rInv_coe_ne h4]
  intro h
  have := OnePoint.coe_injective h
  norm_num at this

/-- `Statement:` for nonzero `u`, conjugating multiplication by `u` (as in `stabiliser_is_bigger`) by
    `rInv` gives multiplication by `u⁻¹`, at every point of `Sphere`.
    `Reading:` **INVERSION** — the twin of `rInv_conj_rScale` for an arbitrary nonzero factor, units
    of norm `1` included; in § V's Möbius terms (`OnePoint.instGLAction`, § V's two `example`s), the
    Weyl element conjugating `diag(u, 1)`. -/
theorem rInv_conj_mulLeft (u : ℚ_[2]) (hu : u ≠ 0) (z : Sphere) :
    rInv ((Homeomorph.onePointCongr (Homeomorph.mulLeft₀ u hu)) (rInv z)) =
      (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ u⁻¹ (inv_ne_zero hu))) z := by
  induction z using OnePoint.rec with
  | infty =>
    rw [rInv_infty]
    show rInv (OnePoint.some (u * 0)) = ∞
    rw [mul_zero, rInv_zero]
  | coe x =>
    by_cases hx : x = 0
    · subst hx
      rw [rInv_zero]
      show rInv ∞ = OnePoint.some (u⁻¹ * 0)
      rw [mul_zero, rInv_infty]
    · rw [rInv_coe_ne hx]
      show rInv (OnePoint.some (u * x⁻¹)) = OnePoint.some (u⁻¹ * x)
      rw [rInv_coe_ne (mul_ne_zero hu (inv_ne_zero hx)), mul_inv, inv_inv]

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
-- § VII: the norm view and its reversal.
#print axioms sNorm
#print axioms sNorm_rInv
#print axioms rInv_reverses
#print axioms rInvRelIso
#print axioms sphere_exchange
#print axioms sphere_polarity_swap
-- § VIII: sideways (unit) and up by valuation (doubling) on ℚ₂.
#print axioms unitDoubleStep
#print axioms unitDouble_reach_mono
#print axioms unitDouble_reach_iff
#print axioms unitDouble_mutual_iff
#print axioms unitDouble_zero_own_class
#print axioms unitDouble_reach_inv
-- § IX: rounding the valuation to a landing, and the flip between UP and DOWN.
#print axioms upV
#print axioms downV
#print axioms rInv_conj_upV
#print axioms upV_eq_downV_rScale_one
#print axioms upV_downV
#print axioms downV_upV
#print axioms sNorm_coe_le_iff
#print axioms upClosure
#print axioms upV_rScale_two
#print axioms upV_rScale_one_upV
#print axioms rInv_conj_mulLeft
end PurityCheck
