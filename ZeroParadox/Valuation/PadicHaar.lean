import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# p-adic Haar measure on ℤ_p

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The measure foundation for the p-adic chart of the bottoms-interconnect map (base point 0 of
`ℤ_[p]`). It equips the compact group `ℤ_p` with its Borel σ-algebra and the additive Haar
**probability** measure (normalized so the whole space has measure `1`), and records the measure of
the standard norm-balls: `{x : ℤ_p | ‖x‖ ≤ p^(-n)}` is the additive subgroup `p^n ℤ_p` of index
`p^n`, so translation-invariance forces its measure to be `p^(-n)`. Built against this measure
downstream: `koopman` (`ZeroParadox/Valuation/PadicKoopman.lean`), `ergodic_odometer`, and the
Vladimirov operator of `vladimirov_gap`. Standard measure theory on a compact group; **no novelty is
claimed**. Prior art: the next block.

## Structure
- § I   Borel measurable-space structure on ℤ_p
- § II  The additive Haar probability measure
- § III Measure of the norm-balls
-/

/-! ## Prior art

FLT at commit `ee47fd2a` (read 2026-11-25, types not elaborated; FLT is outside this dependency closure,
so both are re-proved here; credit runs from FLT to this file). `FLT/HaarMeasure/MeasurableSpacePadics.lean`
(Dillies, Loeffler, 2024) builds the same measure: Borel `PadicInt.instMeasurableSpace`,
`PadicInt.instMeasureSpace := ⟨addHaarMeasure ⊤⟩`, `PadicInt.volume_univ`. `haarZp_ball` is the `x = pⁿ`,
`s = univ` case, stated as a norm-ball, of `PadicInt.volume_padicInt_smul : volume (x • s) = ‖x‖₊ * volume s`
(`FLT/HaarMeasure/HaarChar/Padic.lean`, Dillies, López-Contreras, 2024). Mathlib: not located as of
2026-11-25, searched `import Mathlib`, `#synth MeasurableSpace ℤ_[3]` (fails); its `AbstractMeasure :=
C(X, R) →L[R] E` (`Mathlib/NumberTheory/Padics/Measure/`) is continuous linear maps, not `MeasureTheory.Measure`. -/

namespace ZeroParadox

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

instance : Nonempty ℤ_[p] := ⟨0⟩

/-! ## § I — Borel measurable-space structure on ℤ_p -/

/-- Borel σ-algebra on `ℤ_p` (the metric/ultrametric Borel structure). No Mathlib `MeasurableSpace`
    instance on `ℤ_p` was located (2026-11-25, Prior art block), so we opt into the Borel one. -/
noncomputable instance : MeasurableSpace ℤ_[p] := borel _

instance : BorelSpace ℤ_[p] := ⟨rfl⟩

/-! ## § II — The additive Haar probability measure -/

/-- The additive Haar **probability** measure on the compact group `ℤ_p` (normalized so the whole
    space has measure `1`). Built from the generic compact-group Haar construction with the whole
    space `⊤` as the normalizing positive-compact set. -/
noncomputable def haarZp : Measure ℤ_[p] := Measure.addHaarMeasure ⊤

instance : IsProbabilityMeasure (haarZp (p := p)) :=
  ⟨by
    show Measure.addHaarMeasure (⊤ : PositiveCompacts ℤ_[p]) Set.univ = 1
    rw [← PositiveCompacts.coe_top (α := ℤ_[p])]
    exact Measure.addHaarMeasure_self⟩

/-- `haarZp` is an additive Haar measure (hence left-invariant), inherited from the underlying
    `addHaarMeasure ⊤`. -/
instance : (haarZp (p := p)).IsAddHaarMeasure := by
  unfold haarZp
  exact Measure.isAddHaarMeasure_addHaarMeasure ⊤

/-! ## § III — Measure of the norm-balls -/

/-- **Ball measure.** The norm-ball `{x : ℤ_p | ‖x‖ ≤ p^(-n)}` — equivalently the additive
    subgroup `p^n ℤ_p`, of index `p^n` — has Haar measure `p^(-n)`. This gives the ball indicators
    their lengths in `L²(ℤ_p, haarZp)` (`norm_ballIndicatorL2`). -/
theorem haarZp_ball (n : ℕ) :
    haarZp (p := p) {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))} = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  -- The ball is the additive subgroup underlying the ideal `(pⁿ)`.
  set H : AddSubgroup ℤ_[p] := (Ideal.span {(p : ℤ_[p]) ^ n}).toAddSubgroup with hHdef
  have hset : {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))} = (H : Set ℤ_[p]) := by
    ext x
    rw [Set.mem_setOf_eq, PadicInt.norm_le_pow_iff_mem_span_pow, hHdef]
    simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup]
  have hmeas : MeasurableSet (H : Set ℤ_[p]) := by
    rw [← hset]
    have hball : {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
        = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
      ext x; simp [Metric.mem_closedBall, dist_eq_norm]
    rw [hball]; exact measurableSet_closedBall
  -- The index of the ideal `(pⁿ)` in `ℤ_p` is `pⁿ`: it is the kernel of the surjection
  -- `toZModPow n : ℤ_p →+* ZMod pⁿ`, so `ℤ_p ⧸ (pⁿ) ≅ ZMod pⁿ`, which has `pⁿ` elements.
  have hindex : H.index = p ^ n := by
    haveI hNe : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
    have hsurj : Function.Surjective ⇑(PadicInt.toZModPow (p := p) n) := fun a =>
      ⟨(a.val : ℤ_[p]), by rw [map_natCast]; exact ZMod.natCast_rightInverse a⟩
    have hker : H = (PadicInt.toZModPow (p := p) n).toAddMonoidHom.ker := by
      rw [hHdef]
      ext x
      rw [Submodule.mem_toAddSubgroup, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
        AddMonoidHom.mem_ker]
      rfl
    rw [hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top_of_surjective _ hsurj,
      Nat.card_congr (AddSubgroup.topEquiv (G := ZMod (p ^ n))).toEquiv, Nat.card_zmod]
  haveI : H.FiniteIndex := ⟨by rw [hindex]; exact pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hkey := AddSubgroup.index_mul_measure H hmeas (haarZp (p := p))
  rw [hindex, measure_univ, Nat.cast_pow] at hkey
  have hpne : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast ‹Fact p.Prime›.out.pos.ne'
  have hp0 : (p : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero n hpne
  have hpt : (p : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have hkey' : (p : ℝ≥0∞) ^ n * haarZp (p := p) (H : Set ℤ_[p]) = 1 := hkey
  rw [hset]
  calc haarZp (p := p) (H : Set ℤ_[p])
      = ((p : ℝ≥0∞) ^ n)⁻¹ * ((p : ℝ≥0∞) ^ n * haarZp (p := p) (H : Set ℤ_[p])) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpt, one_mul]
    _ = ((p : ℝ≥0∞) ^ n)⁻¹ * 1 := by rw [hkey']
    _ = ((p : ℝ≥0∞) ^ n)⁻¹ := mul_one _

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` in `haarZp_ball`'s footprint is already in its statement: a theorem about the norm
on `ℤ_[p]` alone (`‖(0 : ℤ_[3])‖ = 0 := norm_zero`, scratch probe 2026-11-25) prints the same
footprint. Inherited from Mathlib, not a commitment of this file. -/
section PurityCheck
open ZeroParadox
#print axioms haarZp_ball
end PurityCheck
