-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): one tape ensemble, `fairTape`, the law of the maximum-entropy coin (`trials_eq_fairTape_of_maxEntropy`), almost all of whose members are incompressible, with ⊥ of `ℕ → Bool` a non-random limit of its random firing tapes; and the control that a set containing both faces is null. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.MaxEntropy
import ZeroParadox.Information.PoleWithinEnsemble
import Mathlib.Tactic

/-!
# One ensemble, two faces: the law and its members

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
`tape_totality_two_faces` bundles the uniqueness of the maximum-entropy coin (its `trials` is `fairTape`,
`trials_eq_fairTape_of_maxEntropy`) with three results about `fairTape`; the control
`both_faces_in_null_set` shows a set holding ⊥ of `ℕ → Bool` and a random tape is null.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory Filter Topology

/-- `Statement:` exactly one `p` has `binEntropy p = log 2` (its `trials` is `fairTape` by
`trials_eq_fairTape_of_maxEntropy`, not conjoined here); for each prefix-free decoder `D`,
`fairTape`-almost every tape is incompressible for `D`; ⊥ of `ℕ → Bool` is not Martin-Löf random
for `fairTape`, and is in the closure of `randFiring (1/2)`. -/
theorem tape_totality_two_faces :
    (∃ p : NNReal, Real.binEntropy (p : ℝ) = Real.log 2 ∧ 0 < p ∧ p ≤ 1 ∧
        ∀ q : NNReal, Real.binEntropy (q : ℝ) = Real.log 2 → q = p) ∧
    (∀ (D : List Bool → Option (List Bool)) (_ : PrefixFree {d | (D d).isSome}),
        ∀ᵐ w ∂fairTape, ∃ c, ∀ d x, D d = some x → w ∈ prefixCyl x → x.length < d.length + c) ∧
    ¬ MLRandom fairTape (⊥ : ℕ → Bool) ∧
    (⊥ : ℕ → Bool) ∈ closure (randFiring (1/2) (by norm_num)) :=
  ⟨maximizer_admissible, fun D hD => ae_incompressible D hD,
    bot_not_MLRandom (1/2) _ (by norm_num),
    bot_mem_closure_randFiring (1/2) _ (by norm_num) (by norm_num)⟩

/-- `Statement:` every singleton of `ℕ → Bool` is `fairTape`-null: the standard fact that the
fair-coin product measure has no atoms. Mathlib's `MeasureTheory.Measure.infinitePi_singleton`
(`Mathlib/Probability/ProductMeasure.lean`) gives a singleton's mass as the product of its coordinate
masses; the proof here bounds it by `(1/2)^n` instead. -/
theorem fairTape_singleton_null (t : ℕ → Bool) : fairTape {t} = 0 := by
  have hle : ∀ n : ℕ, fairTape {t} ≤ ((1/2 : NNReal) : ENNReal) ^ n := fun n => by
    rw [← Finset.card_range n, ← fairTape_pi_singleton (Finset.range n) t]
    exact measure_mono fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw
      intro j _; exact Set.mem_singleton _
  have ht : Tendsto (fun n : ℕ => ((1/2 : NNReal) : ENNReal) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  exact le_antisymm (ge_of_tendsto' ht hle) zero_le

/-- `Statement:` CONTROL, some tape `w0` is Martin-Löf random for `fairTape`, ⊥ of `ℕ → Bool` is not,
and `{⊥, w0}` is `fairTape`-null. -/
theorem both_faces_in_null_set :
    ∃ w0, MLRandom fairTape w0 ∧ ¬ MLRandom fairTape (⊥ : ℕ → Bool) ∧
      fairTape ({⊥, w0} : Set (ℕ → Bool)) = 0 := by
  obtain ⟨w0, hw0⟩ := exists_MLRandom (1/2) (by norm_num)
  refine ⟨w0, hw0, bot_not_MLRandom (1/2) _ (by norm_num), ?_⟩
  rw [Set.insert_eq]
  exact measure_union_null (fairTape_singleton_null _) (fairTape_singleton_null _)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms tape_totality_two_faces
#print axioms fairTape_singleton_null
#print axioms both_faces_in_null_set
end PurityCheck
