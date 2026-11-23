-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the start bit and end bit of a tape `ℕ → Bool`, and the tapes whose tail from some position on is ⊥ of `ℕ → Bool` as one countable set, the local floors read as tapes. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.TowerTape
import Mathlib.Tactic

/-!
# The start bit, the end bit, and the tapes whose tail from some position on is ⊥ of `ℕ → Bool`

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
§ I: first `true` iff not ⊥ of `ℕ → Bool`; last `true` iff also eventually `false`. § II: the
eventually-`false` tapes are one set: shifted copies of {⊥}, `silentFrom`, the local floors through
`tapeIso`. § III: null under a constant coin `0 < p ≤ 1`, measure one under a summable coin.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory Filter

/-! ### § I. Start bit and end bit -/

/-- `Statement:` a tape has a first `true` iff it is not ⊥ of `ℕ → Bool`; both directions. The
first one is `Nat.find`, a first hitting time (`firedRun`).
`Reading:` the start bit, Tim's magic-bytes reading (2026-11-15): "In a file, you have magic bytes
that specify what comes after is a given type... Can we call the first heads up coin something like
that?" -/
theorem exists_startBit_iff (w : ℕ → Bool) : (∃ k, w k = true) ↔ w ≠ ⊥ := by
  constructor
  · rintro ⟨k, hk⟩ rfl; simp at hk
  · intro h; by_contra hc; push Not at hc
    exact h (funext fun k => by simpa using hc k)

/-- `Statement:` the tapes that are eventually `false`. -/
def eventuallyFalse : Set (ℕ → Bool) := {w | ∀ᶠ n in atTop, w n = false}

/-- `Statement:` `silentFrom N` is the set of tapes whose subtape from position `N` on is ⊥ of
`ℕ → Bool`. -/
theorem silentFrom_eq_shift_preimage (N : ℕ) :
    silentFrom N = shiftTape N ⁻¹' {(⊥ : ℕ → Bool)} := by
  ext w
  simp only [silentFrom, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    shiftTape]
  constructor
  · intro h n; exact h (N + n) (Nat.le_add_right N n)
  · intro h k hk; have := h (k - N); rwa [Nat.add_sub_cancel' hk] at this

/-- `Statement:` `eventuallyFalse = ⋃ N, silentFrom N`. -/
theorem eventuallyFalse_eq_iUnion_silentFrom : eventuallyFalse = ⋃ N, silentFrom N := by
  ext w; simp [eventuallyFalse, silentFrom, eventually_atTop]

/-- `Statement:` `eventuallyFalse = ⋃ k, shiftTape k ⁻¹' {⊥}`, ⊥ of `ℕ → Bool`. -/
theorem eventuallyFalse_eq_iUnion_shift :
    eventuallyFalse = ⋃ k, shiftTape k ⁻¹' {(⊥ : ℕ → Bool)} := by
  rw [eventuallyFalse_eq_iUnion_silentFrom]
  exact Set.iUnion_congr silentFrom_eq_shift_preimage

/-- `Statement:` `w` is eventually `false` iff it does not fire infinitely often; both directions. -/
theorem mem_eventuallyFalse_iff (w : ℕ → Bool) :
    w ∈ eventuallyFalse ↔ w ∉ Filter.limsup fires Filter.atTop := by
  rw [not_mem_limsup_fires_iff, eventuallyFalse_eq_iUnion_silentFrom, Set.mem_iUnion]

/-- `Statement:` a tape has a last `true` iff it is not ⊥ of `ℕ → Bool` and is eventually `false`;
both directions. `Reading:` the end bit. -/
theorem exists_lastBit_iff (w : ℕ → Bool) :
    (∃ k, w k = true ∧ ∀ n, k < n → w n = false) ↔ w ≠ ⊥ ∧ w ∈ eventuallyFalse := by
  constructor
  · rintro ⟨k, hk, hn⟩
    refine ⟨(exists_startBit_iff w).1 ⟨k, hk⟩, ?_⟩
    rw [eventuallyFalse_eq_iUnion_silentFrom, Set.mem_iUnion]
    exact ⟨k + 1, fun n hn' => hn n (by omega)⟩
  · rintro ⟨hb, he⟩
    rw [eventuallyFalse_eq_iUnion_silentFrom, Set.mem_iUnion] at he
    classical
    let N := Nat.find he
    have hN : w ∈ silentFrom N := Nat.find_spec he
    have hN0 : N ≠ 0 := by
      intro h0
      apply hb; funext k
      have := hN k (by rw [h0]; exact Nat.zero_le k)
      simpa using this
    refine ⟨N - 1, ?_, fun n hn => hN n (by omega)⟩
    by_contra hc
    have hc' : w (N - 1) = false := by simpa using hc
    have hmin := Nat.find_min he (show N - 1 < N by omega)
    apply hmin
    intro k hk
    rcases Nat.eq_or_lt_of_le hk with h | h
    · rw [← h]; exact hc'
    · exact hN k (by omega)

/-! ### § II. Returning to a floor, one set -/

/-- `Statement:` `eventuallyFalse` is the set of local floors `localBotEnd v` read through `tapeIso`;
the subtape of each after `v` is ⊥ of `ℕ → Bool` (`localFloor_subtape_pole_limit`).
`Reading:` Tim (2026-11-15): "If the all zero tape always exists... A returning to bottom like
this... Isn't this the representation of the all bottom tape within that specific localized
context?" -/
theorem eventuallyFalse_eq_range_localFloor :
    eventuallyFalse = Set.range (fun v : List (Fin 2) => tapeIso (localBotEnd v)) := by
  ext w
  constructor
  · intro hw
    rw [eventuallyFalse_eq_iUnion_silentFrom, Set.mem_iUnion] at hw
    obtain ⟨N, hN⟩ := hw
    refine ⟨List.ofFn (fun i : Fin N => digitBool.symm (w i)), ?_⟩
    funext k
    show tapeIso (localBotEnd _) k = w k
    rw [tapeIso_apply]
    simp only [localBotEnd, prependEnd, List.length_ofFn]
    by_cases hk : k < N
    · simp only [hk, ↓reduceIte]
      rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]
      cases h : w k <;> rfl
    · simp only [hk, ↓reduceIte]
      rw [hN k (by omega)]; rfl
  · rintro ⟨v, rfl⟩
    rw [eventuallyFalse_eq_iUnion_silentFrom, Set.mem_iUnion]
    refine ⟨v.length, fun k hk => ?_⟩
    show tapeIso (localBotEnd v) k = false
    rw [tapeIso_apply]
    simp [localBotEnd, prependEnd, show ¬ k < v.length by omega, botEnd]

/-- `Statement:` `eventuallyFalse` is countable. -/
theorem eventuallyFalse_countable : eventuallyFalse.Countable := by
  rw [eventuallyFalse_eq_range_localFloor]; exact Set.countable_range _

/-- `Statement:` `eventuallyFalse` is measurable. -/
theorem measurableSet_eventuallyFalse : MeasurableSet eventuallyFalse := by
  rw [eventuallyFalse_eq_iUnion_shift]
  exact MeasurableSet.iUnion fun k => measurable_shiftTape k (measurableSet_singleton _)

/-- `Statement:` if `0 < p ≤ 1`, `eventuallyFalse` is `trials p hp`-null: a countable union of
`trials_localFloor_null`. -/
theorem trials_eventuallyFalse_null (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp eventuallyFalse = 0 := by
  rw [eventuallyFalse_eq_iUnion_shift]
  exact measure_iUnion_null fun k => trials_localFloor_null p hp hp0 k

/-- `Statement:` CONTROL, `eventuallyFalse` has `trials 0 hp` measure one (`trials_zero_eq_dirac`). -/
theorem trials_zero_eventuallyFalse (hp : (0 : NNReal) ≤ 1) : trials 0 hp eventuallyFalse = 1 := by
  rw [trials_zero_eq_dirac]
  exact Measure.dirac_apply_of_mem (by
    rw [eventuallyFalse_eq_iUnion_silentFrom, Set.mem_iUnion]; exact ⟨0, fun _ _ => rfl⟩)

/-! ### § III. The other chart: a fading coin

`Reading:` CARRIER, returning to a floor as a family indexed by the per-stage law, never a union:
with a constant coin `0 < p ≤ 1` it is null (`trials_eventuallyFalse_null`), with a summable coin
almost sure (`fadingTrials_eventuallyFalse`). `trials p hp` is the constant member
(`fadingTrials_const`); `p = 0` is constant and summable, measure one (`trials_zero_eventuallyFalse`).
Prior art at `returning_two_charts`. -/

set_option linter.deprecated false in
/-- `Statement:` independent Bernoulli(`q n`) flips, one per stage; `trials` with a per-stage `p`. -/
noncomputable def fadingTrials (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun n => (PMF.bernoulli (q n) (hq n)).toMeasure)

/-- `Statement:` `fadingTrials q hq` is a probability measure. -/
instance fadingTrials_isProbability (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) :
    IsProbabilityMeasure (fadingTrials q hq) := by
  unfold fadingTrials; infer_instance

/-- `Statement:` with a constant `q`, `fadingTrials` is `trials`. -/
theorem fadingTrials_const (p : NNReal) (hp : p ≤ 1) :
    fadingTrials (fun _ => p) (fun _ => hp) = trials p hp := rfl

set_option linter.deprecated false in
/-- `Statement:` stage `n` fires with `fadingTrials q hq` probability exactly `q n`. -/
theorem fadingTrials_fires (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) (n : ℕ) :
    fadingTrials q hq (fires n) = (q n : ENNReal) := by
  have hpi : fires n = Set.pi ({n} : Finset ℕ) (fun _ => ({true} : Set Bool)) := by
    ext w; simp [fires]
  rw [hpi, fadingTrials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton true)]
  simp [PMF.bernoulli]

/-- `Statement:` if `q` is summable, `eventuallyFalse` has `fadingTrials q hq` measure one. The first
Borel-Cantelli lemma, Mathlib `measure_limsup_atTop_eq_zero`. -/
theorem fadingTrials_eventuallyFalse (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) (hs : Summable q) :
    fadingTrials q hq eventuallyFalse = 1 := by
  have h0 : fadingTrials q hq (Filter.limsup fires Filter.atTop) = 0 := by
    refine measure_limsup_atTop_eq_zero ?_
    simp only [fadingTrials_fires]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 hs
  have hc : eventuallyFalse = (Filter.limsup fires Filter.atTop)ᶜ := by
    ext w; exact mem_eventuallyFalse_iff w
  rw [hc, prob_compl_eq_one_sub, h0, tsub_zero]
  exact .measurableSet_limsup fun n => fires_measurable n

-- Statement: `q n = (1/2) ^ (n + 1)` is summable, so `fadingTrials_eventuallyFalse` applies to it.
example : Summable (fun n : ℕ => ((1/2 : NNReal) ^ (n + 1))) :=
  (NNReal.summable_nat_add_iff 1).2 (NNReal.summable_geometric (by norm_num))

/-- `Statement:` `eventuallyFalse` is null under every constant coin `0 < p ≤ 1`, and has measure one
under every summable coin. `Reading:` CARRIER, two charts of returning to a floor, indexed by the coin.
`Reading:` prior art, the Borel-Cantelli zero-one law: summable half the first lemma
(`measure_limsup_atTop_eq_zero`), constant-coin half the second (`ProbabilityTheory.measure_limsup_eq_one`);
`eventuallyFalse` is a tail event, so Kolmogorov's zero-one law, not applied in this file, makes it
0-or-1 under every independent coin (`ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`). -/
theorem returning_two_charts :
    (∀ (p : NNReal) (hp : p ≤ 1), 0 < p →
      fadingTrials (fun _ => p) (fun _ => hp) eventuallyFalse = 0) ∧
    (∀ (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1), Summable q →
      fadingTrials q hq eventuallyFalse = 1) :=
  ⟨fun p hp hp0 => trials_eventuallyFalse_null p hp hp0, fadingTrials_eventuallyFalse⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms exists_startBit_iff
#print axioms eventuallyFalse
#print axioms silentFrom_eq_shift_preimage
#print axioms eventuallyFalse_eq_iUnion_silentFrom
#print axioms eventuallyFalse_eq_iUnion_shift
#print axioms mem_eventuallyFalse_iff
#print axioms exists_lastBit_iff
#print axioms eventuallyFalse_eq_range_localFloor
#print axioms eventuallyFalse_countable
#print axioms measurableSet_eventuallyFalse
#print axioms trials_eventuallyFalse_null
#print axioms trials_zero_eventuallyFalse
#print axioms fadingTrials
#print axioms fadingTrials_isProbability
#print axioms fadingTrials_const
#print axioms fadingTrials_fires
#print axioms fadingTrials_eventuallyFalse
#print axioms returning_two_charts
end PurityCheck
