-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the first hitting time `det` of a tape read as a `Computation Unit`, which halts exactly at the first `true`, and almost surely under `trials p hp` with `0 < p`. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.TwoRequirements
import ZeroParadox.Valuation.DepthIsWait
import Mathlib.Tactic

/-!
# A tape's first hitting time, run as a computation

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

"I think it's tied to the same tape read action where statistically speaking you get a random tape... And as soon as the tape has a non zero value in the computability face it's execution"

---

## Formal Overview (AI-assisted)
The first hitting time `det` read through `toComp : NInf → Computation Unit` (`ninfEquivComp`) halts
at step `n` iff `n` is the first firing (`toComp_det_results_iff`), the slot run's crossing step
(`toComp_det_results_iff_slotRun`); almost surely from `trials_fires_once`; depth via `endVal_eq_wait`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open NInf MeasureTheory ProbabilityTheory

/-! ### § I. Halting of `toComp` -/

/-- `Statement:` `toComp y` has a value at step `m` iff `y` is `false` at `m`. -/
theorem toComp_isSome (y : NInf) (m : ℕ) : ((toComp y).1 m).isSome = !y.1 m := by
  show (bif y.1 m then none else some ()).isSome = !y.1 m
  cases y.1 m <;> rfl

/-- `Statement:` `toComp y` halts with `()` at exactly step `n` (Mathlib's `Computation.Results`) iff
`y = ofNat n`; both directions. -/
theorem toComp_results_iff (y : NInf) (n : ℕ) :
    Computation.Results (toComp y) () n ↔ y = ofNat n := by
  constructor
  · rintro ⟨hmem, hlen⟩
    change Nat.find _ = n at hlen
    rw [Nat.find_eq_iff] at hlen
    obtain ⟨hn, hlt⟩ := hlen
    rw [toComp_isSome, Bool.not_eq_true'] at hn
    refine ext fun i => ?_
    show y.1 i = decide (i < n)
    rcases Nat.lt_or_ge i n with hi | hi
    · have := hlt i hi
      rw [toComp_isSome, Bool.not_eq_true', Bool.not_eq_false] at this
      rw [this]; exact (decide_eq_true hi).symm
    · rw [false_ge y hn i hi]; exact (decide_eq_false (Nat.not_lt.2 hi)).symm
  · rintro rfl
    have hP : ∃ m, ((toComp (ofNat n)).1 m).isSome := ⟨n, by rw [toComp_isSome]; simp [ofNat]⟩
    have : (toComp (ofNat n)).Terminates := (Computation.terminates_def _).2 hP
    refine ⟨Computation.get_mem (toComp (ofNat n)), ?_⟩
    change Nat.find _ = n
    rw [Nat.find_eq_iff]
    refine ⟨by rw [toComp_isSome]; simp [ofNat], fun m hm => ?_⟩
    rw [toComp_isSome]; simp [ofNat, hm]

/-! ### § II. The first hitting time of a tape, run -/

/-- `Statement:` `det w = ofNat n` iff `n` is the first `k` with `w k = true`; both directions. The
`example` in `ZeroParadox/Die.lean` § XXV is the left-to-right instance at `n = Nat.find hw`. -/
theorem det_eq_ofNat_iff (w : ℕ → Bool) (n : ℕ) :
    det w = ofNat n ↔ w n = true ∧ ∀ k < n, w k = false := by
  constructor
  · intro h
    have hv : ∀ i, detSeq w i = decide (i < n) := fun i => congrArg (fun x : NInf => x.1 i) h
    have hlt : ∀ k < n, w k = false := fun k hk =>
      detSeq_true w k (by rw [hv]; exact decide_eq_true hk) k le_rfl
    obtain ⟨k, hk, e⟩ := detSeq_false w n (by rw [hv]; exact decide_eq_false (Nat.lt_irrefl n))
    rcases Nat.lt_or_ge k n with h' | h'
    · rw [hlt k h'] at e; cases e
    · rw [show k = n by omega] at e; exact ⟨e, hlt⟩
  · rintro ⟨hn, hlt⟩
    refine ext fun i => ?_
    show detSeq w i = decide (i < n)
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [(detSeq_eq_true_iff w i).2 fun k hk => hlt k (by omega)]
      exact (decide_eq_true hi).symm
    · rw [decide_eq_false (Nat.not_lt.2 hi)]
      cases hd : detSeq w i
      · rfl
      · rw [detSeq_true w i hd n hi] at hn; cases hn

/-- `Statement:` `toComp (det w)` halts at exactly step `n` iff `n` is the first `k` with
`w k = true`; both directions. `Reading:` halting says THAT the computation finishes, not WHAT runs
(the content chart is `code_occurs_of_disjunctive`, `ZeroParadox/Information/Disjunctive.lean`). -/
theorem toComp_det_results_iff (w : ℕ → Bool) (n : ℕ) :
    Computation.Results (toComp (det w)) () n ↔ w n = true ∧ ∀ k < n, w k = false := by
  rw [toComp_results_iff, det_eq_ofNat_iff]

/-- `Statement:` `toComp (det w)` terminates iff `w k = true` for some `k`; both directions. -/
theorem toComp_det_terminates_iff (w : ℕ → Bool) :
    (toComp (det w)).Terminates ↔ ∃ k, w k = true := by
  rw [Computation.terminates_def]
  constructor
  · rintro ⟨n, hn⟩
    rw [toComp_isSome, Bool.not_eq_true'] at hn
    obtain ⟨k, -, hk⟩ := detSeq_false w n hn
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [toComp_isSome]
    show (!detSeq w k) = true
    cases hd : detSeq w k
    · rfl
    · rw [detSeq_true w k hd k le_rfl] at hk; cases hk

/-- `Statement:` if `w k = true` for some `k` (`hw`), `toComp (det w)` halts at step `Nat.find hw`, so
its `Computation.length` is `Nat.find hw` (`Computation.Results.length`). -/
theorem toComp_det_results_find (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    Computation.Results (toComp (det w)) () (Nat.find hw) :=
  (toComp_det_results_iff w _).2 ⟨Nat.find_spec hw, fun k hk => by
    cases h : w k
    · rfl
    · exact absurd h (Nat.find_min hw hk)⟩

/-- `Statement:` `toComp (det w)` halts at exactly step `n` iff `slotRun w` (`CrossingTrials.lean`
§ VII) is `false` at `n` and `true` at `n + 1`; both directions. `Reading:` the delay-type chart and
the slot chart count the same step; with `slotRun_crosses_iff`, termination is reaching `true`. -/
theorem toComp_det_results_iff_slotRun (w : ℕ → Bool) (n : ℕ) :
    Computation.Results (toComp (det w)) () n ↔ slotRun w n = false ∧ slotRun w (n + 1) = true := by
  have h1 : slotRun w n = false ↔ ∀ k < n, w k = false := by simp [slotRun]
  have h2 : slotRun w (n + 1) = true ↔ ∃ k < n + 1, w k = true := by simp [slotRun]
  rw [toComp_det_results_iff, h1, h2]
  constructor
  · rintro ⟨hn, hlt⟩
    exact ⟨hlt, n, by omega, hn⟩
  · rintro ⟨hlt, k, hk, e⟩
    rcases Nat.lt_or_ge k n with h | h
    · rw [hlt k h] at e; cases e
    · rw [show k = n by omega] at e
      exact ⟨e, hlt⟩

/-! ### § III. Depth on `End` -/

/-- `Statement:` the computation of the digit tape of `x` halts at exactly step `n` iff
`endVal x = n`; both directions. `Reading:` finite depth and halting step are one number. -/
theorem endVal_results_iff (x : End) (n : ℕ) :
    Computation.Results (toComp (det (tapeIso x))) () n ↔ endVal x = n := by
  rw [toComp_results_iff, endVal_eq_wait, ← waitENat_ofNat, waitENat.injective.eq_iff]

/-- `Statement:` the computation of the digit tape of `x` never terminates iff `x = botEnd` (⊥ of
`End`), and `x = botEnd` iff `endVal x = ⊤`; both directions of each. `Reading:` the never-halting
computation and infinite depth are one point, ⊥ of `End`. -/
theorem endVal_not_terminates_iff (x : End) :
    (¬ (toComp (det (tapeIso x))).Terminates ↔ x = botEnd) ∧
      (x = botEnd ↔ endVal x = ⊤) := by
  have hb : x = botEnd ↔ ∀ n, x n = 0 := funext_iff
  have hd : det (tapeIso x) = ⊤ ↔ x = botEnd := by
    rw [hb]; refine (det_eq_infty_iff _).trans ?_
    simp [tapeIso_apply]
  refine ⟨?_, ?_⟩
  · rw [toComp_det_terminates_iff, hb]; simp [tapeIso_apply]
  · rw [endVal_eq_wait, ← hd, ← waitENat.map_top, waitENat.injective.eq_iff]

/-! ### § IV. Almost surely -/

/-- `Statement:` if `0 < p ≤ 1`, for `trials p hp`-almost every tape `w`, `w` fires (`hw`) and
`toComp (det w)` halts at step `Nat.find hw`; from `trials_fires_once`. One way. Almost every, not
every (the first CONTROL below). `Reading:` Tim reads halting as execution; that the tape's occupant
is maximally complex is a commitment, not this theorem. -/
theorem toComp_det_halts_ae (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ∀ᵐ w ∂(trials p hp), ∃ hw : ∃ k, w k = true,
      Computation.Results (toComp (det w)) () (Nat.find hw) := by
  have hm : MeasurableSet {w : ℕ → Bool | ∃ k, w k = true} := isOpen_fires_once.measurableSet
  have hfire : ∀ᵐ w ∂(trials p hp), w ∈ {w : ℕ → Bool | ∃ k, w k = true} :=
    (ae_iff_measure_eq hm.nullMeasurableSet).2 (by rw [trials_fires_once p hp hp0, measure_univ])
  filter_upwards [hfire] with w hw
  exact ⟨hw, toComp_det_results_find w hw⟩

/-! ### § V. Controls -/

-- Statement: CONTROL, almost every is not every: ⊥ of `ℕ → Bool` goes to ⊤ of `NInf` (`det_poles`),
-- whose computation is `Computation.empty Unit` (`toComp_infty`) and does not terminate.
example : ¬ (toComp (det (⊥ : ℕ → Bool))).Terminates := by
  rw [det_poles.1]; exact toComp_infty ▸ Computation.not_terminates_empty

-- Statement: CONTROL, `0 < p` is needed: under `trials 0`, the almost-sure halting claim fails.
example : ¬ ∀ᵐ w ∂(trials 0 zero_le_one), (toComp (det w)).Terminates := by
  intro h
  have hnull : trials 0 zero_le_one {w : ℕ → Bool | ∃ k, w k = true} = 0 := by
    have e : {w : ℕ → Bool | ∃ k, w k = true} = ⋃ k, fires k := by ext w; simp [fires]
    rw [e]; exact measure_iUnion_null fun k => by rw [trials_fires]; simp
  have h0 := measure_eq_zero_iff_ae_notMem.1 hnull
  obtain ⟨w, h1, h2⟩ := (h.and h0).exists
  exact h2 ((toComp_det_terminates_iff w).1 h1)

-- Statement: CONTROL, the halting step is the first firing, not the last: the tape firing at `1` and
-- `3` halts at step `1` and not at step `3`.
example : Computation.Results (toComp (det fun k => decide (k = 1 ∨ k = 3))) () 1 ∧
    ¬ Computation.Results (toComp (det fun k => decide (k = 1 ∨ k = 3))) () 3 := by
  rw [toComp_det_results_iff, toComp_det_results_iff]
  exact ⟨⟨by decide, fun k hk => by simp; omega⟩, fun ⟨_, h⟩ => by simpa using h 1 (by omega)⟩

-- Statement: CONTROL, halting forgets the tape after the first firing: the tapes firing at `{1}` and
-- at `{1, 3}` give the same computation.
example : toComp (det fun k => decide (k = 1)) = toComp (det fun k => decide (k = 1 ∨ k = 3)) := by
  rw [det_fire 1, (det_eq_ofNat_iff _ 1).2 ⟨by decide, fun k hk => by simp; omega⟩]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms toComp_isSome
#print axioms toComp_results_iff
#print axioms det_eq_ofNat_iff
#print axioms toComp_det_results_iff
#print axioms toComp_det_terminates_iff
#print axioms toComp_det_results_find
#print axioms toComp_det_results_iff_slotRun
#print axioms endVal_results_iff
#print axioms endVal_not_terminates_iff
#print axioms toComp_det_halts_ae
end PurityCheck
