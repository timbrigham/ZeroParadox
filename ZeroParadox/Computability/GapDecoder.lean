-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): one tape-to-program decoder (the gap after the start bit, read as a code number) and the predicate "reaches every code" it witnesses. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.StartBit
import ZeroParadox.Computability.Kleene
import Mathlib.Tactic

/-!
# Reading a program off a tape: one decoder, and the class it witnesses under a coin `0 < p < 1`

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
§ I: `gapDecode` reads the run of `false` after the start bit as a code number (a unary length).
§ II: a decoder in `ReachesEveryCode μ` reaches the self-printing universal codes with positive
`μ`-mass; `gapDecode` is a member for `trials p hp` with `0 < p < 1`, not at `p = 1`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory Filter Nat.Partrec

/-! ### § I. The gap decoder -/

/-- `Statement:` if `w` has a first `true` at `f` and a next `true` at `f + 1 + j`, the code
numbered `j`; otherwise `none`.
`Reading:` ONE CHOICE among many (`codeWord`, `ZeroParadox/Information/Disjunctive.lean`, reads
binary). `firedRun` records only THAT the tape fired, one run for every firing tape
(`firedRun_spec`); WHEN comes from `det` (`toComp_det_results_iff`); this decoder adds a WHAT.
Prior art at `trials_gapDecode_pos`. -/
noncomputable def gapDecode (w : ℕ → Bool) : Option Code := by
  classical
  exact if hw : ∃ k, w k = true then
    (if hg : ∃ j, w (Nat.find hw + 1 + j) = true then
      some (Denumerable.ofNat Code (Nat.find hg)) else Option.none)
  else Option.none

/-- `Statement:` the subtape from position `k` on is ⊥ of `ℕ → Bool` iff `w` has no `true` from `k`
on. -/
theorem shiftTape_eq_bot_iff (k : ℕ) (w : ℕ → Bool) :
    shiftTape k w = ⊥ ↔ ¬ ∃ j, w (k + j) = true := by
  constructor
  · rintro h ⟨j, hj⟩
    have := congrFun h j
    simp [shiftTape, hj] at this
  · intro h; funext j
    simp only [shiftTape]
    cases hj : w (k + j)
    · rfl
    · exact absurd ⟨j, hj⟩ h

/-- `Statement:` `gapDecode w = none` iff `w` is ⊥ of `ℕ → Bool` or its subtape after its first `true`
is ⊥ of `ℕ → Bool`; both directions. -/
theorem gapDecode_eq_none_iff (w : ℕ → Bool) :
    gapDecode w = Option.none ↔
      w = ⊥ ∨ ∃ hw : ∃ k, w k = true, shiftTape (Nat.find hw + 1) w = ⊥ := by
  unfold gapDecode
  by_cases hw : ∃ k, w k = true
  · have hne : w ≠ ⊥ := (exists_startBit_iff w).1 hw
    conv_lhs => simp only [hw, ↓reduceDIte]
    by_cases hg : ∃ j, w (Nat.find hw + 1 + j) = true
    · conv_lhs => simp only [hg, ↓reduceDIte]
      constructor
      · intro h; cases h
      · rintro (h | ⟨_, h⟩)
        · exact absurd h hne
        · exact absurd hg ((shiftTape_eq_bot_iff _ w).1 h)
    · conv_lhs => simp only [hg, ↓reduceDIte]
      exact ⟨fun _ => Or.inr ⟨hw, (shiftTape_eq_bot_iff _ w).2 hg⟩, fun _ => trivial⟩
  · conv_lhs => simp only [hw, ↓reduceDIte]
    exact ⟨fun _ => Or.inl (not_not.1 (mt (exists_startBit_iff w).2 hw)), fun _ => trivial⟩

/-- `Statement:` the tapes with `gapDecode w = none` are eventually `false`. -/
theorem gapDecode_none_subset :
    {w : ℕ → Bool | gapDecode w = Option.none} ⊆ eventuallyFalse := by
  intro w hw
  rw [eventuallyFalse_eq_iUnion_shift, Set.mem_iUnion]
  rcases (gapDecode_eq_none_iff w).1 hw with rfl | ⟨hw', h⟩
  · exact ⟨0, rfl⟩
  · exact ⟨_, h⟩

/-- `Statement:` if `0 < p ≤ 1`, `gapDecode w = none` on a `trials p hp`-null set. -/
theorem trials_gapDecode_none_null (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp {w | gapDecode w = Option.none} = 0 :=
  measure_mono_null gapDecode_none_subset (trials_eventuallyFalse_null p hp hp0)

/-- `Statement:` the tape `true` at `0` and at `j + 1`, `false` elsewhere. -/
def gapWitness (j : ℕ) : ℕ → Bool := fun k => decide (k = 0 ∨ k = j + 1)

/-- `Statement:` every tape agreeing with `gapWitness j` below `j + 2` decodes to the code numbered
`j`. -/
theorem gapDecode_of_mem_cyl (j : ℕ) (w : ℕ → Bool)
    (hw : w ∈ PiNat.cylinder (gapWitness j) (j + 2)) :
    gapDecode w = some (Denumerable.ofNat Code j) := by
  have hw' : ∀ i < j + 2, w i = gapWitness j i := fun i hi => hw i hi
  have h0 : w 0 = true := by rw [hw' 0 (by omega)]; simp [gapWitness]
  have hex : ∃ k, w k = true := ⟨0, h0⟩
  have hf : Nat.find hex = 0 := (Nat.find_eq_zero hex).2 h0
  unfold gapDecode
  simp only [hex, ↓reduceDIte]
  have hg : ∃ i, w (Nat.find hex + 1 + i) = true := ⟨j, by
    rw [hf, hw' (0 + 1 + j) (by omega)]; simp [gapWitness]; omega⟩
  simp only [hg, ↓reduceDIte, Option.some.injEq]
  congr 1
  rw [Nat.find_eq_iff]
  refine ⟨by rw [hf, hw' (0 + 1 + j) (by omega)]; simp [gapWitness]; omega, fun n hn => ?_⟩
  rw [hf, hw' (0 + 1 + n) (by omega)]; simp [gapWitness]; omega

/-- `Statement:` if `0 < p < 1`, every code `c` has `0 < trials p hp {w | gapDecode w = some c}`.
`Reading:` prior art, after the start bit this is the machine of Shen, Uspensky, Vereshchagin,
*Kolmogorov Complexity and Algorithmic Randomness* (AMS 2017), § 4.1, p. 75: toss a fair coin until
1 appears, output the number of zeros before it, each `i` with probability `2^-(i+1)`; here the coin is
`trials p hp` and outputs are Mathlib `Code`s. Formal neighbour: `Kolmogorov.apriori_pos_of_universal`. -/
theorem trials_gapDecode_pos (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) (c : Code) :
    0 < trials p hp {w | gapDecode w = some c} := by
  refine lt_of_lt_of_le (trials_cyl_pos p hp hp0 hp1 (gapWitness (Encodable.encode c))
    (Encodable.encode c + 2)) (measure_mono fun w hw => ?_)
  show gapDecode w = some c
  rw [gapDecode_of_mem_cyl _ w hw, Denumerable.ofNat_encode]

/-- `Statement:` `gapDecode` sends ⊥ of `ℕ → Bool` to `none` and ⊤ of `ℕ → Bool` to `Code.zero`. -/
theorem gapDecode_poles :
    gapDecode (⊥ : ℕ → Bool) = Option.none ∧ gapDecode (⊤ : ℕ → Bool) = some Code.zero := by
  refine ⟨(gapDecode_eq_none_iff _).2 (Or.inl rfl), ?_⟩
  have := gapDecode_of_mem_cyl 0 ⊤ (fun i hi => by simp [gapWitness]; omega)
  have e : Encodable.encode Code.zero = 0 := by decide
  rw [this, ← e, Denumerable.ofNat_encode]

/-! ### § II. The class `ReachesEveryCode`

`Reading:` Tim (2026-11-15): "So it's not just one program. It's all programs"; and "once you have
one you have evidence that a class exists, right?" His tree reading ("the same chasing the darkness
kind of routing", Tim, 2026-11-15) is not stated here: `t4_snap_orthogonal` covers cells 0 and 1; a
theorem on the right angle of the actual path against the untaken branches is not located in the
corpus as of 2026-11-15 (nearest: orthogonal projection as a die motion, `ZeroParadox/State/DieProjection.lean`).
The class removes § II's dependence on one decoder, not the choice to read programs off tapes, which
stays a commitment carried as the hypothesis. Prior art: Shen, Uspensky, Vereshchagin § 4.1
(`trials_gapDecode_pos`); the broader home is algorithmic probability (Solomonoff, Levin, Chaitin). -/

/-- `Statement:` every code `c` has `0 < μ {w | D w = some c}`. A predicate, used as a hypothesis. -/
def ReachesEveryCode (μ : Measure (ℕ → Bool)) (D : (ℕ → Bool) → Option Code) : Prop :=
  ∀ c, 0 < μ {w | D w = some c}

/-- `Statement:` `D w = none` on a `μ`-null set. A predicate, used as a hypothesis. -/
def DecodesAlmostSurely (μ : Measure (ℕ → Bool)) (D : (ℕ → Bool) → Option Code) : Prop :=
  μ {w | D w = Option.none} = 0

/-- `Statement:` the self-printing universal codes form an infinite set, unconditionally
(`selfref_universal_infinite`); every code's event is pairwise disjoint from every other's; and if
`D` reaches every code for `μ`, each self-printing universal code has positive `μ`-mass under `D`
and so does their union.
`Reading:` beside the machine of Shen, Uspensky, Vereshchagin § 4.1 (`trials_gapDecode_pos`), whose
every output has positive probability: here positivity under an arbitrary measure is the hypothesis
`hD`, not a result. Added: the start bit, the biased coin, Mathlib `Code`, closure under `Code ≃ Code`
(`ReachesEveryCode.map_equiv`), and the infinite set of self-printing universal codes
(`selfref_universal_infinite`) these reach. -/
theorem selfref_universal_reached {μ : Measure (ℕ → Bool)} {D : (ℕ → Bool) → Option Code}
    (hD : ReachesEveryCode μ D) :
    {c : Code | SelfPrints c ∧ Universal c}.Infinite ∧
    (∀ c ∈ {c : Code | SelfPrints c ∧ Universal c}, 0 < μ {w | D w = some c}) ∧
    Pairwise (fun c c' : Code => Disjoint {w | D w = some c} {w | D w = some c'}) ∧
    0 < μ {w | ∃ c, (SelfPrints c ∧ Universal c) ∧ D w = some c} := by
  obtain ⟨c, hc⟩ := selfref_universal_infinite.nonempty
  refine ⟨selfref_universal_infinite, fun c _ => hD c,
    fun _ _ hne => Set.disjoint_left.2 fun _ h h' => hne (Option.some.inj (h.symm.trans h')),
    lt_of_lt_of_le (hD c) (measure_mono fun w hw => ⟨c, hc, hw⟩)⟩

/-- `Statement:` WITNESS, if `0 < p < 1`, `gapDecode` reaches every code for `trials p hp` and
decodes almost surely. -/
theorem gapDecode_mem (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    ReachesEveryCode (trials p hp) gapDecode ∧ DecodesAlmostSurely (trials p hp) gapDecode :=
  ⟨trials_gapDecode_pos p hp hp0 hp1, trials_gapDecode_none_null p hp hp0⟩

/-- `Statement:` composing a member with a bijection `e : Code ≃ Code` gives a member. -/
theorem ReachesEveryCode.map_equiv {μ : Measure (ℕ → Bool)} {D : (ℕ → Bool) → Option Code}
    (hD : ReachesEveryCode μ D) (e : Code ≃ Code) :
    ReachesEveryCode μ (fun w => (D w).map e) := fun c => by
  have : {w | (D w).map e = some c} = {w | D w = some (e.symm c)} := by
    ext w
    show (D w).map e = some c ↔ D w = some (e.symm c)
    cases D w with
    | none => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
    | some a =>
      show some (e a) = some c ↔ some a = some (e.symm c)
      rw [Option.some_inj, Option.some_inj]
      exact ⟨fun h => by rw [← h, e.symm_apply_apply], fun h => by rw [h, e.apply_symm_apply]⟩
  rw [this]; exact hD _

/-- `Statement:` CONTROL, for every `μ` the constant decoder `_ ↦ some Code.zero` is not a member. -/
theorem const_not_reachesEveryCode (μ : Measure (ℕ → Bool)) :
    ¬ ReachesEveryCode μ (fun _ => some Code.zero) := fun h => by
  have := h Code.succ
  have e : {w : ℕ → Bool | some Code.zero = some Code.succ} = ∅ := by
    ext w; simp
  rw [e, measure_empty] at this
  exact lt_irrefl _ this

/-- `Statement:` CONTROL, at `p = 1` the set of tapes decoding to `Code.zero` has `trials 1 hp`
measure one (`trials 1 hp` is the Dirac mass at ⊤ of `ℕ → Bool`, `trials_one_eq_dirac`), `Code.zero`
is self-printing and not universal, and `gapDecode` is not a member. -/
theorem gapDecode_p_one (hp : (1 : NNReal) ≤ 1) :
    trials 1 hp {w | gapDecode w = some Code.zero} = 1 ∧ SelfPrints Code.zero ∧
      ¬ Universal Code.zero ∧ ¬ ReachesEveryCode (trials 1 hp) gapDecode := by
  refine ⟨?_, fun _ => by rw [(by decide : Encodable.encode Code.zero = 0)]; rfl, fun h => ?_,
    fun h => ?_⟩
  · rw [trials_one_eq_dirac]; exact Measure.dirac_apply_of_mem gapDecode_poles.2
  · have := h (Encodable.encode Code.succ) 0
    rw [Denumerable.ofNat_encode] at this
    change Part.some 0 = Part.some 1 at this
    exact absurd (Part.some_injective this) (by decide)
  · have := h Code.succ
    rw [trials_one_eq_dirac, Measure.dirac_apply, Set.indicator_of_notMem] at this
    · exact lt_irrefl _ this
    · show ¬ gapDecode ⊤ = some Code.succ
      rw [gapDecode_poles.2]; simp

/-- `Statement:` CONTROL, `gapDecode w = none` on a set of `trials 0 hp` measure one. -/
theorem gapDecode_p_zero (hp : (0 : NNReal) ≤ 1) :
    trials 0 hp {w | gapDecode w = Option.none} = 1 := by
  rw [trials_zero_eq_dirac]; exact Measure.dirac_apply_of_mem gapDecode_poles.1

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms gapDecode
#print axioms shiftTape_eq_bot_iff
#print axioms gapDecode_eq_none_iff
#print axioms gapDecode_none_subset
#print axioms trials_gapDecode_none_null
#print axioms gapWitness
#print axioms gapDecode_of_mem_cyl
#print axioms trials_gapDecode_pos
#print axioms gapDecode_poles
#print axioms ReachesEveryCode
#print axioms DecodesAlmostSurely
#print axioms selfref_universal_reached
#print axioms gapDecode_mem
#print axioms ReachesEveryCode.map_equiv
#print axioms const_not_reachesEveryCode
#print axioms gapDecode_p_one
#print axioms gapDecode_p_zero
end PurityCheck
