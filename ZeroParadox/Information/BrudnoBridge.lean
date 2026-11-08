-- EXPERIMENTAL (bridge): our `trials` and `MLRandom` against Milovanov's `kolmogorov-complexity-lean` (commit 7e71116), to cite its entropy-rate theorems and its prefix-complexity Levin–Schnorr criterion. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.TwoRequirements
import KolmogorovMathlib.Entropy.Complexity.RandomSequences
import KolmogorovMathlib.MonotoneComplexity.LevinSchnorr.Criteria
import Mathlib.Tactic

/-!
# Brudno bridge: `trials` and `MLRandom` against `kolmogorov-complexity-lean`

## Engineer's Take

There is a specific proof we were aiming to use, written in the new version of Lean, and that is why we upgraded to 4.35. It fills in a substantial gap. Maximum entropy sounds exactly like infinite randomness from the other side.

---

## Formal Overview (AI-assisted)
§ I: `trials p hp` is his `Kolmogorov.bernoulliMeasure p hp`; `prefixCyl` is his `cantorCylinder`.
§ II: `MLTest μ` and his `IsMartinLofTest μ` are the same tests, for every `μ`: both bound level `m`
by `2⁻ᵐ` and list cylinders by a computable function with no access to `μ` (blind). § III: its
entropy-rate theorems (SUV Thm 148, Problems 238, 239) and Levin–Schnorr criterion (SUV Thm 94(d)). -/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory Filter

/-! ## § I. The measure and the cylinders -/

/-- `Statement:` our trial measure is his Bernoulli measure, at every `p ≤ 1`, endpoints included. -/
theorem trials_eq_bernoulliMeasure (p : NNReal) (hp : p ≤ 1) :
    trials p hp = Kolmogorov.bernoulliMeasure p hp := by
  unfold trials Kolmogorov.bernoulliMeasure
  congr 1
  funext _
  refine Measure.ext_of_singleton fun b => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)]
  cases b
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    simp only [unitInterval.toNNReal, unitInterval.symm]
    change ((1 - p : NNReal) : ENNReal) = _
    congr 1
    ext
    simp only [NNReal.coe_sub hp, NNReal.coe_one]
    rfl
  · rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _ (measurableSet_singleton _)
      (by simp) (by simp)]
    rfl

/-- `Statement:` our prefix cylinder is his `cantorCylinder`. -/
theorem prefixCyl_eq_cantorCylinder (l : List Bool) :
    prefixCyl l = _root_.cantorCylinder l := rfl

/-! ## § II. The tests, both directions, at every measure -/

/-- `Statement:` our `none`-skipping union over an optional word is his `Option.elim`. -/
private theorem iUnion_mem_option_prefixCyl (o : Option (List Bool)) :
    (⋃ l ∈ o, prefixCyl l) = o.elim ∅ _root_.cantorCylinder := by
  cases o with
  | none => simp
  | some l => ext w; simp [prefixCyl, _root_.cantorCylinder, _root_.IsCantorPrefix]

/-- `Statement:` each of his Martin-Löf tests for `μ` is one of ours. -/
theorem mlTest_of_isMartinLofTest {μ : Measure (ℕ → Bool)} {U : ℕ → Set (ℕ → Bool)}
    (h : Kolmogorov.IsMartinLofTest μ U) : MLTest μ U := by
  obtain ⟨⟨f, hf, hU⟩, hb⟩ := h
  refine ⟨fun m => ?_, fun q => f q.1 q.2, hf, fun m => ?_⟩
  · rw [← Kolmogorov.dyadicValue_one_eq_inv_two_pow']; exact hb m
  · rw [hU m]; simp only [iUnion_mem_option_prefixCyl]

/-- `Statement:` each of our Martin-Löf tests for `μ` is one of his. -/
theorem isMartinLofTest_of_mlTest {μ : Measure (ℕ → Bool)} {U : ℕ → Set (ℕ → Bool)}
    (h : MLTest μ U) : Kolmogorov.IsMartinLofTest μ U := by
  obtain ⟨hb, g, hg, hU⟩ := h
  refine ⟨⟨fun m j => g (m, j), hg, fun m => ?_⟩, fun m => ?_⟩
  · rw [hU m]; simp only [iUnion_mem_option_prefixCyl]
  · rw [Kolmogorov.dyadicValue_one_eq_inv_two_pow']; exact hb m

/-- `Statement:` random for our tests implies random for his (uses `mlTest_of_isMartinLofTest`). -/
theorem isMartinLofRandom_of_MLRandom {μ : Measure (ℕ → Bool)} {w : ℕ → Bool}
    (h : MLRandom μ w) : Kolmogorov.IsMartinLofRandom μ w :=
  fun U hU => h U (mlTest_of_isMartinLofTest hU)

/-- `Statement:` random for his tests implies random for ours (uses `isMartinLofTest_of_mlTest`). -/
theorem MLRandom_of_isMartinLofRandom {μ : Measure (ℕ → Bool)} {w : ℕ → Bool}
    (h : Kolmogorov.IsMartinLofRandom μ w) : MLRandom μ w :=
  fun U hU => h U (isMartinLofTest_of_mlTest hU)

/-! ## § III. His theorems in our vocabulary

SUV: Shen, Uspensky, Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*, AMS 2017.
"Brudno" in the names below is this corpus's label: neither SUV pp. 229-230 nor the library uses it. -/

/-- `Statement:` SUV Thm 148 (p. 229), binary, a pointwise form along Martin-Löf random tapes of the
Bernoulli case of Brudno's theorem: at computable `p` with `0 < p < 1`, along every
`MLRandom (trials p hp)` tape, plain complexity per bit tends to the binary entropy in bits. -/
theorem brudno_of_MLRandom (D : Kolmogorov.Map) (hD : Kolmogorov.isOptimalConditional D)
    {p : NNReal} (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (hcomp : Kolmogorov.ComputableReals.IsComputableReal (p : ℝ))
    {w : ℕ → Bool} (hw : MLRandom (trials p hp) w) :
    Tendsto (fun N : ℕ => ((Kolmogorov.plainK D (_root_.cantorPrefix w N)).toNat : ℝ) / N)
      atTop (nhds (Kolmogorov.negMulLog2 (p : ℝ) + Kolmogorov.negMulLog2 (1 - (p : ℝ)))) := by
  rw [trials_eq_bernoulliMeasure] at hw
  exact Kolmogorov.tendsto_plainK_cantorPrefix_div D hD hp hp0 hp1 hcomp
    (isMartinLofRandom_of_MLRandom hw)

/-- `Statement:` SUV Problem 239 (p. 229), binary, the almost-everywhere Bernoulli case of Brudno's
theorem: at any `p ≤ 1`, the tapes
where plain complexity per bit fails to tend to the entropy are `trials p hp`-null. -/
theorem brudno_ae_trials (D : Kolmogorov.Map) (hD : Kolmogorov.isOptimalConditional D)
    {p : NNReal} (hp : p ≤ 1) :
    trials p hp {w : ℕ → Bool | ¬ Tendsto
        (fun N : ℕ => ((Kolmogorov.plainK D (_root_.cantorPrefix w N)).toNat : ℝ) / N) atTop
        (nhds (Kolmogorov.negMulLog2 (p : ℝ) + Kolmogorov.negMulLog2 (1 - (p : ℝ))))} = 0 := by
  rw [trials_eq_bernoulliMeasure]
  exact Kolmogorov.measure_setOf_not_tendsto_plainK_cantorPrefix_div D hD hp

/-- `Statement:` SUV Problem 238 (p. 229), binary, Thm 148's pointwise form for the fair coin: along every `MLRandom` fair tape,
plain complexity per bit tends to 1. -/
theorem brudno_fair_of_MLRandom (D : Kolmogorov.Map) (hD : Kolmogorov.isOptimalConditional D)
    {w : ℕ → Bool} (hw : MLRandom (trials (1 / 2) (by norm_num)) w) :
    Tendsto (fun N : ℕ => ((Kolmogorov.plainK D (_root_.cantorPrefix w N)).toNat : ℝ) / N)
      atTop (nhds 1) := by
  rw [trials_eq_bernoulliMeasure] at hw
  exact Kolmogorov.tendsto_plainK_cantorPrefix_div_uniform D hD _
    (isMartinLofRandom_of_MLRandom hw)

/-- `Statement:` the prefix-complexity form of the Levin–Schnorr criterion (SUV Thm 94(d), p. 151;
SUV's Levin–Schnorr theorem is Thm 90, p. 146, in monotone complexity): a tape is `MLRandom` for the fair coin iff its
prefix-free complexity stays within a constant of length, `n ≤ K(w↾n) + c` for all `n`. -/
theorem MLRandom_fair_iff_le_KPPlain {U : Kolmogorov.Map}
    (hU : Kolmogorov.IsOptimalPrefixConditional U) (w : ℕ → Bool) :
    MLRandom (trials (1 / 2) (by norm_num)) w ↔
      ∃ c : ℕ, ∀ n : ℕ, (n : ℕ∞) ≤ Kolmogorov.KPPlain U (_root_.cantorPrefix w n) + c := by
  rw [trials_eq_bernoulliMeasure]
  exact ⟨fun h => (Kolmogorov.isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU w).1
      (isMartinLofRandom_of_MLRandom h),
    fun h => MLRandom_of_isMartinLofRandom
      ((Kolmogorov.isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix hU w).2 h)⟩

section PurityCheck
#print axioms trials_eq_bernoulliMeasure
#print axioms prefixCyl_eq_cantorCylinder
#print axioms iUnion_mem_option_prefixCyl
#print axioms mlTest_of_isMartinLofTest
#print axioms isMartinLofTest_of_mlTest
#print axioms isMartinLofRandom_of_MLRandom
#print axioms MLRandom_of_isMartinLofRandom
#print axioms brudno_of_MLRandom
#print axioms brudno_ae_trials
#print axioms brudno_fair_of_MLRandom
#print axioms MLRandom_fair_iff_le_KPPlain
end PurityCheck

end ZeroParadox
