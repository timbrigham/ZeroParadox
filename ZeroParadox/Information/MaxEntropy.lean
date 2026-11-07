-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the fair coin maximizes entropy, missing information vanishes exactly there, and for each prefix-free decoder almost every fair-coin tape is incompressible. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.TwoRequirements
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.Coding.KraftMcMillan
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Maximum entropy: the fair coin, missing information, and incompressible tapes

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
§ I–II: entropy on `Fin n` is at most `log n`, equal iff uniform; `log 2 - binEntropy p` is 0 iff
`p = 1/2`. § III: that coin is `fairTape`; with a first step at ⊥ of `L`, almost every tape is
Martin-Löf random and gives the snap. § IV: any prefix-free decoder; almost every fair tape is
incompressible up to a constant. -/

namespace ZeroParadox

open MeasureTheory Filter ZPSemilattice

/-! ## § I. Entropy is maximal exactly at the uniform law

Binary case in Mathlib (the first `example`). The `n`-symbol case is Jensen on the strictly concave
`Real.negMulLog`; not located in the pinned Mathlib as of 2026-11-06 (grep of `negMulLog`, `log_card`).
Standard (Gibbs' inequality); a formal version outside the closure is the PFR project's
`ProbabilityTheory.measureEntropy_le_log_card` (located by theoremsearch, not read, not compared
here). -/

section Entropy

open Real

-- Statement: Mathlib, `Real.binEntropy_le_log_two` and `Real.binEntropy_eq_log_two`: binary entropy
-- is at most `log 2`, with equality iff `p = 1/2`; both directions of the equality.
example (p : ℝ) : binEntropy p ≤ log 2 ∧ (binEntropy p = log 2 ↔ p = 2⁻¹) :=
  ⟨binEntropy_le_log_two, binEntropy_eq_log_two⟩

/-- `Statement:` Shannon entropy, in nats, of a weight vector on `Fin n`. -/
noncomputable def shannonEntropy {n : ℕ} (q : Fin n → ℝ) : ℝ := ∑ i, negMulLog (q i)

/-- `Statement:` `negMulLog (1/n) = (1/n) log n`. -/
theorem negMulLog_inv_natCast (n : ℕ) :
    negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * log n := by
  simp [negMulLog, log_inv]

/-- `Statement:` Jensen for `negMulLog` at the uniform weights `1/n`. -/
theorem avg_negMulLog_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i) :
    (∑ i : Fin n, (n : ℝ)⁻¹ • negMulLog (q i)) ≤
      negMulLog (∑ i : Fin n, (n : ℝ)⁻¹ • q i) :=
  concaveOn_negMulLog.le_map_sum (fun _ _ => by positivity)
    (by simp [Finset.card_univ, Fintype.card_fin]; field_simp)
    (fun i _ => Set.mem_Ici.2 (hq0 i))

/-- `Statement:` the uniform average of a probability vector on `Fin n` is `1/n`. -/
theorem avg_eq_inv_card {n : ℕ} (q : Fin n → ℝ) (hq1 : ∑ i, q i = 1) :
    (∑ i : Fin n, (n : ℝ)⁻¹ • q i) = (n : ℝ)⁻¹ := by
  simp [smul_eq_mul, ← Finset.mul_sum, hq1]

/-- `Statement:` the uniform average of `negMulLog ∘ q` is `shannonEntropy q / n`. -/
theorem avg_negMulLog_eq {n : ℕ} (q : Fin n → ℝ) :
    (∑ i : Fin n, (n : ℝ)⁻¹ • negMulLog (q i)) = (n : ℝ)⁻¹ * shannonEntropy q := by
  simp [smul_eq_mul, ← Finset.mul_sum, shannonEntropy]

/-- `Statement:` a probability vector on `Fin n`, `0 < n`, has entropy at most `log n`. -/
theorem shannonEntropy_le_log {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) : shannonEntropy q ≤ log n := by
  have h := avg_negMulLog_le hn q hq0
  rw [avg_eq_inv_card q hq1, avg_negMulLog_eq, negMulLog_inv_natCast n] at h
  have hpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  exact le_of_mul_le_mul_left h hpos

/-- `Statement:` under the same hypotheses, entropy equals `log n` iff `q` is uniform; both
directions. -/
theorem shannonEntropy_eq_log_iff {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) : shannonEntropy q = log n ↔ ∀ i, q i = (n : ℝ)⁻¹ := by
  have hiff := strictConcaveOn_negMulLog.map_sum_eq_iff (t := Finset.univ)
    (w := fun _ : Fin n => (n : ℝ)⁻¹) (p := q) (fun _ _ => by positivity)
    (by simp [Finset.card_univ, Fintype.card_fin]; field_simp)
    (fun i _ => Set.mem_Ici.2 (hq0 i))
  rw [avg_eq_inv_card q hq1, avg_negMulLog_eq, negMulLog_inv_natCast n] at hiff
  have hne : (n : ℝ)⁻¹ ≠ 0 := by positivity
  constructor
  · intro h
    have := hiff.1 (by rw [h])
    exact fun i => this i (Finset.mem_univ i)
  · intro h
    have := hiff.2 (fun j _ => h j)
    exact (mul_left_cancel₀ hne this).symm

-- Statement: CONTROL, a point mass on `Fin 2` has entropy 0, below `log 2`.
example : shannonEntropy (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) = 0 := by
  simp [shannonEntropy, Fin.sum_univ_two]

end Entropy

/-! ## § II. Missing information: zero exactly at the fair coin

`missingInfo p` is the gap between the maximum entropy `log 2` and `binEntropy p`. On `(0, 1)` it is
the Kullback–Leibler divergence of Bernoulli(`p`) from the fair coin, written out; the measure-level
`klDiv μ ν = 0 ↔ μ = ν` is Mathlib's (the `example` closing this section). -/

section Missing

open Real

/-- `Statement:` missing information, in nats, about a coin of bias `p`. -/
noncomputable def missingInfo (p : ℝ) : ℝ := log 2 - binEntropy p

/-- `Statement:` missing information is non-negative. -/
theorem missingInfo_nonneg (p : ℝ) : 0 ≤ missingInfo p :=
  sub_nonneg.2 binEntropy_le_log_two

/-- `Statement:` missing information is zero iff `p = 1/2`, iff `binEntropy p = log 2`; both
directions. `Reading:` INVERSION: the observer's zero sits where the ensemble's entropy is maximal.
For `0 ≤ p ≤ 1` both sides are finite, in `[0, log 2]` per symbol; the pole, zero coinciding with
infinity, has its own coincidence witness, `infinitude_forces_infinite_complexity`. -/
theorem missingInfo_eq_zero_iff (p : ℝ) :
    (missingInfo p = 0 ↔ p = 2⁻¹) ∧ (missingInfo p = 0 ↔ binEntropy p = log 2) := by
  have h : missingInfo p = 0 ↔ binEntropy p = log 2 := by
    unfold missingInfo; constructor <;> intro h <;> linarith
  exact ⟨h.trans binEntropy_eq_log_two, h⟩

/-- `Statement:` on `(0, 1)`, `missingInfo p = p log (p / ½) + (1-p) log ((1-p) / ½)`. -/
theorem missingInfo_eq_kl (p : ℝ) (h0 : 0 < p) (h1 : p < 1) :
    missingInfo p = p * log (p / 2⁻¹) + (1 - p) * log ((1 - p) / 2⁻¹) := by
  have h1' : 0 < 1 - p := by linarith
  unfold missingInfo binEntropy
  rw [log_div h0.ne' (by norm_num), log_div h1'.ne' (by norm_num), log_inv, log_inv, log_inv]
  ring

/-- `Statement:` `n` symbols: `log n - shannonEntropy q = 0` iff `q` is uniform; both directions. -/
theorem missingInfo_fin_eq_zero_iff {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (hq0 : ∀ i, 0 ≤ q i)
    (hq1 : ∑ i, q i = 1) : log n - shannonEntropy q = 0 ↔ ∀ i, q i = (n : ℝ)⁻¹ := by
  rw [sub_eq_zero, eq_comm]; exact shannonEntropy_eq_log_iff hn q hq0 hq1

-- Statement: Mathlib, `InformationTheory.klDiv_eq_zero_iff`: for finite measures, `klDiv μ ν = 0`
-- iff `μ = ν`; both directions.
example {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : InformationTheory.klDiv μ ν = 0 ↔ μ = ν :=
  InformationTheory.klDiv_eq_zero_iff

end Missing

/-! ## § III. The maximizer is `fairTape`, and the chain to the snap -/

/-- `Statement:` a bias in `NNReal` maximizing binary entropy is `1/2`. -/
theorem eq_half_of_maxEntropy (p : NNReal) (h : Real.binEntropy (p : ℝ) = Real.log 2) :
    p = 2⁻¹ :=
  NNReal.eq (by simpa using Real.binEntropy_eq_log_two.1 h)

/-- `Statement:` exactly one bias `p` in `NNReal` maximizes binary entropy, and it has `0 < p ≤ 1`:
the hypotheses `hp0`, `hp` of `snap_ae_of_firstStep`. -/
theorem maximizer_admissible :
    ∃ p : NNReal, Real.binEntropy (p : ℝ) = Real.log 2 ∧ 0 < p ∧ p ≤ 1 ∧
      ∀ q : NNReal, Real.binEntropy (q : ℝ) = Real.log 2 → q = p :=
  ⟨2⁻¹, by simp, by norm_num, by norm_num, fun q hq => eq_half_of_maxEntropy q hq⟩

/-- `Statement:` if `p` maximizes binary entropy, `trials p hp` is `fairTape`. -/
theorem trials_eq_fairTape_of_maxEntropy (p : NNReal) (hp : p ≤ 1)
    (h : Real.binEntropy (p : ℝ) = Real.log 2) : trials p hp = fairTape := by
  have key : ∀ (q : NNReal) (hq : q ≤ 1), q = 1 / 2 → trials q hq = fairTape := by
    rintro q hq rfl; rfl
  exact key p hp (by rw [eq_half_of_maxEntropy p h]; norm_num)

/-- `Statement:` if ⊥ of `L` has a first step and `p` maximizes binary entropy, then `trials p hp`-
almost every tape is Martin-Löf random and gives the snap; `mlRandom_and_snap_ae`. One way.
`Reading:` CARRIER: the occurrence commitment is reduced to "the bottom's tape law is the
maximum-entropy coin", one sufficient choice: any `0 < p` gives the snap (`mlRandom_and_snap_ae`);
the fair coin is the one § IV ties to incompressibility. That ⊥ of `L` has a tape law, is unconstrained, or is random is not proved;
`BotHasFirstStep L` stays a hypothesis, and almost every is not every. -/
theorem maxEntropy_mlRandom_and_snap_ae {L : Type*} [ZPSemilattice L] (hR1 : BotHasFirstStep L)
    (p : NNReal) (hp : p ≤ 1) (hmax : Real.binEntropy (p : ℝ) = Real.log 2) :
    ∀ᵐ w ∂(trials p hp), MLRandom (trials p hp) w ∧ ∃ (φ : Bool → L) (hw : ∃ k, w k = true),
      let S := φ ∘ firedRun w hw
      (S 0 = bot ∧ S 1 ≠ S 0 ∧ IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (bot : L) ⋖ S 1) :=
  mlRandom_and_snap_ae hR1 p hp (by rw [eq_half_of_maxEntropy p hmax]; norm_num)

-- Statement: CONTROL, the bias `0` does not maximize binary entropy.
example : Real.binEntropy ((0 : NNReal) : ℝ) ≠ Real.log 2 := by
  rw [NNReal.coe_zero, Real.binEntropy_zero]; exact (Real.log_pos one_lt_two).ne

/-! ## § IV. Incompressibility without a machine

A decoder is any `D : List Bool → Option (List Bool)`; `D d = some x` reads "`d` describes `x`".
`kraft_measure` is Kraft's inequality, measure form, prefix-free domain; finite sibling: Mathlib's
`InformationTheory.kraft_mcmillan_inequality` (the `example` after it). Closer siblings in Milovanov
(§ V, not compared): `domainWeight_le_one`, and `card_compressibleWordsLt` for `compressible_card`.
The `2⁻ᶜ` bound is the easy half of Schnorr's theorem. `Reading:` CARRIER: with the optimal prefix
machine `U` as `D`, `ae_incompressible` is the almost-every form of "`K(w↾n) ≥ n − c`"; `U` is not
defined here. "Maximally complex" means PREFIX-FREE incompressible: for plain complexity no tape has
constant deficiency (`ZeroParadox/Information/Disjunctive.md`). -/

/-- `Statement:` a prefix cylinder is a box over the first `l.length` coordinates. -/
theorem prefixCyl_eq_pi (l : List Bool) :
    prefixCyl l = (↑(Finset.range l.length) : Set ℕ).pi (fun i => ({l.getD i false} : Set Bool)) := by
  ext w
  simp only [prefixCyl, Set.mem_setOf_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
    Set.mem_singleton_iff]
  constructor
  · intro h i hi; rw [h i hi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · intro h i hi; rw [h i hi]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

/-- `Statement:` prefix cylinders are measurable. -/
theorem prefixCyl_measurable (l : List Bool) : MeasurableSet (prefixCyl l) := by
  rw [prefixCyl_eq_pi]
  exact MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_singleton _)

/-- `Statement:` a word of length `n` has fair-coin measure `2⁻ⁿ`. -/
theorem fairTape_prefixCyl (l : List Bool) : fairTape (prefixCyl l) = 2⁻¹ ^ l.length := by
  rw [prefixCyl_eq_pi, fairTape, trials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  have : ∀ i, (PMF.bernoulli (1/2) (by norm_num)).toMeasure {l.getD i false} = (2⁻¹ : ENNReal) := by
    intro i; cases l.getD i false <;> simp [PMF.bernoulli]
  rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_const, Finset.card_range]

/-- `Statement:` the first `n` bits of a tape. -/
def prefixOf (w : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn (fun i : Fin n => w i)

/-- `Statement:` `w` lies in the cylinder of `x` iff `x` is the first `x.length` bits of `w`; both
directions. -/
theorem mem_prefixCyl_iff (w : ℕ → Bool) (x : List Bool) :
    w ∈ prefixCyl x ↔ x = prefixOf w x.length := by
  constructor
  · intro h
    apply List.ext_getElem (by simp [prefixOf])
    intro i h1 h2
    simp [prefixOf, h i h1]
  · intro h i hi
    have h2 := congrArg (fun l : List Bool => l[i]?) h
    simp only [prefixOf, List.getElem?_ofFn, List.getElem?_eq_getElem hi] at h2
    simp [hi] at h2
    exact h2.symm

/-- `Statement:` the words of length below `k`, as a finset. -/
def shortWords (k : ℕ) : Finset (List Bool) :=
  (Finset.range k).biUnion (fun j => (Finset.univ : Finset (Fin j → Bool)).image List.ofFn)

/-- `Statement:` every word of length below `k` is in `shortWords k`. -/
theorem mem_shortWords {k : ℕ} {d : List Bool} (h : d.length < k) : d ∈ shortWords k := by
  simp only [shortWords, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨d.length, h, fun i => d[i], List.ofFn_getElem⟩

/-- `Statement:` there are at most `2^k - 1` words of length below `k`. -/
theorem card_shortWords_le (k : ℕ) : (shortWords k).card + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp [shortWords]
  | succ k ih =>
    have h1 : shortWords (k + 1) =
        shortWords k ∪ (Finset.univ : Finset (Fin k → Bool)).image List.ofFn := by
      simp [shortWords, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
    rw [h1]
    have h2 := Finset.card_union_le (shortWords k)
      ((Finset.univ : Finset (Fin k → Bool)).image List.ofFn)
    have h3 : ((Finset.univ : Finset (Fin k → Bool)).image List.ofFn).card ≤ 2 ^ k :=
      Finset.card_image_le.trans (by simp)
    rw [pow_succ]; omega

/-- `Statement:` for any decoder `D`, the words with a description shorter than `k` lie in a finset
of at most `2^k - 1` words. -/
theorem compressible_card (D : List Bool → Option (List Bool)) (k : ℕ) :
    ∃ S : Finset (List Bool), {x | ∃ d, d.length < k ∧ D d = some x} ⊆ ↑S ∧ S.card + 1 ≤ 2 ^ k := by
  classical
  refine ⟨(shortWords k).biUnion (fun d => (D d).toFinset), ?_, ?_⟩
  · rintro x ⟨d, hd, hD⟩
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, exists_prop]
    exact ⟨d, mem_shortWords hd, by simp [hD]⟩
  · have : ((shortWords k).biUnion (fun d => (D d).toFinset)).card ≤ (shortWords k).card := by
      refine (Finset.card_biUnion_le).trans ?_
      calc ∑ d ∈ shortWords k, (D d).toFinset.card ≤ ∑ _d ∈ shortWords k, 1 :=
            Finset.sum_le_sum fun d _ => by cases D d <;> simp
        _ = (shortWords k).card := by simp
    have := card_shortWords_le k; omega

/-- `Statement:` no word in `S` is a proper prefix of another in `S`. -/
def PrefixFree (S : Set (List Bool)) : Prop := ∀ d ∈ S, ∀ e ∈ S, d <+: e → d = e

/-- `Statement:` two words whose cylinders meet are prefix-comparable. -/
theorem prefix_of_mem_prefixCyl {d e : List Bool} {w : ℕ → Bool} (hd : w ∈ prefixCyl d)
    (he : w ∈ prefixCyl e) (hle : d.length ≤ e.length) : d <+: e := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take]
  exact (hd i h1).symm.trans (he i (by omega))

/-- `Statement:` over a prefix-free domain, the domain's cylinders are pairwise disjoint. -/
theorem pairwise_disjoint_domCyl (D : List Bool → Option (List Bool))
    (hD : PrefixFree {d | (D d).isSome}) :
    Pairwise (Function.onFun Disjoint
      (fun d => if (D d).isSome then prefixCyl d else (∅ : Set (ℕ → Bool)))) := by
  intro d e hne
  simp only [Function.onFun]
  split_ifs with h1 h2
  · rw [Set.disjoint_left]
    intro w hwd hwe
    rcases le_total d.length e.length with hle | hle
    · exact hne (hD d h1 e h2 (prefix_of_mem_prefixCyl hwd hwe hle))
    · exact hne (hD e h2 d h1 (prefix_of_mem_prefixCyl hwe hwd hle)).symm
  all_goals simp

/-- `Statement:` Kraft, measure form: over a prefix-free domain, `∑ 2^(-|d|) ≤ 1`. -/
theorem kraft_measure (D : List Bool → Option (List Bool)) (hD : PrefixFree {d | (D d).isSome}) :
    ∑' d, fairTape (if (D d).isSome then prefixCyl d else ∅) ≤ 1 := by
  rw [← measure_iUnion (pairwise_disjoint_domCyl D hD) (fun d => by
    split_ifs
    · exact prefixCyl_measurable d
    · exact MeasurableSet.empty)]
  exact prob_le_one

-- Statement: Mathlib, `InformationTheory.kraft_mcmillan_inequality`: a finite uniquely decodable
-- binary code has `∑ (1/2)^|w| ≤ 1`.
example {S : Finset (List Bool)} (h : InformationTheory.UniquelyDecodable (S : Set (List Bool))) :
    ∑ w ∈ S, (1 / Fintype.card Bool : ℝ) ^ w.length ≤ 1 :=
  InformationTheory.kraft_mcmillan_inequality h

/-- `Statement:` the tapes with a prefix `x` having a `D`-description `c` or more bits shorter. -/
def compressibleTapes (D : List Bool → Option (List Bool)) (c : ℕ) : Set (ℕ → Bool) :=
  {w | ∃ d x, D d = some x ∧ d.length + c ≤ x.length ∧ w ∈ prefixCyl x}

/-- `Statement:` over a prefix-free domain, `compressibleTapes D c` has fair-coin measure at most
`2⁻ᶜ`. -/
theorem fairTape_compressibleTapes_le (D : List Bool → Option (List Bool))
    (hD : PrefixFree {d | (D d).isSome}) (c : ℕ) : fairTape (compressibleTapes D c) ≤ 2⁻¹ ^ c := by
  classical
  let B : List Bool → Set (ℕ → Bool) := fun d =>
    match D d with
    | some x => if d.length + c ≤ x.length then prefixCyl x else ∅
    | none => ∅
  have hsub : compressibleTapes D c ⊆ ⋃ d, B d := by
    rintro w ⟨d, x, hDx, hlen, hw⟩
    refine Set.mem_iUnion.2 ⟨d, ?_⟩
    simp only [B, hDx, if_pos hlen]; exact hw
  have hB : ∀ d, fairTape (B d) ≤
      2⁻¹ ^ c * fairTape (if (D d).isSome then prefixCyl d else ∅) := by
    intro d
    simp only [B]
    cases hDd : D d with
    | none => simp
    | some x =>
      simp only [Option.isSome_some, if_true]
      split_ifs with hlen
      · rw [fairTape_prefixCyl, fairTape_prefixCyl, ← pow_add]
        exact pow_le_pow_of_le_one zero_le (by norm_num) (by omega)
      · simp
  calc fairTape (compressibleTapes D c) ≤ fairTape (⋃ d, B d) := measure_mono hsub
    _ ≤ ∑' d, fairTape (B d) := measure_iUnion_le _
    _ ≤ ∑' d, 2⁻¹ ^ c * fairTape (if (D d).isSome then prefixCyl d else ∅) :=
        ENNReal.tsum_le_tsum hB
    _ = 2⁻¹ ^ c * ∑' d, fairTape (if (D d).isSome then prefixCyl d else ∅) :=
        ENNReal.tsum_mul_left
    _ ≤ 2⁻¹ ^ c * 1 := by gcongr; exact kraft_measure D hD
    _ = 2⁻¹ ^ c := mul_one _

/-- `Statement:` over a prefix-free domain, almost every fair-coin tape `w` has a `c` with every
`D`-description of every prefix of `w` fewer than `c` bits shorter than that prefix. -/
theorem ae_incompressible (D : List Bool → Option (List Bool))
    (hD : PrefixFree {d | (D d).isSome}) :
    ∀ᵐ w ∂fairTape, ∃ c, ∀ d x, D d = some x → w ∈ prefixCyl x → x.length < d.length + c := by
  have hnull : fairTape (⋂ c, compressibleTapes D c) = 0 :=
    measure_iInter_le_pow_zero fairTape _ (fairTape_compressibleTapes_le D hD)
  rw [ae_iff]
  refine measure_mono_null (fun w hw => ?_) hnull
  simp only [Set.mem_setOf_eq, not_exists, not_forall, not_lt] at hw
  refine Set.mem_iInter.2 fun c => ?_
  obtain ⟨d, x, hDx, hw', hlen⟩ := hw c
  exact ⟨d, x, hDx, hlen, hw'⟩

/-- `Statement:` the decoder sending every word `d` to `d ++ [false]`. -/
def appendFalse : List Bool → Option (List Bool) := fun d => some (d ++ [false])

/-- `Statement:` `1/2 + 1/4 < 1` in `ENNReal`. -/
theorem half_add_quarter_lt_one : (2⁻¹ : ENNReal) + 2⁻¹ ^ 2 < 1 := by
  have e : (2⁻¹ : ENNReal) = ((2⁻¹ : NNReal) : ENNReal) := by simp
  rw [e, ← ENNReal.coe_pow, ← ENNReal.coe_add, ← ENNReal.coe_one, ENNReal.coe_lt_coe]
  norm_num

-- Statement: CONTROL, drop prefix-freeness: under `appendFalse`, `compressibleTapes appendFalse 1`
-- exceeds the bound `2⁻¹` (it holds every tape with a `false` anywhere; the proof uses the subset
-- with one in the first two bits, measure 3/4).
example : ¬ fairTape (compressibleTapes appendFalse 1) ≤ 2⁻¹ ^ 1 ∧
    ¬ PrefixFree {d | (appendFalse d).isSome} := by
  constructor
  · have hsub : (prefixCyl [true, true])ᶜ ⊆ compressibleTapes appendFalse 1 := by
      intro w hw
      simp only [Set.mem_compl_iff, prefixCyl, Set.mem_setOf_eq, List.length_cons,
        List.length_nil, not_forall] at hw
      obtain ⟨i, hi, hne⟩ := hw
      have hwi : w i = false := by
        interval_cases i <;> simp_all
      refine ⟨prefixOf w i, prefixOf w i ++ [false], rfl, by simp [prefixOf], ?_⟩
      intro j hj
      have hj' : j < i + 1 := by simpa [prefixOf] using hj
      rw [List.getElem_append]
      split_ifs with h
      · simp [prefixOf]
      · have : j = i := by simp [prefixOf] at h; omega
        subst this; simp [hwi]
    intro hle
    have h1 := measure_add_measure_compl (μ := fairTape) (prefixCyl_measurable [true, true])
    rw [measure_univ, fairTape_prefixCyl] at h1
    have h2 : (1 : ENNReal) ≤ 2⁻¹ ^ 2 + 2⁻¹ := by
      calc (1 : ENNReal) = 2⁻¹ ^ [true, true].length + fairTape (prefixCyl [true, true])ᶜ := h1.symm
        _ ≤ 2⁻¹ ^ 2 + fairTape (compressibleTapes appendFalse 1) :=
            add_le_add (le_of_eq (by simp)) (measure_mono hsub)
        _ ≤ 2⁻¹ ^ 2 + 2⁻¹ := add_le_add le_rfl (by simpa using hle)
    rw [add_comm] at h2
    exact absurd h2 (not_le.2 half_add_quarter_lt_one)
  · intro h
    have := h [] (by simp [appendFalse]) [false] (by simp [appendFalse]) (List.nil_prefix)
    simp at this

/-! ## § V. Prior art, outside the dependency closure

A. Milovanov, `kolmogorov-complexity-lean` @7e71116 (Lean 4.35; not compared with our definitions).
Levin–Schnorr, uniform measure: `isMartinLofRandom_uniform_iff_le_KPPlain_cantorPrefix`, Martin-Löf
random iff `K(w↾n) ≥ n − c`, prefix-free `K`. Brudno, Bernoulli `p`:
`tendsto_plainK_cantorPrefix_div` (computable `p`, `0 < p < 1`, every Martin-Löf random tape; entropy
in bits, ours in nats); almost-every form `measure_setOf_not_tendsto_plainK_cantorPrefix_div` (any
`p ≤ 1`). A rate alone does not give Martin-Löf randomness (standard, not proved here). Ergodic
measures: Hoyrup's effective Shannon–McMillan–Breiman (Cenzer–Porter, arXiv:2103.03971, p. 22,
Thm 32, retrieved 2026-11-07; primary: Hoyrup, STACS 2012, arXiv:1107.1149, not retrieved). -/

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms shannonEntropy
#print axioms negMulLog_inv_natCast
#print axioms avg_negMulLog_le
#print axioms avg_eq_inv_card
#print axioms avg_negMulLog_eq
#print axioms shannonEntropy_le_log
#print axioms shannonEntropy_eq_log_iff
#print axioms missingInfo
#print axioms missingInfo_nonneg
#print axioms missingInfo_eq_zero_iff
#print axioms missingInfo_eq_kl
#print axioms missingInfo_fin_eq_zero_iff
#print axioms eq_half_of_maxEntropy
#print axioms maximizer_admissible
#print axioms trials_eq_fairTape_of_maxEntropy
#print axioms maxEntropy_mlRandom_and_snap_ae
#print axioms prefixCyl_eq_pi
#print axioms prefixCyl_measurable
#print axioms fairTape_prefixCyl
#print axioms prefixOf
#print axioms mem_prefixCyl_iff
#print axioms shortWords
#print axioms mem_shortWords
#print axioms card_shortWords_le
#print axioms compressible_card
#print axioms PrefixFree
#print axioms prefix_of_mem_prefixCyl
#print axioms pairwise_disjoint_domCyl
#print axioms kraft_measure
#print axioms compressibleTapes
#print axioms fairTape_compressibleTapes_le
#print axioms ae_incompressible
#print axioms appendFalse
#print axioms half_add_quarter_lt_one

end PurityCheck
