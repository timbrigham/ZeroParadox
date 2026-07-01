import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.DotProduct

set_option maxHeartbeats 1000000

/-!
# Perron–Frobenius: existence of a stationary distribution (the first NON-thin dictionary entry)

Every finite stochastic action has a fixed point. Built via Cesàro averaging on the compact simplex
(Mathlib has `isCompact_stdSimplex` but no Brouwer / Markov–Kakutani fixed-point, so existence is built, not
pulled off a shelf). STUB-FIRST: architecture with `sorry`, fill incrementally.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.PerronFrobenius

open scoped BigOperators
open Filter Topology

variable {n : ℕ}

/-- The transfer matrix of a finite stochastic kernel: `P k j = (f j)(k)`. -/
noncomputable def P (f : Fin n → PMF (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun k j => ((f j) k).toReal

/-- The transfer (Markov) operator as a linear map. -/
noncomputable def T (f : Fin n → PMF (Fin n)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  (P f).mulVecLin

/-- Each row of the transfer matrix sums to 1 (stochasticity). -/
lemma row_sum (f : Fin n → PMF (Fin n)) (j : Fin n) : ∑ k, ((f j) k).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun k _ => (f j).apply_ne_top k)]
  have h1 : ∑ k, (f j) k = 1 := by
    have := (f j).tsum_coe
    rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at this
  rw [h1, ENNReal.toReal_one]

/-- Coordinate formula for the transfer operator. -/
lemma T_apply (f : Fin n → PMF (Fin n)) (v : Fin n → ℝ) (k : Fin n) :
    T f v k = ∑ j, ((f j) k).toReal * v j := by
  simp only [T, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, P, Matrix.of_apply]

/-- The transfer operator maps the simplex into itself. -/
lemma T_mem (f : Fin n → PMF (Fin n)) {v : Fin n → ℝ} (hv : v ∈ stdSimplex ℝ (Fin n)) :
    T f v ∈ stdSimplex ℝ (Fin n) := by
  obtain ⟨hv0, hv1⟩ := hv
  refine ⟨fun k => ?_, ?_⟩
  · rw [T_apply]
    exact Finset.sum_nonneg fun j _ => mul_nonneg ENNReal.toReal_nonneg (hv0 j)
  · simp_rw [T_apply]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ k, ((f j) k).toReal * v j = v j := by
      intro j; rw [← Finset.sum_mul, row_sum f j, one_mul]
    simp_rw [this]
    exact hv1

/-- Iterates of T from a simplex point stay in the simplex. -/
lemma T_pow_mem (f : Fin n → PMF (Fin n)) {v₀ : Fin n → ℝ}
    (hv : v₀ ∈ stdSimplex ℝ (Fin n)) (k : ℕ) : (T f ^ k) v₀ ∈ stdSimplex ℝ (Fin n) := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact T_mem f ih

/-- Cesàro average of the first `N` iterates from `v₀`. -/
noncomputable def cesaro (f : Fin n → PMF (Fin n)) (v₀ : Fin n → ℝ) (N : ℕ) : Fin n → ℝ :=
  (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, (T f ^ k) v₀

/-- The Cesàro averages stay in the simplex (for `N ≥ 1`). -/
lemma cesaro_mem (f : Fin n → PMF (Fin n)) {v₀ : Fin n → ℝ}
    (hv : v₀ ∈ stdSimplex ℝ (Fin n)) {N : ℕ} (hN : 1 ≤ N) :
    cesaro f v₀ N ∈ stdSimplex ℝ (Fin n) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨fun j => ?_, ?_⟩
  · simp only [cesaro, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => (T_pow_mem f hv k).1 j)
  · have hSsum : (∑ j, (∑ k ∈ Finset.range N, (T f ^ k) v₀) j) = (N : ℝ) := by
      simp_rw [Finset.sum_apply]
      rw [Finset.sum_comm, Finset.sum_congr rfl (fun k _ => (T_pow_mem f hv k).2)]
      simp [Finset.card_range]
    simp only [cesaro, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hSsum, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- Telescoping identity: `T(A_N) - A_N = N⁻¹ • (Tᴺ v₀ - v₀)`. -/
lemma cesaro_diff (f : Fin n → PMF (Fin n)) (v₀ : Fin n → ℝ) (N : ℕ) :
    T f (cesaro f v₀ N) - cesaro f v₀ N = (N : ℝ)⁻¹ • ((T f ^ N) v₀ - v₀) := by
  have hTsum : T f (∑ k ∈ Finset.range N, (T f ^ k) v₀)
      = ∑ k ∈ Finset.range N, (T f ^ (k + 1)) v₀ := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ', Module.End.mul_apply])
  have hre : (∑ k ∈ Finset.range N, (T f ^ (k + 1)) v₀)
      = (∑ k ∈ Finset.range N, (T f ^ k) v₀) + (T f ^ N) v₀ - (T f ^ 0) v₀ := by
    have key : (∑ k ∈ Finset.range N, (T f ^ (k + 1)) v₀) + (T f ^ 0) v₀
        = (∑ k ∈ Finset.range N, (T f ^ k) v₀) + (T f ^ N) v₀ := by
      rw [← Finset.sum_range_succ' (fun k => (T f ^ k) v₀) N,
        Finset.sum_range_succ (fun k => (T f ^ k) v₀) N]
    rw [eq_sub_of_add_eq key]
  simp only [cesaro, map_smul, hTsum, hre, pow_zero, Module.End.one_apply]
  simp only [smul_sub, smul_add]
  abel

/-- `N⁻¹ • (Tᴺ v₀ - v₀) → 0`, since both iterates lie in the (bounded) simplex. -/
lemma tendsto_cesaro_diff_zero (f : Fin n → PMF (Fin n)) {v₀ : Fin n → ℝ}
    (hv : v₀ ∈ stdSimplex ℝ (Fin n)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • ((T f ^ N) v₀ - v₀)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ stdSimplex ℝ (Fin n), ‖x‖ ≤ C := by
    obtain ⟨r, hr⟩ := (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin n)).isBounded.subset_closedBall 0
    refine ⟨r, fun x hx => ?_⟩
    have := hr hx
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hbound : ∀ N : ℕ, ‖(N : ℝ)⁻¹ • ((T f ^ N) v₀ - v₀)‖ ≤ (N : ℝ)⁻¹ * (2 * C) := by
    intro N
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖(T f ^ N) v₀ - v₀‖ ≤ ‖(T f ^ N) v₀‖ + ‖v₀‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hC _ (T_pow_mem f hv N)) (hC _ hv)
      _ = 2 * C := by ring
  have hg : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * C)) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 * C)
  exact squeeze_zero_norm hbound hg

/-- **Target — PROVED.** Every finite stochastic action has a stationary distribution: a fixed point of the
    Kleisli action `μ ↦ μ.bind f`. Built by Cesàro averaging on the compact simplex (no Brouwer needed). -/
theorem exists_stationary [Nonempty (Fin n)] (f : Fin n → PMF (Fin n)) :
    ∃ μ : PMF (Fin n), μ.bind f = μ := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty (Fin n))
  set v₀ : Fin n → ℝ := fun j => if j = i₀ then 1 else 0 with hv₀def
  have hv₀ : v₀ ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun j => ?_, ?_⟩
    · simp only [hv₀def]; split <;> norm_num
    · simp only [hv₀def]
      rw [Finset.sum_eq_single i₀ (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ i₀) h)]
      simp
  have hu : ∀ N : ℕ, cesaro f v₀ (N + 1) ∈ stdSimplex ℝ (Fin n) :=
    fun N => cesaro_mem f hv₀ (Nat.succ_le_succ (Nat.zero_le N))
  obtain ⟨w, hw, φ, hφ, hφt⟩ :=
    (isCompact_stdSimplex (𝕜 := ℝ) (ι := Fin n)).tendsto_subseq hu
  have hcont : Continuous (T f) := (T f).continuous_of_finiteDimensional
  have hidx : Tendsto (fun i => φ i + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_succ (φ i)) hφ.tendsto_atTop
  have h1 : Tendsto (fun i => T f (cesaro f v₀ (φ i + 1)) - cesaro f v₀ (φ i + 1))
      atTop (𝓝 (T f w - w)) := ((hcont.tendsto w).comp hφt).sub hφt
  have h2 : Tendsto (fun i => T f (cesaro f v₀ (φ i + 1)) - cesaro f v₀ (φ i + 1))
      atTop (𝓝 0) := by
    simp_rw [cesaro_diff]
    exact (tendsto_cesaro_diff_zero f hv₀).comp hidx
  have hTw : T f w = w := by
    have h := tendsto_nhds_unique h1 h2
    rwa [sub_eq_zero] at h
  have hwsum : ∑ i, ENNReal.ofReal (w i) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hw.1 i), hw.2, ENNReal.ofReal_one]
  refine ⟨PMF.ofFintype (fun i => ENNReal.ofReal (w i)) hwsum, ?_⟩
  ext k
  rw [PMF.bind_apply, tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx),
    PMF.ofFintype_apply]
  simp only [PMF.ofFintype_apply]
  calc ∑ j, ENNReal.ofReal (w j) * (f j) k
      = ∑ j, ENNReal.ofReal (w j * ((f j) k).toReal) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (hw.1 j), ENNReal.ofReal_toReal ((f j).apply_ne_top k)]
    _ = ENNReal.ofReal (∑ j, w j * ((f j) k).toReal) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hw.1 j) ENNReal.toReal_nonneg).symm
    _ = ENNReal.ofReal (w k) := by
        congr 1
        have h := congrFun hTw k
        rw [T_apply] at h
        rw [← h]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end ZeroParadox.PerronFrobenius

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.PerronFrobenius
#print axioms exists_stationary
end PurityCheck
