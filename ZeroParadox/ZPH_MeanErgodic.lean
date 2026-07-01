import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import ZeroParadox.ZPH_PerronFrobenius

set_option maxHeartbeats 800000

/-!
# Mean ergodic convergence for doubly-stochastic kernels (STRETCH; stub-first)

A doubly-stochastic transfer operator is an ℓ²-contraction (Cauchy–Schwarz), so Mathlib's von Neumann mean
ergodic theorem gives FULL Cesàro (Birkhoff-average) convergence — deeper than the subsequential existence in
`exists_stationary`. The whole result reduces to the operator-norm bound `‖T₂‖ ≤ 1`; Mathlib supplies the
ergodic conclusion. Stub-first to confirm the API fits.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.MeanErgodic

open Filter Topology

variable {n : ℕ}

/-- The transfer matrix over ℂ: `Pc k j = (f j)(k)`. -/
noncomputable def Pc (f : Fin n → PMF (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k j => (((f j) k).toReal : ℂ)

/-- The transfer operator on `EuclideanSpace ℂ (Fin n)` as a continuous linear map (finite-dim). -/
noncomputable def T₂ (f : Fin n → PMF (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (Matrix.toEuclideanLin (Pc f)).toContinuousLinearMap

/-- Doubly stochastic: columns also sum to 1 (rows already do, as `f j` is a PMF). -/
def DoublyStochastic (f : Fin n → PMF (Fin n)) : Prop := ∀ k, ∑ j, ((f j) k).toReal = 1

/-- Coordinate of the transfer operator on `EuclideanSpace`. -/
lemma T₂_apply (f : Fin n → PMF (Fin n)) (x : EuclideanSpace ℂ (Fin n)) (k : Fin n) :
    (T₂ f x) k = ∑ j, (((f j) k).toReal : ℂ) * x j := rfl

/-- **Crux.** The doubly-stochastic transfer operator is an ℓ²-contraction (`‖T₂ f‖ ≤ 1`): triangle
    inequality, then Cauchy–Schwarz with the column-sum `= 1`, then the row-sum `= 1`. -/
theorem T₂_opNorm_le_one (f : Fin n → PMF (Fin n)) (hd : DoublyStochastic f) : ‖T₂ f‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have hcs : ∀ k, ‖(T₂ f x) k‖ ^ 2 ≤ ∑ j, ((f j) k).toReal * ‖x j‖ ^ 2 := by
    intro k
    have htri : ‖(T₂ f x) k‖ ≤ ∑ j, ((f j) k).toReal * ‖x j‖ := by
      rw [T₂_apply]
      calc ‖∑ j, (((f j) k).toReal : ℂ) * x j‖ ≤ ∑ j, ‖(((f j) k).toReal : ℂ) * x j‖ := norm_sum_le _ _
        _ = ∑ j, ((f j) k).toReal * ‖x j‖ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have hcsq : (∑ j, ((f j) k).toReal * ‖x j‖) ^ 2
        ≤ (∑ j, ((f j) k).toReal) * ∑ j, ((f j) k).toReal * ‖x j‖ ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => Real.sqrt ((f j k).toReal)) (fun j => Real.sqrt ((f j k).toReal) * ‖x j‖)
      have e1 : (∑ j, Real.sqrt ((f j k).toReal) * (Real.sqrt ((f j k).toReal) * ‖x j‖))
          = ∑ j, ((f j) k).toReal * ‖x j‖ :=
        Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, Real.mul_self_sqrt ENNReal.toReal_nonneg]
      have e2 : (∑ j, Real.sqrt ((f j k).toReal) ^ 2) = ∑ j, ((f j) k).toReal :=
        Finset.sum_congr rfl fun j _ => Real.sq_sqrt ENNReal.toReal_nonneg
      have e3 : (∑ j, (Real.sqrt ((f j k).toReal) * ‖x j‖) ^ 2)
          = ∑ j, ((f j) k).toReal * ‖x j‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
      rw [e1, e2, e3] at h
      exact h
    calc ‖(T₂ f x) k‖ ^ 2 ≤ (∑ j, ((f j) k).toReal * ‖x j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ (∑ j, ((f j) k).toReal) * ∑ j, ((f j) k).toReal * ‖x j‖ ^ 2 := hcsq
      _ = ∑ j, ((f j) k).toReal * ‖x j‖ ^ 2 := by rw [hd k, one_mul]
  calc ∑ k, ‖(T₂ f x) k‖ ^ 2
      ≤ ∑ k, ∑ j, ((f j) k).toReal * ‖x j‖ ^ 2 := Finset.sum_le_sum fun k _ => hcs k
    _ = ∑ j, ∑ k, ((f j) k).toReal * ‖x j‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ‖x j‖ ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_mul, ZeroParadox.PerronFrobenius.row_sum, one_mul]

/-- **Mean ergodic convergence** for a doubly-stochastic kernel: the Birkhoff (Cesàro) averages of the
    transfer operator converge. Follows from Mathlib's von Neumann mean ergodic theorem and the ℓ²-contraction
    bound. -/
theorem doubly_stochastic_mean_ergodic (f : Fin n → PMF (Fin n)) (hd : DoublyStochastic f)
    (x : EuclideanSpace ℂ (Fin n)) :
    ∃ y : EuclideanSpace ℂ (Fin n),
      Tendsto (fun N => birkhoffAverage ℂ (T₂ f) id N x) atTop (𝓝 y) :=
  ⟨_, (T₂ f).tendsto_birkhoffAverage_orthogonalProjection (T₂_opNorm_le_one f hd) x⟩

end ZeroParadox.MeanErgodic

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.MeanErgodic
#print axioms T₂_opNorm_le_one
#print axioms doubly_stochastic_mean_ergodic
end PurityCheck
