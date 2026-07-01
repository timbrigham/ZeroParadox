import ZeroParadox.ZPH_MC1_LinFunctor
import ZeroParadox.ZPH_PerronFrobenius
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000

/-!
# Spectral side: the transfer operator is ℓ¹-nonexpansive, so every eigenvalue has |λ| ≤ 1

A genuine linear-side fact about the linearized stochastic operator. NOTE (precision, per cold audit): the
argument is purely ℓ¹ / triangle-inequality and uses NO inner-product / Hilbert structure — "Hilbert" is the
wrong word for this one. `linMap f` is nonexpansive in the ℓ¹ norm `∑ₖ ‖v k‖` (triangle inequality +
row-stochasticity), and therefore every eigenvalue `c` of `linMap f` satisfies `‖c‖ ≤ 1`. With
`transfer_operator_has_unit_eigenvector` (eigenvalue `1` is achieved), this pins the spectral radius at
exactly `1`. Elementary but genuine — the bound provably fails for a non-stochastic operator (`row_sum` is
load-bearing).

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.SpectralRadius

open ZeroParadox.FinStoch

/-- The transfer operator is ℓ¹-NONEXPANSIVE: `∑ₖ ‖(linMap f v) k‖ ≤ ∑ₖ ‖v k‖`. Triangle inequality plus
    row-stochasticity (`row_sum`). -/
lemma linMap_l1_nonexpansive {n : ℕ} (f : Fin n → PMF (Fin n)) (v : Fin n →₀ ℂ) :
    ∑ k, ‖(linMap (a := ⟨n⟩) (b := ⟨n⟩) f v) k‖ ≤ ∑ k, ‖v k‖ := by
  calc ∑ k, ‖(linMap (a := ⟨n⟩) (b := ⟨n⟩) f v) k‖
      = ∑ k, ‖∑ j, (v j) * (((f j) k).toReal : ℂ)‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [linMap_apply]
    _ ≤ ∑ k, ∑ j, ‖(v j) * (((f j) k).toReal : ℂ)‖ :=
        Finset.sum_le_sum fun k _ => norm_sum_le _ _
    _ = ∑ k, ∑ j, ‖v j‖ * ((f j) k).toReal := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = ∑ j, ∑ k, ‖v j‖ * ((f j) k).toReal := Finset.sum_comm
    _ = ∑ j, ‖v j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.mul_sum, ZeroParadox.PerronFrobenius.row_sum, mul_one]

/-- Every eigenvalue of the transfer operator has modulus `≤ 1` (spectral radius `≤ 1`). -/
lemma eigenvalue_abs_le_one {n : ℕ} (f : Fin n → PMF (Fin n)) {v : Fin n →₀ ℂ} (hv : v ≠ 0)
    {c : ℂ} (hc : linMap (a := ⟨n⟩) (b := ⟨n⟩) f v = c • v) : ‖c‖ ≤ 1 := by
  have hpos : 0 < ∑ k, ‖v k‖ := by
    obtain ⟨k, hk⟩ := Finsupp.ne_iff.mp hv
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hk
    exact Finset.sum_pos' (fun i _ => norm_nonneg _) ⟨k, Finset.mem_univ k, norm_pos_iff.mpr hk⟩
  have h1 : ∑ k, ‖(c • v) k‖ ≤ ∑ k, ‖v k‖ := hc ▸ linMap_l1_nonexpansive f v
  have h2 : ∑ k, ‖(c • v) k‖ = ‖c‖ * ∑ k, ‖v k‖ := by
    simp_rw [Finsupp.smul_apply, smul_eq_mul, norm_mul]
    rw [← Finset.mul_sum]
  rw [h2] at h1
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

end ZeroParadox.SpectralRadius

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.SpectralRadius
#print axioms linMap_l1_nonexpansive
#print axioms eigenvalue_abs_le_one
end PurityCheck
