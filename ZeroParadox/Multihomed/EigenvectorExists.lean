import ZeroParadox.Reals.PerronFrobenius
import ZeroParadox.Category.LinFunctor

set_option maxHeartbeats 400000

/-!
# Deep cross-domain entry: the transfer operator has a unit eigenvector (existence ⟹ existence)

Composes the stochastic-side existence theorem `exists_stationary` with the info→Hilbert transport
`stationary_transports_to_unit_eigenvector`: the linearized transfer operator has a NONZERO fixed vector
(a unit eigenvector). A nonzero fixed vector of the transfer matrix `P f` alone needs no stochastic
existence: the all-ones vector is a LEFT fixed vector, so `P f - 1` is singular (the `example` below).
What `exists_stationary` adds is a fixed vector that is a probability distribution:
`perron_frobenius_finite` (`ZeroParadox/Order/PerronCapstone.lean`).

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

open ZeroParadox ZeroParadox

/-- **Deep cross-domain existence.** For any finite stochastic kernel `f` on a nonempty state space
    (`[Nonempty (Fin n)]`; at `n = 0` no vector is nonzero), the linearized transfer operator
    `linMap f` has a nonzero fixed vector (eigenvalue `1`). Proved by transporting the stationary distribution
    (whose existence is `exists_stationary`) across the linearization. -/
theorem transfer_operator_has_unit_eigenvector {n : ℕ} [Nonempty (Fin n)]
    (f : Fin n → PMF (Fin n)) :
    ∃ v : Fin n →₀ ℂ, v ≠ 0 ∧ linMap (a := ⟨n⟩) (b := ⟨n⟩) f v = v := by
  obtain ⟨μ, hμ⟩ := exists_stationary f
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i => ((μ i).toReal : ℂ)), ?_,
    stationary_transports_to_unit_eigenvector f μ hμ⟩
  intro hzero
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : ∑' i, μ i = 0 := by simp only [h, tsum_zero]
    rw [μ.tsum_coe] at hz
    exact one_ne_zero hz
  have hcoord : ((μ i).toReal : ℂ) = 0 := by
    have hh := DFunLike.congr_fun hzero i
    simpa [Finsupp.coe_equivFunOnFinite_symm] using hh
  exact (ENNReal.toReal_ne_zero.mpr ⟨hi, μ.apply_ne_top i⟩) (by exact_mod_cast hcoord)

-- `Statement:` the transfer matrix `P f` has a nonzero fixed vector by linear algebra alone: the
-- all-ones vector is killed by `(P f - 1)ᵀ`, so the determinant vanishes. `exists_stationary` is not
-- used, and nothing here makes the vector nonnegative.
example {n : ℕ} [Nonempty (Fin n)] (f : Fin n → PMF (Fin n)) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ (P f).mulVec v = v := by
  set M : Matrix (Fin n) (Fin n) ℝ := P f - 1 with hM
  have hT : M.transpose.mulVec (fun _ => (1 : ℝ)) = 0 := by
    ext j
    have hr := row_sum f j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_one, hM, Matrix.sub_apply,
      Finset.sum_sub_distrib, Matrix.one_apply, Pi.zero_apply]
    simp only [P, Matrix.of_apply, hr]
    simp
  have hdet : M.det = 0 := by
    rw [← Matrix.det_transpose, ← Matrix.exists_mulVec_eq_zero_iff]
    obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
    exact ⟨fun _ => 1, fun h => by simpa using congrFun h i, hT⟩
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact ⟨v, hv, sub_eq_zero.mp (by simpa [hM, Matrix.sub_mulVec] using hMv)⟩

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms transfer_operator_has_unit_eigenvector
end PurityCheck
