import ZeroParadox.ZPH_PerronFrobenius
import ZeroParadox.ZPH_MC1_LinFunctor

set_option maxHeartbeats 400000

/-!
# Deep cross-domain entry: the transfer operator has a unit eigenvector (existence ⟹ existence)

The first genuinely deep dictionary entry that crosses a domain boundary. It composes the deep stochastic-side
existence result (`PerronFrobenius.exists_stationary`, cold-audited SOUND) with the info→Hilbert transport
(`FinStoch.stationary_transports_to_unit_eigenvector`) to conclude: the linearized transfer operator on the
Hilbert side has a NONZERO fixed vector (a unit eigenvector). The depth is inherited from existence — the
Hilbert-side eigenvector cannot be produced without the stochastic existence theorem (the trivial all-ones
vector is only the LEFT eigenvector; the right one is the stationary distribution). So existence on the
stochastic side proves existence on the Hilbert side, through the bridge.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.EigenvectorExists

open ZeroParadox.FinStoch ZeroParadox.PerronFrobenius

/-- **Deep cross-domain existence.** For any finite stochastic kernel `f`, the linearized transfer operator
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
    push_neg at h
    have hz : ∑' i, μ i = 0 := by simp only [h, tsum_zero]
    rw [μ.tsum_coe] at hz
    exact one_ne_zero hz
  have hcoord : ((μ i).toReal : ℂ) = 0 := by
    have hh := DFunLike.congr_fun hzero i
    simpa [Finsupp.coe_equivFunOnFinite_symm] using hh
  exact (ENNReal.toReal_ne_zero.mpr ⟨hi, μ.apply_ne_top i⟩) (by exact_mod_cast hcoord)

end ZeroParadox.EigenvectorExists

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.EigenvectorExists
#print axioms transfer_operator_has_unit_eigenvector
end PurityCheck
