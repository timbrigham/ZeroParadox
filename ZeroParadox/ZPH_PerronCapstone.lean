import ZeroParadox.ZPH_SpectralRadius
import ZeroParadox.ZPH_EigenvectorExists

set_option maxHeartbeats 400000

/-!
# Capstone: Perron–Frobenius for finite stochastic operators

Assembles the cold-audited pieces into the complete, recognizable Perron–Frobenius statement for the
linearized transfer operator of a finite stochastic kernel:
1. **Top eigenvalue with a probability eigenvector** — there is a genuine probability vector `w` (nonnegative,
   summing to 1) whose free-module image is fixed by `linMap f` (eigenvalue `1`). The DEPTH is inherited from
   `exists_stationary` (the Krylov–Bogolyubov existence theorem); the positivity/normalization is the Perron
   eigenvector being a distribution.
2. **Spectral radius ≤ 1** — every eigenvalue `c` satisfies `‖c‖ ≤ 1` (`eigenvalue_abs_le_one`).

Together: the spectral radius is exactly `1`, attained by a probability eigenvector. Honest scope: this is the
standard finite Perron–Frobenius/Markov theorem faithfully assembled — the genuine depth is upstream in
`exists_stationary`; this theorem is the legible headline.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.PerronCapstone

open ZeroParadox.FinStoch ZeroParadox.PerronFrobenius ZeroParadox.SpectralRadius

/-- **Perron–Frobenius for a finite stochastic kernel.** (i) There is a probability vector `w`
    (`0 ≤ w i`, `∑ w i = 1`) whose free-module image is a unit eigenvector of the transfer operator
    `linMap f`; (ii) every eigenvalue has modulus `≤ 1`. So the spectral radius is exactly `1`, attained by a
    probability distribution (the stationary distribution). -/
theorem perron_frobenius_finite {n : ℕ} [Nonempty (Fin n)] (f : Fin n → PMF (Fin n)) :
    (∃ w : Fin n → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      linMap (a := ⟨n⟩) (b := ⟨n⟩) f (Finsupp.equivFunOnFinite.symm (fun i => ((w i : ℂ))))
        = Finsupp.equivFunOnFinite.symm (fun i => ((w i : ℂ)))) ∧
    (∀ (v : Fin n →₀ ℂ) (c : ℂ), v ≠ 0 →
      linMap (a := ⟨n⟩) (b := ⟨n⟩) f v = c • v → ‖c‖ ≤ 1) := by
  refine ⟨?_, fun v c hv hc => eigenvalue_abs_le_one f hv hc⟩
  obtain ⟨μ, hμ⟩ := exists_stationary f
  refine ⟨fun i => (μ i).toReal, fun i => ENNReal.toReal_nonneg, ?_,
    stationary_transports_to_unit_eigenvector f μ hμ⟩
  have h1 : ∑ i, μ i = 1 := by
    have h := μ.tsum_coe
    rwa [tsum_eq_sum (s := Finset.univ) (fun x hx => absurd (Finset.mem_univ x) hx)] at h
  rw [← ENNReal.toReal_sum (fun i _ => μ.apply_ne_top i), h1, ENNReal.toReal_one]

end ZeroParadox.PerronCapstone

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.PerronCapstone
#print axioms perron_frobenius_finite
end PurityCheck
