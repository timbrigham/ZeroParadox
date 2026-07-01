import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 400000

/-!
# Batch 2 / G3 (pipeline, T6): the 0↔∞ duality on the 2-adic NORM (metric side of the flip)

Experiment G3 (T6 compute-the-invariant). Item 1 (`ZPH_MC1_PolarityFlip`) realized the 0↔∞ flip on the
*valuation* (`v₂(x⁻¹) = −v₂(x)`). This is the *metric* companion: the snap tower `2ⁿ` has 2-adic norm
`‖2ⁿ‖ = 2⁻ⁿ → 0` (approach to 0), and its inverse `2⁻ⁿ` has norm `‖(2ⁿ)⁻¹‖ = 2ⁿ → ∞` (approach to ∞). So
the inversion sends a sequence collapsing to the floor into one diverging to infinity — the zero=infinity
duality made metric.

Falsifiable prediction: `‖(2ⁿ)⁻¹‖ = 2ⁿ` and it diverges. Would FAIL if the 2-adic norm did not invert
under `x⁻¹`. `norm_inv` + `‖2‖ = 1/2` give the equality; `2ⁿ → ∞` the divergence. **Result: CONFIRMED.**

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.G3

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open Filter Topology

/-- The inverse-tower 2-adic norm: `‖(2ⁿ)⁻¹‖ = 2ⁿ` in ℚ₂ (the norm inverts: `‖2‖ = 1/2`). -/
theorem inv_tower_norm (n : ℕ) : ‖((2 : ℚ_[2]) ^ n)⁻¹‖ = 2 ^ n := by
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have h2c : (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) := by norm_cast
    rw [h2c, Padic.norm_p]; norm_num
  rw [norm_inv, norm_pow, h2, inv_pow, inv_inv]

/-- **The metric 0↔∞ flip.** The inverse-tower norms `‖(2ⁿ)⁻¹‖ = 2ⁿ` diverge to ∞: inversion turns the
    snap tower's collapse to the floor (`‖2ⁿ‖ → 0`) into a divergence to infinity. -/
theorem inv_tower_norm_tendsto_atTop :
    Tendsto (fun n : ℕ => ‖((2 : ℚ_[2]) ^ n)⁻¹‖) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  refine h.congr (fun n => ?_)
  rw [inv_tower_norm]

end ZeroParadox.G3

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.G3
#print axioms inv_tower_norm
#print axioms inv_tower_norm_tendsto_atTop
end PurityCheck
