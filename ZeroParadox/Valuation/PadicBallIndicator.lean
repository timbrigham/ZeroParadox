-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the p-adic norm-ball indicator as an element of L²(ℤ_p) and its L² norm, the first brick of the van der Put ball-indicator basis. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicHaar
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The p-adic ball indicator in L²(ℤ_p)

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Realizes the indicator `𝟙_{‖·‖ ≤ p⁻ⁿ}` of a p-adic norm-ball as an actual vector in `L²(ℤ_p, haarZp)`
(via Mathlib's `indicatorConstLp`), and computes its L² norm: `‖𝟙_ball‖ = (p⁻ⁿ)^(1/2)`. The norm drops
straight out of `‖𝟙_s‖ = μ(s)^(1/2)` together with the ball measure `haarZp_ball` (`μ(ball) = p⁻ⁿ`).
These ball indicators are the first brick of the van der Put ball-indicator basis. All standard once
the measure exists; no novelty claimed.

## Structure
- § I   Measurability of the norm-ball
- § II  The ball indicator as an L² vector, and its norm
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — Measurability of the norm-ball -/

/-- The p-adic norm-ball `{‖x‖ ≤ p⁻ⁿ}` is measurable (it is a metric closed ball). -/
theorem ball_measurableSet (n : ℕ) :
    MeasurableSet {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))} := by
  have hball : {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
      = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
    ext x; simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hball]; exact measurableSet_closedBall

/-! ## § II — The ball indicator as an L² vector, and its norm -/

/-- The indicator of the norm-ball `{‖x‖ ≤ p⁻ⁿ}` as an element of `L²(ℤ_p, haarZp)`. -/
noncomputable def ballIndicatorL2 (n : ℕ) : Lp ℂ 2 (haarZp (p := p)) :=
  indicatorConstLp 2 (ball_measurableSet n) (measure_ne_top (haarZp (p := p)) _) 1

/-- Its L² norm is `(p⁻ⁿ)^(1/2)`: combine `‖𝟙_s‖ = μ(s)^(1/2)` with `haarZp_ball` (`μ(ball) = p⁻ⁿ`). -/
theorem norm_ballIndicatorL2 (n : ℕ) :
    ‖ballIndicatorL2 (p := p) n‖ = ((p : ℝ) ^ n)⁻¹ ^ (1 / 2 : ℝ) := by
  rw [ballIndicatorL2, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul,
    measureReal_def, haarZp_ball, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat]

end ZeroParadox

/-! ## Axiom Purity Check

`norm_ballIndicatorL2` depends on `[propext, Classical.choice, Quot.sound]` — `Classical.choice` enters
through the Mathlib `Lp` / `MeasureTheory` libraries (a dependency, not a new commitment). -/
section PurityCheck
open ZeroParadox
#print axioms norm_ballIndicatorL2
end PurityCheck
