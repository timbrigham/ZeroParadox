-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the Taibleson–Vladimirov singular-integral operator D^α on ℤ_p, its vanishing on constants, and the annulus (shell) measures that turn radial integrals into geometric series. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicHaar
import ZeroParadox.Valuation.PadicBallIndicator
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Taibleson–Vladimirov operator D^α on ℤ_p

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Defines the **Taibleson–Vladimirov operator** `D^α` in its singular-integral form on `ℤ_p`,
`(D^α f)(x) = ∫ (f x - f y) · |x-y|^{-(α+1)} dy` against the Haar measure. Two results: (i) `D^α` kills
constants (the difference `f x - f y` vanishes); (ii) the **annulus measures** `μ(ball_k \ ball_{k+1})
= p^{-k} - p^{-(k+1)}`, the building block that makes a radial integral over `ℤ_p` a geometric series
(each drops out of `haarZp_ball`). Pure math; the value is that Mathlib has no p-adic pseudodifferential
operator, so the construction is built here.

## Structure
- § I   The operator (singular-integral form)
- § II  Vanishing on constants
- § III Annulus (shell) measures
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — The operator (singular-integral form) -/

/-- The singular kernel `|x-y|^{-(α+1)}` (junk value `0` on the diagonal, via `0⁻¹ = 0`). -/
noncomputable def vladimirovKernel (α : ℝ) (x y : ℤ_[p]) : ℝ := (‖x - y‖ ^ (α + 1))⁻¹

/-- The Taibleson–Vladimirov operator `D^α` on `ℤ_p`, singular-integral form. -/
noncomputable def vladimirov (α : ℝ) (f : ℤ_[p] → ℂ) (x : ℤ_[p]) : ℂ :=
  ∫ y, (f x - f y) * (vladimirovKernel α x y : ℂ) ∂(haarZp (p := p))

/-! ## § II — Vanishing on constants -/

/-- `D^α` kills constants: the difference `c - c` vanishes pointwise, so the integral is `0`. -/
theorem vladimirov_const (α : ℝ) (c : ℂ) (x : ℤ_[p]) :
    vladimirov α (fun _ => c) x = 0 := by
  simp only [vladimirov, sub_self, zero_mul, integral_zero]

/-! ## § III — Annulus (shell) measures -/

/-- **Annulus measure.** The shell `ball_k \ ball_{k+1}` (points of norm exactly `p^{-k}`) has Haar
    measure `p^{-k} - p^{-(k+1)}`. Straight from `haarZp_ball`; the radial building block. -/
theorem measure_ball_diff (k : ℕ) :
    haarZp (p := p)
        ({x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ))} \
          {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ))})
      = ((p : ℝ≥0∞) ^ k)⁻¹ - ((p : ℝ≥0∞) ^ (k + 1))⁻¹ := by
  have hsub : {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ))}
      ⊆ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ))} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    refine le_trans hx (zpow_le_zpow_right₀ ?_ ?_)
    · exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
    · omega
  rw [measure_diff hsub (ball_measurableSet (k + 1)).nullMeasurableSet (measure_ne_top _ _),
    haarZp_ball, haarZp_ball]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms vladimirov_const
#print axioms measure_ball_diff
end PurityCheck
