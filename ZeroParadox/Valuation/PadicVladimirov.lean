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

/-! ## § IV — A connection-matrix entry: D^α of a ball indicator at the center -/

/-- The radius-`p⁻ᵐ` ball indicator `𝟙_{‖·‖ ≤ p⁻ᵐ}` as a function `ℤ_p → ℂ`. -/
noncomputable def ballFun (m : ℕ) : ℤ_[p] → ℂ :=
  Set.indicator {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ))} (fun _ => 1)

/-- **Connection-matrix entry (Fourier-free).** `D^α` of the radius-`p⁻¹` ball indicator, evaluated at
    the center `0`, is the units-shell mass `1 - p⁻¹` — and `α` drops out, because the units have norm
    `1` so the singular kernel equals `1` on the whole support. (This is a matrix entry of `D^α` in the
    ball-indicator basis, not a full eigenvalue: a genuine eigenfunction is a Kozyrev wavelet, which
    needs additive characters.) -/
theorem vladimirov_ballFun_one_zero (α : ℝ) :
    vladimirov α (ballFun (p := p) 1) 0 = (1 : ℂ) - (p : ℂ)⁻¹ := by
  have hpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast ‹Fact p.Prime›.out.pos
  have hpinv : (p : ℝ) ^ (-((1 : ℕ) : ℤ)) = (p : ℝ)⁻¹ := by simp
  have h0true : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  -- The integrand equals the indicator of the complement of the ball (the units shell).
  have key : (fun y : ℤ_[p] => (ballFun (p := p) 1 0 - ballFun (p := p) 1 y)
        * ((vladimirovKernel α 0 y : ℝ) : ℂ))
      = Set.indicator {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ))}ᶜ (fun _ => (1 : ℂ)) := by
    funext y
    by_cases hy : ‖y‖ ≤ (p : ℝ)⁻¹
    · simp [ballFun, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_compl_iff, norm_zero, hpinv,
        h0true, hy]
    · have hnorm1 : ‖y‖ = 1 := by
        have hiff := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one y (-((1 : ℕ) : ℤ))
        rw [show (-((1 : ℕ) : ℤ) + 1) = 0 from by norm_num, zpow_zero, hpinv] at hiff
        exact le_antisymm (PadicInt.norm_le_one y) (not_lt.mp (fun h => hy (hiff.mpr h)))
      have hker : vladimirovKernel α 0 y = 1 := by
        simp only [vladimirovKernel, zero_sub, norm_neg, hnorm1, Real.one_rpow, inv_one]
      simp [ballFun, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_compl_iff, norm_zero, hpinv,
        h0true, hy, hker]
  unfold vladimirov
  rw [key, integral_indicator_const (1 : ℂ) (ball_measurableSet 1).compl, measureReal_def,
    measure_compl (ball_measurableSet 1) (measure_ne_top _ _), measure_univ, haarZp_ball]
  have hle : ((p : ℝ≥0∞) ^ 1)⁻¹ ≤ 1 := by
    rw [pow_one]; exact ENNReal.inv_le_one.mpr (by exact_mod_cast ‹Fact p.Prime›.out.one_lt.le)
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, pow_one]
  show ((1 : ℝ) - (p : ℝ)⁻¹) • (1 : ℂ) = (1 : ℂ) - (p : ℂ)⁻¹
  rw [Complex.real_smul, mul_one]
  push_cast
  ring

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms vladimirov_const
#print axioms measure_ball_diff
#print axioms vladimirov_ballFun_one_zero
end PurityCheck
