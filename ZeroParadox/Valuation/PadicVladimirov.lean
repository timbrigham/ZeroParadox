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
  -- The integrand equals the indicator of the complement of the ball (the units shell).
  have key : (fun y : ℤ_[p] => (ballFun (p := p) 1 0 - ballFun (p := p) 1 y)
        * ((vladimirovKernel α 0 y : ℝ) : ℂ))
      = Set.indicator {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ))}ᶜ (fun _ => (1 : ℂ)) := by
    funext y
    by_cases hy : ‖y‖ ≤ (p : ℝ)⁻¹
    · simp [ballFun, Set.mem_setOf_eq, Set.mem_compl_iff, norm_zero, hy]
    · have hnorm1 : ‖y‖ = 1 := by
        have hiff := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one y (-((1 : ℕ) : ℤ))
        rw [show (-((1 : ℕ) : ℤ) + 1) = 0 from by norm_num, zpow_zero, hpinv] at hiff
        exact le_antisymm (PadicInt.norm_le_one y) (not_lt.mp (fun h => hy (hiff.mpr h)))
      have hker : vladimirovKernel α 0 y = 1 := by
        simp only [vladimirovKernel, zero_sub, norm_neg, hnorm1, Real.one_rpow, inv_one]
      simp [ballFun, Set.mem_setOf_eq, Set.mem_compl_iff, norm_zero, hy, hker]
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

/-! ## § V — The general-`m` connection entry: `D^α 𝟙_{ball p⁻ᵐ}(0)`

The general-`m` matrix entry generalizes § IV (`m = 1`) by peeling one shell at a time. The complement
of `ball_m` decomposes into shells of norm `p⁻ᵏ` (`k = 0,…,m-1`); on shell `k` the kernel is the constant
`(p^α)^k · p^k`, so the radial integral is the geometric series `(1 - p⁻¹) ∑_{k<m} (p^α)^k`. -/

/-- The shell `ball_m \ ball_{m+1}` (points of norm exactly `p⁻ᵐ`). Matches `measure_ball_diff`. -/
noncomputable def shellSet (m : ℕ) : Set ℤ_[p] :=
  {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ))} \ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ))}

/-- The constant value of the singular kernel `|·|^{-(α+1)}` on shell `m` (where `‖y‖ = p⁻ᵐ`):
    `(p⁻ᵐ)^{-(α+1)} = p^{m(α+1)} = (p^α)^m · p^m`. Only `p^α` is an `rpow`; the rest is `npow`. -/
noncomputable def shellConst (α : ℝ) (m : ℕ) : ℝ := ((p : ℝ) ^ α) ^ m * (p : ℝ) ^ m

/-- The shell-load integrand: the shell `m` indicator scaled by the kernel's constant value there. -/
noncomputable def shellLoad (α : ℝ) (m : ℕ) : ℤ_[p] → ℂ :=
  Set.indicator (shellSet (p := p) m) (fun _ => ((shellConst (p := p) α m : ℝ) : ℂ))

/-- The integrand defining `D^α (ballFun m) 0`, isolated so it can carry an integrability induction. -/
noncomputable def vladIntegrand (α : ℝ) (m : ℕ) : ℤ_[p] → ℂ :=
  fun y => (ballFun (p := p) m 0 - ballFun (p := p) m y) * (vladimirovKernel α 0 y : ℂ)

/-- `shellSet m` is measurable (difference of two balls). -/
theorem shellSet_measurable (m : ℕ) : MeasurableSet (shellSet (p := p) m) :=
  (ball_measurableSet m).diff (ball_measurableSet (m + 1))

/-- On shell `m`, the norm is exactly `p⁻ᵐ` (a value sandwiched between two adjacent ball radii). -/
theorem norm_eq_of_mem_shell (m : ℕ) {y : ℤ_[p]} (hy : y ∈ shellSet (p := p) m) :
    ‖y‖ = (p : ℝ) ^ (-(m : ℤ)) := by
  simp only [shellSet, Set.mem_diff, Set.mem_setOf_eq] at hy
  obtain ⟨hin, hout⟩ := hy
  refine le_antisymm hin ?_
  have hiff := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one y (-((m + 1 : ℕ) : ℤ))
  rw [show (-((m + 1 : ℕ) : ℤ) + 1) = -(m : ℤ) from by push_cast; ring] at hiff
  exact not_lt.mp (fun h => hout (hiff.mpr h))

/-- On shell `m` (where `‖y‖ = p⁻ᵐ`), the singular kernel equals the constant `shellConst α m`. -/
theorem kernel_on_shell (α : ℝ) (m : ℕ) {y : ℤ_[p]} (h : ‖y‖ = (p : ℝ) ^ (-(m : ℤ))) :
    vladimirovKernel α 0 y = shellConst (p := p) α m := by
  have hP : (0 : ℝ) < (p : ℝ) := by exact_mod_cast ‹Fact p.Prime›.out.pos
  have hbase : ‖(0 : ℤ_[p]) - y‖ = (p : ℝ) ^ (-(m : ℤ)) := by rw [zero_sub, norm_neg, h]
  rw [vladimirovKernel, hbase, shellConst,
    ← Real.rpow_intCast (p : ℝ) (-(m : ℤ)), ← Real.rpow_mul hP.le, ← Real.rpow_neg hP.le,
    ← Real.rpow_natCast ((p : ℝ) ^ α) m, ← Real.rpow_mul hP.le, ← Real.rpow_natCast (p : ℝ) m,
    ← Real.rpow_add hP]
  congr 1
  push_cast
  ring

/-- **Shell load.** The integral of the shell-`m` load is `(1 - p⁻¹)(p^α)^m` — one term of the series. -/
theorem vladimirov_shell_load (α : ℝ) (m : ℕ) :
    ∫ y, shellLoad (p := p) α m y ∂(haarZp (p := p))
      = (((1 - (p : ℝ)⁻¹) * ((p : ℝ) ^ α) ^ m : ℝ) : ℂ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (‹Fact p.Prime›.out.pos).ne'
  have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast (‹Fact p.Prime›.out.pos).ne'
  have hle : ((p : ℝ≥0∞) ^ (m + 1))⁻¹ ≤ ((p : ℝ≥0∞) ^ m)⁻¹ :=
    ENNReal.inv_le_inv.mpr (pow_le_pow_right₀ hp1 (Nat.le_succ m))
  have htop : ((p : ℝ≥0∞) ^ m)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (pow_ne_zero m hp0)
  unfold shellLoad
  rw [integral_indicator_const _ (shellSet_measurable m), measureReal_def]
  unfold shellSet
  rw [measure_ball_diff m, ENNReal.toReal_sub_of_le hle htop]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  show (((p : ℝ) ^ m)⁻¹ - ((p : ℝ) ^ (m + 1))⁻¹) • ((shellConst (p := p) α m : ℝ) : ℂ) = _
  rw [Complex.real_smul, shellConst, ← Complex.ofReal_mul, Complex.ofReal_inj]
  field_simp
  ring

/-- The shell load is integrable (a constant times a finite-measure indicator). -/
theorem shellLoad_integrable (α : ℝ) (m : ℕ) :
    Integrable (shellLoad (p := p) α m) (haarZp (p := p)) := by
  rw [shellLoad]
  exact (integrable_const _).indicator (shellSet_measurable m)

/-- **Peeling step.** The `(m+1)`-integrand is the `m`-integrand plus the shell-`m` load. -/
theorem vladIntegrand_succ (α : ℝ) (m : ℕ) :
    vladIntegrand (p := p) α (m + 1)
      = fun y => vladIntegrand (p := p) α m y + shellLoad (p := p) α m y := by
  have hp1le : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
  have hc : ∀ k : ℕ, ballFun (p := p) k 0 = 1 := by
    intro k
    have hmem : (0 : ℤ_[p]) ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(k : ℤ))} := by
      simp only [Set.mem_setOf_eq, norm_zero]; positivity
    exact Set.indicator_of_mem hmem _
  funext y
  simp only [vladIntegrand, hc]
  simp only [ballFun, shellLoad]
  by_cases h1 : y ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ))}
  · have h2 : y ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ))} := by
      simp only [Set.mem_setOf_eq] at h1 ⊢
      exact le_trans h1 (zpow_le_zpow_right₀ hp1le (by omega))
    have hshell : y ∉ shellSet (p := p) m := by
      simp only [shellSet, Set.mem_diff, not_and, not_not]; intro _; exact h1
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem hshell]
    ring
  · by_cases h2 : y ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ))}
    · have hshell : y ∈ shellSet (p := p) m := by
        simp only [shellSet, Set.mem_diff]; exact ⟨h2, h1⟩
      have hnorm : ‖y‖ = (p : ℝ) ^ (-(m : ℤ)) := norm_eq_of_mem_shell m hshell
      have hker := kernel_on_shell α m hnorm
      simp only [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, Set.indicator_of_mem hshell,
        hker]
      ring
    · have hshell : y ∉ shellSet (p := p) m := by
        simp only [shellSet, Set.mem_diff, not_and]; intro hh; exact absurd hh h2
      simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2,
        Set.indicator_of_notMem hshell]
      ring

/-- The integrand is integrable for every `m` (induction: `g₀ = 0`; `g_{m+1} = g_m + shell load`). -/
theorem vladIntegrand_integrable (α : ℝ) (m : ℕ) :
    Integrable (vladIntegrand (p := p) α m) (haarZp (p := p)) := by
  induction m with
  | zero =>
    have hb : ballFun (p := p) 0 = fun _ => (1 : ℂ) := by
      funext z
      have hz : z ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} := by
        simp only [Set.mem_setOf_eq, Nat.cast_zero, neg_zero, zpow_zero]
        exact PadicInt.norm_le_one z
      exact Set.indicator_of_mem hz _
    have hz0 : vladIntegrand (p := p) α 0 = fun _ => 0 := by
      funext y; simp only [vladIntegrand, hb]; ring
    rw [hz0]; exact integrable_zero _ _ _
  | succ m ih =>
    rw [vladIntegrand_succ]
    exact ih.add (shellLoad_integrable α m)

/-- **General connection-matrix entry (Fourier-free).** `D^α` of the radius-`p⁻ᵐ` ball indicator at the
    center `0` is the geometric series `(1 - p⁻¹) ∑_{k<m} (p^α)^k` — the radial integral over the `m`
    shells peeled off the complement of `ball_m`. Recovers § IV at `m = 1`. -/
theorem vladimirov_ballFun_zero (α : ℝ) (m : ℕ) :
    vladimirov α (ballFun (p := p) m) 0
      = (((1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range m, ((p : ℝ) ^ α) ^ k : ℝ) : ℂ) := by
  induction m with
  | zero =>
    have hb : ballFun (p := p) 0 = fun _ => (1 : ℂ) := by
      funext z
      have hz : z ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} := by
        simp only [Set.mem_setOf_eq, Nat.cast_zero, neg_zero, zpow_zero]
        exact PadicInt.norm_le_one z
      exact Set.indicator_of_mem hz _
    rw [hb, vladimirov_const]
    simp
  | succ m ih =>
    have hstep : vladimirov α (ballFun (p := p) (m + 1)) 0
        = vladimirov α (ballFun (p := p) m) 0
          + ∫ y, shellLoad (p := p) α m y ∂(haarZp (p := p)) := by
      show (∫ y, vladIntegrand (p := p) α (m + 1) y ∂(haarZp (p := p)))
          = (∫ y, vladIntegrand (p := p) α m y ∂(haarZp (p := p)))
            + ∫ y, shellLoad (p := p) α m y ∂(haarZp (p := p))
      rw [← integral_add (vladIntegrand_integrable α m) (shellLoad_integrable α m)]
      congr 1
      exact vladIntegrand_succ α m
    rw [hstep, ih, vladimirov_shell_load, Finset.sum_range_succ]
    push_cast
    ring

/-! ## § VI — The symbol `|ξ|^α`, read off the connection matrix (Fourier-free)

The Taibleson–Vladimirov operator `D^α` is the Fourier multiplier by `|ξ|_p^α`. Its genuine eigenfunctions
are the Kozyrev wavelets, which need additive characters (the Fourier wall). But the *symbol itself* can be
read off the connection matrix without any Fourier transform: a ball of radius `p⁻ᵐ` has dual frequency
scale `|ξ|_p = p^m` (the reciprocal radius), and the per-shell increment of `D^α` at the center is exactly
`(1 - p⁻¹)·(p^m)^α = (1 - p⁻¹)·|ξ|^α`. This is an **operator-level** statement about `D^α` on ℤ_p; it makes
no dynamical or physical claim, and it is not an eigenvalue (the ball indicators are not eigenfunctions). -/

omit [Fact p.Prime] in
/-- The symbol identity: `(p^α)^m = (p^m)^α`. Rewrites the per-shell factor `(p^α)^m` into `|ξ|^α` form
    with `|ξ| = p^m` (the reciprocal of the ball radius `p⁻ᵐ`). -/
theorem pow_rpow_symbol (α : ℝ) (m : ℕ) : ((p : ℝ) ^ α) ^ m = ((p : ℝ) ^ m) ^ α := by
  have hP : (0 : ℝ) ≤ (p : ℝ) := by positivity
  rw [← Real.rpow_natCast ((p : ℝ) ^ α) m, ← Real.rpow_mul hP, ← Real.rpow_natCast (p : ℝ) m,
    ← Real.rpow_mul hP, mul_comm α (m : ℝ)]

/-- **The `|ξ|^α` symbol, Fourier-free.** The per-shell increment of `D^α` at the center is
    `(1 - p⁻¹)·(p^m)^α` — the Vladimirov symbol `|ξ|^α` evaluated at the shell's dual frequency scale
    `|ξ| = p^m`. Restates `vladimirov_shell_load` in symbol form via `pow_rpow_symbol`. -/
theorem vladimirov_shell_symbol (α : ℝ) (m : ℕ) :
    ∫ y, shellLoad (p := p) α m y ∂(haarZp (p := p))
      = (((1 - (p : ℝ)⁻¹) * ((p : ℝ) ^ m) ^ α : ℝ) : ℂ) := by
  rw [vladimirov_shell_load, pow_rpow_symbol]

/-- **Closed form of the connection entry.** When `p^α ≠ 1`, the geometric series sums, so `D^α` of the
    radius-`p⁻ᵐ` ball indicator at the center is `(1 - p⁻¹)·((p^α)^m - 1)/(p^α - 1)`. -/
theorem vladimirov_ballFun_geom (α : ℝ) (m : ℕ) (hα : (p : ℝ) ^ α ≠ 1) :
    vladimirov α (ballFun (p := p) m) 0
      = (((1 - (p : ℝ)⁻¹) * (((p : ℝ) ^ α) ^ m - 1) / ((p : ℝ) ^ α - 1) : ℝ) : ℂ) := by
  rw [vladimirov_ballFun_zero, geom_sum_eq hα]
  push_cast
  ring

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms vladimirov_const
#print axioms measure_ball_diff
#print axioms vladimirov_ballFun_one_zero
#print axioms vladimirov_shell_load
#print axioms vladimirov_ballFun_zero
#print axioms pow_rpow_symbol
#print axioms vladimirov_shell_symbol
#print axioms vladimirov_ballFun_geom
end PurityCheck
