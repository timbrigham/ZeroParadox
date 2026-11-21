-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): on ℤ_p, the integral of a level-n character over the closed ball of radius p^(-j) about 0 is p^(-j) when n ≤ j, for every character, and 0 when j < n, for a primitive one. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicStillPoint
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# On ℤ_p, a level-n character integrates over the closed ball of radius p^(-j) about 0 to p^(-j) when n ≤ j (every character) and, for a primitive character, to 0 when j < n

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
`Statement:` per character `φ` of `ZMod (p ^ n)`, on Haar `ℤ_p`: ball integrals of `paChar n φ`. Stated
per primitive `φ` at level `n`; the reading "the transform of a ball is the indicator of a dual ball" over
the whole dual group is not stated, since no level parametrization of every character is built.
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-- `Statement:` `paChar n φ z = 1` whenever `‖z‖ ≤ p^(-n)`, for every `φ`. -/
theorem paChar_eq_one_of_norm_le (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) {z : ℤ_[p]}
    (hz : ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))) : paChar (p := p) n φ z = 1 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have h0 : (p : ZMod (p ^ n)) ^ n = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hz0 : PadicInt.toZModPow n z = 0 := by
    have := (norm_le_iff_dvd_toZModPow n n le_rfl z).mp hz
    rwa [h0, zero_dvd_iff] at this
  simp [paChar, hz0]

/-- `Statement:` for `n ≤ j` and every `φ`, `∫` over `{‖z‖ ≤ p^(-j)}` of `paChar n φ` is `p^(-j)`. -/
theorem paChar_ball_integral_of_le (n j : ℕ) (hnj : n ≤ j) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p)) = ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) := by
  have hval : Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ)
      = Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      refine paChar_eq_one_of_norm_le n φ (le_trans hx (zpow_le_zpow_right₀ ?_ ?_))
      · exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
      · omega
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [hval, integral_indicator_const _ (ball_measurableSet j), measureReal_def, haarZp_ball,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  show (((p : ℝ) ^ j)⁻¹ : ℝ) • (1 : ℂ) = ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ)
  rw [Complex.real_smul, mul_one]

/-- `Statement:` for primitive `φ`, `∫` over `{‖z‖ ≤ p^(-j)}` of `paChar n φ` is `p^(-j)` if
`n ≤ j` and `0` otherwise; combines `paChar_ball_integral_of_le` and `paChar_ball_integral_eq_zero`. -/
theorem paChar_ball_integral_tradeoff (n j : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ)
    (hφ : φ.IsPrimitive) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p)) = if n ≤ j then ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · exact paChar_ball_integral_of_le n j h φ
  · exact paChar_ball_integral_eq_zero n φ hφ (by omega)

-- Reading: over ℚ_p this is the standard ball transform F[Ω(p^(-k)|·|_p)](ξ) = p^k Ω(p^k|ξ|_p)
-- (Vladimirov–Volovich–Zelenov, p-adic Analysis and Mathematical Physics, IV (3.1), as quoted in
-- Khrennikov–Shelkovich, arXiv:0808.3338, eq. (2.9)); a Lean ℚ_p form is
-- `QuadFormsKB.Analysis.fourierP_ballInd` (jonhanke/quadratic-forms-lean).

/-- `Statement:` at every level `n`, the trivial character `paChar n 0` integrates to `1` over
`{‖z‖ ≤ p^0}`, which is all of `ℤ_p`. -/
theorem paChar_trivial_ball_zero (n : ℕ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} (paChar (p := p) n 0) x
      ∂(haarZp (p := p)) = 1 := by
  rw [paChar_trivial, integral_indicator_const _ (ball_measurableSet 0), measureReal_def,
    haarZp_ball]
  simp

-- Statement: CONTROL, primitivity is load-bearing in `paChar_ball_integral_tradeoff`: for `n ≥ 1`,
-- `φ = 0` with `j = 0 < n` integrates to `1 ≠ 0`.
example (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℕ) < n ∧
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} (paChar (p := p) n 0) x
      ∂(haarZp (p := p)) ≠ 0 := by
  refine ⟨by omega, ?_⟩
  rw [paChar_trivial_ball_zero]; exact one_ne_zero

-- Statement: and for `n ≥ 1`, `φ = 0` is not primitive, so the control sits outside that hypothesis.
example (n : ℕ) (hn : 1 ≤ n) : ¬ (0 : AddChar (ZMod (p ^ n)) ℂ).IsPrimitive := by
  intro h
  have : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have h1 : (1 : ZMod (p ^ n)) ≠ 0 := by
    have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow (by omega) ‹Fact p.Prime›.out.one_lt⟩
    exact one_ne_zero
  have := h h1
  apply this
  ext x
  simp

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_eq_one_of_norm_le
#print axioms paChar_ball_integral_of_le
#print axioms paChar_ball_integral_tradeoff
#print axioms paChar_trivial_ball_zero
end PurityCheck
