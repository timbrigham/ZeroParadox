-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a genuine eigenfunction of the ℤ_p Taibleson–Vladimirov operator D^α — the level-1 p-adic additive character, with eigenvalue 1. Unlike the ball-indicator matrix entries of PadicVladimirov §IV, this is a true eigenfunction, and the character orthogonality ∫χ=0 (the "crane") is exactly what closes the computation. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicVladimirov
import ZeroParadox.Valuation.PadicCharacter
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# A genuine eigenfunction of D^α: the level-1 p-adic character

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The Vladimirov operator `D^α` (`PadicVladimirov`) has genuine eigenfunctions — the Kozyrev wavelets,
built from the p-adic additive characters (`PadicCharacter`). This file proves the first one on `ℤ_p`:
the **level-1 character `paChar 1 φ` is an eigenfunction of `D^α`, with eigenvalue 1**.

The computation is Fourier-free and rests on two facts already built: (i) `paChar 1 φ` is *constant on
every ball of radius `p⁻¹`* (`paChar_locally_constant`), so the difference `χ(x) − χ(y)` vanishes exactly
where the singular kernel `|x−y|^{-(α+1)}` is `> 1` — the difference regularizes the singularity, and the
kernel factor collapses to `1` on the whole space; (ii) a nontrivial character *integrates to zero*
(`paChar_integral_eq_zero`, the "crane"). Then
`D^α χ (x) = ∫ (χ(x) − χ(y)) dy = χ(x)·μ(ℤ_p) − ∫ χ = χ(x)·1 − 0 = χ(x)`.

**Fences.** This is the *compact* `ℤ_p` operator, whose eigenvalue here is `1` — not the full-space
symbol `|ξ|^α`. The difference is exactly the large-scale shells `‖x−y‖ > 1` that the `ℚ_p` operator
integrates over and this compact one omits; recovering `|ξ|^α` needs the `ℚ_p` operator, not built here.
The point is structural: these characters are *eigenfunctions*, where the ball indicators of § IV were
only matrix entries. No physical or dynamical claim.

## Structure
- § I   Integrability of the character
- § II  The level-1 eigenfunction `D^α (paChar 1 φ) = paChar 1 φ`
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — Integrability of the character -/

/-- A p-adic character is integrable (a finite sum of constant indicators on finite-measure fibers). -/
theorem paChar_integrable (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    Integrable (paChar (p := p) n φ) (haarZp (p := p)) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hdecomp : paChar (p := p) n φ
      = fun x => ∑ r : ZMod (p ^ n),
          Set.indicator {y : ℤ_[p] | PadicInt.toZModPow n y = r} (fun _ => φ r) x := by
    funext x
    simp only [paChar, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [hdecomp]
  apply integrable_finset_sum
  intro r _
  exact (integrable_const (φ r)).indicator (toZModPow_fiber_measurableSet n r)

/-! ## § II — The level-1 eigenfunction -/

/-- **The level-1 character is an eigenfunction of `D^α`, with eigenvalue 1.** Because `paChar 1 φ` is
    constant on radius-`p⁻¹` balls, the kernel factor collapses to `1`, and the crane `∫ χ = 0` closes
    the integral: `D^α (paChar 1 φ) = paChar 1 φ`. -/
theorem vladimirov_paChar_one (α : ℝ) (φ : AddChar (ZMod (p ^ 1)) ℂ) (hφ : φ ≠ 0) (x : ℤ_[p]) :
    vladimirov α (paChar (p := p) 1 φ) x = paChar (p := p) 1 φ x := by
  have hint : (fun y => (paChar (p := p) 1 φ x - paChar (p := p) 1 φ y)
        * (vladimirovKernel α x y : ℂ))
      = fun y => paChar (p := p) 1 φ x - paChar (p := p) 1 φ y := by
    funext y
    by_cases hxy : ‖x - y‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ))
    · rw [paChar_locally_constant 1 φ hxy]; ring
    · have hnorm1 : ‖x - y‖ = 1 := by
        have hiff := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (x - y) (-((1 : ℕ) : ℤ))
        rw [show (-((1 : ℕ) : ℤ) + 1) = 0 from by norm_num, zpow_zero] at hiff
        exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp (fun h => hxy (hiff.mpr h)))
      have hker : vladimirovKernel α x y = 1 := by
        simp only [vladimirovKernel, hnorm1, Real.one_rpow, inv_one]
      rw [hker]; push_cast; ring
  have hci : Integrable (fun _ : ℤ_[p] => paChar (p := p) 1 φ x) (haarZp (p := p)) :=
    integrable_const _
  unfold vladimirov
  rw [hint, integral_sub hci (paChar_integrable 1 φ), integral_const,
    paChar_integral_eq_zero 1 φ hφ, sub_zero, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_integrable
#print axioms vladimirov_paChar_one
end PurityCheck
