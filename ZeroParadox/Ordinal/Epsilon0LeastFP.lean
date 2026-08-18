import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 400000

/-!
# Batch 2 / G1 (pipeline, T6): ε₀ is the LEAST fixed point of α ↦ ωᵅ — the snap sits at minimal closure

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview
**Result: CONFIRMED.** ε₀ is the least fixed point of `α ↦ ω^α` — positionally the FIRST, never a
"ceiling" or "a large ordinal". ⚠ Least in the FIXED-POINT order, **not** order-adjacency: ordinals sit
strictly between ⊥ and ε₀. Which order, Veblen's Corollary 1, and the traps: `ZeroParadox/Ordinal/Epsilon0LeastFP.md`.
-/

namespace ZeroParadox

open Ordinal

/-- ε₀ is a fixed point of `α ↦ ω^α` (= Mathlib `omega0_opow_epsilon` at 0). -/
theorem epsilon0_is_fixedpoint : ω ^ ε₀ = ε₀ :=
  omega0_opow_epsilon 0

/-- **ε₀ is the LEAST fixed point.** Any ordinal `o` closed under exponentiation (`ω^o = o`) satisfies
    `ε₀ ≤ o`. With `epsilon0_is_fixedpoint`, ε₀ is the minimal closure — the snap sits at the least
    ordinal fixed by `α ↦ ω^α`, not a larger Veblen point. -/
theorem epsilon0_least_fixedpoint (o : Ordinal) (h : ω ^ o = o) : ε₀ ≤ o :=
  epsilon_zero_le_of_omega0_opow_le (le_of_eq h)

/-- **`Statement:` nothing strictly below ε₀ is a landing.** No ordinal under ε₀ is fixed by
`α ↦ ω^α`, so the intermediate ordinals are stages of the ascent rather than steps. This is the
checkable half of "ε₀ is the minimum distinct step above ⊥". -/
theorem nothing_between_is_a_step (o : Ordinal) (hlt : o < Ordinal.epsilon 0) :
    Ordinal.omega0 ^ o ≠ o :=
  fun h => absurd (epsilon0_least_fixedpoint o h) (not_le.mpr hlt)

/-- **`Statement:` and ⊥ is not a landing either**, so ε₀ is the first. -/
theorem bot_is_not_a_step : Ordinal.omega0 ^ (0 : Ordinal) ≠ (0 : Ordinal) := by simp

/-! ### The rungs are the structure — the seed is not load-bearing

`nothing_between_is_a_step` says no point strictly below ε₀ is a landing; the theorems below say the
complement, that **every point at or below ε₀ reaches the SAME landing**. ⚠ The general fact is that
`nfp (ω^·) a` is the least ε-number `≥ a`, so no ε-number can test it and the rungs do not partition.
Veblen's classical form, the three traps, and the SHAPE-never-instance-of fence: `ZeroParadox/Ordinal/Epsilon0LeastFP.md`. -/

/-- **`Statement:` every seed at or below ε₀ reaches ε₀.** The least fixed point *from* `a` is ε₀ for
every `a ≤ ε₀`, so within that range the seed carries no information: `≤` because ε₀ is itself a
fixed point at or above `a` (`epsilon0_is_fixedpoint` with `Ordinal.nfp_le_fp`), and `≥` because ε₀ is
the least fixed point outright (`epsilon0_least_fixedpoint` applied to `Ordinal.nfp_fp`). ⚠ Normality
of `α ↦ ω^α` is load-bearing, and `nothing_between_is_a_step` is **not** used. -/
theorem nfp_seed_independent_below_epsilon0 (a : Ordinal) (ha : a ≤ ε₀) :
    Ordinal.nfp (fun α => ω ^ α) a = ε₀ := by
  have hnorm := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  refine le_antisymm ?_ ?_
  · exact Ordinal.nfp_le_fp hnorm.strictMono.monotone ha (le_of_eq epsilon0_is_fixedpoint)
  · exact epsilon0_least_fixedpoint _ (Ordinal.nfp_fp hnorm a)

/-- **`Statement:` concretely — seeding at `1` is seeding at `⊥`.** The witness that makes the
seed-independence visible without a quantifier. -/
theorem nfp_seed_one_eq_seed_bot :
    Ordinal.nfp (fun α => ω ^ α) 1 = Ordinal.nfp (fun α => ω ^ α) (⊥ : Ordinal) := by
  rw [nfp_seed_independent_below_epsilon0 1 (Order.one_le_iff_ne_zero.mpr (Ordinal.epsilon_pos 0).ne'),
      nfp_seed_independent_below_epsilon0 ⊥ bot_le]

/-- **Invariant — ε₀ ≠ 0.** ε₀ can never be zero, in any reading. It is a fixed point of `α ↦ ω^α`
    (`epsilon0_is_fixedpoint`); were it 0, that would say `ω^0 = 0`, i.e. `1 = 0`. This is the bedrock
    guard beneath every ε₀ characterization. -/
theorem epsilon0_ne_zero : ε₀ ≠ 0 := by
  intro h
  have hf := epsilon0_is_fixedpoint
  rw [h, opow_zero] at hf
  exact one_ne_zero hf

/-- **Invariant — ε₀ ≠ ⊥.** Since `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`) and ε₀ ≠ 0, ε₀ is never
    the bottom ⊥. ⊥ is *a* base the ε₀-tower is seeded at (`epsilon0_eq_nfp_bot`), never its closure.
    It is the *least* such base and not the only one: for **normal** `F`, every seed at or below the
    closure reaches the same closure (`isLeastFixedPointFrom_nfp`). The invariant does not depend
    on that. -/
theorem epsilon0_ne_bot : ε₀ ≠ (⊥ : Ordinal) := by
  rw [Ordinal.bot_eq_zero]
  exact epsilon0_ne_zero

/-- **ε₀'s Veblen coordinates are (1, 0).** ε₀ = `veblen 1 0` (Mathlib `epsilon := veblen 1`, so this is
    definitional): the element at index 0 of level 1 — the origin of the Veblen coordinate system, hence
    the *minimum* fixed-point closure (matching `epsilon0_least_fixedpoint`), not a definitional pick of a
    large ordinal. The hierarchy continues above ε₀ (ε₁, ε₂, …, ζ₀ = `veblen 2 0`, …) up to Γ₀, the
    Feferman–Schütte ordinal closing the two-argument Veblen hierarchy; the framework lives below Γ₀. -/
theorem epsilon0_eq_veblen_one_zero : ε₀ = Ordinal.veblen 1 0 := rfl

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms epsilon0_is_fixedpoint
#print axioms epsilon0_least_fixedpoint
#print axioms nothing_between_is_a_step
#print axioms bot_is_not_a_step
#print axioms nfp_seed_independent_below_epsilon0
#print axioms nfp_seed_one_eq_seed_bot
#print axioms epsilon0_ne_zero
#print axioms epsilon0_ne_bot
#print axioms epsilon0_eq_veblen_one_zero
end PurityCheck
