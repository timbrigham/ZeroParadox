import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 400000

/-!
# Batch 2 / G1 (pipeline, T6): ε₀ is the LEAST fixed point of α ↦ ωᵅ — the snap sits at minimal closure

Experiment G1 (T6 compute-the-invariant), independent of the MC-1 arc. ε₀ is where the ω-tower closes —
its **minimal** closure. **Do not call it a "ceiling" or "a large ordinal"** (an earlier revision of this
line said "the snap ceiling"): positionally ε₀ is the FIRST — `Ordinal.epsilon 0`, index zero in the
epsilon enumeration, Veblen coordinates (1,0), the minimum step next to the pole — and that is exactly what
`epsilon0_least_fixedpoint` below proves. Its magnitude as a tower supremum is large; its position is
first. Both faces are live (`epsilon0_min_eq_max`), and collapsing to the magnitude face is the recorded
error this line used to commit. Being a position, it carries no units. Falsifiable prediction: ε₀ is not just *a* fixed point of `α ↦ ω^α` but the **least** one —
the snap is located at the *minimal* ordinal closed under exponentiation, not at some larger Veblen point.
Would FAIL if some `o < ε₀` satisfied `ω^o = o` (then the snap closure wouldn't be minimal).

**Result: CONFIRMED.** `epsilon0_is_fixedpoint` (`ω ^ ε₀ = ε₀`) and `epsilon0_least_fixedpoint` (any
`o` with `ω^o = o` has `ε₀ ≤ o`) together pin ε₀ as the least fixed point. So the snap closure is minimal —
the framework's "snap at the minimum fixed-point closure" (Veblen-angle) as a two-line theorem. Both reuse
Mathlib (`omega0_opow_epsilon`, `epsilon_zero_le_of_omega0_opow_le`), cited not reproved.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
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

/-- **Invariant — ε₀ ≠ 0.** ε₀ can never be zero, in any reading. It is a fixed point of `α ↦ ω^α`
    (`epsilon0_is_fixedpoint`); were it 0, that would say `ω^0 = 0`, i.e. `1 = 0`. This is the bedrock
    guard beneath every ε₀ characterization. -/
theorem epsilon0_ne_zero : ε₀ ≠ 0 := by
  intro h
  have hf := epsilon0_is_fixedpoint
  rw [h, opow_zero] at hf
  exact one_ne_zero hf

/-- **Invariant — ε₀ ≠ ⊥.** Since `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`) and ε₀ ≠ 0, ε₀ is never
    the bottom ⊥. ⊥ is *a* base the ε₀-tower is seeded at (`epsilon0_eq_nfp_bot`), never its closure
    — and not a distinguished base: every seed at or below the closure reaches the same closure
    (`ZeroParadox/Ordinal/Epsilon0MinMax.lean` § I-b). The invariant does not depend on that. -/
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
#print axioms epsilon0_ne_zero
#print axioms epsilon0_ne_bot
#print axioms epsilon0_eq_veblen_one_zero
end PurityCheck
