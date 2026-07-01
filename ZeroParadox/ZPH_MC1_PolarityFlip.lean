-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.NumberTheory.Padics.PadicNumbers

set_option maxHeartbeats 400000

/-!
# 2-adic inversion negates the valuation (a cited Mathlib fact + one tower corollary)

**Proves.** `padic_inv_flips_valuation` IS Mathlib's `Padic.valuation_inv` (`v₂(x⁻¹) = −v₂(x)`), cited not
reproved. `tower_inv_valuation` is the corollary `v₂((2ⁿ)⁻¹) = −n` (from `valuation_inv` + `valuation_pow`
+ `valuation_p`). That is the formal content: inversion negates the 2-adic valuation, and on the tower
`n ↦ −n`.

**Reaching for (intent, NOT proved here).** This was *meant to* be the generator of the framework's 0=∞
"polarity flip" — reading the valuation sign-flip as turning the Top bottom's inverse-limit-toward-0 into a
direct-limit-toward-∞ (the same object from the ∞-side), the principled route around the Top no-go.

**Gap (as far as this reaches).** The "polarity flip / aligns Top with the cluster / removes the no-go"
reading is a framework interpretation of a valuation sign-fact; no category, functor, or polarity object
appears in the Lean. The flip's role in any comparison is conjecture (`...construction_spec...`, see its
correction). The valuation fact itself is solid and Mathlib's.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1_PolarityFlip

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open Padic

/-- **The polarity-flip generator (= Mathlib `Padic.valuation_inv`).** 2-adic inversion negates the
    valuation: `v₂(x⁻¹) = −v₂(x)`. The framework's 0↔∞ probe reversal as a field fact. Cited, not reproved. -/
theorem padic_inv_flips_valuation (x : ℚ_[2]) : (x⁻¹).valuation = - x.valuation :=
  Padic.valuation_inv x

/-- **The flip on the snap tower.** `v₂((2ⁿ)⁻¹) = −n`: the tower point `2ⁿ` (valuation `n`, approach to 0,
    `v→+∞`) inverts to `2⁻ⁿ` (valuation `−n`, approach to ∞, `v→−∞`). The inverse-limit toward 0 becomes a
    direct limit toward ∞ — F_B's limit polarity flipped to colimit, the same object from the ∞-side. -/
theorem tower_inv_valuation (n : ℕ) : (((2 : ℚ_[2]) ^ n)⁻¹).valuation = -(n : ℤ) := by
  rw [Padic.valuation_inv, Padic.valuation_pow]
  have h2 : (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) := by norm_cast
  rw [h2, Padic.valuation_p, mul_one]

end ZeroParadox.ZPH_MC1_PolarityFlip

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_PolarityFlip
#print axioms padic_inv_flips_valuation
#print axioms tower_inv_valuation
end PurityCheck
