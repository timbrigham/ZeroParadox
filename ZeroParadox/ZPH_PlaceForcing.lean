import ZeroParadox.ZPH_ArchPlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Direction A, Cycle A2 — the archimedean place is the product-formula balancer

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

A1 (`ZPH_ArchPlace`) located node #2 over ℚ's unique archimedean place. A2 supplies the *role*: the
**product formula** makes that archimedean place not optional but **forced**.

Mathlib's `NumberField.prod_abs_eq_one` at K = ℚ states
`(∏ w : InfinitePlace ℚ, w x ^ w.mult) * ∏ᶠ w : FinitePlace ℚ, w x = 1` — the archimedean (infinite)
factor times the finite (p-adic) product equals the global 1. Two consequences:

- `archimedean_place_unique_rat` — `InfinitePlace ℚ` is a subsingleton: ℚ has exactly ONE archimedean
  place, the slot A1 put #2 in.
- `archimedean_factor_forced` — the archimedean factor **equals the inverse of the finite product**:
  `∏ infinite = (∏ finite)⁻¹`. So #2's archimedean contribution is *determined* by (and balances) the
  finite places to make the global product 1. Remove it and the product is the finite product ≠ 1 in
  general. #2 is the required balancer, not an optional node.

**Honest scope (same fence as A1).** The product runs over ALL places of ℚ (the one infinite place +
every prime). The framework lights up #2 (the infinite place) and #3 (the p = 2 finite place) as two of
them; #3 is one factor of the finite product the archimedean place balances. A2 is a Mathlib-anchored
result (the product formula is Mathlib's) with the framework interpretation that #2 occupies the forced
archimedean slot — NOT a from-scratch framework theorem, and NOT an object-level claim about the simplex.
-/

namespace ZeroParadox.ZPH_PlaceForcing

open NumberField

/-- The product formula at K = ℚ (Mathlib's `prod_abs_eq_one`): the archimedean (infinite-place) factor
    times the finite-place product is 1. -/
theorem productFormula_rat (x : ℚ) (hx : x ≠ 0) :
    (∏ w : InfinitePlace ℚ, w x ^ w.mult) * ∏ᶠ w : FinitePlace ℚ, w x = 1 :=
  prod_abs_eq_one hx

/-- ℚ has a UNIQUE archimedean (infinite) place — the slot A1 placed #2 in. -/
theorem archimedean_place_unique_rat : Subsingleton (InfinitePlace ℚ) := inferInstance

/-- **A2 — the balancing role** (Mathlib's product formula, rearranged). The archimedean factor equals
    the inverse of the finite product: it is *determined* by the finite (p-adic, incl. #3) places — the
    factor that balances them to the global 1. Interpretation: #2's archimedean slot is the balancer of
    the finite places, not a free/optional contribution. (Content is `prod_abs_eq_one`; this is the
    `a*b=1 → a=b⁻¹` reading of it, not new derivation.) -/
theorem archimedean_factor_forced (x : ℚ) (hx : x ≠ 0) :
    (∏ w : InfinitePlace ℚ, w x ^ w.mult) = (∏ᶠ w : FinitePlace ℚ, w x)⁻¹ := by
  have h := productFormula_rat x hx
  have hB : (∏ᶠ w : FinitePlace ℚ, w x) ≠ 0 := by
    intro hB0; rw [hB0, mul_zero] at h; exact one_ne_zero h.symm
  field_simp [hB]
  linear_combination h

end ZeroParadox.ZPH_PlaceForcing

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_PlaceForcing

#print axioms productFormula_rat
#print axioms archimedean_place_unique_rat
#print axioms archimedean_factor_forced

end PurityCheck
