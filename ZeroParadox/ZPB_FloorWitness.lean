import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Valuation.Basic

/-!
# Floor-class witnesses: valuation = ⊤ at the bottom (P7)

ZP-B realizes ⊥ as the 2-adic 0 with diverging valuation (v₂(0) = ∞). This file records that the
"floor carries +∞ measure" pattern is GENERIC — the bottom `0` of a valued / discrete-valuation-like
structure has valuation `⊤` — by exhibiting witnesses beyond ℚ₂, so the v₂(0)=∞ datum is an instance
of a structural fact rather than a quirk of ℚ₂:

* `addVal_bot` — ABSTRACT: in ANY additive valuation, `v 0 = ⊤` (the bottom maps to +∞). This is the
  general reason behind ZP-B's `v₂(0) = ∞`, and it covers every p-adic field (the p-adic additive
  valuation is an `AddValuation`), not just p = 2.
* `powerSeries_order_bot` — CONCRETE (a DVR): the order valuation of the zero power series is `⊤`.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.FloorWitness

/-- **Abstract floor witness.** Any additive valuation sends the bottom `0` to `⊤` (+∞): the floor of
    a valued structure always carries the maximal/infinite valuation. This is the general fact behind
    ZP-B's `v₂(0) = ∞` — it is not special to ℚ₂, and applies to every p-adic field. -/
theorem addVal_bot {R Γ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation R Γ) : v 0 = ⊤ :=
  v.map_zero

/-- **Concrete floor witness (a discrete valuation ring).** The order valuation of the zero power
    series is `⊤`: the bottom of `R⟦X⟧` carries infinite order. -/
theorem powerSeries_order_bot {R : Type*} [Semiring R] :
    (0 : PowerSeries R).order = ⊤ :=
  PowerSeries.order_zero

end ZeroParadox.FloorWitness

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.FloorWitness
#print axioms addVal_bot
#print axioms powerSeries_order_bot
end PurityCheck
