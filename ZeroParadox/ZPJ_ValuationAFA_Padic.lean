import ZeroParadox.ZPJ_ValuationAFA
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# P10 concrete: the bottom-valuation axioms are THEOREMS for the 2-adic numbers

P10 (`ZPJ_ValuationAFA`) derives AFA self-containment from a `BottomValuation` — abstractly a reduction
(AFA posit ⟸ valuation posit), with one residual posit `v_top_unique`. This file discharges that posit
on the genuine 2-adic valuation: both `BottomValuation` axioms, instantiated to
`Padic.addValuation : AddValuation ℚ_[2] (WithTop ℤ)`, are THEOREMS of 2-adic analysis, not posits:

* `v_bot`        ↦ `padic_addVal_bot`        — `addValuation 0 = ⊤` (free; also P7's `addVal_bot`);
* `v_top_unique` ↦ `padic_addVal_top_unique` — `addValuation x = ⊤ → x = 0`: the only 2-adic number of
  infinite valuation is 0.

So on ℚ₂ the bottom-valuation structure is realized with **no posit left over** — P10's only real
axiom becomes a proven theorem (`padic_addVal_eq_top_iff`).

**Honest scope (the recurring MC-1 boundary).** This discharges the *valuation* half. The AFA
self-containment conclusion (`BottomValuation.toAFA`, ⊥={⊥}) needs the carrier to be a `ZPSemilattice`,
and ℚ₂ has no natural such structure — it is the framework's *topological* realization of the bottom
(F_B / TopCat), not a lattice. So the AFA conclusion stays on the lattice side, joined to ℚ₂ by the
MC-1 commitment, exactly as the type boundary predicts. What is genuinely upgraded: P10's residual posit
is now a 2-adic theorem.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPJ

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

open Padic

/-- **v_bot for ℚ₂.** The additive 2-adic valuation of 0 is ⊤. (Mathlib; also an instance of P7's
    `addVal_bot`, every additive valuation sends 0 to ⊤.) -/
theorem padic_addVal_bot : Padic.addValuation (0 : ℚ_[2]) = ⊤ :=
  Padic.addValuation.map_zero

/-- **v_top_unique for ℚ₂ (P10's residual posit, now a THEOREM).** The only 2-adic number with infinite
    additive valuation is 0: for `x ≠ 0`, `addValuation x = ↑(x.valuation)`, a finite value `≠ ⊤`. -/
theorem padic_addVal_top_unique (x : ℚ_[2]) (hx : Padic.addValuation x = ⊤) : x = 0 := by
  by_contra h
  rw [Padic.addValuation.apply h] at hx
  exact WithTop.coe_ne_top hx

/-- **The 2-adic bottom-valuation characterization.** `addValuation x = ⊤ ↔ x = 0`: the ⊤ valuation
    pins out 0 uniquely. P10's `BottomValuation` characterization, fully theorem-grade on ℚ₂. -/
theorem padic_addVal_eq_top_iff (x : ℚ_[2]) : Padic.addValuation x = ⊤ ↔ x = 0 :=
  ⟨padic_addVal_top_unique x, fun h => h ▸ padic_addVal_bot⟩

end ZeroParadox.ZPJ

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPJ
#print axioms padic_addVal_bot
#print axioms padic_addVal_top_unique
#print axioms padic_addVal_eq_top_iff
end PurityCheck
