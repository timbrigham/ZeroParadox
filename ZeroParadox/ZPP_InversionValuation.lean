import Mathlib.NumberTheory.Padics.PadicNumbers

set_option maxHeartbeats 400000

/-!
# An elementary fact: 2-adic inversion reverses the valuation filtration

This is the one original (if elementary) result that survived a cold audit (2026-06-29) of an attempt to
formalize the conjecture "the arithmetic inversion `z ↦ 1/z` IS the categorical passage to `Cᵒᵖ`" (note
`two_as_one_fork_zero_infinity_2026-06-29`). The audit verdict on that attempt was **LARGELY PROSE**: the
keystone identification was never formalized (no category instance, no functor, no natural iso), and the
other "results" there were one-line re-exports of Mathlib (`Padic.valuation_inv`, `inv_zero`,
`IsInitial.op`/`IsTerminal.op`) carrying interpretive docstrings. Those have been removed. What remains is
this single honest lemma.

**Proves** `inversion_reverses_filtration`: inversion carries the valuation `n`-sublevel to the
`(-n)`-superlevel on the nonzero 2-adic points. Built directly on `Padic.valuation_inv`. NOTE: this
`valuation` is ℤ-valued, so `v₂(0) = 0` — there is no `+∞` / `0=∞` content in this statement (that lives in
`addValuation`, not used here).

**Does NOT prove** the keystone "inversion = passing to the opposite category." That remains a conjecture
(see the note); no part of it is formalized.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.InversionValuation

/-- Inversion REVERSES the valuation filtration on the nonzero points: the image under `z ↦ z⁻¹` of the
    `n`-sublevel `{x ≠ 0 | n ≤ v₂(x)}` is exactly the `(-n)`-superlevel `{x ≠ 0 | v₂(x) ≤ -n}`. An elementary
    `Set.ext` over `Padic.valuation_inv`. (ℤ-valued valuation; the floor `0` is excluded from both sides.) -/
theorem inversion_reverses_filtration (n : ℤ) :
    (·⁻¹) '' {x : ℚ_[2] | x ≠ 0 ∧ n ≤ x.valuation} = {x : ℚ_[2] | x ≠ 0 ∧ x.valuation ≤ -n} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨y, ⟨hy, hyn⟩, rfl⟩
    refine ⟨inv_ne_zero hy, ?_⟩
    rw [Padic.valuation_inv]; omega
  · rintro ⟨hx, hxn⟩
    refine ⟨x⁻¹, ⟨inv_ne_zero hx, ?_⟩, inv_inv x⟩
    rw [Padic.valuation_inv]; omega

end ZeroParadox.InversionValuation

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.InversionValuation
#print axioms inversion_reverses_filtration
end PurityCheck
