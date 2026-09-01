import ZeroParadox.Settheory.Wall
import Mathlib.Tactic

/-!
# Curry's paradox — the diagonal family's EXPLOSION face (probe)

## Engineer's Take

Back to basics. We're filling in everything that's left where the relationship between one over
infinity and a bottom element still wasn't fully defined, using the same structure that we have for
everything else in the family.

---

## Formal Overview
A self-referential `p ↔ (p → C)` proves `C` for **any** `C`, using implication alone — so the liar is
Curry at `C = False`, and `curry_paradox` strictly generalizes `negation_no_fixedpoint`. Placement,
relation to the engine and attribution: `ZeroParadox/Settheory/Curry.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ## § I. Curry's paradox -/

/-- **Curry's paradox.** A self-referential proposition `p ↔ (p → C)` proves `C`, for any `C`.
    Proof: `p → C` holds (assume `p`; then `p → C` by `mp`, applied to `p`); feed it back through `mpr`
    to get `p`; then `p → C` at `p` gives `C`. No negation is used — only implication and the
    self-reference `p ↔ (p → C)`. -/
theorem curry_paradox {C : Prop} {p : Prop} (h : p ↔ (p → C)) : C :=
  have hpc : p → C := fun hp => h.mp hp hp
  hpc (h.mpr hpc)

/-! ## § II. The liar is Curry at `C = False` -/

/-- **The liar is Curry at `C = False`.** `Not p` is `p → False`, so a liar `p ↔ ¬p` is a Curry
    proposition `p ↔ (p → False)`, and `curry_paradox` yields `False`. This exhibits
    `negation_no_fixedpoint` (the engine) as the `C = False` instance of the more general Curry —
    Curry is the strictly stronger face. -/
theorem liar_is_curry_at_false (p : Prop) (h : p ↔ ¬ p) : False :=
  curry_paradox (C := False) h

/-! ## § III. Curry from an internal naming -/

/-- **Explosion from internal comprehension.** If a naming `name : A → (A → Prop)` is point-surjective
    (unrestricted internal comprehension — every predicate is named), then *every* `C` is provable:
    the Curry sentence names `fun a => name a a → C`. This is the sharpest inconsistency of unrestricted
    comprehension — not just a contradiction (Cantor/Russell) but total explosion — routed through the
    same Lawvere naming as the rest of the family. -/
theorem curry_from_naming {A : Type*} {C : Prop} (name : A → (A → Prop))
    (hsurj : Function.Surjective name) : C := by
  obtain ⟨q, hq⟩ := hsurj (fun a => name a a → C)
  exact curry_paradox (iff_of_eq (congrFun hq q))

/-! ## § IV. The bottom-element relationship — the wall (μ): a bottom would explode -/

/-- **Curry on the μ/ν fork: no bottom element, and pretending otherwise explodes.** No internal naming
    `name : A → (A → Prop)` is surjective — the wall — because a surjective naming (a bottom for the
    predicate-diagonal) would, by `curry_from_naming` at `C = False`, prove `False` (indeed any `C`). So
    on the one-over-infinity-to-bottom map, the explosion face is the μ/wall side in its most violent
    form: self-reference finds no floor, and assuming it does proves everything. Same family shape as
    Cantor/Russell (`no self-surjection onto predicates`), routed through Curry's explosion. -/
theorem curry_no_bottom {A : Type*} (name : A → (A → Prop)) : ¬ Function.Surjective name :=
  fun h => curry_from_naming (C := False) name h

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms curry_paradox
#print axioms liar_is_curry_at_false
#print axioms curry_from_naming
#print axioms curry_no_bottom
end PurityCheck
