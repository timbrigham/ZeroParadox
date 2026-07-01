import ZeroParadox.ZPP_Wall

/-!
# Two small facts: self-loops exist without well-foundedness; the Lawvere lemma needs no order

**Proves.** `selfloop_permitted`: there is a relation with `r x x` (witness: `Unit`, `True`) — so
`wf_no_selfloop` genuinely needs its `WellFounded` hypothesis. `engine_is_wf_free`: `lawvere_fixedpoint`
holds for any point-surjection with no well-foundedness assumption (a restatement). The content: the
well-founded face's hypothesis (well-foundedness) is one the negation engine's theorems do not carry.

**Reaching for (intent, NOT proved here).** This was *aimed at* the wall's open question — whether the
well-founded face (`wf_no_selfloop`, by accessibility) *reduces* to the negation engine (one root) or is a
genuinely distinct mechanism (two roots) — arguing for two, narrowing the "all wall faces are one
phenomenon" keystone claim to "the diagonal family is one phenomenon."

**Gap (as far as this reaches).** "TWO ROOTS / keystone falsified" is a STRUCTURAL ARGUMENT from the two
facts above (disjoint hypotheses ⇒ no available reduction), NOT a formal meta-theorem of irreducibility —
there is no Lean proof that no reduction exists. So the conclusion is reasoned conjecture, not a proved
result; treat the headline as the argument it is.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPPWall

/-- **The load-bearing hypothesis is well-foundedness, not the engine.** Absent `WellFounded`, self-loops
    are PERMITTED — the negation engine alone does not forbid `r x x`. Since the engine theorems carry no
    well-foundedness, they cannot supply what `wf_no_selfloop` requires: the two roots are distinct. -/
theorem selfloop_permitted : ∃ (A : Type) (r : A → A → Prop) (x : A), r x x :=
  ⟨Unit, fun _ _ => True, (), trivial⟩

/-- **The engine is well-foundedness-blind.** `lawvere_fixedpoint` holds for ANY point-surjective
    `e : A → (A → B)` with no order/well-foundedness assumption whatsoever — restated here to make explicit
    that the diagonal root never references the structure the well-founded root depends on. -/
theorem engine_is_wf_free {A B : Type*} (e : A → (A → B)) (he : Function.Surjective e) (f : B → B) :
    ∃ b, f b = b :=
  lawvere_fixedpoint e he f

end ZeroParadox.ZPPWall

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPPWall
#print axioms selfloop_permitted
#print axioms engine_is_wf_free
end PurityCheck
