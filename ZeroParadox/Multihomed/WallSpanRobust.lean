-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.TreeObstructions
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Spans into the ordinals: the wall bites on non-well-founded apexes (#1 vs #2, #2 taken as ℝ)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file sharpens the E4 / `ZeroParadox/Multihomed/CrossRootCompleteness.lean` cross-root obstruction between the **proof-theory floor** (#1, the
base of a well-founded order — `0 : Ordinal`) and the **Markov-dynamical attractor** (#2, the
stationary point in the probability simplex). This file takes #2's carrier to be ℝ, non-well-founded
by `real_carrier_not_wellFounded`, as a modelling choice: under the coordinate order the simplex
itself is an antichain (`simplex_antichain`), hence well-founded.

`no_strictMono_real_to_ordinal` (E4) already proved there is **no direct** order map ℝ → Ordinal.
This file asks the strictly stronger question the framework's own G-construction would face: is the wall
robust against a **span** — a common apex object `S` mapping order-preservingly to *both* the
well-founded Ordinal leg and the non-well-founded carrier taken for the attractor (ℝ)? A span that reconciled would mean
the root cut is only an obstruction-to-direct-maps; an obstruction even to spans means the well-founded
wall is a genuine invariant.

**Verdict: the wall bites on every apex whose relation is not well-founded, such as ℝ under `<`, and
every well-founded apex in the same universe as the ordinals escapes it (`faithful_iff_descending`).**

The load-bearing content is in the statements (not the prose):

- `apex_wf_of_strictMono_to_ordinal` — the **invariant**: for ANY relation `r` on ANY apex `S`, a map
  `f : S → Ordinal` with `r a b → f a < f b` (an order-preserving leg into the well-founded ordinal
  carrier) forces `WellFounded r`. Well-foundedness pulls back along the ordinal leg, period.

- `no_faithful_span_to_ordinal_and_descending` — the **robust wall**, in-statement: there is NO apex
  `S` carrying a non-well-founded relation `r` (such as `<` on ℝ, `real_carrier_not_wellFounded`)
  that ALSO admits a strictly order-preserving leg `f : S → Ordinal`. So, with #2's carrier taken to be ℝ,
  no span whose apex carries that infinite descent reconciles #1 and #2. This is strictly stronger than `no_strictMono_real_to_ordinal` (a direct map is the special
  case `S = ℝ`, `r = (· < ·)`, `f` the embedding): it rules out the entire span shape, not just the
  direct edge.

- `descending_apex_obstructs_padic_span` — the same wall at ℝ (with `<`) itself; despite the
  identifier, it concerns ℝ, not the p-adics.

**The escapes, also in-statement.** `trivial_bottoms_only_span` exhibits the single-point apex
`S = PUnit` over the one-point simplex `stdSimplex ℝ (Fin 1)`: a **degenerate** escape.
`faithful_iff_descending` makes the dividing line precise: with the apex and the ordinals in the same
universe, a span escapes the wall **iff** its apex is well-founded. The Markov simplex `stdSimplex ℝ (Fin 2)` under the coordinate order is such an apex
(the `example` after `faithful_iff_descending`): the attractor's own ambient escapes.

**Net reading.** For apexes whose relation is not well-founded, such as ℝ under `<`, the
well-foundedness invariant survives the span construction, not only direct maps. Every well-founded
apex in the same universe as the ordinals escapes it, the simplex the attractor lives in included. So the wall separates #1 from #2 only
under the modelling choice that #2's descent is ℝ-valued.
-/

namespace ZeroParadox

open ZeroParadox

/-! ## The invariant: order-preserving leg into the well-founded ordinal carrier -/

/-- **The pullback invariant.** For any relation `r` on any apex `S`, an order-preserving leg
    `f : S → Ordinal` (`r a b → f a < f b`) forces `WellFounded r`: well-foundedness of `<` on the
    ordinals pulls back along `f`. This is the engine of the robust wall — the well-founded leg of any
    span imposes well-foundedness on the apex. -/
theorem apex_wf_of_strictMono_to_ordinal {S : Type*} (r : S → S → Prop)
    (f : S → Ordinal) (hf : ∀ a b, r a b → f a < f b) : WellFounded r := by
  have hsub : Subrelation r (InvImage (· < ·) f) := fun {a b} hab => hf a b hab
  exact hsub.wf (InvImage.wf f ordinal_carrier_wellFounded)

/-! ## The robust wall: no span with a non-well-founded apex reconciles #1 and #2 -/

/-- **robust wall (in-statement).** There is no apex `S` carrying a *non-well-founded* relation
    `r` (such as `<` on ℝ, the carrier this file takes for #2) that also admits a strictly
    order-preserving leg `f : S → Ordinal` to the #1 well-founded floor. So, with #2's carrier taken to be ℝ, no span
    whose apex carries that descent can reconcile #1 with #2.

    Strictly stronger than `no_strictMono_real_to_ordinal`: that is the special case
    `S = ℝ, r = (· < ·)`. Here the *entire span shape* is obstructed, not just the direct edge. -/
theorem no_faithful_span_to_ordinal_and_descending {S : Type*} (r : S → S → Prop)
    (hr : ¬ WellFounded r) :
    ¬ ∃ f : S → Ordinal, ∀ a b, r a b → f a < f b := by
  rintro ⟨f, hf⟩
  exact hr (apex_wf_of_strictMono_to_ordinal r f hf)

/-- The robust wall at ℝ with `<` (this file's carrier for #2): no strictly order-preserving leg to the #1
    ordinal floor. Despite the identifier, the statement concerns ℝ, not the p-adics; it is
    `no_strictMono_real_to_ordinal` in span form. -/
theorem descending_apex_obstructs_padic_span :
    ¬ ∃ f : ℝ → Ordinal, ∀ a b : ℝ, a < b → f a < f b :=
  no_faithful_span_to_ordinal_and_descending (· < ·) real_carrier_not_wellFounded

/-! ## One escape: the trivial bottoms-only span (degenerate; every well-founded apex in the same universe as the ordinals also escapes) -/

/-- **The NO-GO escape, in-statement.** The single-point apex `PUnit` DOES span #1 and #2: its `<`
    maps order-preservingly to `0 : Ordinal` (vacuously — `PUnit` has no `<`-pair) and its unique
    point lands at a chosen simplex point (here the one point of `stdSimplex ℝ (Fin 1)`, not the
    Markov node's simplex). So the cross-root obstruction does dissolve under *this* span. The escape
    is degenerate, and it is not the only one: every well-founded apex in the same universe as the
    ordinals escapes — see `faithful_iff_descending`. -/
theorem trivial_bottoms_only_span :
    (∃ f : PUnit → Ordinal, ∀ a b : PUnit, (a < b) → f a < f b) ∧
    (∃ g : PUnit → (Fin 1 → ℝ), ∀ x, g x ∈ stdSimplex ℝ (Fin 1)) := by
  refine ⟨⟨fun _ => 0, fun a b h => ?_⟩, ⟨fun _ => fun _ => 1, fun _ => ?_⟩⟩
  · exact absurd h (by simp)
  · constructor
    · intro i; exact zero_le_one
    · simp

/-- **The dividing line, in-statement.** A span's apex `S : Type u` (with relation `r`) admits a
    strictly order-preserving leg to the #1 ordinal floor `Ordinal.{u}`, in the apex's own universe,
    **iff** it is well-founded (despite the identifier, the right-hand side is well-foundedness, not
    descent). Combined with `apex_wf_of_strictMono_to_ordinal`: the existence of *any* strictly
    order-preserving leg into `Ordinal` forces well-foundedness, and conversely a well-founded apex
    always has one into the ordinals of its own universe (its own rank map). So, with the apex and the
    ordinals in the same universe, "escapes the wall" ⟺ "well-founded apex". The trivial bottoms-only span is one instance; the
    Markov simplex under the coordinate order is another (the `example` below). -/
theorem faithful_iff_descending {S : Type u} (r : S → S → Prop) :
    (∃ f : S → Ordinal.{u}, ∀ a b, r a b → f a < f b) ↔ WellFounded r := by
  constructor
  · rintro ⟨f, hf⟩; exact apex_wf_of_strictMono_to_ordinal r f hf
  · intro hwf
    exact ⟨WellFounded.rank r, fun a b hab => WellFounded.rank_lt_of_rel hab⟩

-- Statement: the Markov simplex `stdSimplex ℝ (Fin 2)` under the coordinate order is well-founded
-- (it is an antichain, `simplex_antichain`), so it escapes the wall although it is not `PUnit`.
set_option linter.deprecated false in
example : WellFounded ((· < ·) : ↥(stdSimplex ℝ (Fin 2)) → ↥(stdSimplex ℝ (Fin 2)) → Prop) :=
  (faithful_iff_descending (S := ↥(stdSimplex ℝ (Fin 2))) (· < ·)).mp
    ⟨fun _ => 0, fun p q hpq => absurd (Subtype.ext (simplex_antichain p.1 q.1 p.2 q.2 (le_of_lt hpq)))
      (ne_of_lt hpq)⟩

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / rank / simplex libraries — a library
dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox

#print axioms apex_wf_of_strictMono_to_ordinal
#print axioms no_faithful_span_to_ordinal_and_descending
#print axioms descending_apex_obstructs_padic_span
#print axioms trivial_bottoms_only_span
#print axioms faithful_iff_descending

end PurityCheck
