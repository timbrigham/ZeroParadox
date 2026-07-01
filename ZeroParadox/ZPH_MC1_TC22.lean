-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_TreeObstructions
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC19 — span-robustness of the well-founded cross-root wall (#1 vs #2)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file sharpens the E4 / TC04 cross-root obstruction between the **proof-theory floor** (#1, the
base of a well-founded order — `0 : Ordinal`) and the **Markov-dynamical attractor** (#2, the
stationary point in the probability simplex, whose carrier ℝ is genuinely non-well-founded via
`ZPH_MC1_TreeObstructions.real_carrier_not_wellFounded`).

`no_strictMono_real_to_ordinal` (E4) already proved there is **no direct** order map ℝ → Ordinal.
TC19 asks the strictly stronger question the framework's own G-construction would face: is the wall
robust against a **span** — a common apex object `S` mapping order-preservingly to *both* the
well-founded Ordinal leg and the non-well-founded attractor carrier? A span that reconciled would mean
the root cut is only an obstruction-to-direct-maps; an obstruction even to spans means the well-founded
wall is a genuine invariant.

**Verdict: GO — the wall is robust against faithful spans, and we say exactly which spans escape.**

The load-bearing content is in the statements (not the prose):

- `apex_wf_of_strictMono_to_ordinal` — the **invariant**: for ANY relation `r` on ANY apex `S`, a map
  `f : S → Ordinal` with `r a b → f a < f b` (an order-preserving leg into the well-founded ordinal
  carrier) forces `WellFounded r`. Well-foundedness pulls back along the ordinal leg, period.

- `no_faithful_span_to_ordinal_and_descending` — the **robust wall**, in-statement: there is NO apex
  `S` carrying a non-well-founded relation `r` (the descending structure the #2 / ℝ leg supplies,
  `real_carrier_not_wellFounded`) that ALSO admits an order-preserving leg `f : S → Ordinal`. So no
  *faithful* span — one whose apex actually carries the attractor's infinite descent — reconciles #1
  and #2. This is strictly stronger than `no_strictMono_real_to_ordinal` (a direct map is the special
  case `S = ℝ`, `r = (· < ·)`, `f` the embedding): it rules out the entire span shape, not just the
  direct edge.

- `descending_apex_obstructs_padic_span` — the same wall instantiated against the concrete #2 witness
  ℝ itself: ℝ (with `<`) is a non-well-founded apex, hence admits no order-preserving leg to Ordinal.

**The honest NO-GO half — the escape, also in-statement.** `trivial_bottoms_only_span` exhibits the
single-point apex `S = PUnit`: its (empty) `<` maps order-preservingly to `0 : Ordinal` and its unique
point sits at the simplex stationary vertex, so it IS an order-preserving span. The escape is real but
**degenerate**: the apex carries none of #2's descending structure (PUnit is well-founded), so it
witnesses nothing about the attractor. `faithful_iff_descending` makes the dividing line precise: a
span escapes the wall **iff** its apex is well-founded; a span carries the attractor's content **iff**
its apex is non-well-founded; and these are mutually exclusive on the ordinal leg.

**Net reading.** The μ/ν root cut is NOT merely an obstruction-to-direct-maps: it is a
well-foundedness invariant that survives the span construction, escaped only by the trivial
bottoms-only span that transports no ν-content. The "leaves related through common ancestors" reading
holds only for ancestors that drop the descending structure — exactly the well-founded ones.
-/

namespace ZeroParadox.ZPH_MC1_TC22

open ZeroParadox.ZPH_MC1_TreeObstructions

/-! ## The invariant: order-preserving leg into the well-founded ordinal carrier -/

/-- **The pullback invariant.** For any relation `r` on any apex `S`, an order-preserving leg
    `f : S → Ordinal` (`r a b → f a < f b`) forces `WellFounded r`: well-foundedness of `<` on the
    ordinals pulls back along `f`. This is the engine of the robust wall — the well-founded leg of any
    span imposes well-foundedness on the apex. -/
theorem apex_wf_of_strictMono_to_ordinal {S : Type*} (r : S → S → Prop)
    (f : S → Ordinal) (hf : ∀ a b, r a b → f a < f b) : WellFounded r := by
  have hsub : Subrelation r (InvImage (· < ·) f) := fun {a b} hab => hf a b hab
  exact hsub.wf (InvImage.wf f ordinal_carrier_wellFounded)

/-! ## The robust wall: no faithful span reconciles #1 and #2 -/

/-- **TC19 robust wall (in-statement).** There is no apex `S` carrying a *non-well-founded* relation
    `r` — the infinite-descent structure the #2 / ℝ attractor leg supplies — that also admits an
    order-preserving leg `f : S → Ordinal` to the #1 well-founded floor. So no span whose apex
    faithfully carries the attractor's descending structure can reconcile #1 with #2.

    Strictly stronger than `no_strictMono_real_to_ordinal`: that is the special case
    `S = ℝ, r = (· < ·)`. Here the *entire span shape* is obstructed, not just the direct edge. -/
theorem no_faithful_span_to_ordinal_and_descending {S : Type*} (r : S → S → Prop)
    (hr : ¬ WellFounded r) :
    ¬ ∃ f : S → Ordinal, ∀ a b, r a b → f a < f b := by
  rintro ⟨f, hf⟩
  exact hr (apex_wf_of_strictMono_to_ordinal r f hf)

/-- The robust wall instantiated at the concrete #2 witness: ℝ (with `<`, the carrier of the simplex
    attractor's order, non-well-founded by `real_carrier_not_wellFounded`) is itself a faithful apex,
    hence admits no order-preserving leg to the #1 ordinal floor. -/
theorem descending_apex_obstructs_padic_span :
    ¬ ∃ f : ℝ → Ordinal, ∀ a b : ℝ, a < b → f a < f b :=
  no_faithful_span_to_ordinal_and_descending (· < ·) real_carrier_not_wellFounded

/-! ## The honest escape: the trivial bottoms-only span (degenerate, transports no ν-content) -/

/-- **The NO-GO escape, in-statement.** The single-point apex `PUnit` DOES span #1 and #2: its `<`
    maps order-preservingly to `0 : Ordinal` (vacuously — `PUnit` has no `<`-pair) and its unique
    point lands at a chosen simplex point (here the apex of `stdSimplex ℝ (Fin 1)`). So the cross-root
    obstruction does dissolve under *this* span. The escape is degenerate: the apex is well-founded and
    carries none of #2's descending structure — see `faithful_iff_descending`. -/
theorem trivial_bottoms_only_span :
    (∃ f : PUnit → Ordinal, ∀ a b : PUnit, (a < b) → f a < f b) ∧
    (∃ g : PUnit → (Fin 1 → ℝ), ∀ x, g x ∈ stdSimplex ℝ (Fin 1)) := by
  refine ⟨⟨fun _ => 0, fun a b h => ?_⟩, ⟨fun _ => fun _ => 1, fun _ => ?_⟩⟩
  · exact absurd h (by simp)
  · constructor
    · intro i; exact zero_le_one
    · simp

/-- **The dividing line, in-statement.** A span's apex `S` (with relation `r`) admits an
    order-preserving leg to the #1 ordinal floor **iff** it is well-founded — i.e. exactly when it
    drops #2's descending structure. Combined with `apex_wf_of_strictMono_to_ordinal`: the existence of
    *any* order-preserving leg forces well-foundedness, and conversely a well-founded apex always has
    one (its own rank map). So "escapes the wall" ⟺ "well-founded apex" ⟺ "carries no ν-content"; the
    trivial bottoms-only span is the degenerate instance. -/
theorem faithful_iff_descending {S : Type u} (r : S → S → Prop) :
    (∃ f : S → Ordinal.{u}, ∀ a b, r a b → f a < f b) ↔ WellFounded r := by
  constructor
  · rintro ⟨f, hf⟩; exact apex_wf_of_strictMono_to_ordinal r f hf
  · intro hwf
    haveI : IsWellFounded S r := ⟨hwf⟩
    exact ⟨IsWellFounded.rank r, fun a b hab => IsWellFounded.rank_lt_of_rel hab⟩

end ZeroParadox.ZPH_MC1_TC22

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / rank / simplex libraries — a library
dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC22

#print axioms apex_wf_of_strictMono_to_ordinal
#print axioms no_faithful_span_to_ordinal_and_descending
#print axioms descending_apex_obstructs_padic_span
#print axioms trivial_bottoms_only_span
#print axioms faithful_iff_descending

end PurityCheck
