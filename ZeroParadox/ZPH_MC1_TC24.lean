-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_InfoFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.PEmpty
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H TC24: the Kleisli μ-bottom's `IsInitial` is definitionally an empty-colimit witness (a remark)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

**This file is a clarifying REMARK, not a campaign edge, and it closes no pre-registered question.**

The edge was pre-registered as a possible NO-GO: do the μ-bottoms (#4 `Fin 0` in `KleisliCat PMF`,
#5 `StateSpace 0`) carry only a *bare* `IsInitial`, while the ν-floor #3 carries a real universal
cone — leaving the forks asymmetric? **That question is ill-posed in this Mathlib pin.** Here
`IsInitial X` is *definitionally* `IsColimit (asEmptyCocone X)` (an `abbrev`,
`Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean:59`). There is no such thing as an `IsInitial`
that is not already an empty-diagram colimit witness — the two are one object. So the answer is forced
and content-free: the pre-existing `fC_zero_isInitial` from `ZPH_InfoFunctor` already *is* an
empty-colimit cocone. Nothing in this file is a discovery about the snap floor; it is an unfolding of
a Mathlib `abbrev` plus two applications of generic category-theory lemmas (true of *any* initial
object in *any* category), restated with `fC_obj 0` plugged in.

**What is actually here (all of it generic, scoped honestly in the statement names):**

- `fC_zero_isInitial_as_empty_colimit` — `IsColimit (asEmptyCocone (fC_obj 0))`. This is the SAME
  TERM as `fC_zero_isInitial`; it does zero proof work (the types are one `abbrev`).
- `fC_zero_cocone_apex` — the empty cocone's apex is `fC_obj 0`. Proved by `rfl` (definitional).
- `fC_hasInitial` — `HasInitial (KleisliCat PMF)`, the generic `IsInitial.hasInitial` lemma applied.
- `fC_initial_iso_floor` — `(⊥_ (KleisliCat PMF)) ≅ fC_obj 0`. This is the generic uniqueness-up-to-iso
  fact `initialIsoIsInitial` (any abstract initial object is iso to any concrete initial object),
  specialized — NOT a finding specific to the snap floor.

**No comparative claim is made.** The earlier framing asserted "matching categorical strength" against
the ν-floor #3's `IsLimit` cone. No such comparison is formalized: that ν cone (campaign target TH10)
is **unbuilt** — `fB_bottom_is_limit` is only the set equation `⋂ q2Ball n = {0}`, not an `IsLimit`.
Without TH10 there is no second witness to compare against, so any "matching strength" / "stronger
fork" / "closes the μ half" language would be an overclaim and has been removed. To make this edge
load-bearing one must first build TH10; until then this is generic category theory recorded for the
ledger, deliberately demoted from a verdict bundle to a remark.
-/

namespace ZeroParadox.ZPH_MC1_TC24

open CategoryTheory
open ZeroParadox.ZPH_InfoFunctor

/-- `fC_zero_isInitial` restated with its definitional type unfolded: in this Mathlib pin
    `IsInitial X` is the `abbrev` `IsColimit (asEmptyCocone X)`, so this is the *same term* and does
    no proof work. Recorded only to make the empty-colimit reading visible; not a new witness. -/
noncomputable def fC_zero_isInitial_as_empty_colimit :
    Limits.IsColimit (Limits.asEmptyCocone (fC_obj 0)) :=
  fC_zero_isInitial

/-- The apex of the μ-bottom's colimit cocone is exactly the snap floor `Fin 0`. -/
theorem fC_zero_cocone_apex :
    (Limits.asEmptyCocone (fC_obj 0)).pt = fC_obj 0 := rfl

/-- Having an explicit `IsInitial`/empty-colimit witness, `KleisliCat PMF` `HasInitial`.
    (Universes pinned to those of `KleisliCat PMF` so the witness elaborates.) -/
@[reducible] noncomputable def fC_hasInitial : Limits.HasInitial.{0, 1} (KleisliCat PMF) :=
  fC_zero_isInitial.hasInitial

/-- Generic uniqueness-up-to-iso (`initialIsoIsInitial`), specialized: the abstract initial object
    `⊥_ (KleisliCat PMF)` is iso to the concrete initial object `fC_obj 0`. True of any initial
    object in any category with `HasInitial`; this is not a fact specific to the snap floor. -/
noncomputable def fC_initial_iso_floor :
    haveI := fC_hasInitial
    (⊥_ (KleisliCat PMF)) ≅ fC_obj 0 :=
  haveI := fC_hasInitial
  Limits.initialIsoIsInitial fC_zero_isInitial

end ZeroParadox.ZPH_MC1_TC24

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's `PMF` / `KleisliCat` / colimit library,
exactly as in `ZPH_InfoFunctor`. No new commitment is introduced by this file. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC24

#print axioms fC_zero_isInitial_as_empty_colimit
#print axioms fC_zero_cocone_apex
#print axioms fC_hasInitial
#print axioms fC_initial_iso_floor

end PurityCheck
