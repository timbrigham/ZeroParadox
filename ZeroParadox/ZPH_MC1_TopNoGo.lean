-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1
import Mathlib.Topology.Category.TopCat.Limits.Basic

set_option maxHeartbeats 400000

/-!
# In TopCat the empty space is not isomorphic to the one-point space

**Proves.** `top_initial_not_iso_terminal`: `TopCat.of PEmpty` (the initial object) is not isomorphic to
`TopCat.of PUnit` (the terminal object) — an iso's inverse would map the point into the empty space.
The content: in `TopCat`, initial ≄ terminal (because ∅ is empty and the point is not).

**Reaching for (intent, NOT proved here).** This was *meant to* be the "Top polarity wall" — the claim
that, because Top's bottom is terminal-flavored while the cluster bottoms are initial, no
initiality-preserving functor can carry a cluster bottom onto the Top floor; with the 0=∞ flip
(`tower_inv_valuation`) as the principled escape.

**Gap (as far as this reaches).** The statement is about `TopCat`'s generic initial/terminal objects, not
about `fB_functor` or the snap floor specifically, and it does not quantify over functors — so "no functor
can carry the bottom across" is an interpretation, not a proved no-go. The escape via the flip is likewise
intent (the ∞-view→cluster functor is not built). Conjecture: the spec note (read its cold-audit correction).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory Limits

/-- Proves: in `TopCat` the initial object (empty space) is not isomorphic to the terminal object
    (one-point space) — an iso's inverse would map the point into the empty space. Intent: the "Top polarity
    wall". NOT proved here: anything about functors — the statement does not quantify over them, so "no
    initiality-preserving functor can carry the bottom across" is interpretation, not a proved no-go. -/
theorem top_initial_not_iso_terminal :
    IsEmpty (TopCat.of PEmpty ≅ TopCat.of PUnit) := by
  constructor
  intro e
  exact (e.inv.hom PUnit.unit).elim

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms top_initial_not_iso_terminal
end PurityCheck
