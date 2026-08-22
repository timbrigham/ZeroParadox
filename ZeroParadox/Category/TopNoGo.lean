-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.MC1Bridge
import Mathlib.Topology.Category.TopCat.Limits.Basic

set_option maxHeartbeats 400000

/-!
# In TopCat the empty space is not isomorphic to the one-point space

**Proves.** `top_initial_not_iso_terminal`: in `TopCat` initial ≄ terminal. **Gap:** a statement about
generic objects, not quantified over functors — that fence is canonical on the theorem's docstring.
**Reaching for (intent, NOT proved here).** The "Top polarity wall" — no initiality-preserving functor
carrying a cluster bottom onto the Top floor, escaping via 0=∞ (`tower_inv_valuation`); not built.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
---
-/

namespace ZeroParadox

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

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms top_initial_not_iso_terminal
end PurityCheck
