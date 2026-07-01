-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1

set_option maxHeartbeats 400000

/-!
# The Kleisli snap floor is not isomorphic to any object above it

**Proves.** `mc1_bottom_directed_not_mutual`: in `KleisliCat PMF`, for `n > 0`, `fC_functor.obj 0` is not
isomorphic to `fC_functor.obj n`. One-line consequence of `fC_no_return` (no morphism back into the floor):
an iso would supply one. The content is "no return ⟹ not iso to anything above it", about one domain.

**Reaching for (intent, NOT proved here).** This was *aimed at* the NP-complete reframe — testing whether
the MC-1 bottoms form a *mutual* "degree" (inter-reducible, the most identity can be earned) or a
*directed* one (stratified, identity softer) — and reading the no-iso fact as: the relation is directed,
not mutual, the snap's irreversibility being the non-mutuality.

**Gap (as far as this reaches).** The "degree / mutual-vs-directed / NP-style" framing is interpretation
on top of a single-category no-iso fact. The cross-category mutuality question has no Lean object at all
(those transfers were never built). So this neither establishes nor refutes a cross-framework "degree";
the MC-1 identity status is unchanged by it. Conjecture: `np_complete_transfer_degree_2026-06-28.md`.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory ZeroParadox.ZPH_InfoFunctor

/-- **The MC-1 bottom is directed, not mutual (B7).** In `KleisliCat PMF` the snap floor admits no
    return morphism from any nonempty object (`fC_no_return`), so it is not isomorphic to any such
    object: there is no mutual/equivalence pairing with anything above it. The bottom sits strictly at
    the source of a directed structure — the snap's irreversibility *is* the failure of mutuality, so
    MC-1's bottoms do not form a single mutual (NP-style) degree. -/
theorem mc1_bottom_directed_not_mutual {n : ℕ} (hn : 0 < n) :
    IsEmpty (fC_functor.obj n ≅ fC_functor.obj 0) := by
  constructor
  intro e
  exact (fC_no_return hn).false e.hom

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms mc1_bottom_directed_not_mutual
end PurityCheck
