-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge T2 — the within-ν edge: Markov attractor ↔ p-adic inverse-limit

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Tests **T2**: are the Markov bottom (#2, an attractor in the probability simplex) and the p-adic
bottom (#3, the floor `{0} = ⋂ q2Ball n ⊆ Q₂`) reconcilable as ν-siblings? **PARTIAL; T2 OPEN.**
-/

namespace ZeroParadox

open ZeroParadox
open scoped Topology

/-- **T2 partial obstruction (coarse).** No homeomorphism between the connected simplex
    `stdSimplex ℝ (Fin 2)` (Markov ν-ambient) and the totally-disconnected `Q₂` (p-adic ν-ambient). -/
theorem padic_simplex_not_homeomorphic :
    IsEmpty (↥(stdSimplex ℝ (Fin 2)) ≃ₜ Q₂) := by
  refine ⟨fun e => ?_⟩
  -- the simplex is convex and nonempty, hence a connected space
  haveI hSconn : ConnectedSpace ↥(stdSimplex ℝ (Fin 2)) :=
    isConnected_iff_connectedSpace.mp
      ⟨⟨_, single_mem_stdSimplex ℝ (0 : Fin 2)⟩,
        (convex_stdSimplex ℝ (Fin 2)).isPreconnected⟩
  -- transport connectedness across the homeomorphism to Q₂
  haveI hQconn : ConnectedSpace Q₂ := e.connectedSpace_iff.mp hSconn
  -- Statement: the obstruction is a CARDINALITY floor, not a topological fact about Q₂. Mathlib's
  -- lemma concludes `Subsingleton` — preconnected AND totally disconnected admits AT MOST ONE point
  -- — and `Nontrivial Q₂` says at least two. Nothing below the two classes is consumed.
  exact not_subsingleton Q₂ subsingleton_of_preconnected_totallyDisconnected

-- Reading: the theorem rules out a GLOBAL homeomorphism of the two AMBIENTS, and nothing more. It
-- does NOT show the two bottoms fail to glue: both are singletons (`{0}` and one stationary
-- distribution), so comparing the bottoms is trivially available, and a LOCAL comparison
-- (neighbourhoods of the bottoms) or any non-homeomorphic reconciliation is untouched here.
-- T2 is therefore OPEN. Unlike T1 — the μ edge, which glues via real functors — ν has only this
-- coarse wall, so the tree's symmetric prediction is neither confirmed nor falsified. An asymmetry
-- is SUGGESTED, not proven; the sharper test is a local-near-⊥ or inverse-limit-vs-attractor
-- comparison, never a global ambient homeomorphism.

-- Reading: #2 and #3 may be ν in DIFFERENT SENSES — #2 a dynamical attractor, #3 a categorical
-- limit — which would explain a genuine ν-asymmetry. Open direction, not a result.

-- Statement: GENERICITY WITNESS for the theorem above. The same argument closes with BOTH ambients
-- universally quantified, so nothing 2-adic and nothing simplicial survives into it: the wall is
-- about the two topological classes, never about these two carriers. Anonymous, so it declares
-- nothing. ⚠ This is NOT the archimedean/non-archimedean distinction — ℚ under the ordinary
-- absolute value is archimedean AND totally disconnected, so the two come apart.
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [TotallyDisconnectedSpace Y] [Nontrivial Y] :
    IsEmpty (X ≃ₜ Y) := by
  refine ⟨fun e => ?_⟩
  haveI : ConnectedSpace Y := e.connectedSpace_iff.mp inferInstance
  exact not_subsingleton Y subsingleton_of_preconnected_totallyDisconnected

-- Statement: `Nontrivial` is load-bearing — dropping it makes the universal above FALSE, not weaker,
-- and `Unit` is the refutation because it is connected AND totally disconnected at once. Stated as a
-- refutation rather than as `Nonempty (Unit ≃ₜ Unit)`, which would witness nothing: `Homeomorph.refl`
-- inhabits `Z ≃ₜ Z` for every `Z` carrying a topology. Instantiating the universal at `Unit` forces
-- the ELABORATOR to synthesize both instances, so those two conjuncts are checked rather than
-- asserted in this comment.
example : ¬ (∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [TotallyDisconnectedSpace Y], IsEmpty (X ≃ₜ Y)) := by
  intro h
  exact (h Unit Unit).false (Homeomorph.refl Unit)

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms padic_simplex_not_homeomorphic

end PurityCheck
