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

This file tests **T2**, the within-ν internal edge of the bottom-diagram tree
(`thread_obstruction_table_2026-06-29.md` §7): are the Markov-dynamical bottom (#2, a stationary
attractor in the compact probability simplex) and the p-adic bottom (#3, the inverse-limit floor
`{0} = ⋂ q2Ball n ⊆ Q₂`) **reconcilable**, as the tree predicts for siblings under the ν root?

**Pre-registered no-go (named before building):** #2's ambient is the simplex over ℝ (archimedean,
*connected*); #3's ambient is `Q₂ = ℚ_[2]` (non-archimedean, *totally disconnected*). This is the
ℝ-vs-ℚ₂ wall — the topological cousin of E4.

**Race outcome: PARTIAL — a coarse obstruction proven, but the ν-edge is OPEN, NOT settled.**
(Cold audit corrected an earlier "NO-GO / tree FALSIFIED" overclaim — see the scope fence below.)

- `padic_simplex_not_homeomorphic` — there is **no homeomorphism** between the connected simplex
  `stdSimplex ℝ (Fin 2)` (the Markov ν-system's ambient) and the totally-disconnected `Q₂` (the
  p-adic ν-system's ambient). Proof: the simplex is convex hence connected; a homeomorphism would make
  `Q₂` connected; but `Q₂` is totally disconnected and nontrivial (`0 ≠ 1`) — contradiction.

**SCOPE FENCE (what this does and does NOT establish).** This theorem rules out *only* a **global
homeomorphism of the two ambient spaces**. It is, honestly, the **generic** connected-vs-
totally-disconnected wall (any connected nontrivial space fails to be homeomorphic to any totally-
disconnected nontrivial one) — i.e. the archimedean/non-archimedean distinction, instantiated; it is
not a statement about *attractors vs inverse limits* specifically. Crucially it does **NOT** prove
"the ν-bottoms don't glue": both bottoms are *singletons* (`{0}` and a single stationary
distribution), so a comparison of the *bottoms* is trivially available, and a **local** comparison
(neighborhoods of the bottoms) or any **non-homeomorphic** reconciliation is not ruled out here.

**Honest verdict: T2 is OPEN.** Unlike T1 (the μ edge, genuinely GO — siblings glue via real
functors), the ν edge has only this coarse global-ambient wall. The tree's symmetric prediction is
therefore **neither confirmed nor falsified** at ν: a real obstruction exists at the global-topology
level, but the load-bearing glue question (a local / structure-preserving reconciliation of the two
ν-systems) is unresolved. An **asymmetry is SUGGESTED** (μ glues; ν has a wall) but not proven — flag
for human review and a future sharper test (the genuine ν-edge needs a local-near-⊥ or
inverse-limit-vs-attractor comparison, not a global ambient homeomorphism).

**Conjectural diagnosis (interpretation, not a Lean claim).** #2 and #3 may be "ν" in *different
senses* — #2 a *dynamical* attractor, #3 a *categorical* limit — which would explain a genuine
ν-asymmetry; but this is unproven and is the open direction, not a result.
-/

namespace ZeroParadox

open ZeroParadox
open scoped Topology

/-- **T2 partial obstruction (coarse).** No homeomorphism between the connected simplex
    `stdSimplex ℝ (Fin 2)` (Markov ν-ambient) and the totally-disconnected `Q₂` (p-adic ν-ambient).
    This is the generic connected-vs-totally-disconnected (archimedean/non-archimedean) wall; it rules
    out a global ambient homeomorphism only, NOT a local or non-homeomorphic gluing of the bottoms
    (which are singletons). The ν-edge stays OPEN — see the scope fence in the file header. -/
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
  -- connected AND totally disconnected forces AT MOST ONE point; Q₂ has at least two
  exact not_subsingleton Q₂ subsingleton_of_preconnected_totallyDisconnected

-- Statement: GENERICITY WITNESS for the theorem above, whose docstring calls it "the generic
-- connected-vs-totally-disconnected wall". The same argument closes with BOTH ambients universally
-- quantified, so nothing 2-adic and nothing simplicial survives into it: the wall is about the two
-- topological classes, never about these two carriers. The obstruction is a CARDINALITY floor, which
-- is why Mathlib states it as `Subsingleton` — connected-and-totally-disconnected forces AT MOST ONE
-- point, and `Nontrivial` forbids that. Anonymous, so it declares nothing.
example (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [ConnectedSpace X] [TotallyDisconnectedSpace Y] [Nontrivial Y] :
    IsEmpty (X ≃ₜ Y) := by
  refine ⟨fun e => ?_⟩
  haveI : ConnectedSpace Y := e.connectedSpace_iff.mp inferInstance
  exact not_subsingleton Y subsingleton_of_preconnected_totallyDisconnected

-- Statement: `Nontrivial` is load-bearing — dropping it makes the universal above FALSE, not weaker,
-- and `Unit` is the refutation because it is connected AND totally disconnected at once. Stated as a
-- refutation rather than as `Nonempty (Unit ≃ₜ Unit)`, which would witness nothing: `Homeomorph.refl`
-- inhabits `Z ≃ₜ Z` for EVERY `Z`. Instantiating the universal at `Unit` forces both instances to be
-- synthesized, so the kernel checks those two conjuncts instead of leaving them as prose.
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
