-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import ZeroParadox.ZPH_TopFunctor
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC16 — the within-ν edge reconciles at the LEAF, not the ambient

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file runs the **sharper, pre-registered** test that the T2 cold audit explicitly demanded
(`ZPH_MC1_TreeT2.lean` scope fence; `thread_obstruction_table_2026-06-29.md`). T2 only refuted a
**global ambient homeomorphism** between the Markov ν-system's ambient (`stdSimplex ℝ (Fin 2)`,
connected) and the p-adic ν-system's ambient (`Q₂`, totally disconnected) — and the audit corrected
that to OPEN because it is the *generic* connected-vs-totally-disconnected wall, not a statement about
the bottoms themselves. The audit named the missing test: both ν-bottoms are **singletons** (the
p-adic floor `{0} = ⋂ q2Ball n`, and a one-state Markov chain's stationary distribution, the unique
point of `stdSimplex ℝ (Fin 1)`), so there should be a canonical **leaf-level** reconciliation map
even though no global homeomorphism exists.

**Race outcome: GO at the leaf — but it is the GENERIC subsingleton reconciliation (the honest, deflated
verdict). The asymmetry the T2 audit flagged is CONFIRMED by the same Lean content.**

- `padic_floor_unique` / `simplex_point_unique` — both ν-bottom carriers are `Unique` (one-element):
  the p-adic floor `↥({0} : Set Q₂)` via `Set.uniqueSingleton`, the one-state stationary point
  `↥(stdSimplex ℝ (Fin 1))` via `stdSimplex_unique` (`= {fun _ ↦ 1}`).
- `nu_leaf_reconcile` (GO, IN-statement) — a genuine **homeomorphism**
  `↥({0} : Set Q₂) ≃ₜ ↥(stdSimplex ℝ (Fin 1))` between the two ν-bottom carriers. So the ν-branch
  *does* glue at the leaf, exactly as the tree's sibling-reconciliation prediction requires — matching
  the μ-branch (T1 GO) at the level of "the bottoms connect".

**The honest fence — this is where the deflation bites (the NO-GO half, made precise).** The map
`nu_leaf_reconcile` is `Homeomorph.homeomorphOfUnique`: it exists for **any** two one-element spaces.
It therefore distinguishes these two ν-bottoms from *nothing* — it carries no valuation, no convex/order,
no inverse-limit structure across the seam. This is witnessed IN-statement by `nu_leaf_reconcile_generic`:
the *same* construction produces a homeomorphism `↥({0} : Set Q₂) ≃ₜ PUnit`, i.e. the p-adic floor is
reconciled with the trivial one-point space by the identical mechanism. So the leaf reconciliation is
**vacuous as a distinguishing invariant**.

**Net verdict (asymmetry CONFIRMED, not refuted).** Contrast with the μ-branch (T1): there the siblings
glue via *real functors carrying universal (initiality) morphisms* — a structure-preserving span
`#4 ⟵ #1 ⟶ #5` that is NOT available between arbitrary objects. The ν-branch glues only by the generic
subsingleton homeomorphism. Hence the μ/ν tree's two branches are **structurally asymmetric**: μ glues
structurally; ν glues only set-theoretically / topologically at the point. That is precisely the
"SUGGESTED-not-proven asymmetry" the T2 audit flagged, now machine-witnessed.

**What is Lean vs interpretation.** Lean proves: the two ν-bottom carriers are each `Unique`; a
homeomorphism between them exists; the *same* construction homeomorphs the p-adic floor with `PUnit`
(genericity witness). The reading that this genericity = "ν glues only vacuously while μ glues
structurally, so the tree's branches are asymmetric" is the framework's interpretation of that Lean
content (the structural μ-glue lives in `ZPH_MC1_TreeT1`, not re-proved here).
-/

namespace ZeroParadox.ZPH_MC1_TC19

open ZeroParadox.ZPB ZeroParadox.ZPH_TopFunctor
open scoped Topology

/-- The p-adic ν-bottom as a topological subspace: the floor `{0} ⊆ Q₂`
    (`fB_bottom_is_limit : ⋂ n, q2Ball n = {0}`). -/
abbrev padicFloor : Type := ↥({(0 : Q₂)} : Set Q₂)

/-- The one-state Markov ν-bottom as a topological subspace: the stationary distribution of a
    1-state chain is the unique point of `stdSimplex ℝ (Fin 1)`. -/
abbrev simplexPoint : Type := ↥(stdSimplex ℝ (Fin 1))

/-- The p-adic floor carrier is a one-element space. -/
noncomputable instance padic_floor_unique : Unique padicFloor := Set.uniqueSingleton _

/-- The one-state stationary point carrier is a one-element space:
    `stdSimplex ℝ (Fin 1) = {fun _ ↦ 1}`. -/
noncomputable instance simplex_point_unique : Unique simplexPoint := by
  have h : stdSimplex ℝ (Fin 1) = {fun _ ↦ (1 : ℝ)} := stdSimplex_unique ℝ (Fin 1)
  -- transport the singleton `Unique` instance across the set equality of carriers
  have e : simplexPoint ≃ ↥({fun _ ↦ (1 : ℝ)} : Set (Fin 1 → ℝ)) :=
    Equiv.setCongr h
  exact e.unique

/-- **GO (leaf-level ν reconciliation, IN-statement).** A genuine homeomorphism between the two
    ν-bottom carriers — the p-adic floor `{0} ⊆ Q₂` and the one-state stationary point of
    `stdSimplex ℝ (Fin 1)`. The ν-branch glues at the leaf even though T2 ruled out a global ambient
    homeomorphism. NOTE: this is `homeomorphOfUnique` — see `nu_leaf_reconcile_generic` for the
    honest deflation (it is the generic subsingleton map, carrying no distinguishing structure). -/
noncomputable def nu_leaf_reconcile : padicFloor ≃ₜ simplexPoint :=
  Homeomorph.homeomorphOfUnique padicFloor simplexPoint

/-- **The deflation, IN-statement (the NO-GO half made precise).** The *same* construction that builds
    `nu_leaf_reconcile` also homeomorphs the p-adic floor with the trivial one-point space `PUnit`. So
    the leaf reconciliation distinguishes the simplex point from nothing — it is the generic
    subsingleton homeomorphism, vacuous as an invariant. This is why the ν-glue is only
    set-theoretic / topological, in contrast to the structure-preserving μ-glue of T1
    (`t1_mu_cluster_glue`). -/
noncomputable def nu_leaf_reconcile_generic : padicFloor ≃ₜ PUnit :=
  Homeomorph.homeomorphOfUnique padicFloor PUnit

/-- **TC16 capstone (both halves IN one statement).** (a) GO: the ν-bottoms reconcile at the leaf
    (`Nonempty (padicFloor ≃ₜ simplexPoint)`); (b) deflation: the identical construction reconciles
    the p-adic floor with `PUnit`, so the leaf map is the generic subsingleton homeomorphism and
    carries no distinguishing structure. Together: the ν-branch glues, but only vacuously — confirming
    the μ/ν asymmetry (μ glues structurally via T1's functor span; ν glues only at the point). -/
theorem tc16_nu_leaf_glue_but_generic :
    Nonempty (padicFloor ≃ₜ simplexPoint) ∧ Nonempty (padicFloor ≃ₜ PUnit) :=
  ⟨⟨nu_leaf_reconcile⟩, ⟨nu_leaf_reconcile_generic⟩⟩

end ZeroParadox.ZPH_MC1_TC19

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib topology / p-adic / simplex libraries (`Q₂`,
`stdSimplex`, `Homeomorph`) — a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC19

#print axioms padic_floor_unique
#print axioms simplex_point_unique
#print axioms nu_leaf_reconcile
#print axioms nu_leaf_reconcile_generic
#print axioms tc16_nu_leaf_glue_but_generic

end PurityCheck
