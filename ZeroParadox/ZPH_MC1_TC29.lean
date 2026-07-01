-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPD
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC29 — the THREE-carrier ν/seam leaf set is one-point (adds #5 Hilbert to TC19's #3/#2)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

**Honest verdict: DECORATIVE (generic one-point case throughout).** Like TC19, this file proves
nothing structural about the p-adic, simplex, or Hilbert objects: every result is a consequence of the
single fact that the carriers are *one-point spaces*. It is **not** a strengthening of TC19's claim
about the #3/#2 leaves.

**Why TC29 is a separate node and not pure duplication of TC19.** TC19 (`ZPH_MC1_TC19.lean`) covers
exactly the two ν-bottom leaves #3 (p-adic floor `↥({0} : Set Q₂)`) and #2 (`Fin 1` stationary point
`↥(stdSimplex ℝ (Fin 1))`). TC29 **adds the #5 Hilbert seam carrier** `StateSpace 0 =
EuclideanSpace ℂ (Fin 0)` to the leaf-reconciliation set and witnesses the three-way reconciliation
**in the capstone statement** (`nu_leaf_glue_three`). The #5 carrier is load-bearing in that statement
— it is not a conjunction of facts TC19 already proves. So TC29's tree contribution is the *edge to the
#5 seam node*: the Hilbert bottom's carrier reconciles with the other two ν-leaves at the point. The
honest verdict is that this edge, like TC19's, is the **generic subsingleton** one — it carries no
Hilbert/p-adic/simplex content — and the file says so in-statement (see the `≃ₜ PUnit` genericity
witnesses).

**What is actually proved (all of it the degenerate one-point case).** Each of the three carriers — #3
`↥({0} : Set Q₂)`, #2 `↥(stdSimplex ℝ (Fin 1))`, #5 `StateSpace 0` — is `Unique`, i.e. a singleton.
Everything else follows from that alone:

- `padic_floor_unique` / `simplex_point_unique` / `hilbert_carrier_unique` — the three carriers are
  each `Unique`. These are the only statements that touch the actual objects, and each says only "this
  carrier has one element".
- `hom_padic_simplex_subsingleton`, `hom_padic_hilbert_subsingleton` — `Subsingleton C(X, Y)`. These
  are **`inferInstance`**: Mathlib's *generic* codomain-subsingleton instance for `C(X, Y)`
  (`Subsingleton Y ⇒ Subsingleton C(X, Y)`) applied to one-point carriers. Zero p-adic / simplex /
  Hilbert content — the same statement holds for any map into any singleton.
- `nu_leaf_homeo` / `seam_leaf_homeo` — `homeomorphOfUnique`, the canonical homeomorphism between two
  `Unique` spaces (#3 ≃ₜ #2 and #3 ≃ₜ #5). Purely cardinality-driven.
- `padic_is_punit` / `hilbert_is_punit` — the genericity witnesses (the NO-GO half, in-statement): the
  *same* `homeomorphOfUnique` construction homeomorphs the p-adic floor AND the Hilbert carrier with
  the trivial one-point space `PUnit`. So each leaf reconciliation distinguishes the carriers from
  nothing — it is vacuous as an invariant.
- `nu_leaf_glue_three` (capstone) — the load-bearing claim. It conjoins (a) the three-way leaf homeo
  span `#3 ≃ₜ #2` and `#3 ≃ₜ #5` (this is what is NEW vs TC19: #5 is in the statement), with (b) the
  genericity witness `#5 ≃ₜ PUnit`. The conjunction says: the Hilbert seam carrier joins the ν-leaf
  glue, but only by the generic subsingleton map. The #5 carrier is load-bearing; the deflation is
  in-statement.

**Why the pre-registered obstruction is absent here, NOT defeated here.** The intended obstruction —
that #3's floor remembers a valuation/embedding invariant the bare leaves lack — does not even arise at
this level, because the valuation structure lives on the **ambient** `Q₂`, and the one-point subspace
`{0}` forgets it (`padic_is_punit`). This file cannot speak to the real asymmetry. The load-bearing μ/ν
asymmetry (the connected-vs-totally-disconnected wall) is an **ambient** phenomenon and remains **OPEN
in `ZPH_MC1_TreeT2`** — it is neither proved nor probed here.

**What is Lean vs interpretation.** Lean proves exactly: three carriers are `Unique`; the #5 Hilbert
carrier reconciles with #3/#2 at the point (the new content over TC19); hom-sets between them are
`Subsingleton`; each carrier is homeomorphic to `PUnit` (genericity). Any reading of this as "the seam
leaf glue is canonically forced" is just the restatement that one-point spaces have unique maps — it is
not framework-specific evidence. The single non-vacuous claim in this corner of the tree (the ambient
valuation asymmetry) is NOT in this file.
-/

namespace ZeroParadox.ZPH_MC1_TC29

open ZeroParadox.ZPB ZeroParadox.ZPH_TopFunctor ZeroParadox.ZPD
open scoped Topology

/-- #3: the p-adic ν-bottom as a topological subspace, the floor `{0} ⊆ Q₂`
    (`fB_bottom_is_limit : ⋂ n, q2Ball n = {0}`). -/
abbrev padicFloor : Type := ↥({(0 : Q₂)} : Set Q₂)

/-- #2: the one-state Markov ν-bottom, the unique point of `stdSimplex ℝ (Fin 1)`. -/
abbrev simplexPoint : Type := ↥(stdSimplex ℝ (Fin 1))

/-- #5: the Hilbert bottom's underlying carrier `StateSpace 0 = EuclideanSpace ℂ (Fin 0)`. -/
abbrev hilbertCarrier : Type := StateSpace 0

/-- #3 carrier is a one-element space. -/
noncomputable instance padic_floor_unique : Unique padicFloor := Set.uniqueSingleton _

/-- #2 carrier is a one-element space: `stdSimplex ℝ (Fin 1) = {fun _ ↦ 1}`. -/
noncomputable instance simplex_point_unique : Unique simplexPoint := by
  have h : stdSimplex ℝ (Fin 1) = {fun _ ↦ (1 : ℝ)} := stdSimplex_unique ℝ (Fin 1)
  have e : simplexPoint ≃ ↥({fun _ ↦ (1 : ℝ)} : Set (Fin 1 → ℝ)) := Equiv.setCongr h
  exact e.unique

/-- #5 carrier is a one-element space: `EuclideanSpace ℂ (Fin 0)` has only `0`. -/
instance hilbert_carrier_unique : Unique hilbertCarrier where
  default := 0
  uniq a := by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i

/-! ### One-point consequences (generic, NOT framework-specific).

`Subsingleton C(X, Y)` whenever `Subsingleton Y` — this is Mathlib's generic codomain-subsingleton
instance (`ContinuousMap.Defs`), true of any map into any singleton. Each carrier here is `Unique`,
so the instances below are just that generic fact applied to one-point carriers. They carry NO
p-adic / simplex / Hilbert content. -/

/-- The hom-set `C(padicFloor, simplexPoint)` is a `Subsingleton`. This is `inferInstance` resolving
    the GENERIC codomain-subsingleton instance, because `simplexPoint` is a one-point space — it has
    no p-adic or simplex content and would hold for any map into any singleton. Naming note: this is
    NOT a "forcing" specific to these objects; it is "maps into a one-point space are unique". -/
instance hom_padic_simplex_subsingleton : Subsingleton C(padicFloor, simplexPoint) :=
  inferInstance

/-- The hom-set `C(padicFloor, hilbertCarrier)` is a `Subsingleton`, again by the generic
    codomain-subsingleton instance (the codomain is one-point). No Hilbert content. -/
instance hom_padic_hilbert_subsingleton : Subsingleton C(padicFloor, hilbertCarrier) :=
  inferInstance

/-- The canonical homeomorphism between two `Unique` spaces (`homeomorphOfUnique`): "any two
    one-point spaces are homeomorphic". Cardinality-driven, not a structural identification.
    This is the #3 ≃ₜ #2 leaf reconciliation TC19 already established. -/
noncomputable def nu_leaf_homeo : padicFloor ≃ₜ simplexPoint :=
  Homeomorph.homeomorphOfUnique padicFloor simplexPoint

/-- **The TC29-specific edge: #3 ≃ₜ #5.** The canonical homeomorphism between the p-adic floor and the
    Hilbert seam carrier `StateSpace 0` — again `homeomorphOfUnique` (both are `Unique`). This is the
    leaf reconciliation TC19 does NOT cover: it adds the #5 seam node to the ν-leaf glue set. Generic
    (cardinality-driven), per the genericity witnesses below. -/
noncomputable def seam_leaf_homeo : padicFloor ≃ₜ hilbertCarrier :=
  Homeomorph.homeomorphOfUnique padicFloor hilbertCarrier

/-- `padicFloor ≃ₜ PUnit`, again `homeomorphOfUnique`. Genericity witness for #3: the valuation/
    embedding invariant lives on the ambient `Q₂`, and the one-point subspace `{0}` forgets it, so the
    floor-as-space is a bare point. The real asymmetry is ambient and stays OPEN in `ZPH_MC1_TreeT2`. -/
noncomputable def padic_is_punit : padicFloor ≃ₜ PUnit :=
  Homeomorph.homeomorphOfUnique padicFloor PUnit

/-- `hilbertCarrier ≃ₜ PUnit`, again `homeomorphOfUnique`. Genericity witness for the #5 seam edge:
    the *same* construction that builds `seam_leaf_homeo` reconciles the Hilbert carrier with the
    trivial one-point space. So the #5 leaf glue distinguishes the Hilbert carrier from nothing — it is
    the generic subsingleton homeomorphism, vacuous as an invariant. The Hilbert bottom's structural
    content (its zero-object seam role in `ModuleCat ℂ`) lives in the ambient category, not in this
    one-point carrier. -/
noncomputable def hilbert_is_punit : hilbertCarrier ≃ₜ PUnit :=
  Homeomorph.homeomorphOfUnique hilbertCarrier PUnit

/-- **TC29 capstone — the three-carrier ν/seam leaf glue, with #5 Hilbert load-bearing in-statement.**
    The NEW content over TC19: the statement names the #5 Hilbert seam carrier, not only #3/#2.
    Conjoins (a) the three-way leaf homeo span `padicFloor ≃ₜ simplexPoint` (= #3 ≃ₜ #2) and
    `padicFloor ≃ₜ hilbertCarrier` (= #3 ≃ₜ #5, the TC29-specific edge), with (b) the genericity
    deflation `hilbertCarrier ≃ₜ PUnit`. Reading: the Hilbert seam carrier joins the ν-leaf glue, but
    only by the generic subsingleton map — so this edge carries no Hilbert content beyond cardinality,
    exactly as the one-point case forces. Honest verdict: DECORATIVE, edge-to-#5 added, deflation
    in-statement. -/
theorem nu_leaf_glue_three :
    (Nonempty (padicFloor ≃ₜ simplexPoint) ∧ Nonempty (padicFloor ≃ₜ hilbertCarrier))
      ∧ Nonempty (hilbertCarrier ≃ₜ PUnit) :=
  ⟨⟨⟨nu_leaf_homeo⟩, ⟨seam_leaf_homeo⟩⟩, ⟨hilbert_is_punit⟩⟩

end ZeroParadox.ZPH_MC1_TC29

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib topology / p-adic / simplex / Euclidean-space libraries
(`Q₂`, `stdSimplex`, `StateSpace`, `Homeomorph`, `ContinuousMap`) — a library dependency, not a new
commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC29

#print axioms padic_floor_unique
#print axioms simplex_point_unique
#print axioms hilbert_carrier_unique
#print axioms hom_padic_simplex_subsingleton
#print axioms hom_padic_hilbert_subsingleton
#print axioms nu_leaf_homeo
#print axioms seam_leaf_homeo
#print axioms padic_is_punit
#print axioms hilbert_is_punit
#print axioms nu_leaf_glue_three

end PurityCheck
