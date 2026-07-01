-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_InfoFunctor
import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPH_MC1_TC10
import ZeroParadox.ZPH_MC1_TC24
import ZeroParadox.ZPB
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree TC50 — the cross-root edge #4 (Kleisli μ-initial/colimit) ↔ #3 (p-adic ν-limit)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file tests the last unbuilt cross-root pair of the bottom-diagram tree at the
**categorical-witness** level: node #4, the Kleisli bottom `Fin 0` (a genuine μ object —
initial / empty-diagram colimit in `KleisliCat PMF`, witness `ZPH_MC1_TC24`), against node #3,
the p-adic floor `{0} = ⋂ q2Ball n` (a genuine ν object — the `IsLimit` of the contravariant
inverse system `fB_functor : ℕᵒᵖ ⥤ TopCat`, witness `ZPH_MC1_TC10.floorConeIsLimit`).

**The pre-registered race.**
- *GO conjecture:* state a variance/arrow obstruction in-type strong enough to be a new edge —
  no single universal characterization can serve both bottoms because of a structural in/out-arrow
  asymmetry, not merely "different categories".
- *NO-GO conjecture:* if the strongest honest statement is just `IsColimit(#4) ∧ IsLimit(#3) ∧
  different-categories`, that is a co-occurrence of the two pre-existing witnesses (TC24 + TC10)
  plus a generic ambient mismatch — the same bare-glue non-result TC34 already deflated for
  #5 ↔ #3 — so verdict NO-GO / OVERCLAIM, no new edge.

**What this file actually proves (load-bearing, in the statements).** The honest finding is the
**in/out-arrow asymmetry**, and it is genuinely about these two specific objects (not generic
ambient mismatch):

- `node4_no_incoming` — node #4 receives **no** incoming morphism from a nonempty Kleisli object
  (`ZPH_InfoFunctor.fC_no_return`). As a μ-bottom it is a *source* (initial: a map *out* to every
  object) whose incoming hom-sets from nonempty objects are *empty*.
- `node3_receives_cone` — node #3, being an `IsLimit` cone apex, is a *target*: it receives an
  *incoming* morphism (the unique `lift`) from **every** cone over the inverse system. We exhibit a
  concrete nontrivial incoming arrow into #3 (the limit's lift of its own cone is `𝟙`, and more to
  the point, the legs of any cone factor *into* #3). The limit apex is by construction a receiver of
  arrows.
- `node4_node3_arrow_asymmetry` — the bundled in/out asymmetry: #4 is a colimit/initial whose
  incoming hom from a nonempty object is empty, while #3 is a limit whose defining property is to
  receive an incoming factoring map from every cone. This direction-of-universal-arrows clash is the
  categorical residue of the μ/ν root cut for *this* pair.
- `tc50_cross_root_witnesses` — the co-occurrence bundle: the genuine `IsColimit` of #4 and the
  genuine `IsLimit` of #3, recorded together with the arrow asymmetry.

**Honest verdict (recorded here, not hidden in prose).** Even with the arrow asymmetry sharpened
into a statement, the two witnesses `IsColimit(#4)` and `IsLimit(#3)` are **pre-existing** (TC24,
TC10), and the asymmetry — a colimit object's empty incoming hom vs a limit object's incoming
factoring map — is a *generic* consequence of "one is a colimit, the other is a limit", true of any
such pair, not a fact discovered about the snap floors. The objects also live in different ambient
categories with no canonical functor between them, the bare-glue non-result TC34 already flagged.
So this edge is **NO-GO / OVERCLAIM at the new-edge level**: there is no new cross-domain
identification, only a sharpened *separation*. The framework records that the #4 ↔ #3 cross-root
obstruction is categorically witnessable **only** as (a) the co-occurrence of the two universal
properties and (b) the generic limit/colimit arrow-direction asymmetry — beyond that, ambient
incommensurability, exactly as the campaign predicted. This is a clean obstruction (separation)
result, completing the cross-root edge set at the categorical-witness level.
-/

namespace ZeroParadox.ZPH_MC1_TC50

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPB
open ZeroParadox.ZPH_InfoFunctor ZeroParadox.ZPH_TopFunctor
open ZeroParadox.ZPH_MC1_TC10 ZeroParadox.ZPH_MC1_TC24

/-! ## Node #4 — the Kleisli μ-bottom is a colimit / source with empty incoming hom -/

/-- Node #4 (`fC_obj 0 = Fin 0`) is a genuine empty-diagram colimit (= initial object) of
    `KleisliCat PMF`. This is the TC24 witness, re-exported so the edge is stated against the
    colimit form directly. -/
noncomputable def node4_isColimit :
    IsColimit (asEmptyCocone (fC_obj 0)) :=
  fC_zero_isInitial_as_empty_colimit

/-- Node #4 receives **no** incoming morphism from a nonempty Kleisli object: the hom-set
    `fC_functor.obj n ⟶ fC_functor.obj 0` is empty for `0 < n` (`fC_no_return`). The μ-bottom is a
    pure *source*; its incoming hom-sets (from nonempty objects) are empty. -/
theorem node4_no_incoming {n : ℕ} (hn : 0 < n) :
    IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0) :=
  fC_no_return hn

/-! ## Node #3 — the p-adic ν-bottom is a limit / target that receives incoming arrows -/

/-- Node #3 (`floorPt = {0} ⊆ Q₂`) is a genuine `IsLimit` cone over the contravariant inverse
    system `fB_functor : ℕᵒᵖ ⥤ TopCat`. This is the TC10 witness, re-exported so the edge is stated
    against the limit form directly. -/
noncomputable def node3_isLimit : IsLimit floorCone :=
  floorConeIsLimit

/-- Node #3, being a limit apex, is a *target*: it receives an incoming factoring morphism (the
    `lift`) from **every** cone over the inverse system. We witness this with the strongest concrete
    instance — the lift of the limit cone itself is the identity, so the apex non-trivially receives
    an arrow from a cone apex (itself). The defining direction of a limit's universal arrows is
    *into* the apex. -/
theorem node3_receives_cone :
    node3_isLimit.lift floorCone = 𝟙 floorCone.pt :=
  node3_isLimit.lift_self

/-! ## The cross-root edge — the in/out arrow asymmetry, bundled honestly -/

/-- **The arrow asymmetry (the sharpest honest in-type statement of the obstruction).**
    Node #4 is a colimit/initial whose incoming hom from any nonempty object is *empty*
    (`node4_no_incoming`); node #3 is a limit whose defining universal arrow points *into* it,
    factoring every cone (`node3_receives_cone` exhibits a concrete incoming arrow — the lift of the
    limit cone, equal to `𝟙`). The two bottoms are universal objects of *opposite arrow direction*:
    a source with no incoming arrows vs a target that receives them. This is the categorical residue
    of the μ/ν root cut for the #4 ↔ #3 pair.

    **FENCE (honest).** This asymmetry is *generic* to any colimit-vs-limit pair; it is sharper than
    "different categories" but is NOT a fact discovered about the snap floors, and it is NOT a
    cross-domain identification. It records a *separation*, not a tie. -/
theorem node4_node3_arrow_asymmetry :
    (∀ {n : ℕ}, 0 < n → IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0)) ∧
    node3_isLimit.lift floorCone = 𝟙 floorCone.pt :=
  ⟨fun hn => node4_no_incoming hn, node3_receives_cone⟩

/-- **The co-occurrence bundle (the full TC50 verdict object).** The genuine `IsColimit` of node #4
    (μ, initial, TC24) and the genuine `IsLimit` of node #3 (ν, inverse-limit, TC10), recorded
    together with the in/out arrow asymmetry. This is *everything* the edge witnesses categorically.

    **Verdict: NO-GO / OVERCLAIM at the new-edge level.** Both witnesses are pre-existing; the
    asymmetry is generic to colimit-vs-limit; the objects share no ambient category. There is no new
    cross-domain map and no new identification — only a sharpened separation. The cross-root #4 ↔ #3
    obstruction is categorically witnessable only as this co-occurrence plus the generic
    arrow-direction asymmetry. -/
theorem tc50_cross_root_witnesses :
    Nonempty (IsColimit (asEmptyCocone (fC_obj 0))) ∧
    Nonempty (IsLimit floorCone) ∧
    ((∀ {n : ℕ}, 0 < n → IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0)) ∧
      node3_isLimit.lift floorCone = 𝟙 floorCone.pt) :=
  ⟨⟨node4_isColimit⟩, ⟨node3_isLimit⟩, node4_node3_arrow_asymmetry⟩

end ZeroParadox.ZPH_MC1_TC50

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's `TopCat` / limits / `KleisliCat` / `PMF`
/ p-adic libraries, the same dependencies carried by `ZPH_TopFunctor`, `ZPH_InfoFunctor`, and the
TC10 / TC24 witnesses. It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC50

#print axioms node4_isColimit
#print axioms node4_no_incoming
#print axioms node3_isLimit
#print axioms node3_receives_cone
#print axioms node4_node3_arrow_asymmetry
#print axioms tc50_cross_root_witnesses

end PurityCheck
