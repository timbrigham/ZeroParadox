-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import ZeroParadox.ZPH_MC1_TreeObstructions
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC17 / TC14 — the #1↔#3 cross-root obstruction under a SPAN (THIN-BUT-HONEST)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file probed whether the cross-root NO-GO edges (E4, SPLIT) survive a **span** instead of a
*direct* structure-preserving map, for the pair **#1 (well-founded ordinal floor) ↔ #3 (p-adic
inverse-limit floor)**. The original framing was: T1's μ-cluster was declared GO by a SPAN
(`#4 ⟵ #1 ⟶ #5`), so if a span also reconciled the cross-root pair, the GO/NO-GO asymmetry would be
a "reconciliation-strength method artifact" rather than a μ/ν property.

**Verdict: THIN-BUT-HONEST. The intended deflationary conclusion is NOT earned, and the file does not
claim it.** What the Lean actually proves is much weaker than T1's reconciliation, and weaker in a way
that voids the method-artifact reading:

- `padic_floor_unique` — the p-adic floor `↥({0} : Set Q₂)` is a one-point space (`Unique`).
- `ordinal_floor_unique` — the well-founded ordinal floor `↥({0} : Set Ordinal)` is one point.
- `span_apex_to_padic_floor : PUnit.{1} ≃ₜ ↥({0} : Set Q₂)` — a homeomorphism, but only because both
  sides are singletons (`homeomorphOfUnique`).
- `span_apex_to_ordinal_floor : PUnit.{1} ≃o ↥({0} : Set Ordinal)` — an order-iso, but only because
  both sides are subsingletons (every `≤` collapses to `le_refl`).
- `tc17_span_reconciles_1_and_3` — the capstone: a single apex `S = PUnit` is iso to both singleton
  floors, `#3 ⟵ S ⟶ #1` in-statement.

**Why this is NOT T1's reconciliation strength (the retracted overclaim).** An earlier draft of this
file headlined "Race outcome: NO-GO — the cross-root cut is a method artifact; the pair reconciles at
the span strength that made T1 GO." That is **false** and is retracted. The capstone proves only that
*two one-point sets are each isomorphic to a one-point apex* — a fact that holds for **any** two
singletons whatsoever and carries **zero** structural content specific to #1 or #3. T1's span was
GO for a different reason: its legs (`fC_floor_transport` / `fD_floor_transport`) **transport the
floor's descent morphism onto the categorical bottom's initiality morphism**, and those equations are
*in* `t1_mu_cluster_glue`'s statement. TC17's apex legs transport **nothing** — they are isos of bare
points with no universal role. The two spans therefore sit at *different* reconciliation strengths:
T1's carries a universal role; TC17's is the trivial floor of the strength scale. So a singleton-apex
span existing does **not** show the cross-root cut is a method artifact, because it does not match
T1's role-preserving span.

**What is honestly proved.** Two facts, both true, witnessed in `tc17_span_but_no_direct_ambient_map`:
1. a singleton-apex span exists for the two bottom *points* (vacuous: they are singletons), and
2. the *direct* ambient obstruction survives — `no_strictMono_real_to_ordinal` (in
   `ZPH_MC1_TreeObstructions`) still rules out a strict-mono embedding of the attractor ambient `ℝ`
   into the well-order. ℝ's `<` is not well-founded; the ordinal's is. That is the real content.

**Honest scope (interpretation vs Lean).** The Lean fact is: the singleton bottom *points* admit a
trivial common-apex span, while the *ambient/descent-carrier* direct map remains obstructed. The
*interpretation* this file does NOT support: that the GO/NO-GO asymmetry is a method artifact. To
support that, the apex legs would have to carry a universal role matching T1's (transporting a
descent/initiality morphism); a singleton-iso does not. The tree's μ/ν cross-root cut therefore
stands; this file neither strengthens nor refutes it, it only records that the obstruction is genuinely
about the ambient carriers, not the bare bottom points.
-/

namespace ZeroParadox.ZPH_MC1_TC17

open ZeroParadox.ZPB
open scoped Topology

/-- #3 carrier as a one-point space: the p-adic floor `{0} ⊆ Q₂` is `Unique`. -/
noncomputable instance padic_floor_unique : Unique (↥({(0 : Q₂)} : Set Q₂)) := Set.uniqueSingleton 0

/-- #1 carrier as a one-point order: the well-founded ordinal floor `{0} ⊆ Ordinal` is `Unique`. -/
instance ordinal_floor_unique : Unique (↥({(0 : Ordinal)} : Set Ordinal)) := Set.uniqueSingleton 0

/-- Span apex → #3: a genuine **homeomorphism** from the singleton apex to the p-adic floor.
    Structure-preserving in #3's topological (ν / inverse-limit) setting. -/
noncomputable def span_apex_to_padic_floor : PUnit.{1} ≃ₜ ↥({(0 : Q₂)} : Set Q₂) :=
  Homeomorph.homeomorphOfUnique PUnit.{1} (↥({(0 : Q₂)} : Set Q₂))

/-- Span apex → #1: a genuine **order isomorphism** from the singleton apex to the ordinal floor.
    Structure-preserving in #1's order/well-founded (μ / descent) setting. Built by hand because both
    sides are subsingletons, so every `≤` is forced. -/
def span_apex_to_ordinal_floor : PUnit.{1} ≃o ↥({(0 : Ordinal)} : Set Ordinal) where
  toFun _ := default
  invFun _ := PUnit.unit
  left_inv := fun _ => rfl
  right_inv := fun y => Subsingleton.elim _ _
  map_rel_iff' := by
    intro a b
    constructor
    · intro _; exact le_refl _
    · intro _; exact le_refl _

/-- **TC17 capstone — the two singleton bottom POINTS admit a trivial common-apex span.**
    A single apex `S = PUnit` is isomorphic to the p-adic floor #3 (a homeomorphism) and to the
    ordinal floor #1 (an order-iso): `#3 ⟵ S ⟶ #1`, in-statement. **This is vacuous on purpose:**
    both floor carriers are singletons, so the isos hold for the trivial reason that any two
    one-point sets are isomorphic to a one-point apex — it carries NO structural content specific to
    #1 or #3. It does NOT match T1's GO span, whose legs transport a descent/initiality morphism
    (a universal role, in `t1_mu_cluster_glue`'s statement). The apex legs here transport nothing.
    So this does NOT show the cross-root cut is a method artifact; see `tc17_span_but_no_direct_ambient_map`
    for the real content (the ambient direct-map obstruction survives). -/
theorem tc17_span_reconciles_1_and_3 :
    Nonempty (PUnit.{1} ≃ₜ ↥({(0 : Q₂)} : Set Q₂)) ∧
    Nonempty (PUnit.{1} ≃o ↥({(0 : Ordinal)} : Set Ordinal)) :=
  ⟨⟨span_apex_to_padic_floor⟩, ⟨span_apex_to_ordinal_floor⟩⟩

/-- **The real content, in-statement.** Two facts hold simultaneously: (1) the singleton bottom
    *points* admit the trivial common-apex span above, and (2) the *direct* ambient obstruction
    survives — `no_strictMono_real_to_ordinal` still holds: there is no strict-mono embedding of the
    attractor ambient `ℝ` into the well-order (ℝ's `<` is not well-founded; the ordinal's is). The
    honest finding is just this simultaneity: the cross-root obstruction is genuinely about the
    ambient/descent carriers, and the bare bottom *points* being singletons does not touch it. This
    is NOT a method-artifact result — see the capstone docstring and Formal Overview. -/
theorem tc17_span_but_no_direct_ambient_map :
    (Nonempty (PUnit.{1} ≃ₜ ↥({(0 : Q₂)} : Set Q₂)) ∧
      Nonempty (PUnit.{1} ≃o ↥({(0 : Ordinal)} : Set Ordinal))) ∧
    ¬ ∃ f : ℝ → Ordinal, StrictMono f :=
  ⟨tc17_span_reconciles_1_and_3,
    ZeroParadox.ZPH_MC1_TreeObstructions.no_strictMono_real_to_ordinal⟩

end ZeroParadox.ZPH_MC1_TC17

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / p-adic / topology libraries — a library
dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC17

#print axioms span_apex_to_padic_floor
#print axioms span_apex_to_ordinal_floor
#print axioms tc17_span_reconciles_1_and_3
#print axioms tc17_span_but_no_direct_ambient_map

end PurityCheck
