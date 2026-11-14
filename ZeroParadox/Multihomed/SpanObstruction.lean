-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import ZeroParadox.Multihomed.TreeObstructions
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The #1↔#3 cross-root obstruction under a SPAN (THIN-BUT-HONEST)

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

- `padic_floor_unique_SpanObstruction` — the p-adic floor `↥({0} : Set Q₂)` is a one-point space (`Unique`).
- `ordinal_floor_unique` — the well-founded ordinal floor `↥({0} : Set Ordinal)` is one point.
- `span_apex_to_padic_floor : PUnit.{1} ≃ₜ ↥({0} : Set Q₂)` — a homeomorphism, but only because both
  sides are singletons (`homeomorphOfUnique`).
- `span_apex_to_ordinal_floor : PUnit.{1} ≃o ↥({0} : Set Ordinal)` — an order-iso, but only because
  both sides are subsingletons (every `≤` collapses to `le_refl`).
- `apex_iso_padic_ordinal_floor` — the capstone: a single apex `S = PUnit` is iso to both singleton
  floors, `#3 ⟵ S ⟶ #1` in-statement.

**Why this is NOT T1's reconciliation strength (the retracted overclaim).** An earlier draft of this
file headlined "Race outcome: NO-GO — the cross-root cut is a method artifact; the pair reconciles at
the span strength that made T1 GO." That is **false** and is retracted. The capstone proves only that
*two one-point sets are each isomorphic to a one-point apex* — a fact that holds for **any** two
singletons whatsoever and carries **zero** structural content specific to #1 or #3. T1's span was
GO for a different reason: its legs (`fC_floor_transport` / `fD_floor_transport`) **transport the
floor's descent morphism onto the categorical bottom's initiality morphism**, and those equations are
*in* `t1_mu_cluster_glue`'s statement. This file's apex legs transport **nothing** — they are isos of bare
points with no universal role. The two spans therefore sit at *different* reconciliation strengths:
T1's carries a universal role; this file's is the trivial floor of the strength scale. So a singleton-apex
span existing does **not** show the cross-root cut is a method artifact, because it does not match
T1's role-preserving span.

**What is proved.** Two facts, both true, paired in `apex_span_no_ambient_strictMono`:
1. a singleton-apex span exists for the two bottom *points* (vacuous: they are singletons), and
2. `no_strictMono_real_to_ordinal` (`ZeroParadox/Multihomed/TreeObstructions.lean`): no strict-mono
   map `ℝ → Ordinal`. ℝ is #2's carrier there (the Markov attractor), not #3's: an #1↔#2 fact. #3's
   ambient `Q₂` appears nowhere in it, so the file has no ambient-level content for #3.

**Honest scope (interpretation vs Lean).** The *interpretation* this file does NOT support: that the GO/NO-GO asymmetry is a method artifact. To
support that, the apex legs would have to carry a universal role matching T1's (transporting a
descent/initiality morphism); a singleton-iso does not. The tree's μ/ν cross-root cut therefore
stands; this file neither strengthens nor refutes it. The #1↔#3 separation the corpus does carry is
`padic_bottom_not_initial` (against `nat_floor_isInitial`, `ZeroParadox/Multihomed/TreeT1.lean`): a
fact about the one-point space `{0} ⊆ Q₂` itself as a `TopCat` object, not about an ambient carrier.
-/

namespace ZeroParadox

open ZeroParadox
open scoped Topology

/-- #3 carrier as a one-point space: the p-adic floor `{0} ⊆ Q₂` is `Unique`. -/
noncomputable instance padic_floor_unique_SpanObstruction : Unique (↥({(0 : Q₂)} : Set Q₂)) := Set.uniqueSingleton 0

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

/-- **capstone — the two singleton bottom POINTS admit a trivial common-apex span.**
    A single apex `S = PUnit` is isomorphic to the p-adic floor #3 (a homeomorphism) and to the
    ordinal floor #1 (an order-iso): `#3 ⟵ S ⟶ #1`, in-statement. **This is vacuous on purpose:**
    both floor carriers are singletons, so the isos hold for the trivial reason that any two
    one-point sets are isomorphic to a one-point apex — it carries NO structural content specific to
    #1 or #3. It does NOT match T1's GO span, whose legs transport a descent/initiality morphism
    (a universal role, in `t1_mu_cluster_glue`'s statement). The apex legs here transport nothing.
    So this does NOT show the cross-root cut is a method artifact. `apex_span_no_ambient_strictMono`
    pairs it with an #1↔#2 fact about ℝ; that adds no content about #3. -/
theorem apex_iso_padic_ordinal_floor :
    Nonempty (PUnit.{1} ≃ₜ ↥({(0 : Q₂)} : Set Q₂)) ∧
    Nonempty (PUnit.{1} ≃o ↥({(0 : Ordinal)} : Set Ordinal)) :=
  ⟨⟨span_apex_to_padic_floor⟩, ⟨span_apex_to_ordinal_floor⟩⟩

/-- `Statement:` (1) the singleton bottom *points* admit the trivial common-apex span above, and
    (2) `no_strictMono_real_to_ordinal`: there is no strict-mono map `ℝ → Ordinal`. ℝ is #2's
    carrier (the Markov attractor, `ZeroParadox/Multihomed/TreeObstructions.lean`), not #3's, so (2)
    is an #1↔#2 fact and nothing in the statement concerns #3's ambient `Q₂`. The #1↔#3 separation
    the corpus carries is `padic_bottom_not_initial`, a fact about the one-point space `{0} ⊆ Q₂`
    itself. This is NOT a method-artifact result — see the capstone docstring and Formal Overview. -/
theorem apex_span_no_ambient_strictMono :
    (Nonempty (PUnit.{1} ≃ₜ ↥({(0 : Q₂)} : Set Q₂)) ∧
      Nonempty (PUnit.{1} ≃o ↥({(0 : Ordinal)} : Set Ordinal))) ∧
    ¬ ∃ f : ℝ → Ordinal, StrictMono f :=
  ⟨apex_iso_padic_ordinal_floor,
    ZeroParadox.no_strictMono_real_to_ordinal⟩

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / p-adic / topology libraries — a library
dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox

#print axioms span_apex_to_padic_floor
#print axioms span_apex_to_ordinal_floor
#print axioms apex_iso_padic_ordinal_floor
#print axioms apex_span_no_ambient_strictMono

end PurityCheck
