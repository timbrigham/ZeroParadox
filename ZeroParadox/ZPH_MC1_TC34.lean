-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeObstructions
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree TC34 — the seam #5 fails as a two-sided connector to the ν-LIMIT node #3

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC18/TC27 deflated the Hilbert zero object's two-sidedness as *intra-category* (its zero-object
universal property lives only in `ModuleCat ℂ`) and tested the bridge from the seam #5 toward the
μ-bottom #4. This file isolates the **other** direction the seam would need to be a genuine
tree-connector: a canonical structure-respecting map from the seam #5 — `fD_functor.obj 0 =
StateSpace 0`, a `ModuleCat ℂ` object — TO node #3, the p-adic floor `{0} ⊆ Q₂`, the genuine
ν-LIMIT node (a `TopCat` / set object, the limit of the shrinking-ball inverse system).

**Pre-registered prediction: NO-GO.** The two objects live in different ambient categories with no
canonical functor `ModuleCat ℂ → TopCat` carrying the seam to the p-adic limit. The only shared
invariant is underlying-set cardinality 1, and a cardinality-forced singleton bijection is
*generic glue* (true of any two singletons), not a categorical bridge.

**What the Lean witnesses (load-bearing, in the statements):**

- `seam_carrier_subsingleton`, `padic_floor_subsingleton` — both carriers are singletons.
- `seam_to_padic_map_unique` — the type of maps `seam.carrier → #3.carrier` is a **subsingleton**:
  there is exactly one function, and it exists *only because the target is a singleton*. This is the
  cardinality-forced trivial map. It is GENERIC: the identical statement holds for any function into
  any singleton (`generic_singleton_target_map_unique`), so this map carries no information specific
  to these two objects — it is the singleton glue, not a bridge.
- `seam_role_not_transported` — the NO-GO payload. The seam #5 carries a genuine `ModuleCat ℂ`
  universal property (it is a **zero object**: initial ∧ terminal there), while node #3 is **not an
  initial object** of `TopCat` (`padic_bottom_not_initial`). So the singleton correspondence cannot
  transport the seam's categorical role to #3: any map seam → #3 is role-blind. The seam connects to
  the ν-limit node only as a bare singleton, NOT as a categorical bridge — confirming TC18's
  deflation in the ν-direction.

**Honest fence.** The Lean content is exactly the three facts above: both carriers are singletons; the
inter-carrier map is the unique cardinality-forced one and is generic; and the seam's zero-object role
in `ModuleCat ℂ` is not matched by an initial-object role of #3 in `TopCat`. The reading "therefore
the seam is not a literal two-sided bridge to the ν-limit node" is the framework's interpretation
attached to that pattern. This is an obstruction (separation) result, not a cross-domain
identification: it records precisely *how* the seam fails to bridge to #3.
-/

namespace ZeroParadox.ZPH_MC1_TC34

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPB ZeroParadox.ZPH_HilbFunctor
open ZeroParadox.ZPH_MC1_TreeObstructions

/-- The seam #5's carrier `StateSpace 0` is a singleton (subsingleton). -/
theorem seam_carrier_subsingleton : Subsingleton (StateSpace 0) :=
  ⟨fun a b => by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i⟩

/-- Node #3's carrier `{0} ⊆ Q₂` is a singleton (subsingleton). -/
theorem padic_floor_subsingleton : Subsingleton (↥({(0 : Q₂)} : Set Q₂)) :=
  ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩

/-- GENERIC baseline: for ANY type `α` and any singleton `β`, the function type `α → β` is a
    subsingleton. This is the cardinality fact that the inter-carrier map below is an instance of —
    making explicit that the seam → #3 map carries no information specific to these objects. -/
theorem generic_singleton_target_map_unique
    {α : Type*} {β : Type*} [Subsingleton β] : Subsingleton (α → β) :=
  ⟨fun f g => funext fun a => Subsingleton.elim (f a) (g a)⟩

/-- The only map from the seam #5's carrier to node #3's carrier is the cardinality-forced trivial
    one: the type of such maps is a subsingleton (exactly one function, the constant map onto the
    point). It exists *only because the target `{0} ⊆ Q₂` is a singleton* — it is the singleton glue
    (`generic_singleton_target_map_unique` specialized), NOT a categorical bridge. -/
theorem seam_to_padic_map_unique :
    Subsingleton (StateSpace 0 → ↥({(0 : Q₂)} : Set Q₂)) :=
  @generic_singleton_target_map_unique _ _ padic_floor_subsingleton

/-- **NO-GO payload.** The seam #5 carries a genuine `ModuleCat ℂ` universal property — it is a
    **zero object** there (initial ∧ terminal) — but node #3 is **not** an initial object of
    `TopCat`. So the singleton correspondence between the two carriers cannot transport the seam's
    categorical role to #3: the seam meets the ν-limit node #3 only as a bare singleton (the
    cardinality-forced map), not as a categorical two-sided bridge. -/
theorem seam_role_not_transported :
    Limits.IsZero (fD_functor.obj 0)
    ∧ IsEmpty (Limits.IsInitial (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))) :=
  ⟨ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero, padic_bottom_not_initial⟩

/-- The full TC34 verdict assembled: both carriers are singletons; the only inter-carrier map is the
    cardinality-forced trivial one (an instance of the generic singleton fact); and the seam's
    zero-object role in `ModuleCat ℂ` is not matched by any initial-object role of #3 in `TopCat`.
    Together: the seam #5 connects to the ν-limit node #3 only as a bare singleton, NOT as a literal
    categorical bridge — the NO-GO in the ν-direction. -/
theorem tc34_no_bridge_to_nu_limit :
    Subsingleton (StateSpace 0 → ↥({(0 : Q₂)} : Set Q₂))
    ∧ Limits.IsZero (fD_functor.obj 0)
    ∧ IsEmpty (Limits.IsInitial (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))) :=
  ⟨seam_to_padic_map_unique, seam_role_not_transported⟩

end ZeroParadox.ZPH_MC1_TC34

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `TopCat` / `ModuleCat` / p-adic libraries — a library
dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC34

#print axioms seam_carrier_subsingleton
#print axioms padic_floor_subsingleton
#print axioms generic_singleton_target_map_unique
#print axioms seam_to_padic_map_unique
#print axioms seam_role_not_transported
#print axioms tc34_no_bridge_to_nu_limit

end PurityCheck
