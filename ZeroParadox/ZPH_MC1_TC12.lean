-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, keystone TC12 — the seam IS the categorical μ=ν coincidence

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The bottom-diagram tree (`tree_test_campaign_2026-06-29.md`) splits the framework bottoms across a μ
root (initial / least-fixed-point / colimit) and a ν root (terminal / greatest-fixed-point / limit).
`ZPH_MC1_TreeSeam` already identified node #5 (the Hilbert bottom `fD_functor.obj 0 = StateSpace 0`)
as a *zero object* and called it "the seam". This file restates the **zero-object definition** as the
μ=ν seam property and **witnesses it at the real node**. In *any* category, a zero object is by
definition an object that is simultaneously initial and terminal, i.e. the place where the
least-fixed-point (initial / μ) and greatest-fixed-point (terminal / ν) universal characterizations
coincide. That coincidence is what "the seam" names.

**Scope — this is a definitional unfolding, not a new theorem.** Mathlib already defines `IsZero` as
`unique_to ∧ unique_from` (`Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`). The biconditional
below repackages that definition in terms of `IsInitial` / `IsTerminal`; there was never a live
possibility that `IsZero` is "stronger or weaker" than initial ∧ terminal, since by definition they
are the same. The value here is faithfulness — phrasing the seam's defining property explicitly and
checking it holds at the actual ZP-D bottom node, with the unfolding spelled out rather than assumed.

- `isZero_iff_isInitial_and_isTerminal {X : C} : IsZero X ↔ Nonempty (IsInitial X) ∧ Nonempty (IsTerminal X)`.
  Forward is Mathlib's `IsZero.isInitial` / `IsZero.isTerminal`. The reverse repackages the two
  universal families `IsZero` requires: an initial object gives a unique morphism *out*
  (`IsInitial.to` + `IsInitial.hom_ext`), a terminal object gives a unique morphism *in*
  (`IsTerminal.from` + `IsTerminal.hom_ext`). This is a short restatement of the `IsZero` definition,
  not novel content.

- `seam_is_mu_nu_coincidence` — the definition instantiated at the actual seam node: `fD_functor.obj 0`
  is a zero object **iff** it is both initial and terminal, and (since it *is* a zero object, via
  `ZPH_MC1_TreeSeam.hilbert_bottom_isZero`) both sides hold. So the #5 seam is literally the μ=ν
  coincidence point, not merely a node we labelled "seam".

**Honest fence — what is Lean vs interpretation.** Lean proves: `IsZero ↔ initial ∧ terminal`
(a definitional unfolding), and that the Hilbert bottom realizes it. The reading that this categorical
coincidence *is* "the diagonal fixed point" / the framework keystone — the μ and ν fixed-point
characterizations collapsing at one node — is the framework's interpretation, not an additional Lean
claim. The biconditional itself is a standard categorical fact (the definition of a zero object); the
content here is stating it as the seam's defining property and witnessing it at node #5.
-/

namespace ZeroParadox.ZPH_MC1_TC12

open CategoryTheory CategoryTheory.Limits

universe v u
variable {C : Type u} [Category.{v} C]

/-- An initial object has a unique morphism to every object. -/
@[reducible] def uniqueFromInitial {X : C} (hi : IsInitial X) (Y : C) : Unique (X ⟶ Y) where
  default := hi.to Y
  uniq f := hi.hom_ext f (hi.to Y)

/-- A terminal object has a unique morphism from every object. -/
@[reducible] def uniqueToTerminal {X : C} (ht : IsTerminal X) (Y : C) : Unique (Y ⟶ X) where
  default := ht.from Y
  uniq f := ht.hom_ext f (ht.from Y)

/-- **Reverse direction (definitional unfolding).** If `X` is both initial and terminal, then `X` is a
    zero object. This just repackages the two `Unique` families `IsZero` is defined from: initial gives
    the unique "out" family, terminal gives the unique "in" family. `IsZero` is by definition the
    conjunction of those two universal families, so this is a restatement, not new content. -/
theorem isZero_of_isInitial_isTerminal {X : C} (hi : IsInitial X) (ht : IsTerminal X) :
    IsZero X where
  unique_to Y := ⟨uniqueFromInitial hi Y⟩
  unique_from Y := ⟨uniqueToTerminal ht Y⟩

/-- **Seam property (general, definitional).** In any category, a zero object is *exactly* an object
    that is both initial and terminal — the point where the least-fixed-point (initial / μ) and
    greatest-fixed-point (terminal / ν) universal characterizations coincide. This is the `IsZero`
    definition restated; the forward direction is Mathlib's, the reverse is
    `isZero_of_isInitial_isTerminal`. -/
theorem isZero_iff_isInitial_and_isTerminal {X : C} :
    IsZero X ↔ Nonempty (IsInitial X) ∧ Nonempty (IsTerminal X) := by
  constructor
  · intro h
    exact ⟨⟨h.isInitial⟩, ⟨h.isTerminal⟩⟩
  · rintro ⟨⟨hi⟩, ⟨ht⟩⟩
    exact isZero_of_isInitial_isTerminal hi ht

/-- **Keystone at the seam node #5.** The Hilbert bottom `fD_functor.obj 0` is a zero object **iff**
    it is both initial and terminal (the general keystone, specialized), and both sides in fact hold
    (it *is* a zero object, by `ZPH_MC1_TreeSeam.hilbert_bottom_isZero`). So the seam is literally the
    μ=ν coincidence point. -/
theorem seam_is_mu_nu_coincidence :
    (IsZero (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0)
      ↔ Nonempty (IsInitial (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0))
        ∧ Nonempty (IsTerminal (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0)))
    ∧ IsZero (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0) :=
  ⟨isZero_iff_isInitial_and_isTerminal, ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero⟩

end ZeroParadox.ZPH_MC1_TC12

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC12

#print axioms isZero_of_isInitial_isTerminal
#print axioms isZero_iff_isInitial_and_isTerminal
#print axioms seam_is_mu_nu_coincidence

end PurityCheck
