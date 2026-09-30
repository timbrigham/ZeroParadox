import ZeroParadox.Category.Category
import ZeroParadox.Order.Lattice

/-!
# B4 (pipeline): AX-G2 is derivable from strict-initiality (a ZP-G posit collapses)

`ax_g2_from_strict_initial`: if every morphism into `zero` is an isomorphism (strict initiality,
Carboni–Lack–Walters), the AX-G2 shape `IsEmpty (X ≅ zero) → IsEmpty (X ⟶ zero)` follows, with no
further hypothesis. The converse needs `zero` initial; it is the `example` below, not a declaration, and
a named scratch copy of the same proof measured `[propext, Classical.choice, Quot.sound]` (2026-09-29).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

open CategoryTheory

/-- **AX-G2 from strict-initiality (B4).** If `zero` is strict initial — every morphism into it is an iso
    (Carboni–Lack–Walters) — then the AX-G2 source-asymmetry shape holds: no morphism into `zero` from an
    object not isomorphic to it. Reduces a posited ZP-G axiom to a recognized categorical notion. -/
theorem ax_g2_from_strict_initial {C : Type*} [Category C] (zero : C)
    (hstrict : ∀ (X : C) (f : X ⟶ zero), IsIso f) (X : C)
    (hne : IsEmpty (X ≅ zero)) : IsEmpty (X ⟶ zero) := by
  constructor
  intro f
  haveI := hstrict X f
  exact hne.false (asIso f)

-- `Statement:` the converse, given initiality: AX-G2 at an initial `zero` makes every morphism into
-- `zero` an isomorphism. With the theorem above, the two are equivalent at an initial object.
-- Folklore: nLab (*strict initial object*) states strictness in AX-G2's form. Mathlib's neighbouring
-- `IsInitial.ofStrict` (`Mathlib/CategoryTheory/Limits/Shapes/StrictInitial.lean`): a morphism into a
-- strict initial object makes its source initial.
example {C : Type*} [Category C] (zero : C) (hi : Limits.IsInitial zero)
    (hg2 : ∀ X : C, IsEmpty (X ≅ zero) → IsEmpty (X ⟶ zero)) (X : C) (f : X ⟶ zero) : IsIso f := by
  classical
  by_cases h : Nonempty (X ≅ zero)
  · obtain ⟨e⟩ := h
    obtain rfl : f = e.hom := (hi.ofIso e.symm).hom_ext _ _
    infer_instance
  · exact ((hg2 X ⟨fun e => h ⟨e⟩⟩).false f).elim

-- `Statement:` AX-G2 from antisymmetry: in the poset category of any partial order with a least
-- element, nothing not isomorphic to `⊥` has a morphism into it (a morphism `X ⟶ ⊥` is `X ≤ ⊥`, so
-- `X = ⊥`). nLab (*strict initial object*) lists posets among the categories with strict initials.
example (α : Type) [PartialOrder α] [OrderBot α] :
    ∀ X : α, IsEmpty (X ≅ (⊥ : α)) → IsEmpty (X ⟶ (⊥ : α)) := by
  intro X hX
  refine ⟨fun f => hX.false ?_⟩
  have h1 : X ≤ ⊥ := leOfHom f
  have : X = ⊥ := le_antisymm h1 bot_le
  subst this
  exact Iso.refl _

-- `Statement:` the same fact in ZP-A's own vocabulary: on any `ZPSemilattice`, an element below `bot`
-- is `bot` (antisymmetry with T2, `bot_le`).
example (L : Type) [ZPSemilattice L] (x : L) (hx : ZPSemilattice.le x ZPSemilattice.bot) :
    x = (ZPSemilattice.bot : L) :=
  ZPSemilattice.le_antisymm hx (ZPSemilattice.bot_le x)

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms ax_g2_from_strict_initial
end PurityCheck
