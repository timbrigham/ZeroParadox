-- EXPERIMENTAL (branch scaffolding): the categorical form of the next-time operator, and the bridge
-- to the concrete one. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean
-- and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Category.WellFoundedCoalgebra
import Mathlib.CategoryTheory.Subobject.Types
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The next-time operator, categorically — and the bridge to the concrete one

## Engineer's Take

While working through the span question with my AI assistant, I asked whether this is one of those
meta level cases where these are the requirements we need to meet, and the commonly named version of
those requirements already exists somewhere. It did. When the category list came back, three of the
four lines sounded really damn familiar.

The question after that was whether to name the bridges or build them. Then whether bridge one was
buildable at all. And before spending anything on it, what elevating this to an instance actually buys
us, especially on the information theory side. That last one is worth keeping in view: the honest
answer at the time was that it buys a citation and not new mathematics.

We built it anyway, because knowing whether the requirements are met is worth having settled rather
than left open. I defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview
Adámek–Milius–Moss Def 4.1 and 4.3 built at full generality, plus `isWellFoundedCoalgCat_iff`, which
proves the categorical and concrete predicates equivalent for polynomial functors on `Type u`. ⚠ AMM
are not the origin of either definition. Locators, credit chain and technique: `ZeroParadox/Category/NextTimeCategorical.md`.
-/

namespace ZeroParadox

open CategoryTheory CategoryTheory.Limits

universe v u

/-! ### § I. A mono-preserving functor's action on subobjects -/

section General
variable {C : Type u} [Category.{v} C] (F : C ⥤ C) [F.PreservesMonomorphisms]

/-- **A mono-preserving functor acts on `MonoOver`.**

**Closest prior art — Mathlib has this for EQUIVALENCES.** `MonoOver.congr (e : C ≌ D) : MonoOver X ≌
MonoOver (e.functor.obj X)` (`Mathlib/CategoryTheory/Subobject/MonoOver.lean`) has functor field
literally `lift (Over.post e.functor)` — the same construction, character for character. **The delta is
the hypothesis:** an equivalence preserves monomorphisms automatically, so `congr` never needs to
assume it; this asks only `[F.PreservesMonomorphisms]` and gives a functor rather than an equivalence. -/
def monoOverPost (X : C) : MonoOver X ⥤ MonoOver (F.obj X) :=
  MonoOver.lift (Over.post F) (fun f => by
    have : Mono f.arrow := f.mono
    exact F.map_mono f.arrow)

/-- **Hence on `Subobject`.** ⚠ Not located in Mathlib as of 2026-08-05. All **three** of its
`Subobject X ⥤ Subobject Y` functors are along a *morphism*, not a functor: `Subobject.map` (along a
**mono**), `Subobject.pullback` (contravariantly along any morphism), and `Subobject.«exists»` (the
direct image, needing `HasImages`). Structural corroboration rather than a bare grep:
**`PreservesMonomorphisms` appears nowhere in `Mathlib/CategoryTheory/Subobject/`** — the subobject
development never takes that hypothesis at all. -/
def subobjectPost (X : C) : Subobject X ⥤ Subobject (F.obj X) :=
  Subobject.lower (monoOverPost F X)

/-- `Statement:` it computes on `Subobject.mk` — by `rfl`, because `Subobject.lower` is
`ThinSkeleton.map`, a plain `Quotient.map`. -/
theorem subobjectPost_mk {X A : C} (i : A ⟶ X) [Mono i] :
    (subobjectPost F X).obj (Subobject.mk i) = Subobject.mk (F.map i) := rfl

/-! ### § II. AMM Def 4.1 and 4.3, at full generality -/

/-- **AMM Def 4.1 — the next time operator, categorically.** `⃝(s) = α⁻¹(F s)`: push the subobject
through `F`, then pull back along the coalgebra structure map. Stated for **any** category with
pullbacks and **any** mono-preserving endofunctor. -/
noncomputable def nextTimeCat [HasPullbacks C] {X : C} (α : X ⟶ F.obj X) :
    Subobject X ⥤ Subobject X :=
  subobjectPost F X ⋙ Subobject.pullback α

/-- **AMM Def 4.3, categorically** — the only fixed point of next time is the whole object. AMM write
"`id_A` is the only fixed point"; `id_A` as a subobject is `⊤`. -/
def IsWellFoundedCoalgCat [HasPullbacks C] {X : C} (α : X ⟶ F.obj X) : Prop :=
  ∀ s : Subobject X, (nextTimeCat F α).obj s = s → s = ⊤

end General

/-! ### § III. The computable descent `Subobject X → Set X` -/

section Types
variable {X : Type u}

/-- Isomorphic monos have the same image, **because `Set X` is a partial order**: push the iso through
Mathlib's own `monoOverEquivalenceSet` functor and read it off by antisymmetry. This is what makes the
`Quotient.lift` below well-defined without touching the noncomputable order iso. -/
theorem range_eq_of_monoOver_iso {m n : MonoOver X} (e : m ≅ n) :
    (Types.monoOverEquivalenceSet X).functor.obj m
      = (Types.monoOverEquivalenceSet X).functor.obj n :=
  le_antisymm (leOfHom ((Types.monoOverEquivalenceSet X).functor.mapIso e).hom)
    (leOfHom ((Types.monoOverEquivalenceSet X).functor.mapIso e).inv)

/-- **The computable descent.** See the overview's technique note for why this exists rather than
`Types.subobjectEquivSet`, and for the fence on claiming the two are the same function. -/
def toSet : Subobject X → Set X :=
  Quotient.lift (fun m : MonoOver X => (Types.monoOverEquivalenceSet X).functor.obj m)
    (fun _ _ ⟨e⟩ => range_eq_of_monoOver_iso e)

/-- `Statement:` **it computes** — by `rfl`. This is the fact the noncomputable iso could not supply,
and everything downstream rests on it. -/
theorem toSet_mk {A : Type u} (i : A ⟶ X) [Mono i] :
    toSet (Subobject.mk i) = Set.range (ConcreteCategory.hom i) := rfl

theorem toSet_eq_range_arrow (s : Subobject X) :
    toSet s = Set.range (ConcreteCategory.hom s.arrow) := by
  conv_lhs => rw [← Subobject.mk_arrow s]
  exact toSet_mk s.arrow

/-- `Statement:` **pullback is preimage.** AMM's `α⁻¹(−)` computes to the set-theoretic preimage. -/
theorem toSet_pullback {Y : Type u} (α : X ⟶ Y) (t : Subobject Y) :
    toSet ((Subobject.pullback α).obj t) = (ConcreteCategory.hom α) ⁻¹' toSet t := by
  rw [Subobject.pullback_obj, toSet_mk, toSet_eq_range_arrow]
  exact Types.range_pullbackSnd t.arrow α

/-- `Statement:` **the functor acts by image.** -/
theorem toSet_subobjectPost (F : Type u ⥤ Type u) [F.PreservesMonomorphisms] (s : Subobject X) :
    toSet ((subobjectPost F X).obj s) = Set.range (ConcreteCategory.hom (F.map s.arrow)) := by
  conv_lhs => rw [← Subobject.mk_arrow s]
  rw [subobjectPost_mk, toSet_mk]

/-- `Statement:` the image of a polynomial functor's action is exactly "**every child lands in the
image**". ⚠ Injectivity of `i` is **not** needed — read the signature: there is no such hypothesis. -/
theorem mem_range_pfunctor_map {P : PFunctor.{u, u}} {A : Type u} (i : A → X) (z : P.Obj X) :
    z ∈ Set.range (P.map i) ↔ ∀ b, z.2 b ∈ Set.range i := by
  obtain ⟨a, g⟩ := z
  constructor
  · rintro ⟨⟨a', h⟩, heq⟩ b
    rw [PFunctor.map_eq] at heq
    cases heq
    exact ⟨h b, rfl⟩
  · intro hg
    refine ⟨⟨a, fun b => (hg b).choose⟩, ?_⟩
    rw [PFunctor.map_eq]
    congr 1
    funext b
    exact (hg b).choose_spec

/-- The `ofTypeFunctor` coercion round-trip, isolated so the bridge's rewrite chain stays readable. -/
theorem ofTypeFunctor_pfunctor_map (P : PFunctor.{u, u}) {A : Type u} (i : A ⟶ X) :
    ⇑(ConcreteCategory.hom ((ofTypeFunctor P.Obj).map i)) = P.map ⇑(ConcreteCategory.hom i) := rfl

/-- `Statement:` `toSet` sends `⊤` to `Set.univ`, and **only** `⊤` — a mono with full image is
surjective, hence bijective, hence an isomorphism. -/
theorem toSet_eq_univ_iff (s : Subobject X) : toSet s = Set.univ ↔ s = ⊤ := by
  rw [toSet_eq_range_arrow, Set.range_eq_univ, ← Subobject.isIso_arrow_iff_eq_top,
    isIso_iff_bijective]
  exact ⟨fun h => ⟨(mono_iff_injective s.arrow).mp inferInstance, h⟩, fun h => h.2⟩

/-- `Statement:` every set arises from a subobject. -/
theorem toSet_surjective (S : Set X) : ∃ s : Subobject X, toSet s = S := by
  haveI := subtype_val_mono S
  exact ⟨Subobject.mk (TypeCat.ofHom (Subtype.val : S → X)), by
    rw [toSet_mk]; exact Subtype.range_val⟩

/-- `Statement:` image containment gives `≤` — a mono whose image sits inside another's factors
through it. -/
theorem le_of_toSet_le {s t : Subobject X} (h : toSet s ≤ toSet t) : s ≤ t := by
  rw [toSet_eq_range_arrow, toSet_eq_range_arrow] at h
  refine Subobject.le_of_comm (TypeCat.ofHom (fun a => (h ⟨a, rfl⟩).choose)) ?_
  ext a
  exact (h ⟨a, rfl⟩).choose_spec

/-- `Statement:` hence `toSet` is injective. -/
theorem toSet_injective : Function.Injective (toSet (X := X)) := fun _ _ h =>
  le_antisymm (le_of_toSet_le (le_of_eq h)) (le_of_toSet_le (le_of_eq h.symm))

/-! ### § IV. The bridge -/

/-- **`Statement:` THE OPERATORS CORRESPOND.** AMM's categorical next-time operator computes, under
`toSet`, to this corpus's concrete `nextTime`. -/
theorem toSet_nextTimeCat (P : PFunctor.{u, u}) (α : X ⟶ (ofTypeFunctor P.Obj).obj X)
    (s : Subobject X) :
    toSet ((nextTimeCat (ofTypeFunctor P.Obj) α).obj s)
      = nextTime (P := P) (ConcreteCategory.hom α) (toSet s) := by
  show toSet ((Subobject.pullback α).obj ((subobjectPost _ X).obj s)) = _
  rw [toSet_pullback, toSet_subobjectPost, ofTypeFunctor_pfunctor_map]
  ext x
  simp only [Set.mem_preimage, nextTime, Set.mem_setOf_eq, toSet_eq_range_arrow]
  exact mem_range_pfunctor_map _ _

/-- **`Statement:` BRIDGE 1.** For a polynomial functor on `Type u`, `IsWellFoundedCoalg` and the
categorical `IsWellFoundedCoalgCat` are **equivalent** — that, and only that, is what the theorem says.

`Reading:` the framework reads this as "the concrete predicate **is** AMM Def 4.3". That step is a
judgement about whether `IsWellFoundedCoalgCat` transcribes their Def 4.3 faithfully, which no Lean
statement can carry; the locator table in the overview is the evidence for it.

**What this does and does not license.** It closes the *predicate transport*, so results stated with
`IsWellFoundedCoalg` are results about AMM's notion. It does **not** formalize AMM Thm 7.6, and does
not by itself earn every instance-of claim: AMM's
ambient hypotheses are discharged separately (all four, smoothness clause (b) included), and that
discharge is what the instance-of claim would additionally require. -/
theorem isWellFoundedCoalgCat_iff (P : PFunctor.{u, u})
    (α : X ⟶ (ofTypeFunctor P.Obj).obj X) :
    IsWellFoundedCoalgCat (ofTypeFunctor P.Obj) α
      ↔ IsWellFoundedCoalg (P := P) (ConcreteCategory.hom α) := by
  constructor
  · intro hcat S hS
    obtain ⟨s, rfl⟩ := toSet_surjective S
    exact (toSet_eq_univ_iff s).mpr (hcat s (toSet_injective (by rw [toSet_nextTimeCat, hS])))
  · intro hset s hs
    rw [← toSet_eq_univ_iff]
    exact hset _ (by rw [← toSet_nextTimeCat, hs])

end Types

end ZeroParadox

/-! ## Axiom Purity Check

`CategoryTheory.Subobject` and `MonoOver` carry `Classical.choice` **in the TYPE**, so every result
below mentioning them is choice-carrying no matter how it is proved, and nothing is claimed removable.
⚠ Subobject-freedom is necessary but NOT sufficient — `mem_range_pfunctor_map` selects with `.choose`
independently. Measured footprints and the control pair: `ZeroParadox/Category/NextTimeCategorical.md`. -/

section PurityCheck
open ZeroParadox

#print axioms ZeroParadox.monoOverPost
#print axioms ZeroParadox.subobjectPost
#print axioms ZeroParadox.subobjectPost_mk
#print axioms ZeroParadox.nextTimeCat
#print axioms ZeroParadox.IsWellFoundedCoalgCat
#print axioms ZeroParadox.range_eq_of_monoOver_iso
#print axioms ZeroParadox.toSet
#print axioms ZeroParadox.toSet_mk
#print axioms ZeroParadox.toSet_eq_range_arrow
#print axioms ZeroParadox.toSet_pullback
#print axioms ZeroParadox.toSet_subobjectPost
#print axioms ZeroParadox.mem_range_pfunctor_map
#print axioms ZeroParadox.ofTypeFunctor_pfunctor_map
#print axioms ZeroParadox.toSet_eq_univ_iff
#print axioms ZeroParadox.toSet_surjective
#print axioms ZeroParadox.le_of_toSet_le
#print axioms ZeroParadox.toSet_injective
#print axioms ZeroParadox.toSet_nextTimeCat
#print axioms ZeroParadox.isWellFoundedCoalgCat_iff

end PurityCheck
