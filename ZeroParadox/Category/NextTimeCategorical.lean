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

## Formal Overview (AI-assisted)

`ZeroParadox/Category/WellFoundedCoalgebra.lean` states well-foundedness over `Set X` with a concrete
`nextTime`. Adámek-Milius-Moss state it over `Sub(A)` in a **category**. This file builds their version
and proves the two agree, so the concrete predicate is no longer merely *shaped like* theirs.

**PRIOR ART — locators, not quotations** (the transcription lesson from
`ZeroParadox/Computability/GroundZero.lean` § V; see `CLAUDE.md` § "the pointer must not become a
COPY"). Source: `.claude-local/papers/adamek_milius_moss_wellfounded_recursive_coalgebras.pdf`.

| AMM | what is there | built here as |
|---|---|---|
| **Def 4.1, p. 14** | the next time operator `⃝(s) = α⁻¹(F s)` on `Sub(A)` | `nextTimeCat` |
| **Def 4.3, p. 15** | well-founded = `id_A` is the only fixed point of `⃝` | `IsWellFoundedCoalgCat` |
| **Def 4.7, p. 16** | the canonical graph (cited for orientation, not used here) | — |

**The delta is the formalization and the bridge.** AMM's definitions are theirs; what is added is that
they are now Lean objects, that `nextTimeCat` is stated at **full generality** (any category with
pullbacks, any mono-preserving endofunctor), and that `isWellFoundedCoalgCat_iff` proves the categorical
and concrete predicates equivalent for polynomial functors on `Type u`.

**⚠ THE TECHNIQUE, because the obvious route does not work.** Mathlib's
`Types.subobjectEquivSet : Subobject α ≃o Set α` is built from `Equivalence.thinSkeletonOrderIso`, which
selects representatives out of a quotient — it is `noncomputable` and **nothing reduces through it**;
`subobjectEquivSet X (Subobject.mk i) = Set.range i` is neither `rfl` nor `simp`, and Mathlib supplies
no computation lemmas for it. The route taken instead: `Subobject X` **is** `ThinSkeleton (MonoOver X)`,
a plain `Quotient`, so descend with `Quotient.lift` directly, taking well-definedness from the fact that
**`Set X` is a partial order, where an isomorphism simply is an equality**. That makes `toSet_mk` hold
by `rfl` and everything downstream follows.

**⚠ `toSet` IS NOT CLAIMED TO BE `subobjectEquivSet`.** They are built from the same functor and ought to
agree, and **that agreement is not proved here and is not needed**: the bridge uses only the properties
established below (`toSet_injective`, `toSet_surjective`, `toSet_eq_univ_iff`, `le_of_toSet_le`). Do not
assert the two are the same function without proving it.

## Structure

- § I   `monoOverPost` / `subobjectPost` — a mono-preserving functor's action on subobjects, which
        Mathlib does not provide (`Subobject.map` is along a *mono*, not a functor).
- § II  `nextTimeCat`, `IsWellFoundedCoalgCat` — AMM Def 4.1 and 4.3, general.
- § III `toSet` and its properties — the computable descent to `Set X`.
- § IV  `toSet_nextTimeCat` and `isWellFoundedCoalgCat_iff` — the bridge.
-/

namespace ZeroParadox

open CategoryTheory CategoryTheory.Limits

universe v u

/-! ### § I. A mono-preserving functor's action on subobjects -/

section General
variable {C : Type u} [Category.{v} C] (F : C ⥤ C) [F.PreservesMonomorphisms]

/-- **A mono-preserving functor acts on `MonoOver`.** Built in Mathlib's own idiom — `Over.post`
composed through `MonoOver.lift` — exactly the shape of Mathlib's `MonoOver.map`. -/
def monoOverPost (X : C) : MonoOver X ⥤ MonoOver (F.obj X) :=
  MonoOver.lift (Over.post F) (fun f => by
    have : Mono f.arrow := f.mono
    exact F.map_mono f.arrow)

/-- **Hence on `Subobject`.** ⚠ Mathlib has no such construction: `Subobject.map` is along a **mono**,
`Subobject.pullback` is along a morphism contravariantly, and neither is a functor's action. -/
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
image**". ⚠ Injectivity of `i` is **not** needed — the linter confirmed it unused. -/
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

/-- **`Statement:` BRIDGE 1 — the concrete predicate IS AMM Def 4.3.** For a polynomial functor on
`Type u`, `IsWellFoundedCoalg` and the categorical `IsWellFoundedCoalgCat` are equivalent.

**What this does and does not license.** It closes the *predicate transport*, so results stated with
`IsWellFoundedCoalg` are results about AMM's notion. It does **not** formalize AMM Thm 7.6, and does
not by itself earn every instance-of claim — see
`ZeroParadox/Category/WellFoundedCoalgebra.lean`'s overview, where smoothness clause (b) is the other
open item. -/
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

**Measured 2026-08-05, and the headline is that the proofs are not the reason.**

**`CategoryTheory.Subobject` — the TYPE — carries `Classical.choice`, and so does `MonoOver`:**
```
CategoryTheory.Subobject          [propext, Classical.choice, Quot.sound]   <- the TYPE
CategoryTheory.MonoOver           [propext, Classical.choice, Quot.sound]   <- the TYPE
Subobject.mk / .arrow / .pullback / .lower   all the same
```
`#print axioms` follows the **statement**, so **every result in this file mentioning `Subobject` is
choice-carrying no matter how it is proved.** Per `CLAUDE.md` § *Revalidate, don't redraft*: a type
carrying an axiom makes "removable" false for every possible proof. This is a fact about Mathlib's
subobject machinery, not about anything here.

**Two proofs do additionally make genuine selections** — `mem_range_pfunctor_map`'s reverse direction
picks a preimage per child, and `le_of_toSet_le` picks a factoring witness per element. Both are real
`.choose` uses on existence statements. ⚠ **But do not present those as the source of the footprint** —
the type already settled it, and the one declaration here whose statement avoids `Subobject`
(`ofTypeFunctor_pfunctor_map`) measures `[propext, Quot.sound]`, which is the control showing the
difference.

⚠ **Nothing is claimed removable.** That is a modal claim needing an exhibited clean proof or a
reduction, and for anything mentioning `Subobject` it is in fact **false**, by the type. -/

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
