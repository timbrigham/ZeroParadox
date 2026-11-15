-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.State.HilbFunctor
import ZeroParadox.Multihomed.TreeT1
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Axis III over the proof-theory floor #1 (the hom-set carrier convention)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`pointedness_dichotomy` proved the Axis-III (carrier-cardinality) dichotomy as a forced
binary for the two categories whose initial bottoms the framework instantiates with a **Type-valued
carrier**: `Type` (#4-style, `Fin 0` empty, card 0) and `ModuleCat ℂ` (#5-style, `StateSpace 0`
singleton, card ≤ 1). This file asks whether the **proof-theory floor #1** — `0 : ℕ` as the initial object
of the `ℕ` **preorder category** (`nat_floor_isInitial`, the base of the Goodstein/KP/Kruskal descent)
— extends that ledger or breaks it.

**The honest finding is a two-part split: the GO half is in the theorem statements, the carrier
dependence in the anonymous `example`s after `floor_has_no_forgetful_carrier`.**

### Thinness: #1's carrier is set by a choice of functor

`floor_has_no_forgetful_carrier` — the `ℕ` preorder category is **thin** (every hom-set is a
subsingleton: at most one morphism between any two objects). So every functor out of it is faithful,
and faithful functors to `Type` give `0 : ℕ` different carriers: `n ↦ Fin n` gives it an empty one
(card 0, #4's value) and the constant functor at `PUnit` a singleton (card 1, #5's value); the
first `example` after `floor_has_no_forgetful_carrier` builds both. So #1's carrier cardinality is not
read off the object: it is fixed only once a carrier convention is chosen.

### GO half: the hom-set carrier puts #1 at card 1

One convention that extends to a thin category is the **hom-set carrier**: for an initial object
`I`, the canonical set attached to `I` is its hom-set `I ⟶ Y` (the descent morphism set). For #1 this
is `(0 ⟶ n)`, which is **inhabited and a subsingleton**, hence a singleton (card exactly 1) for every
`n`:

- `floor_homset_card_one` — `Unique ((0 : ℕ) ⟶ n)`: #1's hom-set carrier is a singleton.
- `floor_homset_equiv_punit` — `((0 : ℕ) ⟶ n) ≃ PUnit`: card-1, equal to #5's pointed endpoint.
- `floor_homset_not_equiv_fin0` — `¬ Nonempty ((0 : ℕ) ⟶ n ≃ Fin 0)`: card-distinct from #4 (empty).

So under the hom-set carrier, #1 lands at the **pointed (card-1)** Axis-III endpoint:
card-indistinguishable from #5 and card-distinct from #4 — Axis III separates #1 from #4 the same way
it separates #5 from #4, and adds **no new cardinality value** (the {0,1} dichotomy survives).

### Capstone

`nat_floor_initial_singleton_homs` bundles thinness, the GO half and `IsInitial (0 : ℕ)`: the floor's category is thin; (GO) its
hom-set carrier is a singleton, card-equal to a point and card-distinct from `Fin 0`. The delta over
`ZeroParadox/Category/PointednessSharp.lean`: that file covered the two Type-carried endpoints; this
file adds #1 to the ledger under the hom-set convention, where it lands on an existing value of the
{0,1} dichotomy. Under the `Fin` functor it lands on the other value. The {0,1} placement holds for
these two conventions, not for every carrier choice: the constant functor at `Fin 2` is also faithful
and gives `0 : ℕ` a two-element carrier, and a constant functor gives it any carrier at all (the
second `example` after `floor_has_no_forgetful_carrier`).

**Honest fence — Lean vs interpretation.** The Lean content is exactly: (a) the `ℕ` preorder hom-sets
are subsingletons (thinness); (b) `(0 ⟶ n)` is a singleton for all `n`; (c) it is `PUnit`-equivalent
and not `Fin 0`-equivalent. That this *is* the canonically right carrier for a thin bottom (rather
than a fix-up that rescues the dichotomy by fiat) is the framework's reading: the Lean proves the
hom-set is card 1, not that the hom-set is the unique legitimate carrier: the `Fin` functor is another
faithful choice and gives card 0. The GO half is the Axis-III reading under the hom-set convention.
-/

namespace ZeroParadox

open CategoryTheory
open ZeroParadox ZeroParadox ZeroParadox

/-! ## Thinness: the proof-theory floor lives in a thin category -/

/-- `Statement:` the `ℕ` preorder category is **thin**: every hom-set is a subsingleton (at most one
    morphism between any two objects). Thinness only; it does not say the floor `0 : ℕ` lacks a
    carrier (the two `example`s below). -/
theorem floor_has_no_forgetful_carrier (x y : ℕ) : Subsingleton (x ⟶ y) :=
  ⟨fun a b => Subsingleton.elim a b⟩

-- `Statement:` so every functor `ℕ ⥤ Type` is faithful, and two such functors give `0 : ℕ` an empty
-- carrier (`n ↦ Fin n`, card 0) and a singleton carrier (constant `PUnit`, card 1).
example : (∃ F : ℕ ⥤ Type, F.Faithful ∧ IsEmpty (F.obj 0)) ∧
    (∃ F : ℕ ⥤ Type, F.Faithful ∧ Nonempty (Unique (F.obj 0))) :=
  ⟨⟨{ obj := fun n => Fin n, map := fun f => TypeCat.ofHom (Fin.castLE (leOfHom f)) },
      ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩, by exact inferInstanceAs (IsEmpty (Fin 0))⟩,
    ⟨(Functor.const ℕ).obj PUnit, ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩,
      ⟨by exact inferInstanceAs (Unique PUnit)⟩⟩⟩

-- `Statement:` for every type `T`, the constant functor at `T` is faithful and gives `0 : ℕ` the
-- carrier `T`; at `T = Fin 2` that carrier has two elements.
example (T : Type) : ∃ F : ℕ ⥤ Type, F.Faithful ∧ Nonempty (F.obj 0 ≃ T) :=
  ⟨(Functor.const ℕ).obj T, ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩, ⟨Equiv.refl _⟩⟩

/-! ## GO half: the hom-set carrier of #1 is a singleton (card 1, pointed endpoint) -/

/-- The hom-set carrier of the floor: `(0 ⟶ n)` is a **singleton** for every `n`. Inhabited (the
    descent morphism `homOfLE (Nat.zero_le n)`, the floor's universal "least → level n") and a
    subsingleton (thinness), hence card exactly 1. This is the thin-category carrier of the initial
    object #1. -/
instance floor_homset_card_one (n : ℕ) : Unique ((0 : ℕ) ⟶ n) where
  default := homOfLE (Nat.zero_le n)
  uniq := fun _ => Subsingleton.elim _ _

/-- **GO, card-equal to #5.** The floor's hom-set carrier `(0 ⟶ n)` is in bijection with `PUnit`
    (card exactly 1): #1 lands at the *pointed* Axis-III endpoint, the same cardinality class as the
    Hilbert bottom #5's singleton carrier. -/
noncomputable def floor_homset_equiv_punit (n : ℕ) : ((0 : ℕ) ⟶ n) ≃ PUnit :=
  Equiv.equivPUnit _

/-- **GO, card-distinct from #4.** The floor's hom-set carrier `(0 ⟶ n)` (a singleton) is **not** in
    bijection with `Fin 0` (the empty carrier of the Kleisli bottom #4): Axis III separates #1 from #4
    exactly as it separates #5 from #4. -/
theorem floor_homset_not_equiv_fin0 (n : ℕ) :
    ¬ Nonempty (((0 : ℕ) ⟶ n) ≃ Fin 0) := by
  rintro ⟨e⟩
  exact (e default).elim0

/-! ## Capstone: #1 under the hom-set convention -/

/-- **capstone — Axis III over the proof-theory floor #1: the GO half in-statement, the carrier
    dependence in the `example`s after `floor_has_no_forgetful_carrier`.**

    1. **Thin** — `∀ x y, Subsingleton (x ⟶ y)`: the floor's category is thin, so every functor to
       `Type` is faithful and #1's carrier depends on which one is chosen (the two `example`s after
       `floor_has_no_forgetful_carrier`).
    2. **GO, card 1** — `Unique (0 ⟶ n)`: under the hom-set carrier convention, #1's carrier is a
       singleton.
    3. **GO, = #5** — `(0 ⟶ n) ≃ PUnit`: card-equal to the pointed (card-1) endpoint.
    4. **GO, ≠ #4** — `¬ Nonempty ((0 ⟶ n) ≃ Fin 0)`: card-distinct from the empty bottom.

    Together: under the hom-set carrier convention, #1 joins the Axis-III ledger at the existing
    pointed endpoint and introduces **no new cardinality value** — the {0,1} pointedness dichotomy of
    `ZeroParadox/Category/PointednessSharp.lean` survives the addition of the proof-theory floor. The floor
    `0 : ℕ` is the genuine initial object of its category (`nat_floor_isInitial`), so this is the
    Axis-III reading of a real μ-bottom, not a contrived element. -/
theorem nat_floor_initial_singleton_homs :
    (∀ x y : ℕ, Subsingleton (x ⟶ y)) ∧
    (∀ n : ℕ, Nonempty (Unique ((0 : ℕ) ⟶ n))) ∧
    (∀ n : ℕ, Nonempty (((0 : ℕ) ⟶ n) ≃ PUnit)) ∧
    (∀ n : ℕ, ¬ Nonempty (((0 : ℕ) ⟶ n) ≃ Fin 0)) ∧
    Nonempty (Limits.IsInitial (0 : ℕ)) :=
  ⟨floor_has_no_forgetful_carrier,
   fun n => ⟨floor_homset_card_one n⟩,
   fun n => ⟨floor_homset_equiv_punit n⟩,
   floor_homset_not_equiv_fin0,
   ⟨nat_floor_isInitial⟩⟩

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `CategoryTheory` / preorder-category / `Equiv`
libraries — a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox

#print axioms floor_has_no_forgetful_carrier
#print axioms floor_homset_card_one
#print axioms floor_homset_equiv_punit
#print axioms floor_homset_not_equiv_fin0
#print axioms nat_floor_initial_singleton_homs

end PurityCheck
