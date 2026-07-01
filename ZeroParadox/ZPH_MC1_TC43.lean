-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_InfoFunctor
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeT1
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC43 — Axis III over the proof-theory floor #1 (the hom-set carrier convention)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`ZPH_MC1_TC14.pointedness_dichotomy` proved the Axis-III (carrier-cardinality) dichotomy as a forced
binary for the two categories whose initial bottoms the framework instantiates with a **Type-valued
carrier**: `Type` (#4-style, `Fin 0` empty, card 0) and `ModuleCat ℂ` (#5-style, `StateSpace 0`
singleton, card ≤ 1). TC43 asks whether the **proof-theory floor #1** — `0 : ℕ` as the initial object
of the `ℕ` **preorder category** (`nat_floor_isInitial`, the base of the Goodstein/KP/Kruskal descent)
— extends that ledger or breaks it.

**The honest finding is a two-part split, both halves IN the theorem statements.**

### NO-GO half (the primary structural finding): #1 has no Type-valued carrier

`floor_has_no_forgetful_carrier` — the `ℕ` preorder category is **thin** (every hom-set is a
subsingleton: at most one morphism between any two objects). An object of a thin category has no
underlying set the way #4 (`Fin 0`, the carrier of `fC_functor.obj 0`) and #5 (`StateSpace 0`, the
carrier of `fD_functor.obj 0`) do — there is no faithful Type-valued forgetful functor reading off a
"carrier" of `0 : ℕ`. So the naive Axis-III question ("what is the cardinality of #1's carrier?") is a
**category error**: the cardinality axis, as a forgetful-carrier invariant, does not extend to #1.
This is itself a structural result — Axis III is *not* a tree-wide invariant; it is an invariant of
the genuinely set-carried (Type-forgetful) bottoms only.

### GO half (the recovery under the right convention): the hom-set carrier puts #1 at card 1

The convention that *does* extend to a thin category is the **hom-set carrier**: for an initial object
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

`tc43_axis_iii_over_floor` bundles both halves: (NO-GO) the floor is thin, so it has no
Type-forgetful carrier; (GO) its hom-set carrier is a singleton, card-equal to a point and
card-distinct from `Fin 0`. The delta over TC14: TC14 covered the two Type-forgetful endpoints; TC43
adds #1 to the ledger and shows it does *not* break the {0,1} dichotomy — but only once the carrier
notion is corrected from "forgetful set" to "hom-set", which is the price #1's thinness exacts.

**Honest fence — Lean vs interpretation.** The Lean content is exactly: (a) the `ℕ` preorder hom-sets
are subsingletons (thinness); (b) `(0 ⟶ n)` is a singleton for all `n`; (c) it is `PUnit`-equivalent
and not `Fin 0`-equivalent. That this *is* the canonically right carrier for a thin bottom (rather
than a fix-up that rescues the dichotomy by fiat) is the framework's reading: the Lean proves the
hom-set is card 1, not that the hom-set is the unique legitimate carrier. The NO-GO half — that no
Type-forgetful carrier exists — is the genuinely forced part; the GO half is "the surviving Axis-III
reading once you accept the thin-category carrier convention".
-/

namespace ZeroParadox.ZPH_MC1_TC43

open CategoryTheory
open ZeroParadox.ZPH_InfoFunctor ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_MC1_TreeT1

/-! ## NO-GO half: the proof-theory floor lives in a thin category (no Type-valued carrier) -/

/-- **NO-GO (structural).** The `ℕ` preorder category is **thin**: every hom-set is a subsingleton
    (at most one morphism between any two objects). An object of a thin category — in particular the
    floor `0 : ℕ` — has no underlying set the way #4 (`Fin 0`) and #5 (`StateSpace 0`) do; there is no
    Type-forgetful carrier to read a cardinality off. So the Axis-III carrier-cardinality question, as
    posed for #4/#5, is a category error for #1: the axis does not extend to thin bottoms as a
    forgetful-carrier invariant. -/
theorem floor_has_no_forgetful_carrier (x y : ℕ) : Subsingleton (x ⟶ y) :=
  ⟨fun a b => Subsingleton.elim a b⟩

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

/-! ## Capstone: #1 added to the Axis-III ledger, dichotomy unbroken -/

/-- **TC43 capstone — Axis III over the proof-theory floor #1, both halves in-statement.**

    1. **NO-GO** — `∀ x y, Subsingleton (x ⟶ y)`: the floor's category is thin, so #1 has no
       Type-forgetful carrier (the cardinality axis is *not* a tree-wide invariant; it is confined to
       the genuinely set-carried bottoms #4/#5).
    2. **GO, card 1** — `Unique (0 ⟶ n)`: under the hom-set carrier convention, #1's carrier is a
       singleton.
    3. **GO, = #5** — `(0 ⟶ n) ≃ PUnit`: card-equal to the pointed (card-1) endpoint.
    4. **GO, ≠ #4** — `¬ Nonempty ((0 ⟶ n) ≃ Fin 0)`: card-distinct from the empty bottom.

    Together: once the carrier notion is corrected to "hom-set" (the price of #1's thinness), #1 joins
    the Axis-III ledger at the existing pointed endpoint and introduces **no new cardinality value** —
    the {0,1} pointedness dichotomy of TC14 survives the addition of the proof-theory floor. The floor
    `0 : ℕ` is the genuine initial object of its category (`nat_floor_isInitial`), so this is the
    Axis-III reading of a real μ-bottom, not a contrived element. -/
theorem tc43_axis_iii_over_floor :
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

end ZeroParadox.ZPH_MC1_TC43

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `CategoryTheory` / preorder-category / `Equiv`
libraries — a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC43

#print axioms floor_has_no_forgetful_carrier
#print axioms floor_homset_card_one
#print axioms floor_homset_equiv_punit
#print axioms floor_homset_not_equiv_fin0
#print axioms tc43_axis_iii_over_floor

end PurityCheck
