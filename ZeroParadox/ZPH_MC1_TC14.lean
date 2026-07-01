-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_InfoFunctor
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC14 — the pointedness dichotomy SHARPENED (the gap TC09 left open)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`ZPH_MC1_TC09.axis_iii_is_pointedness` asserted that across the framework's initial bottoms only
carrier-cardinalities 0 and 1 arise, governed by a single binary distinction (whether the category
forces a distinguished point — a zero object). But TC09 only **witnessed the two endpoints**
(`PEmpty`/`Fin 0` empty, `PUnit`/`StateSpace 0` singleton). It did **not** prove the *closure* claim
in its own docstring — "no initial object has a carrier of cardinality ≥ 2" — quantified over *all*
initial objects. That gap is exactly the apparatus-discipline failure mode: a heuristic stated in
prose, exemplified at two points, but never proved as a universal.

**This file closes the gap by proving both halves of the dichotomy as universals**, each quantified
over every initial object of the relevant category — not over a single named witness.

### The pointed half (GO, load-bearing closure)

`pointed_initial_carrier_subsingleton` — **in `ModuleCat ℂ`, EVERY initial object has a subsingleton
carrier (card ≤ 1).** Quantified over all `Z : ModuleCat ℂ` with `IsInitial Z`. The proof is the
load-bearing step TC09 skipped: an initial object is iso to the zero object
(`IsZero.isoIsInitial`), the zero object's carrier is a subsingleton
(`ModuleCat.subsingleton_of_isZero`), and the carrier subsingleton transfers across the iso
(`ModuleCat.toLinearEquiv`). So nothing of carrier-cardinality ≥ 2 can be initial here — the upper
endpoint of the dichotomy is *forced*, not merely sampled.

This is strictly stronger than `fD_zero_isInitial` / TC09's `module_initial_card1`, which only
exhibit one initial object that happens to be a singleton. Here the bound holds for every initial
object simultaneously.

### The non-pointed half (the other endpoint, also a universal)

`nonpointed_initial_isEmpty` — **in `Type`, an object is initial iff it is empty.** This is
`Types.initial_iff_empty`, quantified over all `X : Type`: every initial object has card exactly 0,
none has a point. So the non-pointed endpoint is *also* forced, not sampled.

### The dichotomy is genuinely a binary (not multi-valued)

`pointedness_dichotomy` bundles the two universals with the structural separator: `Type` has **no**
zero object while `ModuleCat ℂ` **does** (`HasZeroObject`). The two regimes are therefore separated
by a real categorical invariant, and within each regime the initial carrier-cardinality is pinned to
a single value (0 for non-pointed, ≤ 1 for pointed). This upgrades TC09's heuristic from
"the framework happens to sample only two classes" to "the relevant categories *force* exactly these
two classes" — Axis III is a clean binary, witnessed.

**Honest fence — what is Lean and what is interpretation.** The Lean content is exactly: (a) every
initial object of `ModuleCat ℂ` has a subsingleton carrier; (b) every initial object of `Type` is
empty; (c) `Type` has no zero object, `ModuleCat ℂ` has one. The claim that *this* binary is THE
governing invariant of "the framework's bottoms" generally (beyond these two categories) is the
framework's reading, not a Lean theorem — the universals are proved only for `Type` and
`ModuleCat ℂ`, the two categories whose initial bottoms (#4-style empty, #5-style singleton) the
framework actually instantiates. The NO-GO obstruction (an initial object with a card-≥-2 carrier in
a framework-relevant category) is *refuted* for `ModuleCat ℂ` by (a): the dichotomy does not break
there.
-/

namespace ZeroParadox.ZPH_MC1_TC14

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-! ## The pointed half: every initial object of `ModuleCat ℂ` has a subsingleton carrier -/

/-- **GO (load-bearing closure).** In `ModuleCat ℂ`, **every** initial object has a subsingleton
    carrier (cardinality ≤ 1). Quantified over all `Z`, not a single witness: this is the closure
    claim TC09 stated in prose ("no initial object has a carrier of cardinality ≥ 2") but never
    proved. Proof chain: initial `Z` ≅ the zero object `0` (`IsZero.isoIsInitial`), the zero object's
    carrier is a subsingleton (`subsingleton_of_isZero`), and that transfers across the ℂ-linear
    equivalence `ModuleCat.toLinearEquiv`. -/
theorem pointed_initial_carrier_subsingleton (Z : ModuleCat ℂ) (hZ : IsInitial Z) :
    Subsingleton Z := by
  -- `0` is the zero object of `ModuleCat ℂ`; it is initial and `Z` is initial, so `0 ≅ Z`.
  have hiso : (0 : ModuleCat ℂ) ≅ Z := (isZero_zero (ModuleCat ℂ)).isoIsInitial hZ
  -- the zero object's carrier is a subsingleton
  haveI hsub0 : Subsingleton (0 : ModuleCat ℂ) :=
    ModuleCat.subsingleton_of_isZero (isZero_zero (ModuleCat ℂ))
  -- transfer the subsingleton across the carrier-level linear equivalence
  exact hiso.toLinearEquiv.toEquiv.symm.subsingleton

/-- The same closure stated directly for a **zero object** carrier: any zero object of `ModuleCat ℂ`
    has a subsingleton carrier. (The pointed endpoint, isolated.) -/
theorem zero_initial_carrier_subsingleton (Z : ModuleCat ℂ) (hZ : IsZero Z) :
    Subsingleton Z :=
  ModuleCat.subsingleton_of_isZero hZ

/-! ## The non-pointed half: every initial object of `Type` is empty -/

/-- **The non-pointed endpoint (universal).** In `Type`, an object is initial **iff** it is empty.
    Quantified over all `X` (this is `Types.initial_iff_empty`): every initial object of `Type` has
    cardinality exactly 0, none carries a point. The lower endpoint of the dichotomy is forced. -/
theorem nonpointed_initial_isEmpty (X : Type u) :
    Nonempty (IsInitial X) ↔ IsEmpty X :=
  Types.initial_iff_empty X

/-! ## The dichotomy is a clean binary, separated by a real categorical invariant -/

/-- **TC14 capstone — the pointedness dichotomy, now witnessed as a binary (not sampled).**

    1. **Pointed regime forced** — every initial object of `ModuleCat ℂ` has card ≤ 1.
    2. **Non-pointed regime forced** — every initial object of `Type` is empty (card 0).
    3. **Real separator** — `Type` has **no** zero object, `ModuleCat ℂ` **has** one.

    Together: the two cardinality classes TC09 sampled are pinned by the pointedness invariant, and
    no third class (card ≥ 2) is reachable in either category. This sharpens TC09's heuristic into a
    proved binary for the two categories the framework's bottoms (#4 empty / #5 singleton)
    instantiate. -/
theorem pointedness_dichotomy :
    (∀ Z : ModuleCat ℂ, IsInitial Z → Subsingleton Z) ∧
    (∀ X : Type, Nonempty (IsInitial X) ↔ IsEmpty X) ∧
    ¬ HasZeroObject (Type) ∧
    HasZeroObject (ModuleCat ℂ) := by
  refine ⟨pointed_initial_carrier_subsingleton, fun X => nonpointed_initial_isEmpty X, ?_, ?_⟩
  · -- `Type` has no zero object: a zero object would be both initial (empty) and terminal
    -- (inhabited), a contradiction.
    rintro ⟨⟨Z, hZ⟩⟩
    -- `Z` is initial, hence empty
    haveI hempty : IsEmpty Z := (Types.initial_iff_empty Z).mp ⟨hZ.isInitial⟩
    -- `Z` is terminal, hence the unique map from `PUnit` lands a point in `Z`
    have hterm : IsTerminal Z := hZ.isTerminal
    exact hempty.elim (hterm.from (PUnit : Type) PUnit.unit)
  · infer_instance

end ZeroParadox.ZPH_MC1_TC14

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `ModuleCat` / `Type`-limits / inner-product libraries
— a library dependency carried by these standard categories, not a new commitment of this
construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC14

#print axioms pointed_initial_carrier_subsingleton
#print axioms zero_initial_carrier_subsingleton
#print axioms nonpointed_initial_isEmpty
#print axioms pointedness_dichotomy

end PurityCheck
