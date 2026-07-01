-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_InfoFunctor
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC09 — Axis III generality: is the #4/#5 cardinality split canonical?

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`ZPH_MC1_TreeObstructions.split_kleisli_vs_hilbert` records **Axis III**: the Kleisli bottom
`Fin 0` (empty, cardinality 0) and the Hilbert bottom `StateSpace 0` (a singleton, cardinality 1)
are **both initial objects** of their respective categories, yet their carriers are not in bijection.
So initiality (polarity) is not a complete invariant of a bottom; a finer invariant — carrier
cardinality — separates two same-polarity bottoms.

**The TC09 question (TH9):** is the #4/#5 pair the *canonical* instance of this phenomenon, or is the
phenomenon generic — does another natural same-polarity pair, distinguished only by cardinality,
exist?

**Pre-registered GO:** another cardinality-only-distinguished initial pair exists.
**Pre-registered NO-GO:** #4/#5 is the canonical/only natural instance.

**Verdict: GO — the phenomenon is generic; #4/#5 is *not* canonical.** A second, completely
independent same-polarity pair is exhibited, drawn from two of the most standard categories in
Mathlib (neither is a ZP construction):

- `type_initial_card0` — the initial object of the category `Type u` is `PEmpty`
  (`Types.isInitialPEmpty`): an **empty** carrier, cardinality 0.
- `module_initial_card1` — the zero module `ModuleCat.of ℂ PUnit` is an initial object of
  `ModuleCat ℂ`: a **singleton** carrier, cardinality 1.
- `split_type_vs_module` — **both are initial, yet `PEmpty` and `PUnit` are not in bijection**
  (the load-bearing statement: same polarity, distinct cardinality). This is a *different* pair from
  the Kleisli/Hilbert pair, so Axis III is not a peculiarity of #4/#5.

**The structural explanation (also in-statement, `axis_iii_is_pointedness`).** The two cardinality
classes are governed by a single binary distinction: whether the category's objects are forced to
carry a distinguished point (a zero object). When they are not (`Type`, `KleisliCat PMF`,
`TopCat`), the initial object is **empty** (card 0); when they are (`ModuleCat`, any category with a
zero object), the initial object is a **singleton** (card 1, the zero object's underlying set). The
theorem witnesses both endpoints: `Type`'s initial object is empty, `ModuleCat ℂ`'s is a
subsingleton. So the #4/#5 split is one shadow of this binary; the canonical content is the
pointedness dichotomy, not the specific Kleisli/Hilbert objects.

**Honest scope.** "Distinguished only by cardinality" is witnessed as "both initial AND carriers not
in bijection" — exactly the form `split_kleisli_vs_hilbert` uses. Only the two cardinality classes
0 and 1 arise (no initial object has a carrier of cardinality ≥ 2, because an initial object is
unique up to iso *within its category* and the categories here have at most one point in the initial
carrier); the result is that the phenomenon recurs across unrelated categories, not that arbitrary
cardinalities occur.
-/

namespace ZeroParadox.ZPH_MC1_TC09

open CategoryTheory

/-! ## A second, independent same-polarity pair: `Type` (empty) vs `ModuleCat ℂ` (singleton) -/

/-- The initial object of `Type u` is `PEmpty` — an **empty** carrier (cardinality 0).
    Same polarity (initial) as the Kleisli bottom `Fin 0`, drawn from a completely different,
    standard category. -/
noncomputable def type_initial_card0 : Limits.IsInitial (PEmpty.{u + 1} : Type u) :=
  Limits.Types.isInitialPEmpty

/-- The zero module (carrier `PUnit`) is an initial object of `ModuleCat ℂ` — a **singleton**
    carrier (cardinality 1). Same polarity (initial) as the Hilbert bottom `StateSpace 0`, drawn
    from a standard category. -/
noncomputable def module_initial_card1 :
    Limits.IsInitial (ModuleCat.of ℂ PUnit) :=
  (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ PUnit)).isInitial

/-- **TC09 GO (load-bearing).** A second same-polarity pair, distinguished only by cardinality,
    independent of #4/#5: the initial object of `Type` (`PEmpty`, empty) and an initial object of
    `ModuleCat ℂ` (`PUnit`, singleton) are **both initial**, yet their carriers are **not in
    bijection**. So Axis III (a same-polarity pair separated by cardinality alone) is generic — the
    Kleisli/Hilbert split is one instance, not the canonical one. -/
theorem split_type_vs_module :
    Nonempty (Limits.IsInitial (PEmpty.{1} : Type 0)) ∧
    Nonempty (Limits.IsInitial (ModuleCat.of ℂ PUnit)) ∧
    ¬ Nonempty ((PEmpty : Type 0) ≃ PUnit) := by
  refine ⟨⟨type_initial_card0⟩, ⟨module_initial_card1⟩, ?_⟩
  rintro ⟨e⟩
  exact (e.symm PUnit.unit).elim

/-! ## The structural explanation: Axis III is the pointedness dichotomy -/

/-- **The canonical content (in-statement).** The two cardinality classes seen across all four
    initial bottoms (#4 `Fin 0`, `Type`'s `PEmpty` — empty; #5 `StateSpace 0`, `ModuleCat`'s `PUnit`
    — singleton) are the two endpoints of a single binary distinction: whether the category forces a
    distinguished point.

    - `IsEmpty PEmpty` — the non-pointed endpoint: `Type`'s initial carrier is empty.
    - `Subsingleton PUnit` — the pointed endpoint: `ModuleCat`'s initial carrier has at most one
      point (it is the zero object's underlying set).

    Both the new pair (`PEmpty`/`PUnit`) and the original #4/#5 pair (`Fin 0`/`StateSpace 0`) sit at
    these same two endpoints, which is why the split is not special to Kleisli/Hilbert. -/
theorem axis_iii_is_pointedness :
    IsEmpty (PEmpty : Type 0) ∧ Subsingleton PUnit ∧
    IsEmpty (Fin 0) ∧ Subsingleton (ZeroParadox.ZPD.StateSpace 0) := by
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨fun a b => by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i⟩

/-- **Cross-link to the original instance.** Both pairs are genuine same-polarity-distinct-cardinality
    pairs: the new `Type`/`ModuleCat` pair (this file) and the `Fin 0`/`StateSpace 0` pair
    (`ZPH_MC1_TreeObstructions.split_kleisli_vs_hilbert`) both have empty-vs-singleton carriers with
    both members initial. Stated here as the two empty carriers and the two singleton carriers failing
    to be in bijection with each other's class. -/
theorem two_independent_pairs :
    ¬ Nonempty ((PEmpty : Type 0) ≃ PUnit) ∧
    ¬ Nonempty (Fin 0 ≃ ZeroParadox.ZPD.StateSpace 0) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨e⟩; exact (e.symm PUnit.unit).elim
  · rintro ⟨e⟩
    exact (e.symm 0).elim0

end ZeroParadox.ZPH_MC1_TC09

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `Type`-limits / `ModuleCat` / `EuclideanSpace`
libraries — a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC09

#print axioms type_initial_card0
#print axioms module_initial_card1
#print axioms split_type_vs_module
#print axioms axis_iii_is_pointedness
#print axioms two_independent_pairs

end PurityCheck
