-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Category.Category
import ZeroParadox.Order.Lattice
import ZeroParadox.Multihomed.TreeObstructions
import ZeroParadox.Category.TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Seam uniqueness extended: is any OTHER bottom a zero object?

Of five NAMED bottoms only #5 is a zero object (`seam_unique_among_named`), a finite case check. The
ZP-G case uses AX-G1 (no terminal) only; strict initiality (Carboni–Lack–Walters) is AX-G2, per
`ZPCategory` in `ZeroParadox/Category/Category.lean`. Detail: `ZeroParadox/Category/SeamUniqueness.md`.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

-/

namespace ZeroParadox

open CategoryTheory
open ZeroParadox ZeroParadox
open ZeroParadox ZeroParadox
open ZeroParadox ZeroParadox

/-! ## ZP-G: the initial object of a ZPCategory is never a zero object -/

/-- In **any** `ZPCategory C`, the initial bottom `zpInitial` is **not** a zero object.
    A zero object is terminal (`IsZero.isTerminal`), but `ax_g1_no_terminal` forbids any terminal
    object in a ZPCategory. So the ZP-G bottom is strictly on the initial (μ) side — it cannot
    straddle. -/
theorem zpcategory_initial_not_zero (C : Type*) [Category C] [ZPC : ZPCategory C] :
    ¬ Limits.IsZero ZPC.zpInitial := by
  intro hz
  exact (ZPC.ax_g1_no_terminal ZPC.zpInitial).false hz.isTerminal

-- `Statement:` the same conclusion from the no-terminal hypothesis alone, with no initiality and no
-- AX-G2 in the binders.
example {C : Type*} [Category C] (z : C) (h : ∀ t : C, IsEmpty (Limits.IsTerminal t)) :
    ¬ Limits.IsZero z :=
  fun hz => (h z).false hz.isTerminal

/-- Concrete instance: the initial object of the `ForkObj` ZPCategory is not a zero object. -/
theorem forkcat_initial_not_zero :
    ¬ Limits.IsZero (forkZPCategory.zpInitial) :=
  zpcategory_initial_not_zero ForkObj

/-! ## ZP-A: the lattice bottom is least but not greatest -/

/-- In any ZP-A semilattice with no top element, the bottom `⊥ₗ` is the **least** element
    (`bot_le`) but is **not** a greatest element: `¬ ∀ x, x ≼ ⊥ₗ`. This is the order-theoretic
    analogue of "initial but not terminal" — the poset-as-category bottom is the colimit (μ) end,
    not the limit (ν) end, so it does not straddle. -/
theorem zpa_bot_not_greatest (L : Type*) [ZPSemilattice L] (hnt : ZPSemilattice.HasNoTop L) :
    (∀ x : L, ZPSemilattice.le (ZPSemilattice.bot : L) x)
      ∧ ¬ (∀ x : L, ZPSemilattice.le x (ZPSemilattice.bot : L)) := by
  refine ⟨ZPSemilattice.bot_le, fun hgreatest => ?_⟩
  obtain ⟨y, hby, hne⟩ := hnt (ZPSemilattice.bot : L)
  exact hne (ZPSemilattice.le_antisymm hby (hgreatest y))

/-! ## #4 Kleisli and #3 p-adic: not zero objects -/

/-- #4: the Kleisli bottom `Fin 0` is **not** a zero object. A zero object is terminal, but
    `kleisli_bottom_not_terminal` proves it is not terminal. Strictly μ. -/
theorem kleisli_bottom_not_zero :
    ¬ Limits.IsZero (fC_functor.obj 0) := by
  intro hz
  exact kleisli_bottom_not_terminal.false hz.isTerminal

/-- #3: the p-adic floor `{0} ⊆ Q₂` is **not** a zero object. A zero object is initial, but
    `padic_bottom_not_initial` proves it is not initial. Strictly ν. -/
theorem padic_bottom_not_zero :
    ¬ Limits.IsZero (TopCat.of (↥({(0 : Q₂)} : Set Q₂))) := by
  intro hz
  exact padic_bottom_not_initial.false hz.isInitial

/-! ## Capstone: among the named bottoms, #5 is the only zero object -/

/-- **Seam uniqueness among the named bottoms.** Of the five framework bottoms, only #5 (the Hilbert
    bottom) is a zero object; #3, #4, the ZP-G initial, and the ZP-A bottom each provably fail, the
    ZP-A bottom under the premise `HasNoTop L` (it is least but not greatest when `L` has no top).

    This refutes the pre-registered GO conjecture ("another zero-object bottom exists") and
    establishes the pre-registered NO-GO obstruction ("#5 is the only zero-object bottom among those
    tested"). It is a finite case check over the **named** list, not a universal claim over all
    objects. -/
theorem seam_unique_among_named (L : Type*) [ZPSemilattice L]
    (hnt : ZPSemilattice.HasNoTop L) :
    -- #5 IS a zero object (the seam)
    Limits.IsZero (fD_functor.obj 0)
    -- #4 is NOT a zero object
    ∧ ¬ Limits.IsZero (fC_functor.obj 0)
    -- #3 is NOT a zero object
    ∧ ¬ Limits.IsZero (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))
    -- the ZP-G ForkCat initial is NOT a zero object
    ∧ ¬ Limits.IsZero (forkZPCategory.zpInitial)
    -- the ZP-A bottom is least but NOT greatest (no zero/top end)
    ∧ ((∀ x : L, ZPSemilattice.le (ZPSemilattice.bot : L) x)
        ∧ ¬ (∀ x : L, ZPSemilattice.le x (ZPSemilattice.bot : L))) :=
  ⟨hilbert_bottom_isZero,
   kleisli_bottom_not_zero,
   padic_bottom_not_zero,
   forkcat_initial_not_zero,
   zpa_bot_not_greatest L hnt⟩

-- `Statement:` on any ZP-A semilattice with two distinct elements the bottom is not greatest. Unlike
-- `zpa_bot_not_greatest`, this takes no `HasNoTop` premise.
example {L : Type*} [ZPSemilattice L] (a b : L) (hab : a ≠ b) :
    ¬ ∀ x : L, ZPSemilattice.le x (ZPSemilattice.bot : L) := by
  intro h
  exact hab ((ZPSemilattice.le_antisymm (h a) (ZPSemilattice.bot_le a)).trans
    (ZPSemilattice.le_antisymm (h b) (ZPSemilattice.bot_le b)).symm)

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `ModuleCat` / `TopCat` / `KleisliCat` / category
libraries used by the cited bottoms — a library dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox

#print axioms zpcategory_initial_not_zero
#print axioms forkcat_initial_not_zero
#print axioms zpa_bot_not_greatest
#print axioms kleisli_bottom_not_zero
#print axioms padic_bottom_not_zero
#print axioms seam_unique_among_named

end PurityCheck
