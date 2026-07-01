-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPG
import ZeroParadox.ZPA
import ZeroParadox.ZPH_MC1_TreeObstructions
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree TC-08 — seam uniqueness extended: is any OTHER bottom a zero object?

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`ZPH_MC1_TreeSeam` established that node #5 (the Hilbert bottom `fD_functor.obj 0 = StateSpace 0`)
is a **zero object** of `ModuleCat ℂ` — the μ=ν seam node, initial ∧ terminal. The natural
follow-up (this file, campaign cycle TC-08): **is #5 the only zero-object bottom among the framework
bottoms, or does another bottom also straddle?**

A zero object is one that is **both** initial **and** terminal. To rule a bottom *out* of being a
zero object it suffices to show it fails *one* of the two halves. We collect the four other bottoms
and show each fails — every one of them lands strictly on a single side of the μ/ν fork:

- `zpcategory_initial_not_zero` (ZP-G, generic) — in **any** `ZPCategory C`, the initial object
  `zpInitial` is **not** a zero object. The obstruction is structural and clean: a zero object is in
  particular *terminal* (`IsZero.isTerminal`), but `ZPCategory.ax_g1_no_terminal` says the category
  has **no** terminal object at all. This is a strict-initial-without-terminal category by design
  (Carboni–Lack–Walters; ZP-G AX-G1), so its bottom can never be a zero object. Specialized to the
  concrete instance `ForkObj` by `forkcat_initial_not_zero`.
- `zpa_bot_not_greatest` (ZP-A, generic) — in any ZP-A semilattice `HasNoTop L`, the bottom `⊥ₗ`
  is the **least** element (`bot_le`) but is **not** a greatest element: `¬ ∀ x, x ≼ ⊥ₗ`. The
  order-theoretic shadow of "initial but not terminal" — the poset-as-category bottom is the colimit
  end, not the limit end, exactly because there is no top.
- `kleisli_bottom_not_zero` (#4) — `fC_functor.obj 0 = Fin 0` is **not** a zero object: a zero
  object is terminal, but `ZPH_MC1_TreeSeam.kleisli_bottom_not_terminal` proves it is not terminal
  (`fC_no_return`: no stochastic map returns into the empty type). Strictly μ.
- `padic_bottom_not_zero` (#3) — the p-adic floor `{0} ⊆ Q₂` is **not** a zero object: a zero
  object is initial, but `ZPH_MC1_TreeObstructions.padic_bottom_not_initial` proves it is not
  initial. Strictly ν.

`seam_unique_among_named` bundles all four negatives with the positive
`ZPH_MC1_TreeSeam.hilbert_bottom_isZero` into one statement: among {#3, #4, #5, the ZP-G initial,
the ZP-A bottom} only #5 is a zero object.

**Verdict witnessed: NO-GO on the GO conjecture.** The pre-registered GO conjecture was "another
zero-object bottom exists"; it is **refuted** for every bottom tested. The pre-registered NO-GO
obstruction — "#5 is the only zero-object bottom among those tested" — is the result.

**Honest fence.** This is NOT a uniqueness theorem quantified over *all* objects of *all* categories
(that would be false — every category with a zero object has one). The Lean content is exactly: of
the five **named framework bottoms**, #5 is a zero object and the other four are provably not. The
five live in five different categories, so "uniqueness" here means "of the named list," a finite
case check, not a universal claim. The seam reading (#5 is the diagonal-fixed-point keystone realized
at a node) remains the framework's interpretation, not a Lean claim.
-/

namespace ZeroParadox.ZPH_MC1_TC08

open CategoryTheory
open ZeroParadox.ZPG ZeroParadox.ZPA
open ZeroParadox.ZPH_InfoFunctor ZeroParadox.ZPH_HilbFunctor
open ZeroParadox.ZPH_MC1_TreeObstructions ZeroParadox.ZPH_MC1_TreeSeam

/-! ## ZP-G: the initial object of a ZPCategory is never a zero object -/

/-- In **any** `ZPCategory C`, the initial bottom `zpInitial` is **not** a zero object.
    A zero object is terminal (`IsZero.isTerminal`), but `ax_g1_no_terminal` forbids any terminal
    object in a ZPCategory. So the ZP-G bottom is strictly on the initial (μ) side — it cannot
    straddle. -/
theorem zpcategory_initial_not_zero (C : Type*) [Category C] [ZPC : ZPCategory C] :
    ¬ Limits.IsZero ZPC.zpInitial := by
  intro hz
  exact (ZPC.ax_g1_no_terminal ZPC.zpInitial).false hz.isTerminal

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
    bottom) is a zero object; #3, #4, the ZP-G initial, and the ZP-A bottom each provably fail.

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

end ZeroParadox.ZPH_MC1_TC08

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `ModuleCat` / `TopCat` / `KleisliCat` / category
libraries used by the cited bottoms — a library dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC08

#print axioms zpcategory_initial_not_zero
#print axioms forkcat_initial_not_zero
#print axioms zpa_bot_not_greatest
#print axioms kleisli_bottom_not_zero
#print axioms padic_bottom_not_zero
#print axioms seam_unique_among_named

end PurityCheck
