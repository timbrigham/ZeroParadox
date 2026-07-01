-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_InfoFunctor
import ZeroParadox.ZPH_MC1_TreeObstructions
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — the #5 straddle resolved: the Hilbert bottom is the μ=ν seam

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The bottom-diagram tree (`thread_obstruction_table_2026-06-29.md` §7) has a μ root (initial /
least-fixed-point / colimit) and a ν root (terminal / greatest-fixed-point / limit). Node #5, the
Hilbert bottom `fD_functor.obj 0 = StateSpace 0`, **straddles**: it is a *zero object* of
`ModuleCat ℂ` (initial ∧ terminal). A clean tree cannot put one leaf in both branches — so either #5
sits AT the μ/ν seam (the μ=ν coincidence, the [[project_diagonal_fixed_point]]) or it is a defect.

**Resolution: #5 is the seam, not a defect — the only both-sided node among the three categorical
bottoms** (a three-way separation, not a uniqueness claim over all objects). The others sit strictly
on one side:

- `hilbert_bottom_isZero` — #5 `fD_functor.obj 0` is a **zero object** (initial ∧ terminal): the
  μ=ν coincidence, the seam node.
- `kleisli_bottom_not_terminal` — #4 `fC_functor.obj 0 = Fin 0` is **initial but NOT terminal** (a
  terminal object would need a morphism *into* it from every object, but `fC_no_return` proves the
  hom-set from any nonempty object into `Fin 0` is empty). So #4 is strictly on the μ side.
- (#3, the p-adic floor, is strictly on the ν side: `ZPH_MC1_TreeObstructions.padic_bottom_not_initial`
  — not initial.)

So the μ/ν fork is genuinely populated: #4 strictly μ, #3 strictly ν, #5 the (among-these-three) seam
where they coincide. That `StateSpace 0` is special this way is exactly what the zero object means — the place
the two universal properties collapse into one — which is the diagonal-fixed-point keystone realized
at a node, not a bug in the tree.

**Honest fence.** "This seam IS the diagonal fixed point / the keystone" is the framework's
interpretation, not a Lean claim; the Lean content is precisely: #5 is a zero object, #4 is initial
and not terminal, #3 is not initial. The seam reading is the meaning we attach to that pattern.
-/

namespace ZeroParadox.ZPH_MC1_TreeSeam

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPB ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor
open ZeroParadox.ZPH_MC1_TreeObstructions

/-- #5 is the seam: the Hilbert bottom is a **zero object** (initial ∧ terminal) of `ModuleCat ℂ` —
    the μ=ν coincidence at a node. -/
theorem hilbert_bottom_isZero : Limits.IsZero (fD_functor.obj 0) := by
  haveI : Subsingleton (StateSpace 0) := ⟨fun a b => by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ (StateSpace 0))

/-- #4 is strictly on the μ side: the Kleisli bottom `Fin 0` is initial but **not terminal** — a
    terminal object would need a morphism into it from `fC_functor.obj 1`, but `fC_no_return` proves
    that hom-set is empty (the snap's irreversibility). -/
theorem kleisli_bottom_not_terminal :
    IsEmpty (Limits.IsTerminal (fC_functor.obj 0)) := by
  refine ⟨fun hterm => ?_⟩
  exact (fC_no_return (by norm_num : 0 < 1)).false (hterm.from (fC_functor.obj 1))

/-- The three categorical bottoms sit at **distinct positions of the μ/ν fork**, all in one statement:
    #5 is a zero object (μ ∧ ν — the seam); #4 is not terminal (strictly μ); #3 is not initial
    (strictly ν). So among these three, #5 is the only both-sided (seam) node. NOTE: this is a
    three-way separation of the *named* bottoms, NOT a uniqueness claim quantified over all objects. -/
theorem fork_positions_distinct :
    Limits.IsZero (fD_functor.obj 0)
    ∧ IsEmpty (Limits.IsTerminal (fC_functor.obj 0))
    ∧ IsEmpty (Limits.IsInitial (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))) :=
  ⟨hilbert_bottom_isZero, kleisli_bottom_not_terminal, padic_bottom_not_initial⟩

end ZeroParadox.ZPH_MC1_TreeSeam

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TreeSeam

#print axioms hilbert_bottom_isZero
#print axioms kleisli_bottom_not_terminal
#print axioms fork_positions_distinct

end PurityCheck
