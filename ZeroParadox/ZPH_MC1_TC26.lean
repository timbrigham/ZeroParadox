-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import ZeroParadox.ZPP_Coalgebra

/-!
# ZP-H MC-1 tree test TC26: the root-cut degeneracy dichotomy

This module sharpens the strict μ/ν fork of `ZPP_Coalgebra.lean` (TC21) into a **dichotomy at the
root of the tree**. TC21 proved the fork *strict* on the leaf-free one-child functor `idPF`
(child type `PUnit`, a recursive position): the initial algebra `QPF.Fix idPF.Obj` is empty and the
final coalgebra `QPF.Cofix idPF.Obj` is inhabited, so the two fixed points cannot agree.

Here we show the complementary case. Take the **leaf-free constant polynomial functor**
`constPF A := ⟨A, fun _ => PEmpty⟩` — head type `A`, **no recursive position** (child type empty).
Then both fixed points collapse:

- `QPF.Fix (constPF A).Obj ≃ A`  (`fixEquiv`)
- `QPF.Cofix (constPF A).Obj ≃ A` (`cofixEquiv`)

and therefore the least and greatest fixed points are equivalent — a **root-level seam**:

- `root_seam : QPF.Fix (constPF A).Obj ≃ QPF.Cofix (constPF A).Obj`.

The dichotomy theorem `root_cut_dichotomy` records both halves with the discriminating structural
feature stated in the type: the constant functor (no recursive position) gives `Fix ≃ Cofix`, while
the identity functor (one recursive position) gives `IsEmpty (Fix) ∧ Nonempty (Cofix)` — i.e. they are
*not* equivalent (`idPF_no_seam`). The seam therefore recurs at the root level exactly when the
functor has no recursive position, paralleling the zero-object seam at node #5 (Hilbert bottom).

## Formal Overview

For a polynomial functor `P`, `QPF.Fix P.Obj ≃ P (Fix P.Obj)` and `QPF.Cofix P.Obj ≃ P (Cofix P.Obj)`
via the mutually-inverse pairs `Fix.mk/Fix.dest` and (for `Cofix`, built here by corecursion)
`cofixMk/Cofix.dest`. For `constPF A` the action is `(constPF A).Obj X = Σ _ : A, (PEmpty → X) ≃ A`
because `PEmpty → X` is a singleton. Composing the unfold equivalence with this collapse gives both
`fixEquiv` and `cofixEquiv`, and `root_seam := fixEquiv.trans cofixEquiv.symm`. The strict side is
imported verbatim from `ZeroParadox.ZPP.categorical_fork_strict`.

What is PROVED is exactly the equivalences and the dichotomy bundle below. The identification of this
root seam with the diagonal fixed point / the node-#5 zero-object seam is the cross-instance modeling
commitment of ZP-P, not a theorem.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH.TC26

open QPF

set_option maxHeartbeats 400000

universe u

/-- The leaf-free **constant** polynomial functor: head type `A`, **no recursive position**
(child family `fun _ => PEmpty`). Its action is `(constPF A).Obj X ≃ A` for every `X`. -/
def constPF (A : Type u) : PFunctor.{u, u} := ⟨A, fun _ => PEmpty⟩

/-- `(constPF A).Obj` is a QPF, with `abs`/`repr` the identity (it is already polynomial). -/
instance qpfConstPF (A : Type u) : QPF (constPF A).Obj where
  P := constPF A
  abs := fun x => x
  repr := fun x => x
  abs_repr := fun _ => rfl
  abs_map := fun _ _ => rfl

variable {A : Type u}

/-- The action collapses: `(constPF A).Obj X ≃ A` for any `X`, because the child type is empty so
`PEmpty → X` is a singleton. -/
def objEquiv (X : Type u) : (constPF A).Obj X ≃ A where
  toFun x := x.1
  invFun a := ⟨a, fun e => e.elim⟩
  left_inv := by
    rintro ⟨a, f⟩
    simp only
    congr
    funext e
    exact e.elim
  right_inv := by intro a; rfl

/-! ### μ side: `Fix (constPF A).Obj ≃ A` -/

/-- `Fix ≃ A`: the initial algebra of the leaf-free constant functor collapses to `A`. -/
def fixEquiv : Fix (constPF A).Obj ≃ A where
  toFun x := (Fix.dest x).1
  invFun a := Fix.mk ⟨a, fun e => e.elim⟩
  left_inv := by
    intro x
    show Fix.mk (⟨(Fix.dest x).1, fun e => e.elim⟩ :
        (constPF A).Obj (Fix (constPF A).Obj)) = x
    conv_rhs => rw [← Fix.mk_dest x]
    congr 1
    rcases Fix.dest x with ⟨a, f⟩
    congr 1
    funext e
    exact e.elim
  right_inv := by
    intro a
    simp only [Fix.dest_mk]

/-! ### ν side: `Cofix (constPF A).Obj ≃ A` -/

/-- The corecursive constructor for `Cofix (constPF A).Obj`: every `a : A` corecurses to the node
with head `a` and no children. -/
def cofixMk (a : A) : Cofix (constPF A).Obj :=
  Cofix.corec (fun a => (⟨a, fun e => e.elim⟩ : (constPF A).Obj A)) a

/-- `Cofix.dest (cofixMk a)` has head `a`. -/
theorem cofixMk_head (a : A) : (Cofix.dest (cofixMk a)).1 = a := by
  rw [cofixMk, Cofix.dest_corec]
  rfl

/-- `Cofix ≃ A`: the final coalgebra of the leaf-free constant functor collapses to `A`.
The right inverse `cofixMk (dest x).1 = x` is proved by bisimulation. -/
def cofixEquiv : Cofix (constPF A).Obj ≃ A where
  toFun x := (Cofix.dest x).1
  invFun a := cofixMk a
  left_inv := by
    -- cofixMk ((Cofix.dest x).1) = x, by bisimulation
    intro x
    refine Cofix.bisim (fun u v => u = cofixMk (Cofix.dest v).1) ?_ _ _ rfl
    intro u v huv
    subst huv
    rw [liftr_iff]
    refine ⟨(Cofix.dest v).1, fun e => e.elim, fun e => e.elim, ?_, ?_, ?_⟩
    · -- Cofix.dest (cofixMk (Cofix.dest v).1) = abs ⟨(Cofix.dest v).1, PEmpty.elim⟩
      rw [cofixMk, Cofix.dest_corec]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext e
        exact e.elim
    · -- Cofix.dest v = abs ⟨(Cofix.dest v).1, PEmpty.elim⟩  (abs = id; children vacuous)
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext e
        exact e.elim
    · intro e; exact e.elim
  right_inv := by
    intro a
    exact cofixMk_head a

/-! ### The root seam and the dichotomy -/

/-- **Root-level seam.** For the leaf-free constant functor the least and greatest fixed points are
equivalent: `Fix ≃ Cofix`. The seam recurs at the root of the tree. -/
def root_seam : Fix (constPF A).Obj ≃ Cofix (constPF A).Obj :=
  fixEquiv.trans cofixEquiv.symm

/-- For the one-recursive-position functor `idPF`, the fixed points are NOT equivalent: an equivalence
would carry the inhabitant of `Cofix idPF.Obj` (ν) back into the empty `Fix idPF.Obj` (μ). This is the
strict half of the dichotomy, derived from `ZeroParadox.ZPP.categorical_fork_strict`. -/
theorem idPF_no_seam : IsEmpty (Fix ZeroParadox.ZPP.idPF.Obj ≃ Cofix ZeroParadox.ZPP.idPF.Obj) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨c⟩ := ZeroParadox.ZPP.cofix_nonempty
  exact ZeroParadox.ZPP.fix_isEmpty.false (e.symm c)

/-- **The root-cut degeneracy dichotomy.** The μ/ν root cut is strict exactly when the functor has a
recursive position and collapses to a seam exactly when it has none:

* leaf-free **constant** functor `constPF A` (child type `PEmpty`, no recursive position):
  `Fix ≃ Cofix` (a seam) — first component;
* one-shape **identity** functor `idPF` (child type `PUnit`, one recursive position):
  `IsEmpty (Fix ≃ Cofix)` (strict, no seam) — second component. -/
theorem root_cut_dichotomy :
    (Nonempty (Fix (constPF Unit).Obj ≃ Cofix (constPF Unit).Obj)) ∧
    IsEmpty (Fix ZeroParadox.ZPP.idPF.Obj ≃ Cofix ZeroParadox.ZPP.idPF.Obj) :=
  ⟨⟨(root_seam : Fix (constPF Unit).Obj ≃ _)⟩, idPF_no_seam⟩

section PurityCheck
-- Measured footprint (lake build, v4.30.0-rc2):
--   objEquiv             : [Quot.sound]                                — the action collapse
--   fixEquiv  (μ side)   : [propext, Quot.sound]                       — CHOICE-FREE
--   cofixEquiv (ν side)  : [propext, Classical.choice, Quot.sound]     — choice-carrying
--   root_seam            : [propext, Classical.choice, Quot.sound]     — inherits ν's choice
--   idPF_no_seam         : [propext, Classical.choice, Quot.sound]     — inherits via cofix_nonempty
--   root_cut_dichotomy   : [propext, Classical.choice, Quot.sound]
-- The same μ-choice-free / ν-choice split as ZPP_Coalgebra: the seam's ν half carries the M-type
-- choice artifact inherited from Mathlib (Cofix.corec / Cofix.bisim). The μ half (fixEquiv) is
-- choice-free, exactly as in the strict case. The choice on the ν side is a library artifact, not a
-- necessity (polynomial-functor final coalgebra is constructible choice-free in principle).
#print axioms objEquiv
#print axioms fixEquiv
#print axioms cofixEquiv
#print axioms root_seam
#print axioms idPF_no_seam
#print axioms root_cut_dichotomy
end PurityCheck

end ZeroParadox.ZPH.TC26
