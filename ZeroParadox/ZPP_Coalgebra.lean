import Mathlib.Data.QPF.Univariate.Basic
import ZeroParadox.ZPP

/-!
# ZP-P instance: the categorical parent (initial algebra vs final coalgebra)

The categorical-parent instance of the fixed-point fork (ZP-P). The set-theory fork
(ZFC+Foundation / ZFC+AFA) is the powerset-functor case of a general categorical fork: for an
endofunctor, the **initial algebra** (least fixed point μ, the well-founded / inductive closure) versus
the **final coalgebra** (greatest fixed point ν, the non-well-founded / coinductive closure). Mathlib
realises these for a QPF as `QPF.Fix` (the W-type) and `QPF.Cofix` (the M-type).

This file exhibits the strictest possible form of the fork on a concrete functor. Take the one-shape,
one-child polynomial functor `idPF` (`A = PUnit`, `B = fun _ => PUnit`), which has no leaf constructor.
Then:

- **`Fix idPF.Obj` is empty** — there is no finite, well-founded element, because every element would
  need a child and there is no base case. The least-fixed-point (inductive) closure is empty.
- **`Cofix idPF.Obj` is inhabited** — the infinite self-referential element exists (built by
  corecursion: the node that unfolds to itself forever). The greatest-fixed-point (coinductive)
  closure contains it.

So the non-well-founded closure contains a self-referential element that the well-founded closure
lacks. This is the categorical analog of the Quine atom living in νF \ μF: the contact point of the
fork is exactly the self-referential element that ν admits and μ forbids — the same shape as
ZFC+Foundation (no ⊥={⊥}) vs ZFC+AFA (⊥={⊥}) (set theory: ZP-J).

**FENCE.** This is the genuine μ/ν instance of the schema (unlike the Ostrowski number-system instance,
which is theorem-backed but not a μ/ν instance). What is claimed here is exactly the two Lean theorems
below: `Fix` empty, `Cofix` inhabited, for this functor. The identification of this categorical contact
point with the diagonal fixed point of the other layers is the cross-instance identity — a modeling
commitment, not a theorem (ZP-P hard fence).

## Status

STUB (stub-first protocol): the functor and QPF instance are concrete; the two theorems are `sorry`.
-/

namespace ZeroParadox.ZPP

open QPF

set_option maxHeartbeats 400000

/-- The one-shape, one-child polynomial functor: `A = PUnit`, `B = fun _ => PUnit`. Its action is
`idPF.Obj α ≅ α` (one constructor, one recursive child, no leaf). -/
def idPF : PFunctor.{0, 0} := ⟨PUnit, fun _ => PUnit⟩

/-- `idPF.Obj` is a QPF, with `abs` and `repr` the identity (it is already a polynomial functor). -/
instance : QPF idPF.Obj where
  P := idPF
  abs := fun x => x
  repr := fun x => x
  abs_repr := fun _ => rfl
  abs_map := fun _ _ => rfl

/-- **μ is empty.** The initial algebra (W-type) of the leaf-free functor has no element: no
well-founded / inductive tree exists without a base case. -/
theorem fix_isEmpty : IsEmpty (Fix idPF.Obj) := by
  sorry

/-- **ν is inhabited.** The final coalgebra (M-type) contains the infinite self-referential element,
built by corecursion from the single node that unfolds to itself. -/
theorem cofix_nonempty : Nonempty (Cofix idPF.Obj) := by
  sorry

/-- **The strict categorical fork.** The least fixed point is empty while the greatest is inhabited:
the non-well-founded closure contains a self-referential element the well-founded closure lacks — the
categorical analog of the Quine atom in νF \ μF. -/
theorem categorical_fork_strict :
    IsEmpty (Fix idPF.Obj) ∧ Nonempty (Cofix idPF.Obj) :=
  ⟨fix_isEmpty, cofix_nonempty⟩

end ZeroParadox.ZPP
