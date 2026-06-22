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

PROVED. Two theorems, no `sorry`. Split axiom footprint: `fix_isEmpty` (μ empty) is choice-free
`[propext, Quot.sound]`; `cofix_nonempty` (ν inhabited) carries `Classical.choice` from Mathlib's
M-type / corecursion machinery. That choice is a library artifact, not a necessity: for a polynomial
functor the final coalgebra is constructible choice-free (Ahrens et al.; Veltri, FSCD 2021). See
PurityCheck.
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
theorem fix_isEmpty : IsEmpty (Fix idPF.Obj) :=
  ⟨fun x => Fix.ind (fun _ => False) (fun y hy => by
      rw [liftp_iff] at hy
      obtain ⟨_, f, _, hf⟩ := hy
      exact hf PUnit.unit) x⟩

/-- **ν is inhabited.** The final coalgebra (M-type) contains the infinite self-referential element,
built by corecursion from the single node that unfolds to itself. -/
theorem cofix_nonempty : Nonempty (Cofix idPF.Obj) :=
  ⟨Cofix.corec (fun _ : PUnit => (⟨PUnit.unit, fun _ => PUnit.unit⟩ : idPF.Obj PUnit)) PUnit.unit⟩

/-- **The strict categorical fork.** The least fixed point is empty while the greatest is inhabited:
the non-well-founded closure contains a self-referential element the well-founded closure lacks — the
categorical analog of the Quine atom in νF \ μF. -/
theorem categorical_fork_strict :
    IsEmpty (Fix idPF.Obj) ∧ Nonempty (Cofix idPF.Obj) :=
  ⟨fix_isEmpty, cofix_nonempty⟩

/-! ## Engineer's Take

These files sit at the boundary of where choice lives within the framework. There is a distinct boundary
between the theorems that define the Zero Paradox framework itself and the individual implementations of
the tooling, and that boundary is the same for set theory, coalgebra, and p-adics. This is a synthesis
layer: a validation tool, a unit test to represent that concept quickly.

Here the dataset is the leaf-free polynomial functor `idPF`: its W-type (`QPF.Fix`, μ) is empty and
choice-free, while its M-type (`QPF.Cofix`, ν) is inhabited and carries choice inherited from Mathlib, with
choice entering exactly on the non-well-founded, self-referential side.

*Editorial addendum (Claude):* that choice on the ν side is inherited from Mathlib's M-type machinery,
not a necessity — for a polynomial functor like `idPF` the final coalgebra is constructible choice-free
in principle (Ahrens–Capriotti–Spadotti; Veltri, FSCD 2021, the coinductive construction). Choice
genuinely enters the μ/ν story only for the non-polynomial finite-powerset functor, where it is pinned
per presentation: full AC for the set-quotient, countable choice + LLPO (⟺ injectivity of the canonical
algebra) for Worrell's (ω+ω)-limit (Veltri, FSCD 2021).
-/

section PurityCheck
-- Split footprint, and the split is meaningful:
--   fix_isEmpty (μ is empty)        : [propext, Quot.sound]                     — CHOICE-FREE
--   cofix_nonempty (ν is inhabited) : [propext, Classical.choice, Quot.sound]  — choice-carrying
--   categorical_fork_strict         : inherits Classical.choice from cofix_nonempty
-- The well-founded (inductive) side is constructive; the non-well-founded (coinductive) side carries
-- Classical.choice — but as a Mathlib artifact, NOT a necessity: for a polynomial functor like idPF the
-- final coalgebra (M-type) is constructible choice-free in principle (Ahrens–Capriotti–Spadotti;
-- Veltri, FSCD 2021, the coinductive construction). Choice genuinely enters the μ/ν story only for the
-- non-polynomial finite-powerset functor — pinned per presentation: full AC for the set-quotient,
-- countable choice + LLPO (⟺ injectivity of alg_Vω) for Worrell's limit (Veltri). The fork spine
-- (`ZeroParadox.ZPP.fork_collapse_iff`) is fully choice-free. See AxiomProfile.lean.
#print axioms fix_isEmpty
#print axioms cofix_nonempty
#print axioms categorical_fork_strict
end PurityCheck

end ZeroParadox.ZPP
