import Mathlib.Data.QPF.Univariate.Basic
import ZeroParadox.Settheory.FixedPointFork

/-!
# ZP-P instance: the categorical parent (initial algebra vs final coalgebra)

The categorical-parent instance of the fixed-point fork (ZP-P). The set-theory fork
(ZFC+Foundation / ZFC+AFA) is the powerset-functor case of a general categorical fork: for an
endofunctor, the **initial algebra** (least fixed point μ, the well-founded / inductive closure) versus
the **final coalgebra** (greatest fixed point ν, the non-well-founded / coinductive closure). Mathlib
realises these for a QPF as `QPF.Fix` (the W-type) and `QPF.Cofix` (the M-type).

This file exhibits the strictest possible form of the fork on a concrete functor. Take the one-shape,
one-child polynomial functor `idPF_Coalgebra` (`A = PUnit`, `B = fun _ => PUnit`), which has no leaf constructor.
Then:

- **`Fix idPF_Coalgebra.Obj` is empty** — there is no finite, well-founded element, because every element would
  need a child and there is no base case. The least-fixed-point (inductive) closure is empty.
- **`Cofix idPF_Coalgebra.Obj` is inhabited** — the infinite self-referential element exists (built by
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
functor the final coalgebra is constructible choice-free (Ahrens et al. — their construction needs
only function extensionality, which Lean has; only their uniqueness half uses univalence, see
`ZeroParadox/Computability/ChoicePurityInvariant.lean`. Veltri is CONTRAST, not support: for the
non-polynomial finite-powerset functor his results run the other way — certain constructions
there are obtained ASSUMING choice principles rather than shown to need them, and his own
preferred coinductive construction needs neither choice nor LLPO). See PurityCheck.
-/

namespace ZeroParadox

open QPF

set_option maxHeartbeats 400000

/-- The one-shape, one-child polynomial functor: `A = PUnit`, `B = fun _ => PUnit`. Its action is
`idPF_Coalgebra.Obj α ≅ α` (one constructor, one recursive child, no leaf). -/
def idPF_Coalgebra : PFunctor.{0, 0} := ⟨PUnit, fun _ => PUnit⟩

/-- `idPF_Coalgebra.Obj` is a QPF, with `abs` and `repr` the identity (it is already a polynomial functor). -/
instance : QPF idPF_Coalgebra.Obj where
  P := idPF_Coalgebra
  abs := fun x => x
  repr := fun x => x
  abs_repr := fun _ => rfl
  abs_map := fun _ _ => rfl

/-- **μ is empty.** The initial algebra (W-type) of the leaf-free functor has no element: no
well-founded / inductive tree exists without a base case. -/
theorem fix_isEmpty : IsEmpty (Fix idPF_Coalgebra.Obj) :=
  ⟨fun x => Fix.ind (fun _ => False) (fun y hy => by
      rw [liftp_iff] at hy
      obtain ⟨_, f, _, hf⟩ := hy
      exact hf PUnit.unit) x⟩

/-- **ν is inhabited.** The final coalgebra (M-type) contains the infinite self-referential element,
built by corecursion from the single node that unfolds to itself. -/
theorem cofix_nonempty : Nonempty (Cofix idPF_Coalgebra.Obj) :=
  ⟨Cofix.corec (fun _ : PUnit => (⟨PUnit.unit, fun _ => PUnit.unit⟩ : idPF_Coalgebra.Obj PUnit)) PUnit.unit⟩

/-- **The strict categorical fork.** The least fixed point is empty while the greatest is inhabited:
the non-well-founded closure contains a self-referential element the well-founded closure lacks — the
categorical analog of the Quine atom in νF \ μF. -/
theorem categorical_fork_strict :
    IsEmpty (Fix idPF_Coalgebra.Obj) ∧ Nonempty (Cofix idPF_Coalgebra.Obj) :=
  ⟨fix_isEmpty, cofix_nonempty⟩

/-! ## Engineer's Take

These files sit at the boundary of where choice lives within the framework. There is a distinct boundary
between the theorems that define the Zero Paradox framework itself and the individual implementations of
the tooling, and that boundary is the same for set theory, coalgebra, and p-adics. This is a synthesis
layer: a validation tool, a unit test to represent that concept quickly.

Here the dataset is the leaf-free polynomial functor `idPF_Coalgebra`: its W-type (`QPF.Fix`, μ) is empty and
choice-free, while its M-type (`QPF.Cofix`, ν) is inhabited and carries choice inherited from Mathlib, with
choice entering exactly on the non-well-founded, self-referential side.

*Editorial addendum (Claude):* that choice on the ν side is inherited from Mathlib's M-type machinery,
not a necessity — for a polynomial functor like `idPF_Coalgebra` the final coalgebra is constructible choice-free
in principle (Ahrens–Capriotti–Spadotti — their construction needs only function extensionality,
which Lean has; only their uniqueness half uses univalence). In the finite-powerset case — the
non-polynomial one — the literature pins each presentation: full AC for the set-quotient, countable
choice together with LLPO for Worrell's (ω+ω)-limit. **The CHOICE half is a fact about those
constructions rather than a necessity result** — Veltri's own preferred coinductive construction
(his Theorem 2) needs neither choice nor LLPO. The LLPO half is different: that one he does prove
necessary, injectivity of the
canonical algebra implying LLPO outright and being equivalent to it under countable choice (Veltri,
FSCD 2021). So the necessity in that paper is of a logic taboo, not of choice.
-/

section PurityCheck
-- Split footprint, and the split is meaningful:
--   fix_isEmpty (μ is empty)        : [propext, Quot.sound]                     — CHOICE-FREE
--   cofix_nonempty (ν is inhabited) : [propext, Classical.choice, Quot.sound]  — choice-carrying
--   categorical_fork_strict         : inherits Classical.choice from cofix_nonempty
-- The well-founded (inductive) side is constructive; the non-well-founded (coinductive) side carries
-- Classical.choice — but as a Mathlib artifact, NOT a necessity: for a polynomial functor like idPF_Coalgebra the
-- final coalgebra (M-type) is constructible choice-free in principle (Ahrens–Capriotti–Spadotti,
-- TLCA 2015, who build it as an ω-limit; the construction needs only funext, univalence entering
-- only at their uniqueness result; Lean has funext). For Lean's Axiom-K setting the closer
-- citation is **Altenkirch–Ghani–Hancock–McBride–Morris, *Indexed Containers* (JFP 25, 2015)**,
-- which ACS themselves point at (§1.1) and generalize "to the whole of HoTT". **The full
-- three-way setting comparison is in `ZeroParadox/Computability/ChoicePurityInvariant.lean` —
-- read it there, not here.** In the finite-powerset case — the non-polynomial one — the literature
-- pins each presentation: full AC for the set-quotient, countable choice together with LLPO for
-- Worrell's limit. The CHOICE half is a fact about those constructions, not a necessity (his own
-- preferred coinductive construction needs neither). The LLPO half he does prove necessary:
-- injectivity of `alg_Vω` implies LLPO outright and is equivalent to it under countable choice.
-- The fork spine
-- (`ZeroParadox.fork_collapse_iff`) is fully choice-free. See `ZeroParadox/AxiomProfile.lean`.
#print axioms fix_isEmpty
#print axioms cofix_nonempty
#print axioms categorical_fork_strict

/- **M3 metric — the fork choice discriminator (lake build, 2026-06-27).** The per-side footprint is
   a genuine SPLIT, and that split is the measured invariant of the fork: the μ (initial-algebra,
   well-founded) side `fix_isEmpty` is choice-free `[propext, Quot.sound]`, while the ν (final-coalgebra,
   non-well-founded) side `cofix_nonempty` carries `[propext, Classical.choice, Quot.sound]`;
   `categorical_fork_strict` inherits ν's choice. So choice is the discriminator between the two ends of
   the fork at this abstract polynomial-functor level. (Contrast M1: at the concrete Mathlib-category
   realization the analogous split is invisible — every functor is uniformly choice-carrying because the
   library proves it with choice. The ν choice here is likewise a Mathlib M-type artifact, not a
   necessity — Ahrens–Capriotti–Spadotti, TLCA 2015 — so the discriminator is real but its structural
   status is fenced. **Do NOT cite Veltri here**: his subject is the finite-powerset functor, which is
   not polynomial, and he cites ACS for the polynomial case himself. He is apt only for the
   finite-powerset claims above.) -/
end PurityCheck

end ZeroParadox
