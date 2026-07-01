-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import ZeroParadox.ZPP_Coalgebra
import ZeroParadox.ZPH_MC1_TC26

/-!
# ZP-H MC-1 tree test TC32: the root cut is binary in arity, not graded

This module sharpens the root-cut dichotomy of `ZPH_MC1_TC26.lean` into a statement about the
**number** of recursive positions. TC26 established the dichotomy on the two boundary cases:

* `constPF A` — child type `PEmpty`, **zero** recursive positions: `Fix ≃ Cofix` (a seam);
* `idPF`      — child type `PUnit`, **one** recursive position: `IsEmpty (Fix ≃ Cofix)` (strict).

The open question this file closes: is the strict side graded by arity, or is it triggered by mere
*presence* of a recursive position? We take the **binary-tree polynomial functor**

  `binPF := ⟨Unit, fun _ => Bool⟩`

— head type `Unit`, child type `Bool`, i.e. **two** recursive positions per node and **no leaf
constructor**. The pre-registered NO-GO conjecture was that two positions might admit a *finite* full
binary tree (a bounded-depth tree), making `Fix` inhabited and grading the dichotomy by arity.

The NO-GO is refuted; the GO holds. With no leaf constructor every node still demands children (now
two of them), so no well-founded finite tree exists — the same base-case obstruction as the unary
`idPF`, unchanged by doubling the arity:

- `binFix_isEmpty`   : `IsEmpty (QPF.Fix binPF.Obj)`     (μ side: still empty)
- `binCofix_nonempty`: `Nonempty (QPF.Cofix binPF.Obj)`  (ν side: still inhabited)
- `binPF_fork_strict`: `IsEmpty (Fix) ∧ Nonempty (Cofix)` (the strict side, mirroring
  `ZeroParadox.ZPP.categorical_fork_strict` for `idPF`)
- `binPF_no_seam`    : `IsEmpty (Fix binPF.Obj ≃ Cofix binPF.Obj)`

The capstone `arity_collapse` records the trichotomy of child types `{empty, one, two}` collapsing to
the **binary** dichotomy `{no recursive position ⇒ seam | ≥ 1 recursive position ⇒ strict}`: the
zero-position `constPF Unit` seams, while both the one-position `idPF` and the two-position `binPF` are
strict. The cut is presence-vs-absence, not multiplicity.

## Formal Overview (AI-assisted)

The μ-emptiness argument is the leaf-free induction of `ZeroParadox.ZPP.fix_isEmpty`, generalised
from `PUnit` to `Bool` children: `Fix.ind` reduces emptiness to: for every `x : binPF.Obj (Fix …)`,
the children satisfy `False` — which `liftp_iff` unpacks to a child predicate that we evaluate at one
concrete child (`true : Bool`), contradiction. Doubling the child type changes nothing because the
argument needs only *one* child to derive the contradiction. The ν-inhabitedness is one corecursion
from the single head shape, exactly as for `idPF`. `binPF_no_seam` is the TC26 transport argument:
an equivalence would carry the ν inhabitant into the empty μ.

What is PROVED is exactly the four theorems and the capstone bundle below. The reading of "two
positions behaves like one" as a confirmation that the framework's root cut is binary (a structural
fact about presence of self-reference, not its count) is the interpretation; the Lean content is the
emptiness/inhabitedness pair for the arity-two functor and its juxtaposition with the arity-zero and
arity-one cases.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH.TC32

open QPF

set_option maxHeartbeats 400000

/-- The **binary-tree** polynomial functor: head type `Unit`, child type `Bool` (**two** recursive
positions, **no** leaf constructor). Its action is `binPF.Obj X ≅ X × X`. -/
def binPF : PFunctor.{0, 0} := ⟨Unit, fun _ => Bool⟩

/-- `binPF.Obj` is a QPF, with `abs`/`repr` the identity (it is already polynomial). -/
instance : QPF binPF.Obj where
  P := binPF
  abs := fun x => x
  repr := fun x => x
  abs_repr := fun _ => rfl
  abs_map := fun _ _ => rfl

/-! ### μ side: `Fix binPF.Obj` is empty -/

/-- **μ is empty.** The initial algebra of the leaf-free **binary** functor has no element: every
node demands two children with no base case, so no well-founded finite tree exists. This is the same
obstruction as `ZeroParadox.ZPP.fix_isEmpty` (unary `idPF`); the extra child position does not create
a base case. The contradiction is derived from a single child (`true`). -/
theorem binFix_isEmpty : IsEmpty (Fix binPF.Obj) :=
  ⟨fun x => Fix.ind (fun _ => False) (fun y hy => by
      rw [liftp_iff] at hy
      obtain ⟨_, f, _, hf⟩ := hy
      exact hf true) x⟩

/-! ### ν side: `Cofix binPF.Obj` is inhabited -/

/-- **ν is inhabited.** The final coalgebra contains the infinite self-referential full binary tree,
built by corecursion from the single head shape that unfolds to two copies of itself. -/
theorem binCofix_nonempty : Nonempty (Cofix binPF.Obj) :=
  ⟨Cofix.corec (fun _ : Unit => (⟨(), fun _ => ()⟩ : binPF.Obj Unit)) ()⟩

/-! ### The strict fork and the absence of a seam -/

/-- **The strict fork for the arity-two functor.** Exactly like `idPF` (arity one): the least fixed
point is empty while the greatest is inhabited. Doubling the recursive positions does not soften the
fork. -/
theorem binPF_fork_strict :
    IsEmpty (Fix binPF.Obj) ∧ Nonempty (Cofix binPF.Obj) :=
  ⟨binFix_isEmpty, binCofix_nonempty⟩

/-- For the two-recursive-position functor `binPF`, the fixed points are NOT equivalent: an
equivalence would carry the inhabitant of `Cofix binPF.Obj` (ν) back into the empty `Fix binPF.Obj`
(μ). Mirrors `ZeroParadox.ZPH.TC26.idPF_no_seam`. -/
theorem binPF_no_seam : IsEmpty (Fix binPF.Obj ≃ Cofix binPF.Obj) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨c⟩ := binCofix_nonempty
  exact binFix_isEmpty.false (e.symm c)

/-- **Arity collapse: the root cut is binary, not graded.** The trichotomy of child-type sizes
`{empty, one, two}` collapses to the binary dichotomy `{no recursive position ⇒ seam | ≥ 1 recursive
position ⇒ strict}`:

* `constPF Unit` (child `PEmpty`, **zero** positions): `Nonempty (Fix ≃ Cofix)` — a seam;
* `idPF`         (child `PUnit`,  **one**  position):  `IsEmpty (Fix ≃ Cofix)` — strict;
* `binPF`        (child `Bool`,   **two**  positions): `IsEmpty (Fix ≃ Cofix)` — strict.

The one-position and two-position cases agree (both strict), so the discriminator is presence vs
absence of a recursive position, not its multiplicity. -/
theorem arity_collapse :
    Nonempty (Fix (ZeroParadox.ZPH.TC26.constPF Unit).Obj ≃
        Cofix (ZeroParadox.ZPH.TC26.constPF Unit).Obj) ∧
    IsEmpty (Fix ZeroParadox.ZPP.idPF.Obj ≃ Cofix ZeroParadox.ZPP.idPF.Obj) ∧
    IsEmpty (Fix binPF.Obj ≃ Cofix binPF.Obj) :=
  ⟨⟨(ZeroParadox.ZPH.TC26.root_seam : Fix (ZeroParadox.ZPH.TC26.constPF Unit).Obj ≃ _)⟩,
    ZeroParadox.ZPH.TC26.idPF_no_seam, binPF_no_seam⟩

section PurityCheck
-- Measured footprint (lake build, v4.30.0-rc2) — the same μ-choice-free / ν-choice split as
-- ZPP_Coalgebra and TC26:
--   binFix_isEmpty    (μ empty)     : [propext, Quot.sound]                       — CHOICE-FREE
--   binCofix_nonempty (ν inhabited) : [propext, Classical.choice, Quot.sound]     — Mathlib M-type
--   binPF_fork_strict               : [propext, Classical.choice, Quot.sound]     — inherits ν
--   binPF_no_seam                   : [propext, Classical.choice, Quot.sound]     — inherits ν
--   arity_collapse                  : [propext, Classical.choice, Quot.sound]
-- The arity-two μ side is choice-free exactly as the arity-one (idPF) μ side: doubling the recursive
-- positions changes neither the emptiness nor its axiom footprint. The ν choice is the Mathlib
-- corecursion artifact, not a necessity (polynomial-functor final coalgebra is constructible
-- choice-free in principle; Veltri, FSCD 2021).
#print axioms binFix_isEmpty
#print axioms binCofix_nonempty
#print axioms binPF_fork_strict
#print axioms binPF_no_seam
#print axioms arity_collapse
end PurityCheck

end ZeroParadox.ZPH.TC32
