/-
# Self-Closure Obstructions: the wall-side mirror of the diagonal fixed point (experimental probe)

`AbstractSelfApp` (`ZeroParadox/Computability/SelfApp.lean`) abstracts the FIXED POINT — the
self-application that closes on ⊥. This file abstracts its OBSTRUCTION. The walls of the framework's
Boundary Map (`SNAP.md`) are not scattered: they all stand at the same self-referential locus (the
floor, where ⊥ lives), and they sort by *which closure fails* into three shapes (`ClosureShape`):

* `selfApplication`   — a structure cannot name/contain itself (Cantor/diagonal from above, or
                        Foundation/well-founded from below). The wall of the fixed-point face.
* `limitFromBelow`    — a structure cannot reach its own floor/limit by its internal means (density;
                        a notation system that cannot name its own limit). The wall of the limit face.
* `crossFrameIdentity`— two frames cannot be identified as one object. The wall of the seam (MC-1).

A `SelfClosureObstruction` records, per wall, the proposition "the closing operation has a witness"
together with a proof that it does not — drawn from an existing wall theorem, so the classification is
grounded, not asserted. This is an ORGANIZING abstraction, the wall-side mirror of `AbstractSelfApp`;
it does NOT claim the walls are one object — that would be the very cross-frame identity the seam-wall
blocks (MC-1). Shapes 1 and 2 are the walls of ⊥'s two faces (fixed point + limit); shape 3 is the
wall of the seam.

EXPERIMENTAL; physics-silent.
-/
import ZeroParadox.Settheory.Wall
import ZeroParadox.Reals.OrderedField
import ZeroParadox.Valuation.BottomInvariant

set_option maxHeartbeats 400000

namespace ZeroParadox

/-- The closure-shapes the framework's walls sort into (the sort key of the Boundary Map's walls). -/
inductive ClosureShape where
  /-- Shape 1: a structure cannot name/contain itself — Cantor/diagonal from above, or Foundation
      from below. The wall of the fixed-point face. -/
  | selfApplication
  /-- Shape 2: a structure cannot reach its own floor/limit by its internal means — density, or a
      notation system that cannot name its own limit. The wall of the limit face. -/
  | limitFromBelow
  /-- Shape 3: two frames cannot be identified as one object. The wall of the seam (MC-1). -/
  | crossFrameIdentity
  deriving DecidableEq, Repr

/-- A **self-closure obstruction**: the proposition `closable` ("the closing operation has a
    witness") together with the wall `no_closure : ¬ closable`, tagged by its `shape`. The
    wall-side mirror of `AbstractSelfApp`. An organizing abstraction only — the content lives in
    each instance's `closable`/`no_closure`, which reduce to existing wall theorems. -/
structure SelfClosureObstruction where
  shape : ClosureShape
  closable : Prop
  no_closure : ¬ closable

/-! ### NO-GO gauge — what fails to be a `SelfClosureObstruction`?

**Measured 2026-08-09: nothing does.** `closable := False`, `no_closure := id` discharges the
structure for any `shape`, so *"there is an obstruction here"* is inhabited without exhibiting any
obstruction. The structure is a **record of a proof**, not a requirements class: its content is
entirely in *which* `Prop` a given value puts in `closable`.

**So membership is never the claim — the field is.** Cite `obstruction_negation` and its siblings for
their specific `closable`; never *"X is a `SelfClosureObstruction`, therefore X cannot close."* -/

/-- Shape 1a (Cantor/diagonal, `Prop` level — the ENGINE): no proposition is equivalent to its own
    negation. Empty by `negation_no_fixedpoint`. -/
def obstruction_negation : SelfClosureObstruction where
  shape := .selfApplication
  closable := ∃ p : Prop, p ↔ ¬ p
  no_closure := fun ⟨p, hp⟩ => negation_no_fixedpoint p hp

/-- Shape 1b (Foundation/well-founded): no set contains itself. Empty by `no_quine_atom` — the wall
    the Quine atom `⊥ = {⊥}` needs ZF+AFA to cross (Foundation *is* this wall). -/
def obstruction_quine : SelfClosureObstruction where
  shape := .selfApplication
  closable := ∃ x : ZFSet.{0}, x ∈ x
  no_closure := fun ⟨x, hx⟩ => no_quine_atom x hx

/-- Shape 2 (limit from below): the reals have no minimal positive — the floor is unreachable from
    above. Empty by `r_no_minimal_positive`. -/
def obstruction_no_minimal_real : SelfClosureObstruction where
  shape := .limitFromBelow
  closable := ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ε ≤ δ
  no_closure := r_no_minimal_positive

/-- Shape 3 (cross-frame identity — the seam): no measure-preserving map identifies the concentrated
    invariant `δ₀` of the p-adic doubling attractor with the spread uniform invariant of the Markov
    kernel. Empty by `no_mp_attractor_to_markov` (§X). The `closable` proposition is inferred from the
    wall theorem's type. -/
def obstruction_no_comparison : SelfClosureObstruction :=
  { shape := .crossFrameIdentity
    closable := _
    no_closure := no_mp_attractor_to_markov }

/-- The classification is inhabited at every shape: each of the three closure-shapes has at least one
    witnessed obstruction. The classification is inhabited at each of ⊥'s two face-wall shapes (fixed
    point + limit) and its seam-wall shape — the sort into (two faces + seam) is our organizing design,
    not a claim of exhaustiveness. -/
theorem every_shape_witnessed :
    (∃ o : SelfClosureObstruction, o.shape = ClosureShape.selfApplication) ∧
    (∃ o : SelfClosureObstruction, o.shape = ClosureShape.limitFromBelow) ∧
    (∃ o : SelfClosureObstruction, o.shape = ClosureShape.crossFrameIdentity) :=
  ⟨⟨obstruction_negation, rfl⟩, ⟨obstruction_no_minimal_real, rfl⟩, ⟨obstruction_no_comparison, rfl⟩⟩

/-!
## Engineer's Take

This probe maps MC-1 by the obstructions it surfaces. We can't directly view the root cause, and we
read it off the error conditions it creates from the input provided.
-/

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms obstruction_negation
#print axioms obstruction_quine
#print axioms obstruction_no_minimal_real
#print axioms obstruction_no_comparison
#print axioms every_shape_witnessed
end PurityCheck
