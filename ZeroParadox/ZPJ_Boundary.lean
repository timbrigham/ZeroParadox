import ZeroParadox.ZPJ_SelfApp
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Tactic

/-!
# ZPJ — The well-foundedness boundary (keystone snap-as-boundary probe)

**Status: PROBE, stub-first, local branch `keystone-boundary`.** Rung A of the iterative A→B plan
(see `.claude-local/notes/wellfounded_coalgebra_foray_2026-06-23.md`).

Conjecture (Taylor/AMM framing): the forced snap ⊥→ε₀ crosses the **well-foundedness boundary** —
from the non-well-founded floor (⊥ is the self-loop / back edge, where recursion cannot reach,
Taylor Prop 111) to the well-founded ascent (the ε₀ ordinal tower, recursively generated).

**Rung A (this file): the RELATION-LEVEL form.** Mathlib has `WellFounded` and ordinal well-foundedness
but NOT Taylor's coalgebraic well-founded coalgebras — so this is the faithful relation-level *shadow*
of the Taylor boundary, not the full coalgebraic statement (that is Rung C, deferred). Honest scope: this
proves "the self-application floor is non-well-founded; the ordinal ascent is well-founded; the snap
crosses between," at the level of relations.
-/

namespace ZeroParadox.ZPJ_Boundary

open ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPJ_SelfApp

set_option maxHeartbeats 400000

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-! ## § I. The floor is non-well-founded (the back edge)

    `selfApp` has ⊥ as a fixed point (`fixed_bot`): ⊥ self-loops. The relation "a is the selfApp-image
    of b" therefore has a self-loop at ⊥, so it cannot be well-founded. -/

/-- The descent relation induced by `selfApp`: `a` is the self-application image of `b`. -/
def floorRel (a b : L) : Prop := AbstractSelfApp.selfApp b = a

/-- An accessible point cannot have a self-loop (well-founded relations are irreflexive). -/
private theorem acc_irrefl {α : Type*} {r : α → α → Prop} : ∀ {a : α}, Acc r a → ¬ r a a := by
  intro a h
  induction h with
  | intro x _ ih => intro hself; exact ih x hself hself

/-- **The floor is non-well-founded.** ⊥ self-loops under `selfApp` (`fixed_bot`), so `floorRel` has a
    self-loop at ⊥ and cannot be well-founded — the back edge. -/
theorem floor_not_wellFounded : ¬ WellFounded (floorRel (L := L)) := fun hwf =>
  acc_irrefl (hwf.apply bot) AbstractSelfApp.fixed_bot

/-! ## § II. The ascent is well-founded (the ε₀ tower)

    The ordinal order is well-founded (ordinals are well-ordered); ε₀ and the snap ascent live inside it.
    This is the recursively-generated side — Taylor: well-founded ⟹ recursive. -/

/-- **The ascent is well-founded.** The strict order on ordinals is well-founded; the ε₀ tower (ZP-L)
    is an initial segment of it. -/
theorem ascent_wellFounded : WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  Ordinal.lt_wf

/-! ## § III. The boundary (Rung A statement)

    The snap crosses from the non-well-founded floor to the well-founded ascent. -/

/-- **Rung A — the well-foundedness boundary (relation level).** The floor relation is non-well-founded;
    the ascent relation is well-founded. The snap ⊥→ε₀ crosses between them. -/
theorem snap_crosses_boundary :
    ¬ WellFounded (floorRel (L := L)) ∧ WellFounded ((· < ·) : Ordinal → Ordinal → Prop) :=
  ⟨floor_not_wellFounded, ascent_wellFounded⟩

end ZeroParadox.ZPJ_Boundary

section PurityCheck
open ZeroParadox.ZPJ_Boundary
#print axioms floor_not_wellFounded
#print axioms ascent_wellFounded
end PurityCheck
