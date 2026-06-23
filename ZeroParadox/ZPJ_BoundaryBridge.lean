import ZeroParadox.ZPJ_Boundary
import ZeroParadox.ZPP_Coalgebra

/-!
# ZPJ — The snap-boundary, QPF bridge (best-effort; Rung C-QPF)

## Engineer's Take

This file is a shortcut, a quick representation of the ν versus μ relationship. Mathlib at current does
not currently provide complete Taylor machinery, so we're representing the same premise to the best of
our abilities using indexes. Please take this as an open invitation to expand both the Zero Paradox
project as well as Mathlib as a whole.

---

**Status: PROBE, local branch `keystone-boundary`.** This is the deliberately-scoped "C-QPF" route
(see `.claude-local/notes/wellfounded_coalgebra_foray_2026-06-23.md`).

## What this states
The snap ⊥→ε₀ as the crossing of the well-foundedness boundary, witnessed in **two formalized registers**:

* **Relation / carrier level** (`ZPJ_Boundary`): the self-application floor is non-well-founded (the ⊥
  self-loop, `fixed_bot`); the ordinal ascent is well-founded; on one carrier, the floor is the *sole*
  non-accessible point and every post-snap state is accessible (`snap_crossing`).
* **Categorical level** (`ZPP_Coalgebra`, the ZP-P μ/ν fork): for the leaf-free functor `idPF`, the
  initial algebra (W-type, μ, the well-founded closure) is **empty** and the final coalgebra (M-type, ν,
  the non-well-founded closure) is **inhabited** (`categorical_fork_strict`). The self-referential element
  lives in ν, not μ — the back edge on the non-well-founded side.

`snap_boundary_two_registers` bundles both as the best-effort witness that the snap crosses from the
non-well-founded side to the well-founded side.

## Scope fence — why this is NOT the full Taylor coalgebraic statement (deliberate, tooling-limited)
The **full** Rung C would state this in Taylor's sense: ⊥ is a non-well-founded *coalgebra* (broken-pullback
definition), the ascent is the initial algebra, and the snap is the ν→μ crossing, with the depth result
**well-founded ⟺ recursive** (Taylor's General Recursion Theorem; Taylor Prop 111: well-foundedness is
*necessary* for recursion — the rigorous "you cannot recurse through ⊥"). We do **not** formalize that here,
because Mathlib currently lacks the required machinery:
* the **next-time operator** on subobject lattices (Jacobs) — absent;
* **Pataraia's fixed-point theorem** — absent (Taylor's recursion proof depends on it);
* the **General Recursion Theorem** for well-founded coalgebras — absent.
Building these would be a standalone Lean/Mathlib contribution in its own right. We therefore **cite** the
depth result rather than re-prove it:
* Paul Taylor, *Well-founded coalgebras and recursion* (General Recursion Theorem; Prop 111).
* Adámek–Milius–Moss, *On Well-Founded and Recursive Coalgebras*, 2020 (arXiv:1910.09401)
  (well-founded ⟺ recursive ⟺ morphism to the initial algebra).

## OPEN CONTRIBUTION POINT
Formalizing the full Taylor well-founded-coalgebra theory in Lean — the next-time operator, Pataraia's
fixed-point theorem, and the General Recursion Theorem — would upgrade this best-effort bridge to the full
Rung C, and would be a reusable contribution independent of the Zero Paradox. Contributions welcome; the
precise missing pieces are listed above.
-/

namespace ZeroParadox.ZPJ_BoundaryBridge

open ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPJ_SelfApp ZeroParadox.ZPJ_Boundary ZeroParadox.ZPP

set_option maxHeartbeats 400000

/-- **Best-effort snap-boundary witness (C-QPF).** The snap crosses the well-foundedness boundary,
    witnessed in two registers: the relation/carrier level (`snap_crossing` — floor the sole
    non-accessible point, every post-snap state accessible) and the categorical μ/ν level
    (`categorical_fork_strict` — initial algebra empty, final coalgebra inhabited; the self-referential
    element lives in ν, not μ). The well-founded ⟺ recursive *depth* (Taylor/AMM) is cited, not proved
    here — see the scope fence. -/
theorem snap_boundary_two_registers {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] :
    ((¬ WellFounded (floorRel (L := L)))
        ∧ (¬ Acc phaseRel Phase.floor ∧ ∀ o : Ordinal, Acc phaseRel (Phase.up o)))
      ∧ (IsEmpty (QPF.Fix idPF.Obj) ∧ Nonempty (QPF.Cofix idPF.Obj)) :=
  ⟨⟨floor_not_wellFounded, snap_crossing⟩, categorical_fork_strict⟩

end ZeroParadox.ZPJ_BoundaryBridge

section PurityCheck
open ZeroParadox.ZPJ_BoundaryBridge
#print axioms snap_boundary_two_registers
end PurityCheck
