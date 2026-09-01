-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCorners
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Order.Snap
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Bridge: the four corners are the corners of the tower to ω (shared-shape correspondence)

## Engineer's Take

Looking at it from the top down, this is the very same single point versus an infinite field that we started
out looking at. These four corners are the corners of the whole tower to omega, and the inversion corner is
the framework's own bridge map. The one direction we cannot reverse is the definition of the snap, and it is
the same wall we kept hitting from the start.

This landed when I looked at it from the top down and saw the same single point versus infinite field we
started with. Sometimes it helps to work through this from the ground up. Much of what is here re-derives
results the framework already has, and that is fine. The movement of the thought process itself was what I
needed.

---


## Formal Overview
The four corners of the pole carry the same SHAPE as the corners of the tower — a correspondence, never
a cross-type identity. Argument, fences and structure: `ZeroParadox/Valuation/PoleCornersBridge.md`.
-/

namespace ZeroParadox

open OnePoint

/-! ### § I. The pole embedding into the 2-adic Riemann sphere -/

/-- Embed the abstract pole-pair into the 2-adic Riemann sphere: `zero ↦ 0`, `infty ↦ ∞`. The floor and
its antipode; the two poles the whole four-corner structure is about. -/
noncomputable def poleToSphere : Pole → Sphere
  | Pole.zero => OnePoint.some (0 : ℚ_[2])
  | Pole.infty => (∞ : Sphere)

@[simp] theorem poleToSphere_zero : poleToSphere Pole.zero = OnePoint.some (0 : ℚ_[2]) := rfl

@[simp] theorem poleToSphere_infty : poleToSphere Pole.infty = (∞ : Sphere) := rfl

/-! ### § II. The inversion corner IS the Riemann-sphere inversion -/

/-- **The inversion corner is `z ↦ 1/z`.** Under the pole embedding, the abstract `swap` corner commutes
with the Riemann-sphere inversion `rInv`: `poleToSphere (swap p) = rInv (poleToSphere p)`. The four-corner
inversion is the framework's own `rInv` — the map that, on the tower side (`cnfToZp2`), reverses ordinal
ascent into 2-adic descent. The corner that connects the two poles is the map that connects the tower to the
tree. -/
theorem swap_is_rInv (p : Pole) : poleToSphere (Pole.swap p) = rInv (poleToSphere p) := by
  cases p <;> simp [poleToSphere, Pole.swap, rInv_zero, rInv_infty]

/-- The floor corner and the infinity corner are genuinely the two swapped poles: `swap` moves the zero
corner to `∞` and the infinity corner to `0`, exactly as `rInv_swaps` does on the sphere. -/
theorem corners_are_the_swapped_poles :
    poleToSphere (Pole.swap Pole.zero) = (∞ : Sphere) ∧
      poleToSphere (Pole.swap Pole.infty) = OnePoint.some (0 : ℚ_[2]) := by
  constructor <;> rfl

/-! ### § III. The capstone — a single point versus an infinite field, at both poles at once -/

/-- **The capstone (co-witnessing, shared-shape).** The structure the whole pivot turned on: **two single,
distinct points — the poles — swapped by the inversion, sitting in an infinite field.** That is the "single
point versus infinite field" seen at BOTH ends at once. On the 2-adic sphere: `0` (the floor; the tower's
2-adic limit, `tower_converges_to_zero`) and `∞` (its inversion; the summit side) are the two single points;
`rInv` swaps them; and `ℚ_[2]` is the infinite field between. Via `cnfToZp2` (`CnfBridge`) the **top-down**
view — summit `ε₀` (a single point), tree boundary `ℤ₂` (a field) — is the **inverted image** of the
**bottom-up** view — floor `0` (a single point), its field. One construction, two ends, joined by the map,
never by `=`: `ε₀ = 0` stays a type boundary (`cnf_bridge_type_boundary`). The point and the field are the
same object read up or down; the inversion is what turns each into the other. -/
theorem point_and_field_at_the_poles :
    poleToSphere Pole.zero ≠ poleToSphere Pole.infty ∧
      rInv (poleToSphere Pole.zero) = poleToSphere Pole.infty ∧
      rInv (poleToSphere Pole.infty) = poleToSphere Pole.zero ∧
      Infinite ℚ_[2] := by
  refine ⟨?_, ?_, ?_, inferInstance⟩
  · simp [poleToSphere]
  · simp [poleToSphere, rInv_zero]
  · simp [poleToSphere, rInv_infty]

/-! ### § IV. The forbidden direction is the snap (co-witness, shared-shape) -/

/-- **The irreversible direction is the snap.** The two proved one-way facts, sharing one shape:
* **corner side** — `cornerZero` is not injective: falling to a pole forgets the origin, there is no inverse
  (the forbidden transition among the four corners is *un-collapsing*);
* **snap side** — `t_snap_irreversible`: once `x ≼ y` with `x ≠ y`, no join from `y` returns to `x` (the
  forbidden transition of the snap is *returning to the same ⊥*).

These are the same one-way shape on two structures. It is the wall the whole abstraction is bounded by:
everything reversible is free (the ν-symmetries `cornerId`, `swap`); the one thing you cannot reverse is the
fall to the floor. The forbidden direction is not a gap — it is the definition of the snap. Co-witnessed,
never a cross-type `=`. -/
theorem irreversible_direction_is_the_snap {L : Type*} [ZPSemilattice L] {x y : L}
    (hle : ZPSemilattice.join x y = y) (hne : x ≠ y) :
    ¬ Function.Injective Pole.cornerZero ∧ ¬ ∃ z : L, ZPSemilattice.join y z = x :=
  ⟨Pole.cornerZero_not_injective, t_snap_irreversible hle hne⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms poleToSphere
#print axioms swap_is_rInv
#print axioms corners_are_the_swapped_poles
#print axioms point_and_field_at_the_poles
#print axioms irreversible_direction_is_the_snap
end PurityCheck
