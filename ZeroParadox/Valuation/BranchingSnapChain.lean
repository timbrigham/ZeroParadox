import ZeroParadox.Valuation.Padic
import ZeroParadox.Valuation.PoleCorners
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The single chain: branching → disconnectedness → forbidden return → the snap

## Engineer's Take

Trees grow outward and upward toward infinity, and towers grow only upward until infinity. This tower is
tied to where it branches into infinity, and the behavior there is tied directly to the forbidden state
behind the snap. The branching into infinity is exactly what forbids the return, so the wall is the
fanning-out itself.

---

## Formal Overview (AI-assisted)

Assembles into **one chain** the fact that the 2-adic *branching into infinity* is what forbids the snap's
return. The abstract root, `disconnectedness_forbids_path`: **in ANY totally disconnected space, no
continuous path joins two distinct points** — a connected `[0,1]` maps to a single point, so it cannot move
between them. That is the geometric source of the forbidden direction, stated at full generality.

`branching_is_the_snap_wall` instantiates it on `Q₂`, tying the three faces of one geometry:
* **branching** — `TotallyDisconnectedSpace Q₂`, i.e. the nested clopen-ball hierarchy `B(0, 2⁻ⁿ) ↘ {0}`,
  which is exactly the tree `PadicTree`;
* **the forbidden return** — no continuous path from `x ≠ 0` back to the floor `0` (this is ZP-B's
  `c3_irreversible`, re-derived here from the abstract root so the dependency is visible in one place);
* **the snap's one-way shape** — `cornerZero` is not injective (the collapse to a pole forgets its origin;
  co-witnessed with the algebraic `t_snap_irreversible` in `PoleCornersBridge`).

So the branching does both jobs at once: it opens the clopen gap that lets the snap jump, and the same total
disconnectedness forbids the continuous return. Contrast — ℝ is *connected*, so ZP-F's `f_snap_impossible`:
no gap, no snap. **Connected → no snap; branching → a snap that cannot reverse.** The wall behind the snap
and the branching into infinity are one fact: total disconnectedness, read as an obstruction one way and a
gap the other. No cross-type `=` anywhere — the faces are connected by shared geometry, co-witnessed.
-/

namespace ZeroParadox

/-- **The abstract root of the wall.** In any totally disconnected space, no continuous path joins two
distinct points: the connected image of `[0,1]` collapses to a single point. This is `c3_irreversible`'s
content at full generality — the branching (total disconnectedness) forbids the transition. -/
theorem disconnectedness_forbids_path {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    {x y : X} (hxy : x ≠ y) :
    ¬ ∃ γ : C(Set.Icc (0 : ℝ) 1, X), γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y := by
  rintro ⟨γ, h0, h1⟩
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hsingl : (Set.range (γ : Set.Icc (0 : ℝ) 1 → X)).Subsingleton :=
    isTotallyDisconnected_of_totallyDisconnectedSpace Set.univ (Set.range _) (Set.subset_univ _)
      (isPreconnected_range γ.continuous)
  have hpt := hsingl (Set.mem_range_self ⟨0, by norm_num⟩) (Set.mem_range_self ⟨1, by norm_num⟩)
  rw [h0, h1] at hpt
  exact hxy hpt

/-- **The chain, in one statement.** Branching (total disconnectedness = the clopen-ball tree `PadicTree`)
→ the forbidden return (no continuous path from `x ≠ 0` to the floor `0`) → the snap's one-way shape (the
corner collapse `cornerZero` is not injective). One geometry, three faces; the branching-into-infinity is
what makes the return forbidden. -/
theorem branching_is_the_snap_wall (x : Q₂) (hx : x ≠ 0) :
    TotallyDisconnectedSpace Q₂ ∧
      (¬ ∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂), γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0) ∧
      ¬ Function.Injective Pole.cornerZero :=
  ⟨inferInstance, disconnectedness_forbids_path hx, Pole.cornerZero_not_injective⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms disconnectedness_forbids_path
#print axioms branching_is_the_snap_wall
end PurityCheck
