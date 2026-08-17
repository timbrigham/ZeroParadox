-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import ZeroParadox.Valuation.PoleCorners
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The single chain: branching → disconnectedness → the forbidden return

## Engineer's Take

Trees grow outward and upward toward infinity, and towers grow only upward until infinity. This tower is
tied to where it branches into infinity, and the behavior there is tied directly to the forbidden state
behind the snap. The branching into infinity is exactly what forbids the return, so the wall is the
fanning-out itself.

This was me tying the tower's branching into infinity to the snap's forbidden return. Sometimes it helps to
work through this from the ground up. Much of what is here re-derives results the framework already has, and
that is fine. The movement of the thought process itself was what I needed.

## Formal Overview (AI-assisted)
`Reading:` CARRIER — one chain over `Q₂`: total disconnectedness is an obstruction one way and a gap the other.
`disconnectedness_forbids_path` states the root at full generality; `branching_is_the_snap_wall` instantiates its
three faces. ⚠ **A clopen gap is not a first step.** ZP-F proves *ordered field → no first step*, obstruction
DENSITY (`ZeroParadox.axb1_fails_everywhere_iff_dense`, no topology in it); the topological half is
`ZeroParadox.real_no_snap`. Neither yields a first step — that is AX-B1, per `ZeroParadox/Valuation/Padic.lean`.
-/

namespace ZeroParadox

/-- **The abstract root of the wall.** `Statement:` CARRIER — in any totally disconnected space, no
continuous path joins two distinct points: the connected image of `[0,1]` collapses to a single point.
This is `c3_irreversible`'s content at full generality; the branching forbids the transition. -/
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

/-- **The chain, in one statement.** `Statement:` CARRIER — three conjuncts on `Q₂`: branching (total
disconnectedness, realized as the clopen-ball tree `PadicTree`), the forbidden return (no continuous path
from `x ≠ 0` to the floor `0`), and the snap's one-way shape (the corner collapse `cornerZero` is not
injective). One geometry, three faces; the branching is what makes the return forbidden. -/
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
