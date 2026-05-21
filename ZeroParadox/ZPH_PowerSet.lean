import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# ZP-H Extension: Power Set Lattice as Structural Floor Witness

This file verifies that the power set lattice 𝒫(S) — represented via `Finset α` — is a
member of the structural floor class: the bottom element (∅) is not a limit point of the
non-bottom elements.

The argument is elementary. Any nonempty finset has cardinality ≥ 1, so there is a discrete
gap of size 1 between ∅ and every nonempty set. No sequence of nonempty finsets can converge
to ∅ in the cardinality depth metric. The bottom is a structural floor, not a limit.

This is proved independently of ZPA–ZPH to demonstrate that the structural floor property
holds for its own reasons in this domain — the same class condition, a different witness.

## Engineer's Take

The power set lattice is the most elementary member of the structural floor class. Every
mathematician knows it. ∅ is isolated from all nonempty sets by exactly one element — you
cannot have half an element. The gap is not metric or topological in the usual sense; it is
combinatorial. Cardinality lives in ℕ, and there is no natural number strictly between 0 and 1.
That is the entire proof. The rest is scaffolding to make the statement precise.
-/

namespace ZeroParadox.ZPH_PowerSet

variable {α : Type*}

/-! ## Depth structure -/

/-- The depth of a finset is its cardinality. ∅ has depth 0; every nonempty set has depth ≥ 1. -/
def psDepth (A : Finset α) : ℕ := A.card

/-! ## T-PS1: ∅ has depth 0 -/

theorem ps_bot_depth : psDepth (∅ : Finset α) = 0 := by
  simp [psDepth]

/-! ## T-PS2: The discrete gap — any nonempty finset has depth ≥ 1 -/

theorem ps_nonempty_depth_pos (A : Finset α) (hA : A ≠ ∅) : 0 < psDepth A := by
  simp [psDepth, Finset.card_pos, Finset.nonempty_iff_ne_empty.mpr hA]

/-! ## T-PS3: Depth 0 iff empty — nothing sits between ∅ and depth 1 -/

theorem ps_depth_zero_iff_empty (A : Finset α) : psDepth A = 0 ↔ A = ∅ := by
  simp [psDepth, Finset.card_eq_zero]

/-! ## T-PS4: The floor theorem — ∅ is not a limit of nonempty finsets

Any sequence of nonempty finsets has strictly positive depth at every step.
∅ cannot appear as a limit because the depth gap of 1 is never closed.
-/

theorem ps_empty_not_limit (S : ℕ → Finset α) (hS : ∀ n, S n ≠ ∅) :
    ∀ n, 0 < psDepth (S n) := by
  intro n; exact ps_nonempty_depth_pos (S n) (hS n)

/-! ## T-PS5: No first step below the gap

There is no finset A satisfying A ≠ ∅ and psDepth A < 1.
The gap between ∅ and the simplest nonempty set is exactly 1 — a singleton.
-/

theorem ps_no_subgap (A : Finset α) (hA : A ≠ ∅) : ¬ psDepth A < 1 := by
  exact Nat.not_lt.mpr (ps_nonempty_depth_pos A hA)

/-! ## T-PS6: The class condition

∅ is not a limit point of the non-empty finsets: there exists a depth threshold (1)
below which no nonempty finset can fall. This is the structural floor property.
-/

theorem ps_structural_floor :
    ∃ gap : ℕ, 0 < gap ∧ ∀ A : Finset α, A ≠ ∅ → gap ≤ psDepth A := by
  exact ⟨1, Nat.one_pos, fun A hA => ps_nonempty_depth_pos A hA⟩

/-! ## Purity check -/

section PurityCheck
#print axioms ps_bot_depth
#print axioms ps_nonempty_depth_pos
#print axioms ps_depth_zero_iff_empty
#print axioms ps_empty_not_limit
#print axioms ps_no_subgap
#print axioms ps_structural_floor
end PurityCheck

end ZeroParadox.ZPH_PowerSet
