import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Grade
import Mathlib.Tactic

/-!
# ZP-H Extension: Power Set Lattice as Structural Floor Witness

The structural floor class is an ORDER property: the bottom has a first step, `HasFirstStep` (`⊥ ⋖ a`,
AX-B1, `ZeroParadox/Reals/OrderedField.lean`). Density rules one out at every element, the bottom
included; `axb1_fails_everywhere_iff_dense` quantifies over all elements, so one element without a
first step does not make an order dense. In `Finset α` under inclusion, ∅ is covered by every
singleton (the `example` after T-PS6). Statement: CARRIER, the depth chart. Every nonempty finset has
cardinality ≥ 1 (`ps_nonempty_depth_pos`), so ∅ is no limit of nonempty finsets in that depth. That
does not decide the class: ℚ₂'s 0 is the limit of the doubling orbit, not reached in finite time, where
ℕ's 0 is (`floor_reach_separates_mu_nu`); `LT ℚ_[2]` does not synthesize (`ZeroParadox/BottomCannotBe.lean`
§ ROLE), so a cover there is not stated. Proved independently of ZPA–ZPH: the same order property.

## Engineer's Take

The power set lattice is the most elementary member of the structural floor class. Every
mathematician knows it. ∅ is isolated from all nonempty sets by exactly one element — you
cannot have half an element. The gap is not metric or topological in the usual sense; it is
combinatorial. Cardinality lives in ℕ, and there is no natural number strictly between 0 and 1.
That is the entire proof. The rest is scaffolding to make the statement precise.
-/

namespace ZeroParadox

variable {α : Type*}

set_option maxHeartbeats 400000

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

/-! ## T-PS6: A depth threshold above ∅

Depth chart: a threshold (1) below which no nonempty finset can fall. This is not the class
condition, which is the order property, a first step off ∅; the `example` after this theorem
measures that.
-/

theorem ps_structural_floor :
    ∃ gap : ℕ, 0 < gap ∧ ∀ A : Finset α, A ≠ ∅ → gap ≤ psDepth A := by
  exact ⟨1, Nat.one_pos, fun A hA => ps_nonempty_depth_pos A hA⟩

-- `Statement:` ∅, ⊥ of `Finset α` under inclusion, is covered by every singleton (Mathlib's
-- `Finset.empty_covBy_singleton`); for inhabited `α` that is `HasFirstStep ∅`
-- (`ZeroParadox/Reals/OrderedField.lean`).
example : ∀ a : α, (∅ : Finset α) ⋖ {a} := Finset.empty_covBy_singleton

/-- Statement: a descending orbit of finsets that shrinks at every nonempty step (removing an element
    is one) is `∅` from step `(S 0).card` on. Analogs: `descent_with_strict_steps_reaches_floor`
    (`ZeroParadox/Order/WellFoundedObstruct.lean`) and Mathlib's `Finset.lt_wf`; adds `N ≤ (S 0).card`. -/
theorem ps_descent_reaches_floor (S : ℕ → Finset α) (hsub : ∀ k, S (k + 1) ⊆ S k)
    (hstrict : ∀ k, S k ≠ ∅ → S (k + 1) ≠ S k) :
    ∃ N, N ≤ (S 0).card ∧ ∀ k, N ≤ k → S k = ∅ := by
  -- via cardinality: Mathlib's `Finset.subset_empty` measures `Classical.choice`, this route does not
  have sub_empty : ∀ {A : Finset α}, A ⊆ ∅ → A = ∅ := fun hA => by
    have h := Finset.card_le_card hA
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (Nat.le_zero.mp h)
  have key : ∀ k, S k = ∅ ∨ (S k).card + k ≤ (S 0).card := by
    intro k
    induction k with
    | zero => exact Or.inr (Nat.le_of_eq (Nat.add_zero _))
    | succ k ih =>
      rcases ih with h0 | h0
      · have hs := hsub k
        rw [h0] at hs
        exact Or.inl (sub_empty hs)
      · rcases Nat.eq_zero_or_pos (S k).card with hc | hc
        · have hs := hsub k
          rw [Finset.card_eq_zero.mp hc] at hs
          exact Or.inl (sub_empty hs)
        · have hk : S k ≠ ∅ := fun e => by
            rw [e, Finset.card_empty] at hc
            exact lt_irrefl 0 hc
          have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub k, hstrict k hk⟩)
          exact Or.inr (by omega)
  have stay : ∀ k, S k = ∅ → ∀ j, S (k + j) = ∅ := by
    intro k hk j
    induction j with
    | zero => exact hk
    | succ j ih =>
      have hs := hsub (k + j)
      rw [ih] at hs
      exact sub_empty hs
  have hN : S (S 0).card = ∅ := by
    rcases key (S 0).card with h | h
    · exact h
    · exact Finset.card_eq_zero.mp (by omega)
  refine ⟨(S 0).card, le_rfl, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact stay _ hN j

/-! ## Purity check -/

section PurityCheck
#print axioms ps_bot_depth
#print axioms ps_nonempty_depth_pos
#print axioms ps_depth_zero_iff_empty
#print axioms ps_empty_not_limit
#print axioms ps_no_subgap
#print axioms ps_structural_floor
#print axioms ps_descent_reaches_floor
end PurityCheck

end ZeroParadox
