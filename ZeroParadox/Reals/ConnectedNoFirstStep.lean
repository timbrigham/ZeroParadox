import ZeroParadox.Reals.OrderedField
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Real.Lemmas

set_option maxHeartbeats 400000

/-!
# Connectedness and the first step on a linear order with its order topology

A cover `a ⋖ b` (a first step, `HasFirstStep`) makes `Set.Iio b` and `Set.Ioi a` two disjoint open
sets covering the space, so a preconnected linear order has no first step anywhere. The converse
needs conditional completeness, and ℚ is the control.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

/-- `Statement:` in a linear order carrying its order topology, preconnected, no point has a first
    step. Mathlib's `denselyOrdered_of_preconnectedSpace` is the same fact in `DenselyOrdered` form
    (the `example` below); this proof keeps the footprint free of `Classical.choice`. -/
theorem no_firstStep_of_preconnected {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [PreconnectedSpace α] (bot : α) : ¬ HasFirstStep bot := by
  rintro ⟨b, h⟩
  obtain ⟨c, hcb, hac⟩ := nonempty_inter (isOpen_Iio' b) (isOpen_Ioi' bot)
    (Set.Iio_union_Ioi_of_lt h.1) ⟨bot, h.1⟩ ⟨b, h.1⟩
  exact h.2 hac hcb

-- `Statement:` Mathlib's route, through `axb1_fails_everywhere_iff_dense`, reaches the same conclusion.
example {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [PreconnectedSpace α] :
    ∀ bot : α, ¬ HasFirstStep bot :=
  axb1_fails_everywhere_iff_dense.mp denselyOrdered_of_preconnectedSpace

/-- `Statement:` the contrapositive: a first step at any point makes a linear order with its order
    topology not preconnected. -/
theorem not_preconnected_of_firstStep {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {bot : α} (h : HasFirstStep bot) : ¬ PreconnectedSpace α :=
  fun _ => no_firstStep_of_preconnected bot h

/-- `Statement:` on a conditionally complete linear order with its order topology, preconnected iff
    no point has a first step. The backward direction is Mathlib's `ordered_connected_space`. -/
theorem preconnected_iff_no_firstStep {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] :
    PreconnectedSpace α ↔ ∀ bot : α, ¬ HasFirstStep bot :=
  ⟨fun _ => no_firstStep_of_preconnected, fun h =>
    haveI : DenselyOrdered α := axb1_fails_everywhere_iff_dense.mpr h
    ordered_connected_space⟩

-- `Statement:` ℝ is preconnected, so no real has a first step; at `0` this is
-- `axb1_fails_in_ordered_field`, there by density.
example : ∀ x : ℝ, ¬ HasFirstStep x := no_firstStep_of_preconnected

-- `Statement:` control, completeness carries the backward direction: ℚ has no first step anywhere
-- and is not preconnected (Mathlib's `TotallyDisconnectedSpace ℚ`).
example : (∀ q : ℚ, ¬ HasFirstStep q) ∧ ¬ PreconnectedSpace ℚ :=
  ⟨axb1_fails_everywhere_iff_dense.mp inferInstance, fun _ =>
    not_subsingleton ℚ subsingleton_of_preconnected_totallyDisconnected⟩

-- `Statement:` control, the discrete side: every integer has a first step, and `0 : Fin 2` has one;
-- neither carrier is preconnected in its order topology.
example : (∀ n : ℤ, HasFirstStep n) ∧ ¬ PreconnectedSpace ℤ :=
  ⟨fun n => ⟨n + 1, Int.lt_succ n, fun _ h1 h2 => by omega⟩,
   not_preconnected_of_firstStep (bot := (0 : ℤ)) ⟨1, by decide, fun _ h1 h2 => by omega⟩⟩
example : HasFirstStep (0 : Fin 2) ∧ ¬ PreconnectedSpace (Fin 2) :=
  ⟨⟨1, by decide, fun _ h1 h2 => by omega⟩,
   not_preconnected_of_firstStep (bot := (0 : Fin 2)) ⟨1, by decide, fun _ h1 h2 => by omega⟩⟩

-- `Statement:` control, a first step at one point leaves the rest of the order dense: on
-- `{0} ∪ [1, 2] ⊆ ℝ`, `0` has a first step and `1` has none; with its order topology the carrier
-- is not preconnected.
example : letI : TopologicalSpace ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := Preorder.topology _
    HasFirstStep (⟨0, Or.inl rfl⟩ : ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ)) ∧
    ¬ HasFirstStep (⟨1, Or.inr ⟨le_rfl, by norm_num⟩⟩ : ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ)) ∧
    ¬ PreconnectedSpace ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := by
  letI : TopologicalSpace ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := Preorder.topology _
  haveI : OrderTopology ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := ⟨rfl⟩
  have h0 : HasFirstStep (⟨0, Or.inl rfl⟩ : ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ)) := by
    refine ⟨⟨1, Or.inr ⟨le_rfl, by norm_num⟩⟩, show (0 : ℝ) < 1 by norm_num, ?_⟩
    rintro ⟨c, hc | hc⟩ h1 h2
    · rw [Set.mem_singleton_iff] at hc; subst hc; exact lt_irrefl _ h1
    · exact absurd (show c < 1 from h2) (not_lt.2 hc.1)
  refine ⟨h0, ?_, not_preconnected_of_firstStep h0⟩
  rintro ⟨⟨a, ha | ha⟩, h1, h2⟩
  · rw [Set.mem_singleton_iff] at ha; subst ha
    exact absurd (show (1 : ℝ) < 0 from h1) (by norm_num)
  · have h1' : (1 : ℝ) < a := h1
    exact h2 (c := ⟨(1 + a) / 2, Or.inr ⟨by linarith, by linarith [ha.2]⟩⟩)
      (show (1 : ℝ) < (1 + a) / 2 by linarith) (show (1 + a) / 2 < a by linarith)

-- `Reading:` the implication runs from topology to order on every linear order with its order
-- topology, and from order to topology only under completeness. On one such carrier a continuous
-- passage (preconnected) and the snap (a first step) exclude each other. This supplies no first step
-- anywhere: AX-B1 stays a commitment.
-- `Reading:` CARRIER. ℚ₂ carries no linear order (`LT ℚ_[2]` does not synthesize, the `#check_failure` in
-- `ZeroParadox/BottomCannotBe.lean` § ROLE), so these hypotheses are not met there; its no-path
-- fact is total disconnectedness (`disconnectedness_forbids_path`,
-- `ZeroParadox/Valuation/BranchingSnapChain.lean`), a different route.

end ZeroParadox

section PurityCheck
#print axioms ZeroParadox.no_firstStep_of_preconnected
#print axioms ZeroParadox.not_preconnected_of_firstStep
#print axioms ZeroParadox.preconnected_iff_no_firstStep
-- Mathlib's lemmas cited above: printed, not asserted.
#print axioms denselyOrdered_of_preconnectedSpace
#print axioms ordered_connected_space
end PurityCheck
