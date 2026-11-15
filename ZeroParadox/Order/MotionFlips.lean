-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the up-then-over loop against the corpus's over-then-up `Motion.Loop`, the 2-adic tower as a die `Motion` and its leg polarity, and time reversal as a non-invariant of `Loop`. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Die
import ZeroParadox.Ordinal.CnfBridge
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic

/-!
# Which leg first, which way the legs point, which way time runs

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
An up-then-over loop exists iff `Motion.Loop` does (§ I). `z2TowerMotion` on ℤ_[2] loops, so no partial
order makes its legs agree; under the valuation its legs oppose (§ II). Reversing the step, which keeps
UP, does not preserve `Loop` (§ III).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

universe u

/-! ### § I. Which leg first: one cycle, entered at either leg -/

/-- `Statement:` up-then-over loop: `up` sends `x` to `y ≠ x`, and `y` steps back to `x`. -/
def Motion.UpOverLoop {α : Type u} (M : Motion α) : Prop := ∃ x y, y ∈ M.up x ∧ M.step y x ∧ x ≠ y

/-- `Statement:` `M.UpOverLoop ↔ M.Loop`; both directions. -/
theorem Motion.upOverLoop_iff_loop {α : Type u} (M : Motion α) : M.UpOverLoop ↔ M.Loop :=
  ⟨fun ⟨x, y, hu, hs, hne⟩ => ⟨y, x, M.up_idem x y hu, hs, hne, hu⟩,
   fun ⟨y, b, _, hs, hne, hu⟩ => ⟨b, y, hu, hs, hne⟩⟩

-- Statement: for functions, an `n`-cycle of `g ∘ f` at `x` gives an `n`-cycle of `f ∘ g` at `f x`;
-- this is Mathlib's `Function.IsPeriodicPt.map` along the semiconjugacy `f ∘ (g ∘ f) = (f ∘ g) ∘ f`.
example {α : Type u} (f g : α → α) (n : ℕ) (x : α) (h : Function.IsPeriodicPt (g ∘ f) n x) :
    Function.IsPeriodicPt (f ∘ g) n (f x) :=
  h.map (fun _ => rfl)

-- Statement: CONTROL, agreeing legs exclude the up-then-over loop too (`Motion.not_loop_of_agree`).
example {α : Type u} [PartialOrder α] (M : Motion α) (h : M.Agree) : ¬ M.UpOverLoop :=
  fun hl => Motion.not_loop_of_agree h ((Motion.upOverLoop_iff_loop M).1 hl)

/-! ### § II. The 2-adic tower as a motion: it loops, and its legs oppose under the valuation -/

/-- `Statement:` on ℤ_[2], UP sends every point to 0 and OVER steps the `cnfToZp2` image of tower
stage `n` to that of stage `n + 1`. The constant UP is this definition's choice. -/
noncomputable def z2TowerMotion : Motion ℤ_[2] :=
  Motion.ofTotal (fun _ => 0) (fun _ => rfl)
    (fun x y => ∃ n, x = cnfToZp2 (towerNONote n) ∧ y = cnfToZp2 (towerNONote (n + 1)))

/-- `Statement:` `z2TowerMotion` loops. -/
theorem z2TowerMotion_loop : z2TowerMotion.Loop :=
  ⟨0, cnfToZp2 (towerNONote 1), Part.mem_some _, ⟨0, snap_arc_z2_loop.1.symm, rfl⟩,
    snap_arc_z2_loop.2.1 1 le_rfl, Part.mem_some _⟩

/-- `Statement:` no partial order on ℤ_[2] makes both legs of `z2TowerMotion` raise. -/
theorem z2_no_agreeing_order (inst : PartialOrder ℤ_[2]) :
    ¬ @Motion.Agree ℤ_[2] z2TowerMotion inst.toLE := fun h => by
  let _ := inst
  exact Motion.not_loop_of_agree h z2TowerMotion_loop

/-- `Statement:` under Mathlib's ℕ-valued `PadicInt.valuation`, 0 has the least value, and the image
of stage `n + 1` has the value of stage `n` plus one. -/
theorem z2_valuation_oppose :
    (∀ x : ℤ_[2], (0 : ℤ_[2]).valuation ≤ x.valuation) ∧
    (∀ n, (cnfToZp2 (towerNONote (n + 1))).valuation = (cnfToZp2 (towerNONote n)).valuation + 1) :=
  ⟨fun x => by rw [PadicInt.valuation_zero]; exact Nat.zero_le _,
   fun n => by simp only [cnfToZp2_tower_valuation]⟩

/-- `Statement:` under the norm, 0 has the least value, the image of stage 1 has a larger norm than
that of stage 0, and from stage 1 on each next image has a smaller norm. -/
theorem z2_norm_drift :
    (∀ x : ℤ_[2], ‖(0 : ℤ_[2])‖ ≤ ‖x‖) ∧
    ‖cnfToZp2 (towerNONote 0)‖ < ‖cnfToZp2 (towerNONote 1)‖ ∧
    (∀ n, 1 ≤ n → ‖cnfToZp2 (towerNONote (n + 1))‖ < ‖cnfToZp2 (towerNONote n)‖) := by
  refine ⟨fun x => norm_zero (E := ℤ_[2]) ▸ norm_nonneg x, ?_, fun n hn => ?_⟩
  · rw [snap_arc_z2_loop.1, norm_zero]
    exact norm_pos_iff.2 (snap_arc_z2_loop.2.1 1 le_rfl)
  · rw [PadicInt.norm_eq_zpow_neg_valuation (snap_arc_z2_loop.2.1 (n + 1) (by omega)),
      PadicInt.norm_eq_zpow_neg_valuation (snap_arc_z2_loop.2.1 n hn),
      cnfToZp2_tower_valuation, cnfToZp2_tower_valuation]
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)

/-! ### § III. Which way time runs: reversal can remove a loop -/

/-- `Statement:` on `Bool`, UP sends every point to `false` and OVER is only `false → true`. -/
def boolOneWayMotion : Motion Bool :=
  Motion.ofTotal (fun _ => false) (fun _ => rfl) (fun x y => x = false ∧ y = true)

/-- `Statement:` `boolOneWayMotion` loops. -/
theorem boolOneWayMotion_loop : boolOneWayMotion.Loop :=
  ⟨false, true, Part.mem_some _, ⟨rfl, rfl⟩, by decide, Part.mem_some _⟩

/-- `Statement:` `boolOneWayMotion.reverse` does not loop. -/
theorem boolOneWayMotion_reverse_not_loop : ¬ boolOneWayMotion.reverse.Loop := by
  rintro ⟨y, b, hy, ⟨hb, hyt⟩, -, -⟩
  subst hyt
  exact Bool.noConfusion (Part.mem_some_iff.1 hy)

/-- `Statement:` not every looping motion on `Bool` has a looping reverse. -/
theorem Motion.loop_not_reverse_invariant : ¬ ∀ (M : Motion Bool), M.Loop → M.reverse.Loop :=
  fun h => boolOneWayMotion_reverse_not_loop (h _ boolOneWayMotion_loop)

/-- `Statement:` `z2TowerMotion.reverse` does not loop. -/
theorem z2TowerMotion_reverse_not_loop : ¬ z2TowerMotion.reverse.Loop := by
  rintro ⟨y, b, hy, ⟨n, -, hyn⟩, -, -⟩
  have h0 : y = 0 := Part.mem_some_iff.1 hy
  exact snap_arc_z2_loop.2.1 (n + 1) (by omega) (hyn.symm.trans h0)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms Motion.UpOverLoop
#print axioms Motion.upOverLoop_iff_loop
#print axioms z2TowerMotion
#print axioms z2TowerMotion_loop
#print axioms z2_no_agreeing_order
#print axioms z2_valuation_oppose
#print axioms z2_norm_drift
#print axioms boolOneWayMotion
#print axioms boolOneWayMotion_loop
#print axioms boolOneWayMotion_reverse_not_loop
#print axioms Motion.loop_not_reverse_invariant
#print axioms z2TowerMotion_reverse_not_loop
end PurityCheck
