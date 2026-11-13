-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the local floor `localBotEnd v` as ⊥ of `ℕ → Bool` on its subtape, and a whole local tower packed into one end of `End` by `natDirsOrderIso`. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.PoleWithinEnsemble
import ZeroParadox.Valuation.OneWayFlow
import ZeroParadox.Valuation.Interleave
import Mathlib.Tactic

/-!
# Local floors as subtape poles, and a tower as one tape

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
The subtape of `localBotEnd v` after `v` is ⊥ of `ℕ → Bool`; below a `1` the whole tape fires
(`localFloor_two_charts_limit`). `towerTape v` packs a `localPush v`-orbit into one end; its depths
diverge at the floor (`tower_pole_within_pole`, `ℕ∞`; `tower_pole_within_pole_limit`, `NInf`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology NInf

/-! ### § I. The local floor is the pole of its subtape -/

/-- `Statement:` `localCx v x` is the `ℕ∞` wait of the subtape of `x` after `v`. -/
theorem localCx_eq_wait (v : List (Fin 2)) (x : End) :
    localCx v x = waitENat (det (tapeIso (shiftEnd v.length x))) :=
  endVal_eq_wait _

/-- `Statement:` `localPush v` delays the subtape wait by one, as `succ` in `NInf`. -/
theorem det_localPush (v : List (Fin 2)) (x : End) :
    det (tapeIso (shiftEnd v.length (localPush v x))) =
      succ (det (tapeIso (shiftEnd v.length x))) := by
  unfold localPush
  rw [shiftEnd_prependEnd, tapeIso_boundaryDouble, det_tapeCons_false]

/-- `Statement:` `localPush v` adds one to `localCx v`, in `ℕ∞`. -/
theorem localCx_localPush (v : List (Fin 2)) (x : End) :
    localCx v (localPush v x) = localCx v x + 1 := by
  rw [localCx_eq_wait, localCx_eq_wait, det_localPush, waitENat_succ]

/-- `Statement:` the subtape of `localBotEnd v` after `v` is ⊥ of `ℕ → Bool`, with `det` ⊤ of `NInf`.
The `ℕ∞` form is `localCx_bot`. -/
theorem localFloor_subtape_pole_limit (v : List (Fin 2)) :
    tapeIso (shiftEnd v.length (localBotEnd v)) = ⊥ ∧
      det (tapeIso (shiftEnd v.length (localBotEnd v))) = ⊤ := by
  have h : tapeIso (shiftEnd v.length (localBotEnd v)) = ⊥ := by
    unfold localBotEnd; rw [shiftEnd_prependEnd]; funext n; rfl
  exact ⟨h, by rw [h]; exact det_poles.1⟩

/-- `Statement:` `localFloor_subtape_pole_limit`, and `localCx v (localBotEnd v) = ⊤` in `ℕ∞`. -/
theorem localFloor_subtape_pole (v : List (Fin 2)) :
    tapeIso (shiftEnd v.length (localBotEnd v)) = ⊥ ∧
      det (tapeIso (shiftEnd v.length (localBotEnd v))) = ⊤ ∧ localCx v (localBotEnd v) = ⊤ :=
  ⟨(localFloor_subtape_pole_limit v).1, (localFloor_subtape_pole_limit v).2, localCx_bot v⟩

/-- `Statement:` for `v = u ++ [1]`, the subtape wait of `localBotEnd v` is ⊤ of `NInf`, and the
computation of its whole tape terminates. -/
theorem localFloor_two_charts_limit (u : List (Fin 2)) :
    det (tapeIso (shiftEnd (u ++ [1]).length (localBotEnd (u ++ [1])))) = ⊤ ∧
      (toComp (det (tapeIso (localBotEnd (u ++ [1]))))).Terminates := by
  refine ⟨(localFloor_subtape_pole_limit _).2, (toComp_det_terminates_iff _).2 ⟨u.length, ?_⟩⟩
  have hlen : u.length < (u ++ [1]).length := by rw [List.length_append]; exact Nat.lt_succ_self _
  have hg : (u ++ [1]).getD u.length 0 = 1 := by
    induction u with
    | nil => rfl
    | cons a u ih => exact ih (by rw [List.length_append]; exact Nat.lt_succ_self _)
  show decide (prependEnd (u ++ [1]) botEnd u.length ≠ 0) = true
  unfold prependEnd
  rw [ite_eq_left hlen, hg]
  rfl

/-- `Statement:` for `v = u ++ [1]`, `localCx v (localBotEnd v) = ⊤` and `endVal (localBotEnd v) ≠ ⊤`. -/
theorem localFloor_two_charts (u : List (Fin 2)) :
    localCx (u ++ [1]) (localBotEnd (u ++ [1])) = ⊤ ∧
      endVal (localBotEnd (u ++ [1])) ≠ ⊤ := by
  refine ⟨localCx_bot _, ?_⟩
  rw [endVal_eq_wait]
  refine wait_ne_top_of_fires _ ⟨u.length, ?_⟩
  rw [tapeIso_apply, localBotEnd_apply, canonNode_last]
  decide

-- Statement: CONTROL, under an all-zero prefix the local floor is ⊥ of `End`, of `endVal` ⊤: the two
-- charts agree there, so `localFloor_two_charts` needs the `1`.
example (k : ℕ) : localBotEnd (List.replicate k 0) = botEnd ∧
    endVal (localBotEnd (List.replicate k 0)) = ⊤ := by
  have h : localBotEnd (List.replicate k 0) = botEnd := by
    have := localBotEnd_append_zeros [] k
    rw [List.nil_append] at this
    rw [this]; exact prependEnd_nil _
  refine ⟨h, by rw [h]; exact depth_wait_poles.1.2.2⟩

/-! ### § II. A tower as one tape -/

/-- `Statement:` `localPush v` is monotone. -/
theorem localPush_monotone (v : List (Fin 2)) : Monotone (localPush v) := fun a b h n => by
  unfold localPush prependEnd
  split_ifs
  · exact le_rfl
  · show boundaryDouble (shiftEnd v.length a) (n - v.length) ≤
      boundaryDouble (shiftEnd v.length b) (n - v.length)
    generalize n - v.length = m
    cases m with
    | zero => exact le_rfl
    | succ k => exact h _

/-- `Statement:` `localPush v` is continuous. -/
theorem localPush_continuous (v : List (Fin 2)) : Continuous (localPush v) := by
  refine continuous_pi fun n => ?_
  show Continuous fun x : End => localPush v x n
  by_cases hn : n < v.length
  · simp only [localPush, prependEnd, hn, ite_true]; exact continuous_const
  · simp only [localPush, prependEnd, hn, ite_false]
    generalize n - v.length = m
    cases m with
    | zero => exact continuous_const
    | succ k => exact continuous_apply (v.length + k)

/-- `Statement:` `natDirsOrderIso` is continuous. -/
theorem natDirs_continuous : Continuous natDirsOrderIso := by
  show Continuous fun x : End => fun i j => x (Nat.pair i j)
  exact continuous_pi fun i => continuous_pi fun j => continuous_apply _

/-- `Statement:` `natDirsOrderIso.symm` is continuous. -/
theorem natDirs_symm_continuous : Continuous natDirsOrderIso.symm := by
  show Continuous fun y : ℕ → End => fun n => y (Nat.unpair n).1 (Nat.unpair n).2
  exact continuous_pi fun n => (continuous_apply _).comp (continuous_apply _)

/-- `Statement:` `natDirsOrderIso` as a homeomorphism `End ≃ₜ (ℕ → End)`. -/
def natDirsHomeo : End ≃ₜ (ℕ → End) where
  toEquiv := natDirsOrderIso.toEquiv
  continuous_toFun := natDirs_continuous
  continuous_invFun := natDirs_symm_continuous

/-- `Statement:` `natDirsOrderIso x` is the constant `botEnd` iff `x = botEnd`. -/
theorem natDirs_bot_iff (x : End) : natDirsOrderIso x = (fun _ => botEnd) ↔ x = botEnd := by
  constructor
  · intro h
    apply natDirsOrderIso.injective; rw [h]; rfl
  · rintro rfl; rfl

/-- `Statement:` the orbit of `x` under `localPush v`, packed into one end. -/
def towerTape (v : List (Fin 2)) (x : End) : End :=
  natDirsOrderIso.symm (fun n => (localPush v)^[n] x)

/-- `Statement:` column `n` of `towerTape v x` is `(localPush v)^[n] x`. -/
theorem towerTape_col (v : List (Fin 2)) (x : End) (n j : ℕ) :
    natDirsOrderIso (towerTape v x) n j = (localPush v)^[n] x j := by
  unfold towerTape; rw [OrderIso.apply_symm_apply]

/-- `Statement:` `towerTape v x ≤ towerTape v y ↔ x ≤ y`. -/
theorem towerTape_le_iff (v : List (Fin 2)) (x y : End) :
    towerTape v x ≤ towerTape v y ↔ x ≤ y := by
  unfold towerTape
  rw [OrderIso.le_iff_le]
  constructor
  · intro h; exact h 0
  · intro h n; exact (localPush_monotone v).iterate n h

/-- `Statement:` `towerTape v` is injective. -/
theorem towerTape_injective (v : List (Fin 2)) : Function.Injective (towerTape v) :=
  fun x y h => le_antisymm ((towerTape_le_iff v x y).1 h.le) ((towerTape_le_iff v y x).1 h.ge)

/-- `Statement:` `towerTape v` is continuous. -/
theorem towerTape_continuous (v : List (Fin 2)) : Continuous (towerTape v) :=
  natDirs_symm_continuous.comp (continuous_pi fun n => (localPush_continuous v).iterate n)

/-- `Statement:` `towerTape v` is a closed embedding. -/
theorem towerTape_isClosedEmbedding (v : List (Fin 2)) :
    Topology.IsClosedEmbedding (towerTape v) :=
  (towerTape_continuous v).isClosedEmbedding (towerTape_injective v)

/-- `Statement:` the columns of `towerTape v (localMember v 0)` are `localMember v`. -/
theorem towerTape_member (v : List (Fin 2)) :
    natDirsOrderIso (towerTape v (localMember v 0)) = localMember v := by
  unfold towerTape; rw [OrderIso.apply_symm_apply]; funext n; exact localPush_iterate v n

/-- `Statement:` the tower of `localBotEnd v` is the constant listing of `localBotEnd v`. -/
theorem towerTape_floor (v : List (Fin 2)) :
    towerTape v (localBotEnd v) = natDirsOrderIso.symm (fun _ => localBotEnd v) := by
  unfold towerTape; congr 1; funext n; exact Function.iterate_fixed (localPush_floor v) n

/-- `Statement:` `towerTape [] x = botEnd` iff `x = botEnd`. -/
theorem towerTape_root_pole (x : End) : towerTape [] x = botEnd ↔ x = botEnd := by
  constructor
  · intro h
    have := congrArg (fun y => natDirsOrderIso y 0) h
    simp only [towerTape, OrderIso.apply_symm_apply, Function.iterate_zero, id] at this
    rw [this]; rfl
  · rintro rfl
    have h := towerTape_floor []
    rw [show localBotEnd [] = botEnd from prependEnd_nil _] at h
    rw [h]
    apply natDirsOrderIso.injective
    rw [OrderIso.apply_symm_apply]
    funext n; rfl

-- Statement: CONTROL, `towerTape []` is not onto: column 1 is forced by column 0.
example : ¬ Function.Surjective (towerTape []) := by
  intro h
  obtain ⟨x, hx⟩ := h (natDirsOrderIso.symm (fun n => if n = 0 then botEnd else unitEnd 0))
  have h0 := congrArg (fun y => natDirsOrderIso y 0) hx
  have h1 := congrArg (fun y => natDirsOrderIso y 1) hx
  simp only [towerTape, OrderIso.apply_symm_apply, Function.iterate_zero, id, ite_true,
    Function.iterate_one, one_ne_zero, ite_false] at h0 h1
  rw [h0, localPush_nil, boundaryDouble_botEnd] at h1
  have := congrFun h1 0
  simp [unitEnd, botEnd] at this

/-! ### § III. Depth along the tower -/

/-- `Statement:` `localCx v` tends to ⊤ of `ℕ∞` at `localBotEnd v`. -/
theorem localCx_tendsto_top_at_floor (v : List (Fin 2)) :
    Tendsto (localCx v) (𝓝 (localBotEnd v)) (𝓝 ⊤) := by
  have hT : Continuous (fun x : End => tapeIso (shiftEnd v.length x)) := by
    refine continuous_pi fun n => ?_
    exact (continuous_of_discreteTopology (f := fun a : Fin 2 => decide (a ≠ 0))).comp
      (continuous_apply (v.length + n))
  have h := (localFloor_subtape_pole_limit v).1
  have := wait_tendsto_top_at_bot.comp (h ▸ hT.tendsto (localBotEnd v))
  have e : localCx v = fun x => waitENat (det (tapeIso (shiftEnd v.length x))) :=
    funext (localCx_eq_wait v)
  rw [e]; exact this

/-- `Statement:` the orbit of `localMember v 0` tends to `localBotEnd v` with `localCx` `n` at step
`n`, tending to ⊤ of `ℕ∞`; the floor has `localCx` ⊤ and subtape ⊥ of `ℕ → Bool`. -/
theorem tower_pole_within_pole (v : List (Fin 2)) :
    Tendsto (fun n => (localPush v)^[n] (localMember v 0)) atTop (𝓝 (localBotEnd v)) ∧
    (∀ n, localCx v ((localPush v)^[n] (localMember v 0)) = n) ∧
    Tendsto (fun n => localCx v ((localPush v)^[n] (localMember v 0))) atTop (𝓝 ⊤) ∧
    localCx v (localBotEnd v) = ⊤ ∧ tapeIso (shiftEnd v.length (localBotEnd v)) = ⊥ := by
  have h2 : ∀ n, localCx v ((localPush v)^[n] (localMember v 0)) = n := fun n => by
    rw [localPush_iterate, localCx_member]
  refine ⟨tendsto_iterate_localPush v _, h2, ?_, localCx_bot v,
    (localFloor_subtape_pole_limit v).1⟩
  simp_rw [h2]; exact ENat.tendsto_natCast_nhds_top

/-- `Statement:` the subtape wait of `localMember v n` is `ofNat n`; each digit `m` of the orbit agrees
with `localBotEnd v` from step `m + 1`; the floor's subtape wait is ⊤ of `NInf`. -/
theorem tower_pole_within_pole_limit (v : List (Fin 2)) :
    (∀ n, det (tapeIso (shiftEnd v.length (localMember v n))) = ofNat n) ∧
    (∀ m, ∀ n > m, (localPush v)^[n] (localMember v 0) m = localBotEnd v m) ∧
    det (tapeIso (shiftEnd v.length (localBotEnd v))) = ⊤ := by
  refine ⟨fun n => ?_, fun m n hn => ?_, (localFloor_subtape_pole_limit v).2⟩
  · unfold localMember; rw [shiftEnd_prependEnd]
    have : tapeIso (fun k => if k = n then (1 : Fin 2) else 0) = fun k => decide (k = n) := by
      funext k; rw [tapeIso_apply]; by_cases hk : k = n
      · subst hk; simp
      · rw [ite_eq_right hk, decide_eq_false hk]; rfl
    rw [this, det_fire]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [localPush_iterate_succ]
    show prependEnd v _ m = prependEnd v botEnd m
    unfold prependEnd
    split_ifs with h
    · rfl
    · exact iterate_boundaryDouble_mem_cell _ (k + 1) (m - v.length) (by omega)

-- Statement: CONTROL, the constant map `_ ↦ localBotEnd v` reaches the floor in one step, so its
-- orbit has no finite-depth approach.
example (v : List (Fin 2)) (x : End) :
    localCx v ((fun _ : End => localBotEnd v)^[1] x) = ⊤ := by
  simp [localCx_bot]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms localCx_eq_wait
#print axioms det_localPush
#print axioms localCx_localPush
#print axioms localFloor_subtape_pole_limit
#print axioms localFloor_subtape_pole
#print axioms localFloor_two_charts_limit
#print axioms localFloor_two_charts
#print axioms localPush_monotone
#print axioms localPush_continuous
#print axioms natDirs_continuous
#print axioms natDirs_symm_continuous
#print axioms natDirsHomeo
#print axioms natDirs_bot_iff
#print axioms towerTape
#print axioms towerTape_col
#print axioms towerTape_le_iff
#print axioms towerTape_injective
#print axioms towerTape_continuous
#print axioms towerTape_isClosedEmbedding
#print axioms towerTape_member
#print axioms towerTape_floor
#print axioms towerTape_root_pole
#print axioms localCx_tendsto_top_at_floor
#print axioms tower_pole_within_pole
#print axioms tower_pole_within_pole_limit
end PurityCheck
