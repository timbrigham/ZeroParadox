-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the depth `endVal` on `End` as the first hitting time `det` of its digit tape, read in `ℕ∞`. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Category.IgnoranceSeam
import ZeroParadox.Valuation.CellsJoint
import Mathlib.Tactic

/-!
# Depth on `End` is the waiting time of its digit tape

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

"I'm quite sure that we have previously had a model for zero that worked on the tapes that functioned
where it can currently grow in both width and depth"

---

## Formal Overview (AI-assisted)
`endVal x = waitENat (det (tapeIso x))` (`endVal_eq_wait`). `Reading:` width (pointwise tape order)
and depth are one map read two ways: order-reversing (`endVal_antitone`), a section on one side
(`endVal_gi`), no adjoint on the other (`endVal_no_lower_adjoint`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open NInf OrderDual

/-! ### § I. The digit tape -/

/-- `Statement:` the order isomorphism `Fin 2 ≃o Bool`, `0 ↦ false`, `1 ↦ true`. -/
def digitBool : Fin 2 ≃o Bool where
  toFun a := decide (a ≠ 0)
  invFun b := cond b 1 0
  left_inv a := by revert a; decide
  right_inv b := by cases b <;> rfl
  map_rel_iff' := by
    intro a b; revert a b; decide

/-- `Statement:` the digit tape of an end, digitwise `digitBool`: `End ≃o (ℕ → Bool)`, pointwise orders. -/
def tapeIso : End ≃o (ℕ → Bool) where
  toEquiv := Equiv.piCongrRight fun _ => digitBool.toEquiv
  map_rel_iff' := forall_congr' fun _ => digitBool.le_iff_le

/-- `Statement:` bit `n` of the tape of `x` is `true` iff digit `n` of `x` is nonzero. -/
theorem tapeIso_apply (x : End) (n : ℕ) : tapeIso x n = decide (x n ≠ 0) := rfl

/-! ### § II. The waiting time read in `ℕ∞` -/

/-- `Statement:` `NInf.orderIsoWithTopClassical` as `NInf ≃o ℕ∞` (costs WLPO, `NInf.wlpo_of_iso`). -/
noncomputable def waitENat : NInf ≃o ℕ∞ := NInf.orderIsoWithTopClassical

/-- `Statement:` `waitENat` sends `ofNat n` to `n`. -/
theorem waitENat_ofNat (n : ℕ) : waitENat (ofNat n) = n :=
  (waitENat.symm_apply_eq.1 (rfl : waitENat.symm (n : ℕ∞) = ofNat n)).symm

/-- `Statement:` `n ≤ waitENat y ↔ ofNat n ≤ y`. -/
theorem natCast_le_waitENat_iff (n : ℕ) (y : NInf) : (n : ℕ∞) ≤ waitENat y ↔ ofNat n ≤ y := by
  have h : waitENat.symm (n : ℕ∞) = ofNat n := rfl
  rw [← h, OrderIso.symm_apply_le]

/-- `Statement:` `n ≤ endVal x ↔ ofNat n ≤ det (tapeIso x)`; both say `x` is `0` below `n`. -/
theorem natCast_le_endVal_iff (x : End) (n : ℕ) :
    (n : ℕ∞) ≤ endVal x ↔ ofNat n ≤ det (tapeIso x) := by
  rw [← mem_boundaryCell_iff, ofNat_le_det_iff]
  show (∀ k < n, x k = 0) ↔ _
  refine forall₂_congr fun k _ => ?_
  rw [tapeIso_apply]
  simp

/-- `Statement:` the 2-adic valuation `endVal x` is the first hitting time of `true` on the digit tape
    of `x`, read in `ℕ∞`. -/
theorem endVal_eq_wait (x : End) : endVal x = waitENat (det (tapeIso x)) := by
  apply le_antisymm
  · rw [← ENat.forall_natCast_le_iff_le]
    intro a h
    rw [natCast_le_waitENat_iff]; exact (natCast_le_endVal_iff x a).1 h
  · rw [← ENat.forall_natCast_le_iff_le]
    intro a h
    rw [natCast_le_endVal_iff]; exact (natCast_le_waitENat_iff a _).1 h

/-! ### § III. Transported -/

/-- `Statement:` ⊥ of `End` goes to ⊥ of `ℕ → Bool`, its waiting time is ⊤ of `NInf`, and its
    depth is ⊤ of `ℕ∞`; ⊤ of `End` goes to ⊤ of `ℕ → Bool`, ⊥ of `NInf`, and `0`. -/
theorem depth_wait_poles :
    (tapeIso botEnd = ⊥ ∧ det (tapeIso botEnd) = ⊤ ∧ endVal botEnd = ⊤) ∧
    (tapeIso ⊤ = ⊤ ∧ det (tapeIso ⊤) = ⊥ ∧ endVal ⊤ = 0) := by
  have hb : tapeIso botEnd = ⊥ := funext fun _ => rfl
  have ht : tapeIso ⊤ = ⊤ := funext fun _ => rfl
  refine ⟨⟨hb, by rw [hb]; exact det_poles.1, botEnd_val_top⟩,
    ⟨ht, by rw [ht]; exact det_poles.2, ?_⟩⟩
  rw [endVal_eq_wait, ht, det_poles.2]
  exact (waitENat_ofNat 0).trans Nat.cast_zero

/-- `Statement:` `unitEnd k` has the tape firing exactly at `k`, waiting time `ofNat k`, depth `k`. -/
theorem depth_wait_unitEnd (k : ℕ) :
    tapeIso (unitEnd k) = (fun n => decide (n = k)) ∧ det (tapeIso (unitEnd k)) = ofNat k ∧
      endVal (unitEnd k) = waitENat (ofNat k) := by
  have h : tapeIso (unitEnd k) = fun n => decide (n = k) := by
    funext n
    rw [tapeIso_apply]
    by_cases hn : n = k
    · subst hn; simp [unitEnd_self]
    · simp [unitEnd_ne hn, hn]
  exact ⟨h, by rw [h]; exact det_fire k, by rw [endVal_unitEnd, waitENat_ofNat]⟩

/-- `Statement:` `boundaryDouble` on ends is prepend-`false` (`tapeCons false`) on tapes. -/
theorem tapeIso_boundaryDouble (x : End) :
    tapeIso (boundaryDouble x) = tapeCons false (tapeIso x) := by
  funext n; cases n <;> rfl

/-- `Statement:` prepending `false` delays the first hitting time by one: `det (tapeCons false r) =
    succ (det r)`. -/
theorem det_tapeCons_false (r : ℕ → Bool) : det (tapeCons false r) = succ (det r) := ext fun n => by
  cases n with
  | zero => rfl
  | succ m =>
    show detSeq (tapeCons false r) (m + 1) = detSeq r m
    apply Bool.eq_iff_iff.2
    rw [detSeq_eq_true_iff, detSeq_eq_true_iff]
    constructor
    · intro h k hk; exact h (k + 1) (by omega)
    · intro h k hk
      cases k with
      | zero => rfl
      | succ j => exact h j (by omega)

/-- `Statement:` `waitENat (succ y) = waitENat y + 1`, transported from `endVal_boundaryDouble`. -/
theorem waitENat_succ (y : NInf) : waitENat (succ y) = waitENat y + 1 := by
  have h1 : det (tapeIso (tapeIso.symm (negS y))) = y := by
    rw [OrderIso.apply_symm_apply, det_negS]
  calc waitENat (succ y)
      = waitENat (det (tapeIso (boundaryDouble (tapeIso.symm (negS y))))) := by
        rw [tapeIso_boundaryDouble, det_tapeCons_false, h1]
    _ = endVal (boundaryDouble (tapeIso.symm (negS y))) := (endVal_eq_wait _).symm
    _ = endVal (tapeIso.symm (negS y)) + 1 := endVal_boundaryDouble _
    _ = waitENat y + 1 := by rw [endVal_eq_wait, h1]

/-- `Statement:` `endVal` is antitone for the pointwise order on `End`. -/
theorem endVal_antitone : Antitone endVal := fun a b h => by
  rw [endVal_eq_wait, endVal_eq_wait]
  exact waitENat.monotone (det_antitone (tapeIso.monotone h))

/-- `Statement:` `endVal` into the order dual of `ℕ∞` is the lower adjoint of a Galois connection with
    upper adjoint `v ↦ tapeIso.symm (negS (waitENat.symm v))`. -/
theorem endVal_gc : GaloisConnection (toDual ∘ endVal)
    (fun v : ℕ∞ᵒᵈ => tapeIso.symm (negS (waitENat.symm (ofDual v)))) := fun x v => by
  show toDual (endVal x) ≤ v ↔ _
  rw [toDual_le, endVal_eq_wait, ← OrderIso.symm_apply_le, le_det_iff, OrderIso.le_symm_apply]

/-- `Statement:` and a Galois insertion (Mathlib `GaloisInsertion`), transported from `det_gi`. -/
noncomputable def endVal_gi : GaloisInsertion (toDual ∘ endVal)
    (fun v : ℕ∞ᵒᵈ => tapeIso.symm (negS (waitENat.symm (ofDual v)))) :=
  endVal_gc.toGaloisInsertion fun v => by
    show v ≤ toDual (endVal (tapeIso.symm (negS (waitENat.symm (ofDual v)))))
    rw [endVal_eq_wait, OrderIso.apply_symm_apply, det_negS, OrderIso.apply_symm_apply]
    exact le_rfl

/-- `Statement:` no adjoint on the other side, transported from `NInf.no_lower_adjoint`. -/
theorem endVal_no_lower_adjoint : ¬ ∃ g : ℕ∞ → End, ∀ v x, g v ≤ x ↔ endVal x ≤ v := by
  rintro ⟨g, hg⟩
  refine NInf.no_lower_adjoint ⟨fun y => tapeIso (g (waitENat y)), fun y r => ?_⟩
  rw [← OrderIso.le_symm_apply, hg, endVal_eq_wait, OrderIso.apply_symm_apply, OrderIso.le_iff_le]

/-- `Statement:` `endVal` is not injective. -/
theorem endVal_not_injective : ¬ Function.Injective endVal := fun h => by
  have e : endVal (unitEnd 0) = endVal ⊤ := by
    rw [endVal_unitEnd, depth_wait_poles.2.2.2, Nat.cast_zero]
  have := congrFun (h e) 1
  rw [unitEnd_ne (by omega)] at this
  exact absurd this (by decide)

/-! ### § IV. Controls -/

-- Statement: CONTROL, the count of nonzero digits does not satisfy the bridge: at `unitEnd 3` it is `1`.
example : Set.encard {n | unitEnd 3 n ≠ 0} ≠ waitENat (det (tapeIso (unitEnd 3))) := by
  have hs : {n | unitEnd 3 n ≠ 0} = ({3} : Set ℕ) := by
    ext n
    by_cases hn : n = 3
    · subst hn; simp [unitEnd_self]
    · simp [unitEnd_ne hn, hn]
  rw [hs, Set.encard_singleton, (depth_wait_unitEnd 3).2.1, waitENat_ofNat]
  exact_mod_cast (by decide : (1 : ℕ) ≠ 3)

-- Statement: CONTROL, the complement tape (digit `0` read as `true`) does not satisfy the bridge: at ⊥
-- of `End` its waiting time reads `0`, where `endVal botEnd = ⊤`.
example : waitENat (det (fun n => decide (botEnd n = 0))) ≠ endVal botEnd := by
  have h : (fun n => decide (botEnd n = 0)) = (⊤ : ℕ → Bool) := funext fun _ => rfl
  rw [h, det_poles.2, botEnd_val_top]
  show waitENat (ofNat 0) ≠ ⊤
  rw [waitENat_ofNat]
  exact ENat.natCast_ne_top 0

-- Statement: axioms (PurityCheck), `digitBool`, `tapeIso`, `tapeIso_boundaryDouble`, `det_tapeCons_false`
--   `[propext, Quot.sound]`; the rest add `Classical.choice`, via `endVal` (an `sInf` in `ℕ∞`) and
--   `waitENat` (any `NInf ≃o ℕ∞` gives WLPO, `NInf.wlpo_of_iso`).

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms digitBool
#print axioms tapeIso
#print axioms tapeIso_apply
#print axioms waitENat
#print axioms waitENat_ofNat
#print axioms natCast_le_waitENat_iff
#print axioms natCast_le_endVal_iff
#print axioms endVal_eq_wait
#print axioms depth_wait_poles
#print axioms depth_wait_unitEnd
#print axioms tapeIso_boundaryDouble
#print axioms det_tapeCons_false
#print axioms waitENat_succ
#print axioms endVal_antitone
#print axioms endVal_gc
#print axioms endVal_gi
#print axioms endVal_no_lower_adjoint
#print axioms endVal_not_injective
end PurityCheck
