-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the tower tape `towerTape [] x`, read through `tapeIso` as a tape `ℕ → Bool`, fed to `t_snap_of_fires_once` tape by tape and for `trials p hp`-almost every seed; and the control that the tower tapes themselves form a `trials p hp`-null set. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.TowerTape
import Mathlib.Tactic

/-!
# The tower tape fed to the snap, chart by chart

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
`tapeIso` carries `towerTape [] x` to a tape that fires iff `x ≠ botEnd` (§ I); the snap, seed by
seed and for almost every seed (§ II); the tower tapes form a null set (§ III).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory Filter Topology

/-! ### § I. The map, and the one tower tape that never fires -/

/-- `Statement:` the tape `tapeIso y` fires somewhere iff `y ≠ botEnd`. -/
theorem tapeIso_fires_iff (y : End) : (∃ k, tapeIso y k = true) ↔ y ≠ botEnd := by
  constructor
  · rintro ⟨k, hk⟩ rfl
    simp [tapeIso_apply, botEnd] at hk
  · intro hy
    by_contra h
    apply hy; funext k
    have hk : tapeIso y k ≠ true := fun hk => h ⟨k, hk⟩
    rw [tapeIso_apply] at hk
    show y k = 0
    simpa using hk

/-- `Statement:` the tape `tapeIso (towerTape [] x)` fires somewhere iff `x ≠ botEnd`. -/
theorem towerTape_fires_iff (x : End) :
    (∃ k, tapeIso (towerTape [] x) k = true) ↔ x ≠ botEnd := by
  rw [tapeIso_fires_iff, Ne, towerTape_root_pole]

/-- `Statement:` `tapeIso (towerTape [] botEnd)` is ⊥ of `ℕ → Bool`, the all-`false` tape. -/
theorem towerTape_floor_allFalse : tapeIso (towerTape [] botEnd) = ⊥ := by
  rw [(towerTape_root_pole botEnd).2 rfl]; funext n; rfl

/-! ### § II. Two charts: tape by tape, and almost every seed -/

/-- `Statement:` if `φ : Bool → L` sends `false` to ⊥ of `L` and `true` to a point other than ⊥ of
`L`, and `x ≠ botEnd`, then `tapeIso (towerTape [] x)` fires and gives `t_snap_of_fires_once`'s
conclusion. -/
theorem towerTape_snap_pointwise {L : Type*} [ZPSemilattice L] (φ : Bool → L)
    (hφ0 : φ false = ZPSemilattice.bot) (hφ1 : φ true ≠ ZPSemilattice.bot) (x : End)
    (hx : x ≠ botEnd) :
    ∃ hw : ∃ k, tapeIso (towerTape [] x) k = true,
      let S := φ ∘ firedRun _ hw
      S 0 = ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧ ZPSemilattice.IsStateSequence S ∧
        (S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ ZPSemilattice.join (S 0) (S 1) = S 1) := by
  have hw := (towerTape_fires_iff x).2 hx
  exact ⟨hw, t_snap_of_fires_once φ hφ0 hφ1 _ hw⟩

/-- `Statement:` under `towerTape_snap_pointwise`'s hypotheses on `φ`, if `0 < p ≤ 1`, then for
`trials p hp`-almost every tape `w`, the tower tape of the seed `tapeIso.symm w` fires and gives
`t_snap_of_fires_once`'s conclusion. -/
theorem towerTape_snap_ae {L : Type*} [ZPSemilattice L] (φ : Bool → L)
    (hφ0 : φ false = ZPSemilattice.bot) (hφ1 : φ true ≠ ZPSemilattice.bot)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ∀ᵐ w ∂(trials p hp), ∃ hw : ∃ k, tapeIso (towerTape [] (tapeIso.symm w)) k = true,
      let S := φ ∘ firedRun _ hw
      S 0 = ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧ ZPSemilattice.IsStateSequence S ∧
        (S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ ZPSemilattice.join (S 0) (S 1) = S 1) := by
  filter_upwards [ae_firesOnce p hp hp0] with w hw
  have hx : tapeIso.symm w ≠ botEnd := by
    rw [← tapeIso_fires_iff, OrderIso.apply_symm_apply]; exact hw
  exact towerTape_snap_pointwise φ hφ0 hφ1 _ hx

/-! ### § III. CONTROL: the tower tapes are a null set of tapes -/

/-- `Statement:` the digit of `towerTape [] x` at `Nat.pair (n + 1) 0` is `0`. -/
theorem towerTape_digit_zero (x : End) (n : ℕ) : towerTape [] x (Nat.pair (n + 1) 0) = 0 := by
  have := towerTape_col [] x (n + 1) 0
  rw [natDirsOrderIso_apply] at this
  rw [this, localPush_nil, Function.iterate_succ_apply']
  rfl

/-- `Statement:` CONTROL, if `0 < p ≤ 1`, the set of tapes `tapeIso (towerTape [] x)` is
`trials p hp`-null. -/
theorem towerTapes_null (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp (Set.range fun x => tapeIso (towerTape [] x)) = 0 := by
  have hsub : ∀ N : ℕ, (Set.range fun x => tapeIso (towerTape [] x)) ⊆
      (↑((Finset.range N).image (fun n => Nat.pair (n + 1) 0)) : Set ℕ).pi
        (fun _ => ({false} : Set Bool)) := by
    rintro N _ ⟨x, rfl⟩ j hj
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hj
    obtain ⟨n, -, rfl⟩ := hj
    simp [tapeIso_apply, towerTape_digit_zero]
  have hinj : Function.Injective (fun n : ℕ => Nat.pair (n + 1) 0) := fun a b h => by
    have := (Nat.pair_eq_pair.1 h).1; omega
  have hle : ∀ N : ℕ, trials p hp (Set.range fun x => tapeIso (towerTape [] x)) ≤
      (((1 - p : NNReal)) : ENNReal) ^ N := fun N => by
    refine (measure_mono (hsub N)).trans (le_of_eq ?_)
    have h1 := trials_zeroBlock p hp 0 1
    rw [zeroBlock_eq_pi, trials, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)] at h1
    simp only [zero_add, Nat.Ico_zero_eq_range, Finset.range_one, Finset.prod_singleton, pow_one] at h1
    rw [trials, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _),
      Finset.prod_image (fun a _ b _ h => hinj h), Finset.prod_const, Finset.card_range, h1]
  have ht : Tendsto (fun N : ℕ => (((1 - p : NNReal)) : ENNReal) ^ N) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by
      have : (1 - p : NNReal) < 1 := tsub_lt_self one_pos hp0
      exact_mod_cast this)
  exact le_antisymm (ge_of_tendsto' ht hle) zero_le

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms tapeIso_fires_iff
#print axioms towerTape_fires_iff
#print axioms towerTape_floor_allFalse
#print axioms towerTape_snap_pointwise
#print axioms towerTape_snap_ae
#print axioms towerTape_digit_zero
#print axioms towerTapes_null
end PurityCheck
