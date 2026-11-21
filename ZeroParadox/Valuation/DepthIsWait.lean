-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the depth `endVal` on `End` as the first hitting time `det` of its digit tape, read in `ℕ∞`. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Category.IgnoranceSeam
import ZeroParadox.Valuation.CellsJoint
import ZeroParadox.Valuation.Scale
import Mathlib.NumberTheory.Padics.ProperSpace
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

/-- `Statement:` `NInf.orderIsoWithTopClassical` as `NInf ≃o ℕ∞` (any such gives LPO: `NInf.lpo_of_enatIso`). -/
noncomputable def waitENat : NInf ≃o ℕ∞ := NInf.orderIsoWithTopClassical

/-- `Statement:` any order isomorphism `NInf ≃o ℕ∞` gives LPO; `NInf.lpo_of_iso` at `ℕ∞`. -/
theorem NInf.lpo_of_enatIso (e : NInf ≃o ℕ∞) :
    ∀ r : ℕ → Bool, (∃ n, r n = true) ∨ ∀ n, r n = false :=
  NInf.lpo_of_iso e

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

/-! ### § V. ℤ_[2] through the digit tape
`Reading:` no novelty: the homeomorphism is Example 3.3's digit map at p = 2 (Kingsbery–Levin–Preygel–
Silva, arXiv:math/0701899); the square proved here is for doubling, a one-sided inverse of their shift
T (T(2x) = x), and T's own square is not stated; closest formal prior art, the set-level `WittVector.equiv` with `WittVector.verschiebung_frobenius`.
PROVED here: the commuting square (`padicEndHomeo_semiconj`), continuity and bijectivity
(`padicEndHomeo`), and the valuation match (`endVal_padicEndHomeo`). -/

section PadicEnd
open PadicInt

/-- `Statement:` for `x : ℤ_[2]`, `q2Val x = waitENat (det (padicTape x))`; 0 of ℤ_[2] goes to ⊤ of
    `ℕ∞`. The `det` form without `waitENat`: `det_padicTape_eq_infty_iff`,
    `det_padicTape_eq_ofNat_valuation`. -/
theorem q2Val_eq_wait_padicTape (x : ℤ_[2]) : q2Val x = waitENat (det (padicTape x)) := by
  by_cases hx : x = 0
  · subst hx
    rw [q2Val_bot, (det_padicTape_eq_infty_iff 0).2 rfl]
    exact (waitENat.map_top).symm
  · rw [det_padicTape_eq_ofNat_valuation x hx, waitENat_ofNat]
    simp [q2Val, hx]

/-- `Statement:` `q2Val x = endVal (tapeIso.symm (padicTape x))`. -/
theorem q2Val_eq_endVal_padicTape (x : ℤ_[2]) :
    q2Val x = endVal (tapeIso.symm (padicTape x)) := by
  rw [endVal_eq_wait, OrderIso.apply_symm_apply, q2Val_eq_wait_padicTape]

/-- `Statement:` `(2 * x).appr (k + 1) = 2 * x.appr k`. -/
theorem appr_two_mul_succ (x : ℤ_[2]) (k : ℕ) : (2 * x).appr (k + 1) = 2 * x.appr k := by
  apply appr_two_eq_of _ _ _ (by have := appr_lt x k; rw [pow_succ]; omega)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (appr_spec k x)
  refine ⟨c, ?_⟩
  push_cast at hc ⊢
  rw [pow_succ]
  linear_combination 2 * hc

/-- `Statement:` doubling on ℤ_[2] is prepend-`false` on digit tapes. -/
theorem padicTape_two_mul (x : ℤ_[2]) : padicTape (2 * x) = tapeCons false (padicTape x) := by
  funext n
  cases n with
  | zero =>
    have h0 : (2 * x).appr 0 = 0 := by simp [PadicInt.appr]
    have h1 : (2 * x).appr (0 + 1) = 0 := by rw [appr_two_mul_succ]; simp [PadicInt.appr]
    simp only [padicTape, tapeCons, h0, h1]; simp
  | succ k =>
    simp only [padicTape, tapeCons, appr_two_mul_succ]
    simp

/-- `Statement:` if `2 ^ n ∣ x - y` then `x.appr n = y.appr n`. -/
theorem appr_two_eq_of_dvd {x y : ℤ_[2]} {n : ℕ} (h : (2 : ℤ_[2]) ^ n ∣ x - y) :
    x.appr n = y.appr n := by
  apply appr_two_eq_of _ _ _ (appr_lt y n)
  have hs := Ideal.mem_span_singleton.1 (appr_spec n y)
  have := dvd_add h hs
  convert this using 1; ring

/-- `Statement:` `x.appr (k + 1)` is `x.appr k` plus `2 ^ k` when digit `k` is `true`. -/
theorem appr_two_succ (x : ℤ_[2]) (k : ℕ) :
    x.appr (k + 1) = x.appr k + if padicTape x k then 2 ^ k else 0 := by
  set b := x.appr (k + 1) with hb
  have hbl : b < 2 ^ (k + 1) := by simpa using appr_lt x (k + 1)
  have hmod : x.appr k = b % 2 ^ k := by
    apply appr_two_eq_of _ _ _ (Nat.mod_lt _ (by positivity))
    have hs := Ideal.mem_span_singleton.1 (appr_spec (k + 1) x)
    have h1 : (2 : ℤ_[2]) ^ k ∣ x - (b : ℤ_[2]) :=
      (pow_dvd_pow 2 (Nat.le_succ k)).trans (by simpa using hs)
    have h2 : (2 : ℤ_[2]) ^ k ∣ ((b : ℕ) : ℤ_[2]) - ((b % 2 ^ k : ℕ) : ℤ_[2]) := by
      refine ⟨((b / 2 ^ k : ℕ) : ℤ_[2]), ?_⟩
      have := Nat.div_add_mod b (2 ^ k)
      have h3 : ((b : ℕ) : ℤ_[2]) =
          2 ^ k * ((b / 2 ^ k : ℕ) : ℤ_[2]) + ((b % 2 ^ k : ℕ) : ℤ_[2]) := by
        conv_lhs => rw [← this]
        push_cast; ring
      rw [h3]; ring
    have := dvd_add h1 h2
    convert this using 1; ring
  have hq : b / 2 ^ k < 2 := Nat.div_lt_of_lt_mul (by rwa [pow_succ] at hbl)
  have hdm := Nat.div_add_mod b (2 ^ k)
  have hpos : 0 < 2 ^ k := by positivity
  generalize b / 2 ^ k = q at hq hdm
  rcases (by omega : q = 0 ∨ q = 1) with h | h
  · have hbe : b = x.appr k := by rw [hmod]; rw [h] at hdm; omega
    have : padicTape x k = false := by simp [padicTape, ← hb, hbe]
    rw [this]; simp [hbe]
  · have hbe : b = x.appr k + 2 ^ k := by rw [hmod]; rw [h] at hdm; omega
    have : padicTape x k = true := by simp [padicTape, ← hb, hbe]
    rw [this]; simp [hbe]

/-- `Statement:` `padicTape` is injective. -/
theorem padicTape_injective : Function.Injective padicTape := by
  intro x y h
  have ha : ∀ n, x.appr n = y.appr n := by
    intro n
    induction n with
    | zero => simp [PadicInt.appr]
    | succ n ih => rw [appr_two_succ, appr_two_succ, ih, h]
  rw [← sub_eq_zero, ← two_pow_dvd_forall_iff]
  intro n
  have hx := Ideal.mem_span_singleton.1 (appr_spec n x)
  have hy := Ideal.mem_span_singleton.1 (appr_spec n y)
  have := dvd_sub hx hy
  rw [ha n] at this
  convert this using 1; ring

/-- `Statement:` `padicTape` is surjective: every tape is the digit tape of the limit of its partial
    sums. -/
theorem padicTape_surjective : Function.Surjective padicTape := by
  intro r
  let S : ℕ → ℕ := fun n => ∑ k ∈ Finset.range n, if r k then 2 ^ k else 0
  have hS : ∀ n, S (n + 1) = S n + if r n then 2 ^ n else 0 := fun n => Finset.sum_range_succ _ _
  have hSlt : ∀ n, S n < 2 ^ n := by
    intro n
    induction n with
    | zero => simp [S]
    | succ n ih => rw [hS, pow_succ]; split_ifs <;> omega
  have hSdvd : ∀ n m, n ≤ m → (2 : ℤ_[2]) ^ n ∣ ((S m : ℕ) : ℤ_[2]) - ((S n : ℕ) : ℤ_[2]) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => simp
    | succ m hnm ih =>
      have h2 : (2 : ℤ_[2]) ^ n ∣ (((if r m then 2 ^ m else 0 : ℕ)) : ℤ_[2]) := by
        split_ifs
        · push_cast; exact pow_dvd_pow 2 hnm
        · simp
      rw [hS, Nat.cast_add]
      convert dvd_add ih h2 using 1; ring
  let s : ℕ → ℤ_[2] := fun n => ((S n : ℕ) : ℤ_[2])
  have hnorm : ∀ n m, n ≤ m → dist (s m) (s n) ≤ ((2 : ℕ) : ℝ) ^ (-(n : ℤ)) := by
    intro n m h
    rw [dist_eq_norm]
    exact (norm_le_pow_iff_mem_span_pow _ n).2
      (Ideal.mem_span_singleton.2 (by simpa using hSdvd n m h))
  have hcau : CauchySeq s := by
    refine Metric.cauchySeq_iff'.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N, fun n hn => lt_of_le_of_lt (hnorm N n hn) ?_⟩
    simpa [zpow_neg, one_div, inv_pow] using hN
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  have hxn : ∀ n, dist x (s n) ≤ ((2 : ℕ) : ℝ) ^ (-(n : ℤ)) := fun n =>
    Metric.isClosed_closedBall.mem_of_tendsto hx
      (Filter.eventually_atTop.2 ⟨n, fun m hm => Metric.mem_closedBall.2 (hnorm n m hm)⟩)
  have happr : ∀ n, x.appr n = S n := fun n => by
    apply appr_two_eq_of x n (S n) (hSlt n)
    have := (norm_le_pow_iff_mem_span_pow (x - s n) n).1 (by rw [← dist_eq_norm]; exact hxn n)
    simpa using Ideal.mem_span_singleton.1 this
  refine ⟨x, funext fun k => ?_⟩
  simp only [padicTape, happr, hS]
  cases r k <;> simp

/-- `Statement:` `padicTape` is continuous: digit `k` is constant on balls of radius `2 ^ (-(k + 1))`. -/
theorem continuous_padicTape : Continuous padicTape := by
  refine continuous_pi fun k => continuous_iff_continuousAt.2 fun x => ?_
  refine tendsto_nhds_of_eventually_eq ?_
  have hε : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by positivity
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  have h := (norm_le_pow_iff_mem_span_pow (y - x) (k + 1)).1
    (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hy).le)
  have hd : (2 : ℤ_[2]) ^ (k + 1) ∣ y - x := by simpa using Ideal.mem_span_singleton.1 h
  simp only [padicTape, appr_two_eq_of_dvd hd,
    appr_two_eq_of_dvd ((pow_dvd_pow 2 (Nat.le_succ k)).trans hd)]

/-- `Statement:` `padicTape` as a homeomorphism `ℤ_[2] ≃ₜ (ℕ → Bool)` (Mathlib
    `Continuous.homeoOfEquivCompactToT2`). -/
noncomputable def padicTapeHomeo : ℤ_[2] ≃ₜ (ℕ → Bool) :=
  (show Continuous (Equiv.ofBijective padicTape ⟨padicTape_injective, padicTape_surjective⟩) from
    continuous_padicTape).homeoOfEquivCompactToT2

/-- `Statement:` `padicTapeHomeo x = padicTape x`. -/
theorem padicTapeHomeo_apply (x : ℤ_[2]) : padicTapeHomeo x = padicTape x := rfl

/-- `Statement:` `tapeIso.symm : (ℕ → Bool) → End` is continuous. -/
theorem continuous_tapeIso_symm : Continuous (tapeIso.symm : (ℕ → Bool) → End) :=
  continuous_pi fun n =>
    (continuous_of_discreteTopology.comp (continuous_apply n) :
      Continuous ((fun b : Bool => digitBool.symm b) ∘ fun r : ℕ → Bool => r n)).congr fun _ => rfl

/-- `Statement:` `x ↦ tapeIso.symm (padicTape x)` as a homeomorphism `ℤ_[2] ≃ₜ End`. -/
noncomputable def padicEndHomeo : ℤ_[2] ≃ₜ End :=
  (show Continuous ((Equiv.ofBijective padicTape ⟨padicTape_injective, padicTape_surjective⟩).trans
      tapeIso.symm.toEquiv) from continuous_tapeIso_symm.comp continuous_padicTape).homeoOfEquivCompactToT2

/-- `Statement:` `padicEndHomeo x = tapeIso.symm (padicTape x)`. -/
theorem padicEndHomeo_apply (x : ℤ_[2]) : padicEndHomeo x = tapeIso.symm (padicTape x) := rfl

/-- `Statement:` the commuting square: `padicEndHomeo (2 * x) = boundaryDouble (padicEndHomeo x)`. -/
theorem padicEndHomeo_semiconj :
    Function.Semiconj padicEndHomeo (fun x : ℤ_[2] => 2 * x) boundaryDouble := fun x => by
  show tapeIso.symm (padicTape (2 * x)) = boundaryDouble (tapeIso.symm (padicTape x))
  rw [OrderIso.symm_apply_eq, tapeIso_boundaryDouble, OrderIso.apply_symm_apply, padicTape_two_mul]

/-- `Statement:` `endVal (padicEndHomeo x) = q2Val x`. -/
theorem endVal_padicEndHomeo (x : ℤ_[2]) : endVal (padicEndHomeo x) = q2Val x :=
  (q2Val_eq_endVal_padicTape x).symm

end PadicEnd

-- Statement: axioms (PurityCheck), `digitBool`, `tapeIso`, `tapeIso_boundaryDouble`, `det_tapeCons_false`
--   `[propext, Quot.sound]`; the rest add `Classical.choice`, via `endVal` (an `sInf` in `ℕ∞`) and
--   `waitENat` (any `NInf ≃o ℕ∞` gives LPO, `NInf.lpo_of_enatIso`), and in § V via `PadicInt.appr`.

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms digitBool
#print axioms tapeIso
#print axioms tapeIso_apply
#print axioms waitENat
#print axioms NInf.lpo_of_enatIso
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
#print axioms q2Val_eq_wait_padicTape
#print axioms q2Val_eq_endVal_padicTape
#print axioms appr_two_mul_succ
#print axioms padicTape_two_mul
#print axioms appr_two_eq_of_dvd
#print axioms appr_two_succ
#print axioms padicTape_injective
#print axioms padicTape_surjective
#print axioms continuous_padicTape
#print axioms padicTapeHomeo
#print axioms padicTapeHomeo_apply
#print axioms continuous_tapeIso_symm
#print axioms padicEndHomeo
#print axioms padicEndHomeo_apply
#print axioms padicEndHomeo_semiconj
#print axioms endVal_padicEndHomeo
end PurityCheck
