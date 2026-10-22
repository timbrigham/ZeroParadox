-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCorners
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Order.Snap
import ZeroParadox.Valuation.Scale
import ZeroParadox.Ordinal.CnfBridge
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Bridge: the four corners are the corners of the tower to ω (shared-shape correspondence)

## Engineer's Take

Looking at it from the top down, this is the very same single point versus an infinite field that we started
out looking at. These four corners are the corners of the whole tower to omega, and the inversion corner is
the framework's own bridge map. The one direction we cannot reverse is the definition of the snap, and it is
the same wall we kept hitting from the start.

This landed when I looked at it from the top down and saw the same single point versus infinite field we
started with. Sometimes it helps to work through this from the ground up. Much of what is here re-derives
results the framework already has, and that is fine. The movement of the thought process itself was what I
needed.

---


## Formal Overview
The four corners of the pole carry the same SHAPE as the corners of the tower — a correspondence, never
a cross-type identity. Argument, fences and structure: `ZeroParadox/Valuation/PoleCornersBridge.md`.
-/

namespace ZeroParadox

open OnePoint

/-! ### § I. The pole embedding into the 2-adic Riemann sphere -/

/-- Embed the abstract pole-pair into the 2-adic Riemann sphere: `zero ↦ 0`, `infty ↦ ∞`. The floor and
its antipode; the two poles the whole four-corner structure is about. -/
noncomputable def poleToSphere : Pole → Sphere
  | Pole.zero => OnePoint.some (0 : ℚ_[2])
  | Pole.infty => (∞ : Sphere)

@[simp] theorem poleToSphere_zero : poleToSphere Pole.zero = OnePoint.some (0 : ℚ_[2]) := rfl

@[simp] theorem poleToSphere_infty : poleToSphere Pole.infty = (∞ : Sphere) := rfl

/-! ### § II. The inversion corner IS the Riemann-sphere inversion -/

/-- **The inversion corner is `z ↦ 1/z`.** Under the pole embedding, the abstract `swap` corner commutes
with the Riemann-sphere inversion `rInv`: `poleToSphere (swap p) = rInv (poleToSphere p)`. The four-corner
inversion is the framework's own `rInv` — the map that, on the tower side (`cnfToZp2`), reverses ordinal
ascent into 2-adic descent. The corner that connects the two poles is the map that connects the tower to the
tree. -/
theorem swap_is_rInv (p : Pole) : poleToSphere (Pole.swap p) = rInv (poleToSphere p) := by
  cases p <;> simp [poleToSphere, Pole.swap, rInv_zero, rInv_infty]

/-- The floor corner and the infinity corner are genuinely the two swapped poles: `swap` moves the zero
corner to `∞` and the infinity corner to `0`, exactly as `rInv_swaps` does on the sphere. -/
theorem corners_are_the_swapped_poles :
    poleToSphere (Pole.swap Pole.zero) = (∞ : Sphere) ∧
      poleToSphere (Pole.swap Pole.infty) = OnePoint.some (0 : ℚ_[2]) := by
  constructor <;> rfl

/-! ### § III. The capstone — a single point versus an infinite field, at both poles at once -/

/-- **The capstone (co-witnessing, shared-shape).** The structure the whole pivot turned on: **two single,
distinct points — the poles — swapped by the inversion, sitting in an infinite field.** That is the "single
point versus infinite field" seen at BOTH ends at once. On the 2-adic sphere: `0` (the floor; the tower's
2-adic limit, `tower_converges_to_zero`) and `∞` (its inversion; the summit side) are the two single points;
`rInv` swaps them; and `ℚ_[2]` is the infinite field between. Via `cnfToZp2` (`CnfBridge`) the **top-down**
view — summit `ε₀` (a single point), tree boundary `ℤ₂` (a field) — is the **inverted image** of the
**bottom-up** view — floor `0` (a single point), its field. One construction, two ends, joined by the map,
never by `=`: `ε₀ = 0` with 0 the 2-adic zero stays a type boundary (it fails to elaborate). The point
and the field are the same object read up or down; the inversion is what turns each into the other. -/
theorem point_and_field_at_the_poles :
    poleToSphere Pole.zero ≠ poleToSphere Pole.infty ∧
      rInv (poleToSphere Pole.zero) = poleToSphere Pole.infty ∧
      rInv (poleToSphere Pole.infty) = poleToSphere Pole.zero ∧
      Infinite ℚ_[2] := by
  refine ⟨?_, ?_, ?_, inferInstance⟩
  · simp [poleToSphere]
  · simp [poleToSphere, rInv_zero]
  · simp [poleToSphere, rInv_infty]

/-! ### § IV. The forbidden direction is the snap (co-witness, shared-shape) -/

/-- **The irreversible direction is the snap.** The two proved one-way facts, sharing one shape:
* **corner side** — `cornerZero` is not injective: falling to a pole forgets the origin, there is no inverse
  (the forbidden transition among the four corners is *un-collapsing*);
* **snap side** — `t_snap_irreversible`: once `x ≼ y` with `x ≠ y`, no join from `y` returns to `x` (the
  forbidden transition of the snap is *returning to the same ⊥*).

These are the same one-way shape on two structures. It is the wall the whole abstraction is bounded by:
everything reversible is free (the ν-symmetries `cornerId`, `swap`); the one thing you cannot reverse is the
fall to the floor. The forbidden direction is not a gap — it is the definition of the snap. Co-witnessed,
never a cross-type `=`. -/
theorem irreversible_direction_is_the_snap {L : Type*} [ZPSemilattice L] {x y : L}
    (hle : ZPSemilattice.join x y = y) (hne : x ≠ y) :
    ¬ Function.Injective Pole.cornerZero ∧ ¬ ∃ z : L, ZPSemilattice.join y z = x :=
  ⟨Pole.cornerZero_not_injective, t_snap_irreversible hle hne⟩

/-! ### § V. The tower as a span of motions: one motion on notations, maps to `Ordinal` and ℤ_[2]

The tower's step on `NONote` is a die motion; `NONote.repr` and `cnfToZp2` are maps of motions
(Mathlib `RelHom` on the steps) out of it, so the two carriers are joined by a span and never by
`=`. Polarity of the 2-adic image motion is read in three views of ℤ_[2]. -/

section TowerSpan

open Motion

/-- `Statement:` the notation `ω^x · 1 + 0`, the tower's step on `NONote`. -/
noncomputable def omegaPowNote (x : NONote) : NONote := NONote.oadd x 1 0 ONote.NFBelow.zero

/-- `Statement:` the next tower stage is `omegaPowNote` of the current one. -/
theorem towerNONote_succ_eq (n : ℕ) : towerNONote (n + 1) = omegaPowNote (towerNONote n) := rfl

/-- `Statement:` the image step on ℤ_[2]: `x ↦ 2^(v x + 1)`, `v` Mathlib's `PadicInt.valuation`. -/
noncomputable def towerImageStep (x : ℤ_[2]) : ℤ_[2] := (2 : ℤ_[2]) ^ (x.valuation + 1)

/-- `Statement:` for every `NONote` `x`, `cnfToZp2 (omegaPowNote x) = towerImageStep (cnfToZp2 x)`. -/
theorem cnfToZp2_omegaPowNote (x : NONote) :
    cnfToZp2 (omegaPowNote x) = towerImageStep (cnfToZp2 x) := by
  have hcast : ((1 : ℕ+) : ℤ_[2]) = 1 := by norm_cast
  show (2 : ℤ_[2]) ^ ((cnfToZp2 x).valuation + 1) * ((1 : ℕ+) : ℤ_[2]) + cnfToZp2 0 =
    towerImageStep (cnfToZp2 x)
  rw [hcast, mul_one, cnfToZp2_zero, add_zero]
  rfl

/-- `Statement:` for every `NONote` `x`, `repr (omegaPowNote x) = ω ^ repr x`. -/
theorem repr_omegaPowNote (x : NONote) :
    NONote.repr (omegaPowNote x) = Ordinal.omega0 ^ NONote.repr x := by
  have hcast : (↑(1 : ℕ+) : Ordinal) = 1 := by norm_cast
  show Ordinal.omega0 ^ NONote.repr x * (↑(1 : ℕ+) : Ordinal) + NONote.repr 0 = _
  rw [hcast, mul_one, show NONote.repr (0 : NONote) = 0 from rfl, add_zero]

/-- `Statement:` `cnfToZp2` is a relation homomorphism from the steps of `ofFun omegaPowNote` to the
    steps of `ofFun towerImageStep`, on all of `NONote`. -/
noncomputable def towerToZp2Hom : (ofFun omegaPowNote).step →r (ofFun towerImageStep).step :=
  ⟨cnfToZp2, fun {a b} (h : b = omegaPowNote a) =>
    show cnfToZp2 b = towerImageStep (cnfToZp2 a) by rw [h]; exact cnfToZp2_omegaPowNote a⟩

/-- `Statement:` `NONote.repr` is a relation homomorphism from the steps of `ofFun omegaPowNote` to
    the steps of `ofFun (ω^·)` on `Ordinal`. -/
noncomputable def towerToOrdHom :
    (ofFun omegaPowNote).step →r (ofFun (fun α : Ordinal => Ordinal.omega0 ^ α)).step :=
  ⟨NONote.repr, fun {a b} (h : b = omegaPowNote a) =>
    show NONote.repr b = _ by rw [h]; exact repr_omegaPowNote a⟩

/-- `Statement:` the `n`-th tower stage has image `towerImageStep^[n] 0` in ℤ_[2] and value
    `fundamentalSeq n` in `Ordinal`. -/
theorem towerNONote_orbits (n : ℕ) :
    cnfToZp2 (towerNONote n) = towerImageStep^[n] 0 ∧
      NONote.repr (towerNONote n) = fundamentalSeq n := by
  refine ⟨?_, towerNONote_repr n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote, ih, Function.iterate_succ_apply']

/-- `Statement:` `towerImageStep x ≠ 0`. -/
theorem towerImageStep_ne_zero (x : ℤ_[2]) : towerImageStep x ≠ 0 := pow_ne_zero _ two_ne_zero

/-- `Statement:` the valuation of `towerImageStep x` is the valuation of `x` plus one. -/
theorem valuation_towerImageStep (x : ℤ_[2]) :
    (towerImageStep x).valuation = x.valuation + 1 := by
  rw [towerImageStep, PadicInt.valuation_pow,
    show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_cast, PadicInt.valuation_p, mul_one]

/-- `Statement:` `‖towerImageStep x‖ = 2 ^ (-(v x + 1))`. -/
theorem norm_towerImageStep (x : ℤ_[2]) :
    ‖towerImageStep x‖ = (2 : ℝ) ^ (-((x.valuation : ℤ) + 1)) := by
  rw [PadicInt.norm_eq_zpow_neg_valuation (towerImageStep_ne_zero x), valuation_towerImageStep]
  push_cast
  ring_nf

/-- `Statement:` the view of ℤ_[2] lifted along the norm (ℤ_[2]'s 0 least). -/
noncomputable abbrev z2NormView : Preorder ℤ_[2] := Preorder.lift (‖·‖ : ℤ_[2] → ℝ)

/-- `Statement:` the view lifted along `q2Val` (ℤ_[2]'s 0 greatest). -/
noncomputable abbrev z2Q2ValView : Preorder ℤ_[2] := Preorder.lift q2Val

/-- `Statement:` the view lifted along Mathlib's `PadicInt.valuation` (`valuation 0 = 0`, so ℤ_[2]'s 0
    least). -/
noncomputable abbrev z2ValuationView : Preorder ℤ_[2] :=
  Preorder.lift (PadicInt.valuation : ℤ_[2] → ℕ)

/-- `Statement:` under `z2ValuationView`, OVER of `ofFun towerImageStep` raises at every point. -/
theorem towerImageStep_raises_valuation :
    @StepRaises ℤ_[2] (ofFun towerImageStep) z2ValuationView.toLE := by
  rintro x y rfl
  show x.valuation ≤ (towerImageStep x).valuation
  rw [valuation_towerImageStep]
  omega

/-- `Statement:` the norm of `towerImageStep x` is strictly below `‖x‖` at every `x ≠ 0`, and
    strictly above `‖0‖` at `0`. -/
theorem towerImageStep_norm_drift :
    (∀ x : ℤ_[2], x ≠ 0 → ‖towerImageStep x‖ < ‖x‖) ∧ ‖(0 : ℤ_[2])‖ < ‖towerImageStep 0‖ := by
  refine ⟨fun x hx => ?_, by rw [norm_zero]; exact norm_pos_iff.2 (towerImageStep_ne_zero 0)⟩
  rw [norm_towerImageStep, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  exact zpow_lt_zpow_right₀ (by norm_num) (by omega)

/-- `Statement:` `q2Val x < q2Val (towerImageStep x)` at every `x ≠ 0`, and
    `q2Val (towerImageStep 0) < q2Val 0`. -/
theorem towerImageStep_q2Val_drift :
    (∀ x : ℤ_[2], x ≠ 0 → q2Val x < q2Val (towerImageStep x)) ∧
      q2Val (towerImageStep 0) < q2Val 0 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · exact not_le.1 (fun h =>
      not_le.2 (towerImageStep_norm_drift.1 x hx) ((q2Val_le_iff_norm_le _ _).1 h))
  · rw [q2Val_bot, lt_top_iff_ne_top]
    exact fun h => towerImageStep_ne_zero 0 (q2Val_unique _ h)

/-- `Statement:` under `z2NormView` and under `z2Q2ValView`, OVER of `ofFun towerImageStep` neither
    raises nor lowers. -/
theorem towerImageStep_no_polarity_norm_q2Val :
    ¬ @StepLowers ℤ_[2] (ofFun towerImageStep) z2NormView.toLE ∧
    ¬ @StepRaises ℤ_[2] (ofFun towerImageStep) z2NormView.toLE ∧
    ¬ @StepRaises ℤ_[2] (ofFun towerImageStep) z2Q2ValView.toLE ∧
    ¬ @StepLowers ℤ_[2] (ofFun towerImageStep) z2Q2ValView.toLE := by
  have hd := towerImageStep_norm_drift
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (h 0 (towerImageStep 0) rfl) (not_le.2 hd.2)
  · exact absurd (h 1 (towerImageStep 1) rfl) (not_le.2 (hd.1 1 one_ne_zero))
  · exact absurd (h 0 (towerImageStep 0) rfl) (not_le.2 towerImageStep_q2Val_drift.2)
  · exact absurd (h 1 (towerImageStep 1) rfl) (not_le.2 (towerImageStep_q2Val_drift.1 1 one_ne_zero))

/-- `Statement:` the nonzero points of ℤ_[2]. -/
def z2Nonzero : Set ℤ_[2] := {x | x ≠ 0}

/-- `Statement:` `z2Nonzero` is UP-closed for `ofFun towerImageStep`. -/
theorem z2Nonzero_upClosed : (ofFun towerImageStep).UpClosed z2Nonzero := by
  intro x hx y hy
  have : y = x := Part.mem_some_iff.1 hy
  rw [this]
  exact hx

/-- `Statement:` restricted to `z2Nonzero`, OVER of `ofFun towerImageStep` lowers in the norm view and
    raises in the `q2Val` view, the second from the first by `stepRaises_iff_of_dual`. -/
theorem towerImageStep_nonzero_polarity :
    @StepLowers z2Nonzero ((ofFun towerImageStep).restrict z2Nonzero z2Nonzero_upClosed)
        (Preorder.lift (fun x : z2Nonzero => ‖(x : ℤ_[2])‖)).toLE ∧
    @StepRaises z2Nonzero ((ofFun towerImageStep).restrict z2Nonzero z2Nonzero_upClosed)
        (Preorder.lift (fun x : z2Nonzero => q2Val (x : ℤ_[2]))).toLE := by
  have hl : @StepLowers z2Nonzero ((ofFun towerImageStep).restrict z2Nonzero z2Nonzero_upClosed)
      (Preorder.lift (fun x : z2Nonzero => ‖(x : ℤ_[2])‖)).toLE := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ (h : y = towerImageStep x)
    show ‖y‖ ≤ ‖x‖
    rw [h]
    exact (towerImageStep_norm_drift.1 x hx).le
  exact ⟨hl, (stepRaises_iff_of_dual _ _ (fun a b => q2Val_le_iff_norm_le a.1 b.1) _).2 hl⟩

/-- `Statement:` in `Ordinal`'s order, OVER of `ofFun (ω^·)` raises at every point. -/
theorem omegaPow_stepRaises :
    StepRaises (ofFun (fun α : Ordinal => Ordinal.omega0 ^ α)) := by
  rintro x y rfl
  exact Ordinal.right_le_opow x Ordinal.one_lt_omega0

/-- `Statement:` from stage `n` to stage `n + 1`: the ordinal value rises; the 2-adic image's
    valuation rises; at `n = 0` the image's norm rises and its `q2Val` falls; for `n ≥ 1` the image's
    norm falls and its `q2Val` rises. -/
theorem tower_polarity (n : ℕ) :
    NONote.repr (towerNONote n) < NONote.repr (towerNONote (n + 1)) ∧
    (cnfToZp2 (towerNONote n)).valuation < (cnfToZp2 (towerNONote (n + 1))).valuation ∧
    (n = 0 → ‖cnfToZp2 (towerNONote n)‖ < ‖cnfToZp2 (towerNONote (n + 1))‖ ∧
       q2Val (cnfToZp2 (towerNONote (n + 1))) < q2Val (cnfToZp2 (towerNONote n))) ∧
    (1 ≤ n → ‖cnfToZp2 (towerNONote (n + 1))‖ < ‖cnfToZp2 (towerNONote n)‖ ∧
       q2Val (cnfToZp2 (towerNONote n)) < q2Val (cnfToZp2 (towerNONote (n + 1)))) := by
  have hne : 1 ≤ n → cnfToZp2 (towerNONote n) ≠ 0 := snap_arc_z2_loop.2.1 n
  refine ⟨(tower_orders_agree n (n + 1)).2 ?_, ?_, ?_, ?_⟩
  · rw [cnfToZp2_tower_valuation, cnfToZp2_tower_valuation]; omega
  · rw [cnfToZp2_tower_valuation, cnfToZp2_tower_valuation]; omega
  · rintro rfl
    have h0 : cnfToZp2 (towerNONote 0) = 0 := cnfToZp2_zero
    rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote, h0]
    exact ⟨towerImageStep_norm_drift.2, towerImageStep_q2Val_drift.2⟩
  · intro hn
    rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote]
    exact ⟨towerImageStep_norm_drift.1 _ (hne hn), towerImageStep_q2Val_drift.1 _ (hne hn)⟩

/-- `Statement:` in `ofFun towerImageStep` every point steps elsewhere. -/
theorem towerImageStep_leavesAt (x : ℤ_[2]) : (ofFun towerImageStep).LeavesAt x := by
  rw [leavesAt_ofFun_iff]
  intro h
  have := congrArg PadicInt.valuation h
  rw [valuation_towerImageStep] at this
  omega

/-- `Statement:` no relation homomorphism from the steps of `ofFun (ω^·)` on `Ordinal` to the steps of
    `ofFun towerImageStep`: ε₀ steps to itself in the first, and no point does in the second. -/
theorem isEmpty_relHom_omegaPow_towerImageStep :
    IsEmpty ((ofFun (fun α : Ordinal => Ordinal.omega0 ^ α)).step →r
      (ofFun towerImageStep).step) :=
  isEmpty_relHom_of_step_self (y := Ordinal.epsilon 0) (Ordinal.omega0_opow_epsilon 0).symm
    (fun t (ht : t = towerImageStep t) =>
      (leavesAt_ofFun_iff towerImageStep t).1 (towerImageStep_leavesAt t) ht.symm)

end TowerSpan

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms poleToSphere
#print axioms swap_is_rInv
#print axioms corners_are_the_swapped_poles
#print axioms point_and_field_at_the_poles
#print axioms irreversible_direction_is_the_snap
#print axioms omegaPowNote
#print axioms towerNONote_succ_eq
#print axioms towerImageStep
#print axioms cnfToZp2_omegaPowNote
#print axioms repr_omegaPowNote
#print axioms towerToZp2Hom
#print axioms towerToOrdHom
#print axioms towerNONote_orbits
#print axioms towerImageStep_ne_zero
#print axioms valuation_towerImageStep
#print axioms norm_towerImageStep
#print axioms z2NormView
#print axioms z2Q2ValView
#print axioms z2ValuationView
#print axioms towerImageStep_raises_valuation
#print axioms towerImageStep_norm_drift
#print axioms towerImageStep_q2Val_drift
#print axioms towerImageStep_no_polarity_norm_q2Val
#print axioms z2Nonzero
#print axioms z2Nonzero_upClosed
#print axioms towerImageStep_nonzero_polarity
#print axioms omegaPow_stepRaises
#print axioms tower_polarity
#print axioms towerImageStep_leavesAt
#print axioms isEmpty_relHom_omegaPow_towerImageStep
end PurityCheck
