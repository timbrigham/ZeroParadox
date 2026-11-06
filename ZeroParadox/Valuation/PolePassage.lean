-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the snap arc on the 2-adic sphere `OnePoint ℚ_[2]`, its inversion, and its valuation reading. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCornersBridge
import ZeroParadox.Reals.OrderedField
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.Topology.Path
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The snap arc on the 2-adic sphere: no passage through `∞`, a return in the valuation

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
The `cnfToZp2` tower images (`snap_arc_z2_loop`) on `Sphere`: no route from `0` of `ℚ_[2]` through
`∞` of `Sphere`, the `rInv` image, the `q2Val` return to `⊤` of `ℕ∞`, and the `OnePoint ℝ` control.
§ VI: `HasFirstStep 0` in an ordered group iff not dense. § VII: the dense-valued `HahnSeries ℚ ℚ`.
-/

namespace ZeroParadox

open OnePoint Filter Topology

/-! ### § I. The arc on the sphere, and its image under inversion -/

/-- `Statement:` stage `n` of the arc: the `cnfToZp2` image of `towerNONote n`, as a point of
    `Sphere`. -/
noncomputable def arcS (n : ℕ) : Sphere :=
  OnePoint.some ((cnfToZp2 (towerNONote n) : ℤ_[2]) : ℚ_[2])

/-- `Statement:` on `Sphere`, the arc tends to `0` of `ℚ_[2]` (the third conjunct of
    `snap_arc_z2_loop`, carried along `ℤ_[2] → ℚ_[2] → Sphere`). -/
theorem arcS_tendsto_zero : Tendsto arcS atTop (𝓝 (OnePoint.some (0 : ℚ_[2]))) := by
  have h : Tendsto (fun n => ((cnfToZp2 (towerNONote n) : ℤ_[2]) : ℚ_[2])) atTop (𝓝 0) := by
    have := (continuous_subtype_val (p := fun x : ℚ_[2] => ‖x‖ ≤ 1)).tendsto (0 : ℤ_[2])
    simpa using this.comp tower_converges_to_zero
  exact (OnePoint.continuous_coe.tendsto _).comp h

/-- `Statement:` `rInv ∘ arcS` tends to `∞` of `Sphere`, starts at `∞`, and has stage `n + 1` equal
    to `(2 ^ (n + 1))⁻¹`.
    `Reading:` **INVERSION** — `rInv` carries the arc's loop at `0` of `ℚ_[2]` onto a loop at `∞` of
    `Sphere`; it exchanges the two loops and does not join them (`arc_never_meets_infty`). -/
theorem rInv_arcS :
    Tendsto (fun n => rInv (arcS n)) atTop (𝓝 (∞ : Sphere)) ∧
    rInv (arcS 0) = ∞ ∧
    ∀ n : ℕ, rInv (arcS (n + 1)) = OnePoint.some (((2 : ℚ_[2]) ^ (n + 1))⁻¹) := by
  refine ⟨?_, ?_, fun n => ?_⟩
  · have := (continuous_rInv.tendsto _).comp arcS_tendsto_zero
    rwa [rInv_zero] at this
  · show rInv (OnePoint.some ((cnfToZp2 (towerNONote 0) : ℤ_[2]) : ℚ_[2])) = ∞
    rw [snap_arc_z2_loop.1]; simp
  · have h2 : ((2 : ℚ_[2]) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hstage : cnfToZp2 (towerNONote (n + 1)) = (2 : ℤ_[2]) ^ (n + 1) := by
      rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote, towerImageStep, cnfToZp2_tower_valuation]
    show rInv (OnePoint.some ((cnfToZp2 (towerNONote (n + 1)) : ℤ_[2]) : ℚ_[2])) = _
    have hc : (((2 : ℤ_[2]) ^ (n + 1) : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ (n + 1) := by
      rw [PadicInt.coe_pow]; norm_cast
    rw [hstage, hc, rInv_coe_ne h2]

/-! ### § II. A clopen set separates `0` of `ℚ_[2]` from `∞` of `Sphere` -/

/-- `Statement:` the image in `Sphere` of the closed unit ball of `ℚ_[2]`. -/
def ballS : Set Sphere := OnePoint.some '' Metric.closedBall (0 : ℚ_[2]) 1

/-- `Statement:` `ballS` is clopen in `Sphere`. -/
theorem ballS_isClopen : IsClopen ballS := by
  refine ⟨?_, ?_⟩
  · exact ((isCompact_closedBall (0 : ℚ_[2]) 1).image OnePoint.continuous_coe).isClosed
  · exact OnePoint.isOpenMap_coe _ (IsUltrametricDist.isOpen_closedBall _ one_ne_zero)

/-- `Statement:` every stage of the arc and `0` of `ℚ_[2]` lie in `ballS`, `∞` of `Sphere` does not,
    `∞` is outside the connected component of `0`, and the arc does not tend to `∞`. -/
theorem arc_never_meets_infty :
    (∀ n, arcS n ∈ ballS) ∧ OnePoint.some (0 : ℚ_[2]) ∈ ballS ∧ (∞ : Sphere) ∉ ballS ∧
    (∞ : Sphere) ∉ connectedComponent (OnePoint.some (0 : ℚ_[2])) ∧
    ¬ Tendsto arcS atTop (𝓝 (∞ : Sphere)) := by
  have h0 : OnePoint.some (0 : ℚ_[2]) ∈ ballS := ⟨0, by simp, rfl⟩
  have hinf : (∞ : Sphere) ∉ ballS := by
    rintro ⟨x, -, hx⟩; exact OnePoint.coe_ne_infty x hx
  refine ⟨fun n => ⟨_, by simpa using (cnfToZp2 (towerNONote n)).2, rfl⟩, h0, hinf,
    fun h => hinf (ballS_isClopen.connectedComponent_subset h0 h), fun h => ?_⟩
  exact OnePoint.coe_ne_infty _ (tendsto_nhds_unique arcS_tendsto_zero h)

/-- `Statement:` no continuous path in `Sphere` runs from `0` of `ℚ_[2]` to `∞` of `Sphere`. The
    path form inside `ℚ_[2]`, from a nonzero point to `0`, is `c3_irreversible`. -/
theorem no_path_zero_infty : IsEmpty (Path (OnePoint.some (0 : ℚ_[2]) : Sphere) ∞) := by
  refine ⟨fun γ => ?_⟩
  have hc : IsClopen (γ ⁻¹' ballS) := ballS_isClopen.preimage γ.continuous
  rcases isClopen_iff.1 hc with h | h
  · have : (0 : unitInterval) ∈ γ ⁻¹' ballS := by
      show γ 0 ∈ ballS; rw [γ.source]; exact ⟨0, by simp, rfl⟩
    rw [h] at this; exact this
  · have : (1 : unitInterval) ∈ γ ⁻¹' ballS := by rw [h]; trivial
    have h1 : γ 1 ∈ ballS := this
    rw [γ.target] at h1
    obtain ⟨x, -, hx⟩ := h1
    exact OnePoint.coe_ne_infty x hx

/-! ### § III. The valuation reading: from `⊤` of `ℕ∞` and back to `⊤` -/

/-- `Statement:` `q2Val` of the arc is `⊤` of `ℕ∞` at stage `0`, is `n` at every stage `n ≥ 1`, and
    tends to `⊤`.
    `Reading:` **COINCIDENCE** — the `⊤` the valuation returns to is the value at the same `0` of
    `ℤ_[2]` the arc started from (`q2Val_bot`, `snap_arc_z2_loop`), not `∞` of `Sphere`
    (`arc_never_meets_infty`). The supremum form is `tower_height_floor_reconciliation`. -/
theorem arc_q2Val :
    q2Val (cnfToZp2 (towerNONote 0)) = ⊤ ∧
    (∀ n : ℕ, 1 ≤ n → q2Val (cnfToZp2 (towerNONote n)) = (n : ℕ∞)) ∧
    Tendsto (fun n => q2Val (cnfToZp2 (towerNONote n))) atTop (𝓝 ⊤) := by
  have hfin : ∀ n : ℕ, 1 ≤ n → q2Val (cnfToZp2 (towerNONote n)) = (n : ℕ∞) := by
    intro n hn
    simp [q2Val, snap_arc_z2_loop.2.1 n hn, cnfToZp2_tower_valuation]
  refine ⟨by rw [snap_arc_z2_loop.1]; exact q2Val_bot, hfin, ?_⟩
  refine ENat.tendsto_nhds_top_iff_natCast_lt.2 fun m => ?_
  filter_upwards [eventually_ge_atTop (m + 1)] with n hn
  rw [hfin n (by omega)]
  exact_mod_cast (by omega : m < n)

/-! ### § IV. A run built by joins does not return to `⊥` of `L` at any finite stage -/

/-- `Statement:` in any `ZPSemilattice L`, if `S (n + 1) = join (S n) (z n)` for all `n` and
    `S 1 ≠ bot`, then `S n ≠ bot` for every `n ≥ 1` (by `t_snap_irreversible`).
    `Reading:` the return in `snap_arc_z2_loop` is a limit in `ℤ_[2]`, which this statement does
    not quantify over. -/
theorem join_run_never_returns {L : Type*} [ZPSemilattice L] (S : ℕ → L) (z : ℕ → L)
    (hrun : ∀ n, S (n + 1) = ZPSemilattice.join (S n) (z n)) (h1 : S 1 ≠ ZPSemilattice.bot) :
    ∀ n, 1 ≤ n → S n ≠ ZPSemilattice.bot := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 1 with hk | hk
    · have : k = 0 := by omega
      subst this; exact h1
    · intro hb
      exact t_snap_irreversible (x := ZPSemilattice.bot) (y := S k) (ZPSemilattice.bot_le _)
        (Ne.symm (ih hk)) ⟨z k, (hrun k).symm.trans hb⟩

-- Statement: the arc's step `towerImageStep` lowers the norm at every nonzero point of `ℤ_[2]`
-- (`towerImageStep_norm_drift`), so it is not inflationary in the norm order, as a join is.
example : ∀ x : ℤ_[2], x ≠ 0 → ‖towerImageStep x‖ < ‖x‖ := towerImageStep_norm_drift.1

/-! ### § V. Control: `OnePoint ℝ` -/

/-- `Statement:` `∞` of `OnePoint ℝ` lies in the connected component of `0` of `ℝ`.
    `Reading:` **CARRIER** — on `Sphere` they do not (`arc_never_meets_infty`). -/
theorem real_zero_infty_connected :
    (∞ : OnePoint ℝ) ∈ connectedComponent (OnePoint.some (0 : ℝ)) := by
  rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial

/-! ### § VI. The value chart: a first step at `0` exactly when the order is not dense -/

/-- `Statement:` in a linearly ordered additive commutative group `G`, `HasFirstStep (0 : G)` iff
    `G` is not densely ordered (standard; e.g. Clay–Rolfsen, arXiv:0705.2623, Prop. 1.1). No
    Archimedean hypothesis. The whole-order form, over any
    `Preorder`, is `axb1_fails_everywhere_iff_dense`; translation by `a` carries a cover at `a` to
    one at `0`. -/
theorem cover_at_zero_iff_not_dense {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] : HasFirstStep (0 : G) ↔ ¬ DenselyOrdered G := by
  constructor
  · rintro ⟨a, ha⟩ hd
    obtain ⟨c, h1, h2⟩ := exists_between ha.1
    exact ha.2 h1 h2
  · intro hnd
    rw [axb1_fails_everywhere_iff_dense] at hnd
    push Not at hnd
    obtain ⟨a, ⟨b, hab⟩⟩ := hnd
    exact ⟨b - a, sub_pos.2 hab.1, fun c hc0 hcb =>
      hab.2 (lt_add_of_pos_right a hc0) (lt_sub_iff_add_lt'.1 hcb)⟩

/-- `Statement:` with `[Archimedean G]`, `HasFirstStep (0 : G)` iff `G ≃+o ℤ`, by Mathlib's
    `LinearOrderedAddCommGroup.discrete_iff_not_denselyOrdered`. -/
theorem cover_at_zero_iff_int {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [Archimedean G] : HasFirstStep (0 : G) ↔ Nonempty (G ≃+o ℤ) := by
  rw [cover_at_zero_iff_not_dense, LinearOrderedAddCommGroup.discrete_iff_not_denselyOrdered]

-- Statement: ℤ, the value group of `q2Val` off `⊤`, has its first step at `0`: `0 ⋖ 1`.
example : HasFirstStep (0 : ℤ) := ⟨1, ⟨zero_lt_one, fun _ h1 h2 => by omega⟩⟩
-- Statement: control, ℝ has none (`axb1_fails_in_ordered_field`).
example : ¬ HasFirstStep (0 : ℝ) := axb1_fails_in_ordered_field
-- Statement: in `ℕ∞`, the codomain of `q2Val`, nothing is covered by `⊤` (Mathlib's
-- `WithTop.coe_covBy_top`), so the step `⊤ → 1` of `arc_q2Val` is not a cover.
example : ¬ ∃ b : ℕ∞, b ⋖ ⊤ := by
  rintro ⟨b, hb⟩
  induction b using ENat.recTopCoe with
  | top => exact lt_irrefl _ hb.1
  | coe n => exact not_isMax n (WithTop.coe_covBy_top.1 hb)
-- Statement: the same in `WithTop ℚ`, the codomain of `HahnSeries.addVal ℚ ℚ` (§ VII).
example : ¬ ∃ b : WithTop ℚ, b ⋖ ⊤ := by
  rintro ⟨b, hb⟩
  induction b using WithTop.recTopCoe with
  | top => exact lt_irrefl _ hb.1
  | coe r => exact not_isMax r (WithTop.coe_covBy_top.1 hb)

/-! ### § VII. Control: a dense value group, `HahnSeries ℚ ℚ` -/

-- Statement: `HahnSeries ℚ ℚ` is a field (Mathlib); its additive valuation takes values in `WithTop ℚ`.
noncomputable example : Field (HahnSeries ℚ ℚ) := inferInstance

/-- `Statement:` stage `0` is `0` of `HahnSeries ℚ ℚ`; stage `n + 1` is the monomial
    `single ((n + 1) / 2) 1`. -/
noncomputable def hahnArc : ℕ → HahnSeries ℚ ℚ
  | 0 => 0
  | n + 1 => HahnSeries.single (((n : ℚ) + 1) / 2) (1 : ℚ)

/-- `Statement:` `addVal` of `hahnArc` is `⊤` at stage `0`, is `(n + 1) / 2` at stage `n + 1`, and
    eventually exceeds every rational.
    `Reading:` **CARRIER** — the valuation runs `⊤ → finite → ⊤` over the dense value group `ℚ`, as
    `arc_q2Val` does over `ℤ`; a first step at `0` of the value group is not needed for it. -/
theorem hahnArc_loop :
    HahnSeries.addVal ℚ ℚ (hahnArc 0) = ⊤ ∧
    (∀ n : ℕ, HahnSeries.addVal ℚ ℚ (hahnArc (n + 1)) = ((((n : ℚ) + 1) / 2 : ℚ) : WithTop ℚ)) ∧
    (∀ q : ℚ, ∀ᶠ n in atTop, (q : WithTop ℚ) < HahnSeries.addVal ℚ ℚ (hahnArc n)) := by
  have hs : ∀ n : ℕ,
      HahnSeries.addVal ℚ ℚ (hahnArc (n + 1)) = ((((n : ℚ) + 1) / 2 : ℚ) : WithTop ℚ) :=
    fun n => by
      rw [HahnSeries.addVal_apply]
      exact HahnSeries.orderTop_single one_ne_zero
  refine ⟨by simp [hahnArc], hs, fun q => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * q)
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hs m, WithTop.coe_lt_coe]
  have : (N : ℚ) ≤ m := by exact_mod_cast (by omega : N ≤ m)
  linarith

/-- `Statement:` below every positive value of `addVal` on `HahnSeries ℚ ℚ` lies a smaller positive
    value, taken by a monomial. -/
theorem hahn_no_least_positive_value (x : HahnSeries ℚ ℚ) (hx : x ≠ 0)
    (hpos : (0 : WithTop ℚ) < HahnSeries.addVal ℚ ℚ x) :
    ∃ y : HahnSeries ℚ ℚ, (0 : WithTop ℚ) < HahnSeries.addVal ℚ ℚ y ∧
      HahnSeries.addVal ℚ ℚ y < HahnSeries.addVal ℚ ℚ x := by
  rw [HahnSeries.addVal_apply_of_ne hx] at hpos ⊢
  have h0 : (0 : ℚ) < x.order := WithTop.coe_lt_coe.1 hpos
  refine ⟨HahnSeries.single (x.order / 2) (1 : ℚ), ?_⟩
  rw [HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]
  exact ⟨WithTop.coe_lt_coe.2 (half_pos h0), WithTop.coe_lt_coe.2 (half_lt_self h0)⟩

-- Statement: the value group ℚ has no first step at `0` (`cover_at_zero_iff_not_dense`) and no least
-- positive element (`f_snap_impossible`).
example : ¬ HasFirstStep (0 : ℚ) ∧ ¬ ∃ ε₀ : ℚ, 0 < ε₀ ∧ ¬ ∃ δ : ℚ, 0 < δ ∧ δ < ε₀ :=
  ⟨fun h => cover_at_zero_iff_not_dense.1 h inferInstance, f_snap_impossible⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms arcS
#print axioms arcS_tendsto_zero
#print axioms rInv_arcS
#print axioms ballS
#print axioms ballS_isClopen
#print axioms arc_never_meets_infty
#print axioms no_path_zero_infty
#print axioms arc_q2Val
#print axioms join_run_never_returns
#print axioms real_zero_infty_connected
#print axioms cover_at_zero_iff_not_dense
#print axioms cover_at_zero_iff_int
#print axioms hahnArc
#print axioms hahnArc_loop
#print axioms hahn_no_least_positive_value
end PurityCheck
