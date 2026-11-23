-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): multiplier maps `z ↦ c z` on `OnePoint ℚ_[2]` up to topological conjugacy, the 2-adic companion to BendDie: the discrete twist `u ^ v(z) * z`, every multiplier with `‖c‖ ≠ 1` conjugate to `×2`, four commuting flips, four multipliers on ℂ, and attracting and repelling fixed points of a multiplier map on `OnePoint K`. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.BendDie
import ZeroParadox.Valuation.RiemannSphere
import Mathlib.Tactic

/-!
# The 2-adic bend: multiplier maps on `OnePoint ℚ_[2]` up to topological conjugacy

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

Formal Overview (AI-assisted), citations and prior art: the ride-along `TwoAdicBend.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology ComplexConjugate

/-! ## § I. Topological conjugacy of multiplier maps on `OnePoint K` -/

section Generic
variable {K : Type*} [NormedField K] [ProperSpace K]

/-- `Statement:` a homeomorphism of `OnePoint K` conjugates the multiplier map `lmScale c` to
    `lmScale d`. -/
def ScaleConj (c d : K) (hc : c ≠ 0) (hd : d ≠ 0) : Prop :=
  ∃ e : OnePoint K ≃ₜ OnePoint K, ∀ x, e (lmScale c hc x) = lmScale d hd (e x)

omit [ProperSpace K] in
/-- `Statement:` `ScaleConj` is reflexive. -/
theorem scaleConj_refl (c : K) (hc : c ≠ 0) : ScaleConj c c hc hc :=
  ⟨Homeomorph.refl _, fun _ => rfl⟩

omit [ProperSpace K] in
/-- `Statement:` `ScaleConj` is symmetric. -/
theorem scaleConj_symm {c d : K} {hc : c ≠ 0} {hd : d ≠ 0}
    (h : ScaleConj c d hc hd) : ScaleConj d c hd hc := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun y => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

omit [ProperSpace K] in
/-- `Statement:` `ScaleConj` is transitive. -/
theorem scaleConj_trans {c d f : K} {hc : c ≠ 0} {hd : d ≠ 0} {hf : f ≠ 0}
    (h1 : ScaleConj c d hc hd) (h2 : ScaleConj d f hd hf) : ScaleConj c f hc hf := by
  obtain ⟨e1, he1⟩ := h1
  obtain ⟨e2, he2⟩ := h2
  refine ⟨e1.trans e2, fun x => ?_⟩
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, he1, he2]

omit [ProperSpace K] in
/-- `Statement:` `ScaleConj` respects equality of the multipliers. -/
theorem scaleConj_congr {c d c' d' : K} {hc : c ≠ 0} {hd : d ≠ 0} {hc' : c' ≠ 0}
    {hd' : d' ≠ 0} (h1 : c = c') (h2 : d = d') (h : ScaleConj c d hc hd) :
    ScaleConj c' d' hc' hd' := by
  subst h1 h2; exact h

/-- `Statement:` conjugate multipliers have limit motions related by a `Motion.HomeoIso`
    (`lmHomeoIsoOfConj`). -/
theorem scaleConj_homeoIso {c d : K} {hc : c ≠ 0} {hd : d ≠ 0} (h : ScaleConj c d hc hd) :
    Nonempty (Motion.HomeoIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale d hd) (lmScale d hd).continuous)) := by
  obtain ⟨e, he⟩ := h
  exact ⟨lmHomeoIsoOfConj _ e he⟩

/-- `Statement:` inversion `onePointInvHomeo` conjugates `×c` to `×c⁻¹`, every `c ≠ 0`. -/
theorem scaleConj_inv (c : K) (hc : c ≠ 0) : ScaleConj c c⁻¹ hc (inv_ne_zero hc) :=
  ⟨onePointInvHomeo, lm_onePointInv_conj_scale c c⁻¹ hc (inv_ne_zero hc) (mul_inv_cancel₀ hc)⟩

omit [ProperSpace K] in
/-- `Statement:` a homeomorphism `e` of `K` with `e (c z) = d (e z)` gives `ScaleConj c d`
    (`Homeomorph.onePointCongr`). -/
theorem scaleConj_of_homeo {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) (e : K ≃ₜ K)
    (h : ∀ z, e (c * z) = d * e z) : ScaleConj c d hc hd := by
  refine ⟨Homeomorph.onePointCongr e, fun x => ?_⟩
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    show OnePoint.some (e (c * z)) = OnePoint.some (d * e z)
    rw [h]

end Generic

/-! ## § II. The valuation on `ℚ_[2]` -/

section Base

/-- `Statement:` `‖u‖ = 1` gives `v(u) = 0`. -/
theorem tb_val_eq_zero_of_norm_one {u : ℚ_[2]} (hu : ‖u‖ = 1) : u.valuation = 0 := by
  have h1 := (Padic.norm_le_one_iff_val_nonneg u).1 hu.le
  have h2 := (Padic.norm_le_one_iff_val_nonneg u⁻¹).1 (by rw [norm_inv, hu, inv_one])
  rw [Padic.valuation_inv] at h2
  omega

/-- `Statement:` `‖u‖ = 1` gives `u ≠ 0`. -/
theorem tb_ne_zero_of_norm_one {u : ℚ_[2]} (hu : ‖u‖ = 1) : u ≠ 0 := by
  rintro rfl; simp at hu

/-- `Statement:` `‖u‖ = 1` gives `‖u⁻¹‖ = 1`. -/
theorem tb_norm_inv_one {u : ℚ_[2]} (hu : ‖u‖ = 1) : ‖u⁻¹‖ = 1 := by
  rw [norm_inv, hu, inv_one]

/-- `Statement:` nonzero points of equal norm have equal valuation. -/
theorem tb_val_eq_of_norm_eq {y z : ℚ_[2]} (hy : y ≠ 0) (hz : z ≠ 0) (h : ‖y‖ = ‖z‖) :
    y.valuation = z.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hy, Padic.norm_eq_zpow_neg_valuation hz] at h
  have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < ((2 : ℕ) : ℝ)) (by norm_num) h
  omega

/-- `Statement:` `‖y - z‖ < ‖z‖` gives `‖y‖ = ‖z‖` (the ultrametric inequality). -/
theorem tb_norm_eq_of_near {y z : ℚ_[2]} (h : ‖y - z‖ < ‖z‖) : ‖y‖ = ‖z‖ := by
  have := Padic.add_eq_max_of_ne h.ne
  rw [sub_add_cancel] at this
  rw [this, max_eq_right h.le]

/-- `Statement:` the valuation is locally constant at every nonzero point of `ℚ_[2]`. -/
theorem tb_val_eventually_eq {z : ℚ_[2]} (hz : z ≠ 0) :
    ∀ᶠ y in 𝓝 z, y.valuation = z.valuation := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  filter_upwards [Metric.ball_mem_nhds z hpos] with y hy
  rw [Metric.mem_ball, dist_eq_norm] at hy
  have hn := tb_norm_eq_of_near hy
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [norm_zero] at hn; exact hpos.ne hn
  exact tb_val_eq_of_norm_eq hy0 hz hn

/-- `Statement:` `v(2) = 1` in `ℚ_[2]`. -/
theorem tb_val_two : (2 : ℚ_[2]).valuation = 1 := by
  have := Padic.valuation_p (p := 2); exact_mod_cast this

/-- `Statement:` `v(3) = 0` in `ℚ_[2]`. -/
theorem tb_val_three : (3 : ℚ_[2]).valuation = 0 := by
  rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rfl

/-- `Statement:` `v(4) = 2` in `ℚ_[2]`. -/
theorem tb_val_four : (4 : ℚ_[2]).valuation = 2 := by
  rw [show (4 : ℚ_[2]) = 2 * 2 by norm_num, Padic.valuation_mul two_ne_zero two_ne_zero,
    tb_val_two]; rfl

/-- `Statement:` `‖3‖ = 1` in `ℚ_[2]`. -/
theorem tb_norm_three : ‖(3 : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (by norm_num), tb_val_three]; simp

end Base

/-! ## § III. The discrete twist `T_u z = u ^ v(z) * z` -/

section DTwist

/-- `Statement:` the discrete twist `z ↦ u ^ v(z) * z`; `v 0 = 0`, so `0 ↦ 0`. -/
noncomputable def dTwist (u z : ℚ_[2]) : ℚ_[2] := u ^ z.valuation * z

/-- `Statement:` `dTwist u 0 = 0`. -/
theorem dTwist_zero (u : ℚ_[2]) : dTwist u 0 = 0 := by simp [dTwist]

/-- `Statement:` for `‖u‖ = 1` the twist preserves the norm. -/
theorem dTwist_norm {u : ℚ_[2]} (hu : ‖u‖ = 1) (z : ℚ_[2]) : ‖dTwist u z‖ = ‖z‖ := by
  rw [dTwist, norm_mul, norm_zpow, hu, one_zpow, one_mul]

/-- `Statement:` for `‖u‖ = 1` the twist preserves the valuation. -/
theorem dTwist_valuation {u : ℚ_[2]} (hu : ‖u‖ = 1) (z : ℚ_[2]) :
    (dTwist u z).valuation = z.valuation := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [dTwist]
  · have h0 : dTwist u z ≠ 0 := by
      rw [← norm_ne_zero_iff, dTwist_norm hu]; exact norm_ne_zero_iff.2 hz
    exact tb_val_eq_of_norm_eq h0 hz (dTwist_norm hu z)

/-- `Statement:` for `‖u‖ = 1` the twist by `u⁻¹` undoes the twist by `u`. -/
theorem dTwist_inv_left {u : ℚ_[2]} (hu : ‖u‖ = 1) (z : ℚ_[2]) :
    dTwist u⁻¹ (dTwist u z) = z := by
  have hu0 := tb_ne_zero_of_norm_one hu
  show u⁻¹ ^ (dTwist u z).valuation * dTwist u z = z
  rw [dTwist_valuation hu, dTwist, inv_zpow, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hu0), one_mul]

/-- `Statement:` for `‖u‖ = 1` the twist is continuous on `ℚ_[2]`, `0` included. -/
theorem dTwist_continuous {u : ℚ_[2]} (hu : ‖u‖ = 1) : Continuous (dTwist u) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · show Tendsto (dTwist u) (𝓝 0) (𝓝 (dTwist u 0))
    rw [dTwist_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp only [dTwist_norm hu]
    exact tendsto_norm_zero
  · have hev : (fun y => u ^ z.valuation * y) =ᶠ[𝓝 z] dTwist u := by
      filter_upwards [tb_val_eventually_eq hz] with y hy
      simp [dTwist, hy]
    exact ((continuous_const.mul continuous_id).continuousAt).congr hev

/-- `Statement:` for `‖u‖ = 1` the twist as a homeomorphism of `ℚ_[2]`, inverse the twist by
    `u⁻¹`. -/
noncomputable def dTwistHomeo (u : ℚ_[2]) (hu : ‖u‖ = 1) : ℚ_[2] ≃ₜ ℚ_[2] where
  toFun := dTwist u
  invFun := dTwist u⁻¹
  left_inv := dTwist_inv_left hu
  right_inv z := by simpa using dTwist_inv_left (tb_norm_inv_one hu) z
  continuous_toFun := dTwist_continuous hu
  continuous_invFun := dTwist_continuous (tb_norm_inv_one hu)

/-- `Statement:` for `‖u‖ = 1` the twist is an isometry of `ℚ_[2]` for the distance
    `‖x - y‖` of the 2-adic norm. -/
theorem dTwist_isometry {u : ℚ_[2]} (hu : ‖u‖ = 1) : Isometry (dTwist u) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [dTwist_zero, dTwist_norm hu]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [dTwist_zero, dTwist_norm hu]
  by_cases hv : x.valuation = y.valuation
  · have : dTwist u x - dTwist u y = u ^ x.valuation * (x - y) := by
      simp only [dTwist, hv]; ring
    rw [this, norm_mul, norm_zpow, hu, one_zpow, one_mul]
  · have hn : ‖x‖ ≠ ‖y‖ := fun h => hv (tb_val_eq_of_norm_eq hx hy h)
    have key : ∀ a b : ℚ_[2], ‖a‖ ≠ ‖b‖ → ‖a - b‖ = max ‖a‖ ‖b‖ := by
      intro a b hab
      rw [sub_eq_add_neg, Padic.add_eq_max_of_ne (by rwa [norm_neg]), norm_neg]
    rw [key _ _ (by rwa [dTwist_norm hu, dTwist_norm hu]), dTwist_norm hu, dTwist_norm hu,
      key _ _ hn]

/-- `Statement:` for `‖u‖ = 1` and `c ≠ 0`, `dTwist u (c z) = (u ^ v(c) * c) * dTwist u z`. -/
theorem dTwist_conj_mul {u c : ℚ_[2]} (hu : ‖u‖ = 1) (hc : c ≠ 0) (z : ℚ_[2]) :
    dTwist u (c * z) = (u ^ c.valuation * c) * dTwist u z := by
  have hu0 := tb_ne_zero_of_norm_one hu
  rcases eq_or_ne z 0 with rfl | hz
  · simp [dTwist]
  · simp only [dTwist, Padic.valuation_mul hc hz, zpow_add₀ hu0]; ring

/-- `Statement:` for `‖u‖ = 1`, `u ^ v(c) * c = d` gives `ScaleConj c d` on `OnePoint ℚ_[2]`. -/
theorem dTwist_scaleConj {u c d : ℚ_[2]} (hu : ‖u‖ = 1) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : u ^ c.valuation * c = d) : ScaleConj c d hc hd :=
  scaleConj_of_homeo hc hd (dTwistHomeo u hu) (fun z => by
    show dTwist u (c * z) = d * dTwist u z
    rw [dTwist_conj_mul hu hc, h])

/-- `Statement:` for `‖u‖ = 1`, `×2` and `×(2u)` satisfy `ScaleConj` on `OnePoint ℚ_[2]`. -/
theorem dTwist_scaleConj_two {u : ℚ_[2]} (hu : ‖u‖ = 1) (hd : 2 * u ≠ 0) :
    ScaleConj 2 (2 * u) two_ne_zero hd :=
  dTwist_scaleConj hu two_ne_zero hd (by rw [tb_val_two, zpow_one, mul_comm])

/-- `Statement:` `×2` and `×6` on `OnePoint ℚ_[2]` have limit motions related by a
    `Motion.HomeoIso` (`u = 3`). -/
theorem dTwist_two_six :
    Nonempty (Motion.HomeoIso
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous)
      (limitMotion (lmScale (6 : ℚ_[2]) (by norm_num)) (lmScale _ _).continuous)) :=
  scaleConj_homeoIso (dTwist_scaleConj tb_norm_three two_ne_zero _
    (by rw [tb_val_two, zpow_one]; norm_num))

/-- `Statement:` CONTROL: for `‖u‖ = 1` the twist's multiplier `u ^ v(c) * c` has valuation
    `v(c)`. -/
theorem dTwist_mult_valuation {u c : ℚ_[2]} (hu : ‖u‖ = 1) (hc : c ≠ 0) :
    (u ^ c.valuation * c).valuation = c.valuation := by
  have hu0 := tb_ne_zero_of_norm_one hu
  rw [Padic.valuation_mul (zpow_ne_zero _ hu0) hc, Padic.valuation_zpow,
    tb_val_eq_zero_of_norm_one hu, mul_zero, zero_add]

/-- `Statement:` CONTROL: no `u` with `‖u‖ = 1` has `u ^ v(2) * 2 = 4`; with `dTwist_conj_mul`, no
    twist sends `×2` to `×4`. `Reading:` a fact about this construction; `scaleConj_two_four`
    conjugates them. -/
theorem dTwist_not_two_four {u : ℚ_[2]} (hu : ‖u‖ = 1) :
    u ^ (2 : ℚ_[2]).valuation * 2 ≠ 4 := by
  intro h
  have := dTwist_mult_valuation hu (two_ne_zero : (2 : ℚ_[2]) ≠ 0)
  rw [h, tb_val_four, tb_val_two] at this
  omega

end DTwist

/-! ## § IV. The step merge: every `‖c‖ ≠ 1` is conjugate to `×2` -/

section Step

/-- `Statement:` `‖x‖ = 2 ^ (-v(x))` for `x ≠ 0` of `ℚ_[2]`. -/
theorem tb_norm {x : ℚ_[2]} (hx : x ≠ 0) : ‖x‖ = (2 : ℝ) ^ (-x.valuation) := by
  have := Padic.norm_eq_zpow_neg_valuation hx
  simpa using this

/-- `Statement:` for nonzero `x`, `y`: `‖x‖ < ‖y‖ ↔ v(y) < v(x)`. -/
theorem tb_norm_lt_iff {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖x‖ < ‖y‖ ↔ y.valuation < x.valuation := by
  rw [tb_norm hx, tb_norm hy, zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  constructor <;> intro h <;> omega

/-- `Statement:` `0 < ‖2‖` in `ℚ_[2]`. -/
theorem tb_norm_two_pos : 0 < ‖(2 : ℚ_[2])‖ := norm_pos_iff.2 two_ne_zero

/-- `Statement:` `‖2‖ < 1` in `ℚ_[2]`. -/
theorem tb_norm_two_lt_one : ‖(2 : ℚ_[2])‖ < 1 := by
  have := (tb_norm_lt_iff two_ne_zero one_ne_zero).2
    (by rw [tb_val_two, Padic.valuation_one]; norm_num)
  rwa [norm_one] at this

/-- `Statement:` `v(x / y) = v(x) - v(y)` for nonzero `x`, `y`. -/
theorem tb_val_div {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).valuation = x.valuation - y.valuation := by
  rw [div_eq_mul_inv, Padic.valuation_mul hx (inv_ne_zero hy), Padic.valuation_inv]; ring

/-- `Statement:` `v(2 ^ n) = n`, `n : ℤ`. -/
theorem tb_val_two_zpow (n : ℤ) : ((2 : ℚ_[2]) ^ n).valuation = n := by
  rw [Padic.valuation_zpow, tb_val_two, mul_one]

/-- `Statement:` `v(2 ^ n) = n`, `n : ℕ`. -/
theorem tb_val_two_pow (n : ℕ) : ((2 : ℚ_[2]) ^ n).valuation = n := by
  rw [Padic.valuation_pow, tb_val_two, mul_one]

/-- `Statement:` every `w` with `‖w‖ = 1` has `‖w - 1‖ < 1`. -/
theorem tb_res {w : ℚ_[2]} (hw : ‖w‖ = 1) : ‖w - 1‖ < 1 := by
  set x : ℤ_[2] := ⟨w, hw.le⟩
  obtain ⟨n, hn, hmem⟩ := PadicInt.exists_mem_range x
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hmem
  interval_cases n
  · rw [Nat.cast_zero, sub_zero, PadicInt.norm_def] at hmem
    exact absurd hw (ne_of_lt hmem)
  · rw [Nat.cast_one, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one] at hmem
    exact hmem

/-- `Statement:` `w` is a unit of `ℤ_[2]`: `w ≠ 0` and `v(w) = 0`. -/
def TbIsUnit (w : ℚ_[2]) : Prop := w ≠ 0 ∧ w.valuation = 0

/-- `Statement:` `t ≠ 0` with `0 ≤ v(t) ≤ k`. -/
def TbInShells (k : ℕ) (t : ℚ_[2]) : Prop := t ≠ 0 ∧ 0 ≤ t.valuation ∧ t.valuation ≤ k

/-- `Statement:` `TbIsUnit w` gives `‖w‖ = 1`. -/
theorem tbIsUnit_norm {w : ℚ_[2]} (h : TbIsUnit w) : ‖w‖ = 1 := by
  rw [tb_norm h.1, h.2]; simp

/-- `Statement:` `‖w‖ = 1` gives `TbIsUnit w`. -/
theorem tbIsUnit_of_norm {w : ℚ_[2]} (h : ‖w‖ = 1) : TbIsUnit w :=
  ⟨tb_ne_zero_of_norm_one h, tb_val_eq_zero_of_norm_one h⟩

/-- `Statement:` a unit `w` with `‖w - 1‖ < ‖2‖` has `(w + 1) / 2` a unit. -/
theorem tbU_A {w : ℚ_[2]} (_hw : TbIsUnit w) (h : ‖w - 1‖ < ‖(2 : ℚ_[2])‖) :
    TbIsUnit ((w + 1) / 2) := by
  have hn : ‖w + 1‖ = ‖(2 : ℚ_[2])‖ :=
    tb_norm_eq_of_near (by rw [show w + 1 - 2 = w - 1 by ring]; exact h)
  have h1 : w + 1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hn; exact tb_norm_two_pos.ne hn
  have hv : (w + 1).valuation = 1 := by
    rw [tb_val_eq_of_norm_eq h1 two_ne_zero hn, tb_val_two]
  refine ⟨div_ne_zero h1 two_ne_zero, ?_⟩
  rw [tb_val_div h1 two_ne_zero, hv, tb_val_two]; rfl

/-- `Statement:` a unit `w` with `¬ ‖w - 1‖ < ‖2‖` has `v(w - 1) = 1`. -/
theorem tbU_B {w : ℚ_[2]} (hw : TbIsUnit w) (h : ¬ ‖w - 1‖ < ‖(2 : ℚ_[2])‖) :
    w - 1 ≠ 0 ∧ (w - 1).valuation = 1 := by
  have hne : w - 1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact h tb_norm_two_pos
  refine ⟨hne, ?_⟩
  have hlt : ‖w - 1‖ < ‖(1 : ℚ_[2])‖ := by rw [norm_one]; exact tb_res (tbIsUnit_norm hw)
  rw [tb_norm_lt_iff hne one_ne_zero, Padic.valuation_one] at hlt
  rw [tb_norm_lt_iff hne two_ne_zero, tb_val_two] at h
  omega

/-- `Statement:` for a unit `r`, `2 r - 1` is a unit with `‖(2 r - 1) - 1‖ < ‖2‖`. -/
theorem tbU_C {r : ℚ_[2]} (hr : TbIsUnit r) :
    ‖(2 * r - 1) - 1‖ < ‖(2 : ℚ_[2])‖ ∧ TbIsUnit (2 * r - 1) := by
  have hres := tb_res (tbIsUnit_norm hr)
  refine ⟨?_, ?_⟩
  · rw [show 2 * r - 1 - 1 = 2 * (r - 1) by ring, norm_mul]
    exact mul_lt_of_lt_one_right tb_norm_two_pos hres
  · apply tbIsUnit_of_norm
    have : ‖2 * r - 1‖ = ‖(-1 : ℚ_[2])‖ := tb_norm_eq_of_near (by
      rw [show 2 * r - 1 - -1 = 2 * r by ring, norm_mul, tbIsUnit_norm hr, mul_one, norm_neg,
        norm_one]
      exact tb_norm_two_lt_one)
    rw [this, norm_neg, norm_one]

/-- `Statement:` for `v(t) = 1`, `t + 1` is a unit with `¬ ‖(t + 1) - 1‖ < ‖2‖`. -/
theorem tbU_D {t : ℚ_[2]} (ht : t ≠ 0) (hv : t.valuation = 1) :
    TbIsUnit (t + 1) ∧ ¬ ‖(t + 1) - 1‖ < ‖(2 : ℚ_[2])‖ := by
  have hn : ‖t‖ = ‖(2 : ℚ_[2])‖ := by rw [tb_norm ht, tb_norm two_ne_zero, hv, tb_val_two]
  refine ⟨tbIsUnit_of_norm ?_, by rw [add_sub_cancel_right, hn]; exact lt_irrefl _⟩
  have : ‖t + 1‖ = ‖(1 : ℚ_[2])‖ := tb_norm_eq_of_near (by
    rw [add_sub_cancel_right, hn, norm_one]; exact tb_norm_two_lt_one)
  rw [this, norm_one]

/-- `Statement:` `psiK k`, from the units to the shells `0 … k`. -/
noncomputable def psiK : ℕ → ℚ_[2] → ℚ_[2]
  | 0, w => w
  | k + 1, w => if ‖w - 1‖ < ‖(2 : ℚ_[2])‖ then psiK k ((w + 1) / 2) else 2 ^ k * (w - 1)

/-- `Statement:` `rhoK k`, from the shells `0 … k` to the units. -/
noncomputable def rhoK : ℕ → ℚ_[2] → ℚ_[2]
  | 0, t => t
  | k + 1, t => if t.valuation ≤ k then 2 * rhoK k t - 1 else t / 2 ^ k + 1

/-- `Statement:` `psiK k` sends units into the shells `0 … k`. -/
theorem psiK_mem : ∀ (k : ℕ) {w : ℚ_[2]}, TbIsUnit w → TbInShells k (psiK k w)
  | 0, w, hw => show TbInShells 0 w from ⟨hw.1, by simp [hw.2], by simp [hw.2]⟩
  | k + 1, w, hw => by
    rw [psiK]
    split_ifs with h
    · obtain ⟨a, b, c⟩ := psiK_mem k (tbU_A hw h)
      exact ⟨a, b, by push_cast; omega⟩
    · obtain ⟨hne, hv⟩ := tbU_B hw h
      have h2k : (2 : ℚ_[2]) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
      have hval : ((2 : ℚ_[2]) ^ k * (w - 1)).valuation = k + 1 := by
        rw [Padic.valuation_mul h2k hne, tb_val_two_pow, hv]
      refine ⟨mul_ne_zero h2k hne, ?_, ?_⟩ <;> rw [hval] <;> push_cast <;> omega

/-- `Statement:` `rhoK k` sends the shells `0 … k` into the units. -/
theorem rhoK_mem : ∀ (k : ℕ) {t : ℚ_[2]}, TbInShells k t → TbIsUnit (rhoK k t)
  | 0, t, ht => ⟨ht.1, by
      have h1 := ht.2.1; have h2 := ht.2.2; push_cast at h2; exact le_antisymm h2 h1⟩
  | k + 1, t, ht => by
    rw [rhoK]
    split_ifs with h
    · exact (tbU_C (rhoK_mem k ⟨ht.1, ht.2.1, h⟩)).2
    · have hv : t.valuation = k + 1 := by have := ht.2.2; push_cast at this; omega
      have h2k : (2 : ℚ_[2]) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
      have hs : t / 2 ^ k ≠ 0 := div_ne_zero ht.1 h2k
      have hsv : (t / 2 ^ k).valuation = 1 := by
        rw [tb_val_div ht.1 h2k, hv, tb_val_two_pow]; ring
      exact (tbU_D hs hsv).1

/-- `Statement:` `rhoK k (psiK k w) = w` on the units. -/
theorem rho_psi : ∀ (k : ℕ) {w : ℚ_[2]}, TbIsUnit w → rhoK k (psiK k w) = w
  | 0, w, _ => rfl
  | k + 1, w, hw => by
    rw [psiK]
    split_ifs with h
    · have hu := tbU_A hw h
      have hm := psiK_mem k hu
      rw [rhoK, ite_eq_left hm.2.2, rho_psi k hu]
      ring
    · obtain ⟨hne, hv⟩ := tbU_B hw h
      have h2k : (2 : ℚ_[2]) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
      have hval : ¬ ((2 : ℚ_[2]) ^ k * (w - 1)).valuation ≤ k := by
        rw [Padic.valuation_mul h2k hne, tb_val_two_pow, hv]; omega
      rw [rhoK, ite_eq_right hval, mul_div_cancel_left₀ _ h2k]
      ring

/-- `Statement:` `psiK k (rhoK k t) = t` on the shells `0 … k`. -/
theorem psi_rho : ∀ (k : ℕ) {t : ℚ_[2]}, TbInShells k t → psiK k (rhoK k t) = t
  | 0, t, _ => rfl
  | k + 1, t, ht => by
    rw [rhoK]
    split_ifs with h
    · have hS : TbInShells k t := ⟨ht.1, ht.2.1, h⟩
      obtain ⟨hlt, -⟩ := tbU_C (rhoK_mem k hS)
      rw [psiK, ite_eq_left hlt, show (2 * rhoK k t - 1 + 1) / 2 = rhoK k t by ring, psi_rho k hS]
    · have hv : t.valuation = k + 1 := by have := ht.2.2; push_cast at this; omega
      have h2k : (2 : ℚ_[2]) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
      have hs : t / 2 ^ k ≠ 0 := div_ne_zero ht.1 h2k
      have hsv : (t / 2 ^ k).valuation = 1 := by
        rw [tb_val_div ht.1 h2k, hv, tb_val_two_pow]; ring
      rw [psiK, ite_eq_right (tbU_D hs hsv).2, add_sub_cancel_right, mul_div_cancel₀ _ h2k]

/-- `Statement:` `psiK k` is continuous. -/
theorem psiK_continuous : ∀ k : ℕ, Continuous (psiK k)
  | 0 => continuous_id
  | k + 1 => by
    have ih := psiK_continuous k
    rw [continuous_iff_continuousAt]
    intro w0
    by_cases h : ‖w0 - 1‖ < ‖(2 : ℚ_[2])‖
    · have hopen : IsOpen {w : ℚ_[2] | ‖w - 1‖ < ‖(2 : ℚ_[2])‖} :=
        isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
      have hev : (psiK k ∘ fun w => (w + 1) / 2) =ᶠ[𝓝 w0] psiK (k + 1) := by
        filter_upwards [hopen.mem_nhds h] with w hw
        rw [psiK, ite_eq_left hw]; rfl
      exact ((ih.comp ((continuous_id.add continuous_const).div_const 2)).continuousAt).congr hev
    · have hpos : 0 < ‖w0 - 1‖ := lt_of_lt_of_le tb_norm_two_pos (not_lt.1 h)
      have hev : (fun w => (2 : ℚ_[2]) ^ k * (w - 1)) =ᶠ[𝓝 w0] psiK (k + 1) := by
        filter_upwards [Metric.ball_mem_nhds w0 hpos] with w hw
        rw [Metric.mem_ball, dist_eq_norm] at hw
        have hn : ‖w - 1‖ = ‖w0 - 1‖ :=
          tb_norm_eq_of_near (by rw [show w - 1 - (w0 - 1) = w - w0 by ring]; exact hw)
        rw [psiK, ite_eq_right (by rw [hn]; exact h)]
      exact ((continuous_const.mul (continuous_id.sub continuous_const)).continuousAt).congr hev

/-- `Statement:` `rhoK k` is continuous at every nonzero point. -/
theorem rhoK_contAt : ∀ (k : ℕ) {t0 : ℚ_[2]}, t0 ≠ 0 → ContinuousAt (rhoK k) t0
  | 0, _, _ => continuous_id.continuousAt
  | k + 1, t0, h0 => by
    by_cases h : t0.valuation ≤ k
    · have hev : (fun t => 2 * rhoK k t - 1) =ᶠ[𝓝 t0] rhoK (k + 1) := by
        filter_upwards [tb_val_eventually_eq h0] with t ht
        rw [rhoK, ite_eq_left (by rw [ht]; exact h)]
      exact ((continuousAt_const.mul (rhoK_contAt k h0)).sub continuousAt_const).congr hev
    · have hev : (fun t => t / (2 : ℚ_[2]) ^ k + 1) =ᶠ[𝓝 t0] rhoK (k + 1) := by
        filter_upwards [tb_val_eventually_eq h0] with t ht
        rw [rhoK, ite_eq_right (by rw [ht]; exact h)]
      exact (((continuous_id.div_const _).add continuous_const).continuousAt).congr hev

section StepMap

variable {c : ℚ_[2]} {k : ℕ}

open Classical in
/-- `Statement:` the step map `2 ^ n * w ↦ c ^ n * psiK k w` (`w` a unit), `0 ↦ 0`. -/
noncomputable def stepMap (c : ℚ_[2]) (k : ℕ) (z : ℚ_[2]) : ℚ_[2] :=
  if z = 0 then 0 else c ^ z.valuation * psiK k (z / 2 ^ z.valuation)

open Classical in
/-- `Statement:` the inverse step map `c ^ n * t ↦ 2 ^ n * rhoK k t`, `0 ↦ 0`. -/
noncomputable def stepInv (c : ℚ_[2]) (k : ℕ) (y : ℚ_[2]) : ℚ_[2] :=
  if y = 0 then 0 else
    2 ^ (y.valuation / ((k : ℤ) + 1)) * rhoK k (y / c ^ (y.valuation / ((k : ℤ) + 1)))

/-- `Statement:` `v(c) = k + 1` gives `v(c ^ n) = n (k + 1)`. -/
theorem tb_val_c_zpow (hcv : c.valuation = k + 1) (n : ℤ) :
    (c ^ n).valuation = n * (k + 1) := by
  rw [Padic.valuation_zpow, hcv]

/-- `Statement:` `stepMap c k (2 ^ n * w) = c ^ n * psiK k w` for a unit `w`. -/
theorem stepMap_eq (c : ℚ_[2]) (k : ℕ) (n : ℤ) {w : ℚ_[2]} (hw : TbIsUnit w) :
    stepMap c k (2 ^ n * w) = c ^ n * psiK k w := by
  have h2n : (2 : ℚ_[2]) ^ n ≠ 0 := zpow_ne_zero _ two_ne_zero
  have hz : (2 : ℚ_[2]) ^ n * w ≠ 0 := mul_ne_zero h2n hw.1
  have hv : ((2 : ℚ_[2]) ^ n * w).valuation = n := by
    rw [Padic.valuation_mul h2n hw.1, tb_val_two_zpow, hw.2, add_zero]
  rw [stepMap, ite_eq_right hz, hv, mul_div_cancel_left₀ _ h2n]

/-- `Statement:` `stepInv c k (c ^ n * t) = 2 ^ n * rhoK k t` for `t` in the shells `0 … k`. -/
theorem stepInv_eq (hc : c ≠ 0) (hcv : c.valuation = k + 1) (n : ℤ) {t : ℚ_[2]}
    (ht : TbInShells k t) : stepInv c k (c ^ n * t) = 2 ^ n * rhoK k t := by
  have hcn : c ^ n ≠ 0 := zpow_ne_zero _ hc
  have hy : c ^ n * t ≠ 0 := mul_ne_zero hcn ht.1
  have hk : ((k : ℤ) + 1) ≠ 0 := by omega
  have hq : (c ^ n * t).valuation / ((k : ℤ) + 1) = n := by
    rw [Padic.valuation_mul hcn ht.1, tb_val_c_zpow hcv, add_comm,
      Int.add_mul_ediv_right _ _ hk, Int.ediv_eq_zero_of_lt ht.2.1 (by have := ht.2.2; omega),
      zero_add]
  rw [stepInv, ite_eq_right hy, hq, mul_div_cancel_left₀ _ hcn]

/-- `Statement:` every `z ≠ 0` is `2 ^ n * w` with `w` a unit. -/
theorem tb_decompZ {z : ℚ_[2]} (hz : z ≠ 0) :
    ∃ (n : ℤ) (w : ℚ_[2]), TbIsUnit w ∧ z = 2 ^ n * w := by
  have h2n : (2 : ℚ_[2]) ^ z.valuation ≠ 0 := zpow_ne_zero _ two_ne_zero
  refine ⟨z.valuation, z / 2 ^ z.valuation, ⟨div_ne_zero hz h2n, ?_⟩, ?_⟩
  · rw [tb_val_div hz h2n, tb_val_two_zpow, sub_self]
  · rw [mul_div_cancel₀ _ h2n]

/-- `Statement:` for `v(c) = k + 1`, every `y ≠ 0` is `c ^ n * t` with `t` in the shells `0 … k`. -/
theorem tb_decompY (hc : c ≠ 0) (hcv : c.valuation = k + 1) {y : ℚ_[2]} (hy : y ≠ 0) :
    ∃ (n : ℤ) (t : ℚ_[2]), TbInShells k t ∧ y = c ^ n * t := by
  have hpos : (0 : ℤ) < (k : ℤ) + 1 := by omega
  have e := Int.emod_def y.valuation ((k : ℤ) + 1)
  have r0 := Int.emod_nonneg y.valuation hpos.ne'
  have r1 := Int.emod_lt_of_pos y.valuation hpos
  generalize y.valuation / ((k : ℤ) + 1) = q at e
  generalize y.valuation % ((k : ℤ) + 1) = r at e r0 r1
  have hcq : c ^ q ≠ 0 := zpow_ne_zero _ hc
  have hvt : (y / c ^ q).valuation = r := by
    rw [tb_val_div hy hcq, tb_val_c_zpow hcv]
    linear_combination -e
  refine ⟨q, y / c ^ q, ⟨div_ne_zero hy hcq, by rw [hvt]; exact r0, by rw [hvt]; omega⟩, ?_⟩
  rw [mul_div_cancel₀ _ hcq]

/-- `Statement:` `stepMap c k 0 = 0`. -/
theorem stepMap_zero : stepMap c k 0 = 0 := by simp [stepMap]

/-- `Statement:` `stepInv c k 0 = 0`. -/
theorem stepInv_zero : stepInv c k 0 = 0 := by simp [stepInv]

/-- `Statement:` for `v(c) = k + 1`, `stepInv` undoes `stepMap`. -/
theorem stepInv_stepMap (hc : c ≠ 0) (hcv : c.valuation = k + 1) (z : ℚ_[2]) :
    stepInv c k (stepMap c k z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [stepMap_zero, stepInv_zero]
  · obtain ⟨n, w, hw, rfl⟩ := tb_decompZ hz
    rw [stepMap_eq c k n hw, stepInv_eq hc hcv n (psiK_mem k hw), rho_psi k hw]

/-- `Statement:` for `v(c) = k + 1`, `stepMap` undoes `stepInv`. -/
theorem stepMap_stepInv (hc : c ≠ 0) (hcv : c.valuation = k + 1) (y : ℚ_[2]) :
    stepMap c k (stepInv c k y) = y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [stepInv_zero, stepMap_zero]
  · obtain ⟨n, t, ht, rfl⟩ := tb_decompY hc hcv hy
    rw [stepInv_eq hc hcv n ht, stepMap_eq c k n (rhoK_mem k ht), psi_rho k ht]

/-- `Statement:` `stepMap c k (2 z) = c * stepMap c k z`. -/
theorem stepMap_conj (hc : c ≠ 0) (z : ℚ_[2]) : stepMap c k (2 * z) = c * stepMap c k z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [mul_zero, stepMap_zero, mul_zero]
  · obtain ⟨n, w, hw, rfl⟩ := tb_decompZ hz
    rw [show 2 * (2 ^ n * w) = (2 : ℚ_[2]) ^ (n + 1) * w by
          rw [zpow_add_one₀ two_ne_zero]; ring,
      stepMap_eq c k _ hw, stepMap_eq c k _ hw, zpow_add_one₀ hc]
    ring

/-- `Statement:` for `v(c) = k + 1`, `‖stepMap c k y‖ ≤ ‖y‖ ^ (k + 1)`. -/
theorem stepMap_norm_le (hc : c ≠ 0) (hcv : c.valuation = k + 1) (y : ℚ_[2]) :
    ‖stepMap c k y‖ ≤ ‖y‖ ^ (k + 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [stepMap_zero]
  · obtain ⟨n, w, hw, rfl⟩ := tb_decompZ hy
    have hm := psiK_mem k hw
    have hcn : c ^ n ≠ 0 := zpow_ne_zero _ hc
    have h2n : (2 : ℚ_[2]) ^ n ≠ 0 := zpow_ne_zero _ two_ne_zero
    have hv1 : (c ^ n * psiK k w).valuation = n * (k + 1) + (psiK k w).valuation := by
      rw [Padic.valuation_mul hcn hm.1, tb_val_c_zpow hcv]
    have hv2 : ((2 : ℚ_[2]) ^ n * w).valuation = n := by
      rw [Padic.valuation_mul h2n hw.1, tb_val_two_zpow, hw.2, add_zero]
    rw [stepMap_eq c k n hw, tb_norm (mul_ne_zero hcn hm.1), tb_norm (mul_ne_zero h2n hw.1),
      ← zpow_natCast, ← zpow_mul, hv1, hv2]
    apply zpow_le_zpow_right₀ (by norm_num)
    have := hm.2.1
    push_cast
    linarith

/-- `Statement:` for `v(c) = k + 1`, `‖stepInv c k y‖ ^ (k + 1) ≤ 2 ^ k * ‖y‖`. -/
theorem stepInv_norm_le (hc : c ≠ 0) (hcv : c.valuation = k + 1) (y : ℚ_[2]) :
    ‖stepInv c k y‖ ^ (k + 1) ≤ (2 : ℝ) ^ k * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [stepInv_zero]
  · obtain ⟨n, t, ht, rfl⟩ := tb_decompY hc hcv hy
    have hr := rhoK_mem k ht
    have hcn : c ^ n ≠ 0 := zpow_ne_zero _ hc
    have h2n : (2 : ℚ_[2]) ^ n ≠ 0 := zpow_ne_zero _ two_ne_zero
    have hv1 : ((2 : ℚ_[2]) ^ n * rhoK k t).valuation = n := by
      rw [Padic.valuation_mul h2n hr.1, tb_val_two_zpow, hr.2, add_zero]
    have hv2 : (c ^ n * t).valuation = n * (k + 1) + t.valuation := by
      rw [Padic.valuation_mul hcn ht.1, tb_val_c_zpow hcv]
    rw [stepInv_eq hc hcv n ht, tb_norm (mul_ne_zero h2n hr.1), tb_norm (mul_ne_zero hcn ht.1),
      hv1, hv2, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_add₀ (by norm_num)]
    apply zpow_le_zpow_right₀ (by norm_num)
    have := ht.2.2
    push_cast
    linarith

/-- `Statement:` for `v(c) = k + 1`, `stepMap c k` is continuous. -/
theorem stepMap_continuous (hc : c ≠ 0) (hcv : c.valuation = k + 1) :
    Continuous (stepMap c k) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · show Tendsto (stepMap c k) (𝓝 0) (𝓝 (stepMap c k 0))
    rw [stepMap_zero]
    apply squeeze_zero_norm (stepMap_norm_le hc hcv)
    simpa using (tendsto_norm_zero (E := ℚ_[2])).pow (k + 1)
  · have hev : (fun y => c ^ z.valuation * psiK k (y / 2 ^ z.valuation)) =ᶠ[𝓝 z]
        stepMap c k := by
      filter_upwards [tb_val_eventually_eq hz, eventually_ne_nhds hz] with y hy hy0
      rw [stepMap, ite_eq_right hy0, hy]
    exact ((continuous_const.mul
      ((psiK_continuous k).comp (continuous_id.div_const _))).continuousAt).congr hev

/-- `Statement:` for `v(c) = k + 1`, `stepInv c k` is continuous. -/
theorem stepInv_continuous (hc : c ≠ 0) (hcv : c.valuation = k + 1) :
    Continuous (stepInv c k) := by
  rw [continuous_iff_continuousAt]
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · show Tendsto (stepInv c k) (𝓝 0) (𝓝 (stepInv c k 0))
    rw [stepInv_zero]
    set e : ℝ := ((k + 1 : ℕ) : ℝ)⁻¹ with he
    have hb : ∀ y, ‖stepInv c k y‖ ≤ ((2 : ℝ) ^ k * ‖y‖) ^ e := fun y => by
      calc ‖stepInv c k y‖ = (‖stepInv c k y‖ ^ (k + 1)) ^ e :=
            (Real.pow_rpow_inv_natCast (norm_nonneg _) (Nat.succ_ne_zero k)).symm
        _ ≤ ((2 : ℝ) ^ k * ‖y‖) ^ e :=
            Real.rpow_le_rpow (by positivity) (stepInv_norm_le hc hcv y) (by positivity)
    apply squeeze_zero_norm hb
    have h0 : Tendsto (fun y : ℚ_[2] => (2 : ℝ) ^ k * ‖y‖) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_norm_zero (E := ℚ_[2])).const_mul ((2 : ℝ) ^ k)
    exact h0.rpow_const_nhds_zero (by positivity)
  · set q := y.valuation / ((k : ℤ) + 1)
    have hcq : c ^ q ≠ 0 := zpow_ne_zero _ hc
    have hev : (fun y' => (2 : ℚ_[2]) ^ q * rhoK k (y' / c ^ q)) =ᶠ[𝓝 y] stepInv c k := by
      filter_upwards [tb_val_eventually_eq hy, eventually_ne_nhds hy] with y' hy' hy0
      rw [stepInv, ite_eq_right hy0, hy']
    have hr : ContinuousAt (fun y' => rhoK k (y' / c ^ q)) y :=
      ContinuousAt.comp (g := rhoK k) (f := fun y' : ℚ_[2] => y' / c ^ q)
        (rhoK_contAt k (div_ne_zero hy hcq)) ((continuous_id.div_const _).continuousAt)
    exact (continuousAt_const.mul hr).congr hev

/-- `Statement:` for `v(c) = k + 1`, the step map as a homeomorphism of `ℚ_[2]`. -/
noncomputable def stepHomeo (c : ℚ_[2]) (k : ℕ) (hc : c ≠ 0) (hcv : c.valuation = k + 1) :
    ℚ_[2] ≃ₜ ℚ_[2] where
  toFun := stepMap c k
  invFun := stepInv c k
  left_inv := stepInv_stepMap hc hcv
  right_inv := stepMap_stepInv hc hcv
  continuous_toFun := stepMap_continuous hc hcv
  continuous_invFun := stepInv_continuous hc hcv

end StepMap

/-- `Statement:` for `v(c) = k + 1`, `×2` and `×c` satisfy `ScaleConj` on `OnePoint ℚ_[2]`. -/
theorem scaleConj_two_val (c : ℚ_[2]) (hc : c ≠ 0) (k : ℕ) (hcv : c.valuation = k + 1) :
    ScaleConj (2 : ℚ_[2]) c two_ne_zero hc :=
  scaleConj_of_homeo two_ne_zero hc (stepHomeo c k hc hcv)
    (fun z => stepMap_conj (k := k) hc z)

/-- `Statement:` `×2` and `×4` satisfy `ScaleConj` on `OnePoint ℚ_[2]`. -/
theorem scaleConj_two_four : ScaleConj (2 : ℚ_[2]) 4 two_ne_zero (by norm_num) :=
  scaleConj_two_val 4 _ 1 (by rw [tb_val_four]; norm_num)

/-- `Statement:` every contracting multiplier (`‖c‖ < 1`) satisfies `ScaleConj 2 c`. -/
theorem scaleConj_two_of_norm_lt_one {c : ℚ_[2]} (hc : c ≠ 0) (h : ‖c‖ < 1) :
    ScaleConj (2 : ℚ_[2]) c two_ne_zero hc := by
  have hv : 0 < c.valuation := by
    have := (tb_norm_lt_iff hc one_ne_zero).1 (by rwa [norm_one])
    rwa [Padic.valuation_one] at this
  exact scaleConj_two_val c hc (c.valuation - 1).toNat (by omega)

/-- `Statement:` every multiplier with `‖c‖ ≠ 1` satisfies `ScaleConj 2 c`; an expanding `c` goes
    through `scaleConj_inv`. -/
theorem scaleConj_two_of_norm_ne_one {c : ℚ_[2]} (hc : c ≠ 0) (h : ‖c‖ ≠ 1) :
    ScaleConj (2 : ℚ_[2]) c two_ne_zero hc := by
  rcases h.lt_or_gt with h1 | h1
  · exact scaleConj_two_of_norm_lt_one hc h1
  · have hci : ‖c⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h1
    exact scaleConj_trans (scaleConj_two_of_norm_lt_one (inv_ne_zero hc) hci)
      (scaleConj_congr rfl (inv_inv c) (scaleConj_inv c⁻¹ (inv_ne_zero hc)))

/-- `Statement:` any two multipliers with `‖c‖ ≠ 1`, `‖d‖ ≠ 1` satisfy `ScaleConj c d` on
    `OnePoint ℚ_[2]`. -/
theorem scaleConj_of_norm_ne_one {c d : ℚ_[2]} (hc : c ≠ 0) (hd : d ≠ 0) (hc1 : ‖c‖ ≠ 1)
    (hd1 : ‖d‖ ≠ 1) : ScaleConj c d hc hd :=
  scaleConj_trans (scaleConj_symm (scaleConj_two_of_norm_ne_one hc hc1))
    (scaleConj_two_of_norm_ne_one hd hd1)

/-- `Statement:` for `‖c‖ ≠ 1`, `‖d‖ ≠ 1`, the limit motions of `lmScale c` and `lmScale d` on
    `OnePoint ℚ_[2]` are related by a `Motion.HomeoIso`. -/
theorem homeoIso_of_norm_ne_one {c d : ℚ_[2]} (hc : c ≠ 0) (hd : d ≠ 0) (hc1 : ‖c‖ ≠ 1)
    (hd1 : ‖d‖ ≠ 1) :
    Nonempty (Motion.HomeoIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale d hd) (lmScale d hd).continuous)) :=
  scaleConj_homeoIso (scaleConj_of_norm_ne_one hc hd hc1 hd1)

/-- `Statement:` the `n`-th iterate of `lmScale d` sends `w` to `d ^ n * w`. -/
theorem tb_iter_scale (d : ℚ_[2]) (hd : d ≠ 0) (w : ℚ_[2]) (n : ℕ) :
    (⇑(lmScale d hd))^[n] (OnePoint.some w) = OnePoint.some (d ^ n * w) :=
  lm_scale_iterate_some d hd w n

/-- `Statement:` CONTROL: a multiplier with `‖d‖ = 1` does not satisfy `ScaleConj 2 d`. -/
theorem scaleConj_two_not_norm_one {d : ℚ_[2]} (hd : d ≠ 0) (hd1 : ‖d‖ = 1) :
    ¬ ScaleConj (2 : ℚ_[2]) d two_ne_zero hd := by
  rintro ⟨e, he⟩
  have hsc : Function.Semiconj e (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale d hd) := he
  have horb : Tendsto (fun n : ℕ => (⇑(lmScale d hd))^[n] (e (OnePoint.some 1))) atTop
      (𝓝 (e (OnePoint.some 0))) := by
    have h1 : Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one tb_norm_two_lt_one
    have h2 := (e.continuous.tendsto _).comp ((OnePoint.continuous_coe.tendsto 0).comp h1)
    refine h2.congr (fun n => ?_)
    simp only [Function.comp]
    rw [← hsc.iterate_right n (OnePoint.some 1), tb_iter_scale, mul_one]
  have hp : lmScale d hd (e (OnePoint.some 0)) = e (OnePoint.some 0) := by
    rw [← he, lm_scale_some, mul_zero]
  have hqp : e (OnePoint.some 1) ≠ e (OnePoint.some 0) := fun h =>
    one_ne_zero (OnePoint.coe_injective (e.injective h))
  generalize e (OnePoint.some 1) = q at horb hqp
  generalize e (OnePoint.some 0) = p at horb hp hqp
  induction q using OnePoint.rec with
  | infty =>
    have hc : ∀ n : ℕ, (⇑(lmScale d hd))^[n] OnePoint.infty = OnePoint.infty :=
      fun n => Function.iterate_fixed (lm_scale_infty d hd) n
    simp only [hc] at horb
    exact hqp (tendsto_nhds_unique tendsto_const_nhds horb)
  | coe w =>
    simp only [tb_iter_scale] at horb
    induction p using OnePoint.rec with
    | infty =>
      have hK : IsCompact ((OnePoint.some : ℚ_[2] → OnePoint ℚ_[2]) '' Metric.closedBall 0 ‖w‖) :=
        (isCompact_closedBall 0 ‖w‖).image OnePoint.continuous_coe
      have hmem : ((OnePoint.some : ℚ_[2] → OnePoint ℚ_[2]) '' Metric.closedBall 0 ‖w‖)ᶜ ∈
          𝓝 (OnePoint.infty : OnePoint ℚ_[2]) :=
        hK.isClosed.compl_mem_nhds (by rintro ⟨x, -, hx⟩; exact OnePoint.coe_ne_infty x hx)
      obtain ⟨n, hn⟩ := (horb.eventually hmem).exists
      exact hn ⟨d ^ n * w, by simp [Metric.mem_closedBall, norm_mul, norm_pow, hd1], rfl⟩
    | coe a =>
      have h' : Tendsto (fun n : ℕ => d ^ n * w) atTop (𝓝 a) :=
        (OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff).2 horb
      have ha : d * a = a := OnePoint.coe_injective (by rw [← lm_scale_some d hd]; exact hp)
      have hn : ‖a‖ = ‖w‖ := by
        have := h'.norm
        simp only [norm_mul, norm_pow, hd1, one_pow, one_mul] at this
        exact (tendsto_nhds_unique tendsto_const_nhds this).symm
      rcases eq_or_ne a 0 with rfl | ha0
      · rw [norm_zero, eq_comm, norm_eq_zero] at hn
        subst hn; exact hqp rfl
      · have hd1' : d = 1 := mul_right_cancel₀ ha0 (by rw [ha, one_mul])
        subst hd1'
        simp only [one_pow, one_mul] at h'
        exact hqp (by rw [tendsto_nhds_unique tendsto_const_nhds h'])

end Step

/-! ## § V. Four flips on `ℚ_[2]ˣ` and on `OnePoint ℚ_[2]` -/

section Flips

/-- `Statement:` the unit-inverse flip `z ↦ 4 ^ v(z) * z⁻¹` (`2 ^ v * w ↦ 2 ^ v * w⁻¹`), `0 ↦ 0`. -/
noncomputable def uFlip (z : ℚ_[2]) : ℚ_[2] := 4 ^ z.valuation * z⁻¹

/-- `Statement:` `uFlip 0 = 0`. -/
theorem uFlip_zero : uFlip 0 = 0 := by simp [uFlip]

/-- `Statement:` `uFlip z ≠ 0` for `z ≠ 0`. -/
theorem uFlip_ne_zero {z : ℚ_[2]} (hz : z ≠ 0) : uFlip z ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (by norm_num)) (inv_ne_zero hz)

/-- `Statement:` `uFlip` preserves the valuation. -/
theorem uFlip_valuation (z : ℚ_[2]) : (uFlip z).valuation = z.valuation := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [uFlip_zero]
  · rw [uFlip, Padic.valuation_mul (zpow_ne_zero _ (by norm_num)) (inv_ne_zero hz),
      Padic.valuation_zpow, tb_val_four, Padic.valuation_inv]
    omega

/-- `Statement:` `uFlip` preserves the norm. -/
theorem uFlip_norm (z : ℚ_[2]) : ‖uFlip z‖ = ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [uFlip_zero]
  · rw [Padic.norm_eq_zpow_neg_valuation (uFlip_ne_zero hz),
      Padic.norm_eq_zpow_neg_valuation hz, uFlip_valuation]

/-- `Statement:` `uFlip` is an involution. -/
theorem uFlip_uFlip (z : ℚ_[2]) : uFlip (uFlip z) = z := by
  show 4 ^ (uFlip z).valuation * (uFlip z)⁻¹ = z
  rw [uFlip_valuation]
  unfold uFlip
  rw [mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by norm_num)), one_mul]

/-- `Statement:` `uFlip` is multiplicative. -/
theorem uFlip_mul (z y : ℚ_[2]) : uFlip (z * y) = uFlip z * uFlip y := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [uFlip]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [uFlip]
  unfold uFlip
  rw [Padic.valuation_mul hz hy, zpow_add₀ (by norm_num), mul_inv]; ring

/-- `Statement:` `uFlip z⁻¹ = (uFlip z)⁻¹`. -/
theorem uFlip_inv (z : ℚ_[2]) : uFlip z⁻¹ = (uFlip z)⁻¹ := by
  unfold uFlip
  rw [Padic.valuation_inv, zpow_neg, mul_inv, inv_inv]

/-- `Statement:` `uFlip` is continuous on `ℚ_[2]`, `0` included. -/
theorem uFlip_continuous : Continuous uFlip := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · show Tendsto uFlip (𝓝 0) (𝓝 (uFlip 0))
    rw [uFlip_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp only [uFlip_norm]
    exact tendsto_norm_zero
  · have hev : (fun y => (4 : ℚ_[2]) ^ z.valuation * y⁻¹) =ᶠ[𝓝 z] uFlip := by
      filter_upwards [tb_val_eventually_eq hz] with y hy
      simp [uFlip, hy]
    exact (continuousAt_const.mul (continuousAt_inv₀ hz)).congr hev

/-- `Statement:` `uFlip` as a homeomorphism of `ℚ_[2]`. -/
noncomputable def uFlipHomeo : ℚ_[2] ≃ₜ ℚ_[2] where
  toFun := uFlip
  invFun := uFlip
  left_inv := uFlip_uFlip
  right_inv := uFlip_uFlip
  continuous_toFun := uFlip_continuous
  continuous_invFun := uFlip_continuous

/-- `Statement:` `uFlip` as a multiplicative automorphism of `ℚ_[2]`. -/
noncomputable def uFlipMulEquiv : ℚ_[2] ≃* ℚ_[2] where
  toFun := uFlip
  invFun := uFlip
  left_inv := uFlip_uFlip
  right_inv := uFlip_uFlip
  map_mul' := uFlip_mul

/-- `Statement:` the unit-inverse flip as an automorphism of the group `ℚ_[2]ˣ`. -/
noncomputable def flipU : ℚ_[2]ˣ ≃* ℚ_[2]ˣ := Units.mapEquiv uFlipMulEquiv

/-- `Statement:` inversion as an automorphism of the group `ℚ_[2]ˣ`. -/
noncomputable def flipI : ℚ_[2]ˣ ≃* ℚ_[2]ˣ := MulEquiv.inv ℚ_[2]ˣ

/-- `Statement:` `flipU z` has value `uFlip z`, by `rfl`. -/
theorem flipU_val (z : ℚ_[2]ˣ) : ((flipU z : ℚ_[2]ˣ) : ℚ_[2]) = uFlip z := rfl

/-- `Statement:` `flipU` is continuous on `ℚ_[2]ˣ`. -/
theorem flipU_continuous : Continuous (flipU : ℚ_[2]ˣ → ℚ_[2]ˣ) := by
  rw [Units.continuous_iff]
  constructor
  · exact uFlip_continuous.comp Units.continuous_val
  · have : (fun z : ℚ_[2]ˣ => ((flipU z)⁻¹ : ℚ_[2]ˣ).val) =
        fun z => uFlip ((z⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) := by
      funext z
      show (((flipU z)⁻¹ : ℚ_[2]ˣ) : ℚ_[2]) = _
      rw [Units.val_inv_eq_inv_val, flipU_val, Units.val_inv_eq_inv_val, uFlip_inv]
    rw [this]
    exact uFlip_continuous.comp Units.continuous_coe_inv

/-- `Statement:` `flipI` is continuous on `ℚ_[2]ˣ`. -/
theorem flipI_continuous : Continuous (flipI : ℚ_[2]ˣ → ℚ_[2]ˣ) := continuous_inv

/-- `Statement:` `(3 : ℚ_[2])⁻¹ ≠ 3`. -/
theorem tb_three_inv_ne : (3 : ℚ_[2])⁻¹ ≠ 3 := by
  intro h
  have h9 : (3 : ℚ_[2]) * 3 = 1 := by
    calc (3 : ℚ_[2]) * 3 = 3 * 3⁻¹ := by rw [h]
      _ = 1 := mul_inv_cancel₀ (by norm_num)
  norm_num at h9

/-- `Statement:` `uFlip 3 = 3⁻¹`. -/
theorem tb_uFlip_three : uFlip 3 = 3⁻¹ := by rw [uFlip, tb_val_three, zpow_zero, one_mul]

/-- `Statement:` `flipU` and `flipI` are commuting involutions of `ℚ_[2]ˣ`, and `1`, `flipU`,
    `flipI`, `flipU ∘ flipI` are pairwise distinct: a Klein four subgroup of its automorphisms. -/
theorem flip_klein_units :
    flipU.trans flipU = MulEquiv.refl _ ∧ flipI.trans flipI = MulEquiv.refl _ ∧
    flipU.trans flipI = flipI.trans flipU ∧
    flipU ≠ MulEquiv.refl _ ∧ flipI ≠ MulEquiv.refl _ ∧ flipU.trans flipI ≠ MulEquiv.refl _ ∧
    flipU ≠ flipI ∧ flipU ≠ flipU.trans flipI ∧ flipI ≠ flipU.trans flipI := by
  have h3 : (3 : ℚ_[2]) ≠ 0 := by norm_num
  have h3inv := tb_three_inv_ne
  have hu3 := tb_uFlip_three
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hu2 : uFlip 2 = 2 := by
    simp only [uFlip, tb_val_two, zpow_one]; norm_num
  set t : ℚ_[2]ˣ := Units.mk0 3 h3
  set s : ℚ_[2]ˣ := Units.mk0 2 h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext z; simp [flipU, uFlipMulEquiv, uFlip_uFlip]
  · ext z; simp [flipI]
  · ext z; simp [flipU, flipI, uFlipMulEquiv]
  · intro h; have := congrArg (fun f : ℚ_[2]ˣ ≃* ℚ_[2]ˣ => ((f t : ℚ_[2]ˣ) : ℚ_[2])) h
    exact h3inv (by simpa [flipU, uFlipMulEquiv, t, hu3] using this)
  · intro h; have := congrArg (fun f : ℚ_[2]ˣ ≃* ℚ_[2]ˣ => ((f s : ℚ_[2]ˣ) : ℚ_[2])) h
    simp [flipI, s] at this; norm_num at this
  · intro h; have := congrArg (fun f : ℚ_[2]ˣ ≃* ℚ_[2]ˣ => ((f s : ℚ_[2]ˣ) : ℚ_[2])) h
    simp [flipU, flipI, uFlipMulEquiv, s, hu2] at this; norm_num at this
  · intro h; have := congrArg (fun f : ℚ_[2]ˣ ≃* ℚ_[2]ˣ => ((f s : ℚ_[2]ˣ) : ℚ_[2])) h
    simp [flipU, flipI, uFlipMulEquiv, s, hu2] at this; norm_num at this
  · intro h; have := congrArg (fun f : ℚ_[2]ˣ ≃* ℚ_[2]ˣ => ((f s : ℚ_[2]ˣ) : ℚ_[2])) h
    simp [flipU, flipI, uFlipMulEquiv, s, hu2] at this; norm_num at this
  · intro h; have := congrArg (fun f : ℚ_[2]ˣ ≃* ℚ_[2]ˣ => ((f t : ℚ_[2]ˣ) : ℚ_[2])) h
    exact h3inv (by simpa [flipU, flipI, uFlipMulEquiv, t, hu3] using this)

/-- `Statement:` the unit-inverse flip on `OnePoint ℚ_[2]`, fixing `∞`. -/
noncomputable def flipS : OnePoint ℚ_[2] ≃ₜ OnePoint ℚ_[2] :=
  Homeomorph.onePointCongr uFlipHomeo

/-- `Statement:` the amplitude flip `2 ^ v * w ↦ 2 ^ (-v) * w`: `onePointInv`, then `flipS`. -/
noncomputable def flipA : OnePoint ℚ_[2] ≃ₜ OnePoint ℚ_[2] := onePointInvHomeo.trans flipS

/-- `Statement:` `flipS z = uFlip z` on points of `ℚ_[2]`, by `rfl`. -/
theorem flipS_some (z : ℚ_[2]) : flipS (OnePoint.some z) = OnePoint.some (uFlip z) := rfl

/-- `Statement:` `flipS ∞ = ∞`, by `rfl`. -/
theorem flipS_infty : flipS OnePoint.infty = OnePoint.infty := rfl

/-- `Statement:` `flipA x = flipS (onePointInv x)`, by `rfl`. -/
theorem flipA_apply (x : OnePoint ℚ_[2]) : flipA x = flipS (onePointInv x) := rfl

/-- `Statement:` `flipS` is an involution. -/
theorem flipS_flipS (x : OnePoint ℚ_[2]) : flipS (flipS x) = x := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z => rw [flipS_some, flipS_some, uFlip_uFlip]

/-- `Statement:` `flipS` commutes with `onePointInv`. -/
theorem flipS_comm_inv (x : OnePoint ℚ_[2]) :
    flipS (onePointInv x) = onePointInv (flipS x) := by
  induction x using OnePoint.rec with
  | infty => rw [onePointInv_infty, flipS_some, uFlip_zero, flipS_infty, onePointInv_infty]
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · rw [onePointInv_zero, flipS_infty, flipS_some, uFlip_zero, onePointInv_zero]
    · rw [onePointInv_coe_ne hz, flipS_some, flipS_some, onePointInv_coe_ne (uFlip_ne_zero hz),
        uFlip_inv]

/-- `Statement:` on `OnePoint ℚ_[2]`, `flipS` and `onePointInv` are commuting involutions,
    `flipA` is an involution, and `id`, `flipS`, `onePointInv`, `flipA` are pairwise distinct. -/
theorem flip_klein_onePoint :
    (∀ x, flipS (flipS x) = x) ∧ (∀ x : OnePoint ℚ_[2], onePointInv (onePointInv x) = x) ∧
    (∀ x, flipS (onePointInv x) = onePointInv (flipS x)) ∧ (∀ x, flipA (flipA x) = x) ∧
    (⇑flipS ≠ id) ∧ (onePointInv ≠ (id : OnePoint ℚ_[2] → OnePoint ℚ_[2])) ∧ (⇑flipA ≠ id) ∧
    (⇑flipS ≠ onePointInv) ∧ (⇑flipS ≠ ⇑flipA) ∧ (onePointInv ≠ ⇑flipA) := by
  have h3 : (3 : ℚ_[2]) ≠ 0 := by norm_num
  have h3inv := tb_three_inv_ne
  have hu3 := tb_uFlip_three
  have hu3' : uFlip 3⁻¹ = 3 := by rw [uFlip_inv, hu3, inv_inv]
  have hinf : ∀ f : OnePoint ℚ_[2] → OnePoint ℚ_[2], f = id → f OnePoint.infty = OnePoint.infty :=
    fun f h => by rw [h]; rfl
  have hA_inf : flipA OnePoint.infty = OnePoint.some 0 := by
    rw [flipA_apply, onePointInv_infty, flipS_some, uFlip_zero]
  refine ⟨flipS_flipS, onePointInv_involutive, flipS_comm_inv, fun x => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [flipA_apply, flipA_apply, flipS_comm_inv, flipS_flipS, onePointInv_involutive]
  · intro h; have := congrFun h (OnePoint.some 3)
    rw [flipS_some, hu3] at this; exact h3inv (OnePoint.coe_injective this)
  · intro h; have := hinf _ h; rw [onePointInv_infty] at this; exact OnePoint.coe_ne_infty _ this
  · intro h; have := hinf _ h; rw [hA_inf] at this; exact OnePoint.coe_ne_infty _ this
  · intro h; have := congrFun h OnePoint.infty
    rw [flipS_infty, onePointInv_infty] at this; exact OnePoint.infty_ne_coe _ this
  · intro h; have := congrFun h OnePoint.infty
    rw [flipS_infty, hA_inf] at this; exact OnePoint.infty_ne_coe _ this
  · intro h; have := congrFun h (OnePoint.some 3)
    rw [flipA_apply, onePointInv_coe_ne h3, flipS_some, hu3'] at this
    exact h3inv (OnePoint.coe_injective this)

/-- `Statement:` `flipA` exchanges `0` of `ℚ_[2]` and `∞` of `OnePoint ℚ_[2]`, two distinct points;
    `flipS` fixes both. -/
theorem flip_poles :
    flipA (OnePoint.some 0) = OnePoint.infty ∧ flipA OnePoint.infty = OnePoint.some 0 ∧
    flipS (OnePoint.some 0) = OnePoint.some 0 ∧ flipS OnePoint.infty = OnePoint.infty := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · rw [flipA_apply, onePointInv_zero, flipS_infty]
  · rw [flipA_apply, onePointInv_infty, flipS_some, uFlip_zero]
  · rw [flipS_some, uFlip_zero]

/-- `Statement:` `flipA` fixes every point of the unit shell `‖z‖ = 1`. -/
theorem flipA_fixes_shell {z : ℚ_[2]} (hz : ‖z‖ = 1) :
    flipA (OnePoint.some z) = OnePoint.some z := by
  have hz0 := tb_ne_zero_of_norm_one hz
  rw [flipA_apply, onePointInv_coe_ne hz0, flipS_some, uFlip_inv]
  congr 1
  simp [uFlip, tb_val_eq_zero_of_norm_one hz]

/-- `Statement:` `rInv` maps the unit shell into itself, and fixes a shell point `z` iff
    `z = 1 ∨ z = -1`. -/
theorem rInv_shell {z : ℚ_[2]} (hz : ‖z‖ = 1) :
    (∃ w : ℚ_[2], rInv (OnePoint.some z) = OnePoint.some w ∧ ‖w‖ = 1) ∧
    (rInv (OnePoint.some z) = OnePoint.some z ↔ z = 1 ∨ z = -1) := by
  have hz0 := tb_ne_zero_of_norm_one hz
  rw [rInv_coe_ne hz0]
  refine ⟨⟨z⁻¹, rfl, tb_norm_inv_one hz⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h' : z⁻¹ = z := OnePoint.coe_injective h
    have : z * z = 1 := by
      calc z * z = z * z⁻¹ := by rw [h']
        _ = 1 := mul_inv_cancel₀ hz0
    exact mul_self_eq_one_iff.1 this
  · rcases h with rfl | rfl <;> simp

/-- `Statement:` CONTROL: `‖3‖ = 1`, `rInv` moves `3`, and `flipA` fixes it. -/
theorem rInv_moves_three :
    ‖(3 : ℚ_[2])‖ = 1 ∧ rInv (OnePoint.some 3) ≠ OnePoint.some 3 ∧
    flipA (OnePoint.some 3) = OnePoint.some 3 := by
  refine ⟨tb_norm_three, fun h => ?_, flipA_fixes_shell tb_norm_three⟩
  rcases (rInv_shell tb_norm_three).2.1 h with h1 | h1 <;> norm_num at h1

/-- `Statement:` for `c ≠ 0`, `×c` satisfies `ScaleConj` with `×(uFlip c)`, `×c⁻¹` and
    `×(uFlip c)⁻¹`. -/
theorem flip_conj_scales (c : ℚ_[2]) (hc : c ≠ 0) :
    ScaleConj c (uFlip c) hc (uFlip_ne_zero hc) ∧
    ScaleConj c c⁻¹ hc (inv_ne_zero hc) ∧
    ScaleConj c (uFlip c)⁻¹ hc (inv_ne_zero (uFlip_ne_zero hc)) := by
  have hS : ScaleConj c (uFlip c) hc (uFlip_ne_zero hc) :=
    scaleConj_of_homeo hc _ uFlipHomeo (fun z => uFlip_mul c z)
  exact ⟨hS, scaleConj_inv c hc,
    scaleConj_trans hS (scaleConj_inv (uFlip c) (uFlip_ne_zero hc))⟩

/-- `Statement:` `(uFlip c)⁻¹ = 4 ^ (-v(c)) * c`. -/
theorem ampFlip_eq (c : ℚ_[2]) : (uFlip c)⁻¹ = 4 ^ (-c.valuation) * c := by
  unfold uFlip; rw [mul_inv, inv_inv, zpow_neg]

end Flips

/-! ## § VI. Four multipliers on `OnePoint ℂ` -/

section FourComplex

/-- `Statement:` for `c ≠ 0`, `×c` satisfies `ScaleConj` with `×conj c`, `×c⁻¹` and `×(conj c)⁻¹`
    on `OnePoint ℂ` (`bend_conj_conj`, `scaleConj_inv`). -/
theorem complex_four_conj (c : ℂ) (hc : c ≠ 0) :
    ScaleConj c (conj c) hc ((map_ne_zero _).2 hc) ∧
    ScaleConj c c⁻¹ hc (inv_ne_zero hc) ∧
    ScaleConj c (conj c)⁻¹ hc (inv_ne_zero ((map_ne_zero _).2 hc)) := by
  have h1 : ScaleConj c (conj c) hc ((map_ne_zero _).2 hc) := ⟨_, bend_conj_conj c hc _⟩
  exact ⟨h1, scaleConj_inv c hc, scaleConj_trans h1 (scaleConj_inv _ _)⟩

/-- `Statement:` any two of `c`, `conj c`, `c⁻¹`, `(conj c)⁻¹` give limit motions on `OnePoint ℂ`
    related by a `Motion.HomeoIso`. -/
theorem complex_four_homeoIso (c : ℂ) (hc : c ≠ 0) :
    ∀ a b : ℂ, ∀ (ha : a ≠ 0) (hb : b ≠ 0),
      a ∈ ({c, conj c, c⁻¹, (conj c)⁻¹} : Set ℂ) → b ∈ ({c, conj c, c⁻¹, (conj c)⁻¹} : Set ℂ) →
      Nonempty (Motion.HomeoIso (limitMotion (lmScale a ha) (lmScale a ha).continuous)
        (limitMotion (lmScale b hb) (lmScale b hb).continuous)) := by
  obtain ⟨h1, h2, h3⟩ := complex_four_conj c hc
  have toC : ∀ a (ha : a ≠ 0), a ∈ ({c, conj c, c⁻¹, (conj c)⁻¹} : Set ℂ) →
      ScaleConj c a hc ha := by
    intro a ha hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact scaleConj_refl _ _
    · exact h1
    · exact h2
    · exact h3
  intro a b ha hb hma hmb
  exact scaleConj_homeoIso (scaleConj_trans (scaleConj_symm (toC a ha hma)) (toC b hb hmb))

/-- `Statement:` `z ↦ (conj z)⁻¹` on `OnePoint ℂ` fixes every point of the unit circle. -/
theorem complex_ampFlip_fixes_circle {z : ℂ} (hz : ‖z‖ = 1) :
    onePointInv (Homeomorph.onePointCongr Complex.conjLIE.toHomeomorph (OnePoint.some z)) =
      OnePoint.some z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hc0 : conj z ≠ 0 := (map_ne_zero _).2 hz0
  show onePointInv (OnePoint.some (Complex.conjLIE z)) = OnePoint.some z
  rw [Complex.conjLIE_apply, onePointInv_coe_ne hc0]
  congr 1
  apply inv_eq_of_mul_eq_one_left
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

/-- `Statement:` CONTROL: inversion alone and conjugation alone each move `i`. -/
theorem complex_flip_controls :
    onePointInv (OnePoint.some Complex.I) ≠ OnePoint.some Complex.I ∧
    conj Complex.I ≠ Complex.I := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [onePointInv_coe_ne Complex.I_ne_zero, Complex.inv_I] at h
    have := congrArg Complex.im (OnePoint.coe_injective h); simp at this; linarith
  · rw [Complex.conj_I] at h
    have := congrArg Complex.im h; simp at this; linarith

end FourComplex

/-! ## § VII. Attracting and repelling fixed points of a multiplier map on `OnePoint K` -/

section Stability

open Function

section Defs
variable {X : Type*} [TopologicalSpace X]

/-- `Statement:` `p` is fixed by `f` and has a neighbourhood all of whose orbits tend to `p`. -/
def IsAttractingFixedPt (f : X → X) (p : X) : Prop :=
  IsFixedPt f p ∧ ∃ U ∈ 𝓝 p, ∀ x ∈ U, Tendsto (fun n => f^[n] x) atTop (𝓝 p)

/-- `Statement:` `p` is fixed by `f` and has a neighbourhood `U` from which every point other than
    `p` has an iterate outside `U`. -/
def IsRepellingFixedPt (f : X → X) (p : X) : Prop :=
  IsFixedPt f p ∧ ∃ U ∈ 𝓝 p, ∀ x ∈ U, x ≠ p → ∃ n, f^[n] x ∉ U

variable {Y : Type*} [TopologicalSpace Y] {f : X → X} {g : Y → Y}

/-- `Statement:` `e ∘ f = g ∘ e` gives `g^[n] ∘ e = e ∘ f^[n]`. -/
theorem tb_conj_iterate (e : X ≃ₜ Y) (h : ∀ x, e (f x) = g (e x)) (n : ℕ) (x : X) :
    g^[n] (e x) = e (f^[n] x) :=
  ((Semiconj.iterate_right (f := e) h n) x).symm

/-- `Statement:` `e ∘ f = g ∘ e` gives `e⁻¹ ∘ g = f ∘ e⁻¹`. -/
theorem tb_conj_symm (e : X ≃ₜ Y) (h : ∀ x, e (f x) = g (e x)) :
    ∀ y, e.symm (g y) = f (e.symm y) := by
  intro y
  apply e.injective
  rw [h, e.apply_symm_apply, e.apply_symm_apply]

/-- `Statement:` a topological conjugacy carries an attracting fixed point to one. -/
theorem attracting_conj (e : X ≃ₜ Y) (h : ∀ x, e (f x) = g (e x)) {p : X}
    (hp : IsAttractingFixedPt f p) : IsAttractingFixedPt g (e p) := by
  obtain ⟨hfix, U, hU, hT⟩ := hp
  refine ⟨?_, e '' U, e.isOpenMap.image_mem_nhds hU, ?_⟩
  · show g (e p) = e p
    rw [← h, hfix]
  · rintro _ ⟨x, hx, rfl⟩
    simp only [tb_conj_iterate e h]
    exact (e.continuous.tendsto p).comp (hT x hx)

/-- `Statement:` a topological conjugacy carries a repelling fixed point to one. -/
theorem repelling_conj (e : X ≃ₜ Y) (h : ∀ x, e (f x) = g (e x)) {p : X}
    (hp : IsRepellingFixedPt f p) : IsRepellingFixedPt g (e p) := by
  obtain ⟨hfix, U, hU, hR⟩ := hp
  refine ⟨?_, e '' U, e.isOpenMap.image_mem_nhds hU, ?_⟩
  · show g (e p) = e p
    rw [← h, hfix]
  · rintro _ ⟨x, hx, rfl⟩ hne
    have hxp : x ≠ p := fun hxp => hne (by rw [hxp])
    obtain ⟨n, hn⟩ := hR x hx hxp
    refine ⟨n, ?_⟩
    rw [tb_conj_iterate e h]
    rintro ⟨y, hy, hey⟩
    exact hn (by rw [← e.injective hey]; exact hy)

/-- `Statement:` under a topological conjugacy, `e p` is attracting for `g` iff `p` is for `f`. -/
theorem attracting_conj_iff (e : X ≃ₜ Y) (h : ∀ x, e (f x) = g (e x)) (p : X) :
    IsAttractingFixedPt g (e p) ↔ IsAttractingFixedPt f p :=
  ⟨fun hg => by simpa using attracting_conj e.symm (tb_conj_symm e h) hg, attracting_conj e h⟩

/-- `Statement:` under a topological conjugacy, `e p` is repelling for `g` iff `p` is for `f`. -/
theorem repelling_conj_iff (e : X ≃ₜ Y) (h : ∀ x, e (f x) = g (e x)) (p : X) :
    IsRepellingFixedPt g (e p) ↔ IsRepellingFixedPt f p :=
  ⟨fun hg => by simpa using repelling_conj e.symm (tb_conj_symm e h) hg, repelling_conj e h⟩

/-- `Statement:` on a Hausdorff space, if every orbit other than `p`'s tends to `q ≠ p`, the fixed
    point `p` is repelling. -/
theorem repelling_of_tendsto [T2Space X] {p q : X} (hfix : IsFixedPt f p) (hpq : p ≠ q)
    (h : ∀ x, x ≠ p → Tendsto (fun n => f^[n] x) atTop (𝓝 q)) : IsRepellingFixedPt f p := by
  obtain ⟨U, V, hU, hV, hpU, hqV, hUV⟩ := t2_separation hpq
  refine ⟨hfix, U, hU.mem_nhds hpU, fun x _ hx => ?_⟩
  obtain ⟨n, hn⟩ := ((h x hx).eventually_mem (hV.mem_nhds hqV)).exists
  exact ⟨n, fun hU' => Set.disjoint_left.1 hUV hU' hn⟩

/-- `Statement:` for injective `f`, a fixed point `p` every neighbourhood of which holds another
    point is not both attracting and repelling. -/
theorem not_attracting_and_repelling (hf : Injective f) {p : X}
    (hacc : ∀ U ∈ 𝓝 p, ∃ x ∈ U, x ≠ p) :
    ¬ (IsAttractingFixedPt f p ∧ IsRepellingFixedPt f p) := by
  rintro ⟨⟨hfix, U, hU, hT⟩, ⟨_, W, hW, hR⟩⟩
  obtain ⟨x, ⟨hxU, hxW⟩, hxp⟩ := hacc (U ∩ W) (inter_mem hU hW)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hT x hxU).eventually_mem hW)
  have hy : f^[N] x ≠ p := by
    intro hfx
    apply hxp
    have : f^[N] x = f^[N] p := by rw [hfx, iterate_fixed hfix]
    exact (hf.iterate N) this
  obtain ⟨m, hm⟩ := hR _ (hN N le_rfl) hy
  apply hm
  rw [← iterate_add_apply]
  exact hN (m + N) (by omega)

end Defs

section Scaling
variable {K : Type*} [NontriviallyNormedField K]

/-- `Statement:` `lmScale c` fixes `0` of `K`. -/
theorem tb_fix_zero (c : K) (hc : c ≠ 0) : IsFixedPt (lmScale c hc) (OnePoint.some 0) := by
  show lmScale c hc (OnePoint.some 0) = _
  rw [lm_scale_some, mul_zero]

/-- `Statement:` `lmScale c` fixes `∞` of `OnePoint K`. -/
theorem tb_fix_infty (c : K) (hc : c ≠ 0) : IsFixedPt (lmScale c hc) OnePoint.infty :=
  lm_scale_infty c hc

/-- `Statement:` for `d ≠ 1`, the only fixed points of `lmScale d` are `0` of `K` and `∞`. -/
theorem tb_fixed_cases {d : K} (hd : d ≠ 0) (hd1 : d ≠ 1) {x : OnePoint K}
    (hx : IsFixedPt (lmScale d hd) x) : x = OnePoint.some 0 ∨ x = OnePoint.infty := by
  induction x using OnePoint.rec with
  | infty => exact Or.inr rfl
  | coe z =>
    left
    have h1 : d * z = z := OnePoint.coe_injective (by rw [← lm_scale_some d hd]; exact hx)
    have h2 : (d - 1) * z = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hd1
    · rw [h]

/-- `Statement:` for `‖c‖ < 1`, every orbit from a point of `K` tends to `0` of `K`. -/
theorem tb_tendsto_zero {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) (z : K) :
    Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some z)) atTop (𝓝 (OnePoint.some 0)) :=
  lm_tendsto_zero_of_field hc
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1).mul_const z)

/-- `Statement:` for `1 < ‖c‖`, every orbit from `z ≠ 0` tends to `∞`. -/
theorem tb_tendsto_infty [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : 1 < ‖c‖) {z : K}
    (hz : z ≠ 0) :
    Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some z)) atTop (𝓝 OnePoint.infty) := by
  have hci : ‖c⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc1
  have h := lm_tendsto_infty_of_conj c⁻¹ c (inv_ne_zero hc) hc (inv_mul_cancel₀ hc)
    (inv_ne_zero hz) (tb_tendsto_zero (inv_ne_zero hc) hci z⁻¹)
  rwa [inv_inv] at h

/-- `Statement:` every neighbourhood of `0` in `OnePoint K` contains the image of a ball of `K`. -/
theorem tb_ball_sub {U : Set (OnePoint K)} (hU : U ∈ 𝓝 (OnePoint.some (0 : K))) :
    ∃ r > 0, ∀ z : K, ‖z‖ < r → OnePoint.some z ∈ U := by
  have : (OnePoint.some : K → OnePoint K) ⁻¹' U ∈ 𝓝 (0 : K) :=
    OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 this
  exact ⟨r, hr, fun z hz => hball (by simpa using hz)⟩

/-- `Statement:` every neighbourhood of `0` in `OnePoint K` holds a point other than `0`. -/
theorem tb_acc_zero : ∀ U ∈ 𝓝 (OnePoint.some (0 : K)), ∃ x ∈ U, x ≠ OnePoint.some 0 := by
  intro U hU
  obtain ⟨r, hr, hsub⟩ := tb_ball_sub hU
  obtain ⟨z, hz0, hzr⟩ := NormedField.exists_norm_lt K hr
  refine ⟨OnePoint.some z, hsub z hzr, fun h => ?_⟩
  have : z = 0 := OnePoint.coe_injective h
  rw [this, norm_zero] at hz0
  exact lt_irrefl _ hz0

/-- `Statement:` for `‖c‖ < 1`, `0` of `K` is attracting for `lmScale c`. -/
theorem tb_zero_attracting {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) :
    IsAttractingFixedPt (lmScale c hc) (OnePoint.some 0) := by
  refine ⟨tb_fix_zero c hc, {OnePoint.infty}ᶜ,
    isOpen_compl_singleton.mem_nhds (OnePoint.coe_ne_infty 0), fun x hx => ?_⟩
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe z => exact tb_tendsto_zero hc hc1 z

/-- `Statement:` for `‖c‖ < 1`, `∞` of `OnePoint K` is repelling for `lmScale c`. -/
theorem tb_infty_repelling [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) :
    IsRepellingFixedPt (lmScale c hc) OnePoint.infty := by
  refine repelling_of_tendsto (tb_fix_infty c hc) (OnePoint.coe_ne_infty 0).symm (fun x hx => ?_)
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe z => exact tb_tendsto_zero hc hc1 z

/-- `Statement:` for `1 < ‖c‖`, `∞` of `OnePoint K` is attracting for `lmScale c`. -/
theorem tb_infty_attracting [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : 1 < ‖c‖) :
    IsAttractingFixedPt (lmScale c hc) OnePoint.infty := by
  refine ⟨tb_fix_infty c hc, {OnePoint.some 0}ᶜ,
    isOpen_compl_singleton.mem_nhds (OnePoint.coe_ne_infty 0).symm, fun x hx => ?_⟩
  induction x using OnePoint.rec with
  | infty =>
    simp only [iterate_fixed (tb_fix_infty c hc)]
    exact tendsto_const_nhds
  | coe z =>
    exact tb_tendsto_infty hc hc1 (fun h => hx (by simp [h]))

/-- `Statement:` for `1 < ‖c‖`, `0` of `K` is repelling for `lmScale c`. -/
theorem tb_zero_repelling [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : 1 < ‖c‖) :
    IsRepellingFixedPt (lmScale c hc) (OnePoint.some 0) := by
  refine repelling_of_tendsto (tb_fix_zero c hc) (OnePoint.coe_ne_infty 0) (fun x hx => ?_)
  induction x using OnePoint.rec with
  | infty =>
    simp only [iterate_fixed (tb_fix_infty c hc)]
    exact tendsto_const_nhds
  | coe z =>
    exact tb_tendsto_infty hc hc1 (fun h => hx (by simp [h]))

/-- `Statement:` for `1 < ‖c‖`, `0` of `K` is not attracting for `lmScale c`. -/
theorem tb_zero_not_attracting [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : 1 < ‖c‖) :
    ¬ IsAttractingFixedPt (lmScale c hc) (OnePoint.some 0) := by
  rintro ⟨_, U, hU, hT⟩
  obtain ⟨x, hxU, hx0⟩ := tb_acc_zero U hU
  induction x using OnePoint.rec with
  | infty =>
    have h := hT _ hxU
    simp only [iterate_fixed (tb_fix_infty c hc)] at h
    exact OnePoint.coe_ne_infty 0 (tendsto_nhds_unique h tendsto_const_nhds)
  | coe z =>
    have hz : z ≠ 0 := fun h => hx0 (by simp [h])
    exact OnePoint.coe_ne_infty 0
      (tendsto_nhds_unique (hT _ hxU) (tb_tendsto_infty hc hc1 hz))

/-- `Statement:` for `‖c‖ < 1`, `0` of `K` is not repelling for `lmScale c`. -/
theorem tb_zero_not_repelling {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) :
    ¬ IsRepellingFixedPt (lmScale c hc) (OnePoint.some 0) := fun hr =>
  not_attracting_and_repelling (lmScale c hc).injective tb_acc_zero
    ⟨tb_zero_attracting hc hc1, hr⟩

/-- `Statement:` for `‖c‖ = 1`, `0` of `K` is not attracting for `lmScale c`. -/
theorem tb_zero_not_attracting_of_norm_one {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ = 1) :
    ¬ IsAttractingFixedPt (lmScale c hc) (OnePoint.some 0) := by
  rintro ⟨_, U, hU, hT⟩
  obtain ⟨r, hr, hsub⟩ := tb_ball_sub hU
  obtain ⟨z, hz0, hzr⟩ := NormedField.exists_norm_lt K hr
  have h := hT _ (hsub z hzr)
  have hB : (OnePoint.some : K → OnePoint K) '' Metric.ball 0 ‖z‖ ∈
      𝓝 (OnePoint.some (0 : K)) :=
    OnePoint.isOpenMap_coe.image_mem_nhds (Metric.ball_mem_nhds 0 hz0)
  obtain ⟨n, hn⟩ := (h.eventually_mem hB).exists
  rw [lm_scale_iterate_some] at hn
  obtain ⟨w, hw, hwe⟩ := hn
  have : w = c ^ n * z := OnePoint.coe_injective hwe
  rw [this, Metric.mem_ball, dist_zero_right, norm_mul, norm_pow, hc1, one_pow, one_mul] at hw
  exact lt_irrefl _ hw

/-- `Statement:` for `‖c‖ = 1`, `0` of `K` is not repelling for `lmScale c`. -/
theorem tb_zero_not_repelling_of_norm_one {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ = 1) :
    ¬ IsRepellingFixedPt (lmScale c hc) (OnePoint.some 0) := by
  rintro ⟨_, U, hU, hR⟩
  obtain ⟨r, hr, hsub⟩ := tb_ball_sub hU
  obtain ⟨z, hz0, hzr⟩ := NormedField.exists_norm_lt K hr
  have hne : OnePoint.some z ≠ OnePoint.some 0 := fun h => by
    have : z = 0 := OnePoint.coe_injective h
    rw [this, norm_zero] at hz0; exact lt_irrefl _ hz0
  obtain ⟨n, hn⟩ := hR _ (hsub z hzr) hne
  rw [lm_scale_iterate_some] at hn
  apply hn
  apply hsub
  rw [norm_mul, norm_pow, hc1, one_pow, one_mul]
  exact hzr

/-- `Statement:` `∞` is attracting for `×c` iff `0` of `K` is attracting for `×c⁻¹`
    (transport through `onePointInvHomeo`). -/
theorem tb_infty_attracting_iff_zero [ProperSpace K] (c : K) (hc : c ≠ 0) :
    IsAttractingFixedPt (lmScale c hc) OnePoint.infty ↔
      IsAttractingFixedPt (lmScale c⁻¹ (inv_ne_zero hc)) (OnePoint.some 0) := by
  rw [← attracting_conj_iff onePointInvHomeo
    (lm_onePointInv_conj_scale c c⁻¹ hc (inv_ne_zero hc) (mul_inv_cancel₀ hc)),
    onePointInv_swaps.2]

/-- `Statement:` `∞` is repelling for `×c` iff `0` of `K` is repelling for `×c⁻¹`
    (transport through `onePointInvHomeo`). -/
theorem tb_infty_repelling_iff_zero [ProperSpace K] (c : K) (hc : c ≠ 0) :
    IsRepellingFixedPt (lmScale c hc) OnePoint.infty ↔
      IsRepellingFixedPt (lmScale c⁻¹ (inv_ne_zero hc)) (OnePoint.some 0) := by
  rw [← repelling_conj_iff onePointInvHomeo
    (lm_onePointInv_conj_scale c c⁻¹ hc (inv_ne_zero hc) (mul_inv_cancel₀ hc)),
    onePointInv_swaps.2]

/-- `Statement:` for `‖c‖ ≠ 1`: `0` of `K` is attracting for `lmScale c` iff `‖c‖ < 1`, and
    repelling iff `1 < ‖c‖`. -/
theorem scale_zero_classification [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ ≠ 1) :
    (IsAttractingFixedPt (lmScale c hc) (OnePoint.some 0) ↔ ‖c‖ < 1) ∧
    (IsRepellingFixedPt (lmScale c hc) (OnePoint.some 0) ↔ 1 < ‖c‖) := by
  rcases lt_or_gt_of_ne hc1 with h | h
  · exact ⟨iff_of_true (tb_zero_attracting hc h) h,
      iff_of_false (tb_zero_not_repelling hc h) (not_lt.2 h.le)⟩
  · exact ⟨iff_of_false (tb_zero_not_attracting hc h) (not_lt.2 h.le),
      iff_of_true (tb_zero_repelling hc h) h⟩

/-- `Statement:` for `‖c‖ ≠ 1`: `∞` of `OnePoint K` is attracting for `lmScale c` iff `1 < ‖c‖`,
    and repelling iff `‖c‖ < 1`. -/
theorem scale_infty_classification [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ ≠ 1) :
    (IsAttractingFixedPt (lmScale c hc) OnePoint.infty ↔ 1 < ‖c‖) ∧
    (IsRepellingFixedPt (lmScale c hc) OnePoint.infty ↔ ‖c‖ < 1) := by
  have hci : ‖c⁻¹‖ ≠ 1 := by rw [norm_inv]; exact fun h => hc1 (inv_eq_one.1 h)
  obtain ⟨hA, hR⟩ := scale_zero_classification (inv_ne_zero hc) hci
  have hn : 0 < ‖c‖ := norm_pos_iff.2 hc
  rw [tb_infty_attracting_iff_zero, tb_infty_repelling_iff_zero, hA, hR, norm_inv]
  exact ⟨inv_lt_one₀ hn, one_lt_inv₀ hn⟩

/-- `Statement:` for `‖c‖ = 1`, `∞` of `OnePoint K` is neither attracting nor repelling for
    `lmScale c`. -/
theorem scale_infty_neither_of_norm_one [ProperSpace K] {c : K} (hc : c ≠ 0) (hc1 : ‖c‖ = 1) :
    ¬ IsAttractingFixedPt (lmScale c hc) OnePoint.infty ∧
    ¬ IsRepellingFixedPt (lmScale c hc) OnePoint.infty := by
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc1, inv_one]
  rw [tb_infty_attracting_iff_zero, tb_infty_repelling_iff_zero]
  exact ⟨tb_zero_not_attracting_of_norm_one _ hci, tb_zero_not_repelling_of_norm_one _ hci⟩

/-- `Statement:` every homeomorphism of `OnePoint K` conjugating an expanding `lmScale c`
    (`1 < ‖c‖`) to a contracting `lmScale d` (`‖d‖ < 1`) sends `∞` to `0` of `K` and `0` of `K`
    to `∞`. -/
theorem conj_swaps_poles [ProperSpace K] {c d : K} (hc : c ≠ 0) (hd : d ≠ 0) (hc1 : 1 < ‖c‖)
    (hd1 : ‖d‖ < 1)
    (e : OnePoint K ≃ₜ OnePoint K) (he : ∀ x, e (lmScale c hc x) = lmScale d hd (e x)) :
    e OnePoint.infty = OnePoint.some 0 ∧ e (OnePoint.some 0) = OnePoint.infty := by
  have hd1' : d ≠ 1 := fun h => by rw [h, norm_one] at hd1; exact lt_irrefl _ hd1
  have hA := attracting_conj e he (tb_infty_attracting hc hc1)
  have hR := repelling_conj e he (tb_zero_repelling hc hc1)
  constructor
  · rcases tb_fixed_cases hd hd1' hA.1 with h | h
    · exact h
    · rw [h] at hA
      exact absurd hA (fun hA' => not_attracting_and_repelling (lmScale d hd).injective
        (by
          intro U hU
          have hU' : onePointInvHomeo ⁻¹' U ∈ 𝓝 (OnePoint.some (0 : K)) := by
            apply onePointInvHomeo.continuous.continuousAt.preimage_mem_nhds
            rw [onePointInv_swaps.1]; exact hU
          obtain ⟨x, hx, hx0⟩ := tb_acc_zero _ hU'
          refine ⟨onePointInvHomeo x, hx, fun h' => hx0 ?_⟩
          apply onePointInvHomeo.injective
          rw [h', onePointInv_swaps.1])
        ⟨hA', tb_infty_repelling hd hd1⟩)
  · rcases tb_fixed_cases hd hd1' hR.1 with h | h
    · rw [h] at hR; exact absurd hR (tb_zero_not_repelling hd hd1)
    · exact h

end Scaling

/-- `Statement:` on `OnePoint ℂ`, `×2`: `0` of ℂ is repelling and not attracting; `∞` of
    `OnePoint ℂ` is attracting and not repelling. -/
theorem complex_two_poles :
    IsRepellingFixedPt (lmScale (2 : ℂ) two_ne_zero) (OnePoint.some 0) ∧
    ¬ IsAttractingFixedPt (lmScale (2 : ℂ) two_ne_zero) (OnePoint.some 0) ∧
    IsAttractingFixedPt (lmScale (2 : ℂ) two_ne_zero) OnePoint.infty ∧
    ¬ IsRepellingFixedPt (lmScale (2 : ℂ) two_ne_zero) OnePoint.infty := by
  have h : 1 < ‖(2 : ℂ)‖ := by simp
  have h1 : ‖(2 : ℂ)‖ ≠ 1 := ne_of_gt h
  exact ⟨tb_zero_repelling _ h, tb_zero_not_attracting _ h, tb_infty_attracting _ h,
    fun hr => absurd ((scale_infty_classification _ h1).2.1 hr) (not_lt.2 h.le)⟩

/-- `Statement:` on `OnePoint ℚ_[2]`, `×2` (`‖2‖ < 1`): `0` of `ℚ_[2]` is attracting and not
    repelling; `∞` of `OnePoint ℚ_[2]` is repelling and not attracting. `Reading:` the roles of
    `complex_two_poles`, exchanged, on another carrier. -/
theorem padic_two_poles :
    IsAttractingFixedPt (lmScale (2 : ℚ_[2]) two_ne_zero) (OnePoint.some 0) ∧
    ¬ IsRepellingFixedPt (lmScale (2 : ℚ_[2]) two_ne_zero) (OnePoint.some 0) ∧
    IsRepellingFixedPt (lmScale (2 : ℚ_[2]) two_ne_zero) OnePoint.infty ∧
    ¬ IsAttractingFixedPt (lmScale (2 : ℚ_[2]) two_ne_zero) OnePoint.infty := by
  have h : ‖(2 : ℚ_[2])‖ < 1 := tb_norm_two_lt_one
  have h1 : ‖(2 : ℚ_[2])‖ ≠ 1 := ne_of_lt h
  exact ⟨tb_zero_attracting _ h, tb_zero_not_repelling _ h, tb_infty_repelling _ h,
    fun ha => absurd ((scale_infty_classification _ h1).1.1 ha) (not_lt.2 h.le)⟩

/-- `Statement:` CONTROL: `×1` on `OnePoint ℂ` fixes every point, and neither `0` of ℂ nor `∞` is
    attracting or repelling. -/
theorem scale_control_one :
    (∀ x, IsFixedPt (lmScale (1 : ℂ) one_ne_zero) x) ∧
    ¬ IsAttractingFixedPt (lmScale (1 : ℂ) one_ne_zero) (OnePoint.some 0) ∧
    ¬ IsRepellingFixedPt (lmScale (1 : ℂ) one_ne_zero) (OnePoint.some 0) ∧
    ¬ IsAttractingFixedPt (lmScale (1 : ℂ) one_ne_zero) OnePoint.infty ∧
    ¬ IsRepellingFixedPt (lmScale (1 : ℂ) one_ne_zero) OnePoint.infty := by
  have h : ‖(1 : ℂ)‖ = 1 := norm_one
  refine ⟨fun x => ?_, tb_zero_not_attracting_of_norm_one _ h,
    tb_zero_not_repelling_of_norm_one _ h,
    (scale_infty_neither_of_norm_one _ h).1, (scale_infty_neither_of_norm_one _ h).2⟩
  induction x using OnePoint.rec with
  | infty => exact tb_fix_infty _ _
  | coe z => show lmScale 1 _ (OnePoint.some z) = _; rw [lm_scale_some, one_mul]

/-- `Statement:` CONTROL: rotation `×i` on `OnePoint ℂ`: neither `0` of ℂ nor `∞` is attracting or
    repelling. -/
theorem scale_control_rotation :
    ¬ IsAttractingFixedPt (lmScale Complex.I Complex.I_ne_zero) (OnePoint.some 0) ∧
    ¬ IsRepellingFixedPt (lmScale Complex.I Complex.I_ne_zero) (OnePoint.some 0) ∧
    ¬ IsAttractingFixedPt (lmScale Complex.I Complex.I_ne_zero) OnePoint.infty ∧
    ¬ IsRepellingFixedPt (lmScale Complex.I Complex.I_ne_zero) OnePoint.infty := by
  have h : ‖Complex.I‖ = 1 := Complex.norm_I
  exact ⟨tb_zero_not_attracting_of_norm_one _ h, tb_zero_not_repelling_of_norm_one _ h,
    (scale_infty_neither_of_norm_one _ h).1, (scale_infty_neither_of_norm_one _ h).2⟩

end Stability

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms ScaleConj
#print axioms scaleConj_refl
#print axioms scaleConj_symm
#print axioms scaleConj_trans
#print axioms scaleConj_congr
#print axioms scaleConj_homeoIso
#print axioms scaleConj_inv
#print axioms scaleConj_of_homeo
#print axioms tb_val_eq_zero_of_norm_one
#print axioms tb_ne_zero_of_norm_one
#print axioms tb_norm_inv_one
#print axioms tb_val_eq_of_norm_eq
#print axioms tb_norm_eq_of_near
#print axioms tb_val_eventually_eq
#print axioms tb_val_two
#print axioms tb_val_three
#print axioms tb_val_four
#print axioms tb_norm_three
#print axioms dTwist
#print axioms dTwist_zero
#print axioms dTwist_norm
#print axioms dTwist_valuation
#print axioms dTwist_inv_left
#print axioms dTwist_continuous
#print axioms dTwistHomeo
#print axioms dTwist_isometry
#print axioms dTwist_conj_mul
#print axioms dTwist_scaleConj
#print axioms dTwist_scaleConj_two
#print axioms dTwist_two_six
#print axioms dTwist_mult_valuation
#print axioms dTwist_not_two_four
#print axioms tb_norm
#print axioms tb_norm_lt_iff
#print axioms tb_norm_two_pos
#print axioms tb_norm_two_lt_one
#print axioms tb_val_div
#print axioms tb_val_two_zpow
#print axioms tb_val_two_pow
#print axioms tb_res
#print axioms TbIsUnit
#print axioms TbInShells
#print axioms tbIsUnit_norm
#print axioms tbIsUnit_of_norm
#print axioms tbU_A
#print axioms tbU_B
#print axioms tbU_C
#print axioms tbU_D
#print axioms psiK
#print axioms rhoK
#print axioms psiK_mem
#print axioms rhoK_mem
#print axioms rho_psi
#print axioms psi_rho
#print axioms psiK_continuous
#print axioms rhoK_contAt
#print axioms stepMap
#print axioms stepInv
#print axioms tb_val_c_zpow
#print axioms stepMap_eq
#print axioms stepInv_eq
#print axioms tb_decompZ
#print axioms tb_decompY
#print axioms stepMap_zero
#print axioms stepInv_zero
#print axioms stepInv_stepMap
#print axioms stepMap_stepInv
#print axioms stepMap_conj
#print axioms stepMap_norm_le
#print axioms stepInv_norm_le
#print axioms stepMap_continuous
#print axioms stepInv_continuous
#print axioms stepHomeo
#print axioms scaleConj_two_val
#print axioms scaleConj_two_four
#print axioms scaleConj_two_of_norm_lt_one
#print axioms scaleConj_two_of_norm_ne_one
#print axioms scaleConj_of_norm_ne_one
#print axioms homeoIso_of_norm_ne_one
#print axioms tb_iter_scale
#print axioms scaleConj_two_not_norm_one
#print axioms uFlip
#print axioms uFlip_zero
#print axioms uFlip_ne_zero
#print axioms uFlip_valuation
#print axioms uFlip_norm
#print axioms uFlip_uFlip
#print axioms uFlip_mul
#print axioms uFlip_inv
#print axioms uFlip_continuous
#print axioms uFlipHomeo
#print axioms uFlipMulEquiv
#print axioms flipU
#print axioms flipI
#print axioms flipU_val
#print axioms flipU_continuous
#print axioms flipI_continuous
#print axioms tb_three_inv_ne
#print axioms tb_uFlip_three
#print axioms flip_klein_units
#print axioms flipS
#print axioms flipA
#print axioms flipS_some
#print axioms flipS_infty
#print axioms flipA_apply
#print axioms flipS_flipS
#print axioms flipS_comm_inv
#print axioms flip_klein_onePoint
#print axioms flip_poles
#print axioms flipA_fixes_shell
#print axioms rInv_shell
#print axioms rInv_moves_three
#print axioms flip_conj_scales
#print axioms ampFlip_eq
#print axioms complex_four_conj
#print axioms complex_four_homeoIso
#print axioms complex_ampFlip_fixes_circle
#print axioms complex_flip_controls
#print axioms IsAttractingFixedPt
#print axioms IsRepellingFixedPt
#print axioms tb_conj_iterate
#print axioms tb_conj_symm
#print axioms attracting_conj
#print axioms repelling_conj
#print axioms attracting_conj_iff
#print axioms repelling_conj_iff
#print axioms repelling_of_tendsto
#print axioms not_attracting_and_repelling
#print axioms tb_fix_zero
#print axioms tb_fix_infty
#print axioms tb_fixed_cases
#print axioms tb_tendsto_zero
#print axioms tb_tendsto_infty
#print axioms tb_ball_sub
#print axioms tb_acc_zero
#print axioms tb_zero_attracting
#print axioms tb_infty_repelling
#print axioms tb_infty_attracting
#print axioms tb_zero_repelling
#print axioms tb_zero_not_attracting
#print axioms tb_zero_not_repelling
#print axioms tb_zero_not_attracting_of_norm_one
#print axioms tb_zero_not_repelling_of_norm_one
#print axioms tb_infty_attracting_iff_zero
#print axioms tb_infty_repelling_iff_zero
#print axioms scale_zero_classification
#print axioms scale_infty_classification
#print axioms scale_infty_neither_of_norm_one
#print axioms conj_swaps_poles
#print axioms complex_two_poles
#print axioms padic_two_poles
#print axioms scale_control_one
#print axioms scale_control_rotation
end PurityCheck
