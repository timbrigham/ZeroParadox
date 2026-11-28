-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the overlap condition of TH3Die's (A)-(D) obstruction, and complex scaling `z ↦ c z` on `OnePoint ℂ` as a limit motion, read against the topological classification of Möbius (linear) maps: modulus and angle invisible to conjugacy for `‖c‖ ≠ 1`; at `‖c‖ = 1`, `c` and `conj c` conjugate (that conjugacy separates the rest is Rybalkina–Sergeichuk Lemma 2.1, literature, not proved here); and, for periodic maps (`c` a root of unity), the strict isomorphism of motions (`Motion.StrictIso`, the die isomorphism) seeing exactly conjugacy by a bare bijection, irrational rotations not covered. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.TH3Die
import ZeroParadox.Multihomed.LimitMotion
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

/-!
# The bend: the overlap condition, and complex scaling as a limit motion

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

Orthogonality versus not returning to the base vector likely has other applications in the project. We've talked about other potential angles in the relationships, and this might be exactly how they are represented. I was thinking of it as the outer line on a magnetic field, with the bend between zero and infinity.

---

Formal Overview (AI-assisted), citations and prior art: the ride-along `BendDie.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology ZPSemilattice ComplexConjugate

/-! ## § I. The overlap condition of the (A)-(D) obstruction -/

/-- `Statement:` for a unit vector `u`, projecting `v` onto `ℂ ∙ u` returns `u` iff `⟪u, v⟫ = 1`. -/
theorem bend_proj_eq_self_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u : E} (hu : ‖u‖ = 1) (v : E) :
    (ℂ ∙ u).starProjection v = u ↔ @inner ℂ E _ u v = 1 := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  rw [Submodule.starProjection_singleton, hu]
  constructor
  · intro h
    have h' : (@inner ℂ E _ u v) • u = (1 : ℂ) • u := by
      rw [one_smul]; convert h using 2; simp
    exact smul_left_injective ℂ hu0 h'
  · intro h; rw [h]; simp

section Overlap
variable (n : ℕ) (hn : 2 ≤ n)

/-- `Statement:` `th3E0 n hn` has norm `1` (`t2_norm_eq_one`). -/
theorem bend_e0_norm : ‖th3E0 n hn‖ = 1 := t2_norm_eq_one n _

/-- `Statement:` a map `MachinePhase → StateSpace n` with `c₀ ↦ v`, `c₁ ↦ th3E0` satisfying the lax
    UP square from `th3JoinUpMotion` to the projection motion onto `ℂ ∙ th3E0` exists iff
    `⟪th3E0, v⟫ = 1`; both directions. -/
theorem bend_AD_iff (s : StateSpace n → StateSpace n → Prop) (v : StateSpace n) :
    (∃ f : MachinePhase → StateSpace n, f c₀ = v ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f) ↔
      @inner ℂ (StateSpace n) _ (th3E0 n hn) v = 1 := by
  constructor
  · intro h
    by_contra hne
    exact th3_AD_no_upLax_of_proj_ne n hn s v
      (fun hp => hne ((bend_proj_eq_self_iff (bend_e0_norm n hn) v).1 hp)) h
  · intro h
    have hp := (bend_proj_eq_self_iff (bend_e0_norm n hn) v).2 h
    refine ⟨fun p => match p with | .initial => v | .running => th3E0 n hn, rfl, rfl, ?_⟩
    intro x y hy
    have hy' : y = join x c₁ := Part.mem_some_iff.1 hy
    subst hy'
    show _ ∈ Part.some ((ℂ ∙ th3E0 n hn).starProjection _)
    rw [Part.mem_some_iff]
    cases x
    · show th3E0 n hn = (ℂ ∙ th3E0 n hn).starProjection v
      rw [hp]
    · show th3E0 n hn = (ℂ ∙ th3E0 n hn).starProjection (th3E0 n hn)
      rw [th3_proj_e0_e0]

/-- `Statement:` the (A)-(D) obstruction fires iff `⟪th3E0, v⟫ ≠ 1`. -/
theorem bend_AD_obstructed_iff (s : StateSpace n → StateSpace n → Prop) (v : StateSpace n) :
    (¬ ∃ f : MachinePhase → StateSpace n, f c₀ = v ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f) ↔
      @inner ℂ (StateSpace n) _ (th3E0 n hn) v ≠ 1 :=
  not_congr (bend_AD_iff n hn s v)

/-- `Statement:` `⟪th3E0, th3E0⟫ = 1`. -/
theorem bend_inner_e0_e0 : @inner ℂ (StateSpace n) _ (th3E0 n hn) (th3E0 n hn) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, bend_e0_norm]; simp

/-- `Statement:` anti-parallel: overlap `-1`, and the obstruction fires. -/
theorem bend_antiparallel (s : StateSpace n → StateSpace n → Prop) :
    @inner ℂ (StateSpace n) _ (th3E0 n hn) (-th3E0 n hn) = -1 ∧
    ¬ ∃ f : MachinePhase → StateSpace n, f c₀ = -th3E0 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  have hi : @inner ℂ (StateSpace n) _ (th3E0 n hn) (-th3E0 n hn) = -1 := by
    rw [inner_neg_right, bend_inner_e0_e0]
  refine ⟨hi, (bend_AD_obstructed_iff n hn s _).2 ?_⟩
  rw [hi]; norm_num

/-- `Statement:` pure phase: overlap `i`, and the obstruction fires. -/
theorem bend_phase (s : StateSpace n → StateSpace n → Prop) :
    @inner ℂ (StateSpace n) _ (th3E0 n hn) (Complex.I • th3E0 n hn) = Complex.I ∧
    ¬ ∃ f : MachinePhase → StateSpace n, f c₀ = Complex.I • th3E0 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  have hi : @inner ℂ (StateSpace n) _ (th3E0 n hn) (Complex.I • th3E0 n hn) = Complex.I := by
    rw [inner_smul_right, bend_inner_e0_e0, mul_one]
  refine ⟨hi, (bend_AD_obstructed_iff n hn s _).2 ?_⟩
  rw [hi]; intro h; have := congrArg Complex.re h; simp at this

/-- `Statement:` CONTROL: for `w ⊥ th3E0`, the vector `th3E0 + w` has overlap `1`, and the
    obstruction does not fire. -/
theorem bend_overlap_one (s : StateSpace n → StateSpace n → Prop) (w : StateSpace n)
    (hw : @inner ℂ (StateSpace n) _ (th3E0 n hn) w = 0) :
    @inner ℂ (StateSpace n) _ (th3E0 n hn) (th3E0 n hn + w) = 1 ∧
    ∃ f : MachinePhase → StateSpace n, f c₀ = th3E0 n hn + w ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  have hi : @inner ℂ (StateSpace n) _ (th3E0 n hn) (th3E0 n hn + w) = 1 := by
    rw [inner_add_right, bend_inner_e0_e0, hw, add_zero]
  exact ⟨hi, (bend_AD_iff n hn s _).2 hi⟩

/-- `Statement:` the square exists for `-th3E0` iff it exists for the orthogonal `th3E1`, and
    for `i • th3E0` iff for `th3E1`. That it fails at all three is `bend_antiparallel`,
    `bend_phase` and `th3_AD_no_upLax`. -/
theorem bend_no_separation (s : StateSpace n → StateSpace n → Prop) :
    ((∃ f : MachinePhase → StateSpace n, f c₀ = -th3E0 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f) ↔
     (∃ f : MachinePhase → StateSpace n, f c₀ = th3E1 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f)) ∧
    ((∃ f : MachinePhase → StateSpace n, f c₀ = Complex.I • th3E0 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f) ↔
     (∃ f : MachinePhase → StateSpace n, f c₀ = th3E1 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f)) :=
  ⟨iff_of_false (bend_antiparallel n hn s).2 (th3_AD_no_upLax n hn s),
   iff_of_false (bend_phase n hn s).2 (th3_AD_no_upLax n hn s)⟩

end Overlap

/-! ## § II. Scaling by `c` on `OnePoint ℂ`: limits, polar form, inversion -/

/-- `Statement:` `0 < ‖c‖ < 1`: the orbit of every point `z` of ℂ tends to `0`; `∞`, which
    `lmScale` fixes, is not covered. -/
theorem bend_tendsto_zero {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) (z : ℂ) :
    Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some z)) atTop (𝓝 (OnePoint.some 0)) :=
  lm_tendsto_zero_of_field hc
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc1).mul_const z)

/-- `Statement:` `1 < ‖c‖`: every orbit from `z ≠ 0` tends to `∞` (transport through
    `lmHealedIso`). -/
theorem bend_tendsto_infty {c : ℂ} (hc : c ≠ 0) (hc1 : 1 < ‖c‖) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some z)) atTop (𝓝 OnePoint.infty) := by
  have hci : ‖c⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hc1
  have h := lm_tendsto_infty_of_conj c⁻¹ c (inv_ne_zero hc) hc (inv_mul_cancel₀ hc)
    (inv_ne_zero hz) (bend_tendsto_zero (inv_ne_zero hc) hci z⁻¹)
  rwa [inv_inv] at h

/-- `Statement:` `1 < ‖c‖`, `z ≠ 0`: the stages have a stage closure containing `∞`, and `z` does
    not arrive at `∞`. -/
theorem bend_closure_infty {c : ℂ} (hc : c ≠ 0) (hc1 : 1 < ‖c‖) {z : ℂ} (hz : z ≠ 0) :
    (∃ C, (limitMotion (lmScale c hc) (lmScale c hc).continuous).StageClosure
        (Set.range fun n => (lmScale c hc)^[n] (OnePoint.some z)) C ∧ OnePoint.infty ∈ C) ∧
    ¬ (limitMotion (lmScale c hc) (lmScale c hc).continuous).Arrives OnePoint.infty
        (OnePoint.some z) := by
  refine ⟨?_, lm_not_arrives_infty _ _ z⟩
  rcases (lm_tendsto_iff_arrival_or_closure _ _).1 (bend_tendsto_infty hc hc1 hz) with
    ⟨ha, _⟩ | ⟨_, C, hC, hp⟩
  · exact absurd ha (lm_not_arrives_infty _ _ z)
  · exact ⟨C, hC, hp⟩

/-- `Statement:` `0 < ‖c‖ < 1`, `z ≠ 0`: the stages have a stage closure containing `0`, and `z`
    does not arrive at `0`. -/
theorem bend_closure_zero {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ < 1) {z : ℂ} (hz : z ≠ 0) :
    (∃ C, (limitMotion (lmScale c hc) (lmScale c hc).continuous).StageClosure
        (Set.range fun n => (lmScale c hc)^[n] (OnePoint.some z)) C ∧ OnePoint.some 0 ∈ C) ∧
    ¬ (limitMotion (lmScale c hc) (lmScale c hc).continuous).Arrives (OnePoint.some 0)
        (OnePoint.some z) := by
  have hna : ¬ (limitMotion (lmScale c hc) (lmScale c hc).continuous).Arrives (OnePoint.some 0)
      (OnePoint.some z) := by
    rw [lm_arrives_iff]
    rintro ⟨n, hn⟩
    rw [lm_scale_iterate_some] at hn
    exact mul_ne_zero (pow_ne_zero n hc) hz (OnePoint.coe_injective hn)
  refine ⟨?_, hna⟩
  rcases (lm_tendsto_iff_arrival_or_closure _ _).1 (bend_tendsto_zero hc hc1 z) with
    ⟨ha, _⟩ | ⟨_, C, hC, hp⟩
  · exact absurd ha hna
  · exact ⟨C, hC, hp⟩

/-- `Statement:` with `c = r·exp(iθ)`, the `n`-th stage from `z` is `rⁿ·exp(i·nθ)·z`. -/
theorem bend_iterate_polar (r θ : ℝ) (hc : (r : ℂ) * Complex.exp (θ * Complex.I) ≠ 0)
    (z : ℂ) (n : ℕ) :
    (lmScale _ hc)^[n] (OnePoint.some z) =
      OnePoint.some (((r ^ n : ℝ) : ℂ) * Complex.exp (((n * θ : ℝ) : ℂ) * Complex.I) * z) := by
  have he : Complex.exp (((n * θ : ℝ) : ℂ) * Complex.I) = Complex.exp (θ * Complex.I) ^ n := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [lm_scale_iterate_some, he, mul_pow]; push_cast; ring_nf

/-- `Statement:` for `c ≠ 0` and `z ≠ 0`, the argument of `cⁿ·z`, as an angle mod 2π, is
    `n • arg c + arg z`. -/
theorem bend_arg_iterate {c z : ℂ} (hc : c ≠ 0) (hz : z ≠ 0) (n : ℕ) :
    (Complex.arg (c ^ n * z) : Real.Angle) = n • (Complex.arg c : Real.Angle) + Complex.arg z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, Complex.arg_mul_coe_angle hc (mul_ne_zero (pow_ne_zero n hc) hz),
      ih, succ_nsmul]
    abel

/-- `Statement:` for `r > 0`, `arg (r·exp(iθ)) = θ` as an angle. -/
theorem bend_arg_polar {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    (Complex.arg ((r : ℂ) * Complex.exp (θ * Complex.I)) : Real.Angle) = θ := by
  have := Complex.arg_mul_cos_add_sin_mul_I_coe_angle hr (θ : Real.Angle)
  rw [Real.Angle.cos_coe, Real.Angle.sin_coe] at this
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  exact this

/-- `Statement:` `(r·exp(iθ))⁻¹ = r⁻¹·exp(-iθ)`. -/
theorem bend_inv_polar (r θ : ℝ) :
    ((r : ℂ) * Complex.exp (θ * Complex.I))⁻¹ =
      ((r⁻¹ : ℝ) : ℂ) * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
  rw [mul_inv, ← Complex.exp_neg]; push_cast; ring_nf

/-- `Statement:` `arg c⁻¹ = -arg c` as angles; along the orbit, `onePointInv` sends the `n`-th
    `c`-stage from `z` to the `n`-th `c⁻¹`-stage from `z⁻¹`, whose angle is negated. -/
theorem bend_inv_angle {c : ℂ} (hc : c ≠ 0) (z : ℂ) (n : ℕ) :
    (Complex.arg c⁻¹ : Real.Angle) = -(Complex.arg c : Real.Angle) ∧
    (Complex.arg ((c⁻¹) ^ n * z⁻¹) : Real.Angle) = -(Complex.arg (c ^ n * z) : Real.Angle) ∧
    onePointInv ((lmScale c hc)^[n] (OnePoint.some z)) =
      (lmScale c⁻¹ (inv_ne_zero hc))^[n] (onePointInv (OnePoint.some z)) := by
  refine ⟨Complex.arg_inv_coe_angle c, ?_, ?_⟩
  · rw [inv_pow, ← mul_inv, Complex.arg_inv_coe_angle]
  · have hconj := lm_onePointInv_conj_scale c c⁻¹ hc (inv_ne_zero hc) (mul_inv_cancel₀ hc)
    exact (Function.Semiconj.iterate_right (f := onePointInvHomeo) hconj n) (OnePoint.some z)

/-! ## § III. The angle is invisible for `‖c‖ ≠ 1`: the logarithmic-spiral twist -/

/-- `Statement:` the twist `z ↦ z · exp(i α log ‖z‖)`; `Real.log 0 = 0`, so `0 ↦ 0`. -/
noncomputable def bendTwist (α : ℝ) (z : ℂ) : ℂ :=
  z * Complex.exp (((α * Real.log ‖z‖ : ℝ) : ℂ) * Complex.I)

/-- `Statement:` the twist preserves the norm. -/
theorem bendTwist_norm (α : ℝ) (z : ℂ) : ‖bendTwist α z‖ = ‖z‖ := by
  rw [bendTwist, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- `Statement:` the twist by `-α` undoes the twist by `α`. -/
theorem bendTwist_neg_left (α : ℝ) (z : ℂ) : bendTwist (-α) (bendTwist α z) = z := by
  have hn := bendTwist_norm α z
  show bendTwist α z * Complex.exp ((((-α) * Real.log ‖bendTwist α z‖ : ℝ) : ℂ) * Complex.I) = z
  rw [hn, bendTwist, mul_assoc, ← Complex.exp_add]
  have : ((α * Real.log ‖z‖ : ℝ) : ℂ) * Complex.I + (((-α) * Real.log ‖z‖ : ℝ) : ℂ) * Complex.I
      = 0 := by push_cast; ring
  rw [this, Complex.exp_zero, mul_one]

/-- `Statement:` the twist is continuous on ℂ, `0` included. -/
theorem bendTwist_continuous (α : ℝ) : Continuous (bendTwist α) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : bendTwist α 0 = 0 := by simp [bendTwist]
    show Tendsto (bendTwist α) (𝓝 0) (𝓝 (bendTwist α 0))
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [bendTwist_norm]
    exact tendsto_norm_zero
  · have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    unfold bendTwist
    fun_prop (disch := exact hz')

/-- `Statement:` the twist as a homeomorphism of ℂ, with inverse the twist by `-α`. -/
noncomputable def bendTwistHomeo (α : ℝ) : ℂ ≃ₜ ℂ where
  toFun := bendTwist α
  invFun := bendTwist (-α)
  left_inv := bendTwist_neg_left α
  right_inv z := by simpa using bendTwist_neg_left (-α) z
  continuous_toFun := bendTwist_continuous α
  continuous_invFun := bendTwist_continuous (-α)

-- Statement: CONTROL: the twist by `α = 0` is the identity.
example (z : ℂ) : bendTwistHomeo 0 z = z := by simp [bendTwistHomeo, bendTwist]

/-- `Statement:` the twist conjugates multiplication by `c` to multiplication by
    `c·exp(iα log‖c‖)`. -/
theorem bendTwist_conj (α : ℝ) {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    bendTwist α (c * z) =
      (c * Complex.exp (((α * Real.log ‖c‖ : ℝ) : ℂ) * Complex.I)) * bendTwist α z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [bendTwist]
  · simp only [bendTwist, norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 hc) (norm_ne_zero_iff.2 hz)]
    have : Complex.exp (((α * (Real.log ‖c‖ + Real.log ‖z‖) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((α * Real.log ‖c‖ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((α * Real.log ‖z‖ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring

/-- `Statement:` for `‖c‖ ≠ 1` and any angle `φ`, the limit motions of scaling by `c` and by
    `d = c·exp(iφ)` on `OnePoint ℂ` are strictly isomorphic, through a homeomorphism. -/
noncomputable def bendIso (c d : ℂ) (hc : c ≠ 0) (hd : d ≠ 0) (hc1 : ‖c‖ ≠ 1) (φ : ℝ)
    (hcd : d = c * Complex.exp (φ * Complex.I)) :
    Motion.StrictIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale d hd) (lmScale d hd).continuous) :=
  lmIsoOfConj _ (Homeomorph.onePointCongr (bendTwistHomeo (φ / Real.log ‖c‖))) (fun z => by
    have hl : Real.log ‖c‖ ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 hc) hc1
    induction z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      show OnePoint.some (bendTwist (φ / Real.log ‖c‖) (c * x)) =
        OnePoint.some (d * bendTwist (φ / Real.log ‖c‖) x)
      rw [bendTwist_conj _ hc, div_mul_cancel₀ _ hl, hcd])

/-- `Statement:` for `‖c‖ ≠ 1`, scaling by `‖c‖` and by `c` are strictly isomorphic limit
    motions. -/
theorem bend_iso_abs (c : ℂ) (hc : c ≠ 0) (hc1 : ‖c‖ ≠ 1) :
    Nonempty (Motion.StrictIso
      (limitMotion (lmScale (‖c‖ : ℂ) (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc)))
        (lmScale _ _).continuous)
      (limitMotion (lmScale c hc) (lmScale c hc).continuous)) :=
  ⟨bendIso _ c _ hc (by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg c)]; exact hc1)
    (Complex.arg c) (Complex.norm_mul_exp_arg_mul_I c).symm⟩

/-! ## § IV. The modulus is invisible for `‖c‖ ≠ 1`: the radial power -/

/-- `Statement:` the radial power `z ↦ ‖z‖^(p-1) · z`, sending norm `r` to norm `r^p` for `p > 0`. -/
noncomputable def bendRadial (p : ℝ) (z : ℂ) : ℂ := ((‖z‖ ^ (p - 1) : ℝ) : ℂ) * z

/-- `Statement:` for `p > 0`, `‖bendRadial p z‖ = ‖z‖ ^ p`. -/
theorem bendRadial_norm {p : ℝ} (hp : 0 < p) (z : ℂ) : ‖bendRadial p z‖ = ‖z‖ ^ p := by
  rw [bendRadial, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow hp.ne']
  · rw [Real.rpow_sub_one (norm_ne_zero_iff.2 hz), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hz)]

/-- `Statement:` for `p > 0`, the radial power by `p⁻¹` undoes the radial power by `p`. -/
theorem bendRadial_inv {p : ℝ} (hp : 0 < p) (z : ℂ) : bendRadial p⁻¹ (bendRadial p z) = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [bendRadial]
  · have hn := bendRadial_norm hp z
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    rw [bendRadial, hn, bendRadial, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_mul hz'.le,
      ← Real.rpow_add hz']
    have : p * (p⁻¹ - 1) + (p - 1) = 0 := by rw [mul_sub, mul_inv_cancel₀ hp.ne']; ring
    rw [this, Real.rpow_zero, Complex.ofReal_one, one_mul]

/-- `Statement:` for `p > 0`, the radial power is continuous on ℂ, `0` included. -/
theorem bendRadial_continuous {p : ℝ} (hp : 0 < p) : Continuous (bendRadial p) := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · have h0 : bendRadial p 0 = 0 := by simp [bendRadial]
    show Tendsto (bendRadial p) (𝓝 0) (𝓝 (bendRadial p 0))
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    simp only [bendRadial_norm hp]
    have h := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).comp
      (tendsto_norm_zero (E := ℂ))
    simpa [Function.comp_def, Real.zero_rpow hp.ne'] using h
  · have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    unfold bendRadial
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inl hz')).comp continuous_norm.continuousAt)).mul
      continuousAt_id

/-- `Statement:` for `p > 0`, the radial power as a homeomorphism of ℂ. -/
noncomputable def bendRadialHomeo (p : ℝ) (hp : 0 < p) : ℂ ≃ₜ ℂ where
  toFun := bendRadial p
  invFun := bendRadial p⁻¹
  left_inv := bendRadial_inv hp
  right_inv z := by simpa using bendRadial_inv (inv_pos.2 hp) z
  continuous_toFun := bendRadial_continuous hp
  continuous_invFun := bendRadial_continuous (inv_pos.2 hp)

/-- `Statement:` the radial power conjugates multiplication by `c` to multiplication by
    `‖c‖^(p-1) · c`. -/
theorem bendRadial_conj (p : ℝ) (c z : ℂ) :
    bendRadial p (c * z) = (((‖c‖ ^ (p - 1) : ℝ) : ℂ) * c) * bendRadial p z := by
  simp only [bendRadial, norm_mul, Real.mul_rpow (norm_nonneg c) (norm_nonneg z),
    Complex.ofReal_mul]
  ring

/-- `Statement:` for `‖a‖ = ‖d‖ ≠ 1`, the twist by `(arg d - arg a) / log ‖a‖` conjugates
    multiplication by `a` to multiplication by `d`. -/
theorem bend_twist_conj_of_norm_eq {a d : ℂ} (ha : a ≠ 0) (hn : ‖a‖ = ‖d‖) (h1 : ‖a‖ ≠ 1) (z : ℂ) :
    bendTwist ((Complex.arg d - Complex.arg a) / Real.log ‖a‖) (a * z) =
      d * bendTwist ((Complex.arg d - Complex.arg a) / Real.log ‖a‖) z := by
  have hl : Real.log ‖a‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (norm_pos_iff.2 ha) h1
  have key : a * Complex.exp (((Complex.arg d - Complex.arg a : ℝ) : ℂ) * Complex.I) = d := by
    have e1 := Complex.norm_mul_exp_arg_mul_I a
    have e2 := Complex.norm_mul_exp_arg_mul_I d
    calc a * Complex.exp (((Complex.arg d - Complex.arg a : ℝ) : ℂ) * Complex.I)
        = ((‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I)) *
            Complex.exp (((Complex.arg d - Complex.arg a : ℝ) : ℂ) * Complex.I) := by rw [e1]
      _ = (‖d‖ : ℂ) * Complex.exp (Complex.arg d * Complex.I) := by
          rw [hn, mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
      _ = d := e2
  rw [bendTwist_conj _ ha, div_mul_cancel₀ _ hl, key]

/-- `Statement:` for `c ≠ 0` and `d ≠ 0`, if `‖c‖, ‖d‖ < 1`, or `‖c‖, ‖d‖ > 1`, a homeomorphism
    of ℂ conjugates multiplication by `c` to multiplication by `d`. -/
theorem bend_conj_same_side {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0)
    (hs : (‖c‖ < 1 ∧ ‖d‖ < 1) ∨ (1 < ‖c‖ ∧ 1 < ‖d‖)) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ z, e (c * z) = d * e z := by
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hlc : Real.log ‖c‖ ≠ 0 := by
    rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (Real.log_neg hc0 h1).ne
    · exact (Real.log_pos h1).ne'
  have hd1 : ‖d‖ ≠ 1 := by
    rcases hs with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2.ne
    · exact h2.ne'
  obtain ⟨p, hpdef⟩ : ∃ p : ℝ, p = Real.log ‖d‖ / Real.log ‖c‖ := ⟨_, rfl⟩
  have hp : 0 < p := by
    rw [hpdef]
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact div_pos_of_neg_of_neg (Real.log_neg hd0 h2) (Real.log_neg hc0 h1)
    · exact div_pos (Real.log_pos h2) (Real.log_pos h1)
  obtain ⟨a, hadef⟩ : ∃ a : ℂ, a = ((‖c‖ ^ (p - 1) : ℝ) : ℂ) * c := ⟨_, rfl⟩
  have han : ‖a‖ = ‖d‖ := by
    have h : ‖a‖ = ‖c‖ ^ p := by rw [hadef]; exact bendRadial_norm hp c
    rw [h, Real.rpow_def_of_pos hc0,
      show Real.log ‖c‖ * p = Real.log ‖d‖ by rw [hpdef]; field_simp, Real.exp_log hd0]
  have ha : a ≠ 0 := norm_ne_zero_iff.1 (by rw [han]; exact hd0.ne')
  refine ⟨(bendRadialHomeo p hp).trans
    (bendTwistHomeo ((Complex.arg d - Complex.arg a) / Real.log ‖a‖)), fun z => ?_⟩
  show bendTwist _ (bendRadial p (c * z)) = d * bendTwist _ (bendRadial p z)
  rw [bendRadial_conj, ← hadef]
  exact bend_twist_conj_of_norm_eq ha han (by rw [han]; exact hd1) _

/-- `Statement:` a homeomorphism `e` of ℂ with `e (c z) = d (e z)` extends to `OnePoint ℂ`
    conjugating `lmScale c` to `lmScale d`. -/
theorem bend_onePointCongr_conj {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (e : ℂ ≃ₜ ℂ)
    (h : ∀ z, e (c * z) = d * e z) (x : OnePoint ℂ) :
    Homeomorph.onePointCongr e (lmScale c hc x) = lmScale d hd (Homeomorph.onePointCongr e x) := by
  induction x using OnePoint.rec with
  | infty => rfl
  | coe z =>
    show OnePoint.some (e (c * z)) = OnePoint.some (d * e z)
    rw [h]

/-- `Statement:` if `‖c‖ ≠ 1` and `‖d‖ ≠ 1`, a homeomorphism of `OnePoint ℂ` conjugates `lmScale c`
    to `lmScale d`; a contracting `c` and an expanding `d` go through `onePointInvHomeo`. -/
theorem bend_conj_of_norm_ne_one {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (hc1 : ‖c‖ ≠ 1)
    (hd1 : ‖d‖ ≠ 1) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, ∀ x, e (lmScale c hc x) = lmScale d hd (e x) := by
  have hci : c⁻¹ ≠ 0 := inv_ne_zero hc
  have viaInv : ((‖c⁻¹‖ < 1 ∧ ‖d‖ < 1) ∨ (1 < ‖c⁻¹‖ ∧ 1 < ‖d‖)) →
      ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ, ∀ x, e (lmScale c hc x) = lmScale d hd (e x) := by
    intro hs
    obtain ⟨e, he⟩ := bend_conj_same_side hci hd hs
    refine ⟨onePointInvHomeo.trans (Homeomorph.onePointCongr e), fun x => ?_⟩
    show Homeomorph.onePointCongr e (onePointInvHomeo (lmScale c hc x)) =
      lmScale d hd (Homeomorph.onePointCongr e (onePointInvHomeo x))
    rw [lm_onePointInv_conj_scale c c⁻¹ hc hci (mul_inv_cancel₀ hc),
      bend_onePointCongr_conj hci hd e he]
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  rcases lt_or_gt_of_ne hc1 with h1 | h1 <;> rcases lt_or_gt_of_ne hd1 with h2 | h2
  · obtain ⟨e, he⟩ := bend_conj_same_side hc hd (Or.inl ⟨h1, h2⟩)
    exact ⟨Homeomorph.onePointCongr e, bend_onePointCongr_conj hc hd e he⟩
  · exact viaInv (Or.inr ⟨by rw [norm_inv]; exact (one_lt_inv₀ hc0).2 h1, h2⟩)
  · exact viaInv (Or.inl ⟨by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h1, h2⟩)
  · obtain ⟨e, he⟩ := bend_conj_same_side hc hd (Or.inr ⟨h1, h2⟩)
    exact ⟨Homeomorph.onePointCongr e, bend_onePointCongr_conj hc hd e he⟩

/-- `Statement:` if `‖c‖ ≠ 1` and `‖d‖ ≠ 1`, the limit motions of `lmScale c` and `lmScale d` are
    strictly isomorphic. -/
theorem bend_iso_of_norm_ne_one {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (hc1 : ‖c‖ ≠ 1)
    (hd1 : ‖d‖ ≠ 1) :
    Nonempty (Motion.StrictIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale d hd) (lmScale d hd).continuous)) := by
  obtain ⟨e, he⟩ := bend_conj_of_norm_ne_one hc hd hc1 hd1
  exact ⟨lmIsoOfConj _ e he⟩

-- Statement: scaling by `1/2` (contracting) and by `3` (expanding) are strictly isomorphic limit motions.
example : Nonempty (Motion.StrictIso
    (limitMotion (lmScale (1 / 2 : ℂ) (by norm_num)) (lmScale _ _).continuous)
    (limitMotion (lmScale (3 : ℂ) (by norm_num)) (lmScale _ _).continuous)) :=
  bend_iso_of_norm_ne_one _ _ (by norm_num) (by norm_num)

/-! ## § V. `c` against `conj c` for every `c ≠ 0`, the case `‖c‖ = 1`, and two negative controls -/

/-- `Statement:` complex conjugation, extended to `OnePoint ℂ`, conjugates `lmScale c` to
    `lmScale (conj c)`. -/
theorem bend_conj_conj (c : ℂ) (hc : c ≠ 0) (hc' : conj c ≠ 0) (x : OnePoint ℂ) :
    Homeomorph.onePointCongr Complex.conjLIE.toHomeomorph (lmScale c hc x) =
      lmScale (conj c) hc' (Homeomorph.onePointCongr Complex.conjLIE.toHomeomorph x) :=
  bend_onePointCongr_conj hc hc' _ (fun z => by simp) x

/-- `Statement:` the limit motions of `lmScale c` and `lmScale (conj c)` are strictly isomorphic,
    for every `c ≠ 0`. -/
noncomputable def bendConjIso (c : ℂ) (hc : c ≠ 0) (hc' : conj c ≠ 0) :
    Motion.StrictIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale (conj c) hc') (lmScale _ hc').continuous) :=
  lmIsoOfConj _ _ (bend_conj_conj c hc hc')

/-- `Statement:` CONTROL: rotation by `i` and rotation by `-i` are strictly isomorphic limit
    motions. -/
theorem bend_iso_I_negI :
    Nonempty (Motion.StrictIso
      (limitMotion (lmScale Complex.I Complex.I_ne_zero) (lmScale _ _).continuous)
      (limitMotion (lmScale (-Complex.I) (neg_ne_zero.2 Complex.I_ne_zero))
        (lmScale _ _).continuous)) :=
  ⟨lmIsoOfConj _ (Homeomorph.onePointCongr Complex.conjLIE.toHomeomorph)
    (bend_onePointCongr_conj _ _ _ (fun z => by simp))⟩

/-- `Statement:` CONTROL: `‖c‖ = 1`, `c ≠ 1`: the orbit of `1` tends to no point of `OnePoint ℂ`. -/
theorem bend_rotation_no_limit {c : ℂ} (hc : c ≠ 0) (hc1 : ‖c‖ = 1) (hne : c ≠ 1) :
    ¬ ∃ q, Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some 1)) atTop (𝓝 q) := by
  rintro ⟨q, hq⟩
  have hfix := isFixedPt_of_tendsto_iterate hq (lmScale c hc).continuous.continuousAt
  simp only [lm_scale_iterate_some, mul_one] at hq
  induction q using OnePoint.rec with
  | infty =>
    have hU : IsOpen ((OnePoint.some '' Metric.closedBall (0 : ℂ) 1)ᶜ) :=
      OnePoint.isOpen_compl_image_coe.2 ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 1⟩
    obtain ⟨n, hn⟩ := (hq.eventually (hU.mem_nhds OnePoint.infty_notMem_image_coe)).exists
    exact hn ⟨c ^ n, by simp [norm_pow, hc1], rfl⟩
  | coe y =>
    have hy : c * y = y := OnePoint.coe_injective hfix
    have hy0 : y = 0 := by
      have : (c - 1) * y = 0 := by linear_combination hy
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    subst hy0
    have ht : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
      (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).2 hq
    have hn := ht.norm
    simp only [norm_pow, hc1, one_pow, norm_zero] at hn
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

-- Statement: at `‖c‖ = 1` the twist's `α = φ / log ‖c‖` has denominator `0`.
example {c : ℂ} (hc1 : ‖c‖ = 1) : Real.log ‖c‖ = 0 := by rw [hc1, Real.log_one]

/-- `Statement:` CONTROL: a scaling `c ≠ 1` is not strictly isomorphic to the identity scaling. -/
theorem bend_rotation_ne_identity {c : ℂ} (hc : c ≠ 0) (hne : c ≠ 1) :
    ¬ Nonempty (Motion.StrictIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale (1 : ℂ) one_ne_zero) (lmScale _ _).continuous)) := by
  rintro ⟨φ⟩
  set y := φ.hom.toFun (OnePoint.some 1)
  have hland : (limitMotion (lmScale (1 : ℂ) one_ne_zero) (lmScale _ _).continuous).IsLanding y := by
    rw [lm_isLanding_iff]
    induction y using OnePoint.rec with
    | infty => rfl
    | coe x => rw [lm_scale_some, one_mul]
  have hup := φ.inv.map_up y
  have hmem : φ.inv.toFun y ∈
      (limitMotion (lmScale c hc) (lmScale c hc).continuous).up (φ.inv.toFun y) := by
    rw [hup, Part.mem_map_iff]; exact ⟨y, hland, rfl⟩
  rw [φ.left_inv] at hmem
  have hfix := (lm_isLanding_iff (hg := (lmScale c hc).continuous) _).1 hmem
  rw [lm_scale_some, mul_one] at hfix
  exact hne (OnePoint.coe_injective hfix)

/-- `Statement:` the half turn `-1` and the quarter turn `i` give limit motions that are not
    strictly isomorphic; the proof uses that the half turn squares to the identity and that the
    quarter turn does not (`i · i = -1 ≠ 1`). -/
theorem bend_halfturn_ne_quarterturn :
    ¬ Nonempty (Motion.StrictIso
      (limitMotion (lmScale (-1 : ℂ) (neg_ne_zero.2 one_ne_zero)) (lmScale _ _).continuous)
      (limitMotion (lmScale Complex.I Complex.I_ne_zero) (lmScale _ _).continuous)) := by
  rintro ⟨φ⟩
  set g := lmScale (-1 : ℂ) (neg_ne_zero.2 one_ne_zero)
  set h := lmScale Complex.I Complex.I_ne_zero
  have hc : ∀ a, φ.hom.toFun (g a) = h (φ.hom.toFun a) := fun a => φ.hom.map_step rfl
  have hgg : ∀ a, g (g a) = a := by
    intro a
    induction a using OnePoint.rec with
    | infty => rfl
    | coe x => show OnePoint.some ((-1) * ((-1) * x)) = OnePoint.some x; ring_nf
  set a := φ.inv.toFun (OnePoint.some 1)
  have ha : φ.hom.toFun a = OnePoint.some 1 := φ.right_inv _
  have h2 : φ.hom.toFun (g (g a)) = OnePoint.some (Complex.I * (Complex.I * 1)) := by
    rw [hc, hc, ha]; rfl
  rw [hgg, ha] at h2
  have h3 : (1 : ℂ) = Complex.I * (Complex.I * 1) := OnePoint.coe_injective h2
  rw [mul_one, Complex.I_mul_I] at h3
  have := congrArg Complex.re h3
  norm_num at this

/-! ## § VI. Periodic maps: the die isomorphism needs no continuity -/

section Periodic

universe u

variable {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]

/-- `Statement:` if `g^[n] x = x` with `0 < n`, then `q` is a value of the limit retraction at
    `x` iff `x` is a fixed point and `q = x`; on a Hausdorff space, `g` need not be continuous. -/
theorem bend_mem_limitRetraction_of_periodic {g : X → X} {n : ℕ} (hn : 0 < n)
    {x q : X} (hper : g^[n] x = x) : q ∈ limitRetraction g x ↔ g x = x ∧ q = x := by
  rw [lm_mem_limitRetraction_iff]
  constructor
  · intro ht
    have hmul : Tendsto (fun k : ℕ => n * k) atTop atTop :=
      tendsto_atTop_atTop.2 fun b => ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a hn)⟩
    have hsub : Tendsto (fun k => g^[n * k] x) atTop (𝓝 q) := ht.comp hmul
    have hconst : ∀ k, g^[n * k] x = x := fun k => by
      rw [Function.iterate_mul]; exact Function.iterate_fixed hper k
    have hxq : x = q := tendsto_nhds_unique tendsto_const_nhds
      (by simpa only [hconst] using hsub)
    subst hxq
    have hmul1 : Tendsto (fun k : ℕ => n * k + 1) atTop atTop :=
      tendsto_atTop_atTop.2 fun b =>
        ⟨b, fun a ha => le_trans ha (le_trans (Nat.le_mul_of_pos_left a hn) (Nat.le_succ _))⟩
    have hsub1 : Tendsto (fun k => g^[n * k + 1] x) atTop (𝓝 x) := ht.comp hmul1
    have hconst1 : ∀ k, g^[n * k + 1] x = g x := fun k => by
      rw [Function.iterate_succ_apply', hconst]
    exact ⟨tendsto_nhds_unique tendsto_const_nhds (by simpa only [hconst1] using hsub1), rfl⟩
  · rintro ⟨hfix, hq⟩
    rw [hq]
    have : (fun k => g^[k] x) = fun _ => x := funext fun k => Function.iterate_fixed hfix k
    rw [this]; exact tendsto_const_nhds

/-- `Statement:` if `g^[n] = id` and `h^[m] = id` (`0 < n`, `0 < m`), an injective `f` with
    `f ∘ g = h ∘ f` makes the UP square of the limit motions commute (`Motion.UpStrict`). -/
theorem bend_upStrict_of_periodic {g : X → X} {h : Y → Y} (hg : Continuous g) (hh : Continuous h)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hgn : ∀ x, g^[n] x = x) (hhm : ∀ y, h^[m] y = y)
    (f : X → Y) (hf : Function.Injective f) (hc : ∀ x, f (g x) = h (f x)) :
    Motion.UpStrict (limitMotion g hg) (limitMotion h hh) f := by
  intro x
  apply Part.ext
  intro q
  show q ∈ limitRetraction h (f x) ↔ q ∈ (limitRetraction g x).map f
  rw [bend_mem_limitRetraction_of_periodic hm (hhm (f x)), Part.mem_map_iff]
  constructor
  · rintro ⟨hfix, rfl⟩
    exact ⟨x, (bend_mem_limitRetraction_of_periodic hn (hgn x)).2
      ⟨hf (by rw [hc]; exact hfix), rfl⟩, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨hfix, rfl⟩ := (bend_mem_limitRetraction_of_periodic hn (hgn x)).1 ha
    exact ⟨by rw [← hc, hfix], rfl⟩

/-- `Statement:` if `g^[n] = id` and `h^[m] = id` (`0 < n`, `0 < m`), a bijection `e` with
    `e ∘ g = h ∘ e` is a strict isomorphism of the limit motions; no continuity of `e` is used. -/
noncomputable def bendPeriodicIso {g : X → X} {h : Y → Y} (hg : Continuous g) (hh : Continuous h)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hgn : ∀ x, g^[n] x = x) (hhm : ∀ y, h^[m] y = y)
    (e : X ≃ Y) (hc : ∀ x, e (g x) = h (e x)) :
    Motion.StrictIso (limitMotion g hg) (limitMotion h hh) :=
  have hc' : ∀ y, e.symm (h y) = g (e.symm y) := fun y => by
    apply e.injective
    rw [hc, e.apply_symm_apply, e.apply_symm_apply]
  { hom := { toFun := e
             map_step := by rintro a b (rfl : b = g a); exact hc a
             map_up := bend_upStrict_of_periodic hg hh hn hm hgn hhm e e.injective hc }
    inv := { toFun := e.symm
             map_step := by rintro a b (rfl : b = h a); exact hc' a
             map_up := bend_upStrict_of_periodic hh hg hm hn hhm hgn e.symm e.symm.injective hc' }
    left_inv := e.symm_apply_apply
    right_inv := e.apply_symm_apply }

/-- `Statement:` for continuous `g`, `h` on Hausdorff spaces with `g^[n] = id`, `h^[m] = id`
    (`0 < n`, `0 < m`), the limit motions are strictly isomorphic iff some bijection `e` has
    `e ∘ g = h ∘ e`; both directions. -/
theorem bend_strictIso_iff_conj_of_periodic {g : X → X} {h : Y → Y} (hg : Continuous g)
    (hh : Continuous h) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hgn : ∀ x, g^[n] x = x)
    (hhm : ∀ y, h^[m] y = y) :
    Nonempty (Motion.StrictIso (limitMotion g hg) (limitMotion h hh)) ↔
      ∃ e : X ≃ Y, ∀ x, e (g x) = h (e x) := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨φ.toEquiv, fun x => φ.hom.map_step rfl⟩
  · rintro ⟨e, he⟩
    exact ⟨bendPeriodicIso hg hh hn hm hgn hhm e he⟩

end Periodic

/-! ### The fifth roots: rotation by `ζ` against rotation by `ζ²` -/

/-- `Statement:` `ζ = exp(2πi/5)`. -/
noncomputable def bendZeta : ℂ := Complex.exp (((2 * Real.pi / 5 : ℝ) : ℂ) * Complex.I)

/-- `Statement:` `ζ ≠ 0`. -/
theorem bendZeta_ne_zero : bendZeta ≠ 0 := Complex.exp_ne_zero _

/-- `Statement:` `ζ⁵ = 1`. -/
theorem bendZeta_pow_five : bendZeta ^ 5 = 1 := by
  rw [bendZeta, ← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast; ring

/-- `Statement:` `ζ ≠ 1` (its imaginary part is `sin (2π/5) > 0`). -/
theorem bendZeta_ne_one : bendZeta ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  rw [bendZeta, Complex.exp_ofReal_mul_I_im, Complex.one_im] at this
  exact (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne' this

/-- `Statement:` `‖ζ‖ = 1`. -/
theorem bendZeta_norm : ‖bendZeta‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- `Statement:` `ζ ^ k = exp(i · k · 2π/5)` for `k : ℤ`. -/
theorem bendZeta_zpow (k : ℤ) :
    bendZeta ^ k = Complex.exp (((k * (2 * Real.pi / 5) : ℝ) : ℂ) * Complex.I) := by
  rw [bendZeta, ← Complex.exp_int_mul]; congr 1; push_cast; ring

/-- `Statement:` `ζ ^ (a + 5 m) = ζ ^ a` for `a m : ℤ`. -/
theorem bendZeta_zpow_add_five (a m : ℤ) : bendZeta ^ (a + 5 * m) = bendZeta ^ a := by
  have h5 : bendZeta ^ (5 : ℤ) = 1 := by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast, bendZeta_pow_five]
  rw [zpow_add₀ bendZeta_ne_zero, zpow_mul, h5, one_zpow, mul_one]

/-- `Statement:` the sector index `⌊arg z · 5 / 2π⌋`. -/
noncomputable def bendSector (z : ℂ) : ℤ := ⌊Complex.arg z * 5 / (2 * Real.pi)⌋

/-- `Statement:` for `z ≠ 0` and `k : ℤ`, the sector index of `ζ^k z` is that of `z` plus `k`, mod
    `5`. -/
theorem bend_sector_shift (k : ℤ) {z : ℂ} (hz : z ≠ 0) :
    ∃ m : ℤ, bendSector (bendZeta ^ k * z) = bendSector z + k + 5 * m := by
  have hk : bendZeta ^ k ≠ 0 := zpow_ne_zero k bendZeta_ne_zero
  have hang : (Complex.arg (bendZeta ^ k * z) : Real.Angle) =
      ((k * (2 * Real.pi / 5) + Complex.arg z : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hk hz, Real.Angle.coe_add]
    congr 1
    have := bend_arg_polar one_pos (k * (2 * Real.pi / 5))
    rw [Complex.ofReal_one, one_mul] at this
    rw [bendZeta_zpow]; exact this
  obtain ⟨m, hm⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
  refine ⟨m, ?_⟩
  unfold bendSector
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have : Complex.arg (bendZeta ^ k * z) * 5 / (2 * Real.pi) =
      Complex.arg z * 5 / (2 * Real.pi) + ((k + 5 * m : ℤ) : ℝ) := by
    rw [sub_eq_iff_eq_add] at hm
    rw [hm]; push_cast; field_simp; ring
  rw [this, Int.floor_add_intCast]; ring

/-- `Statement:` the forward map `z ↦ ζ^(sector z) · z`. -/
noncomputable def bendFiveFwd (z : ℂ) : ℂ := bendZeta ^ bendSector z * z

/-- `Statement:` the backward map `y ↦ ζ^(2 · sector y) · y`. -/
noncomputable def bendFiveBwd (y : ℂ) : ℂ := bendZeta ^ (2 * bendSector y) * y

/-- `Statement:` the two maps are inverse bijections of ℂ. -/
noncomputable def bendFiveEquiv : ℂ ≃ ℂ where
  toFun := bendFiveFwd
  invFun := bendFiveBwd
  left_inv z := by
    show bendFiveBwd (bendFiveFwd z) = z
    rcases eq_or_ne z 0 with rfl | hz
    · simp [bendFiveFwd, bendFiveBwd]
    obtain ⟨m, hm⟩ := bend_sector_shift (bendSector z) hz
    unfold bendFiveBwd bendFiveFwd
    rw [hm, show 2 * (bendSector z + bendSector z + 5 * m) =
        -bendSector z + 5 * (bendSector z + 2 * m) by ring, bendZeta_zpow_add_five, ← mul_assoc,
      ← zpow_add₀ bendZeta_ne_zero, neg_add_cancel, zpow_zero, one_mul]
  right_inv y := by
    show bendFiveFwd (bendFiveBwd y) = y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [bendFiveFwd, bendFiveBwd]
    obtain ⟨m, hm⟩ := bend_sector_shift (2 * bendSector y) hy
    unfold bendFiveFwd bendFiveBwd
    rw [hm, show bendSector y + 2 * bendSector y + 5 * m =
        -(2 * bendSector y) + 5 * (bendSector y + m) by ring, bendZeta_zpow_add_five, ← mul_assoc,
      ← zpow_add₀ bendZeta_ne_zero, neg_add_cancel, zpow_zero, one_mul]

/-- `Statement:` `bendFiveFwd (ζ z) = ζ² · bendFiveFwd z`. -/
theorem bendFive_conj (z : ℂ) : bendFiveFwd (bendZeta * z) = bendZeta ^ 2 * bendFiveFwd z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [bendFiveFwd]
  obtain ⟨m, hm⟩ := bend_sector_shift 1 hz
  rw [zpow_one] at hm
  unfold bendFiveFwd
  rw [hm, bendZeta_zpow_add_five, zpow_add_one₀ bendZeta_ne_zero]
  ring

/-- `Statement:` the limit motions of rotation by `ζ` and by `ζ²` on `OnePoint ℂ` are strictly
    isomorphic, through `bendFiveEquiv` extended by `∞ ↦ ∞`. -/
noncomputable def bendFiveIso :
    Motion.StrictIso (limitMotion (lmScale bendZeta bendZeta_ne_zero) (lmScale _ _).continuous)
      (limitMotion (lmScale (bendZeta ^ 2) (pow_ne_zero 2 bendZeta_ne_zero))
        (lmScale _ _).continuous) :=
  bendPeriodicIso _ _ (n := 5) (m := 5) (by norm_num) (by norm_num)
    (fun x => by
      induction x using OnePoint.rec with
      | infty => exact Function.iterate_fixed (lm_scale_infty _ _) 5
      | coe z => rw [lm_scale_iterate_some, bendZeta_pow_five, one_mul])
    (fun x => by
      induction x using OnePoint.rec with
      | infty => exact Function.iterate_fixed (lm_scale_infty _ _) 5
      | coe z =>
        rw [lm_scale_iterate_some, ← pow_mul, show 2 * 5 = 5 * 2 from rfl, pow_mul,
          bendZeta_pow_five, one_pow, one_mul])
    (Equiv.optionCongr bendFiveEquiv : OnePoint ℂ ≃ OnePoint ℂ)
    (fun x => by
      induction x using OnePoint.rec with
      | infty => rfl
      | coe z =>
        show OnePoint.some (bendFiveFwd (bendZeta * z)) =
          OnePoint.some (bendZeta ^ 2 * bendFiveFwd z)
        rw [bendFive_conj])

/-- `Statement:` `‖ζ‖ = ‖ζ²‖ = 1`, `ζ ≠ ζ²` and `ζ ≠ conj (ζ²)`: none of the three conditions of
    Rybalkina–Sergeichuk Lemma 2.1 holds for `a = ζ`, `b = ζ²` (that lemma is cited in `BendDie.md`). -/
theorem bend_zeta_sq_conditions :
    ‖bendZeta‖ = 1 ∧ ‖bendZeta ^ 2‖ = 1 ∧ bendZeta ≠ bendZeta ^ 2 ∧
      bendZeta ≠ conj (bendZeta ^ 2) := by
  have h1 := bendZeta_ne_one
  have h0 := bendZeta_ne_zero
  refine ⟨bendZeta_norm, by rw [norm_pow, bendZeta_norm, one_pow], ?_, ?_⟩
  · intro h
    apply h1
    have : bendZeta * (bendZeta - 1) = 0 := by rw [mul_sub, mul_one, ← sq, ← h, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h0)
  · intro h
    apply h1
    have hc : conj bendZeta * bendZeta = 1 := by
      rw [Complex.conj_mul', bendZeta_norm]; simp
    have h3 : bendZeta ^ 3 = 1 := by
      calc bendZeta ^ 3 = bendZeta * bendZeta ^ 2 := by ring
        _ = conj (bendZeta ^ 2) * bendZeta ^ 2 := by rw [← h]
        _ = (conj bendZeta * bendZeta) ^ 2 := by rw [map_pow]; ring
        _ = 1 := by rw [hc, one_pow]
    have h2 : bendZeta ^ 2 = 1 := by
      have h5 := bendZeta_pow_five
      rw [show bendZeta ^ 5 = bendZeta ^ 3 * bendZeta ^ 2 by ring, h3, one_mul] at h5
      exact h5
    calc bendZeta = bendZeta * bendZeta ^ 2 := by rw [h2, mul_one]
      _ = bendZeta ^ 3 := by ring
      _ = 1 := h3

/-! ## § VII. Arc against chord: the unit circle, and the twist's step -/

section ArcChord

open Set

/-- `Statement:` the chord of the unit circle across angle `θ`, `2 sin (θ/2)`. -/
noncomputable def chord (θ : ℝ) : ℝ := 2 * Real.sin (θ / 2)

/-- `Statement:` the sum of `n` equal chords across total angle `θ`. -/
noncomputable def chordSum (n : ℕ) (θ : ℝ) : ℝ := n * chord (θ / n)

/-- `Statement:` the unit circle parametrised by angle, `t ↦ exp (i t)`. -/
noncomputable def unitCirc (t : ℝ) : ℂ := Complex.exp (Complex.I * t)

/-- `Statement:` `dist (unitCirc a) (unitCirc b) = ‖2 sin ((a - b)/2)‖`. -/
theorem dist_unitCirc (a b : ℝ) :
    dist (unitCirc a) (unitCirc b) = ‖2 * Real.sin ((a - b) / 2)‖ := by
  rw [← Complex.norm_exp_I_mul_ofReal_sub_one, dist_eq_norm]
  have : unitCirc a - unitCirc b
      = unitCirc b * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    unfold unitCirc
    rw [mul_sub, ← Complex.exp_add, mul_one]; push_cast; ring_nf
  rw [this, norm_mul]
  have h1 : ‖unitCirc b‖ = 1 := by
    unfold unitCirc; rw [Complex.norm_exp]; simp
  rw [h1, one_mul]

/-- `Statement:` for `0 ≤ θ ≤ 2π`, the chord is the distance between the arc's endpoints. -/
theorem chord_eq_dist {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 2 * Real.pi) :
    dist (unitCirc θ) (unitCirc 0) = chord θ := by
  rw [dist_unitCirc, sub_zero, Real.norm_eq_abs, chord, abs_of_nonneg]
  have := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ / 2) (by linarith) (by linarith)
  linarith

/-- `Statement:` `chord θ < θ` for every `θ > 0` (Mathlib's `Real.sin_lt`). -/
theorem chord_lt {θ : ℝ} (h : 0 < θ) : chord θ < θ := by
  unfold chord
  have := Real.sin_lt (half_pos h)
  linarith

/-- `Statement:` for `n ≥ 1` and `θ > 0`, `chordSum n θ < θ`: every finite refinement falls short. -/
theorem chordSum_lt {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (h : 0 < θ) : chordSum n θ < θ := by
  unfold chordSum
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have := chord_lt (div_pos h hn')
  calc (n : ℝ) * chord (θ / n) < n * (θ / n) := mul_lt_mul_of_pos_left this hn'
    _ = θ := by field_simp

/-- `Statement:` for `n ≥ 1` and `0 ≤ θ ≤ 4πn`, doubling the partition does not shorten the chord sum. -/
theorem chordSum_le_double {n : ℕ} (hn : 1 ≤ n) {θ : ℝ} (h0 : 0 ≤ θ)
    (hπ : θ ≤ 4 * Real.pi * n) : chordSum n θ ≤ chordSum (2 * n) θ := by
  unfold chordSum chord
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℝ := θ / (4 * n) with ha
  have e1 : θ / (n : ℝ) / 2 = 2 * a := by rw [ha]; field_simp; ring
  have e2 : θ / ((2 * n : ℕ) : ℝ) / 2 = a := by rw [ha]; push_cast; field_simp; ring
  rw [e1, e2, Real.sin_two_mul]
  have hs : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by rw [ha, div_le_iff₀ (by positivity)]; linarith)
  have hc := Real.cos_le_one a
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hc hs]

/-- `Statement:` for `θ > 0`, `chordSum n θ → θ` as `n → ∞`. -/
theorem chordSum_tendsto {θ : ℝ} (h : 0 < θ) :
    Tendsto (fun n : ℕ => chordSum n θ) atTop (𝓝 θ) := by
  have hlow : Tendsto (fun n : ℕ => θ - θ ^ 3 / 24 * ((n : ℝ)⁻¹) ^ 2) atTop (𝓝 θ) := by
    have := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul (θ ^ 3 / 24)
    simpa using (tendsto_const_nhds (x := θ)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    unfold chordSum chord
    have hx : 0 < θ / n / 2 := by positivity
    have := Real.sin_gt_sub_cube hx
    have e1 : (n : ℝ) * (2 * (θ / n / 2 - (θ / n / 2) ^ 3 / 6))
        = θ - θ ^ 3 / 24 * ((n : ℝ)⁻¹) ^ 2 := by field_simp; ring
    rw [← e1]
    exact mul_le_mul_of_nonneg_left (by linarith : 2 * (θ / n / 2 - (θ / n / 2) ^ 3 / 6)
      ≤ 2 * Real.sin (θ / n / 2)) hn'.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (chordSum_lt hn h).le

/-- `Statement:` `unitCirc` is 1-Lipschitz. -/
theorem unitCirc_lipschitz : LipschitzWith 1 unitCirc := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  rw [dist_unitCirc, NNReal.coe_one, one_mul, Real.dist_eq, Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_le_abs (x := (a - b) / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- `Statement:` for `θ > 0`, the arc length of the unit circle over `[0, θ]`, Mathlib's
    `eVariationOn` (the supremum of chord sums over partitions), is `θ`. -/
theorem arc_unitCirc {θ : ℝ} (h : 0 < θ) :
    eVariationOn unitCirc (Icc 0 θ) = ENNReal.ofReal θ := by
  apply _root_.le_antisymm
  · have := (unitCirc_lipschitz.lipschitzOnWith (s := univ)).comp_eVariationOn_le
      (g := id) (s := Icc 0 θ) (mapsTo_univ _ _)
    simpa using this
  · have hev : ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (chordSum n θ) ≤ eVariationOn unitCirc (Icc 0 θ) := by
      obtain ⟨M, hM⟩ := exists_nat_gt (θ / (2 * Real.pi))
      filter_upwards [eventually_ge_atTop (max M 1)] with n hn
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn1
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
      have hθn : θ / n ≤ 2 * Real.pi := by
        rw [div_le_iff₀ hn']
        have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).1 hM
        nlinarith [Real.pi_pos]
      let u : ℕ → ℝ := fun i => i * (θ / n)
      have hu : MonotoneOn u (Iic n) := fun i _ j _ hij => by
        simp only [u]; gcongr
      have us : ∀ i ≤ n, u i ∈ Icc 0 θ := fun i hi => by
        refine ⟨by positivity, ?_⟩
        simp only [u]
        calc (i : ℝ) * (θ / n) ≤ n * (θ / n) := by gcongr
          _ = θ := by field_simp
      have hsum := eVariationOn.sum_le_of_monotoneOn_Iic (f := unitCirc) hu us
      have hterm : ∀ i, edist (unitCirc (u (i + 1))) (unitCirc (u i))
          = ENNReal.ofReal (chord (θ / n)) := by
        intro i
        rw [edist_dist, dist_unitCirc]
        have : u (i + 1) - u i = θ / n := by simp only [u]; push_cast; ring
        rw [this, Real.norm_eq_abs, abs_of_nonneg, chord]
        have := Real.sin_nonneg_of_nonneg_of_le_pi (x := θ / n / 2) (by positivity) (by linarith)
        linarith
      simp_rw [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      unfold chordSum
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
      exact hsum
    exact le_of_tendsto ((ENNReal.continuous_ofReal.tendsto θ).comp (chordSum_tendsto h)) hev

/-- `Statement:` the distance from `z` to `bendTwist α z` is `‖z‖ · ‖2 sin (α log ‖z‖ / 2)‖`. -/
theorem dist_bendTwist (α : ℝ) (z : ℂ) :
    dist z (bendTwist α z) = ‖z‖ * ‖2 * Real.sin ((α * Real.log ‖z‖) / 2)‖ := by
  unfold bendTwist
  rw [dist_eq_norm]
  have : z - z * Complex.exp (((α * Real.log ‖z‖ : ℝ) : ℂ) * Complex.I)
      = -z * (Complex.exp (Complex.I * ((α * Real.log ‖z‖ : ℝ) : ℂ)) - 1) := by ring_nf
  rw [this, norm_mul, norm_neg, Complex.norm_exp_I_mul_ofReal_sub_one]

/-- `Statement:` for `z ≠ 0` and twist angle `α log ‖z‖ ≠ 0`, the chord from `z` to `bendTwist α z` is
    shorter than `‖z‖ · |α log ‖z‖|`, the arc of the circle of radius `‖z‖` at that angle. Arc as a
    LENGTH (`eVariationOn`) is proved only on the unit circle (`arc_unitCirc`). -/
theorem bendTwist_chord_lt_arc {α : ℝ} {z : ℂ} (hz : z ≠ 0)
    (hθ : α * Real.log ‖z‖ ≠ 0) :
    dist z (bendTwist α z) < ‖z‖ * |α * Real.log ‖z‖| := by
  rw [dist_bendTwist]
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  apply mul_lt_mul_of_pos_left _ hz'
  rw [Real.norm_eq_abs, abs_mul, abs_two]
  have := Real.abs_sin_lt_abs (x := α * Real.log ‖z‖ / 2) (div_ne_zero hθ two_ne_zero)
  rw [abs_div, abs_two] at this
  linarith

-- Statement: CONTROL, zero twist moves no point: chord 0.
example (z : ℂ) : dist z (bendTwist 0 z) = 0 := by rw [dist_bendTwist]; simp

end ArcChord

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms bend_proj_eq_self_iff
#print axioms bend_e0_norm
#print axioms bend_AD_iff
#print axioms bend_AD_obstructed_iff
#print axioms bend_inner_e0_e0
#print axioms bend_antiparallel
#print axioms bend_phase
#print axioms bend_overlap_one
#print axioms bend_no_separation
#print axioms bend_tendsto_zero
#print axioms bend_tendsto_infty
#print axioms bend_closure_infty
#print axioms bend_closure_zero
#print axioms bend_iterate_polar
#print axioms bend_arg_iterate
#print axioms bend_arg_polar
#print axioms bend_inv_polar
#print axioms bend_inv_angle
#print axioms bendTwist
#print axioms bendTwist_norm
#print axioms bendTwist_neg_left
#print axioms bendTwist_continuous
#print axioms bendTwistHomeo
#print axioms bendTwist_conj
#print axioms bendIso
#print axioms bend_iso_abs
#print axioms bendRadial
#print axioms bendRadial_norm
#print axioms bendRadial_inv
#print axioms bendRadial_continuous
#print axioms bendRadialHomeo
#print axioms bendRadial_conj
#print axioms bend_twist_conj_of_norm_eq
#print axioms bend_conj_same_side
#print axioms bend_onePointCongr_conj
#print axioms bend_conj_of_norm_ne_one
#print axioms bend_iso_of_norm_ne_one
#print axioms bend_conj_conj
#print axioms bendConjIso
#print axioms bend_iso_I_negI
#print axioms bend_rotation_no_limit
#print axioms bend_rotation_ne_identity
#print axioms bend_halfturn_ne_quarterturn
#print axioms bend_mem_limitRetraction_of_periodic
#print axioms bend_upStrict_of_periodic
#print axioms bendPeriodicIso
#print axioms bend_strictIso_iff_conj_of_periodic
#print axioms bendZeta
#print axioms bendZeta_ne_zero
#print axioms bendZeta_pow_five
#print axioms bendZeta_ne_one
#print axioms bendZeta_norm
#print axioms bendZeta_zpow
#print axioms bendZeta_zpow_add_five
#print axioms bendSector
#print axioms bend_sector_shift
#print axioms bendFiveFwd
#print axioms bendFiveBwd
#print axioms bendFiveEquiv
#print axioms bendFive_conj
#print axioms bendFiveIso
#print axioms bend_zeta_sq_conditions
#print axioms chord
#print axioms chordSum
#print axioms unitCirc
#print axioms dist_unitCirc
#print axioms chord_eq_dist
#print axioms chord_lt
#print axioms chordSum_lt
#print axioms chordSum_le_double
#print axioms chordSum_tendsto
#print axioms unitCirc_lipschitz
#print axioms arc_unitCirc
#print axioms dist_bendTwist
#print axioms bendTwist_chord_lt_arc
end PurityCheck
