-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): on ℤ_p, every additive character integrates over the closed ball of radius p^(-j) about 0 to p^(-j) if it is 1 on that ball and to 0 otherwise; for paChar n φ, and for every continuous character (each is some paChar), that condition is level ≤ j. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicStillPoint
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# On ℤ_p, an additive character integrates over the closed ball of radius p^(-j) about 0 to p^(-j) if it is 1 on that ball and to 0 otherwise; for paChar n φ, and for every continuous character, that is exactly when the character's level is at most j

## Engineer's Take

It's a question of mutual exclusivity, where one value can't even theoretically be known without the
other at the same time. I honestly think the structure we're building here feels like it's both a thing
and a motion, which sounds a whole lot like both a particle and a wave. I know we've had other physics
related stuff, and these parallels are a little spooky.

---

## Formal Overview (AI-assisted)
`Statement:` DRIFT, on Haar `ℤ_p` the transform of the ball of radius `p^(-j)` is `p^(-j)` times the
indicator of the dual ball `{level ≤ j}` (`paChar_ball_integral_level`,
`continuous_addChar_ball_integral_level`): as `j` grows the volume falls and the dual ball grows.
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-- `Statement:` `paChar n φ z = 1` whenever `‖z‖ ≤ p^(-n)`, for every `φ`. -/
theorem paChar_eq_one_of_norm_le (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) {z : ℤ_[p]}
    (hz : ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))) : paChar (p := p) n φ z = 1 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have h0 : (p : ZMod (p ^ n)) ^ n = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  have hz0 : PadicInt.toZModPow n z = 0 := by
    have := (norm_le_iff_dvd_toZModPow n n le_rfl z).mp hz
    rwa [h0, zero_dvd_iff] at this
  simp [paChar, hz0]

/-- `Statement:` for `n ≤ j` and every `φ`, `∫` over `{‖z‖ ≤ p^(-j)}` of `paChar n φ` is `p^(-j)`. -/
theorem paChar_ball_integral_of_le (n j : ℕ) (hnj : n ≤ j) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p)) = ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) := by
  have hval : Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ)
      = Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      refine paChar_eq_one_of_norm_le n φ (le_trans hx (zpow_le_zpow_right₀ ?_ ?_))
      · exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
      · omega
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [hval, integral_indicator_const _ (ball_measurableSet j), measureReal_def, haarZp_ball,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  show (((p : ℝ) ^ j)⁻¹ : ℝ) • (1 : ℂ) = ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ)
  rw [Complex.real_smul, mul_one]

/-! ### Every additive character: no continuity, no primitivity -/

open Classical in
/-- `Statement:` for a left-invariant `μ` on an additive commutative group, a measurable subgroup `H`
and `χ : AddChar G ℂ`, `∫` over `H` of `χ` is `μ.real H` if `χ = 1` on `H`, else `0`. Closest Lean
prior art: `QuadFormsKB.Analysis.setIntegral_addChar_addSubgroup` (jonhanke/quadratic-forms-lean,
`QuadFormsKB/Analysis/LocalFourier.lean`, commit 43bd018), for `Circle`-valued characters; in the
literature, Rajkumar–Weisbart, arXiv:2509.24234, Lemma 2.1. -/
theorem addChar_addSubgroup_integral {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant] (H : AddSubgroup G)
    (hH : MeasurableSet (H : Set G)) (χ : AddChar G ℂ) :
    ∫ x, Set.indicator (H : Set G) χ x ∂μ
      = if (∀ h ∈ H, χ h = 1) then ((μ.real (H : Set G) : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · have hval : Set.indicator (H : Set G) χ = Set.indicator (H : Set G) (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (H : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, h x hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    rw [hval, integral_indicator_const _ hH, Complex.real_smul, mul_one]
  · push Not at h
    obtain ⟨y, hy, hχy⟩ := h
    set f := Set.indicator (H : Set G) χ with hf
    have hshift : ∀ x, f (y + x) = χ y * f x := by
      intro x
      by_cases hx : x ∈ (H : Set G)
      · have hyx : y + x ∈ (H : Set G) := H.add_mem hy hx
        rw [hf, Set.indicator_of_mem hyx, Set.indicator_of_mem hx, AddChar.map_add_eq_mul]
      · have hyx : y + x ∉ (H : Set G) := fun h' => hx ((H.add_mem_cancel_left hy).mp h')
        rw [hf, Set.indicator_of_notMem hyx, Set.indicator_of_notMem hx, mul_zero]
    have key : ∫ x, f x ∂μ = χ y * ∫ x, f x ∂μ := by
      calc ∫ x, f x ∂μ
          = ∫ x, f (y + x) ∂μ := (integral_add_left_eq_self f y).symm
        _ = ∫ x, χ y * f x ∂μ := integral_congr_ae (Filter.Eventually.of_forall hshift)
        _ = χ y * ∫ x, f x ∂μ := integral_const_mul _ _
    have hz : (1 - χ y) * ∫ x, f x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm hχy))

/-- `Statement:` `‖z‖ ≤ p^(-j)` in `ℤ_p` iff `p^j ∣ z`. -/
theorem norm_le_zpow_neg_iff_dvd (j : ℕ) (z : ℤ_[p]) :
    ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) ↔ (p : ℤ_[p]) ^ j ∣ z := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

open Classical in
/-- `Statement:` every `χ : AddChar ℤ_[p] ℂ` integrates over `{‖z‖ ≤ p^(-j)}` to `p^(-j)` if `χ = 1`
there, else to `0`; the ball case of `addChar_addSubgroup_integral`. -/
theorem addChar_ball_integral (χ : AddChar ℤ_[p] ℂ) (j : ℕ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} χ x ∂(haarZp (p := p))
      = if (∀ z : ℤ_[p], ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) → χ z = 1)
          then ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) else 0 := by
  set H : AddSubgroup ℤ_[p] := (Ideal.span {(p : ℤ_[p]) ^ j}).toAddSubgroup with hHdef
  have hset : (H : Set ℤ_[p]) = {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} := by
    ext x
    rw [Set.mem_ofPred_eq, PadicInt.norm_le_pow_iff_mem_span_pow, hHdef]
    simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup]
  have hmeas : MeasurableSet (H : Set ℤ_[p]) := by rw [hset]; exact ball_measurableSet j
  have hreal : (haarZp (p := p)).real (H : Set ℤ_[p]) = ((p : ℝ) ^ j)⁻¹ := by
    rw [hset, measureReal_def, haarZp_ball, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_natCast]
  have h := addChar_addSubgroup_integral (haarZp (p := p)) H hmeas χ
  rw [hreal, hset] at h
  rw [h]
  refine if_congr ?_ rfl rfl
  constructor
  · intro h' z hz
    exact h' z (by rw [← SetLike.mem_coe, hset]; exact hz)
  · intro h' z hz
    rw [← SetLike.mem_coe, hset] at hz
    exact h' z hz

/-! ### The `paChar` family and its level -/

/-- `Statement:` `paChar n φ`, bundled as an additive character of `ℤ_p`. -/
noncomputable def paCharHom (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) : AddChar ℤ_[p] ℂ :=
  φ.compAddMonoidHom (PadicInt.toZModPow (p := p) n).toAddMonoidHom

/-- `Statement:` the function underlying `paCharHom n φ` is `paChar n φ`, by `rfl`. -/
theorem coe_paCharHom (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ⇑(paCharHom (p := p) n φ) = paChar (p := p) n φ := rfl

/-- `Statement:` `paChar n φ = 1` on `{‖z‖ ≤ p^(-j)}` iff `φ = 1` on `p^j · ZMod (p^n)`. -/
theorem paChar_trivial_on_ball_iff (n j : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    (∀ z : ℤ_[p], ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) → paChar (p := p) n φ z = 1)
      ↔ ∀ r : ZMod (p ^ n), φ ((p : ZMod (p ^ n)) ^ j * r) = 1 := by
  constructor
  · intro h r
    obtain ⟨w, hw⟩ := toZModPow_surjective (p := p) n r
    have hz : ‖(p : ℤ_[p]) ^ j * w‖ ≤ (p : ℝ) ^ (-(j : ℤ)) :=
      (norm_le_zpow_neg_iff_dvd j _).mpr (dvd_mul_right _ _)
    have := h _ hz
    simpa [paChar, map_mul, map_pow, map_natCast, hw] using this
  · intro h z hz
    obtain ⟨w, rfl⟩ := (norm_le_zpow_neg_iff_dvd j z).mp hz
    have := h (PadicInt.toZModPow n w)
    simpa [paChar, map_mul, map_pow, map_natCast] using this

open Classical in
/-- `Statement:` every `paChar n φ` integrates over `{‖z‖ ≤ p^(-j)}` to `p^(-j)` if `φ = 1` on
`p^j · ZMod (p^n)`, else to `0`. -/
theorem paChar_ball_integral (n j : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p))
      = if (∀ r : ZMod (p ^ n), φ ((p : ZMod (p ^ n)) ^ j * r) = 1)
          then ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) else 0 := by
  have h := addChar_ball_integral (paCharHom (p := p) n φ) j
  rw [coe_paCharHom] at h
  rw [h]
  exact if_congr (paChar_trivial_on_ball_iff n j φ) rfl rfl

omit [Fact p.Prime] in
/-- `Statement:` every `φ` is `1` on `p^n · ZMod (p^n)`. -/
theorem addChar_zmodPow_trivial_self (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ∀ r : ZMod (p ^ n), φ ((p : ZMod (p ^ n)) ^ n * r) = 1 := by
  intro r
  have h0 : (p : ZMod (p ^ n)) ^ n = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  rw [h0, zero_mul, AddChar.map_zero_eq_one]

open Classical in
/-- `Statement:` the level of `φ`: the least `m` with `φ = 1` on `p^m · ZMod (p^n)`. -/
noncomputable def charLevel (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) : ℕ :=
  Nat.find (⟨n, addChar_zmodPow_trivial_self n φ⟩ :
    ∃ m : ℕ, ∀ r : ZMod (p ^ n), φ ((p : ZMod (p ^ n)) ^ m * r) = 1)

/-- `Statement:` `charLevel n φ ≤ j` iff `φ = 1` on `p^j · ZMod (p^n)`. -/
theorem charLevel_le_iff (n j : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    charLevel (p := p) n φ ≤ j ↔ ∀ r : ZMod (p ^ n), φ ((p : ZMod (p ^ n)) ^ j * r) = 1 := by
  classical
  unfold charLevel
  rw [Nat.find_le_iff]
  constructor
  · rintro ⟨m, hm, h⟩ r
    have e : (p : ZMod (p ^ n)) ^ j * r
        = (p : ZMod (p ^ n)) ^ m * ((p : ZMod (p ^ n)) ^ (j - m) * r) := by
      rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hm]
    rw [e]; exact h _
  · intro h; exact ⟨j, le_rfl, h⟩

/-- `Statement:` `charLevel n φ ≤ n`. -/
theorem charLevel_le (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) : charLevel (p := p) n φ ≤ n :=
  (charLevel_le_iff n n φ).mpr (addChar_zmodPow_trivial_self n φ)

/-- `Statement:` every `paChar n φ` integrates over `{‖z‖ ≤ p^(-j)}` to `p^(-j)` if
`charLevel n φ ≤ j`, else to `0`. -/
theorem paChar_ball_integral_level (n j : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p))
      = if charLevel (p := p) n φ ≤ j then ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) else 0 := by
  rw [paChar_ball_integral]
  exact if_congr (charLevel_le_iff n j φ).symm rfl rfl

/-- `Statement:` a primitive `φ` has `charLevel n φ = n`. -/
theorem charLevel_of_isPrimitive (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive) :
    charLevel (p := p) n φ = n := by
  refine le_antisymm (charLevel_le n φ) ?_
  by_contra hlt
  push Not at hlt
  set m := charLevel (p := p) n φ with hm
  have htriv := (charLevel_le_iff (p := p) n m φ).mp le_rfl
  have hpm : (p : ZMod (p ^ n)) ^ m ≠ 0 := by
    have : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
    rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h1 : p ^ n ≤ p ^ m := Nat.le_of_dvd (pow_pos ‹Fact p.Prime›.out.pos m) hdvd
    have h2 : n ≤ m := (Nat.pow_le_pow_iff_right ‹Fact p.Prime›.out.one_lt).mp h1
    omega
  apply hφ hpm
  ext r
  rw [AddChar.mulShift_apply, AddChar.one_apply]
  exact htriv r

/-- `Statement:` for primitive `φ`, `∫` over `{‖z‖ ≤ p^(-j)}` of `paChar n φ` is `p^(-j)` if
`n ≤ j` and `0` otherwise; `paChar_ball_integral_level` at `charLevel_of_isPrimitive`. -/
theorem paChar_ball_integral_tradeoff (n j : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ)
    (hφ : φ.IsPrimitive) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p)) = if n ≤ j then ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) else 0 := by
  rw [paChar_ball_integral_level, charLevel_of_isPrimitive n φ hφ]

-- Reading: over ℚ_p this is the standard ball transform F[Ω(p^(-k)|·|_p)](ξ) = p^k Ω(p^k|ξ|_p)
-- (Vladimirov–Volovich–Zelenov, p-adic Analysis and Mathematical Physics, IV (3.1), as quoted in
-- Khrennikov–Shelkovich, arXiv:0808.3338, eq. (2.9)); a Lean ℚ_p form is
-- `QuadFormsKB.Analysis.fourierP_ballInd` (jonhanke/quadratic-forms-lean, commit 43bd018).

/-- `Statement:` at every level `n`, the trivial character `paChar n 0` integrates to `1` over
`{‖z‖ ≤ p^0}`, which is all of `ℤ_p`. -/
theorem paChar_trivial_ball_zero (n : ℕ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} (paChar (p := p) n 0) x
      ∂(haarZp (p := p)) = 1 := by
  rw [paChar_trivial, integral_indicator_const _ (ball_measurableSet 0), measureReal_def,
    haarZp_ball]
  simp

/-! ### Continuous characters: each is trivial on some ball, and is a `paChar` -/

-- Reading: continuity enters only at `continuous_addChar_trivial_on_ball`; the later declarations
-- use `hχ` only through it. No discontinuous control is built here.

/-- `Statement:` if `‖w ^ n - 1‖ < 1/2` and `‖w⁻¹ ^ n - 1‖ < 1/2` for every `n`, then `w = 1`; the
circle step is Mathlib's `Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two`. -/
theorem eq_one_of_pow_near_one {w : ℂ} (h : ∀ n : ℕ, ‖w ^ n - 1‖ < 1 / 2)
    (h' : ∀ n : ℕ, ‖w⁻¹ ^ n - 1‖ < 1 / 2) : w = 1 := by
  have hbound : ∀ u : ℂ, (∀ n : ℕ, ‖u ^ n - 1‖ < 1 / 2) → ‖u‖ ≤ 1 := by
    intro u hu
    by_contra hgt
    push Not at hgt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / 2 : ℝ) hgt
    have h1 : ‖u ^ n‖ ≤ ‖u ^ n - 1‖ + ‖(1 : ℂ)‖ := by
      have := norm_add_le (u ^ n - 1) 1; rwa [sub_add_cancel] at this
    rw [norm_pow, norm_one] at h1
    linarith [hu n]
  have hw0 : w ≠ 0 := by
    intro hw; have := h 1; rw [hw, pow_one, zero_sub, norm_neg, norm_one] at this; norm_num at this
  have hle := hbound w h
  have hle' := hbound w⁻¹ h'
  rw [norm_inv] at hle'
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hge : 1 ≤ ‖w‖ := by
    by_contra hlt; push Not at hlt
    have : 1 < ‖w‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hpos, hlt⟩
    linarith
  have hnorm : ‖w‖ = 1 := le_antisymm hle hge
  let c : Circle := ⟨w, by simp [Submonoid.unitSphere, hnorm]⟩
  have hc : (c : ℂ) = w := rfl
  have : c = 1 := by
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two (fun n _ => ?_)
    rw [Circle.mem_centeredArc (by linarith [Real.pi_pos]), Circle.coe_pow, hc,
      Complex.abs_arg_lt_pi_div_two_iff]
    left
    have hre := Complex.abs_re_le_norm (w ^ n - 1)
    rw [Complex.sub_re, Complex.one_re] at hre
    have := h n
    have := (abs_le.mp hre).1
    linarith
  rw [← hc, this, Circle.coe_one]

/-- `Statement:` a continuous `χ : AddChar ℤ_[p] ℂ` is `1` on `{‖z‖ ≤ p^(-j)}` for some `j`. -/
theorem continuous_addChar_trivial_on_ball (χ : AddChar ℤ_[p] ℂ) (hχ : Continuous χ) :
    ∃ j : ℕ, ∀ z : ℤ_[p], ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) → χ z = 1 := by
  have hc := hχ.continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc (1 / 2) (by norm_num)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast ‹Fact p.Prime›.out.one_lt
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hδ (inv_lt_one_of_one_lt₀ hp1)
  have hjδ : (p : ℝ) ^ (-(j : ℤ)) < δ := by rwa [zpow_neg, zpow_natCast, ← inv_pow]
  refine ⟨j, fun z hz => ?_⟩
  have near : ∀ u : ℤ_[p], ‖u‖ ≤ (p : ℝ) ^ (-(j : ℤ)) → ∀ n : ℕ, ‖χ u ^ n - 1‖ < 1 / 2 := by
    intro u hu n
    have hnu : ‖n • u‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
      rw [norm_le_zpow_neg_iff_dvd] at hu ⊢
      rw [nsmul_eq_mul]; exact dvd_mul_of_dvd_right hu _
    have := hδ' (x := n • u) (by rw [dist_zero_right]; exact lt_of_le_of_lt hnu hjδ)
    rwa [AddChar.map_nsmul_eq_pow, AddChar.map_zero_eq_one, dist_eq_norm] at this
  have hneg : ‖-z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by rw [norm_neg]; exact hz
  refine eq_one_of_pow_near_one (near z hz) ?_
  intro n
  rw [← AddChar.map_neg_eq_inv]
  exact near (-z) hneg n

open Classical in
/-- `Statement:` the level of a continuous `χ`: the least `j` with `χ = 1` on `{‖z‖ ≤ p^(-j)}`. -/
noncomputable def contLevel (χ : AddChar ℤ_[p] ℂ) (hχ : Continuous χ) : ℕ :=
  Nat.find (continuous_addChar_trivial_on_ball χ hχ)

/-- `Statement:` if `χ = 1` on `{‖z‖ ≤ p^(-m)}` and `m ≤ j`, then `χ = 1` on `{‖z‖ ≤ p^(-j)}`. -/
theorem addChar_trivial_on_ball_mono (χ : AddChar ℤ_[p] ℂ) {m j : ℕ} (hmj : m ≤ j)
    (h : ∀ z : ℤ_[p], ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ)) → χ z = 1) :
    ∀ z : ℤ_[p], ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) → χ z = 1 := by
  intro z hz
  apply h
  rw [norm_le_zpow_neg_iff_dvd] at hz ⊢
  exact (pow_dvd_pow _ hmj).trans hz

/-- `Statement:` a continuous `χ` integrates over `{‖z‖ ≤ p^(-j)}` to `p^(-j)` if
`contLevel χ hχ ≤ j`, else to `0`. -/
theorem continuous_addChar_ball_integral_level (χ : AddChar ℤ_[p] ℂ) (hχ : Continuous χ)
    (j : ℕ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} χ x ∂(haarZp (p := p))
      = if contLevel χ hχ ≤ j then ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) else 0 := by
  classical
  rw [addChar_ball_integral]
  refine if_congr ?_ rfl rfl
  unfold contLevel
  rw [Nat.find_le_iff]
  constructor
  · intro h; exact ⟨j, le_rfl, h⟩
  · rintro ⟨m, hm, h⟩; exact addChar_trivial_on_ball_mono χ hm h

/-- `Statement:` every continuous `χ : AddChar ℤ_[p] ℂ` is `paChar j φ` for some `j` and `φ`. -/
theorem continuous_addChar_eq_paChar (χ : AddChar ℤ_[p] ℂ) (hχ : Continuous χ) :
    ∃ (j : ℕ) (φ : AddChar (ZMod (p ^ j)) ℂ), ⇑χ = paChar (p := p) j φ := by
  obtain ⟨j, hj⟩ := continuous_addChar_trivial_on_ball χ hχ
  have : NeZero (p ^ j) := ⟨pow_ne_zero j ‹Fact p.Prime›.out.pos.ne'⟩
  have hfib : ∀ x y : ℤ_[p], PadicInt.toZModPow j x = PadicInt.toZModPow j y → χ x = χ y := by
    intro x y hxy
    have hmem : ‖x - y‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
      rw [norm_le_zpow_neg_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow,
        RingHom.mem_ker, map_sub, hxy, sub_self]
    have := hj _ hmem
    calc χ x = χ (y + (x - y)) := by rw [add_sub_cancel]
      _ = χ y := by rw [AddChar.map_add_eq_mul, this, mul_one]
  let lift : ZMod (p ^ j) → ℤ_[p] := fun r => (r.val : ℤ_[p])
  have hlift : ∀ r, PadicInt.toZModPow j (lift r) = r := fun r => by
    simp only [lift, map_natCast]; exact ZMod.natCast_zmod_val r
  let φ : AddChar (ZMod (p ^ j)) ℂ :=
    { toFun := fun r => χ (lift r)
      map_zero_eq_one' := by
        show χ (lift 0) = 1
        rw [hfib (lift 0) 0 (by rw [hlift, map_zero]), AddChar.map_zero_eq_one]
      map_add_eq_mul' := by
        intro a b
        show χ (lift (a + b)) = χ (lift a) * χ (lift b)
        rw [← AddChar.map_add_eq_mul]
        exact hfib _ _ (by rw [hlift, map_add, hlift, hlift]) }
  refine ⟨j, φ, funext fun x => ?_⟩
  show χ x = χ (lift (PadicInt.toZModPow j x))
  exact hfib _ _ (by rw [hlift])

/-! ### Controls -/

-- Statement: CONTROL, primitivity is load-bearing in `paChar_ball_integral_tradeoff`: for `n ≥ 1`,
-- `φ = 0` with `j = 0 < n` integrates to `1 ≠ 0`.
example (n : ℕ) (hn : 1 ≤ n) :
    (0 : ℕ) < n ∧
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} (paChar (p := p) n 0) x
      ∂(haarZp (p := p)) ≠ 0 := by
  refine ⟨by omega, ?_⟩
  rw [paChar_trivial_ball_zero]; exact one_ne_zero

-- Statement: and for `n ≥ 1`, `φ = 0` is not primitive, so the control sits outside that hypothesis.
example (n : ℕ) (hn : 1 ≤ n) : ¬ (0 : AddChar (ZMod (p ^ n)) ℂ).IsPrimitive := by
  intro h
  have : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have h1 : (1 : ZMod (p ^ n)) ≠ 0 := by
    have : Fact (1 < p ^ n) := ⟨Nat.one_lt_pow (by omega) ‹Fact p.Prime›.out.one_lt⟩
    exact one_ne_zero
  have := h h1
  apply this
  ext x
  simp

-- Statement: CONTROL, the `then` branch of `addChar_ball_integral` is reached at every `j`: the
-- trivial character of `ℤ_p` integrates to `p^(-j)`.
example (j : ℕ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (⇑(0 : AddChar ℤ_[p] ℂ)) x
      ∂(haarZp (p := p)) = ((((p : ℝ) ^ j)⁻¹ : ℝ) : ℂ) := by
  rw [addChar_ball_integral, if_pos]
  intro z _; rfl

-- Statement: CONTROL, the `else` branch is reached: `paCharHom 1 (ZMod.stdAddChar)`, primitive at
-- level 1, integrates to `0` over `{‖z‖ ≤ p^0}`.
example :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))}
      (⇑(paCharHom (p := p) 1 (ZMod.stdAddChar (N := p ^ 1)))) x ∂(haarZp (p := p)) = 0 := by
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 ‹Fact p.Prime›.out.pos.ne'⟩
  rw [addChar_ball_integral, if_neg]
  intro h
  rw [coe_paCharHom, paChar_trivial_on_ball_iff, ← charLevel_le_iff,
    charLevel_of_isPrimitive 1 _ (ZMod.isPrimitive_stdAddChar _)] at h
  omega

-- Statement: CONTROL, the level is not always `n`: for `n ≥ 1`, the non-primitive `φ = 0` has
-- `charLevel n 0 = 0 ≠ n`.
example (n : ℕ) (hn : 1 ≤ n) : charLevel (p := p) n 0 = 0 ∧ charLevel (p := p) n 0 ≠ n := by
  have h0 : charLevel (p := p) n 0 = 0 :=
    Nat.le_zero.mp ((charLevel_le_iff n 0 0).mpr (fun _ => rfl))
  exact ⟨h0, by omega⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_eq_one_of_norm_le
#print axioms paChar_ball_integral_of_le
#print axioms addChar_addSubgroup_integral
#print axioms norm_le_zpow_neg_iff_dvd
#print axioms addChar_ball_integral
#print axioms paCharHom
#print axioms coe_paCharHom
#print axioms paChar_trivial_on_ball_iff
#print axioms paChar_ball_integral
#print axioms addChar_zmodPow_trivial_self
#print axioms charLevel
#print axioms charLevel_le_iff
#print axioms charLevel_le
#print axioms paChar_ball_integral_level
#print axioms charLevel_of_isPrimitive
#print axioms paChar_ball_integral_tradeoff
#print axioms paChar_trivial_ball_zero
#print axioms eq_one_of_pow_near_one
#print axioms continuous_addChar_trivial_on_ball
#print axioms contLevel
#print axioms addChar_trivial_on_ball_mono
#print axioms continuous_addChar_ball_integral_level
#print axioms continuous_addChar_eq_paChar
end PurityCheck
