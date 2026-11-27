import ZeroParadox.Multihomed.LimitMotion
import ZeroParadox.Multihomed.TH3Die
import ZeroParadox.Order.UpAndOver
import ZeroParadox.Order.Snap
import ZeroParadox.Valuation.PolePassage
import ZeroParadox.Valuation.PlaceMetric
import ZeroParadox.Information.CrossingTrials
import ZeroParadox.Information.PoleWithinEnsemble
import ZeroParadox.Information.TwoRequirements
import ZeroParadox.Information.MaxEntropy
import ZeroParadox.Information.BottomTotality
import ZeroParadox.Information.Surprisal
import ZeroParadox.Information.Dial

/-!
# The givens at the die level: each a `Prop` (all but `GConnected`, `GJoined` on a die `Motion`), proved or refuted per chart

## Engineer's Take

I think these are all the assumptions that we make... That the bottom is infinitely complex and
minimally complex at the same time.. and that it's concurrently both discrete and continuous? And
that when discrete, aka "outside the magnet/weaker state" that breaking away and returning to zero
the long way around through Infinity moving up... Happens

... we represented the continuous motion as going through the core of the magnet as opposed to
traversing the field lines on the outside where the outside lines have longer physical distance to
go but that longer distance is still a fixed amount.. hence the shattering into fixed discrete
steps..

... Ax-b1 seems opposing because that's the chart we're evaluating in..

... it's a new route to zero, although the actual ends of the poll itself zero and infinity are
still "what they are".. each one of those field lines that I'm visualizing is unique in nature

... It feels like these givens should be representable at the die level of abstraction.

---

Every given is a `Prop`, never a class field. All but `GConnected` and `GJoined` take a die `Motion`
(`ZeroParadox/Die.lean`); those two take two points of a topological space. § 0 the
charts; § I the givens; § II per chart, with controls; § III the field lines; § IV given these,
then; § V the limits; § VI the preconditions that stay hypotheses. Long form: `ZeroParadox/Givens.md`.
-/

set_option maxHeartbeats 400000

open Filter Topology OnePoint

namespace ZeroParadox

open ZPSemilattice

/-! ## § 0. The charts: four limit motions (`ZeroParadox/Multihomed/LimitMotion.lean`) -/

/-- `Statement:` doubling on the 2-adic sphere `OnePoint ℚ_[2]`, as a limit motion. -/
noncomputable abbrev dblQ2 : Motion Sphere :=
  limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale (2 : ℚ_[2]) two_ne_zero).continuous
/-- `Statement:` halving on `OnePoint ℚ_[2]`, as a limit motion. -/
noncomputable abbrev hlvQ2 : Motion Sphere :=
  limitMotion (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))
    (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero)).continuous
/-- `Statement:` doubling on the real projective line `OnePoint ℝ`, as a limit motion. -/
noncomputable abbrev dblReal : Motion (OnePoint ℝ) :=
  limitMotion (lmScale (2 : ℝ) two_ne_zero) (lmScale (2 : ℝ) two_ne_zero).continuous
/-- `Statement:` halving on `OnePoint ℝ`, as a limit motion. -/
noncomputable abbrev hlvReal : Motion (OnePoint ℝ) :=
  limitMotion (lmScale (2⁻¹ : ℝ) (inv_ne_zero two_ne_zero))
    (lmScale (2⁻¹ : ℝ) (inv_ne_zero two_ne_zero)).continuous

/-- `Statement:` the extended absolute value on `OnePoint ℝ`, `⊤` at `∞`; the real analogue of `sNorm`. -/
noncomputable def realSphNorm : OnePoint ℝ → ENNReal
  | (∞ : OnePoint ℝ) => ⊤
  | OnePoint.some x => (‖x‖₊ : ENNReal)

/-- `Statement:` the preorder on `OnePoint ℝ` lifted along `realSphNorm` (analogue of `lmSphN`). -/
noncomputable abbrev lmRealN : Preorder (OnePoint ℝ) := Preorder.lift realSphNorm

/-! ## § I. The givens, as predicates (never class fields)

Tim's three: (a) minimally and maximally complex at once: `GMinMax`, `GCoincidence`; (b) the
0-to-infinity run discrete and continuous: `GDiscrete`, `GCoverAtLanding`, `GConnected`, `GJoined`,
`GTwoCharts`; (c) breaking away and returning to zero the long way round: `GLeavesByRun`,
`GClimbNotLoop`, `GReturnToStart`. -/

section Givens
variable {α β : Type*}

/-- `Statement:` given (b), discrete face (AX-B1 along the run): some step moves, and every moving
step is a cover, one way or the other, in the view order `P`. A property of the pair `(M, P)`: real
doubling fails it in `lmRealN` and meets it in the order lifted from `realExpView` (§ II-1). -/
def GDiscrete (M : Motion α) (P : Preorder α) : Prop :=
  (∃ a b, M.step a b ∧ a ≠ b) ∧
    ∀ a b, M.step a b → a ≠ b → (@CovBy α P.toLT a b ∨ @CovBy α P.toLT b a)

/-- `Statement:` given (b), discrete face at a landing: some landing steps to a cover of it. -/
def GCoverAtLanding (M : Motion α) (P : Preorder α) : Prop :=
  ∃ y b, M.IsLanding y ∧ M.step y b ∧ @CovBy α P.toLT y b

/-- `Statement:` given (b), continuous face, component form: `q` is in `p`'s connected component. -/
def GConnected [TopologicalSpace α] (p q : α) : Prop := q ∈ connectedComponent p

/-- `Statement:` given (b), continuous face, path form: `th3PathMotion` steps from `p` to `q`. -/
def GJoined [TopologicalSpace α] (p q : α) : Prop := (th3PathMotion α).step p q

/-- `Statement:` given (a): `p` steps only to itself and is the limit sink off `q`. -/
def GMinMax (M : Motion α) (p q : α) : Prop := M.SelfOnlyAt p ∧ lmSinkOf M p q

/-- `Statement:` given (c), the climb: the corner fires as a climb, never as a loop. -/
def GClimbNotLoop (M : Motion α) : Prop := M.Climb ∧ ¬ M.Loop

/-- `Statement:` given (c), the return to a fixed destination: the tail of `s` is a run whose stage
closure contains `s 0`. The first step `s 0 → s 1` is NOT asked to be a step of `M`. -/
def GReturnToStart (M : Motion α) (s : ℕ → α) : Prop :=
  ∃ c, M.RunClosure (fun n => s (n + 1)) c ∧ s 0 ∈ c

/-- `Statement:` given (c), breaking away: some run of `M` starts at `y` and leaves it at once. -/
def GLeavesByRun (M : Motion α) (y : α) : Prop := ∃ s : ℕ → α, M.IsRun s ∧ s 0 = y ∧ s 1 ≠ y

/-- `Statement:` given (a), coincidence face (ruling 74): a strict map of motions sends `y`, least
in the source view and stepping only to itself, to a point greatest in the target view and stepping
only to itself, and sends no other point there. -/
def GCoincidence (M : Motion α) (N : Motion β) (P : Preorder α) (Q : Preorder β) (y : α) : Prop :=
  ∃ φ : Motion.Hom M N, M.SelfOnlyAt y ∧ (∀ x, @LE.le α P.toLE y x) ∧ N.SelfOnlyAt (φ.toFun y) ∧
    (∀ z, @LE.le β Q.toLE z (φ.toFun y)) ∧ ∀ x, x ≠ y → φ.toFun x ≠ φ.toFun y

/-- `Statement:` given (b), two charts: two dipoles, the poles disconnected in the first carrier
and connected in the second. No map between the motions is asked for. -/
def GTwoCharts [TopologicalSpace α] [TopologicalSpace β] (M N : Motion α) (p q : α)
    (M' N' : Motion β) (p' q' : β) : Prop :=
  lmDipole M N p q ∧ lmDipole M' N' p' q' ∧ q ∉ connectedComponent p ∧ q' ∈ connectedComponent p'

/-- `Statement:` INVARIANT under reversal: `GDiscrete M P` gives `GDiscrete M.reverse P`. -/
theorem GDiscrete.reverse {M : Motion α} {P : Preorder α} (h : GDiscrete M P) :
    GDiscrete M.reverse P := by
  obtain ⟨⟨a, b, hs, hne⟩, hall⟩ := h
  exact ⟨⟨b, a, hs, hne.symm⟩, fun x y hs hne => (hall y x hs hne.symm).symm⟩

end Givens

/-! ## § II. Per chart, with controls -/

/-! ### § II-0. General facts about limit motions and identity-UP motions -/

/-- `Statement:` a limit motion on a Hausdorff space has no corner. -/
theorem lm_not_corner {X : Type*} [TopologicalSpace X] [T2Space X] {g : X → X}
    (hg : Continuous g) : ¬ (limitMotion g hg).Corner := by
  rintro ⟨y, b, z, hy, hs, hz, hzb⟩
  have hfix : g y = y := (lm_isLanding_iff (hg := hg) y).1 hy
  have hb : b = y := (show b = g y from hs).trans hfix
  subst hb
  exact hzb (Part.mem_unique hz hy)

/-- `Statement:` so it neither climbs nor loops. -/
theorem lm_not_climb_not_loop {X : Type*} [TopologicalSpace X] [T2Space X] {g : X → X}
    (hg : Continuous g) : ¬ (limitMotion g hg).Climb ∧ ¬ (limitMotion g hg).Loop :=
  ⟨fun h => lm_not_corner hg (Motion.climb_corner _ h),
   fun h => lm_not_corner hg (Motion.loop_corner _ h)⟩

/-- `Statement:` and no landing of it steps to a cover, in any view. -/
theorem lm_not_coverAtLanding {X : Type*} [TopologicalSpace X] [T2Space X] {g : X → X}
    (hg : Continuous g) (P : Preorder X) : ¬ GCoverAtLanding (limitMotion g hg) P := by
  rintro ⟨y, b, hy, hs, hc⟩
  have hfix : g y = y := (lm_isLanding_iff (hg := hg) y).1 hy
  have hb : b = y := (show b = g y from hs).trans hfix
  subst hb
  exact @lt_irrefl X P b hc.1

/-- `Statement:` an orbit with no fixed stage is a run closing at UP of its start. -/
theorem lm_orbit_runClosure {X : Type*} [TopologicalSpace X] [T2Space X] {g : X → X}
    (hg : Continuous g) (x : X) (hnf : ∀ n, g (g^[n] x) ≠ g^[n] x) :
    (limitMotion g hg).RunClosure (fun n => g^[n] x) ((limitMotion g hg).up x) :=
  ⟨lm_isRun (hg := hg) x, Motion.stageClosure_of_run (lm_upStepInvariant (hg := hg))
    (lm_isRun (hg := hg) x) (fun n h => hnf n ((lm_isLanding_iff (hg := hg) _).1 h))⟩

/-- `Statement:` a motion with identity UP has no corner. -/
theorem idUp_not_corner {α : Type*} (s : α → α → Prop) :
    ¬ (Motion.ofTotal (id : α → α) (fun _ => rfl) s).Corner := by
  rintro ⟨y, b, z, -, -, hz, hzb⟩
  exact hzb (Part.mem_some_iff.1 hz)

/-! ### § II-1. Given (b), discrete face -/

/-- `Statement:` in `lmSphN`, `2x ⋖ x` for nonzero `x` of `ℚ_[2]` (norms are powers of 2). -/
theorem q2_double_covBy (x : ℚ_[2]) (hx : x ≠ 0) :
    @CovBy Sphere lmSphN.toLT (OnePoint.some (2 * x)) (OnePoint.some x) := by
  have h2n : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have key : ∀ a b : ℚ_[2], @LT.lt Sphere lmSphN.toLT (OnePoint.some a) (OnePoint.some b) ↔
      ‖a‖ < ‖b‖ := fun a b => by
    show sNorm (OnePoint.some a) < sNorm (OnePoint.some b) ↔ _
    simp only [sNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm]
  refine ⟨(key _ _).2 ?_, fun c h1 h2 => ?_⟩
  · rw [norm_mul, h2n]; linarith
  · induction c using OnePoint.rec with
    | infty =>
      change sNorm OnePoint.infty < sNorm (OnePoint.some x) at h2
      simp [sNorm] at h2
    | coe w =>
      rw [key] at h1 h2
      rw [norm_mul, h2n] at h1
      have hw : w ≠ 0 := by
        rintro rfl; rw [norm_zero] at h1; linarith
      obtain ⟨m, hm⟩ := Padic.padicNormE.image (p := 2) hx
      obtain ⟨n, hn⟩ := Padic.padicNormE.image (p := 2) hw
      rw [hm, hn] at h1
      rw [hm, hn] at h2
      push_cast at h1 h2
      have e : (2 : ℝ)⁻¹ * (2 : ℝ) ^ (-m) = (2 : ℝ) ^ (-m - 1) := by
        rw [zpow_sub₀ (by norm_num), zpow_one]; ring
      rw [e] at h1
      have a1 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h1
      have a2 := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h2
      omega

/-- `Statement:` 2-adic doubling chart: `GDiscrete` holds in `lmSphN`. -/
theorem q2_GDiscrete : GDiscrete dblQ2 lmSphN := by
  refine ⟨⟨OnePoint.some 1, OnePoint.some 2, ?_, ?_⟩, ?_⟩
  · show OnePoint.some (2 : ℚ_[2]) = lmScale (2 : ℚ_[2]) two_ne_zero (OnePoint.some 1)
    rw [lm_scale_some, mul_one]
  · intro e; have := OnePoint.coe_injective e; norm_num at this
  · intro a b hs hne
    have hb : b = lmScale (2 : ℚ_[2]) two_ne_zero a := hs
    induction a using OnePoint.rec with
    | infty => exact absurd (hb.trans (lm_scale_infty _ _)).symm hne
    | coe x =>
      rw [lm_scale_some] at hb
      subst hb
      have hx : x ≠ 0 := by rintro rfl; exact hne (by rw [mul_zero])
      exact Or.inr (q2_double_covBy x hx)

/-- `Statement:` 2-adic halving chart (OVER reversed): `GDiscrete` holds too. -/
theorem q2_hlv_GDiscrete : GDiscrete hlvQ2 lmSphN := by
  obtain ⟨⟨a, b, hs, hne⟩, hall⟩ := q2_GDiscrete
  exact ⟨⟨b, a, (lm_hlv_step_reverse b a).2 hs, hne.symm⟩,
    fun x y h hne => (hall y x ((lm_hlv_step_reverse x y).1 h) hne.symm).symm⟩

/-- `Statement:` no landing of 2-adic doubling steps to a cover, in any view of `Sphere`. -/
theorem q2_not_GCoverAtLanding (P : Preorder Sphere) : ¬ GCoverAtLanding dblQ2 P :=
  lm_not_coverAtLanding _ P

/-- `Statement:` real doubling chart: `GDiscrete` FAILS in `lmRealN` (`1 → 2`, with `3/2` between). -/
theorem real_not_GDiscrete : ¬ GDiscrete dblReal lmRealN := by
  rintro ⟨-, h⟩
  have hs : dblReal.step (OnePoint.some 1) (OnePoint.some 2) := by
    show OnePoint.some (2 : ℝ) = lmScale (2 : ℝ) two_ne_zero (OnePoint.some 1)
    rw [lm_scale_some, mul_one]
  have hne : (OnePoint.some (1 : ℝ) : OnePoint ℝ) ≠ OnePoint.some 2 := fun e => by
    have := OnePoint.coe_injective e; norm_num at this
  have key : ∀ a b : ℝ, @LT.lt (OnePoint ℝ) lmRealN.toLT (OnePoint.some a) (OnePoint.some b) ↔
      |a| < |b| := fun a b => by
    show realSphNorm (OnePoint.some a) < realSphNorm (OnePoint.some b) ↔ _
    simp only [realSphNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs]
  rcases h _ _ hs hne with hc | hc
  · exact hc.2 ((key 1 (3 / 2)).2 (by norm_num)) ((key (3 / 2) 2).2 (by norm_num))
  · exact absurd ((key 2 1).1 hc.1) (by norm_num)

/-- `Statement:` real halving chart: `GDiscrete` FAILS in `lmRealN` (`1 → 1/2`, with `3/4` between). -/
theorem real_hlv_not_GDiscrete : ¬ GDiscrete hlvReal lmRealN := by
  rintro ⟨-, h⟩
  have hs : hlvReal.step (OnePoint.some 1) (OnePoint.some 2⁻¹) := by
    show OnePoint.some (2⁻¹ : ℝ) = lmScale (2⁻¹ : ℝ) (inv_ne_zero two_ne_zero) (OnePoint.some 1)
    rw [lm_scale_some, mul_one]
  have hne : (OnePoint.some (1 : ℝ) : OnePoint ℝ) ≠ OnePoint.some 2⁻¹ := fun e => by
    have := OnePoint.coe_injective e; norm_num at this
  have key : ∀ a b : ℝ, @LT.lt (OnePoint ℝ) lmRealN.toLT (OnePoint.some a) (OnePoint.some b) ↔
      |a| < |b| := fun a b => by
    show realSphNorm (OnePoint.some a) < realSphNorm (OnePoint.some b) ↔ _
    simp only [realSphNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, Real.norm_eq_abs]
  rcases h _ _ hs hne with hc | hc
  · exact absurd ((key 1 2⁻¹).1 hc.1) (by norm_num)
  · exact hc.2 ((key 2⁻¹ (3 / 4)).2 (by norm_num)) ((key (3 / 4) 1).2 (by norm_num))

/-- `Statement:` `Int.log 2 (2 * r) = Int.log 2 r + 1` for `0 < r` in ℝ. -/
theorem givens_log2_two_mul {r : ℝ} (hr : 0 < r) : Int.log 2 (2 * r) = Int.log 2 r + 1 := by
  apply _root_.le_antisymm
  · have h := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) r
    have : 2 * r < (2 : ℝ) ^ (Int.log 2 r + 1 + 1) := by
      push_cast at h; rw [zpow_add_one₀ (by norm_num)]; linarith
    have := (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (by positivity)).1 this
    omega
  · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (by positivity)).1
    rw [zpow_add_one₀ (by norm_num)]
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hr
    push_cast at this ⊢
    linarith

/-- `Statement:` the binary-exponent view of `OnePoint ℝ`: `Int.log 2 |x|` at `x`, `0` at `∞`. -/
noncomputable def realExpView : OnePoint ℝ → ℤ
  | (∞ : OnePoint ℝ) => 0
  | OnePoint.some x => Int.log 2 |x|

/-- `Statement:` CONTROL (order-relativity): real doubling MEETS `GDiscrete` in the order lifted
from `realExpView`, though it fails it in `lmRealN` (`real_not_GDiscrete`). -/
theorem real_dbl_GDiscrete_expView : GDiscrete dblReal (Preorder.lift realExpView) := by
  refine ⟨⟨OnePoint.some 1, OnePoint.some 2, ?_, ?_⟩, ?_⟩
  · show OnePoint.some (2 : ℝ) = lmScale (2 : ℝ) two_ne_zero (OnePoint.some 1)
    rw [lm_scale_some, mul_one]
  · intro e; have := OnePoint.coe_injective e; norm_num at this
  · intro a b hs hne
    have hb : b = lmScale (2 : ℝ) two_ne_zero a := hs
    induction a using OnePoint.rec with
    | infty => exact absurd (hb.trans (lm_scale_infty _ _)).symm hne
    | coe x =>
      rw [lm_scale_some] at hb
      subst hb
      have hx : x ≠ 0 := by rintro rfl; exact hne (by rw [mul_zero])
      have hv : realExpView (OnePoint.some (2 * x)) = realExpView (OnePoint.some x) + 1 := by
        show Int.log 2 |2 * x| = Int.log 2 |x| + 1
        rw [abs_mul, abs_two]; exact givens_log2_two_mul (abs_pos.2 hx)
      refine Or.inl ⟨?_, fun c h1 h2 => ?_⟩
      · show realExpView _ < realExpView _; omega
      · have h1' : realExpView (OnePoint.some x) < realExpView c := h1
        have h2' : realExpView c < realExpView (OnePoint.some (2 * x)) := h2
        omega

/-- `Statement:` at the native absolute value of `ℚ_[2]`, the nonzero norms are exactly the integer
powers of 2 (`Padic.padicNormE.image` for one inclusion, `Padic.norm_p_zpow` for the other). -/
theorem q2_norm_image :
    (fun x : ℚ_[2] => ‖x‖) '' {x | x ≠ 0} = Set.range (fun k : ℤ => (2 : ℝ) ^ k) := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨n, hn⟩ := Padic.padicNormE.image (p := 2) hx
    exact ⟨-n, by simp only at hn ⊢; rw [hn]; push_cast; rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨(2 : ℚ_[2]) ^ (-k), zpow_ne_zero _ two_ne_zero, ?_⟩
    simpa using Padic.norm_p_zpow (p := 2) (-k)

/-- `Statement:` so above a nonzero norm the next norm is at least its double: no norm of `ℚ_[2]`
lies strictly between `‖x‖` and `2 * ‖x‖`. -/
theorem q2_norm_gap {x y : ℚ_[2]} (hx : x ≠ 0) (h : ‖x‖ < ‖y‖) : 2 * ‖x‖ ≤ ‖y‖ := by
  have hy : y ≠ 0 := by
    rintro rfl; rw [norm_zero] at h; exact absurd h (not_lt.2 (norm_nonneg _))
  obtain ⟨m, hm⟩ := Padic.padicNormE.image (p := 2) hx
  obtain ⟨n, hn⟩ := Padic.padicNormE.image (p := 2) hy
  rw [hm, hn] at h ⊢
  push_cast at h ⊢
  have a := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).1 h
  have e : (2 : ℝ) * (2 : ℝ) ^ (-m) = (2 : ℝ) ^ (-m + 1) := by
    rw [zpow_add_one₀ (by norm_num)]; ring
  rw [e]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

/-- `Statement:` at the native absolute value of ℝ, the nonzero values are every positive real. -/
theorem real_norm_image : (fun x : ℝ => |x|) '' {x | x ≠ 0} = Set.Ioi 0 := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩; exact abs_pos.2 hx
  · intro hr
    exact ⟨r, ne_of_gt hr, abs_of_pos hr⟩

/-- `Statement:` so between any two positive values another absolute value lies. -/
theorem real_norm_dense {a b : ℝ} (ha : 0 < a) (hab : a < b) : ∃ x : ℝ, a < |x| ∧ |x| < b :=
  ⟨(a + b) / 2, by rw [abs_of_pos (by linarith)]; constructor <;> linarith⟩

/-- `Statement:` `MachinePhase` chart: `GDiscrete` holds in ZP-A's induced order. -/
theorem machine_GDiscrete :
    GDiscrete machineJoinMotion (zpSemilatticeSup MachinePhase).toPreorder := by
  refine ⟨⟨c₀, c₁, ⟨c₁, t_snap_machine.symm⟩, by decide⟩, ?_⟩
  rintro a b ⟨z, rfl⟩ hne
  cases a <;> cases z
  · exact absurd rfl hne
  · exact Or.inl t_snap_derived_cover.2
  · exact absurd rfl hne
  · exact absurd rfl hne

/-- `Statement:` `MachinePhase` chart: some landing of `machineJoinMotion` steps to a cover of it in
ZP-A's induced order. The proof's witness is `c₀`, ⊥ of `MachinePhase`, stepping to `c₁`. -/
theorem machine_GCoverAtLanding :
    GCoverAtLanding machineJoinMotion (zpSemilatticeSup MachinePhase).toPreorder :=
  ⟨c₀, c₁, Part.mem_some _, ⟨c₁, t_snap_machine.symm⟩, t_snap_derived_cover.2⟩

/-- `Statement:` ordinal chart (universe 0): `GDiscrete` holds for `ordinalSuccMotion` (OVER = `Order.succ`). -/
theorem ordinal_GDiscrete : GDiscrete ordinalSuccMotion.{0} inferInstance := by
  refine ⟨⟨0, Order.succ 0, rfl, (Order.lt_succ 0).ne⟩, ?_⟩
  rintro a b (rfl : b = Order.succ a) -
  exact Or.inl (Order.covBy_succ a)

/-- `Statement:` ordinal chart (universe 0): some landing of `ordinalSuccMotion` steps to its
successor, a cover of it. The proof's witness is ε₀. -/
theorem ordinal_GCoverAtLanding : GCoverAtLanding ordinalSuccMotion.{0} inferInstance :=
  ⟨Ordinal.epsilon 0, Order.succ (Ordinal.epsilon 0),
    Part.mem_some_iff.2 (Ordinal.nfp_eq_self (Ordinal.omega0_opow_epsilon 0)).symm, rfl,
    Order.covBy_succ _⟩

/-- `Statement:` CONTROL, ordinal tower chart (universe 0): `ordinalTowerMotion` (OVER `α ↦ ω^α`)
fails `GDiscrete` (1 steps to ω, and 2 lies between) and fails `GCoverAtLanding`, in `Ordinal`'s
own order. -/
theorem ordinal_tower_not_discrete :
    ¬ GDiscrete ordinalTowerMotion.{0} inferInstance ∧
      ¬ GCoverAtLanding ordinalTowerMotion.{0} inferInstance := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, h⟩
    have hs : ordinalTowerMotion.{0}.step 1 (Ordinal.omega0 ^ (1 : Ordinal.{0})) := rfl
    have h1w : (1 : Ordinal.{0}) < Ordinal.omega0 ^ (1 : Ordinal.{0}) := by
      rw [Ordinal.opow_one]; exact Ordinal.one_lt_omega0
    rcases h _ _ hs h1w.ne with hc | hc
    · refine hc.2 (c := 2) ?_ ?_
      · exact one_lt_two
      · rw [Ordinal.opow_one]; exact_mod_cast Ordinal.natCast_lt_omega0 2
    · exact absurd hc.1 (not_lt.2 h1w.le)
  · rintro ⟨y, b, hy, hs, hc⟩
    have hfix : Ordinal.omega0 ^ y = y := (ordinalTowerMotion_isLanding_iff y).1 hy
    have hb : b = y := (show b = Ordinal.omega0 ^ y from hs).trans hfix
    subst hb
    exact lt_irrefl _ hc.1

/-- `Statement:` every `UpAndOver` meets `GDiscrete`, from its corner. -/
theorem upAndOver_GDiscrete {α : Type*} [PartialOrder α] (U : UpAndOver α) :
    GDiscrete U.toMotion inferInstance := by
  obtain ⟨y, b, -, hb, -⟩ := U.corner
  exact ⟨⟨y, b, hb, hb.lt.ne⟩, fun _ _ h _ => Or.inl h⟩

/-- `Statement:` and `GCoverAtLanding`. -/
theorem upAndOver_GCoverAtLanding {α : Type*} [PartialOrder α] (U : UpAndOver α) :
    GCoverAtLanding U.toMotion inferInstance := by
  obtain ⟨y, b, hy, hb, -⟩ := U.corner
  exact ⟨y, b, Part.mem_some_iff.2 hy.closure_eq.symm, hb, hb⟩

/-- `Statement:` CONTROL (`Unit`): no motion on `Unit` meets `GDiscrete`. -/
theorem unit_not_GDiscrete (M : Motion Unit) (P : Preorder Unit) : ¬ GDiscrete M P :=
  fun ⟨⟨_, _, _, h⟩, _⟩ => h rfl

-- Statement: CONTROL (ℝ): there is no `UpAndOver` on ℝ at all.
example : IsEmpty (UpAndOver ℝ) := UpAndOver.isEmpty_of_denselyOrdered

/-- `Statement:` in `lmSphN`, `a < b` for points of `ℚ_[2]` iff `‖a‖ < ‖b‖`. -/
theorem sph_lt_iff (a b : ℚ_[2]) :
    @LT.lt Sphere lmSphN.toLT (OnePoint.some a) (OnePoint.some b) ↔ ‖a‖ < ‖b‖ := by
  show sNorm (OnePoint.some a) < sNorm (OnePoint.some b) ↔ _
  simp only [sNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm]

/-- `Statement:` in `lmSphN`, 0 of `ℚ_[2]` has no first step (no cover), although
`GDiscrete dblQ2 lmSphN` holds (`q2_GDiscrete`): covers along the run do not give a first step at
0 of `ℚ_[2]`. -/
theorem q2_zero_not_firstStep : ¬ @HasFirstStep Sphere lmSphN.toLT (OnePoint.some 0) := by
  rintro ⟨c, h0c, hc⟩
  have h2n : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
  induction c using OnePoint.rec with
  | infty =>
    refine hc (c := OnePoint.some 1) ((sph_lt_iff _ _).2 (by simp)) ?_
    show sNorm (OnePoint.some 1) < sNorm OnePoint.infty
    simp [sNorm]
  | coe x =>
    have hx : 0 < ‖x‖ := by simpa using (sph_lt_iff _ _).1 h0c
    refine hc (c := OnePoint.some (2 * x)) ((sph_lt_iff _ _).2 ?_) ((sph_lt_iff _ _).2 ?_)
    · rw [norm_zero, norm_mul, h2n]; positivity
    · rw [norm_mul, h2n]; linarith

/-! ### § II-2. Given (b), continuous face -/

/-- `Statement:` on `OnePoint ℝ`, ∞ is in the connected component of 0 of ℝ. -/
theorem real_GConnected : GConnected (OnePoint.some (0 : ℝ)) (∞ : OnePoint ℝ) :=
  real_zero_infty_connected

/-- `Statement:` on `Sphere`, ∞ is not in the connected component of 0 of `ℚ_[2]`. -/
theorem q2_not_GConnected : ¬ GConnected (OnePoint.some (0 : ℚ_[2]) : Sphere) ∞ :=
  arc_never_meets_infty.2.2.2.1

/-- `Statement:` and no path joins them. -/
theorem q2_not_GJoined : ¬ GJoined (OnePoint.some (0 : ℚ_[2]) : Sphere) ∞ :=
  fun h => no_path_zero_infty.false h.somePath

-- Statement: the order half: in ℝ, 0 has no first step.
example : ¬ HasFirstStep (0 : ℝ) := axb1_fails_in_ordered_field

/-! ### § II-3. Given (b), two charts at once -/

/-- `Statement:` the two dipoles (`ℚ_[2]` disconnected, ℝ connected), and one rational orbit
`2ⁿ · 1` tending to 0 in `ℚ_[2]` and to infinity in ℝ (`doubling_place_dichotomy`). -/
theorem givens_two_charts :
    GTwoCharts dblQ2 hlvQ2 (OnePoint.some 0) ∞ dblReal hlvReal ∞ (OnePoint.some 0) ∧
      Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n * ((1 : ℚ) : ℚ_[2])) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => |(2 : ℝ) ^ n * ((1 : ℚ) : ℝ)|) atTop atTop :=
  ⟨⟨lm_q2_dipole, lm_real_dipole, arc_never_meets_infty.2.2.2.1,
    by rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial⟩,
   doubling_place_dichotomy 1 one_ne_zero⟩

/-- `Statement:` 2-adic doubling meets `GDiscrete` in `lmSphN` and real doubling fails it in
`lmRealN`; the `trials p hp` mass of `stepOff` is the switch on `Bool` (join `||`) and 0 on `NNReal`
(join `max`) at every `p`; and 0 of ℝ has no first step. The probability conjuncts are on `Bool` and
`NNReal`, not on the 2-adic or real charts; at 0 of `ℚ_[2]` in `lmSphN` there is no first step
(`q2_zero_not_firstStep`). -/
theorem two_charts_snap :
    (GDiscrete dblQ2 lmSphN ∧ ¬ GDiscrete dblReal lmRealN) ∧
    (∀ p (hp : p ≤ 1), trials p hp (@stepOff Bool boolOrZPS) = if p = 0 then 0 else 1) ∧
    (∀ p (hp : p ≤ 1), trials p hp (@stepOff NNReal nnrealMaxZPS) = 0) ∧
    ¬ HasFirstStep (0 : ℝ) := by
  refine ⟨⟨q2_GDiscrete, real_not_GDiscrete⟩, fun p hp => ?_, fun p hp => ?_,
    axb1_fails_in_ordered_field⟩
  · rw [@stepOff_of_firstStep Bool boolOrZPS bool_botHasFirstStep, dial_fire_jump]
  · rw [@stepOff_of_not_firstStep NNReal nnrealMaxZPS nnreal_not_botHasFirstStep]; simp

/-- `Statement:` no homeomorphism `Sphere ≃ₜ OnePoint ℝ`. -/
theorem no_homeo_sphere_real : IsEmpty (Sphere ≃ₜ OnePoint ℝ) := by
  refine ⟨fun e => ?_⟩
  have hpre : IsPreconnected (Set.univ : Set Sphere) := by
    have := (isPreconnected_univ (α := OnePoint ℝ)).image e.symm e.symm.continuous.continuousOn
    rwa [Set.image_univ, e.symm.surjective.range_eq] at this
  have : PreconnectedSpace Sphere := ⟨hpre⟩
  exact arc_never_meets_infty.2.2.2.1
    (by rw [PreconnectedSpace.connectedComponent_eq_univ]; trivial)

/-- `Statement:` so the two doubling charts are never `HomeoIso`. -/
theorem no_homeoIso_dblQ2_dblReal : IsEmpty (Motion.HomeoIso dblQ2 dblReal) := by
  refine ⟨fun e => ?_⟩
  exact no_homeo_sphere_real.false
    ⟨e.toStrictIso.toEquiv, e.continuous_hom, e.continuous_inv⟩

/-- `Statement:` any `StrictIso` from 2-adic to real doubling sends 0 of `ℚ_[2]` to ∞ of `OnePoint ℝ`.
`Reading:` INVERSION, forced at the strict level. -/
theorem strictIso_zero_to_infty (φ : Motion.StrictIso dblQ2 dblReal) :
    φ.hom.toFun (OnePoint.some 0) = ∞ := by
  have h := lmSinkOf.map φ lm_dbl_sinkOf
  have ne12 : (OnePoint.some (1 : ℝ) : OnePoint ℝ) ≠ OnePoint.some 2 := fun e => by
    have := OnePoint.coe_injective e; norm_num at this
  have ne10 : (OnePoint.some (1 : ℝ) : OnePoint ℝ) ≠ OnePoint.some 0 := fun e => by
    have := OnePoint.coe_injective e; norm_num at this
  have ne20 : (OnePoint.some (2 : ℝ) : OnePoint ℝ) ≠ OnePoint.some 0 := fun e => by
    have := OnePoint.coe_injective e; norm_num at this
  by_cases hq : φ.hom.toFun ∞ = OnePoint.some 1
  · have hx : (OnePoint.some (2 : ℝ) : OnePoint ℝ) ≠ φ.hom.toFun ∞ := by
      rw [hq]; exact ne12.symm
    exact Part.mem_unique (h _ hx) (lm_real_dipole.2.1 _ ne20)
  · have hx : (OnePoint.some (1 : ℝ) : OnePoint ℝ) ≠ φ.hom.toFun ∞ := fun e => hq e.symm
    exact Part.mem_unique (h _ hx) (lm_real_dipole.2.1 _ ne10)

/-- `Statement:` CONTROL: a strict `Hom` from 2-adic to real doubling exists (constant at ∞), so a
`Hom`-level pairing carries no content. -/
theorem const_infty_hom : ∃ φ : Motion.Hom dblQ2 dblReal, ∀ x, φ.toFun x = ∞ := by
  have hfixR : lmScale (2 : ℝ) two_ne_zero ∞ = ∞ := lm_scale_infty _ _
  have hlandR : (∞ : OnePoint ℝ) ∈ dblReal.up ∞ := (lm_isLanding_iff _).2 hfixR
  have hdom : ∀ x : Sphere, ∃ y, y ∈ dblQ2.up x := by
    intro x
    by_cases hx : x = ∞
    · subst hx; exact ⟨_, (lm_isLanding_iff _).2 (lm_scale_infty _ _)⟩
    · exact ⟨_, lm_dbl_sinkOf x hx⟩
  refine ⟨⟨fun _ => ∞, fun {_ _} _ => hfixR.symm, fun x => ?_⟩, fun _ => rfl⟩
  apply Part.ext
  intro q
  obtain ⟨y, hy⟩ := hdom x
  constructor
  · intro hq
    rw [Part.mem_unique hq hlandR]
    exact (Part.mem_map_iff _).2 ⟨y, hy, rfl⟩
  · intro hq
    obtain ⟨_, _, rfl⟩ := (Part.mem_map_iff _).1 hq
    exact hlandR

/-! ### § II-4. Given (a), minimal and maximal at one point -/

/-- `Statement:` 0 of `ℚ_[2]` meets `GMinMax` under doubling, off ∞. -/
theorem q2_GMinMax : GMinMax dblQ2 (OnePoint.some 0) ∞ := ⟨lm_dbl_step_level.1, lm_dbl_sinkOf⟩

/-- `Statement:` ∞ of `Sphere` meets it under halving, off 0 of `ℚ_[2]`. -/
theorem q2_hlv_GMinMax : GMinMax hlvQ2 ∞ (OnePoint.some 0) :=
  ⟨⟨(lm_scale_infty _ _).symm, fun _ hb => hb.trans (lm_scale_infty _ _)⟩, lm_q2_dipole.2.2.1⟩

/-- `Statement:` real chart: ∞ of `OnePoint ℝ` meets it under doubling, off 0 of ℝ. -/
theorem real_GMinMax_infty : GMinMax dblReal ∞ (OnePoint.some 0) :=
  ⟨⟨(lm_scale_infty _ _).symm, fun _ hb => hb.trans (lm_scale_infty _ _)⟩, lm_real_dipole.2.1⟩

/-- `Statement:` and 0 of ℝ does not, under doubling, off ∞. -/
theorem real_not_GMinMax_zero : ¬ GMinMax dblReal (OnePoint.some 0) ∞ :=
  fun h => lm_real_dbl_zero_not_sink h.2

/-- `Statement:` 0 of ℝ meets it under halving, off ∞. -/
theorem real_hlv_GMinMax_zero : GMinMax hlvReal (OnePoint.some 0) ∞ := by
  refine ⟨⟨?_, fun _ hb => hb.trans ?_⟩, lm_real_dipole.2.2.1⟩
  · show OnePoint.some (0 : ℝ) = lmScale (2⁻¹ : ℝ) _ (OnePoint.some 0)
    rw [lm_scale_some, mul_zero]
  · rw [lm_scale_some, mul_zero]

-- Statement: `MachinePhase` chart: `c₀`, ⊥ of `MachinePhase`, does not step only to itself.
example : ¬ machineJoinMotion.SelfOnlyAt c₀ := fun h =>
  absurd ((machineJoinMotion_selfOnlyAt_iff c₀).1 h) (by decide)

/-- `Statement:` ordinal chart (universe 0): no ordinal steps only to itself under `Order.succ`. -/
theorem ordinal_no_selfOnly (y : Ordinal.{0}) : ¬ ordinalSuccMotion.SelfOnlyAt y :=
  fun h => (Order.lt_succ y).ne (show y = Order.succ y from h.1)

-- Statement: CONTROL (`Unit`): the identity limit motion on `Unit` meets `GMinMax` vacuously.
example : GMinMax (limitMotion (id : Unit → Unit) continuous_id) () () :=
  ⟨⟨rfl, fun _ _ => rfl⟩, fun _ hx => absurd rfl hx⟩

/-- `Statement:` CONTROL (constant map): the constant map at 0 of `ℚ_[2]` meets `GMinMax` there,
off every `q`. -/
theorem const_GMinMax (q : Sphere) :
    GMinMax (limitMotion (fun _ : Sphere => OnePoint.some 0) continuous_const) (OnePoint.some 0) q := by
  refine ⟨⟨rfl, fun _ hb => hb⟩, fun x _ => ?_⟩
  show OnePoint.some 0 ∈ limitRetraction _ x
  rw [lm_mem_limitRetraction_iff]
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  show OnePoint.some 0 = (fun _ : Sphere => OnePoint.some (0 : ℚ_[2]))^[1 + k] x
  rw [add_comm, Function.iterate_succ_apply']

/-- `Statement:` and no limit motion is its dipole partner (OVER reversed). -/
theorem const_no_limit_partner : ¬ ∃ (h : Sphere → Sphere) (hh : Continuous h), ∀ a b,
    (limitMotion h hh).step a b ↔
      (limitMotion (fun _ : Sphere => OnePoint.some 0) continuous_const).step b a := by
  rintro ⟨h, hh, hiff⟩
  have e1 : OnePoint.some 0 = h (OnePoint.some 0) := (hiff (OnePoint.some 0) (OnePoint.some 0)).2 rfl
  have e2 : ∞ = h (OnePoint.some 0) := (hiff (OnePoint.some 0) ∞).2 rfl
  exact OnePoint.coe_ne_infty 0 (e1.trans e2.symm)

-- Statement: CONTROL (`Unit`): no dipole on `Unit`.
example (M N : Motion Unit) : ¬ lmDipole M N () () := fun h => h.1 rfl

/-! ### § II-5. Given (c), the climb, never a loop -/

/-- `Statement:` 2-adic doubling neither climbs nor loops. -/
theorem q2_not_climb : ¬ dblQ2.Climb ∧ ¬ dblQ2.Loop := lm_not_climb_not_loop _
/-- `Statement:` nor does real doubling. -/
theorem real_not_climb : ¬ dblReal.Climb ∧ ¬ dblReal.Loop := lm_not_climb_not_loop _
/-- `Statement:` `machineJoinMotion` has no corner. -/
theorem machine_not_corner : ¬ machineJoinMotion.Corner := idUp_not_corner _
/-- `Statement:` ordinal chart: `ordinalSuccMotion` climbs and never loops. -/
theorem ordinal_GClimbNotLoop : GClimbNotLoop ordinalSuccMotion.{0} :=
  ⟨ordinalSuccMotion_climb, ordinalSuccMotion_not_loop⟩
/-- `Statement:` every `UpAndOver` climbs and never loops. -/
theorem upAndOver_GClimbNotLoop {α : Type*} [PartialOrder α] (U : UpAndOver α) :
    GClimbNotLoop U.toMotion := ⟨U.toMotion_climb, U.toMotion_not_loop⟩

-- Statement: CONTROL (`Fin 3`, always-true OVER): this motion loops, so fails `GClimbNotLoop`.
example : ¬ GClimbNotLoop (Motion.ofTotal (fun x : Fin 3 => if x = 1 then 2 else x) (by decide)
    (fun _ _ => True)) :=
  fun h => h.2 ⟨2, 1, Part.mem_some_iff.2 (by decide), trivial, by decide, Part.mem_some_iff.2 (by decide)⟩

/-! ### § II-6. Given (c), the return to a fixed destination (ruling 75) -/

/-- `Statement:` the snap arc on `Sphere` starts at 0 of `ℚ_[2]`. -/
theorem arcS_zero : arcS 0 = OnePoint.some 0 := by
  show OnePoint.some ((cnfToZp2 (towerNONote 0) : ℤ_[2]) : ℚ_[2]) = _
  rw [snap_arc_z2_loop.1]; simp

/-- `Statement:` its stage `n + 1` is `2 ^ (n + 1)`. -/
theorem arcS_succ (n : ℕ) : arcS (n + 1) = OnePoint.some ((2 : ℚ_[2]) ^ (n + 1)) := by
  have hstage : cnfToZp2 (towerNONote (n + 1)) = (2 : ℤ_[2]) ^ (n + 1) := by
    rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote, towerImageStep, cnfToZp2_tower_valuation]
  have hc : (((2 : ℤ_[2]) ^ (n + 1) : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ (n + 1) := by
    rw [PadicInt.coe_pow]; norm_cast
  show OnePoint.some ((cnfToZp2 (towerNONote (n + 1)) : ℤ_[2]) : ℚ_[2]) = _
  rw [hstage, hc]

/-- `Statement:` the arc's tail is a run of 2-adic doubling whose stage closure contains the arc's
start, 0 of `ℚ_[2]`. `Reading:` FIXED DESTINATION, never a finite step count (ruling 75). -/
theorem q2_arc_returnToStart : GReturnToStart dblQ2 arcS := by
  have hrun : (fun n => arcS (n + 1)) =
      fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some 2) := by
    funext n; rw [arcS_succ, lm_scale_iterate_some, pow_succ]
  have hnf : ∀ n, lmScale (2 : ℚ_[2]) two_ne_zero ((lmScale (2 : ℚ_[2]) two_ne_zero)^[n]
      (OnePoint.some 2)) ≠ (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some 2) := by
    intro n h
    rw [lm_scale_iterate_some, lm_scale_some] at h
    have h' := OnePoint.coe_injective h
    have hz : (2 : ℚ_[2]) ^ n * 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) two_ne_zero
    exact hz (by linear_combination h')
  have hrc := lm_orbit_runClosure (lmScale (2 : ℚ_[2]) two_ne_zero).continuous (OnePoint.some 2) hnf
  rw [← hrun] at hrc
  refine ⟨_, hrc, ?_⟩
  rw [arcS_zero]
  exact lm_dbl_sinkOf _ (OnePoint.coe_ne_infty 2)

/-- `Statement:` real doubling chart: no sequence starting at 0 of ℝ meets `GReturnToStart`. -/
theorem real_dbl_no_return_zero (s : ℕ → OnePoint ℝ) (h0 : s 0 = OnePoint.some 0) :
    ¬ GReturnToStart dblReal s := by
  rintro ⟨c, ⟨-, hc⟩, hmem⟩
  have h1 := hc (s 1) ⟨0, rfl⟩
  rw [h0] at hmem
  have hne0 : s 1 ≠ OnePoint.some 0 := fun e => h1.1 (by
    rw [e]; exact (lm_isLanding_iff _).2 (by rw [lm_scale_some, mul_zero]))
  have hinf : (∞ : OnePoint ℝ) ∈ dblReal.up (s 1) := lm_real_dipole.2.1 _ hne0
  rw [h1.2] at hinf
  exact OnePoint.coe_ne_infty 0 (Part.mem_unique hmem hinf)

/-- `Statement:` real halving chart: a sequence from 0 of ℝ meets `GReturnToStart` (`0, 1, 1/2,
1/4, …`, the tail closing at 0 of ℝ). So `GReturnToStart` alone does not separate a return the
long way round from a plain contraction. -/
theorem real_hlv_returnToStart :
    ∃ s : ℕ → OnePoint ℝ, s 0 = OnePoint.some 0 ∧ GReturnToStart hlvReal s := by
  let g := lmScale (2⁻¹ : ℝ) (inv_ne_zero two_ne_zero)
  have hnf : ∀ n, g (g^[n] (OnePoint.some 1)) ≠ g^[n] (OnePoint.some 1) := by
    intro n h
    rw [lm_scale_iterate_some, lm_scale_some] at h
    have h' := OnePoint.coe_injective h
    have hz : (2⁻¹ : ℝ) ^ n * 1 ≠ 0 := by positivity
    exact hz (by linear_combination (-2) * h')
  have hrc := lm_orbit_runClosure g.continuous (OnePoint.some 1) hnf
  refine ⟨fun n => Nat.casesOn n (OnePoint.some 0) (fun m => g^[m] (OnePoint.some 1)), rfl,
    _, hrc, ?_⟩
  exact lm_real_dipole.2.2.1 _ (OnePoint.coe_ne_infty 1)

/-- `Statement:` ordinal chart (universe 0): the tower from 0 of `Ordinal` does not meet
`GReturnToStart`: no `RunClosure` of its tail contains 0 of `Ordinal`. The proof: that closure is
ε₀ (`ordinalTowerMotion_stageClosure`), and ε₀ ≠ 0 of `Ordinal` (`epsilon0_ne_zero`). -/
theorem ordinal_tower_no_return :
    ¬ GReturnToStart ordinalTowerMotion.{0}
      (fun n => (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] 0) := by
  rintro ⟨c, ⟨-, hc⟩, hmem⟩
  have h1 := hc ((fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[1] 0) ⟨0, rfl⟩
  have h2 := (ordinalTowerMotion_stageClosure.{0}
    ((fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[1] 0) ⟨1, rfl⟩).2
  have hc' : c = Part.some (Ordinal.epsilon 0) := h1.2.symm.trans h2
  rw [hc'] at hmem
  exact epsilon0_ne_zero (Part.mem_some_iff.1 hmem).symm

/-! ### § II-7. Given (c), breaking away -/

/-- `Statement:` `MachinePhase` chart: a run of `machineJoinMotion` leaves `c₀`, ⊥ of `MachinePhase`. -/
theorem machine_leavesByRun : GLeavesByRun machineJoinMotion c₀ :=
  ⟨fun n => match n with | 0 => c₀ | _ + 1 => c₁, fun n => ⟨c₁, by cases n <;> rfl⟩, rfl,
    by decide⟩

/-- `Statement:` ordinal chart: a run of `ordinalSuccMotion` leaves 0 of `Ordinal`. -/
theorem ordinal_leavesByRun : GLeavesByRun ordinalSuccMotion.{0} 0 := by
  refine ⟨fun n => (n : Ordinal.{0}), fun n => ?_, by simp, by simp⟩
  show ((n + 1 : ℕ) : Ordinal.{0}) = Order.succ (n : Ordinal.{0})
  rw [Order.succ_eq_add_one]; push_cast; rfl

/-- `Statement:` slot chart: a run of `slotMotion` leaves `false`. -/
theorem slot_leavesByRun : GLeavesByRun slotMotion false :=
  ⟨slotRun (fun _ => true), slotRun_isRun _, (slotRun_crosses_iff _).1, by decide⟩

/-! ### § II-8. Given (a), coincidence face as a map (ruling 74) -/

/-- `Statement:` on ℤ_[2], ℤ_[2]'s 0 included, doubling raises `q2Val` by one. -/
theorem q2Val_double (x : ℤ_[2]) : q2Val (2 * x) = q2Val x + 1 := by
  by_cases hx : x = 0
  · subst hx; rw [mul_zero, q2Val_bot, top_add]
  · exact q2Val_scale x hx

/-- `Statement:` `q2Val` as a strict map from doubling on ℤ_[2] to `+1` on `ℕ∞`. -/
noncomputable def q2ValHom :
    Motion.Hom (Motion.ofFun (fun x : ℤ_[2] => 2 * x)) (Motion.ofFun (fun n : ℕ∞ => n + 1)) where
  toFun := q2Val
  map_step := fun {a b} h => by
    show q2Val b = q2Val a + 1
    rw [show b = 2 * a from h]; exact q2Val_double a
  map_up := fun x => by simp [Motion.ofFun, Motion.ofTotal]

/-- `Statement:` ℤ_[2]'s 0 meets `GCoincidence`: some strict map of motions sends it, least in norm,
to ⊤ of `ℕ∞`, and sends no other point there. The proof's witness is `q2ValHom`. `Reading:` COINCIDENCE. -/
theorem z2_GCoincidence :
    GCoincidence (Motion.ofFun (fun x : ℤ_[2] => 2 * x)) (Motion.ofFun (fun n : ℕ∞ => n + 1))
      (Preorder.lift (fun x : ℤ_[2] => ‖x‖)) inferInstance 0 := by
  refine ⟨q2ValHom, (z2_double_selfOnlyAt_iff 0).2 rfl, fun x => ?_, ?_, fun z => ?_,
    fun x hx h => hx ?_⟩
  · show ‖(0 : ℤ_[2])‖ ≤ ‖x‖; simp
  · show (Motion.ofFun (fun n : ℕ∞ => n + 1)).SelfOnlyAt (q2Val 0)
    rw [Motion.selfOnlyAt_ofFun_iff, q2Val_bot]; exact top_add 1
  · show z ≤ q2Val 0; rw [q2Val_bot]; exact le_top
  · exact q2Val_unique x (h.trans q2Val_bot)

/-- `Statement:` on a commutative ring, `f (2x) = f x + 1` iterates to `f (2 ^ k * y) = f y + k`. -/
theorem doubling_counter_pow {R : Type*} [CommRing R] (f : R → ℕ∞)
    (hf : ∀ x, f (2 * x) = f x + 1) (k : ℕ) (y : R) : f ((2 : R) ^ k * y) = f y + k := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_comm ((2 : R) ^ k) 2, mul_assoc, hf, ih]; push_cast; ring

/-- `Statement:` on a commutative ring, `f (2x) = f x + 1` forces `f 0 = ⊤`, ⊤ of `ℕ∞`. -/
theorem doubling_counter_zero {R : Type*} [CommRing R] (f : R → ℕ∞)
    (hf : ∀ x, f (2 * x) = f x + 1) : f 0 = ⊤ := by
  by_contra h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h
  have h1 := hf 0
  rw [mul_zero, ← hn] at h1
  have h2 : ((n : ℕ) : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by rw [h1]; push_cast; rfl
  exact absurd (Nat.cast_injective h2) (by omega)

/-- `Statement:` on a commutative ring `R`, some `f : R → ℕ∞` has `f (2x) = f x + 1` and finite
values off R's 0 iff (a) 2 is a non-zero-divisor (`2x = 0` forces `x = 0`) and (b) R is 2-adically
separated (no nonzero `x` is divisible by every `2 ^ k`: ⋂ₖ 2ᵏR = 0, Mathlib's
`IsHausdorff (Ideal.span {2}) R`, `doubling_counter_iff_isHausdorff`). The backward witness is the
2-adic order (`emultiplicity 2`). Krull's intersection theorem (`IsHausdorff.of_isDomain`) gives (b)
on a Noetherian domain whose ideal `(2)` is proper. -/
theorem doubling_counter_iff {R : Type*} [CommRing R] :
    (∃ f : R → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤) ↔
      (∀ x : R, 2 * x = 0 → x = 0) ∧ ∀ x : R, x ≠ 0 → ∃ k : ℕ, ¬ (2 : R) ^ k ∣ x := by
  constructor
  · rintro ⟨f, hf, hfin⟩
    have h0 := doubling_counter_zero f hf
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · by_contra hne
      have h1 := hf x
      rw [hx, h0] at h1
      refine hfin x hne ?_
      by_contra ht
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
      rw [← hn] at h1
      exact absurd h1.symm (by exact_mod_cast (ENat.natCast_ne_top (n + 1)))
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hfin x hx)
      refine ⟨n + 1, fun ⟨y, hy⟩ => ?_⟩
      have h1 := doubling_counter_pow f hf (n + 1) y
      rw [← hy, ← hn] at h1
      have hle : (((n + 1 : ℕ)) : ℕ∞) ≤ n := by rw [h1]; exact le_add_self
      exact absurd (Nat.cast_le.1 hle) (by omega)
  · rintro ⟨hreg, hint⟩
    have hcan : ∀ (k : ℕ) (x : R), (2 : R) ^ (k + 1) ∣ 2 * x ↔ (2 : R) ^ k ∣ x := by
      intro k x
      constructor
      · rintro ⟨y, hy⟩
        refine ⟨y, sub_eq_zero.1 (hreg _ ?_)⟩
        rw [mul_sub, hy, pow_succ]; ring
      · rintro ⟨y, rfl⟩; exact ⟨y, by rw [pow_succ]; ring⟩
    refine ⟨emultiplicity (2 : R), fun x => _root_.le_antisymm ?_ ?_, fun x hx htop => ?_⟩
    · rw [← ENat.forall_natCast_le_iff_le]
      intro a ha
      rcases a with _ | a
      · simp
      · have h1 := le_emultiplicity_of_pow_dvd ((hcan a x).1 (pow_dvd_of_le_emultiplicity ha))
        push_cast; exact add_le_add h1 le_rfl
    · rw [← ENat.forall_natCast_le_iff_le]
      intro a ha
      rcases a with _ | a
      · simp
      · have ha' : (a : ℕ∞) ≤ emultiplicity 2 x := by
          push_cast at ha; exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 ha
        exact le_emultiplicity_of_pow_dvd ((hcan a x).2 (pow_dvd_of_le_emultiplicity ha'))
    · obtain ⟨k, hk⟩ := hint x hx
      exact hk (pow_dvd_of_le_emultiplicity (htop ▸ le_top))

/-- `Statement:` `doubling_counter_iff` with (b) as Mathlib's `IsHausdorff (Ideal.span {2}) R`. -/
theorem doubling_counter_iff_isHausdorff {R : Type*} [CommRing R] :
    (∃ f : R → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤) ↔
      (∀ x : R, 2 * x = 0 → x = 0) ∧ IsHausdorff (Ideal.span {(2 : R)}) R := by
  have hmem : ∀ (n : ℕ) (x : R),
      x ≡ 0 [SMOD (Ideal.span {(2 : R)} ^ n • ⊤ : Submodule R R)] ↔ (2 : R) ^ n ∣ x := by
    intro n x
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hsep : (∀ x : R, x ≠ 0 → ∃ k : ℕ, ¬ (2 : R) ^ k ∣ x) ↔
      IsHausdorff (Ideal.span {(2 : R)}) R := by
    rw [isHausdorff_iff]
    simp only [hmem]
    constructor
    · intro h x hx
      by_contra hne
      obtain ⟨k, hk⟩ := h x hne
      exact hk (hx k)
    · intro h x hx
      by_contra hne
      exact hx (h x (fun k => not_not.1 (fun hk => hne ⟨k, hk⟩)))
  rw [doubling_counter_iff, hsep]

/-- `Statement:` one way: on a nontrivial commutative ring, a doubling counter forces `2 ≠ 0` and
2 not a unit. The converse fails (CONTROLS below, `ZMod 4` and `ℤ × ℚ`). -/
theorem doubling_counter_two_ne_zero_not_isUnit {R : Type*} [CommRing R] [Nontrivial R]
    (f : R → ℕ∞) (hf : ∀ x, f (2 * x) = f x + 1) (hfin : ∀ x, x ≠ 0 → f x ≠ ⊤) :
    (2 : R) ≠ 0 ∧ ¬ IsUnit (2 : R) := by
  obtain ⟨hreg, hint⟩ := doubling_counter_iff.1 ⟨f, hf, hfin⟩
  refine ⟨fun h2 => one_ne_zero (hreg 1 (by rw [mul_one, h2])), fun hu => ?_⟩
  obtain ⟨k, hk⟩ := hint 1 one_ne_zero
  exact hk (hu.pow k).dvd

/-- `Statement:` on every field no `f : K → ℕ∞` has `f (2x) = f x + 1` and finite values off 0:
in a field 2 is 0 or a unit. -/
theorem no_doubling_valuation_field_any {K : Type*} [Field K] (f : K → ℕ∞)
    (hf : ∀ x, f (2 * x) = f x + 1) (hfin : ∀ x, x ≠ 0 → f x ≠ ⊤) : False := by
  obtain ⟨h2, hu⟩ := doubling_counter_two_ne_zero_not_isUnit f hf hfin
  exact hu (Ne.isUnit h2)

/-- `Statement:` on every field, `GCoincidence` of doubling into `+1` on `ℕ∞` fails at the
field's 0. With `z2_GCoincidence` (occupied at ℤ_[2]'s 0): the occupancy pair. -/
theorem field_no_GCoincidence_any {K : Type*} [Field K] (P : Preorder K) :
    ¬ GCoincidence (Motion.ofFun (fun x : K => 2 * x)) (Motion.ofFun (fun n : ℕ∞ => n + 1)) P
      inferInstance 0 := by
  rintro ⟨φ, -, -, -, htop, hoff⟩
  have hf : ∀ x, φ.toFun (2 * x) = φ.toFun x + 1 := fun x => φ.map_step (a := x) (b := 2 * x) rfl
  have h0 : φ.toFun 0 = ⊤ := top_le_iff.1 (htop ⊤)
  exact no_doubling_valuation_field_any φ.toFun hf (fun x hx => by rw [← h0]; exact hoff x hx)

-- Statement: the doubling counter exists at ℤ_[2] (`q2Val`) and at ℤ.
example : ∃ f : ℤ_[2] → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤ :=
  ⟨q2Val, q2Val_double, fun x hx h => hx (q2Val_unique x h)⟩
example : ∃ f : ℤ → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤ := by
  refine doubling_counter_iff.2 ⟨fun x hx => by omega, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := FiniteMultiplicity.def.1
    (Int.finiteMultiplicity_iff.2 ⟨by norm_num, hx⟩ : FiniteMultiplicity (2 : ℤ) x)
  exact ⟨n + 1, hn⟩
-- Statement: CONTROL: on the zero ring `Unit` the constant ⊤ is a counter, and 2 is a unit there.
example : ∃ f : Unit → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤ :=
  ⟨fun _ => ⊤, fun _ => (top_add 1).symm, fun x hx => absurd (Subsingleton.elim x 0) hx⟩
-- Statement: CONTROL: no counter on `ZMod 2`, where 2 = 0.
example : ¬ ∃ f : ZMod 2 → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤ :=
  fun ⟨f, hf, hfin⟩ => (doubling_counter_two_ne_zero_not_isUnit f hf hfin).1 (by decide)
-- Statement: CONTROL: in `ZMod 4`, 2 is nonzero and not a unit, and no counter exists.
example : (2 : ZMod 4) ≠ 0 ∧ ¬ IsUnit (2 : ZMod 4) ∧
    ¬ ∃ f : ZMod 4 → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤ :=
  ⟨by decide, by decide, fun h => absurd ((doubling_counter_iff.1 h).1 2 (by decide)) (by decide)⟩
-- Statement: CONTROL: in `ℤ × ℚ`, `2x = 0` forces `x = 0` and 2 is not a unit, and no counter
-- exists: `(0, 1)` is divisible by every `2 ^ k`.
example : (∀ x : ℤ × ℚ, 2 * x = 0 → x = 0) ∧ ¬ IsUnit (2 : ℤ × ℚ) ∧
    ¬ ∃ f : ℤ × ℚ → ℕ∞, (∀ x, f (2 * x) = f x + 1) ∧ ∀ x, x ≠ 0 → f x ≠ ⊤ := by
  refine ⟨fun x hx => ?_, fun hu => ?_, fun h => ?_⟩
  · ext
    · simpa using congrArg Prod.fst hx
    · simpa using congrArg Prod.snd hx
  · have h2 : IsUnit (2 : ℤ) := by simpa using (Prod.isUnit_iff.1 hu).1
    exact absurd (Int.isUnit_iff.1 h2) (by omega)
  · obtain ⟨k, hk⟩ := (doubling_counter_iff.1 h).2 (0, 1) (by simp)
    exact hk ⟨(0, ((2 : ℚ) ^ k)⁻¹), by ext <;> simp⟩

/-- `Statement:` on a characteristic-0 field no `f : K → ℕ∞` has `f (2x) = f x + 1` and finite
values off 0: halving would push a finite value past every natural number. -/
theorem no_doubling_valuation_field {K : Type} [Field K] [CharZero K] (f : K → ℕ∞)
    (hf : ∀ x, f (2 * x) = f x + 1) (hfin : ∀ x, x ≠ 0 → f x ≠ ⊤) : False := by
  have key : ∀ (k : ℕ) (y : K), f ((2 : K) ^ k * y) = f y + k := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ, mul_comm ((2 : K) ^ k) 2, mul_assoc, hf, ih]; push_cast; ring
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (hfin 1 one_ne_zero)
  have h2 : ((2 : K) ^ (n + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  have := key (n + 1) ((2 : K) ^ (n + 1))⁻¹
  rw [mul_inv_cancel₀ h2, ← hn] at this
  have hle : (((n + 1 : ℕ)) : ℕ∞) ≤ n := by rw [this]; exact le_add_self
  exact absurd (Nat.cast_le.1 hle) (by omega)

/-- `Statement:` CONTROL: on any characteristic-0 field (ℝ and `ℚ_[2]` both), `GCoincidence` of
doubling into `+1` on `ℕ∞` fails at 0. -/
theorem field_no_GCoincidence {K : Type} [Field K] [CharZero K] (P : Preorder K) :
    ¬ GCoincidence (Motion.ofFun (fun x : K => 2 * x)) (Motion.ofFun (fun n : ℕ∞ => n + 1)) P
      inferInstance 0 := by
  rintro ⟨φ, -, -, -, htop, hoff⟩
  have hf : ∀ x, φ.toFun (2 * x) = φ.toFun x + 1 := fun x => φ.map_step (a := x) (b := 2 * x) rfl
  have h0 : φ.toFun 0 = ⊤ := top_le_iff.1 (htop ⊤)
  exact no_doubling_valuation_field φ.toFun hf (fun x hx => by rw [← h0]; exact hoff x hx)

-- Statement: the control at ℝ.
example (P : Preorder ℝ) : ¬ GCoincidence (Motion.ofFun (fun x : ℝ => 2 * x))
    (Motion.ofFun (fun n : ℕ∞ => n + 1)) P inferInstance 0 := field_no_GCoincidence P
-- Statement: the control at `ℚ_[2]`.
example (P : Preorder ℚ_[2]) : ¬ GCoincidence (Motion.ofFun (fun x : ℚ_[2] => 2 * x))
    (Motion.ofFun (fun n : ℕ∞ => n + 1)) P inferInstance 0 := field_no_GCoincidence P

-- Statement: CONTROL: the constant map at ⊤ is a `Hom` between these two motions too.
example : ∃ φ : Motion.Hom (Motion.ofFun (fun x : ℤ_[2] => 2 * x))
    (Motion.ofFun (fun n : ℕ∞ => n + 1)), ∀ x, φ.toFun x = ⊤ :=
  ⟨⟨fun _ => ⊤, fun {_ _} _ => (top_add 1).symm, fun x => by simp [Motion.ofFun, Motion.ofTotal]⟩,
    fun _ => rfl⟩

/-! ## § III. The field lines of 2-adic doubling (ruling 84)

The line through a nonzero `x` of `ℚ_[2]` is `{2 ^ k * x | k : ℤ}`; its label is `x` with its power
of 2 removed. This is the standard decomposition `ℚ_p^× ≅ ⟨p⟩ × ℤ_p^×` at `p = 2` (A. Jenkins and
S. Spallone, arXiv:1011.2451v1, § 3.2, p. 7: "the basic decomposition Q_p^× ≅ <p> × Z_p^×"; cited in
`ZeroParadox/Multihomed/TwoAdicBend.md`); on ℤ_[2] the label is Mathlib's `PadicInt.unitCoeff` (the
`example` after `fieldLineLabel_of_norm_one`). The additions here are the `ℚ_[2]` form and the
reading of each line as a run between the shared ends 0 and ∞. -/

section FieldLines

/-- `Statement:` `‖2 ^ k‖ = 2 ^ (-k)` in `ℚ_[2]`. -/
theorem givens_norm_two_zpow (k : ℤ) : ‖(2 : ℚ_[2]) ^ k‖ = (2 : ℝ) ^ (-k) := by
  simpa using Padic.norm_p_zpow (p := 2) k

/-- `Statement:` `v(2) = 1` in `ℚ_[2]`. -/
theorem givens_valuation_two : (2 : ℚ_[2]).valuation = 1 := by
  simp

/-- `Statement:` the label of `x`: `x * 2 ^ (-v(x))`, `v` the 2-adic valuation. -/
noncomputable def fieldLineLabel (x : ℚ_[2]) : ℚ_[2] := x * (2 : ℚ_[2]) ^ (-x.valuation)

/-- `Statement:` `v(2 ^ k * x) = k + v(x)` for nonzero `x`. -/
theorem valuation_two_zpow_mul (k : ℤ) {x : ℚ_[2]} (hx : x ≠ 0) :
    ((2 : ℚ_[2]) ^ k * x).valuation = k + x.valuation := by
  rw [Padic.valuation_mul (zpow_ne_zero _ two_ne_zero) hx, Padic.valuation_zpow, givens_valuation_two]
  ring

/-- `Statement:` every point is a power of 2 times its label. -/
theorem fieldLine_decomp (x : ℚ_[2]) : x = (2 : ℚ_[2]) ^ x.valuation * fieldLineLabel x := by
  unfold fieldLineLabel
  rw [mul_comm x, ← mul_assoc, ← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero, one_mul]

/-- `Statement:` the label is constant along a line. -/
theorem fieldLineLabel_zpow_mul (k : ℤ) {x : ℚ_[2]} (hx : x ≠ 0) :
    fieldLineLabel ((2 : ℚ_[2]) ^ k * x) = fieldLineLabel x := by
  unfold fieldLineLabel
  have e : (2 : ℚ_[2]) ^ k * (2 : ℚ_[2]) ^ (-k) = 1 := by
    rw [← zpow_add₀ two_ne_zero, add_neg_cancel, zpow_zero]
  rw [valuation_two_zpow_mul k hx, neg_add, zpow_add₀ two_ne_zero]
  linear_combination (x * (2 : ℚ_[2]) ^ (-x.valuation)) * e

/-- `Statement:` two nonzero points lie on one line iff their labels agree; so two lines are equal
or disjoint. -/
theorem fieldLine_same_iff {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∃ k : ℤ, y = (2 : ℚ_[2]) ^ k * x) ↔ fieldLineLabel x = fieldLineLabel y := by
  constructor
  · rintro ⟨k, rfl⟩; exact (fieldLineLabel_zpow_mul k hx).symm
  · intro h
    refine ⟨y.valuation - x.valuation, ?_⟩
    have e : (2 : ℚ_[2]) ^ (y.valuation - x.valuation) * (2 : ℚ_[2]) ^ x.valuation =
        (2 : ℚ_[2]) ^ y.valuation := by
      rw [← zpow_add₀ two_ne_zero, sub_add_cancel]
    calc y = (2 : ℚ_[2]) ^ y.valuation * fieldLineLabel y := fieldLine_decomp y
      _ = (2 : ℚ_[2]) ^ (y.valuation - x.valuation) *
            ((2 : ℚ_[2]) ^ x.valuation * fieldLineLabel x) := by
          rw [← h, ← mul_assoc, e]
      _ = (2 : ℚ_[2]) ^ (y.valuation - x.valuation) * x := by rw [← fieldLine_decomp x]

/-- `Statement:` the label of a nonzero point has norm 1. -/
theorem norm_fieldLineLabel {x : ℚ_[2]} (hx : x ≠ 0) : ‖fieldLineLabel x‖ = 1 := by
  unfold fieldLineLabel
  rw [norm_mul, Padic.norm_eq_zpow_neg_valuation hx, givens_norm_two_zpow]
  push_cast
  rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp

/-- `Statement:` a point of norm 1 is its own label, so distinct units label distinct lines. -/
theorem fieldLineLabel_of_norm_one {u : ℚ_[2]} (hu : ‖u‖ = 1) : fieldLineLabel u = u := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  have hv : u.valuation = 0 := by
    have h := Padic.norm_eq_zpow_neg_valuation hu0
    rw [hu] at h
    have : (2 : ℝ) ^ (-u.valuation) = (2 : ℝ) ^ (0 : ℤ) := by push_cast at h; rw [← h]; simp
    have := zpow_right_injective₀ (by norm_num : (0 : ℝ) < 2) (by norm_num) this
    omega
  simp [fieldLineLabel, hv]

-- Statement: on nonzero `x` of ℤ_[2], the label is Mathlib's unit part `PadicInt.unitCoeff`.
example {x : ℤ_[2]} (hx : x ≠ 0) :
    fieldLineLabel (x : ℚ_[2]) = (PadicInt.unitCoeff hx : ℚ_[2]) := by
  have hs : (x : ℚ_[2]) = ((PadicInt.unitCoeff hx : ℤ_[2]) : ℚ_[2]) * (2 : ℚ_[2]) ^ x.valuation := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    rw [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast]
    norm_num
  have hn : ‖((PadicInt.unitCoeff hx : ℤ_[2]) : ℚ_[2])‖ = 1 := PadicInt.norm_units _
  have hu0 : ((PadicInt.unitCoeff hx : ℤ_[2]) : ℚ_[2]) ≠ 0 := by
    rintro h; rw [h, norm_zero] at hn; norm_num at hn
  rw [hs, mul_comm, ← zpow_natCast, fieldLineLabel_zpow_mul _ hu0, fieldLineLabel_of_norm_one hn]

/-- `Statement:` CONTROL: the lines through 1 and through 3 never meet. -/
theorem fieldLines_one_three_disjoint : ¬ ∃ k : ℤ, (3 : ℚ_[2]) = (2 : ℚ_[2]) ^ k * 1 := by
  rw [fieldLine_same_iff one_ne_zero (by norm_num), fieldLineLabel_of_norm_one (by simp),
    fieldLineLabel_of_norm_one]
  · norm_num
  · rw [show (3 : ℚ_[2]) = ((3 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_natCast_eq_one_iff]
    norm_num

/-- `Statement:` every line has the same two ends: forward it tends to 0 of `ℚ_[2]`, backward its
norm tends to infinity. -/
theorem fieldLine_two_ends {x : ℚ_[2]} (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n * x) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ‖(2 : ℚ_[2]) ^ (-(n : ℤ)) * x‖) atTop atTop := by
  refine ⟨node3_contracts_2adic x, ?_⟩
  have e : (fun n : ℕ => ‖(2 : ℚ_[2]) ^ (-(n : ℤ)) * x‖) = fun n : ℕ => (2 : ℝ) ^ n * ‖x‖ := by
    funext n; rw [norm_mul, givens_norm_two_zpow, neg_neg, zpow_natCast]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
    (norm_pos_iff.2 hx)

end FieldLines

/-! ## § IV. Given these, then -/

/-- `Statement:` given `GMinMax`'s max half (`p` the limit sink off `q`), UP unchanged along steps,
and a run from off `q` with no landing among its stages: the run closes at UP of its start, `p` is in
that closure, and the start `s 0` does not arrive at `p` (`¬ M.Arrives p (s 0)`, `Motion.Arrives`).
One way. -/
theorem given_then_fixed_destination {α : Type*} {M : Motion α} (hinv : M.UpStepInvariant)
    {p q : α} (hmax : lmSinkOf M p q) {s : ℕ → α} (hrun : M.IsRun s) (h0 : s 0 ≠ q)
    (hnl : ∀ n, ¬ M.IsLanding (s n)) :
    M.RunClosure s (M.up (s 0)) ∧ p ∈ M.up (s 0) ∧ ¬ M.Arrives p (s 0) :=
  ⟨⟨hrun, Motion.stageClosure_of_run hinv hrun hnl⟩, hmax _ h0,
   Motion.not_arrives_of_stageClosure hrun (Motion.stageClosure_of_run hinv hrun hnl) (hmax _ h0)⟩

/-- `Statement:` in both charts: the 2-adic field line from 2 closes at 0 of `ℚ_[2]`, the real one
at ∞ of `OnePoint ℝ`, and neither start (2) arrives at its closure point (`Arrives`). `Reading:` INVERSION of the destination across charts. -/
theorem fixed_destination_two_charts :
    (dblQ2.RunClosure (fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some 2))
        (dblQ2.up (OnePoint.some 2)) ∧
      OnePoint.some 0 ∈ dblQ2.up (OnePoint.some 2) ∧ ¬ dblQ2.Arrives (OnePoint.some 0) (OnePoint.some 2)) ∧
    (dblReal.RunClosure (fun n => (lmScale (2 : ℝ) two_ne_zero)^[n] (OnePoint.some 2))
        (dblReal.up (OnePoint.some 2)) ∧
      ∞ ∈ dblReal.up (OnePoint.some 2) ∧ ¬ dblReal.Arrives ∞ (OnePoint.some 2)) := by
  refine ⟨given_then_fixed_destination lm_upStepInvariant lm_dbl_sinkOf (lm_isRun _)
      (OnePoint.coe_ne_infty 2) (fun n h => ?_),
    given_then_fixed_destination lm_upStepInvariant lm_real_dipole.2.1 (lm_isRun _)
      (fun e => two_ne_zero (OnePoint.coe_injective e)) (fun n h => ?_)⟩
  · have hf := (lm_isLanding_iff _).1 h
    rw [lm_scale_iterate_some, lm_scale_some] at hf
    have h' := OnePoint.coe_injective hf
    have hz : (2 : ℚ_[2]) ^ n * 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) two_ne_zero
    exact hz (by linear_combination h')
  · have hf := (lm_isLanding_iff _).1 h
    rw [lm_scale_iterate_some, lm_scale_some] at hf
    have h' := OnePoint.coe_injective hf
    have hz : (2 : ℝ) ^ n * 2 ≠ 0 := by positivity
    exact hz (by linear_combination h')

open MeasureTheory in
/-- `Statement:` for `0 < p ≤ 1`, `trials p hp`-almost every tape gives a run of `slotMotion` from
`false` that eventually departs `false` (`∃ n, slotRun w n ≠ false`). Every tape gives a run; only the
eventual departure needs the measure. The first-step witness is `slot_leavesByRun`. -/
theorem slot_occurrence_ae (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ∀ᵐ w ∂(trials p hp), slotMotion.IsRun (slotRun w) ∧ slotRun w 0 = false ∧
      ∃ n, slotRun w n ≠ false := by
  filter_upwards [(ae_but_not_every p hp hp0).1] with w hw
  obtain ⟨n, hn⟩ := (slotRun_crosses_iff w).2.2 hw
  exact ⟨slotRun_isRun w, (slotRun_crosses_iff w).1, n, by rw [hn]; decide⟩

end ZeroParadox

section GivensIndex

/-! ### § IV (pointers). The results the givens feed, in their home files -/
#check @ZeroParadox.snap_ae_of_firstStep       -- Statement: `BotHasFirstStep L` and `0 < p ≤ 1` give, for almost every tape, a run from ⊥ of `L` whose first step covers ⊥ of `L`. One way.
#check @ZeroParadox.doubling_place_dichotomy   -- Statement: for rational `x ≠ 0`, `2ⁿx → 0` in `ℚ_[2]` and `|2ⁿx| → ∞` in ℝ.
#check @ZeroParadox.q2_zero_min_eq_max         -- Statement: 0 of `ℚ_[2]` steps only to itself under doubling and has least norm; its `cxQ2` is the supremum and greatest value along the field line `2 ^ (n + 1)`.
#check @ZeroParadox.tape_totality_two_faces    -- Statement: one maximum-entropy coin; for each prefix-free decoder, `fairTape`-almost every tape incompressible for it; ⊥ of `ℕ → Bool` not random, and in the closure of the random firing tapes.
#check @ZeroParadox.snap_arc_z2_loop           -- Statement: the tower's image starts at 0 of ℤ_[2], is nonzero from stage 1, and tends to that same 0.
#check @ZeroParadox.arc_q2Val                  -- Statement: `q2Val` of the arc is ⊤ of `ℕ∞` at stage 0, `n` at stage `n ≥ 1`, and tends to ⊤.

/-! ### § V. The limits (ruling 85) -/

/-- `Statement:` no run of doubling from 0 of `ℚ_[2]` leaves it at the first step
(`¬ GLeavesByRun dblQ2 (OnePoint.some 0)`). `Reading:` CARRIER, limit (a): 0 of `ℚ_[2]` meets
`GMinMax` under doubling (`q2_GMinMax`; a constant map meets it too, `const_GMinMax`), and departure
comes from another chart: at the first step (`machine_leavesByRun`, `slot_leavesByRun`), or eventually
on almost every tape (`slot_occurrence_ae`). -/
theorem ZeroParadox.q2_not_leavesByRun_zero :
    ¬ ZeroParadox.GLeavesByRun ZeroParadox.dblQ2 (OnePoint.some 0) := by
  rintro ⟨s, hs, h0, h1⟩
  have hstep : ZeroParadox.dblQ2.step (OnePoint.some 0) (s 1) := by rw [← h0]; exact hs 0
  exact h1 (ZeroParadox.lm_dbl_step_level.1.2 (s 1) hstep)

#check @ZeroParadox.machine_leavesByRun        -- Statement: LIMIT (a), departure from another chart: a run leaves `c₀`, ⊥ of `MachinePhase`.
#check @ZeroParadox.slot_occurrence_ae         -- Statement: LIMIT (a), departure from the tape chart: for `0 < p ≤ 1`, almost every tape's run eventually departs `false`; the first-step witness is `slot_leavesByRun`.
#check @ZeroParadox.snap_ae_of_firstStep       -- Statement: LIMIT (b): any `0 < p ≤ 1` with `BotHasFirstStep L` gives almost-every-run firing; complexity is not a hypothesis.
#check @ZeroParadox.never_fires_ae_zero        -- Statement: LIMIT (b), control: at `p = 0`, almost every tape fires nowhere.
#check @ZeroParadox.q2_arc_returnToStart       -- Statement: LIMIT (c): the run closure of the arc's tail contains the arc's start, the SAME 0 of `ℚ_[2]` (`GReturnToStart`).
#check @ZeroParadox.fieldLine_same_iff         -- Statement: LIMIT (c): along a route unique to its line: two lines are equal or disjoint.
#check @ZeroParadox.q2_double_covBy            -- Statement: LIMIT (c): each 2-adic doubling step from a nonzero point is a cover in the norm order; the value group is discrete (`q2_norm_image`).
#check @ZeroParadox.real_hlv_returnToStart     -- Statement: LIMIT (c), control: under real halving some sequence from 0 of ℝ also meets `GReturnToStart` (its tail's closure contains 0 of ℝ), through a dense value group (`real_norm_image`).

/-! ### § VI. The preconditions that stay hypotheses -/
#check @ZeroParadox.BotHasFirstStep            -- Statement: AX-B1's first-step form, a `Prop` on `L`, used as the hypothesis `hR1`.
#check @ZeroParadox.t_snap_given               -- Statement: CC-1 is the hypothesis `hcc1 : S 0 = bot`; occurrence at index 1 is `hocc`.
-- Statement: the coin `0 < p ≤ 1` is two hypotheses, `hp` and `hp0`, beside `hR1`.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (hR1 : ZeroParadox.BotHasFirstStep L)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :=
  ZeroParadox.snap_ae_of_firstStep hR1 p hp hp0
-- Statement: an ordered field is Archimedean iff every crossing probability strictly between 0 and 1
-- drives survival below every positive bound. Reading: CARRIER, so the coin is a real (Archimedean)
-- nonzero chance; repetition does its work in exactly those carriers.
#check @ZeroParadox.archimedean_iff_survival_eventually_lt
-- Statement: CONTROL: if no standard multiple `k • p` reaches 1, then at every standard `n` no
-- standard multiple of the accumulated crossing probability reaches 1. Standard `n` only.
#check @ZeroParadox.crossing_stays_infinitesimal

end GivensIndex

section PurityCheck
open ZeroParadox
#print axioms GDiscrete.reverse
#print axioms lm_not_corner
#print axioms lm_not_climb_not_loop
#print axioms lm_not_coverAtLanding
#print axioms lm_orbit_runClosure
#print axioms idUp_not_corner
#print axioms q2_double_covBy
#print axioms q2_GDiscrete
#print axioms q2_hlv_GDiscrete
#print axioms q2_not_GCoverAtLanding
#print axioms real_not_GDiscrete
#print axioms real_hlv_not_GDiscrete
#print axioms givens_log2_two_mul
#print axioms realExpView
#print axioms real_dbl_GDiscrete_expView
#print axioms q2_norm_image
#print axioms q2_norm_gap
#print axioms real_norm_image
#print axioms real_norm_dense
#print axioms real_hlv_returnToStart
#print axioms machine_GDiscrete
#print axioms machine_GCoverAtLanding
#print axioms ordinal_GDiscrete
#print axioms ordinal_GCoverAtLanding
#print axioms ordinal_tower_not_discrete
#print axioms upAndOver_GDiscrete
#print axioms upAndOver_GCoverAtLanding
#print axioms unit_not_GDiscrete
#print axioms sph_lt_iff
#print axioms q2_zero_not_firstStep
#print axioms real_GConnected
#print axioms q2_not_GConnected
#print axioms q2_not_GJoined
#print axioms givens_two_charts
#print axioms two_charts_snap
#print axioms no_homeo_sphere_real
#print axioms no_homeoIso_dblQ2_dblReal
#print axioms strictIso_zero_to_infty
#print axioms const_infty_hom
#print axioms q2_GMinMax
#print axioms q2_hlv_GMinMax
#print axioms real_GMinMax_infty
#print axioms real_not_GMinMax_zero
#print axioms real_hlv_GMinMax_zero
#print axioms ordinal_no_selfOnly
#print axioms const_GMinMax
#print axioms const_no_limit_partner
#print axioms q2_not_climb
#print axioms real_not_climb
#print axioms machine_not_corner
#print axioms ordinal_GClimbNotLoop
#print axioms upAndOver_GClimbNotLoop
#print axioms arcS_zero
#print axioms arcS_succ
#print axioms q2_arc_returnToStart
#print axioms real_dbl_no_return_zero
#print axioms ordinal_tower_no_return
#print axioms machine_leavesByRun
#print axioms ordinal_leavesByRun
#print axioms slot_leavesByRun
#print axioms q2Val_double
#print axioms z2_GCoincidence
#print axioms no_doubling_valuation_field
#print axioms field_no_GCoincidence
#print axioms doubling_counter_pow
#print axioms doubling_counter_zero
#print axioms doubling_counter_iff
#print axioms doubling_counter_iff_isHausdorff
#print axioms doubling_counter_two_ne_zero_not_isUnit
#print axioms no_doubling_valuation_field_any
#print axioms field_no_GCoincidence_any
#print axioms valuation_two_zpow_mul
#print axioms fieldLine_decomp
#print axioms fieldLineLabel_zpow_mul
#print axioms fieldLine_same_iff
#print axioms norm_fieldLineLabel
#print axioms fieldLineLabel_of_norm_one
#print axioms fieldLines_one_three_disjoint
#print axioms fieldLine_two_ends
#print axioms given_then_fixed_destination
#print axioms fixed_destination_two_charts
#print axioms slot_occurrence_ae
#print axioms q2_not_leavesByRun_zero
#print axioms givens_norm_two_zpow
#print axioms givens_valuation_two
#print axioms dblQ2
#print axioms hlvQ2
#print axioms dblReal
#print axioms hlvReal
#print axioms realSphNorm
#print axioms lmRealN
#print axioms GDiscrete
#print axioms GCoverAtLanding
#print axioms GConnected
#print axioms GJoined
#print axioms GMinMax
#print axioms GClimbNotLoop
#print axioms GReturnToStart
#print axioms GLeavesByRun
#print axioms GCoincidence
#print axioms GTwoCharts
#print axioms q2ValHom
#print axioms fieldLineLabel
end PurityCheck
