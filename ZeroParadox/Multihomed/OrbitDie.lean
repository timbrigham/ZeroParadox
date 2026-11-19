-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): three "doubling never lands" results (`padic_nat_no_orbit_correspondence`, `doubling_place_dichotomy`, `padic_markov_no_orbit_correspondence`) read as facts about die `Motion`s, each fit beside a failing control, with obstructions (not identities) through step-carrying maps. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Die
import ZeroParadox.Valuation.RateTransport
import ZeroParadox.Valuation.PlaceMetric
import ZeroParadox.Valuation.NuRateMatch
import ZeroParadox.Order.WellFoundedObstruct
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-!
# The orbit family in the die: three "never lands" results as motions, with controls

Experimental probe, not a finalized layer; results are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

I love that our older logic is folding so neatly into the new stuff. That's exactly what I was hoping this project would eventually be able to do. I wondered how much of our legacy content could use another pass, so we ranked it, and this family came out near the top.

---

Formal Overview (AI-assisted) and prior art: the ride-along `OrbitDie.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ## § 0. Die-level lemmas -/

/-- `Statement:` if every step into `y` starts at `y`, no point other than `y` arrives at `y`. A
    repackaging of `Motion.not_noEntry_of_arrives` (`ZeroParadox/Die.lean`). -/
theorem od_never_arrives {α : Type*} (M : Motion α) {y : α} (hF : ∀ a, M.step a y → a = y)
    {x : α} (hx : x ≠ y) : ¬ M.Arrives y x :=
  fun h => Motion.not_noEntry_of_arrives h hx hF

/-- `Statement:` a map carrying steps of `M` to steps of `N` sends every point with a path of steps
    to `y` onto `f y`, when every step of `N` into `f y` starts at `f y`. -/
theorem od_collapse {α β : Type*} {M : Motion α} {N : Motion β} (f : α → β)
    (hf : ∀ a b, M.step a b → N.step (f a) (f b)) {y : α}
    (hN : ∀ a, N.step a (f y) → a = f y) {x : α} (hx : Relation.ReflTransGen M.step x y) :
    f x = f y :=
  Motion.eq_of_reflTransGen_of_noEntry hN (hx.lift f (fun a b h => hf a b h))

/-- `Statement:` a step-carrying map sends a self-step at `y` to a self-step; if `y'` is the only
    self-stepping point of `N`, then `f y = y'`. -/
theorem od_selfstep_image {α β : Type*} {M : Motion α} {N : Motion β} (f : α → β)
    (hf : ∀ a b, M.step a b → N.step (f a) (f b)) {y : α} (hy : M.step y y) {y' : β}
    (hN : ∀ z, N.step z z → z = y') : f y = y' :=
  hN _ (hf y y hy)

/-- `Statement:` for function motions, carrying steps is Mathlib's `Function.Semiconj`; the
    `RelHom` form is `Motion.semiconj_iff_exists_relHom` (`ZeroParadox/Die.lean`). -/
example {α β : Type*} (g : α → α) (h : β → β) (f : α → β) :
    (∀ a b, (Motion.ofFun g).step a b → (Motion.ofFun h).step (f a) (f b)) ↔
      Function.Semiconj f g h :=
  ⟨fun H a => (H a (g a) rfl), fun H a b (hab : b = g a) => by
    show f b = h (f a); rw [hab]; exact H a⟩

/-- `Statement:` the function-motion case of `od_selfstep_image`'s first half is Mathlib's
    `Function.IsFixedPt.map`. -/
example {α β : Type*} {g : α → α} {h : β → β} {f : α → β} (hs : Function.Semiconj f g h) {y : α}
    (hy : Function.IsFixedPt g y) : Function.IsFixedPt h (f y) :=
  hy.map hs

/-! ## § I. `padic_nat_no_orbit_correspondence`: doubling on `Q₂` against halving on ℕ -/

/-- `Statement:` doubling on `Q₂`, as the function motion `z ↦ 2 * z`. -/
noncomputable def odDoubleQ2 : Motion Q₂ := Motion.ofFun (fun z : Q₂ => 2 * z)

/-- `Statement:` halving on ℕ as the source states it: UP `id`, OVER `b ≤ a / 2`. -/
def odHalveNat : Motion ℕ := Motion.ofTotal id (fun _ => rfl) (fun a b => b ≤ a / 2)

/-- `Statement:` halving on ℕ as the function motion `n ↦ n / 2`. -/
def odHalveNatFun : Motion ℕ := Motion.ofFun (fun n : ℕ => n / 2)

/-- `Statement:` the `n`-th iterate of doubling on `Q₂` is multiplication by `2 ^ n`. -/
theorem od_iter_double (x : Q₂) (n : ℕ) :
    (fun z : Q₂ => 2 * z)^[n] x = (2 : Q₂) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_assoc]

/-- `Statement:` the source's run hypothesis is `IsRun` of `odHalveNat`, by `Iff.rfl`. -/
theorem od_isRun_halve (a : ℕ → ℕ) : odHalveNat.IsRun a ↔ ∀ n, a (n + 1) ≤ a n / 2 := Iff.rfl

/-- `Statement:` the source's first conjunct, both directions: every orbit norm is positive iff `x`
    does not arrive at `0` of `Q₂` in the doubling motion. -/
theorem od_RT_padic_iff (x : Q₂) :
    (∀ n, 0 < ‖(2 : Q₂) ^ n * x‖) ↔ ¬ odDoubleQ2.Arrives 0 x := by
  rw [odDoubleQ2, Motion.arrives_ofFun_iff]
  simp only [od_iter_double, norm_pos_iff, ne_eq, not_exists]

/-- `Statement:` in the doubling motion on `Q₂`, every step into `0` starts at `0`, and `0` steps to
    itself only. -/
theorem od_double_noEntry : (∀ a, odDoubleQ2.step a 0 → a = 0) ∧ odDoubleQ2.SelfOnlyAt 0 :=
  ⟨fun a (ha : (0 : Q₂) = 2 * a) => (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero,
   (Motion.selfOnlyAt_ofFun_iff _ _).2 (mul_zero 2)⟩

/-- `Statement:` the fit: for `x ≠ 0`, `x` never arrives at `0` of `Q₂` in the doubling motion,
    from `od_never_arrives` and `od_double_noEntry` alone. -/
theorem od_RT_padic_fit (x : Q₂) (hx : x ≠ 0) : ¬ odDoubleQ2.Arrives 0 x :=
  od_never_arrives _ od_double_noEntry.1 hx

/-- `Statement:` CONTROL, same carrier: with the constant step to `0`, `1` arrives at `0` of `Q₂`. -/
theorem od_RT_padic_control : (Motion.ofFun (fun _ : Q₂ => (0 : Q₂))).Arrives 0 1 :=
  (Motion.arrives_ofFun_iff _ _ _).2 ⟨1, rfl⟩

/-- `Statement:` in `odHalveNat`, `0` steps to itself only. -/
theorem od_halve_selfOnly : odHalveNat.SelfOnlyAt 0 :=
  ⟨Nat.zero_le _, fun b (hb : b ≤ 0 / 2) => by simpa using hb⟩

/-- `Statement:` the source's second conjunct, from `od_halve_selfOnly` by
    `Motion.run_const_of_selfOnlyAt`: a halving run that reaches `0` stays at `0`. -/
theorem od_RT_nat_fit (a : ℕ → ℕ) (ha : odHalveNat.IsRun a) (k : ℕ) (hk : a k = 0) (m : ℕ) :
    a (k + m) = 0 :=
  Motion.run_const_of_selfOnlyAt od_halve_selfOnly (s := fun j => a (k + j))
    (fun j => by simpa [Nat.add_assoc] using ha (k + j)) (by simpa using hk) m

/-- `Statement:` beyond the source: every natural arrives at `0` in `odHalveNat`. -/
theorem od_halve_arrives (x : ℕ) : odHalveNat.Arrives 0 x :=
  Motion.arrives_of_acc (fun _ _ => ⟨0, Nat.zero_le _⟩)
    (Subrelation.accessible (r := (· < ·))
      (fun {b a} (h : a ≠ 0 ∧ b ≤ a / 2) => lt_of_le_of_lt h.2 (Nat.div_lt_self
        (Nat.pos_of_ne_zero h.1) (by norm_num)))
      (wellFounded_lt.apply x))

/-- `Statement:` every natural arrives at `0` in the function motion `n ↦ n / 2`. -/
theorem od_halveFun_arrives (x : ℕ) : odHalveNatFun.Arrives 0 x := by
  obtain ⟨N, hN⟩ := ZeroParadox.descent_with_strict_steps_reaches_floor
    (fun k => (fun n : ℕ => n / 2)^[k] x)
    (fun k hk => by
      show (fun n : ℕ => n / 2)^[k + 1] x < (fun n : ℕ => n / 2)^[k] x
      rw [Function.iterate_succ_apply']
      exact Nat.div_lt_self (Nat.pos_of_ne_zero hk) (by norm_num))
  exact (Motion.arrives_ofFun_iff _ _ _).2 ⟨N, hN⟩

/-- `Statement:` CONTROL, same carrier: with OVER `b ≤ a` (no halving), `0` still steps to itself
    only, and `1` does not arrive at `0`. -/
theorem od_RT_nat_control :
    let M := Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl) (fun a b => b ≤ a)
    M.SelfOnlyAt 0 ∧ ¬ M.Arrives 0 1 := by
  intro M
  refine ⟨⟨le_refl 0, fun b (hb : b ≤ 0) => Nat.le_zero.mp hb⟩, fun h => ?_⟩
  have key : ∀ x, M.Arrives 0 x → x = 1 → False := by
    intro x hx
    induction hx with
    | here => intro h; exact absurd h (by decide)
    | next _ _ ih => intro h; subst h; exact ih 1 (le_refl 1) rfl
  exact key 1 h rfl

/-- `Statement:` OBSTRUCTION, landing into never-landing: every map carrying `odHalveNat` steps to
    `odDoubleQ2` steps is `0`. It consumes, from the source, the self-step at `0` and the one-step
    path `n → 0`; from the target, that `0` of `Q₂` is the only fixed point and every step into it
    starts there. Nothing 2-adic: `od_RT_collapse_ring`. -/
theorem od_RT_collapse (f : ℕ → Q₂) (hf : ∀ a b, odHalveNat.step a b → odDoubleQ2.step (f a) (f b))
    (n : ℕ) : f n = 0 := by
  have h0 : f 0 = 0 := od_selfstep_image f hf od_halve_selfOnly.1
    (fun z (hz : z = 2 * z) => by linear_combination -hz)
  have hpath : Relation.ReflTransGen odHalveNat.step n 0 :=
    Relation.ReflTransGen.single (Nat.zero_le _)
  rw [od_collapse f hf (y := 0) (by rw [h0]; exact od_double_noEntry.1) hpath, h0]

/-- `Statement:` CARRIER — `od_RT_collapse` with target doubling on any commutative ring with no
    zero divisors in which `2 ≠ 0`. These hypotheses are sufficient; they are not shown necessary. -/
theorem od_RT_collapse_ring {K : Type*} [CommRing K] [NoZeroDivisors K] [NeZero (2 : K)]
    (f : ℕ → K)
    (hf : ∀ a b, odHalveNat.step a b → (Motion.ofFun (fun z : K => 2 * z)).step (f a) (f b))
    (n : ℕ) : f n = 0 := by
  have h0 : f 0 = 0 := od_selfstep_image f hf od_halve_selfOnly.1
    (fun z (hz : z = 2 * z) => by linear_combination -hz)
  have hN : ∀ a, (Motion.ofFun (fun z : K => 2 * z)).step a (f 0) → a = f 0 :=
    fun a (ha : f 0 = 2 * a) => by
      rw [h0] at ha ⊢; exact (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero
  rw [od_collapse f hf hN
    (Relation.ReflTransGen.single (show odHalveNat.step n 0 from Nat.zero_le _)), h0]

/-- `Statement:` `od_RT_collapse` is the `Q₂` instance of `od_RT_collapse_ring`. -/
example (f : ℕ → Q₂) (hf : ∀ a b, odHalveNat.step a b → odDoubleQ2.step (f a) (f b)) (n : ℕ) :
    f n = 0 :=
  od_RT_collapse_ring f hf n

/-- `Statement:` the same collapse through the function motion `n ↦ n / 2`, where the path to `0`
    is the whole descent (`od_halveFun_arrives`). -/
theorem od_RT_collapse_fun (f : ℕ → Q₂)
    (hf : ∀ a b, odHalveNatFun.step a b → odDoubleQ2.step (f a) (f b)) (n : ℕ) : f n = 0 := by
  have h0 : f 0 = 0 := od_selfstep_image f hf (show (0 : ℕ) = 0 / 2 from rfl)
    (fun z (hz : z = 2 * z) => by linear_combination -hz)
  rw [od_collapse f hf (y := 0) (by rw [h0]; exact od_double_noEntry.1)
    (Motion.reflTransGen_of_arrives (od_halveFun_arrives n)), h0]

/-- `Statement:` CONTROL, target side (OVER always true on `Q₂`): the cast carries every halving
    step and is not `0`; so `od_RT_collapse` consumes the target's no-entry at `0`. -/
theorem od_RT_collapse_control_target :
    (∀ a b, odHalveNat.step a b →
      (Motion.ofTotal (id : Q₂ → Q₂) (fun _ => rfl) (fun _ _ => True)).step (a : Q₂) (b : Q₂)) ∧
    ((1 : ℕ) : Q₂) ≠ 0 :=
  ⟨fun _ _ _ => trivial, by norm_num⟩

/-- `Statement:` CONTROL, source side (successor on ℕ, no path to `0`, no self-step): `n ↦ 2 ^ n`
    carries every step to a doubling step and is not `0`. -/
theorem od_RT_collapse_control_source :
    (∀ a b, (Motion.ofFun Nat.succ).step a b → odDoubleQ2.step ((2 : Q₂) ^ a) ((2 : Q₂) ^ b)) ∧
    (2 : Q₂) ^ 0 ≠ 0 := by
  refine ⟨fun a b (h : b = a + 1) => ?_, by norm_num⟩
  show (2 : Q₂) ^ b = 2 * 2 ^ a
  rw [h, pow_succ']

/-- `Statement:` REVERSED DIRECTION, never-landing into landing, is NOT obstructed:
    `z ↦ ⌊‖z‖⌋₊` carries doubling steps on `Q₂` to `odHalveNat` steps and is not `0`. This
    direction uses the 2-adic contraction `‖2 * a‖ = ‖a‖ / 2` (`padic_orbit_norm`). -/
theorem od_RT_reverse_map :
    (∀ a b, odDoubleQ2.step a b → odHalveNat.step ⌊‖a‖⌋₊ ⌊‖b‖⌋₊) ∧ ⌊‖(1 / 2 : Q₂)‖⌋₊ ≠ 0 := by
  refine ⟨fun a b (h : b = 2 * a) => ?_, ?_⟩
  · show ⌊‖b‖⌋₊ ≤ ⌊‖a‖⌋₊ / 2
    have hn : ‖b‖ = ‖a‖ / 2 := by
      rw [h]; have := padic_orbit_norm a 1; simp only [pow_one] at this; rw [this]
      norm_num [zpow_neg]; ring
    rw [hn, Nat.floor_div_ofNat]
  · have : ‖(1 / 2 : Q₂)‖ = 2 := by
      rw [norm_div, norm_one]
      have := padic_orbit_norm (1 : Q₂) 1
      simp only [pow_one, mul_one, norm_one] at this
      rw [this]; norm_num [zpow_neg]
    rw [this]; norm_num

/-! ## § II. `doubling_place_dichotomy`: doubling on `Q₂` against doubling on ℝ -/

/-- `Statement:` doubling on ℝ, as the function motion `z ↦ 2 * z`. -/
noncomputable def odDoubleR : Motion ℝ := Motion.ofFun (fun z : ℝ => 2 * z)

/-- `Statement:` INVARIANT — the same die shape at both places: for `x : ℚ`, `x ≠ 0`, the image of
    `x` arrives at `0` neither in `odDoubleQ2` nor in `odDoubleR`. -/
theorem od_PM_same_shape (x : ℚ) (hx : x ≠ 0) :
    ¬ odDoubleQ2.Arrives 0 (x : Q₂) ∧ ¬ odDoubleR.Arrives 0 (x : ℝ) :=
  ⟨od_never_arrives _ od_double_noEntry.1 (by exact_mod_cast hx),
   od_never_arrives _ (fun a (ha : (0 : ℝ) = 2 * a) =>
     (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero) (by exact_mod_cast hx)⟩

/-- `Statement:` both casts from doubling on ℚ carry steps to steps: the two halves share one
    source motion. -/
theorem od_PM_casts :
    (∀ a b, (Motion.ofFun (fun q : ℚ => 2 * q)).step a b → odDoubleQ2.step (a : Q₂) (b : Q₂)) ∧
    (∀ a b, (Motion.ofFun (fun q : ℚ => 2 * q)).step a b → odDoubleR.step (a : ℝ) (b : ℝ)) :=
  ⟨fun a b (h : b = 2 * a) => by show (b : Q₂) = 2 * (a : Q₂); rw [h]; push_cast; rfl,
   fun a b (h : b = 2 * a) => by show (b : ℝ) = 2 * (a : ℝ); rw [h]; push_cast; rfl⟩

/-- `Statement:` CARRIER — as DATA, in the order lifted along the norm: doubling lowers on `Q₂`
    (`StepLowers`) and raises on ℝ (`StepRaises`). -/
theorem od_PM_fit :
    @Motion.StepLowers Q₂ odDoubleQ2 (Preorder.lift (‖·‖ : Q₂ → ℝ)).toLE ∧
    @Motion.StepRaises ℝ odDoubleR (Preorder.lift (‖·‖ : ℝ → ℝ)).toLE := by
  refine ⟨fun x y (h : y = 2 * x) => ?_, fun x y (h : y = 2 * x) => ?_⟩
  · show ‖y‖ ≤ ‖x‖
    rw [h]; have := padic_orbit_norm x 1; simp only [pow_one] at this; rw [this]
    have : (2 : ℝ) ^ (-((1 : ℕ) : ℤ)) = 1 / 2 := by norm_num [zpow_neg]
    rw [this]; nlinarith [norm_nonneg x]
  · show ‖x‖ ≤ ‖y‖
    rw [h, norm_mul, Real.norm_two]; nlinarith [norm_nonneg x]

/-- `Statement:` CONTROL, same carriers: doubling does not raise on `Q₂`, and does not lower on ℝ. -/
theorem od_PM_control :
    ¬ @Motion.StepRaises Q₂ odDoubleQ2 (Preorder.lift (‖·‖ : Q₂ → ℝ)).toLE ∧
    ¬ @Motion.StepLowers ℝ odDoubleR (Preorder.lift (‖·‖ : ℝ → ℝ)).toLE := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : ‖(1 : Q₂)‖ ≤ ‖(2 : Q₂) * 1‖ := h 1 (2 * 1) rfl
    have := padic_orbit_norm (1 : Q₂) 1
    simp only [pow_one] at this; rw [this, norm_one] at h1
    norm_num [zpow_neg] at h1
  · have h1 : ‖(2 : ℝ) * 1‖ ≤ ‖(1 : ℝ)‖ := h 1 (2 * 1) rfl
    norm_num at h1

/-- `Statement:` OBSTRUCTION: a map `Q₂ → ℝ` carrying doubling steps to doubling steps and monotone
    for the two norm orders is `0`. It consumes the step square `f (2 * z) = 2 * f z`, the
    monotonicity, and the source's `StepLowers` (`od_PM_fit`, the 2-adic contraction); controls:
    `od_PM_collapse_control`, `od_PM_collapse_control_mono`. -/
theorem od_PM_collapse (f : Q₂ → ℝ) (hf : ∀ a b, odDoubleQ2.step a b → odDoubleR.step (f a) (f b))
    (hmono : ∀ a b : Q₂, ‖a‖ ≤ ‖b‖ → ‖f a‖ ≤ ‖f b‖) (z : Q₂) : f z = 0 := by
  have hs : f (2 * z) = 2 * f z := hf z (2 * z) rfl
  have hl : ‖f (2 * z)‖ ≤ ‖f z‖ := hmono _ _ (od_PM_fit.1 z (2 * z) rfl)
  rw [hs, norm_mul, Real.norm_two] at hl
  exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg (f z)]) (norm_nonneg _))

/-- `Statement:` INVARIANT under reversal of the direction of the map: a map ℝ → `Q₂` carrying
    doubling steps to doubling steps and monotone for the two norm orders is `0`. It consumes the
    source's `StepRaises` on ℝ and the target's contraction on `Q₂` (`padic_orbit_norm`). -/
theorem od_PM_collapse_rev (g : ℝ → Q₂) (hg : ∀ a b, odDoubleR.step a b → odDoubleQ2.step (g a) (g b))
    (hmono : ∀ a b : ℝ, ‖a‖ ≤ ‖b‖ → ‖g a‖ ≤ ‖g b‖) (z : ℝ) : g z = 0 := by
  have hs : g (2 * z) = 2 * g z := hg z (2 * z) rfl
  have hl : ‖g z‖ ≤ ‖g (2 * z)‖ := hmono _ _ (od_PM_fit.2 z (2 * z) rfl)
  rw [hs] at hl
  have := padic_orbit_norm (g z) 1; simp only [pow_one] at this; rw [this] at hl
  have h2 : (2 : ℝ) ^ (-((1 : ℕ) : ℤ)) = 1 / 2 := by norm_num [zpow_neg]
  rw [h2] at hl
  exact norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg (g z)]) (norm_nonneg _))

/-- `Statement:` CARRIER — `od_RT_collapse` with target `odDoubleR`: the collapse uses nothing
    2-adic. -/
theorem od_RT_collapse_real (f : ℕ → ℝ) (hf : ∀ a b, odHalveNat.step a b → odDoubleR.step (f a) (f b))
    (n : ℕ) : f n = 0 := by
  have h0 : f 0 = 0 := od_selfstep_image f hf od_halve_selfOnly.1
    (fun z (hz : z = 2 * z) => by linear_combination -hz)
  have hN : ∀ a, odDoubleR.step a (f 0) → a = f 0 := fun a (ha : f 0 = 2 * a) => by
    rw [h0] at ha ⊢; exact (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero
  rw [od_collapse f hf hN
    (Relation.ReflTransGen.single (show odHalveNat.step n 0 from Nat.zero_le _)), h0]

/-- `Statement:` CARRIER — CONTROL: with source ℝ in place of `Q₂`, the identity carries steps, is
    monotone, and is not `0`; so `od_PM_collapse` consumes the contraction on `Q₂`. -/
theorem od_PM_collapse_control :
    (∀ a b, odDoubleR.step a b → odDoubleR.step (id a) (id b)) ∧
    (∀ a b : ℝ, ‖a‖ ≤ ‖b‖ → ‖id a‖ ≤ ‖id b‖) ∧ id (1 : ℝ) ≠ 0 :=
  ⟨fun _ _ h => h, fun _ _ h => h, one_ne_zero⟩

/-- `Statement:` CONTROL for the monotonicity: `z ↦ ‖z‖⁻¹` carries doubling steps on `Q₂` to doubling
    steps on ℝ and is not `0`; so `od_PM_collapse` consumes its monotonicity hypothesis. -/
theorem od_PM_collapse_control_mono :
    (∀ a b, odDoubleQ2.step a b → odDoubleR.step ‖a‖⁻¹ ‖b‖⁻¹) ∧ ‖(1 : Q₂)‖⁻¹ ≠ 0 := by
  refine ⟨fun a b (h : b = 2 * a) => ?_, by simp⟩
  show ‖b‖⁻¹ = 2 * ‖a‖⁻¹
  have hn : ‖b‖ = ‖a‖ / 2 := by
    rw [h]; have := padic_orbit_norm a 1; simp only [pow_one] at this; rw [this]
    norm_num [zpow_neg]; ring
  rw [hn, inv_div, div_eq_mul_inv]

/-! ## § III. `padic_markov_no_orbit_correspondence`: doubling on `Q₂` against the Markov step -/

/-- `Statement:` the Markov step at `a = 1/4`, as a function motion on `Fin 2 → ℝ`. -/
noncomputable def odMarkov : Motion (Fin 2 → ℝ) := Motion.ofFun (markovStep (1 / 4))

/-- `Statement:` `v` is fixed by the Markov step at `a = 1/4` iff `imb v = 0`; both directions. -/
theorem od_markov_fixed_iff (v : Fin 2 → ℝ) : markovStep (1 / 4) v = v ↔ imb v = 0 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [markovStep, Matrix.cons_val_zero] at h0
    simp only [imb]; linarith
  · intro h
    simp only [imb] at h
    funext i; fin_cases i <;> simp [markovStep] <;> linarith

/-- `Statement:` in `odMarkov`, `v` steps to itself only iff `imb v = 0`. -/
theorem od_markov_selfOnly_iff (v : Fin 2 → ℝ) : odMarkov.SelfOnlyAt v ↔ imb v = 0 :=
  (Motion.selfOnlyAt_ofFun_iff _ _).trans (od_markov_fixed_iff v)

/-- `Statement:` in `odMarkov`, every step into a balanced `v` starts at `v`. -/
theorem od_markov_noEntry {v : Fin 2 → ℝ} (hv : imb v = 0) : ∀ w, odMarkov.step w v → w = v := by
  intro w (hw : v = markovStep (1 / 4) w)
  have hiw : imb w = 0 := by
    have := step_imb (1 / 4) w; rw [← hw, hv] at this; linarith
  rw [hw]; exact ((od_markov_fixed_iff w).2 hiw).symm

/-- `Statement:` the fit: the Markov step never lands either; an unbalanced start arrives at no
    balanced point. -/
theorem od_NM_markov_fit {x v : Fin 2 → ℝ} (hx : imb x ≠ 0) (hv : imb v = 0) : ¬ odMarkov.Arrives v x :=
  od_never_arrives _ (od_markov_noEntry hv) (fun e => hx (e ▸ hv))

/-- `Statement:` the source's Markov conjunct starts ON the balanced line, where every iterate is the
    start. -/
theorem od_NM_source_markov {v₀ : Fin 2 → ℝ} (hbal : imb v₀ = 0) (k : ℕ) :
    (markovStep (1 / 4))^[k] v₀ = v₀ :=
  Function.iterate_fixed ((od_markov_fixed_iff v₀).2 hbal) k

/-- `Statement:` CONTROL, same carrier: with the constant step to `unif`, the unbalanced `![1, 0]`
    arrives at `unif`. -/
theorem od_NM_markov_control :
    imb ![1, 0] ≠ 0 ∧ (Motion.ofFun (fun _ : Fin 2 → ℝ => unif)).Arrives unif ![1, 0] :=
  ⟨by simp [imb], (Motion.arrives_ofFun_iff _ _ _).2 ⟨1, rfl⟩⟩

/-- `Statement:` the map `z ↦ ![‖z‖, -‖z‖]` from `Q₂` to `Fin 2 → ℝ`. -/
noncomputable def odQ2toMarkov (z : Q₂) : Fin 2 → ℝ := ![‖z‖, -‖z‖]

/-- `Statement:` a strict map of motions (`Motion.Hom`) from `odDoubleQ2` to `odMarkov` with
    underlying map `odQ2toMarkov`; it uses the 2-adic contraction (`padic_orbit_norm`). -/
noncomputable def odQ2toMarkovHom : Motion.Hom odDoubleQ2 odMarkov where
  toFun := odQ2toMarkov
  map_step := by
    intro a b (h : b = 2 * a)
    show odQ2toMarkov b = markovStep (1 / 4) (odQ2toMarkov a)
    have hn : ‖b‖ = ‖a‖ / 2 := by
      rw [h]; have := padic_orbit_norm a 1; simp only [pow_one] at this; rw [this]
      norm_num [zpow_neg]; ring
    funext i; fin_cases i <;> simp [odQ2toMarkov, markovStep, hn] <;> ring
  map_up := fun x => by simp [odDoubleQ2, odMarkov, Motion.ofFun, Motion.ofTotal]

/-- `Statement:` `odQ2toMarkov x` is balanced iff `x = 0`; both directions. -/
theorem od_NM_hom_balance (x : Q₂) : imb (odQ2toMarkov x) = 0 ↔ x = 0 := by
  simp only [imb, odQ2toMarkov, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h; have : ‖x‖ = 0 := by linarith
    exact norm_eq_zero.mp this
  · intro h; subst h; simp

/-- `Statement:` CONTROL: at `a = 0` the same map does not carry the doubling step `1 → 2 * 1`. -/
theorem od_NM_hom_control :
    ¬ ∀ a b, odDoubleQ2.step a b → (Motion.ofFun (markovStep 0)).step (odQ2toMarkov a) (odQ2toMarkov b) := by
  intro H
  have h := congrFun (H 1 (2 * 1) rfl) 0
  simp only [odQ2toMarkov, markovStep, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have h2 : ‖(2 : Q₂) * 1‖ = 1 / 2 := by
    have := padic_orbit_norm (1 : Q₂) 1; simp only [pow_one] at this; rw [this]; norm_num [zpow_neg]
  rw [h2, norm_one] at h; norm_num at h

/-- `Statement:` OBSTRUCTION with the Markov target: a map carrying `odHalveNat` steps to `odMarkov`
    steps is constant at `f 0`. It consumes the self-step at `0` and the one-step path `n → 0` in
    the source, and the target's no-entry at a balanced point (`od_markov_noEntry`). -/
theorem od_NM_halve_collapse (f : ℕ → Fin 2 → ℝ)
    (hf : ∀ a b, odHalveNat.step a b → odMarkov.step (f a) (f b)) (n : ℕ) : f n = f 0 := by
  have hfix : markovStep (1 / 4) (f 0) = f 0 := (hf 0 0 (Nat.zero_le _)).symm
  exact od_collapse f hf (od_markov_noEntry ((od_markov_fixed_iff _).1 hfix))
    (Relation.ReflTransGen.single (Nat.zero_le _))

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms od_never_arrives
#print axioms od_collapse
#print axioms od_selfstep_image
#print axioms odDoubleQ2
#print axioms odHalveNat
#print axioms odHalveNatFun
#print axioms od_iter_double
#print axioms od_isRun_halve
#print axioms od_RT_padic_iff
#print axioms od_double_noEntry
#print axioms od_RT_padic_fit
#print axioms od_RT_padic_control
#print axioms od_halve_selfOnly
#print axioms od_RT_nat_fit
#print axioms od_halve_arrives
#print axioms od_halveFun_arrives
#print axioms od_RT_nat_control
#print axioms od_RT_collapse
#print axioms od_RT_collapse_ring
#print axioms od_RT_collapse_fun
#print axioms od_RT_collapse_control_target
#print axioms od_RT_collapse_control_source
#print axioms od_RT_reverse_map
#print axioms odDoubleR
#print axioms od_PM_same_shape
#print axioms od_PM_casts
#print axioms od_PM_fit
#print axioms od_PM_control
#print axioms od_PM_collapse
#print axioms od_PM_collapse_rev
#print axioms od_RT_collapse_real
#print axioms od_PM_collapse_control
#print axioms od_PM_collapse_control_mono
#print axioms odMarkov
#print axioms od_markov_fixed_iff
#print axioms od_markov_selfOnly_iff
#print axioms od_markov_noEntry
#print axioms od_NM_markov_fit
#print axioms od_NM_source_markov
#print axioms od_NM_markov_control
#print axioms odQ2toMarkov
#print axioms odQ2toMarkovHom
#print axioms od_NM_hom_balance
#print axioms od_NM_hom_control
#print axioms od_NM_halve_collapse
end PurityCheck
