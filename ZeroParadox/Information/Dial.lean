import ZeroParadox.Information.BottomTotality
import ZeroParadox.Information.StartBit
import ZeroParadox.Information.TwoRequirements
import ZeroParadox.Information.SnapEpsilonZero
import ZeroParadox.Valuation.UltrametricView
import ZeroParadox.Reals.ConnectedNoFirstStep
import ZeroParadox.Valuation.PadicCharacter
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Topology.Instances.ENat
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.Tactic

/-!
# The dial: the chance of changing state as the parameter `p` of `trials p hp`

## Engineer's Take

If we're using the tapes as representation, the bottom is the set set of all tapes including the all
zero, right? That's the infinite complexity of bottom... if we treat he likelihood the bottom's ability
to change state.. and we have that fixed zero for the all zero tape.. and then increment that ability to
change shape as one of the parameters as it moves outward.. to any non-zero values.. I might give us
something that we're lacking... This feels like an old mechanical dial that's both an on off switch and
a volume at the same time when I visualize it... This very seriously feels like a bridge between a
analog and a digital value

---

## Formal Overview (AI-assisted)
Switch (§ II): "some stage fires" has mass 0 at `p = 0`, 1 for `0 < p ≤ 1`. Volume (§ III): "fires within `n`
stages" is continuous in `p` and tends to the switch non-uniformly. § IV: the jump in `L`, the step-off mass, `Bool × ℕ∞ᵒᵈ` and its 2-adic norm form `Bool × N2`; § V-VI: schedules,
the law; § VII: mean of `wait + 1` is `p⁻¹`; § VIII: columns; § IX: entropy pins `0 < p < 1`; § X: translations;
§ XI: a Markov kernel on the die; § XII: lumping, reversibility under coarse-graining; § XIII: `cxQ2` as a gap count; § XIV: zoom-out on the 2-adic tower; § XV: the bands of `Int.log 2`. -/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory ProbabilityTheory Filter Topology

/-! ### § I. The one tape that never changes -/

/-- `Statement:` a tape never fires iff it is ⊥ of `ℕ → Bool`, the all-`false` tape; both
directions. The negated form of `exists_startBit_iff`. -/
theorem tape_never_fires_iff (w : ℕ → Bool) : (¬ ∃ k, w k = true) ↔ w = fun _ => false := by
  rw [exists_startBit_iff, not_not]; exact Iff.rfl

/-! ### § II. The switch -/

/-- `Statement:` the `trials p hp` mass of "some stage fires" is 0 at `p = 0` and 1 at every
`0 < p ≤ 1`. One is probability one: `{⊥}` of `ℕ → Bool` has mass 0 at every `0 < p ≤ 1`
(`trials_bot_mass_jump`), and ⊥ of `ℕ → Bool` is in the support only for `p < 1` (`bot_mem_support_iff`). -/
theorem dial_fire_jump (p : NNReal) (hp : p ≤ 1) :
    trials p hp {w | ∃ k, w k = true} = if p = 0 then 0 else 1 := by
  split_ifs with h0
  · subst h0
    have e : {w : ℕ → Bool | ∃ k, w k = true} = ⋃ k, fires k := by ext w; simp [fires]
    rw [e]
    exact measure_iUnion_null fun k => by rw [trials_fires]; simp
  · exact trials_fires_once p hp (pos_iff_ne_zero.2 h0)

/-- `Statement:` the mass of "some stage fires", total on `NNReal` by clamping `p` to `[0, 1]`. -/
noncomputable def fireMass (p : NNReal) : ENNReal :=
  trials (min p 1) (min_le_right _ _) {w | ∃ k, w k = true}

/-- `Statement:` `fireMass p` is 0 at `p = 0` and 1 at every `p > 0`. -/
theorem fireMass_eq (p : NNReal) : fireMass p = if p = 0 then 0 else 1 := by
  unfold fireMass; rw [dial_fire_jump]
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · simp [h, (lt_min (pos_iff_ne_zero.2 h) zero_lt_one).ne']

/-- `Statement:` `fireMass` is not continuous at `p = 0`. -/
theorem fireMass_not_continuousAt_zero : ¬ ContinuousAt fireMass 0 := by
  intro hc
  have hcl : (0 : NNReal) ∈ closure (Set.Ioi 0) := by
    rw [closure_Ioi' ⟨1, zero_lt_one⟩]; exact Set.mem_Ici.2 le_rfl
  have h := mem_closure_image hc hcl
  have himg : fireMass '' Set.Ioi 0 ⊆ {1} := by
    rintro _ ⟨p, hp, rfl⟩; rw [fireMass_eq]; simp [ne_of_gt (Set.mem_Ioi.1 hp)]
  have := closure_mono himg h
  rw [closure_singleton, fireMass_eq] at this
  simp at this

/-! ### § III. The volume, and the switch as its limit -/

/-- `Statement:` the clamped `trials` mass of "some stage below `n` fires". -/
noncomputable def fireWithin (n : ℕ) (p : NNReal) : ENNReal :=
  trials (min p 1) (min_le_right _ _) {w | ∃ k < n, w k = true}

/-- `Statement:` `fireWithin n p = 1 - (1 - min p 1) ^ n`, one minus `cylMass n p`. -/
theorem dial_fire_within (n : ℕ) (p : NNReal) :
    fireWithin n p = 1 - (((1 - min p 1 : NNReal)) : ENNReal) ^ n := by
  have e : {w : ℕ → Bool | ∃ k < n, w k = true} = (PiNat.cylinder (⊥ : ℕ → Bool) n)ᶜ := by
    ext w; simp [PiNat.cylinder]
  unfold fireWithin
  rw [e, prob_compl_eq_one_sub (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ n).measurableSet,
    ← cylMass_eq]
  rfl

/-- `Statement:` `fireWithin n` is continuous in `p`. -/
theorem fireWithin_continuous (n : ℕ) : Continuous (fireWithin n) := by
  have : fireWithin n = fun p => 1 - cylMass n p :=
    funext fun p => by rw [dial_fire_within, cylMass_eq]
  rw [this]
  exact (ENNReal.continuous_sub_left ENNReal.one_ne_top).comp (cylMass_continuous n)

/-- `Statement:` `fireWithin n` is monotone in `p`: a larger chance never lowers the mass of "some
stage below `n` fires". -/
theorem fireWithin_mono (n : ℕ) : Monotone (fireWithin n) := by
  intro p q hpq
  rw [dial_fire_within, dial_fire_within]
  apply tsub_le_tsub_left
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast tsub_le_tsub_left (min_le_min_right 1 hpq) 1

/-- `Statement:` for each `p`, `fireWithin n p` tends to `fireMass p` as `n → ∞`, the value 0 at
`p = 0` and 1 for `p > 0` (`fireMass_eq`). -/
theorem dial_digital_limit (p : NNReal) :
    Tendsto (fun n => fireWithin n p) atTop (𝓝 (fireMass p)) := by
  unfold fireMass fireWithin
  have e : {w : ℕ → Bool | ∃ k, w k = true} = ⋃ n, {w : ℕ → Bool | ∃ k < n, w k = true} := by
    ext w; simp only [Set.mem_iUnion]
    exact ⟨fun ⟨k, hk⟩ => ⟨k + 1, k, by omega, hk⟩, fun ⟨_, k, _, hk⟩ => ⟨k, hk⟩⟩
  rw [e]
  exact tendsto_measure_iUnion_atTop
    (fun a b hab w ⟨k, hk, hw⟩ => ⟨k, lt_of_lt_of_le hk hab, hw⟩)

/-- `Statement:` for every `n` some `0 < p ≤ 1` has `fireWithin n p < 1/2` and `fireMass p = 1`. -/
theorem dial_not_uniform_witness (n : ℕ) :
    ∃ p : NNReal, 0 < p ∧ p ≤ 1 ∧ fireWithin n p < 1/2 ∧ fireMass p = 1 := by
  have h0 : fireWithin n 0 = 0 := by rw [dial_fire_within]; simp
  have hev : ∀ᶠ p in 𝓝 (0 : NNReal), fireWithin n p < 1/2 ∧ p < 1 :=
    ((fireWithin_continuous n).tendsto 0).eventually
      (eventually_lt_nhds (by rw [h0]; norm_num)) |>.and (eventually_lt_nhds zero_lt_one)
  obtain ⟨p, ⟨hlt, hp1⟩, hp0⟩ :=
    ((hev.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))).and self_mem_nhdsWithin).exists
  exact ⟨p, hp0, hp1.le, hlt, by rw [fireMass_eq]; simp [ne_of_gt hp0]⟩

/-- `Statement:` the real values of `fireWithin n` do not converge uniformly to those of `fireMass`
on `(0, 1]`. -/
theorem dial_not_uniform :
    ¬ TendstoUniformlyOn (fun n p => (fireWithin n p).toReal) (fun p => (fireMass p).toReal)
      atTop (Set.Ioc 0 1) := by
  intro h
  rw [Metric.tendstoUniformlyOn_iff] at h
  obtain ⟨n, hn⟩ := (h (1/2) (by norm_num)).exists
  obtain ⟨p, hp0, hp1, hlt, hm⟩ := dial_not_uniform_witness n
  have hd := hn p ⟨hp0, hp1⟩
  have hx : (fireWithin n p).toReal < 1/2 := by
    have := ENNReal.toReal_strict_mono (by norm_num) hlt
    norm_num at this ⊢; exact this
  have hx0 : 0 ≤ (fireWithin n p).toReal := ENNReal.toReal_nonneg
  rw [hm, ENNReal.toReal_one, Real.dist_eq, abs_of_pos (by linarith)] at hd
  linarith

/-! ### § IV. The jump carried into `L` -/

/-- `Statement:` let `φ : Bool → L` send `false` to ⊥ of `L` and `true` elsewhere. Every image run
`φ ∘ slotRun w` starts at ⊥ of `L`; for `trials 0 hp`-almost every tape it is ⊥ of `L` at every stage;
for `0 < p ≤ 1` and `trials p hp`-almost every tape it is somewhere not ⊥ of `L`. From
`never_fires_ae_zero` and `ae_firesOnce`; on `firedRun` the third conjunct also follows from
`snap_ae_fixed_phi`, which adds detail (it names the first exit time). Maps
run tape → run → image; no map from ⊥ of `L` to a tape is claimed. -/
theorem dial_jump_into_L {L : Type*} [ZPSemilattice L] (φ : Bool → L)
    (hφ0 : φ false = ZPSemilattice.bot) (hφ1 : φ true ≠ ZPSemilattice.bot) :
    (∀ w, φ (slotRun w 0) = ZPSemilattice.bot) ∧
    (∀ hp : (0 : NNReal) ≤ 1, ∀ᵐ w ∂(trials 0 hp), ∀ n, φ (slotRun w n) = ZPSemilattice.bot) ∧
    (∀ (p : NNReal) (hp : p ≤ 1), 0 < p →
      ∀ᵐ w ∂(trials p hp), ∃ n, φ (slotRun w n) ≠ ZPSemilattice.bot) := by
  refine ⟨fun w => by rw [(slotRun_crosses_iff w).1]; exact hφ0, fun hp => ?_, fun p hp hp0 => ?_⟩
  · filter_upwards [never_fires_ae_zero hp] with w hw n
    have : slotRun w n = false := by
      rw [(tape_never_fires_iff w).1 hw]; simp [slotRun]
    rw [this, hφ0]
  · filter_upwards [ae_firesOnce p hp hp0] with w hw
    obtain ⟨n, hn⟩ := (slotRun_crosses_iff w).2.2 hw
    exact ⟨n, by rw [hn]; exact hφ1⟩

/-! #### § IV, the step-off event: one statement, the carrier `L` a coordinate of it -/

section StepOff

open ZPSemilattice

/-- `Statement:` the tapes that fire and drive, for some `φ : Bool → L`, a run `φ ∘ firedRun w hw`
that starts at ⊥ of `L`, moves at index 1, is a state sequence, and first moves to a cover of ⊥ of
`L` (covering relation in ZP-A's induced order): the event of `snap_ae_of_firstStep`. -/
def stepOff (L : Type*) [ZPSemilattice L] : Set (ℕ → Bool) :=
  {w | ∃ (φ : Bool → L) (hw : ∃ k, w k = true),
      let S := φ ∘ firedRun w hw
      (S 0 = bot ∧ S 1 ≠ S 0 ∧ IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (bot : L) ⋖ S 1)}

/-- `Statement:` if ⊥ of `L` has a first step, `stepOff L` is the set of tapes that fire. -/
theorem stepOff_of_firstStep {L : Type*} [ZPSemilattice L] (h : BotHasFirstStep L) :
    stepOff L = {w | ∃ k, w k = true} := by
  ext w
  constructor
  · rintro ⟨_, hw, _⟩; exact hw
  · intro hw
    obtain ⟨φ, hφ⟩ := snap_of_firstStep_fires_once h w hw
    exact ⟨φ, hw, hφ⟩

/-- `Statement:` if ⊥ of `L` has no first step, `stepOff L` is empty. -/
theorem stepOff_of_not_firstStep {L : Type*} [ZPSemilattice L] (h : ¬ BotHasFirstStep L) :
    stepOff L = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨φ, hw, -, -, hcov⟩
  exact h ⟨_, hcov⟩

open Classical in
/-- `Statement:` for every carrier `L`, no assumption beyond the `ZPSemilattice` structure: the
`trials p hp` mass of `stepOff L` is 1 if ⊥ of `L` has a first step and `p ≠ 0`, and 0 otherwise. -/
theorem stepOff_mass (L : Type*) [ZPSemilattice L] (p : NNReal) (hp : p ≤ 1) :
    trials p hp (stepOff L) = if BotHasFirstStep L ∧ p ≠ 0 then 1 else 0 := by
  by_cases h : BotHasFirstStep L
  · rw [stepOff_of_firstStep h, dial_fire_jump]
    by_cases h0 : p = 0 <;> simp [h, h0]
  · rw [stepOff_of_not_firstStep h]; simp [h]

/-- `Statement:` at `0 < p ≤ 1`, almost every tape is in `stepOff L` iff ⊥ of `L` has a first step;
both directions. -/
theorem stepOff_ae_iff (L : Type*) [ZPSemilattice L] (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    (∀ᵐ w ∂(trials p hp), w ∈ stepOff L) ↔ BotHasFirstStep L := by
  constructor
  · intro hae
    by_contra h
    rw [stepOff_of_not_firstStep h] at hae
    have : trials p hp Set.univ = 0 := by
      rw [ae_iff] at hae; simp at hae
    simp at this
  · intro h
    filter_upwards [snap_ae_of_firstStep h p hp hp0] with w hw
    exact hw

/-- `Statement:` on a linear order with a least element (join `max`, `linearMaxZPS`), the mass of
`stepOff` is 1 iff the order has an atom (Mathlib `IsAtom`, through `bot_covBy_iff`) and `p ≠ 0`. -/
theorem linear_stepOff_mass_one_iff {α : Type*} [LinearOrder α] [OrderBot α] (p : NNReal)
    (hp : p ≤ 1) :
    (trials p hp (@stepOff α (linearMaxZPS α ⊥ (fun _ => bot_le))) = 1) ↔
      ((∃ a : α, IsAtom a) ∧ p ≠ 0) := by
  classical
  rw [stepOff_mass, linearMaxZPS_botHasFirstStep_iff]
  have : HasFirstStep (⊥ : α) ↔ ∃ a : α, IsAtom a :=
    ⟨fun ⟨a, ha⟩ => ⟨a, bot_covBy_iff.1 ha⟩, fun ⟨a, ha⟩ => ⟨a, bot_covBy_iff.2 ha⟩⟩
  rw [this]
  split_ifs with hc <;> simp [hc]

/-- `Statement:` one way: on a densely ordered linear order with a least element, the mass of
`stepOff` is 0 at every `p`. The converse fails: `W` is not densely ordered (`W_not_dense`) and its
⊥ has no first step (`W_not_firstStep`). -/
theorem dense_stepOff_mass_zero {α : Type*} [LinearOrder α] [OrderBot α] [DenselyOrdered α]
    (p : NNReal) (hp : p ≤ 1) :
    trials p hp (@stepOff α (linearMaxZPS α ⊥ (fun _ => bot_le))) = 0 := by
  have h : ¬ @BotHasFirstStep α (linearMaxZPS α ⊥ (fun _ => bot_le)) := by
    rw [linearMaxZPS_botHasFirstStep_iff]
    exact axb1_fails_everywhere_iff_dense.mp inferInstance ⊥
  rw [@stepOff_of_not_firstStep α (linearMaxZPS α ⊥ (fun _ => bot_le)) h]; simp

section BoolC
attribute [local instance] boolOrZPS
-- Statement: CONTROL, on `Bool` (join `||`): the mass is 0 at `p = 0` and 1 otherwise.
example (p : NNReal) (hp : p ≤ 1) : trials p hp (stepOff Bool) = if p = 0 then 0 else 1 := by
  classical
  rw [stepOff_of_firstStep bool_botHasFirstStep, dial_fire_jump]
end BoolC

section NNRealC
attribute [local instance] nnrealMaxZPS
-- Statement: CONTROL, on `NNReal` (join `max`): the mass is 0 at every `p`.
example (p : NNReal) (hp : p ≤ 1) : trials p hp (stepOff NNReal) = 0 := by
  rw [stepOff_of_not_firstStep nnreal_not_botHasFirstStep]; simp
-- Statement: CONTROL, a run can still leave ⊥ of `NNReal` (to 1); it does not move to a cover of it.
example : ∃ (φ : Bool → NNReal) (hw : ∃ k, (fun _ => true : ℕ → Bool) k = true),
    (φ ∘ firedRun (fun _ => true) hw) 0 = bot ∧
    (φ ∘ firedRun (fun _ => true) hw) 1 ≠ (φ ∘ firedRun (fun _ => true) hw) 0 := by
  refine ⟨fun b => if b then 1 else 0, ⟨0, rfl⟩, ?_, ?_⟩
  · simp [(firedRun_spec (fun _ => true) ⟨0, rfl⟩).1]; rfl
  · simp [(firedRun_spec (fun _ => true) ⟨0, rfl⟩).1, (firedRun_spec (fun _ => true) ⟨0, rfl⟩).2 0]
end NNRealC

/-- `Statement:` the mass of `stepOff` is 0 in two settings with different runs: at `p = 0` on `Bool`
(join `||`) almost every tape never fires; at `0 < p ≤ 1` on `NNReal` (join `max`) almost every tape
fires. `Reading:` CARRIER, mass 0 alone does not tell the dial at 0 from ⊥ of the carrier having no
first step (⊥ of `Bool` has one, `bool_botHasFirstStep`; ⊥ of `NNReal` has none,
`nnreal_not_botHasFirstStep`). -/
theorem zero_mass_two_causes (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    (trials 0 zero_le_one (@stepOff Bool boolOrZPS) = 0 ∧
      ∀ᵐ w ∂(trials 0 zero_le_one), ¬ ∃ k, w k = true) ∧
    (trials p hp (@stepOff NNReal nnrealMaxZPS) = 0 ∧
      ∀ᵐ w ∂(trials p hp), ∃ k, w k = true) := by
  refine ⟨⟨?_, never_fires_ae_zero _⟩, ⟨?_, ae_firesOnce p hp hp0⟩⟩
  · rw [@stepOff_mass Bool boolOrZPS]; simp
  · rw [@stepOff_mass NNReal nnrealMaxZPS]; simp [nnreal_not_botHasFirstStep]

-- Statement: CONTROL, on `ℕ∞` (join `min`): the mass is 0 at every `p`.
example (p : NNReal) (hp : p ≤ 1) : trials p hp (stepOff ℕ∞) = 0 := by
  rw [stepOff_of_not_firstStep natInf_not_botHasFirstStep]; simp

-- Statement: CONTROL, on `Fin 3` (join `max`): ⊥ is covered by 1, and the mass is the switch.
example (p : NNReal) (hp : p ≤ 1) :
    trials p hp (@stepOff (Fin 3) (linearMaxZPS (Fin 3) ⊥ (fun _ => bot_le))) =
      if p = 0 then 0 else 1 := by
  have h : @BotHasFirstStep (Fin 3) (linearMaxZPS (Fin 3) ⊥ (fun _ => bot_le)) := by
    rw [linearMaxZPS_botHasFirstStep_iff]
    exact ⟨1, by decide, fun {c} h1 h2 => by revert c; decide⟩
  rw [@stepOff_of_firstStep (Fin 3) (linearMaxZPS (Fin 3) ⊥ (fun _ => bot_le)) h, dial_fire_jump]

-- Statement: CONTROL, on `Unit` under any `ZPSemilattice`: the mass is 0 at every `p`.
example [ZPSemilattice Unit] (p : NNReal) (hp : p ≤ 1) : trials p hp (stepOff Unit) = 0 := by
  have h : ¬ BotHasFirstStep Unit := by
    rintro ⟨a, ha⟩
    exact @LT.lt.ne Unit (zpSemilatticeSup Unit).toPreorder _ _ ha.1 (Subsingleton.elim _ _)
  rw [stepOff_of_not_firstStep h]; simp

/-- `Statement:` `WithTop (WithTop NNReal)`, the control carrier for `dense_stepOff_mass_zero`. -/
abbrev W := WithTop (WithTop NNReal)

/-- `Statement:` ⊥ of `W` has no first step. -/
theorem W_not_firstStep : ¬ HasFirstStep (⊥ : W) := by
  rintro ⟨a, h0a, hc⟩
  induction a using WithTop.recTopCoe with
  | top =>
    exact hc (c := (((1 : NNReal) : WithTop NNReal) : W)) (by
      show ((((0 : NNReal) : WithTop NNReal)) : W) < _
      exact WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 one_pos)) (WithTop.coe_lt_top _)
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top =>
      exact hc (c := (((1 : NNReal) : WithTop NNReal) : W)) (by
        show ((((0 : NNReal) : WithTop NNReal)) : W) < _
        exact WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 one_pos))
        (WithTop.coe_lt_coe.2 (WithTop.coe_lt_top _))
    | coe x =>
      have hx : (0 : NNReal) < x := by
        have : ((((0 : NNReal) : WithTop NNReal)) : W) < ((x : WithTop NNReal) : W) := h0a
        exact WithTop.coe_lt_coe.1 (WithTop.coe_lt_coe.1 this)
      exact hc (c := (((x / 2 : NNReal) : WithTop NNReal) : W))
        (by
          show ((((0 : NNReal) : WithTop NNReal)) : W) < _
          exact WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (half_pos hx)))
        (WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (half_lt_self hx)))

/-- `Statement:` `W` is not densely ordered: the inner ⊤ is covered by the outer ⊤. -/
theorem W_not_dense : ¬ DenselyOrdered W := by
  intro hd
  refine axb1_fails_everywhere_iff_dense.mp hd ((⊤ : WithTop NNReal) : W)
    ⟨⊤, WithTop.coe_lt_top _, fun {c} h1 h2 => ?_⟩
  induction c using WithTop.recTopCoe with
  | top => exact lt_irrefl _ h2
  | coe b => exact not_top_lt (WithTop.coe_lt_coe.1 h1)

-- Statement: CONTROL, on `W` (join `max`): the mass is 0 at every `p`, and `W` is not densely ordered.
example (p : NNReal) (hp : p ≤ 1) :
    trials p hp (@stepOff W (linearMaxZPS W ⊥ (fun _ => bot_le))) = 0 ∧ ¬ DenselyOrdered W := by
  refine ⟨?_, W_not_dense⟩
  have h : ¬ @BotHasFirstStep W (linearMaxZPS W ⊥ (fun _ => bot_le)) := by
    rw [linearMaxZPS_botHasFirstStep_iff]; exact W_not_firstStep
  rw [@stepOff_of_not_firstStep W (linearMaxZPS W ⊥ (fun _ => bot_le)) h]; simp

/-! #### § IV, one carrier whose ⊥ has a cover and is a limit: `Bool × ℕ∞ᵒᵈ` -/

section BoolNInf

open OrderDual

/-- `Statement:` the `ZPSemilattice` of a `SemilatticeSup` with `OrderBot`: join `⊔`, ⊥ its ⊥. A
definition, not an instance. -/
abbrev supBotZPS (α : Type*) [SemilatticeSup α] [OrderBot α] : ZPSemilattice α where
  join := (· ⊔ ·)
  bot := ⊥
  join_assoc := sup_assoc
  join_comm := sup_comm
  join_idem := sup_idem
  bot_join := bot_sup_eq

/-- `Statement:` under `supBotZPS`, ZP-A's induced `≤` is `α`'s own `≤`. -/
theorem supBotZPS_le_iff {α : Type*} [SemilatticeSup α] [OrderBot α] (x y : α) :
    @LE.le α (@zpSemilatticeSup α (supBotZPS α)).toLE x y ↔ x ≤ y := by
  show x ⊔ y = y ↔ x ≤ y
  exact sup_eq_right

/-- `Statement:` under `supBotZPS`, ZP-A's induced `<` is `α`'s own `<`. -/
theorem supBotZPS_lt_iff {α : Type*} [SemilatticeSup α] [OrderBot α] (x y : α) :
    @LT.lt α (@zpSemilatticeSup α (supBotZPS α)).toLT x y ↔ x < y := by
  rw [@lt_iff_le_not_ge α (@zpSemilatticeSup α (supBotZPS α)).toPreorder, lt_iff_le_not_ge,
    supBotZPS_le_iff, supBotZPS_le_iff]

/-- `Statement:` under `supBotZPS`, ZP-A's induced cover relation is `α`'s own `⋖`. -/
theorem supBotZPS_covBy_iff {α : Type*} [SemilatticeSup α] [OrderBot α] (x y : α) :
    @CovBy α (@zpSemilatticeSup α (supBotZPS α)).toLT x y ↔ x ⋖ y := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(supBotZPS_lt_iff _ _).1 h1, fun c hc1 hc2 =>
      h2 ((supBotZPS_lt_iff _ _).2 hc1) ((supBotZPS_lt_iff _ _).2 hc2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(supBotZPS_lt_iff _ _).2 h1, fun c hc1 hc2 =>
      h2 ((supBotZPS_lt_iff _ _).1 hc1) ((supBotZPS_lt_iff _ _).1 hc2)⟩

/-- `Statement:` `BotHasFirstStep` under `supBotZPS` iff `HasFirstStep ⊥` in `α`'s order. -/
theorem supBotZPS_botHasFirstStep_iff {α : Type*} [SemilatticeSup α] [OrderBot α] :
    @BotHasFirstStep α (supBotZPS α) ↔ HasFirstStep (⊥ : α) :=
  ⟨fun ⟨a, ha⟩ => ⟨a, (supBotZPS_covBy_iff _ _).1 ha⟩,
   fun ⟨a, ha⟩ => ⟨a, (supBotZPS_covBy_iff _ _).2 ha⟩⟩

/-- `Statement:` `ℕ∞ᵒᵈ`, the order dual of `ℕ∞`; its ⊥ is `toDual ⊤`, ⊤ of `ℕ∞`. -/
abbrev NInfDual := ℕ∞ᵒᵈ

/-- `Statement:` `Bool × ℕ∞ᵒᵈ` with Mathlib's product order; its ⊥ is `(false, toDual ⊤)`. -/
abbrev BoolNInfL := Bool × NInfDual

/-- `Statement:` ⊥ of `Bool × ℕ∞ᵒᵈ` is `(false, toDual ⊤)`, ⊤ of `ℕ∞` in the second slot. -/
theorem boolNInfL_bot_eq : (⊥ : BoolNInfL) = (false, toDual (⊤ : ℕ∞)) := rfl

/-- `Statement:` ⊥ of `Bool × ℕ∞ᵒᵈ` is covered by `(true, ⊥)`; product covers are Mathlib's
(`Prod.mk_covBy_mk_iff_left`, `Prod.covBy_iff`). -/
theorem boolNInfL_bot_covBy_true : (⊥ : BoolNInfL) ⋖ (true, ⊥) :=
  Prod.mk_covBy_mk_iff_left.2 (Bool.covBy_iff.2 (by decide))

/-- `Statement:` ⊥ of `Bool × ℕ∞ᵒᵈ` has a first step under `supBotZPS`. -/
theorem boolNInfL_botHasFirstStep : @BotHasFirstStep BoolNInfL (supBotZPS BoolNInfL) :=
  supBotZPS_botHasFirstStep_iff.2 ⟨_, boolNInfL_bot_covBy_true⟩

/-- `Statement:` on `Bool × ℕ∞ᵒᵈ` the mass of `stepOff` is 1 for `p ≠ 0` and 0 at `p = 0`. -/
theorem boolNInfL_stepOff_mass (p : NNReal) (hp : p ≤ 1) :
    trials p hp (@stepOff BoolNInfL (supBotZPS BoolNInfL)) = if p ≠ 0 then 1 else 0 := by
  rw [@stepOff_mass BoolNInfL (supBotZPS BoolNInfL)]
  simp [boolNInfL_botHasFirstStep]

/-- `Statement:` the run `n ↦ (false, toDual n)` in `Bool × ℕ∞ᵒᵈ`. -/
def nInfDualRun (n : ℕ) : BoolNInfL := (false, toDual (n : ℕ∞))

/-- `Statement:` no stage of `nInfDualRun` is ⊥ of `Bool × ℕ∞ᵒᵈ`. -/
theorem nInfDualRun_ne_bot (n : ℕ) : nInfDualRun n ≠ ⊥ := by
  intro h
  have := congrArg (fun x : BoolNInfL => ofDual x.2) h
  simp [nInfDualRun, boolNInfL_bot_eq] at this

/-- `Statement:` `nInfDualRun` is strictly decreasing. -/
theorem nInfDualRun_strictAnti : StrictAnti nInfDualRun := by
  intro m n hmn
  refine Prod.mk_lt_mk_iff_right.2 ?_
  exact toDual_lt_toDual.2 (by exact_mod_cast hmn)

/-- `Statement:` in `ℕ∞`, `n` is covered by `n + 1`. -/
theorem enat_natCast_covBy_succ (n : ℕ) : (n : ℕ∞) ⋖ ((n + 1 : ℕ) : ℕ∞) :=
  WithTop.coe_covBy_coe.2 (Order.covBy_add_one n)

/-- `Statement:` every step of `nInfDualRun` is a cover: stage `n + 1` is covered by stage `n`. -/
theorem nInfDualRun_covBy (n : ℕ) : nInfDualRun (n + 1) ⋖ nInfDualRun n :=
  Prod.mk_covBy_mk_iff_right.2 (toDual_covBy_toDual_iff.2 (enat_natCast_covBy_succ n))

/-- `Statement:` ⊥ of `Bool × ℕ∞ᵒᵈ` is the greatest lower bound of the stages of `nInfDualRun`. -/
theorem boolNInfL_bot_isGLB : IsGLB (Set.range nInfDualRun) (⊥ : BoolNInfL) := by
  refine ⟨fun _ _ => bot_le, fun l hl => ?_⟩
  have h2 : ∀ n : ℕ, (n : ℕ∞) ≤ ofDual l.2 := fun n => by
    have := (hl ⟨n, rfl⟩ : l ≤ nInfDualRun n).2
    exact this
  have htop : ofDual l.2 = ⊤ := ENat.eq_top_iff_forall_ge.2 h2
  have h1 : l.1 = false := by
    have h0 : l.1 ≤ false := (hl ⟨0, rfl⟩ : l ≤ nInfDualRun 0).1
    exact le_bot_iff.1 h0
  refine Prod.mk_le_mk.2 ⟨by simp [h1], ?_⟩
  show l.2 ≤ toDual (⊤ : ℕ∞)
  rw [← toDual_ofDual l.2, htop]

/-- `Statement:` `nInfDualRun` tends to ⊥ of `Bool × ℕ∞ᵒᵈ` in the product of the discrete topology on
`Bool` and the order topology on `ℕ∞ᵒᵈ`. -/
theorem nInfDualRun_tendsto : Tendsto nInfDualRun atTop (𝓝 (⊥ : BoolNInfL)) := by
  have hN : Tendsto (fun n : ℕ => toDual (n : ℕ∞)) atTop (𝓝 (toDual (⊤ : ℕ∞))) :=
    ENat.tendsto_natCast_nhds_top
  exact tendsto_const_nhds.prodMk_nhds hN

/-- `Statement:` no `(false, x)` covers ⊥ of `Bool × ℕ∞ᵒᵈ`: nothing covers ⊤ of `ℕ∞` from below. -/
theorem boolNInfL_no_nInfDual_cover (x : NInfDual) : ¬ (⊥ : BoolNInfL) ⋖ (false, x) := by
  intro h
  have hN : (⊥ : NInfDual) ⋖ x := Prod.mk_covBy_mk_iff_right.1 h
  have : ofDual x ⋖ (⊤ : ℕ∞) := by
    rw [← toDual_covBy_toDual_iff]; exact hN
  exact WithTop.not_covBy_top (α := ℕ) this

/-- `Statement:` the only cover of ⊥ of `Bool × ℕ∞ᵒᵈ` is `(true, ⊥)`; both directions. -/
theorem boolNInfL_bot_cover_unique (a : BoolNInfL) : (⊥ : BoolNInfL) ⋖ a ↔ a = (true, ⊥) := by
  constructor
  · intro h
    rcases Prod.covBy_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : a.1 = true := by
        have := Bool.covBy_iff.1 h1
        revert this; cases a.1 <;> simp
      ext
      · exact this
      · exact h2.symm
    · have ha : a = (false, a.2) := Prod.ext h2.symm rfl
      rw [ha] at h
      exact absurd h (boolNInfL_no_nInfDual_cover a.2)
  · rintro rfl; exact boolNInfL_bot_covBy_true

/-- `Statement:` ⊥ of `Bool × ℕ∞ᵒᵈ` has a first step, is the greatest lower bound and the limit of
`nInfDualRun`, a strictly decreasing run of covers avoiding it, and no `(false, x)` covers it.
`Reading:` CARRIER, both faces sit above ⊥ of `Bool × ℕ∞ᵒᵈ`, on two directions; at ε₀ of `Ordinal`
the limit face is below and the cover above. Both faces at one bottom force a non-linear order (one way);
non-linearity alone does not supply them (the `example` below; compare `preconnected_iff_no_firstStep`). -/
theorem boolNInfL_bot_cover_and_limit :
    (@BotHasFirstStep BoolNInfL (supBotZPS BoolNInfL)) ∧
    ((∀ n, nInfDualRun n ≠ ⊥) ∧ StrictAnti nInfDualRun ∧
      (∀ n, nInfDualRun (n + 1) ⋖ nInfDualRun n) ∧
      IsGLB (Set.range nInfDualRun) (⊥ : BoolNInfL) ∧
      Tendsto nInfDualRun atTop (𝓝 (⊥ : BoolNInfL))) ∧
    (∀ x : NInfDual, ¬ (⊥ : BoolNInfL) ⋖ (false, x)) :=
  ⟨boolNInfL_botHasFirstStep,
    ⟨nInfDualRun_ne_bot, nInfDualRun_strictAnti, nInfDualRun_covBy, boolNInfL_bot_isGLB,
      nInfDualRun_tendsto⟩, boolNInfL_no_nInfDual_cover⟩

-- Statement: on a linear order, if ⊥ is covered then no set avoiding ⊥ has ⊥ as greatest lower bound.
example {α : Type*} [LinearOrder α] [OrderBot α] {a : α} (ha : (⊥ : α) ⋖ a) (S : Set α)
    (hS : ∀ x ∈ S, x ≠ ⊥) : ¬ IsGLB S (⊥ : α) := fun h =>
  ha.lt.not_ge (h.2 fun x hx => not_lt.1 fun hx' => ha.2 (bot_lt_iff_ne_bot.2 (hS x hx)) hx')
-- Mathlib, the same exclusion: `IsGLB.isPredPrelimit_of_notMem` (order) and `CovBy.nhdsGT` (order topology).

/-- `Statement:` CONTROL, ⊥ of `ℕ∞ᵒᵈ` alone has no first step under `supBotZPS`. -/
theorem nInfDual_not_botHasFirstStep : ¬ @BotHasFirstStep NInfDual (supBotZPS NInfDual) := by
  rw [supBotZPS_botHasFirstStep_iff]
  rintro ⟨x, hx⟩
  have : ofDual x ⋖ (⊤ : ℕ∞) := by rw [← toDual_covBy_toDual_iff]; exact hx
  exact WithTop.not_covBy_top (α := ℕ) this

/-- `Statement:` CONTROL, on `ℕ∞ᵒᵈ` alone the mass of `stepOff` is 0 at every `p`. -/
theorem nInfDual_stepOff_mass (p : NNReal) (hp : p ≤ 1) :
    trials p hp (@stepOff NInfDual (supBotZPS NInfDual)) = 0 := by
  rw [@stepOff_mass NInfDual (supBotZPS NInfDual)]
  simp [nInfDual_not_botHasFirstStep]

/-- `Statement:` CONTROL, ⊥ of `ℕ∞ᵒᵈ` alone is the greatest lower bound of `n ↦ toDual n`. -/
theorem nInfDual_bot_isGLB : IsGLB (Set.range fun n : ℕ => toDual (n : ℕ∞)) (⊥ : NInfDual) := by
  refine ⟨fun _ _ => bot_le, fun l hl => ?_⟩
  have h2 : ∀ n : ℕ, (n : ℕ∞) ≤ ofDual l := fun n => (hl ⟨n, rfl⟩ : l ≤ toDual (n : ℕ∞))
  have htop : ofDual l = ⊤ := ENat.eq_top_iff_forall_ge.2 h2
  show l ≤ toDual (⊤ : ℕ∞)
  rw [← toDual_ofDual l, htop]

/-- `Statement:` CONTROL, no nonempty family avoiding ⊥ of `Bool` has ⊥ of `Bool` as greatest
lower bound. -/
theorem bool_bot_not_isGLB (ι : Type) [Nonempty ι] (t : ι → Bool) (ht : ∀ i, t i ≠ ⊥) :
    ¬ IsGLB (Set.range t) (⊥ : Bool) := by
  intro h
  have : (true : Bool) ∈ lowerBounds (Set.range t) := by
    rintro _ ⟨i, rfl⟩
    have := ht i
    revert this; cases t i <;> decide
  have := h.2 this
  exact absurd this (by decide)

-- Statement: ε₀ of `Ordinal` is a successor limit and is covered by its successor.
example : Order.IsSuccLimit (Ordinal.epsilon 0) ∧
    Ordinal.epsilon 0 ⋖ Order.succ (Ordinal.epsilon 0) := by
  refine ⟨?_, Order.covBy_succ _⟩
  refine Order.IsSuccLimit.mk (not_isMin_iff.2 ⟨0, Ordinal.epsilon_pos 0⟩) ?_
  rw [Ordinal.isSuccPrelimit_iff_omega0_dvd, ← Ordinal.omega0_opow_epsilon 0]
  simpa only [Ordinal.opow_one] using
    Ordinal.opow_dvd_opow Ordinal.omega0 (Order.one_le_iff_pos.2 (Ordinal.epsilon_pos 0))

-- Statement: ⊥ of `Bool × ℕ∞ᵒᵈ` is minimal and is not a successor limit.
example : IsMin (⊥ : BoolNInfL) ∧ ¬ Order.IsSuccLimit (⊥ : BoolNInfL) :=
  ⟨isMin_bot, fun h => h.not_isMin isMin_bot⟩

end BoolNInf

/-! #### § IV, the same carrier on the 2-adic norms: `Bool × N2` -/

section BoolN2

open OrderDual

/-- `Statement:` the norm image of ℤ_[2] in `ℝ≥0` (`q2_nnnorm_mem`, `normN2_surjective`). -/
def N2 : Set NNReal := {r | r = 0 ∨ ∃ n : ℕ, r = 2⁻¹ ^ n}

/-- `Statement:` ⊥ of `N2` is 0 of `ℝ≥0`. -/
instance n2OrderBot : OrderBot N2 where
  bot := ⟨0, Or.inl rfl⟩
  bot_le x := show (0 : NNReal) ≤ x.1 from zero_le

/-- `Statement:` the map `ℕ∞ → ℝ≥0` sending ⊤ of `ℕ∞` to 0 of `ℝ≥0` and `n` to `2⁻¹ ^ n`. -/
noncomputable def n2Pow (e : ℕ∞) : NNReal := if e = ⊤ then 0 else (2⁻¹ : NNReal) ^ e.toNat

/-- `Statement:` `n2Pow` sends ⊤ of `ℕ∞` to 0 of `ℝ≥0`. -/
theorem n2Pow_top : n2Pow ⊤ = 0 := by simp [n2Pow]

/-- `Statement:` `n2Pow n = 2⁻¹ ^ n` for `n : ℕ`. -/
theorem n2Pow_coe (n : ℕ) : n2Pow (n : ℕ∞) = (2⁻¹ : NNReal) ^ n := by simp [n2Pow]

/-- `Statement:` every value of `n2Pow` lies in `N2`. -/
theorem n2Pow_mem (e : ℕ∞) : n2Pow e ∈ N2 := by
  induction e using ENat.recTopCoe with
  | top => exact Or.inl n2Pow_top
  | coe n => exact Or.inr ⟨n, n2Pow_coe n⟩

/-- `Statement:` `n2Pow` is strictly antitone on `ℕ∞`. -/
theorem n2Pow_strictAnti : StrictAnti n2Pow := by
  intro a b hab
  induction b using ENat.recTopCoe with
  | top =>
    induction a using ENat.recTopCoe with
    | top => exact absurd hab (lt_irrefl _)
    | coe m => rw [n2Pow_top, n2Pow_coe]; exact pow_pos (by norm_num) m
  | coe n =>
    induction a using ENat.recTopCoe with
    | top => exact absurd hab (not_lt.2 le_top)
    | coe m =>
      rw [n2Pow_coe, n2Pow_coe]
      exact pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by exact_mod_cast hab)

/-- `Statement:` `ℕ∞ᵒᵈ ≃o N2`, sending `toDual n` to `2⁻¹ ^ n` and `toDual ⊤` (⊤ of `ℕ∞`) to 0 of
`ℝ≥0` (`e2_toDual_coe`, `e2_toDual_top`). Mathlib sibling with the same target `ℕ∞ᵒᵈ`:
`IsDiscreteValuationRing.idealOrderIsoENat` (the ideal side, ideal `(2 ^ n)` for norm `2⁻¹ ^ n`);
the value-group form: `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt`. The valuation
side, values in `ℕ ∪ {∞}` with `v(0) = ∞` and the nonzero ideals the chain `(p ^ m)`: A. V. Sutherland,
MIT 18.782 Lecture 4 (Fall 2013), Def. 4.10 and Thm. 4.16, pp. 3-4; Stacks Project tags 00IE, 00IH. -/
noncomputable def e2 : NInfDual ≃o N2 :=
  StrictMono.orderIsoOfSurjective (fun x => ⟨n2Pow (ofDual x), n2Pow_mem _⟩)
    (fun _ _ h => n2Pow_strictAnti h) (by
      rintro ⟨r, hr | ⟨n, rfl⟩⟩
      · exact ⟨toDual ⊤, Subtype.ext (by simp [n2Pow_top, hr])⟩
      · exact ⟨toDual (n : ℕ∞), Subtype.ext (by simp [n2Pow_coe])⟩)

/-- `Statement:` `e2` sends `toDual ⊤` (⊤ of `ℕ∞`) to ⊥ of `N2`, 0 of `ℝ≥0`. -/
theorem e2_toDual_top : e2 (toDual (⊤ : ℕ∞)) = ⊥ :=
  Subtype.ext (show n2Pow ⊤ = 0 from n2Pow_top)

/-- `Statement:` `e2` sends `toDual n` to `2⁻¹ ^ n`. -/
theorem e2_toDual_coe (n : ℕ) :
    e2 (toDual (n : ℕ∞)) = ⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩⟩ :=
  Subtype.ext (show n2Pow (n : ℕ∞) = _ from n2Pow_coe n)

/-- `Statement:` the norm of a nonzero `x : ℤ_[2]` is `2⁻¹ ^ x.valuation`; from Mathlib
`PadicInt.norm_eq_zpow_neg_valuation`. -/
theorem q2_nnnorm_eq_inv_pow (x : ℤ_[2]) (hx : x ≠ 0) :
    ‖x‖₊ = (2⁻¹ : NNReal) ^ x.valuation := by
  apply NNReal.eq
  rw [coe_nnnorm, PadicInt.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- `Statement:` the norm of every `x : ℤ_[2]`, 0 of ℤ_[2] included, lies in `N2`. -/
theorem q2_nnnorm_mem (x : ℤ_[2]) : ‖x‖₊ ∈ N2 := by
  by_cases hx : x = 0
  · exact Or.inl (by simp [hx])
  · exact Or.inr ⟨_, q2_nnnorm_eq_inv_pow x hx⟩

/-- `Statement:` the 2-adic norm on ℤ_[2], corestricted to `N2`. -/
noncomputable def normN2 (x : ℤ_[2]) : N2 := ⟨‖x‖₊, q2_nnnorm_mem x⟩

/-- `Statement:` `normN2 x = e2 (toDual (q2Val x))` for every `x : ℤ_[2]`, 0 of ℤ_[2] included. Its
order content, read on ℤ_[2], is `q2Val_le_iff_norm_le` (`ZeroParadox/Valuation/Scale.lean`). -/
theorem normN2_eq_e2_q2Val (x : ℤ_[2]) : normN2 x = e2 (toDual (q2Val x)) := by
  by_cases hx : x = 0
  · subst hx; rw [q2Val_bot, e2_toDual_top]; exact Subtype.ext (by simp [normN2]; rfl)
  · have hv : q2Val x = (x.valuation : ℕ∞) := by simp [q2Val, hx]
    rw [hv, e2_toDual_coe]; exact Subtype.ext (q2_nnnorm_eq_inv_pow x hx)

/-- `Statement:` `normN2` sends 0 of ℤ_[2] to ⊥ of `N2`. -/
theorem normN2_zero : normN2 0 = ⊥ := by rw [normN2_eq_e2_q2Val, q2Val_bot, e2_toDual_top]

/-- `Statement:` the run `n ↦ (false, 2⁻¹ ^ n)` in `Bool × N2`. -/
noncomputable def n2Run (n : ℕ) : Bool × N2 := (false, ⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩⟩)

/-- `Statement:` `n2Run n = (false, normN2 (2 ^ n))`: the second slot is the norm of `2 ^ n` in
ℤ_[2]; from Mathlib `PadicInt.norm_p_pow`. -/
theorem n2Run_eq_norm (n : ℕ) : n2Run n = (false, normN2 ((2 : ℤ_[2]) ^ n)) := by
  have h : ‖(2 : ℤ_[2]) ^ n‖₊ = (2⁻¹ : NNReal) ^ n := by
    apply NNReal.eq
    have := PadicInt.norm_p_pow (p := 2) n
    push_cast at this ⊢
    rw [this, zpow_neg, zpow_natCast, inv_pow]
  simp only [n2Run, normN2]
  congr 2
  exact h.symm

/-- `Statement:` `normN2` is onto `N2`. -/
theorem normN2_surjective : Function.Surjective normN2 := by
  rintro ⟨r, hr | ⟨n, rfl⟩⟩
  · exact ⟨0, by subst hr; rw [normN2_zero]; rfl⟩
  · exact ⟨(2 : ℤ_[2]) ^ n, (congrArg Prod.snd (n2Run_eq_norm n)).symm⟩

/-- `Statement:` `Bool × ℕ∞ᵒᵈ ≃o Bool × N2`, the identity on `Bool` and `e2` on the second slot. -/
noncomputable def boolN2Iso : BoolNInfL ≃o Bool × N2 where
  toEquiv := Equiv.prodCongr (Equiv.refl Bool) e2.toEquiv
  map_rel_iff' := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    show ((a1, e2 a2) : Bool × N2) ≤ (b1, e2 b2) ↔ (a1, a2) ≤ (b1, b2)
    rw [Prod.mk_le_mk, Prod.mk_le_mk, e2.le_iff_le]

/-- `Statement:` `boolNInfL_bot_cover_and_limit` carried along `boolN2Iso`: ⊥ of `Bool × N2`,
`(false, 0)`, has a first step, is the greatest lower bound and the limit of the strictly decreasing
run of covers `n2Run`, and no `(false, x)` covers it. The limit is in the product of the discrete
topology on `Bool` and the subspace topology of `N2` in `ℝ≥0`; the second slot of `n2Run n` is the
norm of `2 ^ n` in ℤ_[2] (`n2Run_eq_norm`). -/
theorem boolN2_bot_cover_and_limit :
    (@BotHasFirstStep (Bool × N2) (supBotZPS (Bool × N2))) ∧
    ((∀ n, n2Run n ≠ ⊥) ∧ StrictAnti n2Run ∧ (∀ n, n2Run (n + 1) ⋖ n2Run n) ∧
      IsGLB (Set.range n2Run) (⊥ : Bool × N2) ∧ Tendsto n2Run atTop (𝓝 (⊥ : Bool × N2))) ∧
    (∀ x : N2, ¬ (⊥ : Bool × N2) ⋖ (false, x)) := by
  obtain ⟨-, ⟨hne, hanti, hcov, hglb, -⟩, hno⟩ := boolNInfL_bot_cover_and_limit
  have hT : boolN2Iso (true, ⊥) = (true, ⊥) := by
    show ((true, e2 ⊥) : Bool × N2) = (true, ⊥); rw [e2.map_bot]
  have hrun : n2Run = boolN2Iso ∘ nInfDualRun := funext fun n => by
    show n2Run n = (false, e2 (toDual (n : ℕ∞))); rw [e2_toDual_coe]; rfl
  have hcov0 : (⊥ : Bool × N2) ⋖ (true, ⊥) := by
    have h := (apply_covBy_apply_iff boolN2Iso).2 boolNInfL_bot_covBy_true
    rwa [boolN2Iso.map_bot, hT] at h
  refine ⟨supBotZPS_botHasFirstStep_iff.2 ⟨_, hcov0⟩,
    ⟨fun n h => ?_, ?_, fun n => ?_, ?_, ?_⟩, fun x h => ?_⟩
  · rw [hrun, Function.comp_apply, ← boolN2Iso.map_bot] at h
    exact hne n (boolN2Iso.injective h)
  · rw [hrun]; exact boolN2Iso.strictMono.comp_strictAnti hanti
  · simp only [hrun, Function.comp_apply]; exact (apply_covBy_apply_iff boolN2Iso).2 (hcov n)
  · rw [hrun, Set.range_comp, ← boolN2Iso.map_bot]; exact boolN2Iso.isGLB_image'.2 hglb
  · have h2 : Tendsto (fun n : ℕ => (⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩⟩ : N2)) atTop
        (𝓝 (⊥ : N2)) := by
      rw [tendsto_subtype_rng]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one zero_le (by norm_num)
    exact tendsto_const_nhds.prodMk_nhds h2
  · obtain ⟨y, rfl⟩ := e2.surjective x
    have hF : boolN2Iso (false, y) = (false, e2 y) := rfl
    rw [← hF, ← boolN2Iso.map_bot, apply_covBy_apply_iff] at h
    exact hno y h

/-- `Statement:` on `Bool × N2` the mass of `stepOff` is the switch: 1 for `p ≠ 0`, 0 at `p = 0`. -/
theorem boolN2_stepOff_mass (p : NNReal) (hp : p ≤ 1) :
    trials p hp (@stepOff (Bool × N2) (supBotZPS (Bool × N2))) = if p ≠ 0 then 1 else 0 := by
  rw [@stepOff_mass (Bool × N2) (supBotZPS (Bool × N2))]
  simp [boolN2_bot_cover_and_limit.1]

-- Statement: CONTROL, ⊥ of `N2` alone has no first step, and the mass of `stepOff` is 0 at every `p`.
example (p : NNReal) (hp : p ≤ 1) : ¬ @BotHasFirstStep N2 (supBotZPS N2) ∧
    trials p hp (@stepOff N2 (supBotZPS N2)) = 0 := by
  have h : ¬ @BotHasFirstStep N2 (supBotZPS N2) := by
    rw [supBotZPS_botHasFirstStep_iff]
    rintro ⟨a, ha⟩
    apply nInfDual_not_botHasFirstStep
    rw [supBotZPS_botHasFirstStep_iff]
    refine ⟨e2.symm a, (apply_covBy_apply_iff e2).1 ?_⟩
    rw [e2.map_bot, e2.apply_symm_apply]; exact ha
  refine ⟨h, ?_⟩
  rw [@stepOff_of_not_firstStep N2 (supBotZPS N2) h]; simp

-- Statement: CONTROL, ⊥ of `N2` alone is still the greatest lower bound and the limit of `2⁻¹ ^ n`.
example : IsGLB (Set.range fun n : ℕ => (⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩⟩ : N2)) (⊥ : N2) ∧
    Tendsto (fun n : ℕ => (⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩⟩ : N2)) atTop (𝓝 (⊥ : N2)) := by
  refine ⟨?_, ?_⟩
  · have hr : (Set.range fun n : ℕ => (⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩⟩ : N2)) =
        e2 '' Set.range fun n : ℕ => toDual (n : ℕ∞) := by
      rw [← Set.range_comp]; congr 1
    rw [hr, ← e2.map_bot]; exact e2.isGLB_image'.2 nInfDual_bot_isGLB
  · rw [tendsto_subtype_rng]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one zero_le (by norm_num)

end BoolN2

end StepOff

/-! ### § V. A schedule of chances -/

/-- `Statement:` the stage events are independent under `fadingTrials q hq`. -/
theorem fadingTrials_fires_iIndepSet (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) :
    iIndepSet fires (fadingTrials q hq) := by
  have hc : iIndepFun (fun (i : ℕ) (w : ℕ → Bool) => w i) (fadingTrials q hq) := by
    unfold fadingTrials; exact iIndepFun_infinitePi (fun _ => measurable_id)
  rw [iIndepSet_iff_iIndepSets_singleton fires_measurable, iIndepSets_iff]
  intro S f hf
  have hrw : ∀ i ∈ S, f i = fires i := fun i hi => by simpa using hf i hi
  have h1 : (⋂ i ∈ S, f i) = ⋂ i ∈ S, fires i := by
    apply Set.iInter₂_congr; intro i hi; rw [hrw i hi]
  rw [h1, Finset.prod_congr rfl (fun i hi => by rw [hrw i hi])]
  exact hc.meas_biInter (fun i _ => fires_comap i)

/-- `Statement:` if `∑ q n = ∞`, "some stage fires" has `fadingTrials q hq` measure one. The second
Borel-Cantelli lemma, Mathlib `ProbabilityTheory.measure_limsup_eq_one`. -/
theorem schedule_fires_of_tsum_top (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1)
    (hs : ∑' n, (q n : ENNReal) = ⊤) :
    fadingTrials q hq {w | ∃ k, w k = true} = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← measure_limsup_eq_one fires_measurable (fadingTrials_fires_iIndepSet q hq)
    (by simpa only [fadingTrials_fires] using hs)]
  refine measure_mono fun w hw => ?_
  rw [mem_limsup_iff_frequently_mem] at hw
  obtain ⟨k, -, hk⟩ := hw.forall_exists_of_atTop 0
  exact ⟨k, hk⟩

/-- `Statement:` if ⊥ of `L` has a first step and `∑ q n = ∞`, then for `fadingTrials q hq`-almost
every tape `w`, `w` fires (`hw`) and `snap_of_firstStep_fires_once`'s conclusion holds: the run
steps off ⊥ of `L` to a cover. `snap_ae_of_firstStep` with `trials p hp` replaced by a schedule; from
`schedule_fires_of_tsum_top`. One way. -/
theorem schedule_snap_ae {L : Type*} [ZPSemilattice L] (hR1 : BotHasFirstStep L)
    (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) (hs : ∑' n, (q n : ENNReal) = ⊤) :
    ∀ᵐ w ∂(fadingTrials q hq), ∃ (φ : Bool → L) (hw : ∃ k, w k = true),
      let S := φ ∘ firedRun w hw
      (S 0 = ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧ ZPSemilattice.IsStateSequence S) ∧
      ((S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ ZPSemilattice.join (S 0) (S 1) = S 1) ∧
        letI := zpSemilatticeSup L; (ZPSemilattice.bot : L) ⋖ S 1) := by
  have hm : MeasurableSet {w : ℕ → Bool | ∃ k, w k = true} := by
    have e : {w : ℕ → Bool | ∃ k, w k = true} = ⋃ k, fires k := by ext w; simp [fires]
    rw [e]; exact MeasurableSet.iUnion fires_measurable
  have hfire : ∀ᵐ w ∂(fadingTrials q hq), w ∈ {w : ℕ → Bool | ∃ k, w k = true} :=
    (ae_iff_measure_eq hm.nullMeasurableSet).2
      (by rw [schedule_fires_of_tsum_top q hq hs, measure_univ])
  filter_upwards [hfire] with w hw
  obtain ⟨φ, h⟩ := snap_of_firstStep_fires_once hR1 w hw
  exact ⟨φ, hw, h⟩

set_option linter.deprecated false in
/-- `Statement:` if `∑ q n < ∞` and every `q n < 1`, the tapes on which no stage fires, `{⊥}` of
`ℕ → Bool`, have positive `fadingTrials q hq` measure. -/
theorem schedule_never_pos (q : ℕ → NNReal) (hq : ∀ n, q n ≤ 1) (hq1 : ∀ n, q n < 1)
    (hs : ∑' n, (q n : ENNReal) ≠ ⊤) :
    0 < fadingTrials q hq {w | ∀ k, w k = false} := by
  obtain ⟨N, hN⟩ := ((ENNReal.tendsto_sum_nat_add (fun n => (q n : ENNReal)) hs).eventually
    (eventually_lt_nhds zero_lt_one)).exists
  set μ := fadingTrials q hq with hμ
  set A : Set (ℕ → Bool) := ((Finset.range N : Finset ℕ) : Set ℕ).pi fun _ => {false} with hAdef
  set B : Set (ℕ → Bool) := ⋃ k, fires (k + N) with hBdef
  set PA := ∏ i ∈ Finset.range N, (PMF.bernoulli (q i) (hq i)).toMeasure {false} with hPAdef
  have hA : μ A = PA := by
    rw [hμ, hAdef, hPAdef, fadingTrials,
      Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  have hPA0 : PA ≠ 0 := by
    rw [hPAdef, Finset.prod_ne_zero_iff]; intro i _
    simp only [PMF.bernoulli, PMF.toMeasure_apply_fintype, Fintype.univ_bool,
      Set.indicator_singleton, Finset.sum_pi_single', Finset.mem_insert, Bool.false_eq_true,
      Finset.mem_singleton, or_true, ↓reduceIte, ne_eq]
    exact (tsub_pos_of_lt (by exact_mod_cast hq1 i)).ne'
  have hPAt : PA ≠ ⊤ := hA ▸ measure_ne_top μ A
  have hAk : ∀ k, μ (A ∩ fires (k + N)) ≤ q (k + N) * PA := fun k => by
    have hsub : A ∩ fires (k + N) ⊆
        ((insert (k + N) (Finset.range N) : Finset ℕ) : Set ℕ).pi
          (fun j => {decide (j = k + N)}) := by
      rintro w ⟨hw, hf⟩ j hj
      simp only [Finset.coe_insert, Finset.coe_range, Set.mem_insert_iff, Set.mem_Iio] at hj
      simp only [Set.mem_singleton_iff]
      rcases hj with rfl | hj
      · simpa [fires] using hf
      · rw [show w j = false from hw j (by simpa using hj)]
        symm; simp only [decide_eq_false_iff_not]; omega
    refine (measure_mono hsub).trans (le_of_eq ?_)
    rw [hμ, hPAdef, fadingTrials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _),
      Finset.prod_insert (by simp)]
    congr 1
    · simp [PMF.bernoulli]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have : decide (j = k + N) = false := by simp at hj; simp; omega
      rw [this]
  have hAB : μ (A ∩ B) < PA := by
    calc μ (A ∩ B) = μ (⋃ k, A ∩ fires (k + N)) := by rw [Set.inter_iUnion]
      _ ≤ ∑' k, μ (A ∩ fires (k + N)) := measure_iUnion_le _
      _ ≤ ∑' k, (q (k + N) : ENNReal) * PA := ENNReal.tsum_le_tsum hAk
      _ = (∑' k, (q (k + N) : ENNReal)) * PA := ENNReal.tsum_mul_right
      _ < 1 * PA := (ENNReal.mul_lt_mul_iff_left hPA0 hPAt).2 hN
      _ = PA := one_mul _
  have hsub : A \ (A ∩ B) ⊆ {w | ∀ k, w k = false} := by
    rintro w ⟨hwA, hwB⟩ k
    by_cases hk : k < N
    · exact hwA k (by simpa using hk)
    · by_contra hne
      have hkt : w k = true := by simpa using hne
      exact hwB ⟨hwA, Set.mem_iUnion.2 ⟨k - N, by
        show w (k - N + N) = true; rw [Nat.sub_add_cancel (by omega)]; exact hkt⟩⟩
  calc (0 : ENNReal) < PA - μ (A ∩ B) := tsub_pos_of_lt hAB
    _ = μ A - μ (A ∩ B) := by rw [hA]
    _ ≤ μ (A \ (A ∩ B)) := le_measure_sdiff
    _ ≤ μ {w | ∀ k, w k = false} := measure_mono hsub

/-- `Statement:` CONTROL, with `q n = (1/2) ^ (n + 2)` every stage chance is positive and the tapes
on which no stage fires have positive `fadingTrials` measure. -/
theorem schedule_halving_control :
    (∀ n, 0 < (1/2 : NNReal) ^ (n + 2)) ∧
    0 < fadingTrials (fun n => (1/2 : NNReal) ^ (n + 2))
      (fun n => pow_le_one₀ (by norm_num) (by norm_num)) {w | ∀ k, w k = false} := by
  refine ⟨fun n => pow_pos (by norm_num) _, schedule_never_pos _ _
    (fun n => pow_lt_one₀ (by norm_num) (by norm_num) (by omega)) ?_⟩
  exact ENNReal.tsum_coe_ne_top_iff_summable.2
    ((NNReal.summable_nat_add_iff 2).2 (NNReal.summable_geometric (by norm_num)))

/-! ### § VI. The fair coin's law: two faces -/

/-- `Statement:` exactly one `p : NNReal` has `binEntropy p = log 2`, and it lies in `(0, 1]`
(`tape_totality_two_faces`, first conjunct); and `binEntropy q ≤ log 2` for every real `q`
(Mathlib `Real.binEntropy_le_log_two`). `Reading:` the law minimal in description, one condition
fixing it, is the law maximal in entropy; no description length is measured. -/
theorem law_two_faces :
    (∃ p : NNReal, Real.binEntropy (p : ℝ) = Real.log 2 ∧ 0 < p ∧ p ≤ 1 ∧
        ∀ q : NNReal, Real.binEntropy (q : ℝ) = Real.log 2 → q = p) ∧
    ∀ q : ℝ, Real.binEntropy q ≤ Real.log 2 :=
  ⟨tape_totality_two_faces.1, fun _ => Real.binEntropy_le_log_two⟩

section WaitPackFaces

open NInf

/-! ### § VII. The wait chart: chance `p`, mean of `wait + 1` equal to `p⁻¹` -/

/-- `Statement:` for every tape `w`, counting the `k` with `w ∈ PiNat.cylinder ⊥ k` (first `k` stages
all `false`, ⊥ of `ℕ → Bool`) gives `waitENat (det w) + 1` in `ℝ≥0∞`: the tail-sum formula, pointwise. -/
theorem tsum_cylinder_bot_indicator (w : ℕ → Bool) :
    ∑' k : ℕ, (PiNat.cylinder (⊥ : ℕ → Bool) k).indicator (fun _ => (1 : ENNReal)) w =
      ((waitENat (det w) : ℕ∞) : ENNReal) + 1 := by
  have hmem : ∀ k, w ∈ PiNat.cylinder (⊥ : ℕ → Bool) k ↔ (k : ℕ∞) ≤ waitENat (det w) := fun k => by
    rw [natCast_le_waitENat_iff, ofNat_le_det_iff]; simp [PiNat.cylinder]
  have hterm : ∀ k, (PiNat.cylinder (⊥ : ℕ → Bool) k).indicator (fun _ => (1 : ENNReal)) w =
      if (k : ℕ∞) ≤ waitENat (det w) then 1 else 0 := fun k => by
    by_cases hk : (k : ℕ∞) ≤ waitENat (det w)
    · rw [ite_eq_left hk, Set.indicator_of_mem ((hmem k).2 hk)]
    · rw [ite_eq_right hk, Set.indicator_of_notMem (fun h => hk ((hmem k).1 h))]
  simp_rw [hterm]
  generalize waitENat (det w) = W
  induction W using ENat.recTopCoe with
  | top =>
    simp only [le_top, ite_true, ENat.toENNReal_top, top_add]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  | coe m =>
    rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun k hk => by
      simp only [Finset.mem_range, not_lt] at hk
      rw [ite_eq_right (by exact_mod_cast (show ¬ k ≤ m by omega))])]
    rw [Finset.sum_congr rfl (fun k hk => ite_eq_left (by
      simp only [Finset.mem_range] at hk; exact_mod_cast (show k ≤ m by omega)))]
    simp

/-- `Statement:` the mean of `wait + 1` (the shifted geometric count, stages up to and including the
first firing) under `trials p hp` is `p⁻¹` in `ℝ≥0∞`, every `p ≤ 1`; at `p = 0` it is ⊤ of `ℝ≥0∞`. -/
theorem lintegral_wait_succ (p : NNReal) (hp : p ≤ 1) :
    ∫⁻ w, (((waitENat (det w) : ℕ∞) : ENNReal) + 1) ∂(trials p hp) = (p : ENNReal)⁻¹ := by
  have hm : ∀ k, MeasurableSet (PiNat.cylinder (⊥ : ℕ → Bool) k) := fun k =>
    (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ k).measurableSet
  have hc : ∀ k, trials p hp (PiNat.cylinder (⊥ : ℕ → Bool) k) = ((1 - p : NNReal) : ENNReal) ^ k :=
    fun k => by
      rw [trials_cyl]
      have hb : ∀ i, (⊥ : ℕ → Bool) i = false := fun _ => rfl
      simp only [hb, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_range]
  rw [show (fun w : ℕ → Bool => ((waitENat (det w) : ℕ∞) : ENNReal) + 1) =
      fun w => ∑' k : ℕ, (PiNat.cylinder (⊥ : ℕ → Bool) k).indicator (fun _ => (1 : ENNReal)) w from
    funext fun w => (tsum_cylinder_bot_indicator w).symm]
  rw [lintegral_tsum (fun k => (measurable_const.indicator (hm k)).aemeasurable)]
  simp_rw [lintegral_indicator_const (hm _), one_mul, hc]
  rw [ENNReal.tsum_geometric, ← ENNReal.coe_one, ← ENNReal.coe_sub, tsub_tsub_cancel_of_le hp]

/-- `Statement:` the chart `x = p⁻¹`, Mathlib's `OrderIso.invENNReal`: for `x : ℝ≥0∞` with `1 ≤ x`, the
mean of `wait + 1` under `trials (x⁻¹).toNNReal` is `x`. -/
theorem lintegral_wait_succ_inv (x : ENNReal) (hx : 1 ≤ x) :
    ∫⁻ w, (((waitENat (det w) : ℕ∞) : ENNReal) + 1)
      ∂(trials (x⁻¹).toNNReal (by
          rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2
            (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))]
          simpa using ENNReal.inv_le_inv.2 hx)) = x := by
  rw [lintegral_wait_succ, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.2
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))), inv_inv]

-- Statement: `OrderIso.invENNReal` is `x ↦ x⁻¹`, read into the order dual.
example (x : ENNReal) : OrderDual.ofDual (OrderIso.invENNReal x) = x⁻¹ := rfl

/-- `Statement:` the endpoint: for `1 ≤ x`, `(x⁻¹).toNNReal = 0` iff `x = ⊤`; at `p = 0` the mean of
`wait + 1` is ⊤ of `ℝ≥0∞` and almost every tape never fires; ⊥ of `ℕ → Bool` has wait ⊤ of `ℕ∞`. -/
theorem wait_chart_top (x : ENNReal) (hx : 1 ≤ x) :
    ((x⁻¹).toNNReal = 0 ↔ x = ⊤) ∧
    (∀ hp : (0 : NNReal) ≤ 1,
      ∫⁻ w, (((waitENat (det w) : ℕ∞) : ENNReal) + 1) ∂(trials 0 hp) = ⊤ ∧
      ∀ᵐ w ∂(trials 0 hp), ¬ ∃ k, w k = true) ∧
    waitENat (det (⊥ : ℕ → Bool)) = ⊤ := by
  refine ⟨?_, fun hp => ⟨by rw [lintegral_wait_succ]; simp, never_fires_ae_zero hp⟩, wait_bot⟩
  rw [ENNReal.toNNReal_eq_zero_iff, ENNReal.inv_eq_zero, ENNReal.inv_eq_top]
  exact ⟨fun h => h.resolve_right (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)), Or.inl⟩

-- Statement: CONTROL `x = 1`: `p = 1`, stage 0 fires almost surely, and the mean of `wait + 1` is 1.
example : trials 1 le_rfl (fires 0) = 1 ∧
    ∫⁻ w, (((waitENat (det w) : ℕ∞) : ENNReal) + 1) ∂(trials 1 le_rfl) = 1 :=
  ⟨by rw [trials_fires]; simp, by rw [lintegral_wait_succ]; simp⟩

/-- `Statement:` the mean of `wait` (stages before the first firing) under `trials p hp` is `p⁻¹ - 1`
in `ℝ≥0∞`, every `p ≤ 1`: for `0 < p`, the geometric distribution's mean `(1 - p)/p`; at `p = 0`, ⊤
of `ℝ≥0∞`, where Mathlib's `ProbabilityTheory.geometricMeasure 0` is `Measure.dirac 0`, mean 0.
Sources and other libraries: `ZeroParadox/Information/Dial.md` § VII. -/
theorem lintegral_wait (p : NNReal) (hp : p ≤ 1) :
    ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials p hp) = (p : ENNReal)⁻¹ - 1 := by
  have h := lintegral_wait_succ p hp
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, one_mul] at h
  rw [← h, ENNReal.add_sub_cancel_right ENNReal.one_ne_top]

/-- `Statement:` if the means of `wait` under `trials p hp` and `trials q hq` agree, `p = q`. -/
theorem wait_mean_inj (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1)
    (h : ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials p hp) =
      ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials q hq)) : p = q := by
  rw [lintegral_wait, lintegral_wait] at h
  have h1p : (1 : ENNReal) ≤ (p : ENNReal)⁻¹ := ENNReal.one_le_inv.2 (by exact_mod_cast hp)
  have h1q : (1 : ENNReal) ≤ (q : ENNReal)⁻¹ := ENNReal.one_le_inv.2 (by exact_mod_cast hq)
  have hinv : (p : ENNReal)⁻¹ = (q : ENNReal)⁻¹ := by
    rw [← tsub_add_cancel_of_le h1p, ← tsub_add_cancel_of_le h1q, h]
  exact_mod_cast inv_inj.1 hinv

/-- `Statement:` every `y : ℝ≥0∞`, ⊤ included, is the mean of `wait` under `trials p hp` for some `p ≤ 1`. -/
theorem wait_mean_surj (y : ENNReal) :
    ∃ (p : NNReal) (hp : p ≤ 1),
      ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials p hp) = y := by
  have h1 : (1 : ENNReal) ≤ y + 1 := le_add_self
  have hne : (y + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (ne_of_gt (lt_of_lt_of_le zero_lt_one h1))
  refine ⟨((y + 1)⁻¹).toNNReal, ?_, ?_⟩
  · rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
    simp
  · rw [lintegral_wait, ENNReal.coe_toNNReal hne, inv_inv,
      ENNReal.add_sub_cancel_right ENNReal.one_ne_top]

/-- `Statement:` every `y : ℝ≥0∞` is the mean of `wait` at exactly one `p ≤ 1`
(`wait_mean_surj`, `wait_mean_inj`). -/
theorem wait_mean_existsUnique (y : ENNReal) :
    ∃! p : NNReal, ∃ hp : p ≤ 1,
      ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials p hp) = y := by
  obtain ⟨p, hp, h⟩ := wait_mean_surj y
  exact ⟨p, ⟨hp, h⟩, fun q ⟨hq, hq'⟩ => wait_mean_inj q p hq hp (hq'.trans h.symm)⟩

-- Statement: CONTROL `p = 1`: the mean of `wait` is 0.
example : ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials 1 le_rfl) = 0 := by
  rw [lintegral_wait]; simp
-- Statement: CONTROL `p = 0`: the mean of `wait` is ⊤ of `ℝ≥0∞`.
example (hp : (0 : NNReal) ≤ 1) :
    ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials 0 hp) = ⊤ := by
  rw [lintegral_wait]; simp
-- Statement: CONTROL `p = 1/2`: the mean of `wait` is 1.
example (hp : (1 / 2 : NNReal) ≤ 1) :
    ∫⁻ w, ((waitENat (det w) : ℕ∞) : ENNReal) ∂(trials (1 / 2) hp) = 1 := by
  rw [lintegral_wait]
  norm_num
  exact ENNReal.sub_eq_of_eq_add ENNReal.one_ne_top one_add_one_eq_two.symm

/-! ### § VIII. Packing: a tape of tapes at the same chance -/

/-- `Statement:` the columns of a tape along `Nat.pairEquiv`, a measurable equivalence
`(ℕ → Bool) ≃ᵐ (ℕ → ℕ → Bool)`. -/
def unpack : (ℕ → Bool) ≃ᵐ (ℕ → ℕ → Bool) :=
  (MeasurableEquiv.piCongrLeft (fun _ : ℕ × ℕ => Bool) Nat.pairEquiv.symm).trans
    (MeasurableEquiv.curry ℕ ℕ Bool)

/-- `Statement:` `unpack w i j = w (Nat.pair i j)`. -/
theorem unpack_apply (w : ℕ → Bool) (i j : ℕ) : unpack w i j = w (Nat.pair i j) := by
  show (MeasurableEquiv.piCongrLeft (fun _ : ℕ × ℕ => Bool) Nat.pairEquiv.symm w) (i, j) = _
  have h : ((i, j) : ℕ × ℕ) = Nat.pairEquiv.symm (Nat.pair i j) := (Nat.unpair_pair i j).symm
  rw [h, MeasurableEquiv.piCongrLeft_apply_apply]

-- Statement: through `tapeIso`, column `i` of `unpack` is `natDirsOrderIso`'s direction `i`.
example (x : End) (i : ℕ) : unpack (tapeIso x) i = tapeIso (natDirsOrderIso x i) :=
  funext fun j => by rw [unpack_apply]; rfl

set_option linter.deprecated false in
/-- `Statement:` `unpack` is measure preserving from `trials p hp` to the product of countably many
copies of `trials p hp`, every `p ≤ 1`. -/
theorem unpack_measurePreserving (p : NNReal) (hp : p ≤ 1) :
    MeasurePreserving unpack (trials p hp) (Measure.infinitePi fun _ : ℕ => trials p hp) := by
  refine ⟨unpack.measurable, ?_⟩
  unfold unpack trials
  rw [MeasurableEquiv.coe_trans, ← Measure.map_map (MeasurableEquiv.measurable _)
    (MeasurableEquiv.measurable _)]
  rw [Measure.infinitePi_map_piCongrLeft
    (fun _ : ℕ × ℕ => (PMF.bernoulli p hp).toMeasure) Nat.pairEquiv.symm]
  exact Measure.infinitePi_map_curry (fun _ _ => (PMF.bernoulli p hp).toMeasure)

/-- `Statement:` and `unpack.symm` is measure preserving back. -/
theorem pack_measurePreserving (p : NNReal) (hp : p ≤ 1) :
    MeasurePreserving unpack.symm (Measure.infinitePi fun _ : ℕ => trials p hp) (trials p hp) :=
  (unpack_measurePreserving p hp).symm _

-- Statement: CONTROL, a law whose stages differ: for the Dirac law at the tape firing only at stage 0,
-- `unpack` is not measure preserving onto the product of copies of it.
example : ¬ MeasurePreserving unpack (Measure.dirac (fun k => decide (k = 0)))
    (Measure.infinitePi fun _ : ℕ => Measure.dirac (fun k : ℕ => decide (k = 0))) := by
  intro h
  have hs0 : MeasurableSet {f : ℕ → Bool | f 0 = true} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have hs : MeasurableSet {y : ℕ → ℕ → Bool | y 1 0 = true} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp (measurable_pi_apply 1)) measurable_const
  have e := congrArg (fun ν : Measure (ℕ → ℕ → Bool) => ν {y | y 1 0 = true}) h.map_eq
  have hr : {y : ℕ → ℕ → Bool | y 1 0 = true} = (fun y => y 1) ⁻¹' {f | f 0 = true} := rfl
  rw [Measure.map_apply unpack.measurable hs, Measure.dirac_apply' _ (unpack.measurable hs), hr,
    ← Measure.map_apply (measurable_pi_apply 1) hs0, Measure.infinitePi_map_eval,
    Measure.dirac_apply' _ hs0] at e
  have h1 : (fun k : ℕ => decide (k = 0)) ∉
      unpack ⁻¹' ((fun y => y 1) ⁻¹' {f : ℕ → Bool | f 0 = true}) := by
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, unpack_apply]; decide
  have h2 : (fun k : ℕ => decide (k = 0)) ∈ {f : ℕ → Bool | f 0 = true} := rfl
  rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2] at e
  simp at e

/-! ### § IX. Positive entropy pins the dial -/

/-- `Statement:` for `p ≤ 1`, `binEntropy p > 0` iff `0 < p < 1`; both directions. -/
theorem dial_entropy_pos_iff (p : NNReal) (hp : p ≤ 1) :
    0 < Real.binEntropy (p : ℝ) ↔ 0 < p ∧ p < 1 := by
  constructor
  · intro h
    refine ⟨pos_iff_ne_zero.2 fun h0 => ?_, lt_of_le_of_ne hp fun h1 => ?_⟩
    · subst h0; simp at h
    · subst h1; simp at h
  · rintro ⟨h0, h1⟩
    exact Real.binEntropy_pos (by exact_mod_cast h0) (by exact_mod_cast h1)

/-- `Statement:` if `binEntropy p > 0`, ⊥ of `ℕ → Bool` is in the support of `trials p hp`; one way
(the `p = 0` CONTROL below refutes the converse). -/
theorem bot_mem_support_of_entropy_pos (p : NNReal) (hp : p ≤ 1)
    (h : 0 < Real.binEntropy (p : ℝ)) : (⊥ : ℕ → Bool) ∈ (trials p hp).support :=
  (bot_mem_support_iff p hp).2 ((dial_entropy_pos_iff p hp).1 h).2

/-- `Statement:` ⊥ of `ℕ → Bool` is in the support of `trials p hp` and `binEntropy p > 0` iff
`0 < p < 1`; the support conjunct is implied by the entropy one (`bot_mem_support_of_entropy_pos`). -/
theorem dial_two_faces_iff (p : NNReal) (hp : p ≤ 1) :
    ((⊥ : ℕ → Bool) ∈ (trials p hp).support ∧ 0 < Real.binEntropy (p : ℝ)) ↔ 0 < p ∧ p < 1 := by
  rw [← dial_entropy_pos_iff p hp]
  exact ⟨And.right, fun h => ⟨bot_mem_support_of_entropy_pos p hp h, h⟩⟩

/-- `Statement:` if `0 < p < 1`, every tape `t` is in the support of `trials p hp` and `{t}` is
`trials p hp`-null: full support and no atoms. -/
theorem trials_support_null (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℕ → Bool) : t ∈ (trials p hp).support ∧ trials p hp {t} = 0 := by
  refine ⟨by rw [trials_support_univ p hp hp0 hp1]; trivial, ?_⟩
  set m : NNReal := max p (1 - p) with hm
  have hm1 : m < 1 := max_lt hp1 (tsub_lt_self zero_lt_one hp0)
  have hle : ∀ n : ℕ, trials p hp {t} ≤ (m : ENNReal) ^ n := fun n => by
    have hsub : ({t} : Set (ℕ → Bool)) ⊆ PiNat.cylinder t n := fun w hw => by
      rw [Set.mem_singleton_iff] at hw; subst hw; exact PiNat.self_mem_cylinder _ _
    refine (measure_mono hsub).trans ?_
    rw [trials_cyl]
    refine (Finset.prod_le_prod (s := Finset.range n) (g := fun _ => (m : ENNReal))
      fun i _ => ?_).trans (by rw [Finset.prod_const, Finset.card_range])
    split_ifs
    · exact_mod_cast le_max_left _ _
    · exact_mod_cast le_max_right _ _
  have ht : Tendsto (fun n : ℕ => (m : ENNReal) ^ n) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by exact_mod_cast hm1)
  exact le_antisymm (ge_of_tendsto' ht hle) zero_le

-- Statement: CONTROL `p = 0`: `{⊥}` of `ℕ → Bool` has `trials 0` mass 1, an atom.
example : trials 0 zero_le_one {(⊥ : ℕ → Bool)} = 1 := by
  rw [trials_zero_eq_dirac]; exact Measure.dirac_apply_of_mem (Set.mem_singleton _)

/-- `Statement:` if `binEntropy p > 0`, "some stage fires" has `trials p hp` mass 1
(`dial_fire_jump`), and every tape, ⊥ of `ℕ → Bool` among them, is in the support and null
(`trials_support_null`). No conjunct singles out ⊥ of `ℕ → Bool`; the `example` after the
CONTROLs states what does. -/
theorem dial_pinned_faces (p : NNReal) (hp : p ≤ 1) (h : 0 < Real.binEntropy (p : ℝ)) :
    trials p hp {w | ∃ k, w k = true} = 1 ∧
      ∀ t : ℕ → Bool, t ∈ (trials p hp).support ∧ trials p hp {t} = 0 := by
  obtain ⟨h0, h1⟩ := (dial_entropy_pos_iff p hp).1 h
  exact ⟨by rw [dial_fire_jump, ite_eq_right h0.ne'], trials_support_null p hp h0 h1⟩

-- Statement: CONTROL `p = 0`: ⊥ of `ℕ → Bool` in the support, entropy 0; the converse of
-- `bot_mem_support_of_entropy_pos` fails.
example : (⊥ : ℕ → Bool) ∈ (trials 0 zero_le_one).support ∧
    Real.binEntropy ((0 : NNReal) : ℝ) = 0 :=
  ⟨(bot_mem_support_iff 0 _).2 zero_lt_one, by simp⟩

-- Statement: CONTROL `p = 1`: entropy 0, ⊥ of `ℕ → Bool` not in the support, firing of mass 1; it
-- meets neither conjunct of `dial_two_faces_iff`, so firing of mass 1 does not give positive entropy.
example : (⊥ : ℕ → Bool) ∉ (trials 1 le_rfl).support ∧ Real.binEntropy ((1 : NNReal) : ℝ) = 0 ∧
    trials 1 le_rfl {w | ∃ k, w k = true} = 1 :=
  ⟨by rw [bot_mem_support_iff]; exact lt_irrefl 1, by simp,
    by rw [dial_fire_jump, ite_eq_right one_ne_zero]⟩

-- Statement: what singles out ⊥ of `ℕ → Bool`, at every `p`: the least tape in the pointwise order
-- (`bot_le`), the only never-firing tape (`tape_never_fires_iff`), the only tape with wait ⊤ of
-- `ℕ∞` (`wait_bot`; converse via `natCast_le_waitENat_iff`).
-- Reading: (Tim's) ⊥ simultaneously minimally and maximally complex; the complexity rate of
-- `trials p` tapes is `brudno_ae_trials` (`ZeroParadox/Information/BrudnoBridge.lean`).
example (w : ℕ → Bool) : (⊥ : ℕ → Bool) ≤ w ∧ ((¬ ∃ k, w k = true) ↔ w = fun _ => false) ∧
    (waitENat (det w) = ⊤ ↔ w = ⊥) := by
  refine ⟨bot_le, tape_never_fires_iff w, fun h => ?_, fun h => h ▸ wait_bot⟩
  funext k
  have h1 : ((k + 1 : ℕ) : ℕ∞) ≤ waitENat (det w) := by rw [h]; exact le_top
  rw [natCast_le_waitENat_iff, ofNat_le_det_iff] at h1
  exact h1 k (Nat.lt_succ_self k)

/-! ### § X. Translation in the Cantor group

`Reading:` every tape is a local bottom. Proved: `xorOffset t` sends `t` to ⊥ of `ℕ → Bool`
(`xorOffset_bot`), so `t` is least in the pointwise order transported along `xorOffset t` (the
`example` after the not-monotone CONTROL); for `t` not ⊥ of `ℕ → Bool`, `xorOffset t` does not
preserve the pointwise order (that CONTROL). -/

/-- `Statement:` translation by `t` under pointwise `xor` (the compact group `(ℤ/2ℤ)^ℕ`): `xorHomeo t`
(`ZeroParadox/Valuation/UltrametricView.lean`) as a measurable equivalence. -/
noncomputable def xorOffset (t : ℕ → Bool) : (ℕ → Bool) ≃ᵐ (ℕ → Bool) :=
  (xorHomeo t).toMeasurableEquiv

/-- `Statement:` `xorOffset t w n = xor (t n) (w n)`. -/
theorem xorOffset_apply (t w : ℕ → Bool) (n : ℕ) : xorOffset t w n = xor (t n) (w n) := rfl

/-- `Statement:` `xorOffset t` sends ⊥ of `ℕ → Bool` to `t` and `t` to ⊥ of `ℕ → Bool`, and is its
own inverse. -/
theorem xorOffset_bot (t : ℕ → Bool) :
    xorOffset t ⊥ = t ∧ xorOffset t t = ⊥ ∧ Function.Involutive (xorOffset t) :=
  ⟨funext fun n => by rw [xorOffset_apply]; simp, funext fun n => by rw [xorOffset_apply]; simp,
    xorWith_involutive t⟩

-- Statement: CONTROL, for `t` not ⊥ of `ℕ → Bool`, `xorOffset t` does not preserve the pointwise
-- order (not monotone): it sends the pair ⊥ of `ℕ → Bool` ≤ `t` to `t` and ⊥ of `ℕ → Bool`
-- (`xorOffset_bot`).
example (t : ℕ → Bool) (ht : t ≠ ⊥) : ¬ Monotone (xorOffset t) := fun h => by
  have := h (bot_le : (⊥ : ℕ → Bool) ≤ t)
  rw [(xorOffset_bot t).1, (xorOffset_bot t).2.1] at this
  exact ht (le_bot_iff.1 this)

-- Statement: `t` is least in the pointwise order transported along `xorOffset t`.
example (t w : ℕ → Bool) : xorOffset t t ≤ xorOffset t w := by
  rw [(xorOffset_bot t).2.1]; exact bot_le

/-- `Statement:` the wait of `xorOffset t w` is the first disagreement of `w` with `t`:
`det (xorOffset t w) = ofNat n` iff `w n ≠ t n` and `w k = t k` for every `k < n`. -/
theorem det_xorOffset_eq_ofNat_iff (t w : ℕ → Bool) (n : ℕ) :
    det (xorOffset t w) = ofNat n ↔ w n ≠ t n ∧ ∀ k < n, w k = t k := by
  rw [det_eq_ofNat_iff]
  simp only [xorOffset_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => by rw [h] at h1; simp at h1, fun k hk => ?_⟩
    have := h2 k hk
    cases ht : t k <;> cases hw : w k <;> simp_all
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun k hk => by rw [h2 k hk]; simp⟩
    cases ht : t n <;> cases hw : w n <;> simp_all

set_option linter.deprecated false in
/-- `Statement:` `xorOffset t` preserves `fairTape` for every tape `t`: the fair coin is invariant
under every translation. -/
theorem xorOffset_measurePreserving_fair (t : ℕ → Bool) :
    MeasurePreserving (xorOffset t) fairTape fairTape := by
  have hT : (PMF.bernoulli (1/2) (by norm_num)).toMeasure.map (xor true) =
      (PMF.bernoulli (1/2) (by norm_num)).toMeasure := by
    ext s hs
    rw [Measure.map_apply (measurable_of_finite _) hs, PMF.toMeasure_apply_fintype,
      PMF.toMeasure_apply_fintype, Fintype.sum_bool, Fintype.sum_bool]
    by_cases h1 : true ∈ s <;> by_cases h0 : false ∈ s <;> simp [h1, h0, PMF.bernoulli_apply]
  have hF : (xor false : Bool → Bool) = id := funext fun b => Bool.false_xor b
  refine ⟨(xorOffset t).measurable, ?_⟩
  show Measure.map (fun w i => xor (t i) (w i)) (trials (1/2) _) = trials (1/2) _
  unfold trials
  rw [Measure.infinitePi_map_pi _ (fun i => measurable_of_finite _)]
  congr 1; funext i
  cases t i
  · rw [hF, Measure.map_id]
  · exact hT

/-- `Statement:` under `fairTape`, the wait to the first disagreement with `t` has the law of the wait
from ⊥ of `ℕ → Bool`: the two masses agree on every set `S` of values in `ℕ∞`. -/
theorem fair_wait_offset (t : ℕ → Bool) (S : Set ℕ∞) :
    fairTape {w | waitENat (det (xorOffset t w)) ∈ S} = fairTape {w | waitENat (det w) ∈ S} :=
  (xorOffset_measurePreserving_fair t).measure_preimage_equiv {w | waitENat (det w) ∈ S}

/-- `Statement:` for `p ≤ 1`, `xorOffset t` preserves `trials p hp` iff `t` is ⊥ of `ℕ → Bool` or
`p = 1/2`; both directions. `Reading:` (Tim's) a baseline and a local reference change: every tape is
the never-firing bottom of its own offset chart, and only the fair coin makes the change free. -/
theorem xorOffset_measurePreserving_iff (p : NNReal) (hp : p ≤ 1) (t : ℕ → Bool) :
    MeasurePreserving (xorOffset t) (trials p hp) (trials p hp) ↔ t = ⊥ ∨ p = 1/2 := by
  constructor
  · intro h
    by_cases ht : t = ⊥
    · exact Or.inl ht
    right
    obtain ⟨k, hk⟩ : ∃ k, t k = true := by
      by_contra hn; exact ht ((tape_never_fires_iff t).1 hn)
    have e := h.measure_preimage_equiv (fires k)
    have hpre : xorOffset t ⁻¹' fires k = (fires k)ᶜ := by
      ext w; simp [fires, xorOffset_apply, hk]
    rw [hpre, prob_compl_eq_one_sub (fires_measurable k), trials_fires] at e
    have e' : ((1 - p : NNReal) : ENNReal) = p := by
      rw [ENNReal.coe_sub, ENNReal.coe_one]; exact e
    have e'' : 1 - p = p := by exact_mod_cast e'
    have h2 : (1 : NNReal) = p + p := by
      calc (1 : NNReal) = 1 - p + p := (tsub_add_cancel_of_le hp).symm
        _ = p + p := by rw [e'']
    apply NNReal.eq
    have h3 := congrArg (fun x : NNReal => (x : ℝ)) h2
    push_cast at h3 ⊢
    linarith
  · rintro (rfl | rfl)
    · have e : xorOffset ⊥ = MeasurableEquiv.refl _ := by ext w n; simp [xorOffset_apply]
      rw [e]; exact MeasurePreserving.id _
    · exact xorOffset_measurePreserving_fair t

-- Statement: CONTROL `p = 1/2`, `t = ⊥` of `ℕ → Bool`: the identity translation, trivially preserving.
example : MeasurePreserving (xorOffset ⊥) fairTape fairTape :=
  (xorOffset_measurePreserving_iff (1/2) (by norm_num) ⊥).2 (Or.inl rfl)

-- Statement: CONTROL `p = 1/4`, `t` true only at stage 0: not preserving.
example : ¬ MeasurePreserving (xorOffset (fun k => decide (k = 0)))
    (trials (1/4) (div_le_one_of_le₀ (by norm_num) (by norm_num)))
    (trials (1/4) (div_le_one_of_le₀ (by norm_num) (by norm_num))) := by
  rw [xorOffset_measurePreserving_iff]
  rintro (h | h)
  · have := congrFun h 0; simp at this
  · norm_num at h

end WaitPackFaces

/-! ### § XI. The dial on the die: a Markov kernel subordinate to the step relation

`Reading:` to an observer of values, a halted state padded with "stay" and a self-loop give the same
constant run, and the observable question is heads versus non-heads, which `ae_leaves_iff` asks; to an
observer of available moves they differ. Value side: `loop_is_a_trap`, `da1_minimal_path`,
`carry_steps_onward_forever_yet_shows_nothing`, `stutter_obs_const`, `Motion.quot_leavesAt_iff`,
`Motion.selectedTotal_of_option`. Move side: `not_halted_is_stepping_head`,
`dead_yields_live_withholds`, `Motion.LaxHom.noStepAt_iff`. The kernel `K` is a supplied argument
throughout; nothing derives it from the die or from `L`. -/

section MarkovDie

open Finset

/-- `Statement:` the last coordinate of a path indexed by `Iic n`. -/
def pathLast {α : Type*} (n : ℕ) (x : Π _ : Iic n, α) : α := x ⟨n, mem_Iic.2 le_rfl⟩

/-- `Statement:` `pathLast n` is measurable. -/
theorem measurable_pathLast {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (pathLast (α := α) n) :=
  measurable_pi_apply _

/-- `Statement:` the time-homogeneous kernel on paths: read the last state, apply `K`. -/
noncomputable def homK {α : Type*} [MeasurableSpace α] (K : Kernel α α) (n : ℕ) :
    Kernel (Π _ : Iic n, α) α :=
  K.comap (pathLast n) (measurable_pathLast n)

/-- `Statement:` `homK K n` is a Markov kernel when `K` is. -/
instance isMarkovKernel_homK {α : Type*} [MeasurableSpace α] (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) : IsMarkovKernel (homK K n) := by
  unfold homK; infer_instance

/-- `Statement:` the law on `ℕ → α` of the Markov chain with transition kernel `K` started at `x₀`:
Mathlib's `Kernel.trajMeasure` (Ionescu-Tulcea) of `dirac x₀` and `homK K`. -/
noncomputable def runLaw {α : Type*} [MeasurableSpace α] (K : Kernel α α) [IsMarkovKernel K]
    (x₀ : α) : Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ => α) (Measure.dirac x₀) (homK K)

/-- `Statement:` `runLaw K x₀` is a probability measure. -/
instance isProbabilityMeasure_runLaw {α : Type*} [MeasurableSpace α] (K : Kernel α α)
    [IsMarkovKernel K] (x₀ : α) : IsProbabilityMeasure (runLaw K x₀) := by
  unfold runLaw; infer_instance

/-- `Statement:` at every `a`, `K a` gives full mass to the steps of `M` out of `a`. `Reading:` the
weighted die; standard name, a Markov chain whose directed graph lies in the step relation. -/
def Subordinate {α : Type*} [MeasurableSpace α] (M : Motion α) (K : Kernel α α) : Prop :=
  ∀ a, ∀ᵐ b ∂(K a), M.step a b

/-- `Statement:` the paths indexed by `Iic k` that sit at `x₀` throughout. -/
def stayPaths {α : Type*} (x₀ : α) (k : ℕ) : Set (Π _ : Iic k, α) := {y | ∀ i, y i = x₀}

/-- `Statement:` `stayPaths x₀ k` is measurable. -/
theorem measurableSet_stayPaths {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (x₀ : α) (k : ℕ) : MeasurableSet (stayPaths x₀ k) := by
  have : stayPaths x₀ k = ⋂ i, (fun y : Π _ : Iic k, α => y i) ⁻¹' {x₀} := by
    ext y; simp [stayPaths]
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i (measurableSet_singleton x₀)

/-- `Statement:` one more transition keeps a path in `stayPaths x₀` with mass `K x₀ {x₀}` if it was
there, and 0 otherwise. -/
theorem stayPaths_step_mass {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) (k : ℕ) (y : Π _ : Iic k, α) :
    Kernel.partialTraj (X := fun _ => α) (homK K) k (k + 1) y (stayPaths x₀ (k + 1)) =
      (stayPaths x₀ k).indicator (fun _ => K x₀ {x₀}) y := by
  set μ := Kernel.partialTraj (X := fun _ => α) (homK K) k (k + 1) y with hμ
  have hf : Measurable (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ k)) :=
    Preorder.measurable_frestrictLe₂ _
  have hl : Measurable (fun z : Π _ : Iic (k + 1), α => z ⟨k + 1, mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  have hmap : μ.map (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ k)) =
      Measure.dirac y := by
    rw [hμ, Kernel.partialTraj_map_frestrictLe₂_apply, Kernel.partialTraj_self]; rfl
  have hlast : μ.map (fun z : Π _ : Iic (k + 1), α => z ⟨k + 1, mem_Iic.2 le_rfl⟩) =
      homK K k y := by
    rw [hμ, ← Kernel.map_apply _ hl, Kernel.map_partialTraj_succ_self]
  have hset : stayPaths x₀ (k + 1) =
      (Preorder.frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ k)) ⁻¹' stayPaths x₀ k ∩
        (fun z : Π _ : Iic (k + 1), α => z ⟨k + 1, mem_Iic.2 le_rfl⟩) ⁻¹' {x₀} := by
    ext z
    simp only [stayPaths, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Preorder.frestrictLe₂_apply]
    refine ⟨fun h => ⟨fun i => h _, h _⟩, fun ⟨h1, h2⟩ i => ?_⟩
    obtain ⟨i, hi⟩ := i
    have hi' := mem_Iic.1 hi
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact h1 ⟨i, mem_Iic.2 (by omega)⟩
    · have : i = k + 1 := by omega
      subst this; exact h2
  have hA : μ ((Preorder.frestrictLe₂ (π := fun _ : ℕ => α) (Nat.le_succ k)) ⁻¹' stayPaths x₀ k) =
      (Measure.dirac y) (stayPaths x₀ k) := by
    rw [← hmap, Measure.map_apply hf (measurableSet_stayPaths x₀ k)]
  by_cases hy : y ∈ stayPaths x₀ k
  · rw [Set.indicator_of_mem hy, hset, Set.inter_comm, measure_inter_conull]
    · rw [← Measure.map_apply hl (measurableSet_singleton x₀), hlast]
      simp only [homK, Kernel.comap_apply, pathLast]
      rw [hy]
    · rw [← Set.preimage_compl, ← Measure.map_apply hf (measurableSet_stayPaths x₀ k).compl, hmap,
        Measure.dirac_apply' _ (measurableSet_stayPaths x₀ k).compl]
      simp [hy]
  · rw [Set.indicator_of_notMem hy]
    refine le_antisymm ?_ bot_le
    rw [hset]
    refine (measure_mono Set.inter_subset_left).trans (le_of_eq ?_)
    rw [hA, Measure.dirac_apply' _ (measurableSet_stayPaths x₀ k)]
    simp [hy]

/-- `Statement:` the length-1 path at `x₀` lies in `stayPaths x₀ 0`. -/
theorem start_mem_stayPaths {α : Type*} [MeasurableSpace α] (x₀ : α) :
    ((MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm x₀) ∈ stayPaths x₀ 0 := by
  intro i
  rw [Unique.eq_default i]
  exact (MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).apply_symm_apply x₀

/-- `Statement:` from the length-1 path at `x₀`, the first `k` transitions stay at `x₀` with mass
`(K x₀ {x₀}) ^ k`. -/
theorem partialTraj_stayPaths {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) (k : ℕ) :
    Kernel.partialTraj (X := fun _ => α) (homK K) 0 k
      ((MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm x₀) (stayPaths x₀ k) =
      (K x₀ {x₀}) ^ k := by
  induction k with
  | zero =>
    rw [Kernel.partialTraj_zero, Kernel.deterministic_apply,
      Measure.dirac_apply' _ (measurableSet_stayPaths x₀ 0), pow_zero]
    refine Set.indicator_of_mem ?_ _
    intro i
    simp only [Preorder.frestrictLe₂_apply]
    exact start_mem_stayPaths x₀ _
  | succ k ih =>
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le k),
      Kernel.comp_apply' _ _ _ (measurableSet_stayPaths x₀ (k + 1))]
    simp_rw [stayPaths_step_mass K x₀ k]
    rw [lintegral_indicator_const (measurableSet_stayPaths x₀ k), ih, pow_succ, mul_comm]

/-- `Statement:` `runLaw K x₀` is `Kernel.traj (homK K) 0` at the length-1 path at `x₀`. -/
theorem runLaw_eq {α : Type*} [MeasurableSpace α] (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) :
    runLaw K x₀ = Kernel.traj (X := fun _ => α) (homK K) 0
      ((MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm x₀) := by
  ext s hs
  rw [runLaw, Kernel.trajMeasure, Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) (MeasurableEquiv.measurable _)]
  exact lintegral_dirac' x₀ ((Kernel.measurable_coe _ hs).comp (MeasurableEquiv.measurable _))

/-- `Statement:` the run stays at `x₀` through `k` transitions with probability `(K x₀ {x₀}) ^ k`. -/
theorem runLaw_stay {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) (k : ℕ) :
    runLaw K x₀ {x | ∀ i ≤ k, x i = x₀} = (K x₀ {x₀}) ^ k := by
  have hs : {x : ℕ → α | ∀ i ≤ k, x i = x₀} =
      Preorder.frestrictLe (π := fun _ : ℕ => α) k ⁻¹' stayPaths x₀ k := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, stayPaths, Preorder.frestrictLe_apply]
    exact ⟨fun h i => h i.1 (mem_Iic.1 i.2), fun h i hi => h ⟨i, mem_Iic.2 hi⟩⟩
  rw [hs, runLaw_eq, ← Measure.map_apply (Preorder.measurable_frestrictLe k)
    (measurableSet_stayPaths x₀ k), Kernel.traj_map_frestrictLe_apply, partialTraj_stayPaths]

/-- `Statement:` the runs that sit at `x₀` through stage `k` form a measurable set. -/
theorem measurableSet_stayRun {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (x₀ : α) (k : ℕ) : MeasurableSet {x : ℕ → α | ∀ i ≤ k, x i = x₀} := by
  have : {x : ℕ → α | ∀ i ≤ k, x i = x₀} =
      ⋂ i ∈ Finset.range (k + 1), (fun x => x i) ⁻¹' {x₀} := by
    ext x; simp
  rw [this]
  exact Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i (measurableSet_singleton x₀)

/-- `Statement:` with leave-weight `p = (K x₀ {x₀}ᶜ).toNNReal`, the run stays at `x₀` through `k`
transitions with the `trials p` mass of the cylinder of ⊥ of `ℕ → Bool` of length `k`. -/
theorem runLaw_stay_eq_trials {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) (k : ℕ) :
    runLaw K x₀ {x | ∀ i ≤ k, x i = x₀} =
      trials (K x₀ {x₀}ᶜ).toNNReal
        (by rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (measure_ne_top _ _)]; exact prob_le_one)
        (PiNat.cylinder (⊥ : ℕ → Bool) k) := by
  rw [runLaw_stay, trials_cyl]
  have hb : ∀ i, (⊥ : ℕ → Bool) i = false := fun _ => rfl
  simp only [hb, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_range]
  congr 1
  rw [prob_compl_eq_one_sub (measurableSet_singleton x₀), ENNReal.toNNReal_sub (measure_ne_top _ _),
    ENNReal.toNNReal_one, tsub_tsub_cancel_of_le, ENNReal.coe_toNNReal (measure_ne_top _ _)]
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (measure_ne_top _ _)]
  exact prob_le_one

/-- `Statement:` the run ever leaves `x₀` with probability 0 if the leave-weight
`(K x₀ {x₀}ᶜ).toNNReal` is 0 and 1 otherwise; reduced to `dial_fire_jump`. -/
theorem runLaw_leaves {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) :
    runLaw K x₀ {x | ∃ i, x i ≠ x₀} = if (K x₀ {x₀}ᶜ).toNNReal = 0 then 0 else 1 := by
  set p := (K x₀ {x₀}ᶜ).toNNReal
  have hp : p ≤ 1 := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (measure_ne_top _ _)]; exact prob_le_one
  rw [← dial_fire_jump p hp]
  have e1 : {x : ℕ → α | ∃ i, x i ≠ x₀} = (⋂ k, {x : ℕ → α | ∀ i ≤ k, x i = x₀})ᶜ := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, not_forall]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, i, le_rfl, hi⟩, fun ⟨_, i, _, hi⟩ => ⟨i, hi⟩⟩
  have e2 : {w : ℕ → Bool | ∃ k, w k = true} = (⋂ k, PiNat.cylinder (⊥ : ℕ → Bool) k)ᶜ := by
    ext w; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iInter, not_forall,
      PiNat.cylinder]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k + 1, k, by omega, by simp [hk]⟩
    · rintro ⟨_, i, _, hi⟩; exact ⟨i, by simpa using hi⟩
  have hm1 : MeasurableSet (⋂ k, {x : ℕ → α | ∀ i ≤ k, x i = x₀}) :=
    MeasurableSet.iInter fun k => measurableSet_stayRun x₀ k
  have hm2 : MeasurableSet (⋂ k, PiNat.cylinder (⊥ : ℕ → Bool) k) :=
    MeasurableSet.iInter fun k => (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ k).measurableSet
  rw [e1, e2, prob_compl_eq_one_sub hm1, prob_compl_eq_one_sub hm2]
  congr 1
  have t1 := tendsto_measure_iInter_atTop (μ := runLaw K x₀)
    (s := fun k => {x : ℕ → α | ∀ i ≤ k, x i = x₀})
    (fun k => (measurableSet_stayRun x₀ k).nullMeasurableSet)
    (fun a b hab x hx i hi => hx i (le_trans hi hab)) ⟨0, measure_ne_top _ _⟩
  have t2 := tendsto_measure_iInter_atTop (μ := trials p hp)
    (s := fun k => PiNat.cylinder (⊥ : ℕ → Bool) k)
    (fun k => (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ k).measurableSet.nullMeasurableSet)
    (fun a b hab w hw i hi => hw i (lt_of_lt_of_le hi hab)) ⟨0, measure_ne_top _ _⟩
  have hfun : (runLaw K x₀ ∘ fun k => {x : ℕ → α | ∀ i ≤ k, x i = x₀}) =
      (trials p hp ∘ fun k => PiNat.cylinder (⊥ : ℕ → Bool) k) := by
    funext k; exact runLaw_stay_eq_trials K x₀ k
  rw [hfun] at t1
  exact tendsto_nhds_unique t1 t2

/-- `Statement:` almost every run leaves `x₀` iff `K x₀` gives positive mass to leaving; both
directions. -/
theorem ae_leaves_iff {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) :
    (∀ᵐ x ∂(runLaw K x₀), ∃ i, x i ≠ x₀) ↔ 0 < K x₀ {x₀}ᶜ := by
  have hm : MeasurableSet {x : ℕ → α | ∃ i, x i ≠ x₀} := by
    have : {x : ℕ → α | ∃ i, x i ≠ x₀} = ⋃ i, ((fun x => x i) ⁻¹' {x₀})ᶜ := by ext x; simp
    rw [this]
    exact MeasurableSet.iUnion fun i => (measurable_pi_apply i (measurableSet_singleton x₀)).compl
  rw [ae_iff_measure_eq hm.nullMeasurableSet, measure_univ, runLaw_leaves]
  have hz : (K x₀ {x₀}ᶜ).toNNReal = 0 ↔ K x₀ {x₀}ᶜ = 0 := by
    rw [ENNReal.toNNReal_eq_zero_iff]; simp [measure_ne_top]
  split_ifs with h
  · simp [hz.1 h]
  · simp only [true_iff]; exact pos_iff_ne_zero.2 (fun h0 => h (hz.2 h0))

/-- `Statement:` if `K` is subordinate to `M` and the step relation is measurable, almost every run is
a run of `M`. -/
theorem ae_isRun {α : Type*} [MeasurableSpace α] (K : Kernel α α) [IsMarkovKernel K]
    (M : Motion α) (hK : Subordinate M K) (hm : MeasurableSet {q : α × α | M.step q.1 q.2})
    (x₀ : α) : ∀ᵐ x ∂(runLaw K x₀), M.IsRun x := by
  refine ae_all_iff.2 fun n => ?_
  set T : Set ((Π _ : Iic n, α) × α) := {q | ¬ M.step (pathLast n q.1) q.2} with hT
  have hTm : MeasurableSet T :=
    (((measurable_pathLast n).comp measurable_fst).prodMk measurable_snd) hm |>.compl
  have hf : Measurable fun x : ℕ → α =>
      (Preorder.frestrictLe (π := fun _ : ℕ => α) n x, x (n + 1)) :=
    (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply _)
  rw [ae_iff]
  have hset : {x : ℕ → α | ¬ M.step (x n) (x (n + 1))} =
      (fun x : ℕ → α => (Preorder.frestrictLe (π := fun _ : ℕ => α) n x, x (n + 1))) ⁻¹' T := by
    ext x; simp [hT, pathLast, Preorder.frestrictLe_apply]
  rw [hset, ← Measure.map_apply hf hTm]
  unfold runLaw
  rw [← Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure,
    Measure.compProd_apply hTm]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun y => ?_)
  simp only [homK, Kernel.comap_apply, Pi.zero_apply]
  exact ae_iff.1 (hK (pathLast n y))

/-- `Statement:` CONTROL, at a point with no step no Markov kernel gives full mass to the steps out of
it. -/
theorem not_subordinate_of_noStepAt {α : Type*} [MeasurableSpace α] (K : Kernel α α)
    [IsMarkovKernel K] (M : Motion α) {y : α} (hy : M.NoStepAt y) :
    ¬ ∀ᵐ b ∂(K y), M.step y b := by
  intro h
  have : K y {b | ¬ M.step y b} = 0 := ae_iff.1 h
  have hu : {b | ¬ M.step y b} = Set.univ := Set.eq_univ_of_forall fun b => hy b
  rw [hu, measure_univ] at this
  exact one_ne_zero this

/-- `Statement:` CONTROL, at a point stepping to itself only (absorbing), a subordinate kernel has
leave-weight 0. -/
theorem leave_zero_of_selfOnlyAt {α : Type*} [MeasurableSpace α] (K : Kernel α α) (M : Motion α)
    (hK : Subordinate M K) {y : α} (hy : M.SelfOnlyAt y) : K y {y}ᶜ = 0 := by
  exact measure_mono_null (fun b hb hs => hb (hy.2 b hs)) (ae_iff.1 (hK y))

/-- `Statement:` under a subordinate kernel, positive leave-weight at `y` gives a step from `y`
elsewhere; one way (the `example` after the `slotKernel 0` CONTROL below fails the converse). -/
theorem leavesAt_of_pos {α : Type*} [MeasurableSpace α] (K : Kernel α α) (M : Motion α)
    (hK : Subordinate M K) {y : α} (h : 0 < K y {y}ᶜ) : M.LeavesAt y := by
  by_contra hl
  exact h.ne' (measure_mono_null (fun b hb hs => hl ⟨b, hs, hb⟩) (ae_iff.1 (hK y)))

/-- `Statement:` CONTROL, a kernel subordinate to `Motion.ofFun g` gives `{g a}ᶜ` mass 0 at every `a`:
no room for weights. -/
theorem ofFun_kernel_dirac {α : Type*} [MeasurableSpace α] (K : Kernel α α) (g : α → α)
    (hK : Subordinate (Motion.ofFun g) K) (a : α) : K a {g a}ᶜ = 0 := by
  exact measure_mono_null (fun b hb hs => hb hs) (ae_iff.1 (hK a))

set_option linter.deprecated false in
/-- `Statement:` the kernel on `Bool` that at `false` is Bernoulli(`p`) and at `true` the Dirac mass at
`true`. -/
noncomputable def slotKernel (p : NNReal) (hp : p ≤ 1) : Kernel Bool Bool :=
  Kernel.ofFunOfCountable fun b => if b then Measure.dirac true else (PMF.bernoulli p hp).toMeasure

set_option linter.deprecated false in
/-- `Statement:` `slotKernel p hp` is a Markov kernel. -/
instance isMarkovKernel_slotKernel (p : NNReal) (hp : p ≤ 1) : IsMarkovKernel (slotKernel p hp) :=
  ⟨fun b => by
    cases b
    · show IsProbabilityMeasure (PMF.bernoulli p hp).toMeasure; infer_instance
    · show IsProbabilityMeasure (Measure.dirac true); infer_instance⟩

/-- `Statement:` `slotKernel p hp` is subordinate to `slotMotion`. -/
theorem slotKernel_subordinate (p : NNReal) (hp : p ≤ 1) :
    Subordinate slotMotion (slotKernel p hp) := by
  intro a
  cases a
  · exact Filter.Eventually.of_forall fun b => by
      cases b
      · exact Or.inl rfl
      · exact Or.inr ⟨rfl, rfl⟩
  · show ∀ᵐ b ∂(Measure.dirac true), true = b ∨ (true = false ∧ b = true)
    rw [ae_dirac_eq]; exact Filter.eventually_pure.2 (Or.inl rfl)

set_option linter.deprecated false in
/-- `Statement:` the leave-weight of `slotKernel p hp` at `false` is `p`. -/
theorem slotKernel_leave (p : NNReal) (hp : p ≤ 1) : slotKernel p hp false {false}ᶜ = p := by
  have : ({false}ᶜ : Set Bool) = {true} := by ext b; cases b <;> simp
  show (PMF.bernoulli p hp).toMeasure {false}ᶜ = p
  rw [this, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.bernoulli]

/-- `Statement:` from `false`, the run of `slotKernel p hp` stays at `false` through `k` transitions
with the `trials p hp` mass of the cylinder of ⊥ of `ℕ → Bool` of length `k`. -/
theorem slot_stay_eq_trials (p : NNReal) (hp : p ≤ 1) (k : ℕ) :
    runLaw (slotKernel p hp) false {x | ∀ i ≤ k, x i = false} =
      trials p hp (PiNat.cylinder (⊥ : ℕ → Bool) k) := by
  have key : ∀ (q : NNReal) (hq : q ≤ 1), q = p → trials q hq = trials p hp := by
    rintro q hq rfl; rfl
  rw [runLaw_stay_eq_trials, key _ _ (by rw [slotKernel_leave]; simp)]

/-- `Statement:` with leave-weight `glauberExciteNN ΔE T`, almost every run of the slot kernel leaves
`false`, at every `ΔE` and `T`. `Reading:` the temperature relocates `0 < p` into
`glauberExciteNN_pos`; it does not remove it. -/
theorem glauber_slot_leaves (ΔE T : ℝ) :
    ∀ᵐ x ∂(runLaw (slotKernel (glauberExciteNN ΔE T) (glauberExciteNN_le_one ΔE T)) false),
      ∃ i, x i ≠ false := by
  rw [ae_leaves_iff, slotKernel_leave]
  exact_mod_cast glauberExciteNN_pos ΔE T

-- Statement: CONTROL, `slotKernel 0` (subordinate, since `false` steps to itself): almost no run
-- leaves `false` (`runLaw_leaves` at leave-weight 0).
example : ∀ᵐ x ∂(runLaw (slotKernel 0 zero_le_one) false), ∀ i, x i = false := by
  have h := runLaw_leaves (slotKernel 0 zero_le_one) false
  rw [slotKernel_leave] at h
  rw [ae_iff]; simpa using h

-- Statement: CONTROL, the converse of `leavesAt_of_pos` fails: `slotKernel 0` is subordinate to
-- `slotMotion`, `false` steps elsewhere there, and the leave-weight at `false` is 0.
example : Subordinate slotMotion (slotKernel 0 zero_le_one) ∧ slotMotion.LeavesAt false ∧
    slotKernel 0 zero_le_one false {false}ᶜ = 0 :=
  ⟨slotKernel_subordinate 0 zero_le_one, slotMotion_leavesAt_false.1, by rw [slotKernel_leave]; simp⟩

/-- `Statement:` if the binary entropy of the leave-weight at `x₀` is `log 2`, the leave-weight is
`1/2`; `eq_half_of_maxEntropy` applied to it. -/
theorem leave_half_of_maxEntropy {α : Type*} [MeasurableSpace α] (K : Kernel α α) (x₀ : α)
    (h : Real.binEntropy ((K x₀ {x₀}ᶜ).toNNReal : ℝ) = Real.log 2) :
    (K x₀ {x₀}ᶜ).toNNReal = 2⁻¹ := by
  exact eq_half_of_maxEntropy _ h

-- Statement: in a `ZPSemilattice` with measurable singletons, a supplied Markov kernel gives a law on
-- runs from ⊥ of `L`, and almost every run leaves ⊥ of `L` iff leaving has positive weight.
example {L : Type*} [ZPSemilattice L] [MeasurableSpace L] [MeasurableSingletonClass L]
    (K : Kernel L L) [IsMarkovKernel K] :
    (∀ᵐ x ∂(runLaw K ZPSemilattice.bot), ∃ i, x i ≠ ZPSemilattice.bot) ↔
      0 < K ZPSemilattice.bot {ZPSemilattice.bot}ᶜ :=
  ae_leaves_iff K _

end MarkovDie

/-! ### § XII. Lumping: the observed chain, and reversibility under coarse-graining

`Reading:` a map `f` out of the states is an observer; when the kernel lumps along `f`, what the
observer sees is again a Markov chain (`lumps_iff_runLaw_map`), the weighted analogue of the die's
`StepCompat`. Both directions of the arrow are stated: coarse-graining can erase a time arrow
(`a4_direction_erased`), and from a reversible start it creates none, for a measurable lumping map
in general (`isReversible_map_of_lumps`) and, on a finite carrier with measurable singletons, from an
initial probability law w.r.t. which the Markov kernel is reversible, for every measurable observer and
every window of consecutive times (`chainLaw_window_map_reverse`); `coarse_graining_trade` states both
directions. The kernel is a supplied argument throughout. -/

-- Provenance: the lumping and run-law declarations marked `[ZP]` are adapted and modified from
-- MurphyHoops/UEOT, `formalization/ueot-core/UEOT/V3/DynamicsKernel.lean` (lean4-core-export v1.0.0,
-- Apache-2.0); each mark names its UEOT original. See NOTICE.
section Lumping

open Finset

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `Statement:` strong lumpability, Dynkin's intertwining form: `(K a).map f = L (f a)` at every `a`. -/
def Lumps (K : Kernel α α) (L : Kernel β β) (f : α → β) : Prop := ∀ a, (K a).map f = L (f a)

/-- `Statement:` related starts put the same image mass on every class (the per-class form; Levin,
Peres, Wilmer (2.10); attributed to Kemeny-Snell via Wolfer-Watanabe Theorem 3.1). -/
def FiberConst (K : Kernel α α) (f : α → β) : Prop :=
  ∀ a a', f a = f a' → (K a).map f = (K a').map f

/-- [ZP] adapted from UEOT `strongLumpability_fiber_constant`. `Statement:` lumping to some `L`
gives the per-class form; one way. -/
theorem Lumps.fiberConst {K : Kernel α α} {L : Kernel β β} {f : α → β} (h : Lumps K L f) :
    FiberConst K f := fun a a' e => by rw [h a, h a', e]

/-- [ZP] adapted from UEOT `mapHistory`. `Statement:` the coordinatewise map of a finite history. -/
def mapHist (f : α → β) (n : ℕ) (x : (i : Iic n) → α) : (i : Iic n) → β := fun i => f (x i)

/-- [ZP] adapted from UEOT `measurable_mapHistory`. `Statement:` `mapHist f n` is measurable when
`f` is. -/
theorem measurable_mapHist {f : α → β} (hf : Measurable f) (n : ℕ) : Measurable (mapHist f n) :=
  measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)

/-- [ZP] adapted from UEOT `appendHistory`. `Statement:` append one state to a finite history. -/
def appendHist (n : ℕ) (p : ((i : Iic n) → α) × α) : (i : Iic (n + 1)) → α :=
  IicProdIoc (X := fun _ : ℕ => α) n (n + 1)
    (p.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ => α) n p.2)

/-- [ZP] adapted from UEOT `measurable_appendHistory`. `Statement:` `appendHist n` is measurable. -/
theorem measurable_appendHist (n : ℕ) : Measurable (appendHist (α := α) n) :=
  measurable_IicProdIoc.comp (measurable_fst.prodMk
    ((MeasurableEquiv.piSingleton (X := fun _ : ℕ => α) n).measurable.comp measurable_snd))

/-- [ZP] adapted from UEOT `mapHistory_comp_appendHistory` and `mapHistory_appendHistory`.
`Statement:` mapping coordinatewise commutes with appending. -/
theorem mapHist_comp_appendHist (f : α → β) (n : ℕ) :
    mapHist f (n + 1) ∘ appendHist n = appendHist n ∘ Prod.map (mapHist f n) f := by
  funext p
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · simp [mapHist, appendHist, IicProdIoc_def, hi]
  · have hin : (i : ℕ) = n + 1 := by have := Finset.mem_Iic.mp i.2; omega
    have hieq : i = ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hin
    subst hieq
    simp [mapHist, appendHist, IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- [ZP] adapted from UEOT `appendHistory_prefix_next`. `Statement:` the prefix of length `n + 2`
is the prefix of length `n + 1` with `x (n + 1)` appended. -/
theorem appendHist_prefix (n : ℕ) (x : ℕ → α) :
    appendHist n (Preorder.frestrictLe n x, x (n + 1)) = Preorder.frestrictLe (n + 1) x := by
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · simp [appendHist, IicProdIoc_def, Preorder.frestrictLe_apply, hi]
  · have hin : (i : ℕ) = n + 1 := by have := Finset.mem_Iic.mp i.2; omega
    have hieq : i = (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Iic (n + 1)) := Subtype.ext hin
    rw [hieq]
    simp [appendHist, IicProdIoc_def, Preorder.frestrictLe_apply, MeasurableEquiv.piSingleton]

/-- `Statement:` the chain law from an initial law `μ`: `Kernel.trajMeasure μ (homK K)`. -/
noncomputable abbrev chainLaw (μ : Measure α) (K : Kernel α α) [IsMarkovKernel K] :
    Measure (ℕ → α) :=
  Kernel.trajMeasure (X := fun _ => α) μ (homK K)

/-- `Statement:` `chainLaw μ K` is a probability measure when `μ` is. -/
instance isProbabilityMeasure_chainLaw (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] : IsProbabilityMeasure (chainLaw μ K) := by unfold chainLaw; infer_instance

/-- `Statement:` `runLaw K x₀` is `chainLaw` from the Dirac law at `x₀`, by `rfl`. -/
theorem runLaw_eq_chainLaw (K : Kernel α α) [IsMarkovKernel K] (x₀ : α) :
    runLaw K x₀ = chainLaw (Measure.dirac x₀) K := rfl

/-- [ZP] adapted from UEOT `homTrajMeasure_prefix_zero`. `Statement:` the length-1 prefix of
`chainLaw μ K` is `μ`, read on `Iic 0`. -/
theorem chainLaw_prefix_zero (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] :
    (chainLaw μ K).map (Preorder.frestrictLe 0) =
      μ.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm := by
  rw [chainLaw, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

/-- [ZP] adapted from the first step of UEOT `homTrajMeasure_prefix_succ`. `Statement:` the law of
(prefix to `n`, state `n + 1`) is the prefix law `⊗ₘ homK K n`
(Mathlib's `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`). -/
theorem chainLaw_step (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) :
    ((chainLaw μ K).map (Preorder.frestrictLe n)) ⊗ₘ homK K n =
      (chainLaw μ K).map (fun x => (Preorder.frestrictLe n x, x (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => α) (μ₀ := μ) (κ := homK K) (a := n)

/-- [ZP] adapted from UEOT `homTrajMeasure_prefix_succ`. `Statement:` the next prefix law is the
current one `⊗ₘ homK K n`, appended. -/
theorem chainLaw_prefix_succ (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) :
    (((chainLaw μ K).map (Preorder.frestrictLe n)) ⊗ₘ homK K n).map (appendHist n) =
      (chainLaw μ K).map (Preorder.frestrictLe (n + 1)) := by
  rw [chainLaw_step, Measure.map_map (measurable_appendHist n) (by fun_prop)]
  congr 1
  funext x
  exact appendHist_prefix n x

/-- [ZP] adapted from the last step of UEOT `homHistory_compProd_naturality`. `Statement:` pushing
the first factor of `μh ⊗ₘ κ.comap e` along `e` gives `μh.map e ⊗ₘ κ`. -/
theorem compProd_comap_map {Y Z X : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace X] (μh : Measure Y) [SFinite μh] {e : Y → X} (he : Measurable e)
    (κ : Kernel X Z) [IsSFiniteKernel κ] :
    (μh ⊗ₘ κ.comap e he).map (Prod.map e id) = μh.map e ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (he.prodMap measurable_id) hs,
    Measure.compProd_apply (he.prodMap measurable_id hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) he]
  rfl

/-- [ZP] adapted from UEOT `homHistory_compProd_naturality`. `Statement:` if `K` lumps to `L` along
`f`, one step of the history commutes with `f`. -/
theorem homK_compProd_naturality {n : ℕ} (μh : Measure ((i : Iic n) → α)) [SFinite μh]
    (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L]
    {f : α → β} (hf : Measurable f) (h : Lumps K L f) :
    (μh ⊗ₘ homK K n).map (Prod.map (mapHist f n) f) =
      (μh.map (mapHist f n)) ⊗ₘ homK L n := by
  have hF := measurable_mapHist hf n
  have hk : (homK K n).map f = (homK L n).comap (mapHist f n) hF := by
    ext x B hB
    rw [Kernel.map_apply' _ hf _ hB, Kernel.comap_apply']
    simp only [homK, Kernel.comap_apply']
    rw [← Measure.map_apply hf hB, h]
    rfl
  calc (μh ⊗ₘ homK K n).map (Prod.map (mapHist f n) f)
      = ((μh ⊗ₘ homK K n).map (Prod.map id f)).map (Prod.map (mapHist f n) id) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
    _ = (μh ⊗ₘ (homK K n).map f).map (Prod.map (mapHist f n) id) := by
        rw [← Measure.compProd_map hf]
    _ = (μh ⊗ₘ (homK L n).comap (mapHist f n) hF).map (Prod.map (mapHist f n) id) := by rw [hk]
    _ = (μh.map (mapHist f n)) ⊗ₘ homK L n := compProd_comap_map μh hF (homK L n)

/-- [ZP] adapted from UEOT `homTrajMeasure_prefix_naturality`. `Statement:` under lumping, every
finite prefix of the observed chain has the lumped prefix law. -/
theorem chainLaw_prefix_naturality (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L]
    {f : α → β} (hf : Measurable f) (h : Lumps K L f) (n : ℕ) :
    ((chainLaw μ K).map (Preorder.frestrictLe n)).map (mapHist f n) =
      (chainLaw (μ.map f) L).map (Preorder.frestrictLe n) := by
  induction n with
  | zero =>
    rw [chainLaw_prefix_zero μ K, chainLaw_prefix_zero (μ.map f) L,
      Measure.map_map (measurable_mapHist hf 0) (by fun_prop), Measure.map_map (by fun_prop) hf]
    rfl
  | succ n ih =>
    rw [← chainLaw_prefix_succ μ K n,
      Measure.map_map (measurable_mapHist hf (n + 1)) (measurable_appendHist n),
      mapHist_comp_appendHist f n,
      ← Measure.map_map (measurable_appendHist (α := β) n)
        ((measurable_mapHist hf n).prodMap hf),
      homK_compProd_naturality _ K L hf h, ih]
    exact chainLaw_prefix_succ (μ.map f) L n

/-- [ZP] adapted from UEOT `pathMeasure_eq_of_prefix_eq`. `Statement:` two probability measures on
`ℕ → β` with equal laws on every prefix are equal (Mathlib's `IsProjectiveLimit.unique`). -/
theorem pathMeasure_eq_of_prefix_eq (μp νp : Measure (ℕ → β))
    [IsProbabilityMeasure μp] [IsProbabilityMeasure νp]
    (hp : ∀ n, μp.map (Preorder.frestrictLe n) = νp.map (Preorder.frestrictLe n)) : μp = νp := by
  let P : (I : Finset ℕ) → Measure ((i : I) → β) := fun I => μp.map (I.restrict (π := fun _ => β))
  have : ∀ I, IsProbabilityMeasure (P I) := fun I => by dsimp only [P]; infer_instance
  have hν : IsProjectiveLimit (ι := ℕ) (α := fun _ => β) νp P := by
    intro I
    have hsub : I ⊆ Finset.Iic (I.sup id) := I.subset_Iic_sup_id
    have h := hp (I.sup id)
    change μp.map ((Finset.Iic (I.sup id)).restrict (π := fun _ => β)) =
      νp.map ((Finset.Iic (I.sup id)).restrict (π := fun _ => β)) at h
    show νp.map (I.restrict (π := fun _ => β)) = μp.map (I.restrict (π := fun _ => β))
    have e : ∀ ρ : Measure (ℕ → β), ρ.map (I.restrict (π := fun _ => β)) =
        (ρ.map ((Finset.Iic (I.sup id)).restrict (π := fun _ => β))).map
          (Finset.restrict₂ (π := fun _ => β) hsub) := fun ρ => by
      rw [Measure.map_map (Finset.measurable_restrict₂ (X := fun _ => β) hsub)
        (Finset.measurable_restrict _)]; rfl
    rw [e, e μp, h]
  exact (show IsProjectiveLimit (ι := ℕ) (α := fun _ => β) μp P from fun _ => rfl).unique hν

/-- [ZP] adapted from UEOT `homTrajMeasure_path_naturality`. `Statement:` if `K` lumps to `L` along
measurable `f`, the observed process `n ↦ f (x n)` of the chain from `μ` has the law of the
`L`-chain from `μ.map f`. -/
theorem chainLaw_map_of_lumps (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L]
    {f : α → β} (hf : Measurable f) (h : Lumps K L f) :
    (chainLaw μ K).map (fun x n => f (x n)) = chainLaw (μ.map f) L := by
  have hF : Measurable (fun (x : ℕ → α) n => f (x n)) :=
    measurable_pi_iff.mpr fun k => hf.comp (measurable_pi_apply k)
  refine pathMeasure_eq_of_prefix_eq _ _ fun n => ?_
  rw [Measure.map_map (Preorder.measurable_frestrictLe n) hF]
  have : Preorder.frestrictLe n ∘ (fun (x : ℕ → α) k => f (x k)) =
      mapHist f n ∘ Preorder.frestrictLe n := rfl
  rw [this, ← Measure.map_map (measurable_mapHist hf n) (Preorder.measurable_frestrictLe n)]
  exact chainLaw_prefix_naturality μ K L hf h n

/-- [ZP] adapted from UEOT `homTrajMeasure_path_naturality`, at a Dirac start. `Statement:` the same
from a point: the observed run of `runLaw K x₀` has law `runLaw L (f x₀)`. -/
theorem runLaw_map_of_lumps (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L]
    {f : α → β} (hf : Measurable f) (h : Lumps K L f) (x₀ : α) :
    (runLaw K x₀).map (fun x n => f (x n)) = runLaw L (f x₀) := by
  rw [runLaw_eq_chainLaw, runLaw_eq_chainLaw, ← Measure.map_dirac' hf]
  exact chainLaw_map_of_lumps (Measure.dirac x₀) K L hf h

/-- [ZP] adapted from UEOT `homTrajMeasure_dirac_time_one`. `Statement:` the time-1 marginal of
`runLaw K x` is `K x`. -/
theorem runLaw_time_one (K : Kernel α α) [IsMarkovKernel K] (x : α) :
    (runLaw K x).map (fun z => z 1) = K x := by
  have hstep := chainLaw_prefix_succ (Measure.dirac x) K 0
  have hzero := chainLaw_prefix_zero (Measure.dirac x) K
  have hlast : (fun h : (i : Iic 1) → α => h ⟨1, Finset.mem_Iic.mpr le_rfl⟩) ∘ appendHist 0 =
      Prod.snd := by
    funext p; simp [appendHist, IicProdIoc_def, MeasurableEquiv.piSingleton]
  have e1 : (runLaw K x).map (fun z => z 1) =
      ((chainLaw (Measure.dirac x) K).map (Preorder.frestrictLe 1)).map
        (fun h : (i : Iic 1) → α => h ⟨1, Finset.mem_Iic.mpr le_rfl⟩) := by
    have hc : (fun z : ℕ → α => z 1) = (fun h : (i : Iic 1) → α => h ⟨1, Finset.mem_Iic.mpr le_rfl⟩) ∘
        Preorder.frestrictLe 1 := rfl
    rw [runLaw_eq_chainLaw, hc]
    exact (Measure.map_map (measurable_pi_apply _) (Preorder.measurable_frestrictLe 1)).symm
  rw [e1, ← hstep, Measure.map_map (measurable_pi_apply _) (measurable_appendHist 0), hlast,
    ← Measure.snd, Measure.snd_compProd, hzero,
    Measure.map_dirac' (MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm.measurable,
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- [ZP] adapted from UEOT `pathLaw_implies_strongLumpability`. `Statement:` if from every start the
observed run has the `L`-chain's law, `K` lumps to `L`. -/
theorem lumps_of_runLaw_map (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L]
    {f : α → β} (hf : Measurable f)
    (h : ∀ x₀, (runLaw K x₀).map (fun x n => f (x n)) = runLaw L (f x₀)) : Lumps K L f := by
  intro a
  have := congrArg (fun ν : Measure (ℕ → β) => ν.map (fun z => z 1)) (h a)
  have hF : Measurable (fun (x : ℕ → α) (n : ℕ) => f (x n)) :=
    measurable_pi_iff.mpr fun k => hf.comp (measurable_pi_apply k)
  rw [runLaw_time_one, Measure.map_map (measurable_pi_apply 1) hF] at this
  rw [← this, ← runLaw_time_one K a, Measure.map_map hf (measurable_pi_apply 1)]
  rfl

/-- [ZP] adapted from UEOT `strongLumpability_iff_pathLaw`. `Statement:` for measurable `f`, `K`
lumps to `L` along `f` iff from every start the observed run has the law of the `L`-chain from the
observed start; both directions. -/
theorem lumps_iff_runLaw_map (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K]
    [IsMarkovKernel L] {f : α → β} (hf : Measurable f) :
    Lumps K L f ↔ ∀ x₀, (runLaw K x₀).map (fun x n => f (x n)) = runLaw L (f x₀) :=
  ⟨fun h x₀ => runLaw_map_of_lumps K L hf h x₀, lumps_of_runLaw_map K L hf⟩

-- Statement: CONTROL, the identity map: every kernel lumps to itself.
example (K : Kernel α α) : Lumps K K id := fun _ => Measure.map_id

/-- `Statement:` for deterministic kernels, with measurable singletons on `β`, lumping along `f` is the
semiconjugacy `f ∘ g = g' ∘ f`. -/
theorem lumps_deterministic_iff [MeasurableSingletonClass β] {g : α → α} {g' : β → β}
    (hg : Measurable g) (hg' : Measurable g') {f : α → β} (hf : Measurable f) :
    Lumps (Kernel.deterministic g hg) (Kernel.deterministic g' hg') f ↔ ∀ a, f (g a) = g' (f a) := by
  unfold Lumps
  simp only [Kernel.deterministic_apply, Measure.map_dirac' hf, dirac_eq_dirac_iff]

/-- `Statement:` if `K` is subordinate to `M` and lumps to `L` along the classes of `s`, and the quotient's
step sections are measurable, `L` is subordinate to `M.quot s`; one way. -/
theorem subordinate_quot_of_lumps (M : Motion α) (K : Kernel α α) (s : Setoid α)
    (L : Kernel (Quotient s) (Quotient s)) (hK : Subordinate M K) (h : Lumps K L (Quotient.mk s))
    (hm : ∀ X, MeasurableSet {Y | (M.quot s).step X Y}) : Subordinate (M.quot s) L := by
  intro X
  induction X using Quotient.ind with
  | _ a =>
    rw [← h a, ae_map_iff (measurable_quotient_mk'' (s := s)).aemeasurable (hm _)]
    filter_upwards [hK a] with b hb
    exact ⟨a, b, hb, rfl, rfl⟩

/-- `Statement:` the same on a countable carrier with measurable singletons, with no side condition. -/
theorem subordinate_quot_of_lumps_countable [Countable α] [MeasurableSingletonClass α]
    (M : Motion α) (K : Kernel α α) (s : Setoid α) (L : Kernel (Quotient s) (Quotient s))
    (hK : Subordinate M K) (h : Lumps K L (Quotient.mk s)) : Subordinate (M.quot s) L :=
  subordinate_quot_of_lumps M K s L hK h fun _ =>
    measurableSet_quotient.2 (Set.to_countable _).measurableSet

/-- `Statement:` the support die of `K`: OVER is positive one-step mass, UP the identity. -/
def suppMotion (K : Kernel α α) : Motion α :=
  Motion.ofTotal id (fun _ => rfl) (fun a b => 0 < K a {b})

/-- `Statement:` on a countable carrier with measurable singletons, `K` is subordinate to its support die. -/
theorem subordinate_supp [Countable α] [MeasurableSingletonClass α] (K : Kernel α α) :
    Subordinate (suppMotion K) K := by
  intro a
  rw [ae_iff]
  have : {b | ¬ (suppMotion K).step a b} = ⋃ b ∈ {b | K a {b} = 0}, ({b} : Set α) := by
    ext b; simp [suppMotion, Motion.ofTotal, pos_iff_ne_zero]
  rw [this, measure_biUnion_null_iff (Set.to_countable _)]
  exact fun b hb => hb

/-- `Statement:` on a countable carrier, if `K` has the per-class form along the classes of `s`, its
support die is step-compatible with `s`; one way (`suppControlKernel_stepCompat_not_fiberConst`). -/
theorem stepCompat_supp_of_fiberConst [Countable α] [MeasurableSingletonClass α]
    (K : Kernel α α) (s : Setoid α) (h : FiberConst K (Quotient.mk s)) :
    (suppMotion K).StepCompat s := by
  intro a a' b hr hb
  change 0 < K a {b} at hb
  have hC : MeasurableSet ((Quotient.mk s) ⁻¹' {Quotient.mk s b}) := (Set.to_countable _).measurableSet
  have hpos : 0 < K a' ((Quotient.mk s) ⁻¹' {Quotient.mk s b}) := by
    have e := congrArg (fun ν : Measure (Quotient s) => ν {Quotient.mk s b})
      (h a a' (Quotient.sound hr))
    rw [Measure.map_apply (measurable_quotient_mk'' (s := s))
        (measurableSet_quotient.2 hC),
      Measure.map_apply (measurable_quotient_mk'' (s := s))
        (measurableSet_quotient.2 hC)] at e
    rw [← e]
    exact lt_of_lt_of_le hb (measure_mono (by intro c hc; rw [Set.mem_singleton_iff.1 hc]; rfl))
  by_contra hno
  push Not at hno
  apply hpos.ne'
  have : (Quotient.mk s) ⁻¹' {Quotient.mk s b} = ⋃ c ∈ (Quotient.mk s) ⁻¹' {Quotient.mk s b},
      ({c} : Set α) := by ext c; simp
  rw [this, measure_biUnion_null_iff (Set.to_countable _)]
  intro c hc
  by_contra hne
  exact hno c (pos_iff_ne_zero.2 hne) (Quotient.exact (Set.mem_singleton_iff.1 hc).symm)

-- Statement: CONTROL A, a subordinate kernel that lumps does not make the die's relation
-- step-compatible: on `Fin 3`, classes `{0, 1}` and `{2}`, the identity kernel, and a die that also
-- steps `0 → 2` with weight 0.
example : let obs : Fin 3 → Bool := fun x => decide (x = 2)
    let M : Motion (Fin 3) := Motion.ofTotal id (fun _ => rfl) (fun a b => b = a ∨ (a = 0 ∧ b = 2))
    Subordinate M Kernel.id ∧ Lumps (Kernel.id : Kernel (Fin 3) (Fin 3)) Kernel.id obs ∧
      ¬ M.StepCompat (Setoid.ker obs) := by
  intro obs M
  refine ⟨fun a => ?_, fun a => ?_, fun h => ?_⟩
  · rw [Kernel.id_apply, ae_dirac_iff (Set.toFinite _).measurableSet]
    exact Or.inl rfl
  · rw [Kernel.id_apply, Kernel.id_apply, Measure.map_dirac' (by fun_prop)]
  · obtain ⟨b', hb', hr⟩ := h 0 1 2
      (show decide ((0 : Fin 3) = 2) = decide ((1 : Fin 3) = 2) by decide) (Or.inr ⟨rfl, rfl⟩)
    rcases hb' with rfl | ⟨h1, _⟩
    · exact (by decide : ¬ (decide ((2 : Fin 3) = 2) = decide ((1 : Fin 3) = 2))) hr
    · exact absurd h1 (by decide)

-- Statement: CONTROL B, a step-compatible die does not force lumpable weights on a kernel subordinate
-- to it: on `Fin 3`, classes `{0, 1}` and `{2}`, a die stepping everywhere, and the deterministic
-- kernel `0 ↦ 0, 1 ↦ 2, 2 ↦ 2`; that kernel's own support die is not step-compatible.
example : let obs : Fin 3 → Bool := fun x => decide (x = 2)
    let g : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else x
    let M : Motion (Fin 3) := Motion.ofTotal id (fun _ => rfl) (fun _ _ => True)
    M.StepCompat (Setoid.ker obs) ∧ Subordinate M (Kernel.deterministic g (by fun_prop)) ∧
      ¬ FiberConst (Kernel.deterministic g (by fun_prop)) obs ∧
      ¬ (suppMotion (Kernel.deterministic g (by fun_prop))).StepCompat (Setoid.ker obs) := by
  intro obs g M
  refine ⟨fun a a' b _ _ => ⟨b, trivial, rfl⟩, fun a => Filter.Eventually.of_forall fun _ => trivial,
    fun h => ?_, fun h => ?_⟩
  · have := h 0 1 (show decide ((0 : Fin 3) = 2) = decide ((1 : Fin 3) = 2) by decide)
    simp only [Kernel.deterministic_apply, Measure.map_dirac' (by fun_prop : Measurable obs),
      dirac_eq_dirac_iff] at this
    exact absurd this (by decide)
  · have h00 : (suppMotion (Kernel.deterministic g (by fun_prop))).step 0 0 := by
      show 0 < Kernel.deterministic g _ 0 {0}
      rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton _)]
      simp [g]
    obtain ⟨b', hb', hr⟩ := h 0 1 0 (show obs 0 = obs 1 by decide) h00
    change 0 < Kernel.deterministic g _ 1 {b'} at hb'
    rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton _)] at hb'
    have : g 1 = b' := by
      by_contra hne
      simp [Set.indicator, hne] at hb'
    subst this
    change obs 0 = obs (g 1) at hr
    simp [obs, g] at hr

/-- `Statement:` a kernel on `Fin 3`: `0` to `0` and `2` with masses 1/2, 1/2; `1` to `1` and `2` with
masses 1/4, 3/4; `2` to `2`. -/
noncomputable def suppControlKernel : Kernel (Fin 3) (Fin 3) :=
  Kernel.ofFunOfCountable fun a =>
    if a = 0 then (1/2 : ENNReal) • Measure.dirac 0 + (1/2 : ENNReal) • Measure.dirac 2
    else if a = 1 then (1/4 : ENNReal) • Measure.dirac 1 + (3/4 : ENNReal) • Measure.dirac 2
    else Measure.dirac 2

/-- `Statement:` CONTROL for the converse of `stepCompat_supp_of_fiberConst`: with classes `{0, 1}`
and `{2}`, the support die of `suppControlKernel` is step-compatible, and `suppControlKernel` does not
have the per-class form. -/
theorem suppControlKernel_stepCompat_not_fiberConst :
    (suppMotion suppControlKernel).StepCompat (Setoid.ker (fun x : Fin 3 => decide (x = 2))) ∧
      ¬ FiberConst suppControlKernel (fun x : Fin 3 => decide (x = 2)) := by
  have hK : ∀ a, suppControlKernel a =
      if a = 0 then (1/2 : ENNReal) • Measure.dirac 0 + (1/2 : ENNReal) • Measure.dirac 2
      else if a = 1 then (1/4 : ENNReal) • Measure.dirac 1 + (3/4 : ENNReal) • Measure.dirac 2
      else Measure.dirac 2 := fun _ => rfl
  have key : ∀ a b : Fin 3, (suppMotion suppControlKernel).step a b ↔
      ((a = 0 ∧ b = 0) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 2)) := by
    intro a b
    show 0 < suppControlKernel a {b} ↔ _
    rw [hK]
    fin_cases a <;> fin_cases b <;>
      simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · intro a a' b hr hb
    change decide (a = 2) = decide (a' = 2) at hr
    rw [key] at hb
    simp only [key]
    change ∃ b', ((a' = 0 ∧ b' = 0) ∨ (a' = 0 ∧ b' = 2) ∨ (a' = 1 ∧ b' = 1) ∨ (a' = 1 ∧ b' = 2) ∨
      (a' = 2 ∧ b' = 2)) ∧ decide (b = 2) = decide (b' = 2)
    revert a a' b
    decide
  · intro h
    have e := congrArg (fun ν : Measure Bool => ν {false}) (h 0 1 (by decide))
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at e
    have hpre : (fun x : Fin 3 => decide (x = 2)) ⁻¹' {false} = {0} ∪ {1} := by
      ext x; fin_cases x <;> simp
    rw [hpre, measure_union (by simp) (measurableSet_singleton _),
      measure_union (by simp) (measurableSet_singleton _)] at e
    rw [hK, hK] at e
    simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at e

/-- `Statement:` the runs whose observed value at some stage differs from `y₀` form a measurable set. -/
theorem measurableSet_leaves [MeasurableSingletonClass β] (y₀ : β) :
    MeasurableSet {y : ℕ → β | ∃ i, y i ≠ y₀} := by
  have : {y : ℕ → β | ∃ i, y i ≠ y₀} = ⋃ i, ((fun y => y i) ⁻¹' {y₀})ᶜ := by ext y; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => (measurable_pi_apply i (measurableSet_singleton y₀)).compl

/-- `Statement:` if `K` lumps to `L` along `f`, almost every run's observed value changes iff `L` puts
positive mass off `f x₀`; both directions. -/
theorem ae_obs_leaves_iff [MeasurableSingletonClass β] (K : Kernel α α) (L : Kernel β β)
    [IsMarkovKernel K] [IsMarkovKernel L] {f : α → β} (hf : Measurable f) (h : Lumps K L f)
    (x₀ : α) :
    (∀ᵐ x ∂(runLaw K x₀), ∃ i, f (x i) ≠ f x₀) ↔ 0 < L (f x₀) {f x₀}ᶜ := by
  have hF : Measurable (fun (x : ℕ → α) (n : ℕ) => f (x n)) :=
    measurable_pi_iff.mpr fun k => hf.comp (measurable_pi_apply k)
  rw [← ae_leaves_iff L (f x₀), ← runLaw_map_of_lumps K L hf h x₀,
    ae_map_iff hF.aemeasurable (measurableSet_leaves _)]

/-- `Statement:` if `K` lumps to `L` along `f`, `L`'s leave-weight at `f x₀` is `K x₀`'s mass off the class. -/
theorem lumped_leave_weight [MeasurableSingletonClass β] (K : Kernel α α) (L : Kernel β β)
    {f : α → β} (hf : Measurable f) (h : Lumps K L f) (x₀ : α) :
    L (f x₀) {f x₀}ᶜ = K x₀ (f ⁻¹' {f x₀}ᶜ) := by
  rw [← h x₀, Measure.map_apply hf (measurableSet_singleton _).compl]

/-- `Statement:` if `K` is subordinate to `M`, lumps along `f`, the kernel of `f` is step-compatible,
and almost every observed run changes value, the quotient die's class of `x₀` steps elsewhere; one way. -/
theorem quot_leavesAt_of_ae [MeasurableSingletonClass β] (M : Motion α) (K : Kernel α α)
    (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L] {f : α → β} (hf : Measurable f)
    (hK : Subordinate M K) (hc : M.StepCompat (Setoid.ker f)) (h : Lumps K L f) (x₀ : α)
    (hae : ∀ᵐ x ∂(runLaw K x₀), ∃ i, f (x i) ≠ f x₀) :
    (M.quot (Setoid.ker f)).LeavesAt (Quotient.mk _ x₀) := by
  rw [ae_obs_leaves_iff K L hf h, lumped_leave_weight K L hf h] at hae
  rw [Motion.quot_leavesAt_iff M f hc]
  by_contra hno
  push Not at hno
  apply hae.ne'
  exact measure_mono_null (fun b hb hs => hb (hno b hs)) (ae_iff.1 (hK x₀))

-- Statement: CONTROL, the converse of `quot_leavesAt_of_ae` fails: on `Bool`, a die stepping
-- everywhere, `f = id`, the identity kernel; the class of `false` steps elsewhere, and almost no run
-- leaves `false`.
example : let M : Motion Bool := Motion.ofTotal id (fun _ => rfl) (fun _ _ => True)
    (M.quot (Setoid.ker (id : Bool → Bool))).LeavesAt (Quotient.mk _ false) ∧
      ¬ ∀ᵐ x ∂(runLaw (Kernel.id : Kernel Bool Bool) false), ∃ i, x i ≠ false := by
  intro M
  refine ⟨(Motion.quot_leavesAt_iff M id (fun a a' b _ _ => ⟨b, trivial, rfl⟩) false).2
    ⟨true, trivial, by decide⟩, ?_⟩
  rw [ae_leaves_iff, Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton _).compl]
  simp

/-- `Statement:` on a carrier with measurable singletons, if UP is a total idempotent `r` unchanged
along steps (`UpStepInvariant`), a subordinate Markov kernel lumps along `r` to the identity kernel. -/
theorem lumps_id_of_upStepInvariant [MeasurableSingletonClass α] {r : α → α}
    (hr : ∀ x, r (r x) = r x) (st : α → α → Prop) (K : Kernel α α) [IsMarkovKernel K]
    (hK : Subordinate (Motion.ofTotal r hr st) K)
    (hU : (Motion.ofTotal r hr st).UpStepInvariant) : Lumps K Kernel.id r := by
  intro a
  rw [Kernel.id_apply]
  have he : r =ᵐ[K a] fun _ => r a := by
    filter_upwards [hK a] with b hb
    exact (Part.some_injective (hU a b hb)).symm
  rw [Measure.map_congr he, Measure.map_const, measure_univ, one_smul]

/-- `Statement:` under the same hypotheses, almost every run keeps the landing `r x₀` at every stage. -/
theorem ae_landing_const [MeasurableSingletonClass α] {r : α → α} (hrm : Measurable r)
    (hr : ∀ x, r (r x) = r x) (st : α → α → Prop) (K : Kernel α α) [IsMarkovKernel K]
    (hK : Subordinate (Motion.ofTotal r hr st) K)
    (hU : (Motion.ofTotal r hr st).UpStepInvariant) (x₀ : α) :
    ∀ᵐ x ∂(runLaw K x₀), ∀ n, r (x n) = r x₀ := by
  have hF : Measurable (fun (x : ℕ → α) (n : ℕ) => r (x n)) :=
    measurable_pi_iff.mpr fun k => hrm.comp (measurable_pi_apply k)
  have hm : MeasurableSet {y : ℕ → α | ∀ n, y n = r x₀} := by
    have : {y : ℕ → α | ∀ n, y n = r x₀} = ⋂ n, (fun y => y n) ⁻¹' {r x₀} := by ext; simp
    rw [this]; exact MeasurableSet.iInter fun n => measurable_pi_apply n (measurableSet_singleton _)
  have h0 : runLaw (Kernel.id : Kernel α α) (r x₀) {y | ∃ i, y i ≠ r x₀} = 0 := by
    have h := runLaw_leaves (Kernel.id : Kernel α α) (r x₀)
    rw [Kernel.id_apply, Measure.dirac_apply' _ (measurableSet_singleton _).compl] at h
    simpa using h
  have hid : ∀ᵐ y ∂(runLaw (Kernel.id : Kernel α α) (r x₀)), ∀ n, y n = r x₀ := by
    rw [ae_iff]; simpa using h0
  have hl := runLaw_map_of_lumps K Kernel.id hrm (lumps_id_of_upStepInvariant hr st K hK hU) x₀
  rw [← hl, ae_map_iff hF.aemeasurable hm] at hid
  exact hid

/-- `Statement:` if `K` is reversible w.r.t. `π` (Mathlib `Kernel.IsReversible`) and lumps to `L`
along measurable `f`, then `L` is reversible w.r.t. `π.map f`. -/
theorem isReversible_map_of_lumps {K : Kernel α α} {L : Kernel β β} {f : α → β}
    (hf : Measurable f) (h : Lumps K L f) {π : Measure α} (hrev : K.IsReversible π) :
    L.IsReversible (π.map f) := by
  intro A B hA hB
  rw [setLIntegral_map hA (L.measurable_coe hB) hf, setLIntegral_map hB (L.measurable_coe hA) hf]
  have e : ∀ D : Set β, MeasurableSet D → ∀ x, L (f x) D = K x (f ⁻¹' D) := fun D hD x => by
    rw [← h x, Measure.map_apply hf hD]
  simp only [e B hB, e A hA]
  exact hrev (hf hA) (hf hB)

-- Statement: a reversible Markov kernel leaves its measure invariant (Mathlib
-- `Kernel.IsReversible.invariant`), so a reversible start is a stationary one.
example (K : Kernel α α) [IsMarkovKernel K] (π : Measure α) (h : K.IsReversible π) :
    K.Invariant π := h.invariant

/-- `Statement:` every Markov kernel on `Unit` is reversible w.r.t. every measure; the CONTROL
`example` after `a4_direction_erased` uses it. -/
theorem isReversible_unit (L : Kernel Unit Unit) [IsMarkovKernel L] (ν : Measure Unit) :
    L.IsReversible ν := by
  intro A B _ _
  rcases Set.eq_empty_or_nonempty A with rfl | hA'
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl | hB'
  · simp
  rw [hA'.eq_univ, hB'.eq_univ]

/-- `Statement:` the deterministic kernel of a measurable involution `g` with `π.map g = π` is
reversible w.r.t. `π`. -/
theorem isReversible_deterministic_involutive {g : α → α} (hg : Measurable g)
    (hinv : Function.Involutive g) {π : Measure α} (hπ : π.map g = π) :
    (Kernel.deterministic g hg).IsReversible π := by
  intro A B hA hB
  simp only [Kernel.deterministic_apply]
  have e : ∀ C : Set α, MeasurableSet C → ∀ D : Set α, MeasurableSet D →
      ∫⁻ x in C, Measure.dirac (g x) D ∂π = π (g ⁻¹' D ∩ C) := by
    intro C hC D hD
    simp_rw [Measure.dirac_apply' _ hD]
    have : ∀ x, D.indicator (1 : α → ENNReal) (g x) = (g ⁻¹' D).indicator 1 x := fun _ => rfl
    simp_rw [this]
    rw [lintegral_indicator_one (hg hD), Measure.restrict_apply (hg hD)]
  rw [e A hA B hB, e B hB A hA]
  conv_lhs => rw [← hπ]
  rw [Measure.map_apply hg ((hg hB).inter hA), Set.preimage_inter, ← Set.preimage_comp,
    hinv.comp_self, Set.preimage_id, Set.inter_comm]

/-- `Statement:` a deterministic kernel is reversible w.r.t. `π` if `π`-almost every point is fixed. -/
theorem isReversible_deterministic_of_ae_id {g : α → α} (hg : Measurable g) {π : Measure α}
    (hid : ∀ᵐ x ∂π, g x = x) : (Kernel.deterministic g hg).IsReversible π := by
  intro A B hA hB
  have e : ∀ C : Set α, MeasurableSet C → ∀ D : Set α, MeasurableSet D →
      ∫⁻ x in C, Kernel.deterministic g hg x D ∂π = π (D ∩ C) := by
    intro C hC D hD
    have : ∀ᵐ x ∂(π.restrict C), Kernel.deterministic g hg x D = D.indicator 1 x := by
      filter_upwards [ae_restrict_of_ae hid] with x hx
      rw [Kernel.deterministic_apply, Measure.dirac_apply' _ hD, hx]
    rw [lintegral_congr_ae this, lintegral_indicator_one hD, Measure.restrict_apply hD]
  rw [e A hA B hB, e B hB A hA, Set.inter_comm]

/-- `Statement:` rotation of the 4-cycle. -/
def rot4 (x : Fin 4) : Fin 4 := x + 1

/-- `Statement:` the parity of a point of `Fin 4`. -/
def parity4 (x : Fin 4) : Bool := decide (x.val % 2 = 1)

/-- `Statement:` the deterministic kernel of `rot4` is reversible w.r.t. no probability measure. -/
theorem rot4_not_reversible (π : Measure (Fin 4)) [IsProbabilityMeasure π] :
    ¬ (Kernel.deterministic rot4 (measurable_of_finite _)).IsReversible π := by
  intro h
  have hz : ∀ x : Fin 4, π {x} = 0 := by
    intro x
    have := h (measurableSet_singleton x) (measurableSet_singleton (x + 1))
    rw [lintegral_singleton, lintegral_singleton, Kernel.deterministic_apply,
      Kernel.deterministic_apply, Measure.dirac_apply' _ (measurableSet_singleton _),
      Measure.dirac_apply' _ (measurableSet_singleton _)] at this
    fin_cases x <;> simpa [rot4, Set.indicator] using this
  have : π = 0 := (Measure.ext_iff_singleton).2 (by simpa using hz)
  exact IsProbabilityMeasure.ne_zero π this

/-- `Statement:` `rot4` lumps along `parity4` to the swap of `Bool`. -/
theorem rot4_lumps_parity4 :
    Lumps (Kernel.deterministic rot4 (measurable_of_finite _))
      (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)) parity4 :=
  (lumps_deterministic_iff _ _ (measurable_of_finite _)).2 (by decide)

/-- `Statement:` the swap of `Bool` is reversible w.r.t. the counting measure on `Bool`, of mass 2 (the
probability version: `boolSwap_reversible_half`). -/
theorem boolSwap_reversible :
    (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)).IsReversible
      (Measure.dirac true + Measure.dirac false) := by
  refine isReversible_deterministic_involutive _ Bool.not_not ?_
  rw [Measure.map_add _ _ (measurable_of_finite _), Measure.map_dirac' (measurable_of_finite _),
    Measure.map_dirac' (measurable_of_finite _)]
  simp [add_comm]

/-- `Statement:` `rot4` is reversible w.r.t. no probability measure, lumps along `parity4` to the swap
of `Bool`, and the swap is reversible w.r.t. the counting measure on `Bool`, which is not a probability
measure (with a probability measure: `coarse_graining_trade`); `parity4` is `zoom 1` (`parity4_eq_zoom`).
`Reading:` coarse-graining erases an arrow. -/
theorem a4_direction_erased :
    (∀ π : Measure (Fin 4), IsProbabilityMeasure π →
        ¬ (Kernel.deterministic rot4 (measurable_of_finite _)).IsReversible π) ∧
      Lumps (Kernel.deterministic rot4 (measurable_of_finite _))
        (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)) parity4 ∧
      (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)).IsReversible
        (Measure.dirac true + Measure.dirac false) :=
  ⟨fun π _ => rot4_not_reversible π, rot4_lumps_parity4, boolSwap_reversible⟩

-- Statement: CONTROL for `isReversible_map_of_lumps`, a target `Unit` makes its conclusion hold for
-- every kernel: `rot4` lumps along the map to `Unit`, and the kernel on `Unit` is reversible w.r.t.
-- every measure, while `rot4` is reversible w.r.t. no probability measure.
example : Lumps (Kernel.deterministic rot4 (measurable_of_finite _))
      (Kernel.deterministic (id : Unit → Unit) measurable_id) (fun _ : Fin 4 => ()) ∧
    ∀ ν : Measure Unit, (Kernel.deterministic (id : Unit → Unit) measurable_id).IsReversible ν :=
  ⟨(lumps_deterministic_iff _ _ (measurable_of_finite _)).2 fun _ => rfl,
    fun ν => isReversible_unit _ ν⟩

section Matrix
variable {ι κ R : Type*} [Fintype ι] [DecidableEq κ] [CommSemiring R]

/-- `Statement:` detailed balance, matrix form: `π x * P x y = π y * P y x`. -/
def DetailedBalance (P : ι → ι → R) (π : ι → R) : Prop := ∀ x y, π x * P x y = π y * P y x

/-- `Statement:` the two-time weight of the observed pair `(a, b)`: the sum of `π x * P x y` over
`x, y` with `f x = a`, `f y = b`. `Reading:` when `π` is a distribution and `P` is stochastic, this
is `Pr(f X₀ = a, f X₁ = b)`; the three-time case is proved (`chainLaw_coarse3_eq_coarseLaw3`). -/
def coarseLaw2 (π : ι → R) (P : ι → ι → R) (f : ι → κ)
    (a b : κ) : R :=
  ∑ x, ∑ y, if f x = a ∧ f y = b then π x * P x y else 0

/-- `Statement:` the three-time weight of the observed triple `(a, b, c)`: the sum of
`π x * P x y * P y z` over `x, y, z` with `f x = a`, `f y = b`, `f z = c`; when `π` is a distribution
and `P` is stochastic, this is `Pr(f X₀ = a, f X₁ = b, f X₂ = c)`. -/
def coarseLaw3 (π : ι → R) (P : ι → ι → R) (f : ι → κ)
    (a b c : κ) : R :=
  ∑ x, ∑ y, ∑ z, if f x = a ∧ f y = b ∧ f z = c then π x * P x y * P y z else 0

/-- `Statement:` reversing the order of a triple finite sum. -/
theorem sum3_reverse {M : Type*} [AddCommMonoid M] (F : ι → ι → ι → M) :
    ∑ x, ∑ y, ∑ z, F z y x = ∑ x, ∑ y, ∑ z, F x y z :=
  calc ∑ x, ∑ y, ∑ z, F z y x = ∑ y, ∑ x, ∑ z, F z y x := Finset.sum_comm
    _ = ∑ y, ∑ z, ∑ x, F z y x := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, F z y x := Finset.sum_comm

/-- `Statement:` under detailed balance, for every observer `f`, `coarseLaw2` is symmetric in `a, b`. -/
theorem coarseLaw2_reverse {P : ι → ι → R} {π : ι → R} (h : DetailedBalance P π) (f : ι → κ)
    (a b : κ) : coarseLaw2 π P f a b = coarseLaw2 π P f b a := by
  unfold coarseLaw2
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hc : f y = a ∧ f x = b
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true ⟨hc.2, hc.1⟩), h]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
      ite_eq_right_of_eq_false _ _ (eq_false fun h' => hc ⟨h'.2, h'.1⟩)]

/-- `Statement:` under detailed balance, for every observer `f`, `coarseLaw3 a b c = coarseLaw3 c b a`. -/
theorem coarseLaw3_reverse {P : ι → ι → R} {π : ι → R} (h : DetailedBalance P π) (f : ι → κ)
    (a b c : κ) : coarseLaw3 π P f a b c = coarseLaw3 π P f c b a := by
  unfold coarseLaw3
  have key : ∀ x y z, (if f x = a ∧ f y = b ∧ f z = c then π x * P x y * P y z else 0) =
      (if f z = c ∧ f y = b ∧ f x = a then π z * P z y * P y x else 0) := by
    intro x y z
    by_cases hc : f x = a ∧ f y = b ∧ f z = c
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨hc.2.2, hc.2.1, hc.1⟩)]
      calc π x * P x y * P y z = (π y * P y x) * P y z := by rw [h x y]
        _ = P y x * (π y * P y z) := by ring
        _ = P y x * (π z * P z y) := by rw [h y z]
        _ = π z * P z y * P y x := by ring
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
        ite_eq_right_of_eq_false _ _ (eq_false fun h' => hc ⟨h'.2.2, h'.2.1, h'.1⟩)]
  simp_rw [key]
  exact sum3_reverse (fun z y x => if f z = c ∧ f y = b ∧ f x = a then π z * P z y * P y x else 0)

end Matrix

section Aggregated
variable {ι κ : Type*} [Fintype ι] [DecidableEq κ]

/-- `Statement:` the `π`-weight of the class `a` of `f`. -/
noncomputable def classWeight (π : ι → ℚ) (f : ι → κ) (a : κ) : ℚ := ∑ x, if f x = a then π x else 0

/-- `Statement:` the aggregated chain `coarseLaw2 a b / classWeight a`, for every observer `f`. -/
noncomputable def aggregatedChain (π : ι → ℚ) (P : ι → ι → ℚ) (f : ι → κ) (a b : κ) : ℚ :=
  coarseLaw2 π P f a b / classWeight π f a

/-- `Statement:` under detailed balance, if every class has nonzero weight, the aggregated chain
satisfies detailed balance w.r.t. `classWeight`, for every observer `f`. -/
theorem aggregatedChain_detailedBalance {P : ι → ι → ℚ} {π : ι → ℚ} (h : DetailedBalance P π)
    (f : ι → κ) (hpos : ∀ a, classWeight π f a ≠ 0) :
    DetailedBalance (aggregatedChain π P f) (classWeight π f) := by
  intro a b
  unfold aggregatedChain
  rw [mul_div_cancel₀ _ (hpos a), mul_div_cancel₀ _ (hpos b), coarseLaw2_reverse h]

end Aggregated

/-- `Statement:` the lazy pair chain on `Fin 4`: `0 ↔ 1` and `2 ↔ 3`, each with weight 1/2. -/
def lazyPairs : Fin 4 → Fin 4 → ℚ :=
  ![![1/2, 1/2, 0, 0], ![1/2, 1/2, 0, 0], ![0, 0, 1/2, 1/2], ![0, 0, 1/2, 1/2]]

/-- `Statement:` the uniform weight vector on `Fin 4`. -/
def unifFin4 : Fin 4 → ℚ := fun _ => 1/4

/-- `Statement:` the observer `0 ↦ 0`, `2 ↦ 1`, `1, 3 ↦ 2`. -/
def lazyPairsProj (x : Fin 4) : Fin 3 := if x.val = 0 then 0 else if x.val = 2 then 1 else 2

/-- `Statement:` `lazyPairs` satisfies detailed balance w.r.t. `unifFin4`. -/
theorem detailedBalance_lazyPairs : DetailedBalance lazyPairs unifFin4 := by
  intro x y; fin_cases x <;> fin_cases y <;> simp [lazyPairs, unifFin4]

/-- `Statement:` the mass row `x` of `P` sends into the class `b` of `lazyPairsProj`. -/
def projClassMass (P : Fin 4 → Fin 4 → ℚ) (x : Fin 4) (b : Fin 3) : ℚ :=
  ∑ y, if lazyPairsProj y = b then P x y else 0

/-- `Statement:` the witness that `lazyPairs` is not lumpable along `lazyPairsProj`: `1` and `3` share a
class and send different mass into class `0`. -/
theorem lazyPairs_not_lumpable :
    lazyPairsProj 1 = lazyPairsProj 3 ∧ projClassMass lazyPairs 1 0 ≠ projClassMass lazyPairs 3 0 := by
  refine ⟨by decide, ?_⟩
  simp [projClassMass, Fin.sum_univ_four, lazyPairsProj, lazyPairs]

/-- `Statement:` no `ν : Fin 3 → ℚ` and `Q : Fin 3 → Fin 3 → ℚ` give
`coarseLaw3 unifFin4 lazyPairs lazyPairsProj a b c = ν a * Q a b * Q b c` at every `a b c`. -/
theorem lazyPairs_coarse_not_markov :
    ¬ ∃ (ν : Fin 3 → ℚ) (Q : Fin 3 → Fin 3 → ℚ),
      ∀ a b c, coarseLaw3 unifFin4 lazyPairs lazyPairsProj a b c = ν a * Q a b * Q b c := by
  rintro ⟨ν, Q, hQ⟩
  have e020 : coarseLaw3 unifFin4 lazyPairs lazyPairsProj 0 2 0 = 1/16 := by
    simp [coarseLaw3, Fin.sum_univ_four, lazyPairsProj, lazyPairs, unifFin4]; norm_num
  have e121 : coarseLaw3 unifFin4 lazyPairs lazyPairsProj 1 2 1 = 1/16 := by
    simp [coarseLaw3, Fin.sum_univ_four, lazyPairsProj, lazyPairs, unifFin4]; norm_num
  have e021 : coarseLaw3 unifFin4 lazyPairs lazyPairsProj 0 2 1 = 0 := by
    simp [coarseLaw3, Fin.sum_univ_four, lazyPairsProj, lazyPairs, unifFin4]
  have h1 := hQ 0 2 0; have h2 := hQ 1 2 1; have h3 := hQ 0 2 1
  rw [e020] at h1; rw [e121] at h2; rw [e021] at h3
  have a1 : ν 0 * Q 0 2 ≠ 0 := by
    intro e; rw [e, zero_mul] at h1; norm_num at h1
  have a2 : Q 2 1 ≠ 0 := by
    intro e; rw [e, mul_zero] at h2; norm_num at h2
  exact mul_ne_zero a1 a2 h3.symm

/-- `Statement:` the observed three-time statistic of `lazyPairs` under `lazyPairsProj` from `unifFin4`
is reversal-symmetric. -/
theorem lazyPairs_coarse_reversal_symmetric (a b c : Fin 3) :
    coarseLaw3 unifFin4 lazyPairs lazyPairsProj a b c =
      coarseLaw3 unifFin4 lazyPairs lazyPairsProj c b a :=
  coarseLaw3_reverse detailedBalance_lazyPairs lazyPairsProj a b c

/-- `Statement:` the involution `x ↦ 3 - x` of `Fin 4`. -/
def flip4 (x : Fin 4) : Fin 4 := ⟨3 - x.val, by omega⟩

/-- `Statement:` `lazyPairs x y = lazyPairs (flip4 y) (flip4 x)` at every `x y`. -/
theorem lazyPairs_sigma_reversible : ∀ x y, lazyPairs x y = lazyPairs (flip4 y) (flip4 x) := by
  intro x y; fin_cases x <;> fin_cases y <;> rfl

/-- `Statement:` the absorbing map on `Fin 4`: `0 ↦ 1`, `2 ↦ 3`, `1` and `3` fixed. -/
def absorb4 (x : Fin 4) : Fin 4 := if x.val = 0 then 1 else if x.val = 2 then 3 else x

/-- `Statement:` the constant map to `2` on `Fin 3`. -/
def absorb4Coarse (_ : Fin 3) : Fin 3 := 2

/-- `Statement:` the deterministic kernel of `absorb4` lumps along `lazyPairsProj` to `absorb4Coarse`. -/
theorem absorb4_lumps :
    Lumps (Kernel.deterministic absorb4 (measurable_of_finite _))
      (Kernel.deterministic absorb4Coarse (measurable_of_finite _)) lazyPairsProj :=
  (lumps_deterministic_iff _ _ (measurable_of_finite _)).2 (by decide)

/-- `Statement:` the deterministic kernel of `absorb4` is reversible w.r.t. every measure carried by
the fixed points `1` and `3` of `absorb4`. -/
theorem absorb4_reversible (s t : ENNReal) :
    (Kernel.deterministic absorb4 (measurable_of_finite _)).IsReversible
      (s • Measure.dirac (1 : Fin 4) + t • Measure.dirac (3 : Fin 4)) := by
  refine isReversible_deterministic_of_ae_id _ ?_
  rw [ae_add_measure_iff]
  have hm : MeasurableSet {x : Fin 4 | absorb4 x = x} := (Set.toFinite _).measurableSet
  refine ⟨Measure.ae_smul_measure ((ae_dirac_iff hm).2 (by decide)) _,
    Measure.ae_smul_measure ((ae_dirac_iff hm).2 (by decide)) _⟩

/-- `Statement:` the deterministic kernel of `absorb4Coarse` is reversible w.r.t. the image under
`lazyPairsProj` of each of those measures (`isReversible_map_of_lumps`). -/
theorem absorb4_coarse_reversible (s t : ENNReal) :
    (Kernel.deterministic absorb4Coarse (measurable_of_finite _)).IsReversible
      ((s • Measure.dirac (1 : Fin 4) + t • Measure.dirac (3 : Fin 4)).map lazyPairsProj) :=
  isReversible_map_of_lumps (measurable_of_finite _) absorb4_lumps (absorb4_reversible s t)

/-- `Statement:` no involution `σ` of `Fin 4` has `step a b ↔ step (σ b) (σ a)` in `Motion.ofFun absorb4`. -/
theorem absorb4_not_sigma_reversible :
    ¬ ∃ σ : Fin 4 → Fin 4, Function.Involutive σ ∧
      ∀ a b, (Motion.ofFun absorb4).step a b ↔ (Motion.ofFun absorb4).step (σ b) (σ a) := by
  rintro ⟨σ, hσ, h⟩
  have e0 : σ 0 = absorb4 (σ 1) := (h 0 1).1 (show (1 : Fin 4) = absorb4 0 by decide)
  have e1 : σ 1 = absorb4 (σ 1) := (h 1 1).1 (show (1 : Fin 4) = absorb4 1 by decide)
  exact absurd (hσ.injective (e0.trans e1.symm)) (by decide)

/-- `Statement:` under the chain from any probability law `μ`, `(x 0, x 1)` has law `μ ⊗ₘ K`. -/
theorem chainLaw_pair (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] :
    (chainLaw μ K).map (fun x => (x 0, x 1)) = μ ⊗ₘ K := by
  have h01 : (fun x : ℕ → α => (x 0, x 1)) =
      Prod.map (pathLast 0) id ∘ (fun x => (Preorder.frestrictLe 0 x, x (0 + 1))) := by
    funext x; rfl
  rw [h01, ← Measure.map_map ((measurable_pathLast 0).prodMap measurable_id) (by fun_prop),
    ← chainLaw_step μ K 0]
  have hk : homK K 0 = K.comap (pathLast 0) (measurable_pathLast 0) := rfl
  rw [hk, compProd_comap_map _ (measurable_pathLast 0), chainLaw_prefix_zero,
    Measure.map_map (measurable_pathLast 0)
      (MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm.measurable]
  have : pathLast 0 ∘ (MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm = id := by
    funext a; rfl
  rw [this, Measure.map_id]

/-- `Statement:` the first two coordinates of a history indexed by `Iic 1`. -/
def histFirst2 (h : (i : Iic 1) → α) : α × α :=
  (h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩, h ⟨1, Finset.mem_Iic.mpr le_rfl⟩)

/-- `Statement:` `histFirst2` is measurable. -/
theorem measurable_histFirst2 : Measurable (histFirst2 (α := α)) := by
  unfold histFirst2; fun_prop

/-- `Statement:` `((x 0, x 1), x 2)` has law `(μ ⊗ₘ K) ⊗ₘ K` read at the second coordinate. -/
theorem chainLaw_triple (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] :
    (chainLaw μ K).map (fun x => ((x 0, x 1), x 2)) =
      (μ ⊗ₘ K) ⊗ₘ K.comap Prod.snd measurable_snd := by
  have h12 : (fun x : ℕ → α => ((x 0, x 1), x 2)) =
      Prod.map histFirst2 id ∘ (fun x => (Preorder.frestrictLe 1 x, x (1 + 1))) := by
    funext x; rfl
  rw [h12, ← Measure.map_map (measurable_histFirst2.prodMap measurable_id) (by fun_prop),
    ← chainLaw_step μ K 1]
  have hk : homK K 1 = (K.comap Prod.snd measurable_snd).comap histFirst2 measurable_histFirst2 := by
    ext h s hs; rfl
  rw [hk, compProd_comap_map _ measurable_histFirst2,
    Measure.map_map measurable_histFirst2 (Preorder.measurable_frestrictLe 1)]
  have : histFirst2 ∘ Preorder.frestrictLe 1 = fun x : ℕ → α => (x 0, x 1) := by funext x; rfl
  rw [this, chainLaw_pair]

section Discrete
variable [MeasurableSingletonClass α] [Countable α]

/-- `Statement:` `Pr_μ(x 0 = a, x 1 = b, x 2 = c) = μ {a} * K a {b} * K b {c}`. -/
theorem chainLaw_triple_singleton (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] (a b c : α) :
    (chainLaw μ K).map (fun x => (x 0, x 1, x 2)) {(a, b, c)} = μ {a} * K a {b} * K b {c} := by
  have hm1 : Measurable (fun x : ℕ → α => (x 0, x 1, x 2)) := by fun_prop
  have hm2 : Measurable (fun x : ℕ → α => ((x 0, x 1), x 2)) := by fun_prop
  rw [Measure.map_apply hm1 (measurableSet_singleton _)]
  have hpre : (fun x : ℕ → α => (x 0, x 1, x 2)) ⁻¹' {(a, b, c)} =
      (fun x : ℕ → α => ((x 0, x 1), x 2)) ⁻¹' ({(a, b)} ×ˢ {c}) := by
    ext x; simp [and_assoc]
  rw [hpre, ← Measure.map_apply hm2 ((measurableSet_singleton _).prod (measurableSet_singleton _)),
    chainLaw_triple, Measure.compProd_apply_prod (measurableSet_singleton _)
      (measurableSet_singleton _), lintegral_singleton, Kernel.comap_apply,
    ← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton _)
      (measurableSet_singleton _), lintegral_singleton]
  ring

/-- `Statement:` the matrix `K x {y}` read off a kernel. -/
noncomputable def kernelMat (K : Kernel α α) (x y : α) : ENNReal := K x {y}

/-- `Statement:` the vector `μ {x}` read off a measure. -/
noncomputable def measureVec (μ : Measure α) (x : α) : ENNReal := μ {x}

/-- `Statement:` on a finite carrier with measurable singletons, for every Markov kernel, every initial
probability law `μ` and every measurable observer `f` into a space with measurable singletons, the law
of `(f (x 0), f (x 1), f (x 2))` at `(a, b, c)` is `coarseLaw3` of `measureVec μ` and `kernelMat K`. -/
theorem chainLaw_coarse3_eq_coarseLaw3 [Fintype α] {κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [DecidableEq κ] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (f : α → κ) (hf : Measurable f) (a b c : κ) :
    (chainLaw μ K).map (fun x => (f (x 0), f (x 1), f (x 2))) {(a, b, c)} =
      coarseLaw3 (measureVec μ) (kernelMat K) f a b c := by
  have hg : Measurable (fun t : α × α × α => (f t.1, f t.2.1, f t.2.2)) := by fun_prop
  have hcomp : (fun x : ℕ → α => (f (x 0), f (x 1), f (x 2))) =
      (fun t : α × α × α => (f t.1, f t.2.1, f t.2.2)) ∘ (fun x => (x 0, x 1, x 2)) := rfl
  classical
  rw [hcomp, ← Measure.map_map hg (by fun_prop), Measure.map_apply hg (measurableSet_singleton _)]
  set ν := (chainLaw μ K).map (fun x => (x 0, x 1, x 2)) with hν
  have hS : ν ((fun t : α × α × α => (f t.1, f t.2.1, f t.2.2)) ⁻¹' {(a, b, c)}) =
      ∑ t : α × α × α, if (f t.1, f t.2.1, f t.2.2) = (a, b, c) then ν {t} else 0 := by
    rw [← Finset.sum_filter, sum_measure_singleton]
    congr 1
    ext t; simp
  rw [hS]
  unfold coarseLaw3
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [Prod.mk.injEq]
  split_ifs
  · exact chainLaw_triple_singleton μ K x y z
  · rfl

omit [Countable α] in
/-- `Statement:` `K.IsReversible μ` gives `DetailedBalance (kernelMat K) (measureVec μ)`. -/
theorem detailedBalance_of_isReversible (μ : Measure α) (K : Kernel α α) (h : K.IsReversible μ) :
    DetailedBalance (kernelMat K) (measureVec μ) := by
  intro x y
  have := h (measurableSet_singleton x) (measurableSet_singleton y)
  rw [lintegral_singleton, lintegral_singleton] at this
  simpa [kernelMat, measureVec, mul_comm] using this

/-- `Statement:` on a finite carrier with measurable singletons, if `K` is reversible w.r.t. the initial
law `μ`, then for every measurable observer `f` into a space with measurable singletons the observed
three-time law at `(a, b, c)` equals that at `(c, b, a)`. -/
theorem chainLaw_coarse3_reverse [Finite α] {κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : K.IsReversible μ) (f : α → κ) (hf : Measurable f)
    (a b c : κ) :
    (chainLaw μ K).map (fun x => (f (x 0), f (x 1), f (x 2))) {(a, b, c)} =
      (chainLaw μ K).map (fun x => (f (x 0), f (x 1), f (x 2))) {(c, b, a)} := by
  classical
  have := Fintype.ofFinite α
  rw [chainLaw_coarse3_eq_coarseLaw3 μ K f hf, chainLaw_coarse3_eq_coarseLaw3 μ K f hf,
    coarseLaw3_reverse (detailedBalance_of_isReversible μ K hrev)]

end Discrete

/-! #### § XII, every window: reversal at every number of times, and the trade

`Reading:` under detailed balance a path and its reversal have equal weight at every length
(`pathWeight_rev`); the chain-level statements, every premise in their docstrings, are
`chainLaw_coarseN_map_reverse` (from time 0) and `chainLaw_window_map_reverse` (from every time).
Without detailed balance the reversal can fail: `rot4_coarse_not_reversal_symmetric` (matrix level) and
`rot4_chainLaw_not_reversal_symmetric` (chain level). `coarse_graining_trade` pairs the reversal with
`a4_direction_erased`. -/

section MatrixN
variable {ι κ R : Type*} [CommSemiring R]

/-- `Statement:` the weight `π (x 0) * ∏ i < n, P (x i) (x (i + 1))` of the path `x 0, …, x n`. -/
def pathWeight (π : ι → R) (P : ι → ι → R) {n : ℕ} (x : Fin (n + 1) → ι) : R :=
  π (x 0) * ∏ i : Fin n, P (x i.castSucc) (x i.succ)

/-- `Statement:` under detailed balance, a path's weight is the end weight `π (x n)` times the
transitions read backwards. -/
theorem pathWeight_eq_end {P : ι → ι → R} {π : ι → R} (h : DetailedBalance P π) :
    ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      pathWeight π P x = π (x (Fin.last n)) * ∏ i : Fin n, P (x i.succ) (x i.castSucc) := by
  intro n
  induction n with
  | zero => intro x; simp [pathWeight]
  | succ n ih =>
    intro x
    have hi : π (x 0) * ∏ i : Fin n, P (x i.castSucc.castSucc) (x i.succ.castSucc) =
        π (x (Fin.last n).castSucc) * ∏ i : Fin n, P (x i.succ.castSucc) (x i.castSucc.castSucc) :=
      ih (Fin.init x)
    unfold pathWeight
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    show π (x 0) * ((∏ i : Fin n, P (x i.castSucc.castSucc) (x i.succ.castSucc)) *
        P (x (Fin.last n).castSucc) (x (Fin.last (n + 1)))) =
      π (x (Fin.last (n + 1))) * ((∏ i : Fin n, P (x i.succ.castSucc) (x i.castSucc.castSucc)) *
        P (x (Fin.last (n + 1))) (x (Fin.last n).castSucc))
    rw [← mul_assoc, hi]
    calc π (x (Fin.last n).castSucc) * (∏ i : Fin n, P (x i.succ.castSucc) (x i.castSucc.castSucc)) *
          P (x (Fin.last n).castSucc) (x (Fin.last (n + 1)))
        = (π (x (Fin.last n).castSucc) * P (x (Fin.last n).castSucc) (x (Fin.last (n + 1)))) *
            ∏ i : Fin n, P (x i.succ.castSucc) (x i.castSucc.castSucc) := by ring
      _ = (π (x (Fin.last (n + 1))) * P (x (Fin.last (n + 1))) (x (Fin.last n).castSucc)) *
            ∏ i : Fin n, P (x i.succ.castSucc) (x i.castSucc.castSucc) := by rw [h]
      _ = π (x (Fin.last (n + 1))) *
            ((∏ i : Fin n, P (x i.succ.castSucc) (x i.castSucc.castSucc)) *
              P (x (Fin.last (n + 1))) (x (Fin.last n).castSucc)) := by ring

/-- `Statement:` under detailed balance, a path and its reversal `x ∘ Fin.rev` have equal weight, at
every length. -/
theorem pathWeight_rev {P : ι → ι → R} {π : ι → R} (h : DetailedBalance P π) {n : ℕ}
    (x : Fin (n + 1) → ι) : pathWeight π P x = pathWeight π P (x ∘ Fin.rev) := by
  rw [pathWeight_eq_end h]
  unfold pathWeight
  simp only [Function.comp_apply, Fin.rev_zero, Fin.rev_castSucc, Fin.rev_succ]
  congr 1
  exact (Equiv.prod_comp Fin.revPerm (fun i : Fin n => P (x i.succ) (x i.castSucc))).symm

/-- `Statement:` the weight of a path of length `n + 2` is the weight of its initial segment times the
last transition. -/
theorem pathWeight_succ (π : ι → R) (P : ι → ι → R) {n : ℕ} (y : Fin (n + 2) → ι) :
    pathWeight π P y = pathWeight π P (Fin.init y) * P (y (Fin.last n).castSucc) (y (Fin.last (n + 1))) := by
  unfold pathWeight
  rw [Fin.prod_univ_castSucc, mul_assoc]
  rfl

variable [Fintype ι] [DecidableEq κ]

/-- `Statement:` the observed statistic of `n + 1` consecutive times: the total weight of the paths `x`
with `f ∘ x = a`. -/
def coarseLawN (π : ι → R) (P : ι → ι → R) (f : ι → κ) {n : ℕ} (a : Fin (n + 1) → κ) : R :=
  ∑ x : Fin (n + 1) → ι, if f ∘ x = a then pathWeight π P x else 0

/-- `Statement:` under detailed balance, over any commutative semiring, for every observer `f` and every
`n`, `coarseLawN π P f a = coarseLawN π P f (a ∘ Fin.rev)`. -/
theorem coarseLawN_reverse {P : ι → ι → R} {π : ι → R} (h : DetailedBalance P π) (f : ι → κ)
    {n : ℕ} (a : Fin (n + 1) → κ) : coarseLawN π P f a = coarseLawN π P f (a ∘ Fin.rev) := by
  unfold coarseLawN
  let σ : Equiv.Perm (Fin (n + 1) → ι) :=
    Function.Involutive.toPerm (fun x => x ∘ Fin.rev) (fun x => by funext i; simp)
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hσ : σ x = x ∘ Fin.rev := rfl
  rw [hσ]
  have hiff : (f ∘ (x ∘ Fin.rev) = a) ↔ (f ∘ x = a ∘ Fin.rev) := by
    constructor
    · intro e; funext i
      have := congrFun e (Fin.rev i)
      simpa using this
    · intro e; funext i
      have := congrFun e (Fin.rev i)
      simpa using this
  by_cases hc : f ∘ x = a ∘ Fin.rev
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 hc)), ite_eq_left_of_eq_true _ _ (eq_true hc),
      pathWeight_rev h x]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun e => hc (hiff.1 e))),
      ite_eq_right_of_eq_false _ _ (eq_false hc)]

/-- `Statement:` along the identity observer, `coarseLawN` is the path weight. -/
theorem coarseLawN_id (π : ι → R) (P : ι → ι → R) [DecidableEq ι] {n : ℕ} (a : Fin (n + 1) → ι) :
    coarseLawN π P id a = pathWeight π P a := by
  unfold coarseLawN
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- `Statement:` a sum over `Fin 3 → ι` is the triple sum over `![a, b, c]`. -/
theorem sum_fin3 {M : Type*} [AddCommMonoid M] (G : (Fin 3 → ι) → M) :
    ∑ x : Fin 3 → ι, G x = ∑ a, ∑ b, ∑ c, G ![a, b, c] := by
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← (Fin.consEquiv fun _ => ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_unique]
  congr 1

/-- `Statement:` `coarseLaw3 π P f a b c = coarseLawN π P f ![a, b, c]`. -/
theorem coarseLaw3_eq_coarseLawN (π : ι → R) (P : ι → ι → R) (f : ι → κ) (a b c : κ) :
    coarseLaw3 π P f a b c = coarseLawN π P f ![a, b, c] := by
  unfold coarseLaw3 coarseLawN
  rw [sum_fin3]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  have hiff : (f ∘ ![x, y, z] = ![a, b, c]) ↔ (f x = a ∧ f y = b ∧ f z = c) := by
    constructor
    · intro e
      exact ⟨congrFun e 0, congrFun e 1, congrFun e 2⟩
    · rintro ⟨h1, h2, h3⟩; funext i; fin_cases i <;> simp [h1, h2, h3]
  by_cases hc : f x = a ∧ f y = b ∧ f z = c
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true (hiff.2 hc))]
    simp [pathWeight, Fin.prod_univ_two, mul_assoc]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc),
      ite_eq_right_of_eq_false _ _ (eq_false (fun e => hc (hiff.1 e)))]

-- Statement: `coarseLaw3_reverse` is `coarseLawN_reverse` at `n = 2`.
example {P : ι → ι → R} {π : ι → R} (h : DetailedBalance P π) (f : ι → κ) (a b c : κ) :
    coarseLaw3 π P f a b c = coarseLaw3 π P f c b a := by
  rw [coarseLaw3_eq_coarseLawN, coarseLaw3_eq_coarseLawN, coarseLawN_reverse h]
  congr 1
  funext i; fin_cases i <;> rfl

end MatrixN

-- Statement: `lazyPairs` under `lazyPairsProj` (not lumpable, `lazyPairs_not_lumpable`) has a
-- reversal-symmetric observed statistic at every `n`.
example (n : ℕ) (a : Fin (n + 1) → Fin 3) :
    coarseLawN unifFin4 lazyPairs lazyPairsProj a =
      coarseLawN unifFin4 lazyPairs lazyPairsProj (a ∘ Fin.rev) :=
  coarseLawN_reverse detailedBalance_lazyPairs lazyPairsProj a

/-- `Statement:` the transition matrix of `rot4` over ℚ: `rotMat x y = 1` iff `y = rot4 x`, else 0. -/
def rotMat (x y : Fin 4) : ℚ := if y = rot4 x then 1 else 0

/-- `Statement:` `rotMat` does not satisfy detailed balance w.r.t. `unifFin4`. -/
theorem rotMat_not_detailedBalance : ¬ DetailedBalance rotMat unifFin4 := by
  intro h
  have := h 0 1
  simp [rotMat, unifFin4, rot4] at this

/-- `Statement:` CONTROL for `coarseLawN_reverse` without detailed balance: along the identity observer,
the two-time statistic of `rotMat` from `unifFin4` at `(0, 1)` differs from that at `(1, 0)`. -/
theorem rot4_coarse_not_reversal_symmetric :
    coarseLawN unifFin4 rotMat id (![0, 1] : Fin 2 → Fin 4) ≠
      coarseLawN unifFin4 rotMat id ((![0, 1] : Fin 2 → Fin 4) ∘ Fin.rev) := by
  rw [coarseLawN_id, coarseLawN_id]
  simp [pathWeight, rotMat, unifFin4, rot4, Fin.rev]

section MeasureN

/-- `Statement:` the first `n + 1` coordinates of a path, indexed by `Fin (n + 1)`. -/
def finPath (n : ℕ) (x : ℕ → α) : Fin (n + 1) → α := fun i => x i

/-- `Statement:` `finPath n` is measurable. -/
theorem measurable_finPath (n : ℕ) : Measurable (finPath (α := α) n) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- `Statement:` the time-0 marginal of `chainLaw μ K` is `μ`. -/
theorem chainLaw_map_zero (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] : (chainLaw μ K).map (fun x => x 0) = μ := by
  have : (fun x : ℕ → α => x 0) = Prod.fst ∘ (fun x => (x 0, x 1)) := rfl
  rw [this, ← Measure.map_map measurable_fst (by fun_prop), chainLaw_pair, ← Measure.fst,
    Measure.fst_compProd]

variable [MeasurableSingletonClass α]

/-- `Statement:` with measurable singletons, the first `n + 1` coordinates of `chainLaw μ K` put mass
`pathWeight (measureVec μ) (kernelMat K) y`, that is `μ {y 0} * ∏ i < n, K (y i) {y (i + 1)}`, on `{y}`. -/
theorem chainLaw_finPath_singleton (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] : ∀ (n : ℕ) (y : Fin (n + 1) → α),
      (chainLaw μ K).map (finPath n) {y} = pathWeight (measureVec μ) (kernelMat K) y := by
  intro n
  induction n with
  | zero =>
    intro y
    rw [Measure.map_apply (measurable_finPath 0) (measurableSet_singleton y)]
    have hpre : finPath 0 ⁻¹' {y} = (fun x : ℕ → α => x 0) ⁻¹' {y 0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
      constructor
      · intro e; exact e 0
      · intro e i
        obtain ⟨k, hk⟩ := i
        obtain rfl : k = 0 := by omega
        exact e
    rw [hpre, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      chainLaw_map_zero]
    simp [pathWeight, measureVec]
  | succ n ih =>
    intro y
    let h : (i : Finset.Iic n) → α := fun i =>
      y ⟨i, by have := Finset.mem_Iic.mp i.2; omega⟩
    have hpre : finPath (n + 1) ⁻¹' {y} =
        (fun x : ℕ → α => (Preorder.frestrictLe n x, x (n + 1))) ⁻¹' {(h, y (Fin.last (n + 1)))} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, funext_iff]
      constructor
      · intro e
        refine ⟨fun i => ?_, e (Fin.last (n + 1))⟩
        rw [Preorder.frestrictLe_apply]
        exact e ⟨i, by have := Finset.mem_Iic.mp i.2; omega⟩
      · rintro ⟨e1, e2⟩ i
        by_cases hi : (i : ℕ) ≤ n
        · have := e1 ⟨i, Finset.mem_Iic.mpr hi⟩
          rw [Preorder.frestrictLe_apply] at this
          exact this
        · have hl : i = Fin.last (n + 1) := Fin.ext (by have := i.2; simp; omega)
          subst hl
          exact e2
    have hpre2 : (Preorder.frestrictLe n : (ℕ → α) → ((i : Finset.Iic n) → α)) ⁻¹'
        ({h} : Set ((i : Finset.Iic n) → α)) = finPath n ⁻¹' {Fin.init y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
      constructor
      · intro e i
        have := e ⟨i, Finset.mem_Iic.mpr (by omega)⟩
        rw [Preorder.frestrictLe_apply] at this
        exact this
      · intro e i
        rw [Preorder.frestrictLe_apply]
        exact e ⟨i, by have := Finset.mem_Iic.mp i.2; omega⟩
    have hprod : Measurable (fun x : ℕ → α => (Preorder.frestrictLe n x, x (n + 1))) := by fun_prop
    rw [Measure.map_apply (measurable_finPath (n + 1)) (measurableSet_singleton y), hpre,
      ← Measure.map_apply hprod (measurableSet_singleton _), ← chainLaw_step,
      ← Set.singleton_prod_singleton, Measure.compProd_apply_prod (measurableSet_singleton _)
        (measurableSet_singleton _), lintegral_singleton,
      Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton _), hpre2,
      ← Measure.map_apply (measurable_finPath n) (measurableSet_singleton _), ih,
      pathWeight_succ, mul_comm]
    rfl

/-- `Statement:` on a finite carrier with measurable singletons, for an initial probability law `μ`, a
Markov kernel `K` and a measurable observer `f` into a space with measurable singletons, the law of
`(f (x 0), …, f (x n))` at `a` is `coarseLawN (measureVec μ) (kernelMat K) f a`. -/
theorem chainLaw_coarseN_eq_coarseLawN [Fintype α] {κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [DecidableEq κ] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (f : α → κ) (hf : Measurable f) (n : ℕ)
    (a : Fin (n + 1) → κ) :
    (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x i)) {a} =
      coarseLawN (measureVec μ) (kernelMat K) f a := by
  classical
  have hg : Measurable (fun y : Fin (n + 1) → α => f ∘ y) :=
    measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)
  have hcomp : (fun (x : ℕ → α) (i : Fin (n + 1)) => f (x i)) =
      (fun y : Fin (n + 1) → α => f ∘ y) ∘ finPath n := rfl
  rw [hcomp, ← Measure.map_map hg (measurable_finPath n),
    Measure.map_apply hg (measurableSet_singleton _)]
  set ν := (chainLaw μ K).map (finPath n) with hν
  have hS : ν ((fun y : Fin (n + 1) → α => f ∘ y) ⁻¹' {a}) =
      ∑ y : Fin (n + 1) → α, if f ∘ y = a then ν {y} else 0 := by
    rw [← Finset.sum_filter, sum_measure_singleton]
    congr 1
    ext y; simp
  rw [hS]
  unfold coarseLawN
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs
  · exact chainLaw_finPath_singleton μ K n y
  · rfl

/-- `Statement:` on a finite carrier with measurable singletons, if the Markov kernel `K` is reversible
w.r.t. the initial probability law `μ`, then for every measurable observer `f` into a space with
measurable singletons and every `n`, the observed law of `n + 1` times at `a` equals that at
`a ∘ Fin.rev`. -/
theorem chainLaw_coarseN_reverse [Finite α] {κ : Type*} [MeasurableSpace κ]
    [MeasurableSingletonClass κ] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : K.IsReversible μ) (f : α → κ) (hf : Measurable f)
    (n : ℕ) (a : Fin (n + 1) → κ) :
    (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x i)) {a} =
      (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x i)) {a ∘ Fin.rev} := by
  classical
  have := Fintype.ofFinite α
  rw [chainLaw_coarseN_eq_coarseLawN μ K f hf, chainLaw_coarseN_eq_coarseLawN μ K f hf,
    coarseLawN_reverse (detailedBalance_of_isReversible μ K hrev)]

-- Statement: `chainLaw_coarseN_reverse` at `n = 2` gives the three-time reversal, `(a 0, a 1, a 2)`
-- against `(a 2, a 1, a 0)`.
example [Finite α] {κ : Type*} [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K]
    (hrev : K.IsReversible μ) (f : α → κ) (hf : Measurable f) (a : Fin 3 → κ) :
    (chainLaw μ K).map (fun x (i : Fin 3) => f (x i)) {a} =
      (chainLaw μ K).map (fun x (i : Fin 3) => f (x i)) {![a 2, a 1, a 0]} := by
  rw [chainLaw_coarseN_reverse μ K hrev f hf 2 a]
  congr 2
  funext i; fin_cases i <;> rfl

/-- `Statement:` on a finite carrier with measurable singletons, if the Markov kernel `K` is reversible
w.r.t. the initial probability law `μ`, then for every `n` the law of `(x 0, …, x n)` equals the law of
`(x n, …, x 0)`. -/
theorem chainLaw_finPath_map_rev [Finite α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hrev : K.IsReversible μ) (n : ℕ) :
    (chainLaw μ K).map (finPath n) =
      (chainLaw μ K).map (fun x (i : Fin (n + 1)) => x (Fin.rev i)) := by
  have hr : Measurable (fun y : Fin (n + 1) → α => y ∘ Fin.rev) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hc : (fun (x : ℕ → α) (i : Fin (n + 1)) => x (Fin.rev i)) =
      (fun y : Fin (n + 1) → α => y ∘ Fin.rev) ∘ finPath n := rfl
  rw [hc, ← Measure.map_map hr (measurable_finPath n)]
  refine Measure.ext_iff_singleton.2 fun y => ?_
  have hpre : (fun y : Fin (n + 1) → α => y ∘ Fin.rev) ⁻¹' {y} = {y ∘ Fin.rev} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl; funext i; simp
    · rintro rfl; funext i; simp
  rw [Measure.map_apply hr (measurableSet_singleton _), hpre, chainLaw_finPath_singleton,
    chainLaw_finPath_singleton]
  exact pathWeight_rev (detailedBalance_of_isReversible μ K hrev) y

/-- `Statement:` on a finite carrier with measurable singletons, if the Markov kernel `K` is reversible
w.r.t. the initial probability law `μ`, then for every measurable observer `f` and every `n` the law of
`(f (x 0), …, f (x n))` equals the law of `(f (x n), …, f (x 0))`, as measures. -/
theorem chainLaw_coarseN_map_reverse [Finite α] {κ : Type*} [MeasurableSpace κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K]
    (hrev : K.IsReversible μ) (f : α → κ) (hf : Measurable f) (n : ℕ) :
    (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x i)) =
      (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x (Fin.rev i))) := by
  have hg : Measurable (fun y : Fin (n + 1) → α => f ∘ y) :=
    measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)
  have hr : Measurable (fun (x : ℕ → α) (i : Fin (n + 1)) => x (Fin.rev i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have h1 : (fun (x : ℕ → α) (i : Fin (n + 1)) => f (x (Fin.rev i))) =
      (fun y : Fin (n + 1) → α => f ∘ y) ∘ (fun x i => x (Fin.rev i)) := rfl
  have h2 : (fun (x : ℕ → α) (i : Fin (n + 1)) => f (x i)) =
      (fun y : Fin (n + 1) → α => f ∘ y) ∘ finPath n := rfl
  rw [h1, h2, ← Measure.map_map hg hr, ← Measure.map_map hg (measurable_finPath n),
    chainLaw_finPath_map_rev μ K hrev n]

/-- `Statement:` for a measure `ν` on `Fin (n + 2) → α`, `α` finite with measurable singletons, the
image of `ν` under `Fin.tail` puts mass `∑ a, ν {Fin.cons a y}` on `{y}`. -/
theorem map_tail_singleton [Fintype α] {n : ℕ} (ν : Measure (Fin (n + 2) → α))
    (y : Fin (n + 1) → α) :
    ν.map (fun z : Fin (n + 2) → α => Fin.tail z) {y} = ∑ a : α, ν {Fin.cons a y} := by
  classical
  have ht : Measurable (fun z : Fin (n + 2) → α => Fin.tail z) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  rw [Measure.map_apply ht (measurableSet_singleton _)]
  have hpre : (fun z : Fin (n + 2) → α => Fin.tail z) ⁻¹' {y} =
      ↑(Finset.univ.image (fun a : α => (Fin.cons a y : Fin (n + 2) → α))) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.coe_image, Finset.coe_univ,
      Set.image_univ, Set.mem_range]
    constructor
    · rintro rfl; exact ⟨z 0, Fin.cons_self_tail z⟩
    · rintro ⟨a, rfl⟩; exact Fin.tail_cons (α := fun _ => α) a y
  rw [hpre, ← sum_measure_singleton, Finset.sum_image]
  intro a _ b _ h
  exact Fin.cons_left_injective (α := fun _ => α) y h

/-- `Statement:` on a finite carrier with measurable singletons, if the Markov kernel `K` leaves the
initial probability law `μ` invariant (Mathlib `Kernel.Invariant`), then for every start `t` and every
`n` the window `(x t, …, x (t + n))` puts mass `pathWeight (measureVec μ) (kernelMat K) y` on `{y}`. -/
theorem chainLaw_window_singleton [Finite α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hinv : K.Invariant μ) :
    ∀ (t n : ℕ) (y : Fin (n + 1) → α),
      (chainLaw μ K).map (fun x (i : Fin (n + 1)) => x (t + i)) {y} =
        pathWeight (measureVec μ) (kernelMat K) y := by
  have := Fintype.ofFinite α
  have hstat : ∀ b : α, ∑ a, measureVec μ a * kernelMat K a b = measureVec μ b := by
    intro b
    have : (μ.bind K) {b} = μ {b} := by rw [hinv.def]
    rw [Measure.bind_apply (measurableSet_singleton b) (Kernel.aemeasurable _),
      lintegral_fintype] at this
    simpa [measureVec, kernelMat, mul_comm] using this
  intro t
  induction t with
  | zero =>
    intro n y
    have : (fun (x : ℕ → α) (i : Fin (n + 1)) => x (0 + i)) = finPath n := by
      funext x i; simp [finPath]
    rw [this, chainLaw_finPath_singleton]
  | succ t ih =>
    intro n y
    have hw : Measurable (fun (x : ℕ → α) (i : Fin (n + 2)) => x (t + i)) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply _
    have ht : Measurable (fun z : Fin (n + 2) → α => Fin.tail z) :=
      measurable_pi_iff.mpr fun i => measurable_pi_apply _
    have hc : (fun (x : ℕ → α) (i : Fin (n + 1)) => x (t + 1 + i)) =
        (fun z : Fin (n + 2) → α => Fin.tail z) ∘ (fun x (i : Fin (n + 2)) => x (t + i)) := by
      funext x i
      simp only [Function.comp_apply, Fin.tail, Fin.val_succ]
      congr 1; omega
    rw [hc, ← Measure.map_map ht hw, map_tail_singleton]
    simp_rw [ih (n + 1)]
    unfold pathWeight
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.castSucc_zero, ← Fin.succ_castSucc,
      Fin.cons_succ]
    rw [← hstat (y 0), Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-- `Statement:` on a finite carrier with measurable singletons, if the Markov kernel `K` leaves the
initial probability law `μ` invariant, then for every start `t` and every `n` the window
`(x t, …, x (t + n))` has the law of `(x 0, …, x n)`. -/
theorem chainLaw_window_eq_finPath [Finite α] (μ : Measure α) [IsProbabilityMeasure μ]
    (K : Kernel α α) [IsMarkovKernel K] (hinv : K.Invariant μ) (t n : ℕ) :
    (chainLaw μ K).map (fun x (i : Fin (n + 1)) => x (t + i)) =
      (chainLaw μ K).map (finPath n) := by
  refine Measure.ext_iff_singleton.2 fun y => ?_
  rw [chainLaw_window_singleton μ K hinv, chainLaw_finPath_singleton]

/-- `Statement:` on a finite carrier with measurable singletons, if the Markov kernel `K` is reversible
w.r.t. the initial probability law `μ`, then for every measurable observer `f`, every start `t` and every
`n` the law of `(f (x t), …, f (x (t + n)))` equals the law of `(f (x (t + n)), …, f (x t))`, as
measures. -/
theorem chainLaw_window_map_reverse [Finite α] {κ : Type*} [MeasurableSpace κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K]
    (hrev : K.IsReversible μ) (f : α → κ) (hf : Measurable f) (t n : ℕ) :
    (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x (t + i))) =
      (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x (t + Fin.rev i))) := by
  have hw : Measurable (fun (x : ℕ → α) (i : Fin (n + 1)) => x (t + i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hg : Measurable (fun y : Fin (n + 1) → α => f ∘ y) :=
    measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)
  have hg' : Measurable (fun y : Fin (n + 1) → α => f ∘ y ∘ Fin.rev) :=
    measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply _)
  have h1 : (fun (x : ℕ → α) (i : Fin (n + 1)) => f (x (t + i))) =
      (fun y : Fin (n + 1) → α => f ∘ y) ∘ (fun x i => x (t + i)) := rfl
  have h2 : (fun (x : ℕ → α) (i : Fin (n + 1)) => f (x (t + Fin.rev i))) =
      (fun y : Fin (n + 1) → α => f ∘ y ∘ Fin.rev) ∘ (fun x i => x (t + i)) := rfl
  rw [h1, h2, ← Measure.map_map hg hw, ← Measure.map_map hg' hw,
    chainLaw_window_eq_finPath μ K hrev.invariant t n,
    Measure.map_map hg (measurable_finPath n), Measure.map_map hg' (measurable_finPath n)]
  exact chainLaw_coarseN_map_reverse μ K hrev f hf n

/-- `Statement:` CONTROL for `chainLaw_window_map_reverse` without reversibility: for the deterministic
kernel of `rot4` from any probability law `μ` with `μ {0} ≠ 0`, along the identity observer, the law of
`(x 0, x 1)` puts different masses on `(0, 1)` and `(1, 0)`. -/
theorem rot4_chainLaw_not_reversal_symmetric (μ : Measure (Fin 4)) [IsProbabilityMeasure μ]
    (h0 : μ {0} ≠ 0) :
    (chainLaw μ (Kernel.deterministic rot4 (measurable_of_finite _))).map
        (fun x (i : Fin 2) => x i) {![0, 1]} ≠
      (chainLaw μ (Kernel.deterministic rot4 (measurable_of_finite _))).map
        (fun x (i : Fin 2) => x i) {![1, 0]} := by
  have h := chainLaw_finPath_singleton μ (Kernel.deterministic rot4 (measurable_of_finite _)) 1
  change (chainLaw μ _).map (finPath 1) {![0, 1]} ≠ (chainLaw μ _).map (finPath 1) {![1, 0]}
  rw [h, h]
  have h01 : rot4 0 = 1 := by decide
  have h10 : rot4 1 = 2 := by decide
  simp [pathWeight, measureVec, kernelMat, Kernel.deterministic_apply, h01, h10, h0]

end MeasureN

/-- `Statement:` the swap of `Bool` is reversible w.r.t. the probability measure
`(1/2) • (dirac true + dirac false)`. -/
theorem boolSwap_reversible_half :
    (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)).IsReversible
      ((2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)) := by
  refine isReversible_deterministic_involutive _ Bool.not_not ?_
  rw [Measure.map_smul, Measure.map_add _ _ (measurable_of_finite _),
    Measure.map_dirac' (measurable_of_finite _), Measure.map_dirac' (measurable_of_finite _)]
  all_goals first | exact (measurable_of_finite _).aemeasurable | simp [add_comm]

/-- `Statement:` `(1/2) • (dirac true + dirac false)` is a probability measure on `Bool`. -/
instance isProbabilityMeasure_halfBool :
    IsProbabilityMeasure ((2⁻¹ : ENNReal) • (Measure.dirac true + Measure.dirac false)) := by
  constructor
  rw [Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, one_add_one_eq_two,
    smul_eq_mul, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

-- Statement: the measure in `a4_direction_erased` and `boolSwap_reversible`, `dirac true + dirac false`,
-- has total mass 2, so it is not a probability measure.
example : (Measure.dirac true + Measure.dirac false : Measure Bool) Set.univ = 2 := by
  simp [one_add_one_eq_two]

section Trade
universe u v

/-- `Statement:` both directions. First: the deterministic kernel of `rot4` is reversible w.r.t. no
probability measure, lumps along `parity4` to the swap of `Bool`, and the swap is reversible w.r.t. some
probability measure. Second: on a finite carrier with measurable singletons, for every initial
probability law `μ`, Markov kernel `K` with `K.IsReversible μ`, measurable observer `f`, start `t` and
`n`, the law of `(f (x t), …, f (x (t + n)))` equals the law of `(f (x (t + n)), …, f (x t))`.
`Reading:` coarse-graining can erase an arrow, and from a reversible start it creates none in any window
of consecutive times. -/
theorem coarse_graining_trade :
    ((∀ π : Measure (Fin 4), IsProbabilityMeasure π →
        ¬ (Kernel.deterministic rot4 (measurable_of_finite _)).IsReversible π) ∧
      Lumps (Kernel.deterministic rot4 (measurable_of_finite _))
        (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)) parity4 ∧
      ∃ ν : Measure Bool, IsProbabilityMeasure ν ∧
        (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)).IsReversible ν) ∧
    (∀ (α : Type u) [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
      (κ : Type v) [MeasurableSpace κ]
      (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α) [IsMarkovKernel K],
      K.IsReversible μ → ∀ f : α → κ, Measurable f → ∀ (t n : ℕ),
        (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x (t + i))) =
          (chainLaw μ K).map (fun x (i : Fin (n + 1)) => f (x (t + Fin.rev i)))) :=
  ⟨⟨a4_direction_erased.1, a4_direction_erased.2.1,
      ⟨_, isProbabilityMeasure_halfBool, boolSwap_reversible_half⟩⟩,
    fun _ _ _ _ _ _ μ _ K _ hrev f hf t n => chainLaw_window_map_reverse μ K hrev f hf t n⟩

end Trade

end Lumping

/-! ### § XIII. `N2` in ℝ: span minus material, the gap count, and the amount -/

section GapCount

open Set Metric
open scoped ENNReal

/-- `Statement:` `N2` read in ℝ, the image of `N2` under `ℝ≥0 → ℝ`. -/
def n2Real : Set ℝ := ((↑) : NNReal → ℝ) '' N2

/-- `Statement:` `n2Real = {0} ∪ {(1/2)^n | n : ℕ}`. -/
theorem n2Real_eq : n2Real = insert 0 (range fun n : ℕ => (1 / 2 : ℝ) ^ n) := by
  ext r
  constructor
  · rintro ⟨q, hq | ⟨n, rfl⟩, rfl⟩
    · exact Or.inl (by simp [hq])
    · exact Or.inr ⟨n, by push_cast; rw [one_div]⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, Or.inl rfl, by simp⟩
    · exact ⟨(2⁻¹ : NNReal) ^ n, Or.inr ⟨n, rfl⟩, by push_cast; rw [one_div]⟩

/-- `Statement:` `(1/2)^k = 2^(-k)` in ℝ. -/
theorem n2_half_pow_eq_zpow (k : ℕ) : (1 / 2 : ℝ) ^ k = (2 : ℝ) ^ (-(k : ℤ)) := by
  rw [zpow_neg, zpow_natCast, one_div, inv_pow]

/-- `Statement:` `(1/2)^n → 0`. -/
theorem n2_half_pow_tendsto : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- `Statement:` `n2Real` is closed in ℝ. -/
theorem isClosed_n2Real : IsClosed n2Real := by
  rw [n2Real_eq]; exact n2_half_pow_tendsto.isCompact_insert_range.isClosed

/-- `Statement:` `n2Real` has Lebesgue measure 0 (countable). -/
theorem volume_n2Real : volume n2Real = 0 := by
  rw [n2Real_eq]; exact ((Set.countable_range _).insert 0).measure_zero _

/-- `Statement:` `n2Real ⊆ [0, 1]`. -/
theorem n2Real_subset_Icc : n2Real ⊆ Icc 0 1 := by
  rw [n2Real_eq]
  rintro r (rfl | ⟨n, rfl⟩)
  · exact ⟨le_refl _, zero_le_one⟩
  · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- `Statement:` `n2Real` has diameter 1. -/
theorem ediam_n2Real : ediam n2Real = 1 := by
  apply le_antisymm
  · calc ediam n2Real ≤ ediam (Icc (0 : ℝ) 1) := ediam_mono n2Real_subset_Icc
      _ = 1 := by simp
  · have h0 : (0 : ℝ) ∈ n2Real := by rw [n2Real_eq]; exact Or.inl rfl
    have h1 : (1 : ℝ) ∈ n2Real := by rw [n2Real_eq]; exact Or.inr ⟨0, by simp⟩
    have h := edist_le_ediam_of_mem h0 h1
    rw [edist_dist, Real.dist_eq] at h
    norm_num at h
    exact h

/-- `Statement:` `spanGap n2Real = 1` (`spanGap`, `ZeroParadox/Reals/ConnectedNoFirstStep.lean`):
    material 0, span 1; so `n2Real`, closed, is not an interval (`spanGap_eq_zero_iff_interval`). -/
theorem spanGap_n2Real : spanGap n2Real = 1 := by
  rw [spanGap, volume_n2Real, ediam_n2Real, tsub_zero]

/-- `Statement:` the `n`-th gap of `n2Real`, the open interval `((1/2)^(n+1), (1/2)^n)`. -/
def n2GapInt (n : ℕ) : Set ℝ := Ioo ((1 / 2 : ℝ) ^ (n + 1)) ((1 / 2 : ℝ) ^ n)

/-- `Statement:` `[0, 1] \ n2Real` is the union of the gaps `n2GapInt n`. -/
theorem Icc_diff_n2Real : Icc (0 : ℝ) 1 \ n2Real = ⋃ n, n2GapInt n := by
  rw [n2Real_eq]
  ext x
  simp only [Set.mem_sdiff, mem_Icc, mem_iUnion, n2GapInt, mem_Ioo, mem_insert_iff, mem_range,
    not_or, not_exists]
  constructor
  · rintro ⟨⟨h0, h1⟩, hx0, hxn⟩
    have hpos : 0 < x := lt_of_le_of_ne h0 (Ne.symm hx0)
    have hex : ∃ n, (1 / 2 : ℝ) ^ n < x := exists_pow_lt_of_lt_one hpos (by norm_num)
    classical
    let n := Nat.find hex
    have hn : (1 / 2 : ℝ) ^ n < x := Nat.find_spec hex
    have hn0 : n ≠ 0 := by
      intro h; rw [h, pow_zero] at hn; linarith
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hmin : ¬ (1 / 2 : ℝ) ^ m < x := Nat.find_min hex (by omega)
    have hm1 : m + 1 = n := by omega
    refine ⟨m, by rw [hm1]; exact hn, ?_⟩
    exact lt_of_le_of_ne (not_lt.1 hmin) (fun h => hxn m h.symm)
  · rintro ⟨n, h1, h2⟩
    have hpos : 0 < x := lt_trans (by positivity) h1
    refine ⟨⟨hpos.le, h2.le.trans (pow_le_one₀ (by norm_num) (by norm_num))⟩, hpos.ne', ?_⟩
    intro m hm
    rw [← hm] at h1 h2
    have a := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)).1 h1
    have b := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num)).1 h2
    omega

/-- `Statement:` the `n`-th gap has length `(1/2)^(n+1)`. -/
theorem volume_n2GapInt (n : ℕ) :
    volume (n2GapInt n) = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
  rw [n2GapInt, Real.volume_Ioo]; congr 1; ring

/-- `Statement:` the gaps are pairwise disjoint. -/
theorem n2GapInt_pairwise_disjoint : Pairwise (Function.onFun Disjoint n2GapInt) := by
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨a1, _⟩ ⟨_, b2⟩
    have : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ (m + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  · rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨_, a2⟩ ⟨b1, _⟩
    have : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (n + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith

/-- `Statement:` the gaps' lengths sum to `spanGap n2Real`. -/
theorem tsum_volume_n2GapInt : ∑' n, volume (n2GapInt n) = spanGap n2Real := by
  rw [spanGap_n2Real]
  simp_rw [volume_n2GapInt]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)]
  · have h : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
      simp_rw [pow_succ]; rw [tsum_mul_right, tsum_geometric_two]; norm_num
    rw [h, ENNReal.ofReal_one]
  · exact (summable_geometric_two.mul_right (1 / 2)).congr fun n => by rw [pow_succ]

/-- `Statement:` the measure of the union of the gaps is `spanGap n2Real`. -/
theorem volume_iUnion_n2GapInt : volume (⋃ n, n2GapInt n) = spanGap n2Real := by
  rw [measure_iUnion n2GapInt_pairwise_disjoint (fun n => measurableSet_Ioo),
    tsum_volume_n2GapInt]

/-- `Statement:` for `r > 0`, only finitely many gaps reach `r` or above. -/
theorem n2Gaps_above_finite {r : ℝ} (hr : 0 < r) : {n | ∃ y ∈ n2GapInt n, r ≤ y}.Finite := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 (n2_half_pow_tendsto.eventually (gt_mem_nhds hr))
  refine (Set.finite_Iio M).subset ?_
  rintro n ⟨y, ⟨_, hy⟩, hry⟩
  by_contra hn
  have := hM n (not_lt.1 hn)
  linarith

/-- `Statement:` at every `x : ℚ_[2]`, 0 of `ℚ_[2]` included (both sides ⊤ of `ℕ∞`), `cxQ2 x` is the
    number of gaps of `n2Real` of length at least `‖x‖`.
    `Reading:` on a line, discreteness read as span minus material holds (`spanGap_eq_zero_iff_interval`);
    complexity at 0 of `ℚ_[2]` counts the gaps, and the amount missing is a separate quantity
    (`spanGap_scaled_n2Real`), tied to the count by a logarithm only on a fixed-ratio ladder
    (`ladder_count_eq_log`, the control `harm_no_log_law`). -/
theorem cxQ2_eq_gap_count (x : ℚ_[2]) :
    cxQ2 x = {n : ℕ | ‖x‖ ≤ (1 / 2 : ℝ) ^ (n + 1)}.encard := by
  by_cases h0 : x = 0
  · subst h0
    rw [cxQ2_zero]
    have : {n : ℕ | ‖(0 : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ (n + 1)} = univ := by
      ext n; simp only [norm_zero, mem_ofPred_eq, mem_univ, iff_true]; positivity
    rw [this, encard_univ, ENat.card_eq_top_of_infinite]
  · have hset : {n : ℕ | ‖x‖ ≤ (1 / 2 : ℝ) ^ (n + 1)}
        = ((Finset.range x.valuation.toNat : Finset ℕ) : Set ℕ) := by
      ext n
      simp only [mem_ofPred_eq, Finset.coe_range, mem_Iio]
      rw [Padic.norm_eq_zpow_neg_valuation h0, n2_half_pow_eq_zpow]
      push_cast
      rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
      omega
    rw [hset, encard_coe_eq_coe_finsetCard, Finset.card_range]
    simp [cxQ2, h0]

/-- `Statement:` CONTROL, the norm image of `[-1, 1]` in ℝ is `[0, 1]`, and its `spanGap` is 0. -/
theorem real_spanGap_zero : spanGap ((fun x : ℝ => |x|) '' Icc (-1) 1) = 0 := by
  have h : (fun x : ℝ => |x|) '' Icc (-1) 1 = Icc 0 1 := by
    ext r
    constructor
    · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
      exact ⟨abs_nonneg x, abs_le.2 ⟨h1, h2⟩⟩
    · rintro ⟨h0, h1⟩
      exact ⟨r, ⟨by linarith, h1⟩, abs_of_nonneg h0⟩
  rw [h]; exact spanGap_Icc

/-- `Statement:` CONTROL, `spanGap` is not the count: for `t > 0`, `t • n2Real` keeps infinitely many
    gaps at 0 and has `spanGap = t`. -/
theorem spanGap_scaled_n2Real {t : ℝ} (ht : 0 < t) :
    spanGap ((fun y => t * y) '' n2Real) = ENNReal.ofReal t := by
  have hv : volume ((fun y => t * y) '' n2Real) = 0 := by
    rw [n2Real_eq]; exact (((Set.countable_range _).insert 0).image _).measure_zero _
  rw [spanGap, hv, tsub_zero]
  have h0 : (0 : ℝ) ∈ n2Real := by rw [n2Real_eq]; exact Or.inl rfl
  have h1 : (1 : ℝ) ∈ n2Real := by rw [n2Real_eq]; exact Or.inr ⟨0, by simp⟩
  apply le_antisymm
  · calc ediam ((fun y => t * y) '' n2Real) ≤ ediam (Icc (0 : ℝ) t) := by
          apply ediam_mono
          rintro _ ⟨y, hy, rfl⟩
          obtain ⟨hy0, hy1⟩ := n2Real_subset_Icc hy
          exact ⟨by positivity, by nlinarith⟩
      _ = ENNReal.ofReal t := by simp
  · have h := edist_le_ediam_of_mem (s := (fun y => t * y) '' n2Real)
      (⟨0, h0, by simp⟩ : (0 : ℝ) ∈ (fun y => t * y) '' n2Real)
      (⟨1, h1, by simp⟩ : t ∈ (fun y => t * y) '' n2Real)
    rw [edist_dist, Real.dist_eq] at h
    simpa [abs_of_pos ht] using h

/-- `Statement:` the closed ball of radius `2^(-n)` about 0 of ℤ_[2] has diameter `2^(-n)`. -/
theorem ediam_ball_Z2 (n : ℕ) :
    ediam {x : ℤ_[2] | ‖x‖ ≤ (2 : ℝ) ^ (-(n : ℤ))} = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  have key : ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℤ))) = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
    rw [zpow_neg, zpow_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  rw [← key]
  apply le_antisymm
  · apply ediam_le_of_forall_dist_le
    intro x hx y hy
    rw [dist_eq_norm, sub_eq_add_neg]
    exact (PadicInt.nonarchimedean x (-y)).trans (by rw [norm_neg]; exact max_le hx hy)
  · have hmem0 : (0 : ℤ_[2]) ∈ {x : ℤ_[2] | ‖x‖ ≤ (2 : ℝ) ^ (-(n : ℤ))} := by
      simp only [mem_ofPred_eq, norm_zero]; positivity
    have hmem : ((2 : ℤ_[2]) ^ n) ∈ {x : ℤ_[2] | ‖x‖ ≤ (2 : ℝ) ^ (-(n : ℤ))} := by
      simp only [mem_ofPred_eq, norm_pow]
      have := PadicInt.norm_p (p := 2); push_cast at this; rw [this]
      rw [zpow_neg, zpow_natCast, inv_pow]
    have h := edist_le_ediam_of_mem hmem hmem0
    rw [edist_dist, dist_eq_norm, sub_zero, norm_pow] at h
    have := PadicInt.norm_p (p := 2); push_cast at this; rw [this] at h
    refine le_trans (le_of_eq ?_) h
    congr 1; rw [zpow_neg, zpow_natCast, inv_pow]

/-- `Statement:` CONTROL, in ℤ_[2] under `haarZp` each closed ball about 0 has material (Haar
    measure, `haarZp_ball`) equal to span (diameter): the gap lives on `n2Real`, not in ℤ_[2]. -/
theorem haar_eq_ediam_ball_Z2 (n : ℕ) :
    haarZp (p := 2) {x : ℤ_[2] | ‖x‖ ≤ (2 : ℝ) ^ (-(n : ℤ))}
      = ediam {x : ℤ_[2] | ‖x‖ ≤ (2 : ℝ) ^ (-(n : ℤ))} := by
  rw [ediam_ball_Z2]
  have := haarZp_ball (p := 2) n
  push_cast at this
  exact this

/-! #### § XIII, count against amount on a gap-length sequence -/

/-- `Statement:` the total length of the gaps from index `k` on. -/
noncomputable def gapRemaining (ℓ : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j, ℓ (j + k)

/-- `Statement:` the number of gaps of length at least `r`. -/
noncomputable def gapCount (ℓ : ℕ → ℝ) (r : ℝ) : ℕ∞ := {n : ℕ | r ≤ ℓ n}.encard

/-- `Statement:` the fixed-ratio ladder: gap `n` has length `t · (1/2)^(n+1)` (`n2Real` at `t = 1`). -/
noncomputable def gapLadder (t : ℝ) (n : ℕ) : ℝ := t * (1 / 2 : ℝ) ^ (n + 1)

/-- `Statement:` on the ladder, `gapRemaining k = t · (1/2)^k`. -/
theorem gapRemaining_ladder (t : ℝ) (k : ℕ) :
    gapRemaining (gapLadder t) k = t * (1 / 2 : ℝ) ^ k := by
  unfold gapRemaining gapLadder
  have h : ∀ j : ℕ, t * (1 / 2 : ℝ) ^ (j + k + 1)
      = (t * (1 / 2 : ℝ) ^ (k + 1)) * (1 / 2 : ℝ) ^ j := by
    intro j; rw [show j + k + 1 = j + (k + 1) by ring, pow_add]; ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_two, pow_succ]; ring

/-- `Statement:` for `t > 0`, the ladder has exactly `k` gaps of length at least `t · (1/2)^k`. -/
theorem gapCount_ladder {t : ℝ} (ht : 0 < t) (k : ℕ) :
    gapCount (gapLadder t) (t * (1 / 2 : ℝ) ^ k) = k := by
  unfold gapCount gapLadder
  have hset : {n : ℕ | t * (1 / 2 : ℝ) ^ k ≤ t * (1 / 2 : ℝ) ^ (n + 1)}
      = ((Finset.range k : Finset ℕ) : Set ℕ) := by
    ext n
    simp only [mem_ofPred_eq, Finset.coe_range, mem_Iio]
    rw [mul_le_mul_iff_of_pos_left ht,
      pow_le_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)]
    omega
  rw [hset, encard_coe_eq_coe_finsetCard, Finset.card_range]

/-- `Statement:` for `t > 0`, the count at the remaining amount after `k` gaps is `k`. -/
theorem gapCount_remaining_ladder {t : ℝ} (ht : 0 < t) (k : ℕ) :
    gapCount (gapLadder t) (gapRemaining (gapLadder t) k) = k := by
  rw [gapRemaining_ladder, gapCount_ladder ht]

/-- `Statement:` for `t > 0`, `log₂ (1 / gapRemaining k) = k - log₂ t` on the ladder. -/
theorem logb_inv_gapRemaining_ladder {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Real.logb 2 (1 / gapRemaining (gapLadder t) k) = k - Real.logb 2 t := by
  rw [gapRemaining_ladder]
  have : 1 / (t * (1 / 2 : ℝ) ^ k) = t⁻¹ * (2 : ℝ) ^ k := by
    rw [one_div_pow]; field_simp
  rw [this, Real.logb_mul (inv_ne_zero ht.ne') (by positivity), Real.logb_inv, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  ring

/-- `Statement:` on the ladder scaled by `t > 0`, at every level `k`,
    count = `log₂ (1 / remaining) + log₂ t`. One way: a fixed ratio gives the log law; the converse
    is not claimed. -/
theorem ladder_count_eq_log {t : ℝ} (ht : 0 < t) (k : ℕ) :
    ((gapCount (gapLadder t) (gapRemaining (gapLadder t) k)).toNat : ℝ)
      = Real.logb 2 (1 / gapRemaining (gapLadder t) k) + Real.logb 2 t := by
  rw [gapCount_remaining_ladder ht, logb_inv_gapRemaining_ladder ht]
  simp

/-- `Statement:` for `t > 0`, the count against a threshold scaled by `t` is unchanged. -/
theorem gapCount_ladder_scale {t : ℝ} (ht : 0 < t) (r : ℝ) :
    gapCount (gapLadder t) (t * r) = gapCount (gapLadder 1) r := by
  unfold gapCount gapLadder
  congr 1; ext n
  simp only [mem_ofPred_eq, one_mul]
  exact mul_le_mul_iff_of_pos_left ht

/-- `Statement:` `cxQ2 x` is the ladder count at threshold `‖x‖`, at every `x : ℚ_[2]`. -/
theorem cxQ2_eq_gapCount (x : ℚ_[2]) : cxQ2 x = gapCount (gapLadder 1) ‖x‖ := by
  rw [cxQ2_eq_gap_count]; unfold gapCount gapLadder; simp only [one_mul]

/-- `Statement:` at `x = 2^k` in `ℚ_[2]`: `‖x‖` is the remaining amount after `k` gaps,
    `cxQ2 x = k`, and `cxQ2 x = log₂ (1 / remaining)`. -/
theorem cxQ2_two_pow_eq_log (k : ℕ) :
    ‖(2 : ℚ_[2]) ^ k‖ = gapRemaining (gapLadder 1) k ∧
    cxQ2 ((2 : ℚ_[2]) ^ k) = k ∧
    ((cxQ2 ((2 : ℚ_[2]) ^ k)).toNat : ℝ) = Real.logb 2 (1 / gapRemaining (gapLadder 1) k) := by
  have hn : ‖(2 : ℚ_[2]) ^ k‖ = gapRemaining (gapLadder 1) k := by
    rw [norm_pow]
    have := Padic.norm_p (p := 2); push_cast at this
    rw [this, gapRemaining_ladder, one_mul, one_div]
  have hc : cxQ2 ((2 : ℚ_[2]) ^ k) = k := by
    rw [cxQ2_eq_gapCount, hn, gapCount_remaining_ladder one_pos]
  refine ⟨hn, hc, ?_⟩
  rw [hc, logb_inv_gapRemaining_ladder one_pos, Real.logb_one]; simp

/-- `Statement:` `n2Real` has Hausdorff dimension 0 (countable; Mathlib's `dimH_countable`). -/
theorem dimH_n2Real : dimH n2Real = 0 := by
  rw [n2Real_eq]; exact dimH_countable ((Set.countable_range _).insert 0)

/-- `Statement:` CONTROL, the chain `{0} ∪ {1/(n+1)}`: gap `n` has length `1/((n+1)(n+2))`. -/
noncomputable def harmGaps (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

/-- `Statement:` on `harmGaps`, the remaining amount after `k` gaps is `1/(k+1)`. -/
theorem gapRemaining_harm (k : ℕ) : gapRemaining harmGaps k = 1 / ((k : ℝ) + 1) := by
  set f : ℕ → ℝ := fun j => 1 / ((j : ℝ) + k + 1) with hf
  have hterm : ∀ j, harmGaps (j + k) = f j - f (j + 1) := by
    intro j; simp only [harmGaps, hf]; push_cast
    field_simp; ring
  have hlim : Tendsto f atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat k)
    refine h.congr fun j => ?_
    simp only [Function.comp, hf]; push_cast; ring_nf
  have hsum : HasSum (fun j => harmGaps (j + k)) (f 0) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun j => by simp only [harmGaps]; positivity)]
    have : (fun n => ∑ i ∈ Finset.range n, harmGaps (i + k)) = fun n => f 0 - f n := by
      funext n; simp_rw [hterm]; exact Finset.sum_range_sub' f n
    rw [this]
    simpa using (tendsto_const_nhds (x := f 0)).sub hlim
  unfold gapRemaining
  rw [hsum.tsum_eq]; simp [hf]

/-- `Statement:` on `harmGaps`, no gap reaches the remaining amount at level 0. -/
theorem gapCount_harm_zero : gapCount harmGaps (gapRemaining harmGaps 0) = 0 := by
  rw [gapRemaining_harm]; unfold gapCount
  have : {n : ℕ | 1 / (((0 : ℕ) : ℝ) + 1) ≤ harmGaps n} = ∅ := by
    ext n
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le, harmGaps]
    push_cast
    rw [div_lt_div_iff_of_pos_left one_pos (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  rw [this, encard_empty]

/-- `Statement:` on `harmGaps`, exactly one gap reaches the remaining amount at level 2. -/
theorem gapCount_harm_two : gapCount harmGaps (gapRemaining harmGaps 2) = 1 := by
  rw [gapRemaining_harm]; unfold gapCount
  have : {n : ℕ | 1 / (((2 : ℕ) : ℝ) + 1) ≤ harmGaps n} = {0} := by
    ext n
    simp only [mem_ofPred_eq, mem_singleton_iff, harmGaps]
    push_cast
    rw [one_div_le_one_div (by norm_num) (by positivity)]
    constructor
    · intro h
      by_contra hn
      have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn)
      nlinarith
    · rintro rfl; norm_num
  rw [this, encard_singleton]

/-- `Statement:` CONTROL, on `harmGaps` no constant `c` gives
    count = `log₂ (1 / remaining) + c` at every level (levels 0 and 2 disagree). -/
theorem harm_no_log_law :
    ¬ ∃ c : ℝ, ∀ k : ℕ, ((gapCount harmGaps (gapRemaining harmGaps k)).toNat : ℝ)
        = Real.logb 2 (1 / gapRemaining harmGaps k) + c := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h2 := hc 2
  rw [gapCount_harm_zero, gapRemaining_harm] at h0
  rw [gapCount_harm_two, gapRemaining_harm] at h2
  norm_num at h0 h2
  have hc0 : c = 0 := by linarith
  rw [hc0, add_zero] at h2
  have hlt : Real.logb 2 2 < Real.logb 2 3 :=
    Real.logb_lt_logb (by norm_num) (by norm_num) (by norm_num)
  rw [Real.logb_self_eq_one (by norm_num)] at hlt
  linarith

end GapCount

/-! ### § XIV. Zooming out on the 2-adic tower: a coarse-graining observer

The observer `zoom n : ZMod (2^(n+1)) →+* ZMod (2^n)` forgets the top binary digit, and the residue
maps `PadicInt.toZModPow n` read ℤ_[2] at every level. Lumping along a group homomorphism is the
strong lumpability of § XII (Kemeny-Snell and Dynkin, cited there). The uniform law is Mathlib's
`ProbabilityTheory.uniformOn Set.univ`. -/

section ZoomTower

open scoped ENNReal

section Generic

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  [MeasurableSpace G] [DiscreteMeasurableSpace G] [MeasurableSpace H] [DiscreteMeasurableSpace H]

/-- `Statement:` the symmetric walk: step to `x + s` or `x - s`, each with mass 1/2. -/
noncomputable def symWalk (s : G) : Kernel G G where
  toFun x := (2⁻¹ : ℝ≥0∞) • Measure.dirac (x + s) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (x - s)
  measurable' := Measurable.of_discrete

/-- `Statement:` `symWalk s x` unfolds to its two Dirac masses, by `rfl`. -/
theorem symWalk_apply (s x : G) : symWalk s x =
    (2⁻¹ : ℝ≥0∞) • Measure.dirac (x + s) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (x - s) := rfl

/-- `Statement:` `symWalk s` is a Markov kernel. -/
instance isMarkovKernel_symWalk (s : G) : IsMarkovKernel (symWalk s) :=
  ⟨fun x => ⟨by simp [symWalk_apply, ENNReal.inv_two_add_inv_two]⟩⟩

/-- `Statement:` a fair random bit at offset `t`: stay at `x` or move to `x + t`, each with mass 1/2. -/
noncomputable def topBit (t : G) : Kernel G G where
  toFun x := (2⁻¹ : ℝ≥0∞) • Measure.dirac x + (2⁻¹ : ℝ≥0∞) • Measure.dirac (x + t)
  measurable' := Measurable.of_discrete

/-- `Statement:` `topBit t x` unfolds to its two Dirac masses, by `rfl`. -/
theorem topBit_apply (t x : G) : topBit t x =
    (2⁻¹ : ℝ≥0∞) • Measure.dirac x + (2⁻¹ : ℝ≥0∞) • Measure.dirac (x + t) := rfl

/-- `Statement:` `topBit t` is a Markov kernel. -/
instance isMarkovKernel_topBit (t : G) : IsMarkovKernel (topBit t) :=
  ⟨fun x => ⟨by simp [topBit_apply, ENNReal.inv_two_add_inv_two]⟩⟩

/-- `Statement:` along every additive map `φ`, `symWalk s` lumps to `symWalk (φ s)`. -/
theorem symWalk_lumps (φ : G →+ H) (s : G) : Lumps (symWalk s) (symWalk (φ s)) φ := by
  intro x
  rw [symWalk_apply, symWalk_apply, Measure.map_add _ _ Measurable.of_discrete,
    Measure.map_smul, Measure.map_smul, Measure.map_dirac' Measurable.of_discrete,
    Measure.map_dirac' Measurable.of_discrete, map_add, map_sub]
  all_goals exact Measurable.of_discrete.aemeasurable

/-- `Statement:` if `φ t = 0`, `topBit t` lumps along `φ` to the identity kernel. -/
theorem topBit_lumps_id (φ : G →+ H) (t : G) (ht : φ t = 0) : Lumps (topBit t) Kernel.id φ := by
  intro x
  rw [topBit_apply, Kernel.id_apply, Measure.map_add _ _ Measurable.of_discrete,
    Measure.map_smul, Measure.map_smul, Measure.map_dirac' Measurable.of_discrete,
    Measure.map_dirac' Measurable.of_discrete, map_add, ht, add_zero, ← add_smul,
    ENNReal.inv_two_add_inv_two, one_smul]
  all_goals exact Measurable.of_discrete.aemeasurable

/-- `Statement:` integrating `dirac (g x) D` over `C` gives `μ (g ⁻¹' D ∩ C)`. -/
theorem setLIntegral_dirac_comp (g : G → G) (μ : Measure G) (C D : Set G) :
    ∫⁻ x in C, Measure.dirac (g x) D ∂μ = μ (g ⁻¹' D ∩ C) := by
  simp_rw [Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := D))]
  have : ∀ x, D.indicator (1 : G → ℝ≥0∞) (g x) = (g ⁻¹' D).indicator 1 x := fun _ => rfl
  simp_rw [this]
  rw [lintegral_indicator_one MeasurableSet.of_discrete,
    Measure.restrict_apply MeasurableSet.of_discrete]

/-- `Statement:` if `μ` is invariant under `· + s`, the `+s` flow from `A` into `B` equals the `-s`
flow from `B` into `A`. -/
theorem symWalk_translate_pair (s : G) (μ : Measure G) (hμ : μ.map (· + s) = μ) (A B : Set G) :
    ∫⁻ x in A, Measure.dirac (x + s) B ∂μ = ∫⁻ x in B, Measure.dirac (x - s) A ∂μ := by
  rw [setLIntegral_dirac_comp (· + s), setLIntegral_dirac_comp (· - s)]
  conv_rhs => rw [← hμ]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  congr 1
  ext x; simp [and_comm]

/-- `Statement:` `symWalk s` is reversible w.r.t. every measure invariant under `· + s`. -/
theorem symWalk_reversible (s : G) (μ : Measure G) (hμ : μ.map (· + s) = μ) :
    (symWalk s).IsReversible μ := by
  intro A B _ _
  simp only [symWalk_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left Measurable.of_discrete,
    lintegral_const_mul _ Measurable.of_discrete, lintegral_const_mul _ Measurable.of_discrete,
    lintegral_const_mul _ Measurable.of_discrete, lintegral_const_mul _ Measurable.of_discrete,
    symWalk_translate_pair s μ hμ A B, ← symWalk_translate_pair s μ hμ B A, add_comm]

/-- `Statement:` on a finite carrier, a measure with the same mass `c` on every point is invariant
under every translation. -/
theorem map_add_const_of_singleton_const [Finite G] (μ : Measure G) (c : ℝ≥0∞)
    (hc : ∀ x, μ {x} = c) (s : G) : μ.map (· + s) = μ := by
  refine Measure.ext_iff_singleton.2 fun y => ?_
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have : (· + s) ⁻¹' ({y} : Set G) = {y - s} := by
    ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff]; exact eq_sub_iff_add_eq.symm
  rw [this, hc, hc]

/-- `Statement:` the uniform law `uniformOn Set.univ` is invariant under every translation. -/
theorem uniformOn_univ_map_add [Fintype G] (s : G) :
    (uniformOn (Set.univ : Set G)).map (· + s) = uniformOn Set.univ :=
  map_add_const_of_singleton_const _ (1 / (Fintype.card G : ℝ≥0∞))
    (fun x => by rw [uniformOn_univ, Measure.count_singleton]) s

end Generic

/-- `Statement:` zoom out one binary digit: the reduction `ZMod (2^(n+1)) →+* ZMod (2^n)`. -/
noncomputable def zoom (n : ℕ) : ZMod (2 ^ (n + 1)) →+* ZMod (2 ^ n) :=
  ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ n)) _

/-- `Statement:` `zoom n` is measurable. -/
theorem zoom_measurable (n : ℕ) : Measurable (zoom n) := Measurable.of_discrete

/-- `Statement:` the ±1 walk on `ZMod (2^(n+1))` lumps along `zoom n` to the ±1 walk on `ZMod (2^n)`. -/
theorem zoom_symWalk_lumps (n : ℕ) :
    Lumps (symWalk (1 : ZMod (2 ^ (n + 1)))) (symWalk (1 : ZMod (2 ^ n))) (zoom n) := by
  have h := symWalk_lumps (zoom n).toAddMonoidHom (1 : ZMod (2 ^ (n + 1)))
  simpa [map_one] using h

/-- `Statement:` the fair random top digit `topBit (2^n)` on `ZMod (2^(n+1))` lumps along `zoom n` to
the identity kernel. -/
theorem zoom_topBit_lumps_id (n : ℕ) :
    Lumps (topBit (2 ^ n : ZMod (2 ^ (n + 1)))) Kernel.id (zoom n) := by
  have h := topBit_lumps_id (zoom n).toAddMonoidHom (2 ^ n : ZMod (2 ^ (n + 1))) (by
    show zoom n (2 ^ n) = 0
    rw [map_pow, map_ofNat]
    exact_mod_cast ZMod.natCast_self (2 ^ n))
  simpa using h

/-- `Statement:` doubling on `ZMod (2^(n+1))` lumps along `zoom n` to doubling on `ZMod (2^n)`. -/
theorem zoom_doubling_lumps (n : ℕ) :
    Lumps (Kernel.deterministic (fun x : ZMod (2 ^ (n + 1)) => 2 * x) Measurable.of_discrete)
      (Kernel.deterministic (fun x : ZMod (2 ^ n) => 2 * x) Measurable.of_discrete) (zoom n) :=
  (lumps_deterministic_iff _ _ (zoom_measurable n)).2 fun x => by simp [map_mul, map_ofNat]

/-- `Statement:` the rotation `x ↦ x + 1` on `ZMod (2^(n+1))` lumps along `zoom n` to the rotation on
`ZMod (2^n)`. -/
theorem zoom_rot_lumps (n : ℕ) :
    Lumps (Kernel.deterministic (fun x : ZMod (2 ^ (n + 1)) => x + 1) Measurable.of_discrete)
      (Kernel.deterministic (fun x : ZMod (2 ^ n) => x + 1) Measurable.of_discrete) (zoom n) :=
  (lumps_deterministic_iff _ _ (zoom_measurable n)).2 fun x => by simp [map_add, map_one]

/-- `Statement:` the right shift on `ZMod 8`, `x ↦ ⌊x.val / 2⌋`. -/
def shr8 (x : ZMod 8) : ZMod 8 := ((x.val / 2 : ℕ) : ZMod 8)

/-- `Statement:` CONTROL, the right shift on `ZMod 8` lumps along `zoom 2` to no kernel on `ZMod 4`:
`0` and `4` share a class and land in classes `0` and `2`. -/
theorem shr8_not_lumps :
    ¬ ∃ L : Kernel (ZMod 4) (ZMod 4),
      Lumps (Kernel.deterministic shr8 Measurable.of_discrete) L (zoom 2) := by
  rintro ⟨L, h⟩
  have e := h.fiberConst 0 4 (by decide)
  simp only [Kernel.deterministic_apply, Measure.map_dirac' (zoom_measurable 2)] at e
  rw [dirac_eq_dirac_iff] at e
  revert e
  decide

/-- `Statement:` the ±1 walk on `ZMod (2^n)` is reversible w.r.t. the uniform law. -/
theorem symWalk_unif_reversible (n : ℕ) :
    (symWalk (1 : ZMod (2 ^ n))).IsReversible (uniformOn Set.univ) :=
  symWalk_reversible _ _ (uniformOn_univ_map_add _)

/-- `Statement:` from the uniform law on `ZMod (2^(n+1))`, the run of the ±1 walk read through `zoom n`
has the law of the ±1 walk on `ZMod (2^n)` from the image law; that walk is reversible w.r.t. the image
law; and every window of the observed run has the law of its reversal. -/
theorem zoom_symWalk_trade (n : ℕ) :
    (chainLaw (uniformOn (Set.univ : Set (ZMod (2 ^ (n + 1))))) (symWalk 1)).map
          (fun x k => zoom n (x k)) =
        chainLaw ((uniformOn (Set.univ : Set (ZMod (2 ^ (n + 1))))).map (zoom n)) (symWalk 1) ∧
      (symWalk (1 : ZMod (2 ^ n))).IsReversible
        ((uniformOn (Set.univ : Set (ZMod (2 ^ (n + 1))))).map (zoom n)) ∧
      ∀ t m : ℕ,
        (chainLaw (uniformOn (Set.univ : Set (ZMod (2 ^ (n + 1))))) (symWalk 1)).map
            (fun x (i : Fin (m + 1)) => zoom n (x (t + i))) =
          (chainLaw (uniformOn (Set.univ : Set (ZMod (2 ^ (n + 1))))) (symWalk 1)).map
            (fun x (i : Fin (m + 1)) => zoom n (x (t + Fin.rev i))) :=
  ⟨chainLaw_map_of_lumps _ _ _ (zoom_measurable n) (zoom_symWalk_lumps n),
    isReversible_map_of_lumps (zoom_measurable n) (zoom_symWalk_lumps n)
      (symWalk_unif_reversible (n + 1)),
    fun t m => chainLaw_window_map_reverse _ _ (symWalk_unif_reversible (n + 1)) _
      (zoom_measurable n) t m⟩

/-- `Statement:` the rotation `x ↦ x + 1` on `ZMod (2^(n+2))` is reversible w.r.t. no probability
measure (`rot4_not_reversible` is the case of `Fin 4`). -/
theorem rot_not_reversible (n : ℕ) (μ : Measure (ZMod (2 ^ (n + 2)))) [IsProbabilityMeasure μ] :
    ¬ (Kernel.deterministic (fun x : ZMod (2 ^ (n + 2)) => x + 1)
      Measurable.of_discrete).IsReversible μ := by
  intro h
  have h2 : (2 : ZMod (2 ^ (n + 2))) ≠ 0 := by
    intro e
    have : ((2 : ℕ) : ZMod (2 ^ (n + 2))) = 0 := by exact_mod_cast e
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    have : 4 ≤ 2 ^ (n + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hz : ∀ x : ZMod (2 ^ (n + 2)), μ {x} = 0 := by
    intro x
    have := h (MeasurableSet.of_discrete (s := {x})) (MeasurableSet.of_discrete (s := {x + 1}))
    rw [lintegral_singleton, lintegral_singleton, Kernel.deterministic_apply,
      Kernel.deterministic_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete,
      Measure.dirac_apply' _ MeasurableSet.of_discrete] at this
    have hne : x + 1 + 1 ≠ x := by
      intro e; apply h2
      calc (2 : ZMod (2 ^ (n + 2))) = (x + 1 + 1) - x := by ring
        _ = 0 := by rw [e, sub_self]
    simpa [Set.indicator, hne] using this
  have : μ = 0 := (Measure.ext_iff_singleton).2 (by simpa using hz)
  exact IsProbabilityMeasure.ne_zero μ this

/-- `Statement:` the rotation on `ZMod 2`, the flip, is reversible w.r.t. the uniform law. -/
theorem rot2_reversible :
    (Kernel.deterministic (fun x : ZMod 2 => x + 1) Measurable.of_discrete).IsReversible
      (uniformOn Set.univ) :=
  isReversible_deterministic_involutive _ (by intro x; fin_cases x <;> rfl)
    (uniformOn_univ_map_add 1)

/-- `Statement:` the rotation on `ZMod 4` is reversible w.r.t. no probability measure, lumps along
`zoom 1` to the flip on `ZMod 2`, and the flip is reversible w.r.t. the uniform law.
`Reading:` zooming out is coarse-graining; on this tower the rotation's arrow is erased only at the
single-digit level; fine reversible ⇒ coarse reversible (`isReversible_map_of_lumps`), the converse
fails. -/
theorem zoom_last_step_erases_arrow :
    (∀ μ : Measure (ZMod 4), IsProbabilityMeasure μ →
        ¬ (Kernel.deterministic (fun x : ZMod 4 => x + 1) Measurable.of_discrete).IsReversible μ) ∧
      Lumps (Kernel.deterministic (fun x : ZMod (2 ^ 2) => x + 1) Measurable.of_discrete)
        (Kernel.deterministic (fun x : ZMod (2 ^ 1) => x + 1) Measurable.of_discrete) (zoom 1) ∧
      (Kernel.deterministic (fun x : ZMod 2 => x + 1) Measurable.of_discrete).IsReversible
        (uniformOn Set.univ) :=
  ⟨fun μ _ => rot_not_reversible 0 μ, zoom_rot_lumps 1, rot2_reversible⟩

/-- `Statement:` from `ZMod (2^(n+3))` to `ZMod (2^(n+2))` the rotation lumps to the rotation, and on
neither side is it reversible w.r.t. any probability measure. -/
theorem zoom_preserves_rot_arrow (n : ℕ) :
    (∀ μ : Measure (ZMod (2 ^ (n + 3))), IsProbabilityMeasure μ →
        ¬ (Kernel.deterministic (fun x : ZMod (2 ^ (n + 3)) => x + 1)
          Measurable.of_discrete).IsReversible μ) ∧
      Lumps (Kernel.deterministic (fun x : ZMod (2 ^ (n + 2 + 1)) => x + 1) Measurable.of_discrete)
        (Kernel.deterministic (fun x : ZMod (2 ^ (n + 2)) => x + 1) Measurable.of_discrete)
        (zoom (n + 2)) ∧
      (∀ ν : Measure (ZMod (2 ^ (n + 2))), IsProbabilityMeasure ν →
        ¬ (Kernel.deterministic (fun x : ZMod (2 ^ (n + 2)) => x + 1)
          Measurable.of_discrete).IsReversible ν) :=
  ⟨fun μ _ => rot_not_reversible (n + 1) μ, zoom_rot_lumps (n + 2),
    fun ν _ => rot_not_reversible n ν⟩

/-- `Statement:` on `Fin 4 = ZMod 4`, `parity4 x` is `decide (zoom 1 x = 1)`. -/
theorem parity4_eq_zoom (x : Fin 4) : parity4 x = decide (zoom 1 (x : ZMod 4) = 1) := by
  fin_cases x <;> decide

/-- `Statement:` the residue map `PadicInt.toZModPow n : ℤ_[2] → ZMod (2^n)` is measurable. -/
theorem toZModPow_measurable (n : ℕ) : Measurable (PadicInt.toZModPow (p := 2) n) :=
  measurable_to_countable' fun r => toZModPow_fiber_measurableSet n r

/-- `Statement:` doubling on ℤ_[2] lumps along `PadicInt.toZModPow n` to doubling on `ZMod (2^n)`. -/
theorem padic_doubling_lumps (n : ℕ) :
    Lumps (Kernel.deterministic (fun x : ℤ_[2] => 2 * x)
        (continuous_const.mul continuous_id).measurable)
      (Kernel.deterministic (fun r : ZMod (2 ^ n) => 2 * r) Measurable.of_discrete)
      (PadicInt.toZModPow n) :=
  (lumps_deterministic_iff _ _ (toZModPow_measurable n)).2 fun x => by simp [map_mul, map_ofNat]

/-- `Statement:` `zoom n ∘ toZModPow (n+1) = toZModPow n` on ℤ_[2] (Mathlib `PadicInt.cast_toZModPow`). -/
theorem zoom_comp_toZModPow (n : ℕ) (x : ℤ_[2]) :
    zoom n (PadicInt.toZModPow (n + 1) x) = PadicInt.toZModPow n x := by
  unfold zoom
  exact PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) x

end ZoomTower

/-! ### § XV. The bands of `Int.log 2`: the 2-adic norms on their left ends, and the gap count

`Int.log 2` (floor of `log₂`) is the upper adjoint of Mathlib's Galois coinsertion `Int.zpowLogGi`,
`k ↦ 2 ^ k` the lower; its fibres over the positive reals are the bands `log2Band k`. -/

section Log2Band

open Set OrderDual

/-- `Statement:` the band `[2 ^ k, 2 ^ (k + 1))` in ℝ. -/
noncomputable def log2Band (k : ℤ) : Set ℝ := Ico ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))

/-- `Statement:` for `0 < x`, `x ∈ log2Band k` iff `Int.log 2 x = k`; both directions. -/
theorem mem_log2Band_iff {x : ℝ} (hx : 0 < x) (k : ℤ) : x ∈ log2Band k ↔ Int.log 2 x = k := by
  have h1 := Int.zpow_le_iff_le_log (R := ℝ) (b := 2) (by norm_num) (x := k) hx
  have h2 := Int.lt_zpow_iff_log_lt (R := ℝ) (b := 2) (by norm_num) (x := k + 1) hx
  simp only [Nat.cast_ofNat] at h1 h2
  rw [log2Band, mem_Ico, h1, h2]; omega

/-- `Statement:` every positive real lies in exactly one band. -/
theorem log2Band_existsUnique {x : ℝ} (hx : 0 < x) : ∃! k, x ∈ log2Band k :=
  ⟨Int.log 2 x, (mem_log2Band_iff hx _).2 rfl, fun k hk => ((mem_log2Band_iff hx k).1 hk).symm⟩

/-- `Statement:` the bands are pairwise disjoint. -/
theorem log2Band_pairwise_disjoint : Pairwise (Function.onFun Disjoint log2Band) := by
  intro j k hjk
  rw [Function.onFun, Set.disjoint_left]
  intro x hj hk
  have hx : 0 < x := lt_of_lt_of_le (zpow_pos (by norm_num) j) hj.1
  exact hjk (((mem_log2Band_iff hx j).1 hj).symm.trans ((mem_log2Band_iff hx k).1 hk))

/-- `Statement:` the bands cover exactly the positive reals. -/
theorem iUnion_log2Band : (⋃ k, log2Band k) = Ioi 0 := by
  ext x; simp only [mem_iUnion, mem_Ioi]
  constructor
  · rintro ⟨k, hk⟩; exact lt_of_lt_of_le (zpow_pos (by norm_num) k) hk.1
  · intro hx; exact ⟨Int.log 2 x, (mem_log2Band_iff hx _).2 rfl⟩

/-- `Statement:` band `k` has length `2 ^ k`, its left end, and band `k - 1` has half the length of
band `k`; the ratio of the ends is 2 at every `k`. -/
theorem log2Band_length (k : ℤ) :
    (2 : ℝ) ^ (k + 1) - 2 ^ k = 2 ^ k ∧
      (2 : ℝ) ^ k - 2 ^ (k - 1) = ((2 : ℝ) ^ (k + 1) - 2 ^ k) / 2 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  refine ⟨by rw [zpow_add_one₀ h2]; ring, ?_⟩
  rw [zpow_add_one₀ h2, zpow_sub_one₀ h2]; ring

/-- `Statement:` for nonzero `x : ℚ_[2]`, `Int.log 2 ‖x‖ = -x.valuation` and `‖x‖ = 2 ^ Int.log 2 ‖x‖`,
the left end of its band (Mathlib `Padic.norm_eq_zpow_neg_valuation`). -/
theorem q2_log2_norm {x : ℚ_[2]} (hx : x ≠ 0) :
    Int.log 2 ‖x‖ = -x.valuation ∧ ‖x‖ = (2 : ℝ) ^ Int.log 2 ‖x‖ := by
  have hn := Padic.norm_eq_zpow_neg_valuation hx
  have hl : Int.log 2 ‖x‖ = -x.valuation := by
    rw [hn]; exact Int.log_zpow (R := ℝ) (b := 2) (by norm_num) _
  refine ⟨hl, ?_⟩
  rw [hl, hn]; norm_num

/-- `Statement:` for nonzero `x : ℤ_[2]`, `Int.log 2 ‖x‖ = -x.valuation` and
`q2Val x = (-Int.log 2 ‖x‖).toNat`. -/
theorem z2_log2_norm {x : ℤ_[2]} (hx : x ≠ 0) :
    Int.log 2 ‖x‖ = -(x.valuation : ℤ) ∧ q2Val x = ((-Int.log 2 ‖x‖).toNat : ℕ∞) := by
  have hl : Int.log 2 ‖x‖ = -(x.valuation : ℤ) := by
    rw [PadicInt.norm_eq_zpow_neg_valuation hx]
    exact Int.log_zpow (R := ℝ) (b := 2) (by norm_num) _
  refine ⟨hl, ?_⟩
  rw [hl, neg_neg, Int.toNat_natCast]
  simp [q2Val, hx]

/-- `Statement:` `Int.log 2` of `e2 (toDual n)`, read in ℝ, is `-n` for every `n : ℕ`. -/
theorem log2_e2_toDual_coe (n : ℕ) :
    Int.log 2 ((e2 (toDual (n : ℕ∞)) : NNReal) : ℝ) = -(n : ℤ) := by
  rw [e2_toDual_coe]
  have h : (((2⁻¹ : NNReal) ^ n : NNReal) : ℝ) = ((2 : ℕ) : ℝ) ^ (-(n : ℤ)) := by
    push_cast; rw [zpow_neg, zpow_natCast, inv_pow]
  simp only
  rw [h]; exact Int.log_zpow (R := ℝ) (b := 2) (by norm_num) _

/-- `Statement:` no norm of `ℚ_[2]`, 0 of `ℚ_[2]` included, lies in the open band
`(2 ^ k, 2 ^ (k + 1))`. -/
theorem q2_norm_not_mem_Ioo (x : ℚ_[2]) (k : ℤ) :
    ‖x‖ ∉ Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := by
  rintro ⟨h1, h2⟩
  have hx : x ≠ 0 := by
    rintro rfl; rw [norm_zero] at h1; exact absurd h1 (not_lt.2 (zpow_pos (by norm_num) k).le)
  have hk : Int.log 2 ‖x‖ = k := (mem_log2Band_iff (norm_pos_iff.2 hx) k).1 ⟨h1.le, h2⟩
  have := (q2_log2_norm hx).2
  rw [hk] at this; exact absurd this h1.ne'

/-- `Statement:` the same for the norms of ℤ_[2] (`PadicInt.norm_def`). -/
theorem z2_norm_not_mem_Ioo (x : ℤ_[2]) (k : ℤ) :
    ‖x‖ ∉ Ioo ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)) := by
  rw [PadicInt.norm_def]; exact q2_norm_not_mem_Ioo _ k

/-- `Statement:` the gap `n2GapInt n` of § XIII is the band `log2Band (-(n + 1))` without its left end. -/
theorem n2GapInt_eq_log2Band (n : ℕ) :
    n2GapInt n = log2Band (-((n : ℤ) + 1)) \ {(2 : ℝ) ^ (-((n : ℤ) + 1))} := by
  rw [log2Band, Ico_sdiff_left, n2GapInt, n2_half_pow_eq_zpow, n2_half_pow_eq_zpow,
    show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring]
  push_cast; rfl

/-- `Statement:` for nonzero `x : ℚ_[2]`, `cxQ2 x` is the number of band indices `k` with
`Int.log 2 ‖x‖ ≤ k < 0`; through `n2GapInt_eq_log2Band`, the gaps counted by `cxQ2_eq_gap_count`. -/
theorem cxQ2_eq_log2Band_count {x : ℚ_[2]} (hx : x ≠ 0) :
    cxQ2 x = (Ico (Int.log 2 ‖x‖) 0).encard := by
  rw [← Finset.coe_Ico, encard_coe_eq_coe_finsetCard, Int.card_Ico, (q2_log2_norm hx).1]
  simp [cxQ2, hx]

/-- `Statement:` `WithBot ℤ` has no atom: nothing covers its ⊥. -/
theorem withBotInt_no_atom : ¬ ∃ a : WithBot ℤ, IsAtom a := by
  rintro ⟨a, ha⟩
  induction a using WithBot.recBotCoe with
  | bot => exact ha.1 rfl
  | coe k =>
    have h := ha.2 ((k - 1 : ℤ) : WithBot ℤ) (WithBot.coe_lt_coe.2 (by omega))
    exact WithBot.coe_ne_bot h

/-- `Statement:` `Int.log 2` on the positive reals, sending every `x ≤ 0` to ⊥ of `WithBot ℤ`. -/
noncomputable def log2WithBot (x : ℝ) : WithBot ℤ := if 0 < x then (Int.log 2 x : WithBot ℤ) else ⊥

/-- `Statement:` `log2WithBot` is monotone. -/
theorem log2WithBot_mono : Monotone log2WithBot := by
  intro x y hxy
  unfold log2WithBot
  by_cases hx : 0 < x
  · have hy : 0 < y := lt_of_lt_of_le hx hxy
    simp only [hx, hy, ite_true]
    exact WithBot.coe_le_coe.2 (Int.log_mono_right hx hxy)
  · simp only [hx, ite_false]; exact bot_le

/-- `Statement:` on `WithBot ℤ`, the target of `log2WithBot` (join `max`), each `k` is covered by
`k + 1`, and the mass of `stepOff` is 0 at every `p` (`withBotInt_no_atom`). -/
theorem log2Chart_stepOff_mass_zero (p : NNReal) (hp : p ≤ 1) :
    (∀ k : ℤ, (k : WithBot ℤ) ⋖ ((k + 1 : ℤ) : WithBot ℤ)) ∧
      trials p hp (@stepOff (WithBot ℤ) (linearMaxZPS (WithBot ℤ) ⊥ (fun _ => bot_le))) = 0 := by
  classical
  refine ⟨fun k => WithBot.coe_covBy_coe.2 (Order.covBy_add_one k), ?_⟩
  have h := (linear_stepOff_mass_one_iff (α := WithBot ℤ) p hp).not.2
    (fun ⟨ha, _⟩ => withBotInt_no_atom ha)
  rw [stepOff_mass] at h ⊢
  split_ifs with hc
  · simp [hc] at h
  · rfl

end Log2Band

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms tape_never_fires_iff
#print axioms dial_fire_jump
#print axioms fireMass
#print axioms fireMass_eq
#print axioms fireMass_not_continuousAt_zero
#print axioms fireWithin
#print axioms dial_fire_within
#print axioms fireWithin_continuous
#print axioms fireWithin_mono
#print axioms dial_digital_limit
#print axioms dial_not_uniform_witness
#print axioms dial_not_uniform
#print axioms dial_jump_into_L
#print axioms stepOff
#print axioms stepOff_of_firstStep
#print axioms stepOff_of_not_firstStep
#print axioms stepOff_mass
#print axioms stepOff_ae_iff
#print axioms linear_stepOff_mass_one_iff
#print axioms dense_stepOff_mass_zero
#print axioms zero_mass_two_causes
#print axioms W
#print axioms W_not_firstStep
#print axioms W_not_dense
#print axioms supBotZPS
#print axioms supBotZPS_le_iff
#print axioms supBotZPS_lt_iff
#print axioms supBotZPS_covBy_iff
#print axioms supBotZPS_botHasFirstStep_iff
#print axioms NInfDual
#print axioms BoolNInfL
#print axioms boolNInfL_bot_eq
#print axioms boolNInfL_bot_covBy_true
#print axioms boolNInfL_botHasFirstStep
#print axioms boolNInfL_stepOff_mass
#print axioms nInfDualRun
#print axioms nInfDualRun_ne_bot
#print axioms nInfDualRun_strictAnti
#print axioms enat_natCast_covBy_succ
#print axioms nInfDualRun_covBy
#print axioms boolNInfL_bot_isGLB
#print axioms nInfDualRun_tendsto
#print axioms boolNInfL_no_nInfDual_cover
#print axioms boolNInfL_bot_cover_unique
#print axioms boolNInfL_bot_cover_and_limit
#print axioms nInfDual_not_botHasFirstStep
#print axioms nInfDual_stepOff_mass
#print axioms nInfDual_bot_isGLB
#print axioms bool_bot_not_isGLB
#print axioms N2
#print axioms n2OrderBot
#print axioms n2Pow
#print axioms n2Pow_top
#print axioms n2Pow_coe
#print axioms n2Pow_mem
#print axioms n2Pow_strictAnti
#print axioms e2
#print axioms e2_toDual_top
#print axioms e2_toDual_coe
#print axioms q2_nnnorm_eq_inv_pow
#print axioms q2_nnnorm_mem
#print axioms normN2
#print axioms normN2_eq_e2_q2Val
#print axioms normN2_zero
#print axioms n2Run
#print axioms n2Run_eq_norm
#print axioms normN2_surjective
#print axioms boolN2Iso
#print axioms boolN2_bot_cover_and_limit
#print axioms boolN2_stepOff_mass
#print axioms fadingTrials_fires_iIndepSet
#print axioms schedule_fires_of_tsum_top
#print axioms schedule_snap_ae
#print axioms schedule_never_pos
#print axioms schedule_halving_control
#print axioms law_two_faces
#print axioms tsum_cylinder_bot_indicator
#print axioms lintegral_wait_succ
#print axioms lintegral_wait_succ_inv
#print axioms wait_chart_top
#print axioms lintegral_wait
#print axioms wait_mean_inj
#print axioms wait_mean_surj
#print axioms wait_mean_existsUnique
#print axioms unpack
#print axioms unpack_apply
#print axioms unpack_measurePreserving
#print axioms pack_measurePreserving
#print axioms dial_entropy_pos_iff
#print axioms bot_mem_support_of_entropy_pos
#print axioms dial_two_faces_iff
#print axioms trials_support_null
#print axioms dial_pinned_faces
#print axioms xorOffset
#print axioms xorOffset_apply
#print axioms xorOffset_bot
#print axioms det_xorOffset_eq_ofNat_iff
#print axioms xorOffset_measurePreserving_fair
#print axioms fair_wait_offset
#print axioms xorOffset_measurePreserving_iff
#print axioms pathLast
#print axioms measurable_pathLast
#print axioms homK
#print axioms isMarkovKernel_homK
#print axioms runLaw
#print axioms isProbabilityMeasure_runLaw
#print axioms Subordinate
#print axioms stayPaths
#print axioms measurableSet_stayPaths
#print axioms stayPaths_step_mass
#print axioms start_mem_stayPaths
#print axioms partialTraj_stayPaths
#print axioms runLaw_eq
#print axioms runLaw_stay
#print axioms measurableSet_stayRun
#print axioms runLaw_stay_eq_trials
#print axioms runLaw_leaves
#print axioms ae_leaves_iff
#print axioms ae_isRun
#print axioms not_subordinate_of_noStepAt
#print axioms leave_zero_of_selfOnlyAt
#print axioms leavesAt_of_pos
#print axioms ofFun_kernel_dirac
#print axioms slotKernel
#print axioms isMarkovKernel_slotKernel
#print axioms slotKernel_subordinate
#print axioms slotKernel_leave
#print axioms slot_stay_eq_trials
#print axioms glauber_slot_leaves
#print axioms leave_half_of_maxEntropy
#print axioms Lumps
#print axioms FiberConst
#print axioms Lumps.fiberConst
#print axioms mapHist
#print axioms measurable_mapHist
#print axioms appendHist
#print axioms measurable_appendHist
#print axioms mapHist_comp_appendHist
#print axioms appendHist_prefix
#print axioms chainLaw
#print axioms isProbabilityMeasure_chainLaw
#print axioms runLaw_eq_chainLaw
#print axioms chainLaw_prefix_zero
#print axioms chainLaw_step
#print axioms chainLaw_prefix_succ
#print axioms compProd_comap_map
#print axioms homK_compProd_naturality
#print axioms chainLaw_prefix_naturality
#print axioms pathMeasure_eq_of_prefix_eq
#print axioms chainLaw_map_of_lumps
#print axioms runLaw_map_of_lumps
#print axioms runLaw_time_one
#print axioms lumps_of_runLaw_map
#print axioms lumps_iff_runLaw_map
#print axioms lumps_deterministic_iff
#print axioms subordinate_quot_of_lumps
#print axioms subordinate_quot_of_lumps_countable
#print axioms suppMotion
#print axioms subordinate_supp
#print axioms stepCompat_supp_of_fiberConst
#print axioms suppControlKernel
#print axioms suppControlKernel_stepCompat_not_fiberConst
#print axioms measurableSet_leaves
#print axioms ae_obs_leaves_iff
#print axioms lumped_leave_weight
#print axioms quot_leavesAt_of_ae
#print axioms lumps_id_of_upStepInvariant
#print axioms ae_landing_const
#print axioms isReversible_map_of_lumps
#print axioms isReversible_unit
#print axioms isReversible_deterministic_involutive
#print axioms isReversible_deterministic_of_ae_id
#print axioms rot4
#print axioms parity4
#print axioms rot4_not_reversible
#print axioms rot4_lumps_parity4
#print axioms boolSwap_reversible
#print axioms a4_direction_erased
#print axioms DetailedBalance
#print axioms coarseLaw2
#print axioms coarseLaw3
#print axioms sum3_reverse
#print axioms coarseLaw2_reverse
#print axioms coarseLaw3_reverse
#print axioms classWeight
#print axioms aggregatedChain
#print axioms aggregatedChain_detailedBalance
#print axioms lazyPairs
#print axioms unifFin4
#print axioms lazyPairsProj
#print axioms detailedBalance_lazyPairs
#print axioms projClassMass
#print axioms lazyPairs_not_lumpable
#print axioms lazyPairs_coarse_not_markov
#print axioms lazyPairs_coarse_reversal_symmetric
#print axioms flip4
#print axioms lazyPairs_sigma_reversible
#print axioms absorb4
#print axioms absorb4Coarse
#print axioms absorb4_lumps
#print axioms absorb4_reversible
#print axioms absorb4_coarse_reversible
#print axioms absorb4_not_sigma_reversible
#print axioms chainLaw_pair
#print axioms histFirst2
#print axioms measurable_histFirst2
#print axioms chainLaw_triple
#print axioms chainLaw_triple_singleton
#print axioms kernelMat
#print axioms measureVec
#print axioms chainLaw_coarse3_eq_coarseLaw3
#print axioms detailedBalance_of_isReversible
#print axioms chainLaw_coarse3_reverse
#print axioms pathWeight
#print axioms pathWeight_eq_end
#print axioms pathWeight_rev
#print axioms pathWeight_succ
#print axioms coarseLawN
#print axioms coarseLawN_reverse
#print axioms coarseLawN_id
#print axioms sum_fin3
#print axioms coarseLaw3_eq_coarseLawN
#print axioms rotMat
#print axioms rotMat_not_detailedBalance
#print axioms rot4_coarse_not_reversal_symmetric
#print axioms finPath
#print axioms measurable_finPath
#print axioms chainLaw_map_zero
#print axioms chainLaw_finPath_singleton
#print axioms chainLaw_coarseN_eq_coarseLawN
#print axioms chainLaw_coarseN_reverse
#print axioms chainLaw_finPath_map_rev
#print axioms chainLaw_coarseN_map_reverse
#print axioms map_tail_singleton
#print axioms chainLaw_window_singleton
#print axioms chainLaw_window_eq_finPath
#print axioms chainLaw_window_map_reverse
#print axioms rot4_chainLaw_not_reversal_symmetric
#print axioms boolSwap_reversible_half
#print axioms isProbabilityMeasure_halfBool
#print axioms coarse_graining_trade
#print axioms n2Real
#print axioms n2Real_eq
#print axioms n2_half_pow_eq_zpow
#print axioms n2_half_pow_tendsto
#print axioms isClosed_n2Real
#print axioms volume_n2Real
#print axioms n2Real_subset_Icc
#print axioms ediam_n2Real
#print axioms spanGap_n2Real
#print axioms n2GapInt
#print axioms Icc_diff_n2Real
#print axioms volume_n2GapInt
#print axioms n2GapInt_pairwise_disjoint
#print axioms tsum_volume_n2GapInt
#print axioms volume_iUnion_n2GapInt
#print axioms n2Gaps_above_finite
#print axioms cxQ2_eq_gap_count
#print axioms real_spanGap_zero
#print axioms spanGap_scaled_n2Real
#print axioms ediam_ball_Z2
#print axioms haar_eq_ediam_ball_Z2
#print axioms gapRemaining
#print axioms gapCount
#print axioms gapLadder
#print axioms gapRemaining_ladder
#print axioms gapCount_ladder
#print axioms gapCount_remaining_ladder
#print axioms logb_inv_gapRemaining_ladder
#print axioms ladder_count_eq_log
#print axioms gapCount_ladder_scale
#print axioms cxQ2_eq_gapCount
#print axioms cxQ2_two_pow_eq_log
#print axioms dimH_n2Real
#print axioms harmGaps
#print axioms gapRemaining_harm
#print axioms gapCount_harm_zero
#print axioms gapCount_harm_two
#print axioms harm_no_log_law
#print axioms symWalk
#print axioms symWalk_apply
#print axioms isMarkovKernel_symWalk
#print axioms topBit
#print axioms topBit_apply
#print axioms isMarkovKernel_topBit
#print axioms symWalk_lumps
#print axioms topBit_lumps_id
#print axioms setLIntegral_dirac_comp
#print axioms symWalk_translate_pair
#print axioms symWalk_reversible
#print axioms map_add_const_of_singleton_const
#print axioms uniformOn_univ_map_add
#print axioms zoom
#print axioms zoom_measurable
#print axioms zoom_symWalk_lumps
#print axioms zoom_topBit_lumps_id
#print axioms zoom_doubling_lumps
#print axioms zoom_rot_lumps
#print axioms shr8
#print axioms shr8_not_lumps
#print axioms symWalk_unif_reversible
#print axioms zoom_symWalk_trade
#print axioms rot_not_reversible
#print axioms rot2_reversible
#print axioms zoom_last_step_erases_arrow
#print axioms zoom_preserves_rot_arrow
#print axioms parity4_eq_zoom
#print axioms toZModPow_measurable
#print axioms padic_doubling_lumps
#print axioms zoom_comp_toZModPow
#print axioms log2Band
#print axioms mem_log2Band_iff
#print axioms log2Band_existsUnique
#print axioms log2Band_pairwise_disjoint
#print axioms iUnion_log2Band
#print axioms log2Band_length
#print axioms q2_log2_norm
#print axioms z2_log2_norm
#print axioms log2_e2_toDual_coe
#print axioms q2_norm_not_mem_Ioo
#print axioms z2_norm_not_mem_Ioo
#print axioms n2GapInt_eq_log2Band
#print axioms cxQ2_eq_log2Band_count
#print axioms withBotInt_no_atom
#print axioms log2WithBot
#print axioms log2WithBot_mono
#print axioms log2Chart_stepOff_mass_zero
end PurityCheck
