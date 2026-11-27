import ZeroParadox.Information.BottomTotality
import ZeroParadox.Information.StartBit
import ZeroParadox.Information.TwoRequirements
import ZeroParadox.Valuation.UltrametricView
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Invariance
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
stages" is continuous in `p` and tends to the switch non-uniformly. § IV: the jump in `L`; § V-VI: schedules,
the law; § VII: mean of `wait + 1` is `p⁻¹`; § VIII: columns; § IX: entropy pins `0 < p < 1`; § X: translations;
§ XI: a supplied Markov kernel on the die; § XII: lumping, and the time arrow under coarse-graining. -/

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

/-! ### § XII. Lumping: the observed chain, and the time arrow under coarse-graining

`Reading:` a map `f` out of the states is an observer; when the kernel lumps along `f`, what the
observer sees is again a Markov chain (`lumps_iff_runLaw_map`), the weighted analogue of the die's
`StepCompat`. Both directions of the arrow are stated: coarse-graining can erase a time arrow
(`a4_direction_erased`), and from a reversible start it creates none, for a lumping map in general
(`isReversible_map_of_lumps`) and for every observer at three times on a finite carrier
(`chainLaw_coarse3_reverse`). The kernel is a supplied argument throughout. -/

section Lumping

open Finset

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- `Statement:` strong lumpability, Dynkin's intertwining form: `(K a).map f = L (f a)` at every `a`. -/
def Lumps (K : Kernel α α) (L : Kernel β β) (f : α → β) : Prop := ∀ a, (K a).map f = L (f a)

/-- `Statement:` related starts put the same image mass on every class (Kemeny-Snell's form). -/
def FiberConst (K : Kernel α α) (f : α → β) : Prop :=
  ∀ a a', f a = f a' → (K a).map f = (K a').map f

/-- `Statement:` lumping to some `L` gives the per-class form; one way. -/
theorem Lumps.fiberConst {K : Kernel α α} {L : Kernel β β} {f : α → β} (h : Lumps K L f) :
    FiberConst K f := fun a a' e => by rw [h a, h a', e]

/-- `Statement:` the coordinatewise map of a finite history. -/
def mapHist (f : α → β) (n : ℕ) (x : (i : Iic n) → α) : (i : Iic n) → β := fun i => f (x i)

/-- `Statement:` `mapHist f n` is measurable when `f` is. -/
theorem measurable_mapHist {f : α → β} (hf : Measurable f) (n : ℕ) : Measurable (mapHist f n) :=
  measurable_pi_iff.mpr fun i => hf.comp (measurable_pi_apply i)

/-- `Statement:` append one state to a finite history. -/
def appendHist (n : ℕ) (p : ((i : Iic n) → α) × α) : (i : Iic (n + 1)) → α :=
  IicProdIoc (X := fun _ : ℕ => α) n (n + 1)
    (p.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ => α) n p.2)

/-- `Statement:` `appendHist n` is measurable. -/
theorem measurable_appendHist (n : ℕ) : Measurable (appendHist (α := α) n) :=
  measurable_IicProdIoc.comp (measurable_fst.prodMk
    ((MeasurableEquiv.piSingleton (X := fun _ : ℕ => α) n).measurable.comp measurable_snd))

/-- `Statement:` mapping coordinatewise commutes with appending. -/
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

/-- `Statement:` the prefix of length `n + 2` is the prefix of length `n + 1` with `x (n + 1)` appended. -/
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

/-- `Statement:` the length-1 prefix of `chainLaw μ K` is `μ`, read on `Iic 0`. -/
theorem chainLaw_prefix_zero (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] :
    (chainLaw μ K).map (Preorder.frestrictLe 0) =
      μ.map (MeasurableEquiv.piUnique (fun _ : Iic 0 => α)).symm := by
  rw [chainLaw, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

/-- `Statement:` the law of (prefix to `n`, state `n + 1`) is the prefix law `⊗ₘ homK K n`
(Mathlib's `Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure`). -/
theorem chainLaw_step (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) :
    ((chainLaw μ K).map (Preorder.frestrictLe n)) ⊗ₘ homK K n =
      (chainLaw μ K).map (fun x => (Preorder.frestrictLe n x, x (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => α) (μ₀ := μ) (κ := homK K) (a := n)

/-- `Statement:` the next prefix law is the current one `⊗ₘ homK K n`, appended. -/
theorem chainLaw_prefix_succ (μ : Measure α) [IsProbabilityMeasure μ] (K : Kernel α α)
    [IsMarkovKernel K] (n : ℕ) :
    (((chainLaw μ K).map (Preorder.frestrictLe n)) ⊗ₘ homK K n).map (appendHist n) =
      (chainLaw μ K).map (Preorder.frestrictLe (n + 1)) := by
  rw [chainLaw_step, Measure.map_map (measurable_appendHist n) (by fun_prop)]
  congr 1
  funext x
  exact appendHist_prefix n x

/-- `Statement:` pushing the first factor of `μh ⊗ₘ κ.comap e` along `e` gives `μh.map e ⊗ₘ κ`. -/
theorem compProd_comap_map {Y Z X : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    [MeasurableSpace X] (μh : Measure Y) [SFinite μh] {e : Y → X} (he : Measurable e)
    (κ : Kernel X Z) [IsSFiniteKernel κ] :
    (μh ⊗ₘ κ.comap e he).map (Prod.map e id) = μh.map e ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (he.prodMap measurable_id) hs,
    Measure.compProd_apply (he.prodMap measurable_id hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) he]
  rfl

/-- `Statement:` if `K` lumps to `L` along `f`, one step of the history commutes with `f`. -/
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

/-- `Statement:` under lumping, every finite prefix of the observed chain has the lumped prefix law. -/
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

/-- `Statement:` two probability measures on `ℕ → β` with equal laws on every prefix are equal
(Mathlib's `IsProjectiveLimit.unique`). -/
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

/-- `Statement:` if `K` lumps to `L` along measurable `f`, the observed process `n ↦ f (x n)` of the
chain from `μ` has the law of the `L`-chain from `μ.map f`. -/
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

/-- `Statement:` the same from a point: the observed run of `runLaw K x₀` has law `runLaw L (f x₀)`. -/
theorem runLaw_map_of_lumps (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K] [IsMarkovKernel L]
    {f : α → β} (hf : Measurable f) (h : Lumps K L f) (x₀ : α) :
    (runLaw K x₀).map (fun x n => f (x n)) = runLaw L (f x₀) := by
  rw [runLaw_eq_chainLaw, runLaw_eq_chainLaw, ← Measure.map_dirac' hf]
  exact chainLaw_map_of_lumps (Measure.dirac x₀) K L hf h

/-- `Statement:` the time-1 marginal of `runLaw K x` is `K x`. -/
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

/-- `Statement:` if from every start the observed run has the `L`-chain's law, `K` lumps to `L`. -/
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

/-- `Statement:` for measurable `f`, `K` lumps to `L` along `f` iff from every start the observed run
has the law of the `L`-chain from the observed start; both directions. -/
theorem lumps_iff_runLaw_map (K : Kernel α α) (L : Kernel β β) [IsMarkovKernel K]
    [IsMarkovKernel L] {f : α → β} (hf : Measurable f) :
    Lumps K L f ↔ ∀ x₀, (runLaw K x₀).map (fun x n => f (x n)) = runLaw L (f x₀) :=
  ⟨fun h x₀ => runLaw_map_of_lumps K L hf h x₀, lumps_of_runLaw_map K L hf⟩

-- Statement: CONTROL, the identity map: every kernel lumps to itself.
example (K : Kernel α α) : Lumps K K id := fun _ => Measure.map_id

/-- `Statement:` for deterministic kernels, lumping along `f` is the semiconjugacy `f ∘ g = g' ∘ f`. -/
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
support die is step-compatible with `s`; one way (CONTROL B below). -/
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

-- Statement: CONTROL B, step-compatible moves do not force lumpable weights: on `Fin 3`, classes
-- `{0, 1}` and `{2}`, a die stepping everywhere, and the deterministic kernel `0 ↦ 0, 1 ↦ 2, 2 ↦ 2`.
example : let obs : Fin 3 → Bool := fun x => decide (x = 2)
    let g : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else x
    let M : Motion (Fin 3) := Motion.ofTotal id (fun _ => rfl) (fun _ _ => True)
    M.StepCompat (Setoid.ker obs) ∧ Subordinate M (Kernel.deterministic g (by fun_prop)) ∧
      ¬ FiberConst (Kernel.deterministic g (by fun_prop)) obs := by
  intro obs g M
  refine ⟨fun a a' b _ _ => ⟨b, trivial, rfl⟩, fun a => Filter.Eventually.of_forall fun _ => trivial,
    fun h => ?_⟩
  have := h 0 1 (show decide ((0 : Fin 3) = 2) = decide ((1 : Fin 3) = 2) by decide)
  simp only [Kernel.deterministic_apply, Measure.map_dirac' (by fun_prop : Measurable obs),
    dirac_eq_dirac_iff] at this
  exact absurd this (by decide)

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

/-- `Statement:` if UP is a total idempotent `r` unchanged along steps (`UpStepInvariant`), a subordinate
kernel lumps along `r` to the identity kernel. -/
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

/-- `Statement:` CONTROL, every Markov kernel on `Unit` is reversible w.r.t. every measure. -/
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

/-- `Statement:` the swap of `Bool` is reversible w.r.t. the counting measure on `Bool`. -/
theorem boolSwap_reversible :
    (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)).IsReversible
      (Measure.dirac true + Measure.dirac false) := by
  refine isReversible_deterministic_involutive _ Bool.not_not ?_
  rw [Measure.map_add _ _ (measurable_of_finite _), Measure.map_dirac' (measurable_of_finite _),
    Measure.map_dirac' (measurable_of_finite _)]
  simp [add_comm]

/-- `Statement:` coarse-graining erases an arrow: `rot4` is reversible w.r.t. no probability measure,
lumps along `parity4` to the swap of `Bool`, and the swap is reversible. -/
theorem a4_direction_erased :
    (∀ π : Measure (Fin 4), IsProbabilityMeasure π →
        ¬ (Kernel.deterministic rot4 (measurable_of_finite _)).IsReversible π) ∧
      Lumps (Kernel.deterministic rot4 (measurable_of_finite _))
        (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)) parity4 ∧
      (Kernel.deterministic (fun b : Bool => !b) (measurable_of_finite _)).IsReversible
        (Measure.dirac true + Measure.dirac false) :=
  ⟨fun π _ => rot4_not_reversible π, rot4_lumps_parity4, boolSwap_reversible⟩

section Matrix
variable {ι κ R : Type*} [Fintype ι] [DecidableEq κ] [CommSemiring R]

/-- `Statement:` detailed balance, matrix form: `π x * P x y = π y * P y x`. -/
def DetailedBalance (P : ι → ι → R) (π : ι → R) : Prop := ∀ x y, π x * P x y = π y * P y x

/-- `Statement:` the observed two-time statistic `Pr(f X₀ = a, f X₁ = b)` from `π`. -/
def coarseLaw2 (π : ι → R) (P : ι → ι → R) (f : ι → κ) (a b : κ) : R :=
  ∑ x, ∑ y, if f x = a ∧ f y = b then π x * P x y else 0

/-- `Statement:` the observed three-time statistic `Pr(f X₀ = a, f X₁ = b, f X₂ = c)` from `π`. -/
def coarseLaw3 (π : ι → R) (P : ι → ι → R) (f : ι → κ) (a b c : κ) : R :=
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

/-- `Statement:` `lazyPairs` is not lumpable along `lazyPairsProj`: `1` and `3` share a class and send
different mass into class `0`. -/
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

/-- `Statement:` and its observed three-time statistic is reversal-symmetric. -/
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

/-- `Statement:` it is reversible w.r.t. every measure carried by its fixed points `1` and `3`. -/
theorem absorb4_reversible (s t : ENNReal) :
    (Kernel.deterministic absorb4 (measurable_of_finite _)).IsReversible
      (s • Measure.dirac (1 : Fin 4) + t • Measure.dirac (3 : Fin 4)) := by
  refine isReversible_deterministic_of_ae_id _ ?_
  rw [ae_add_measure_iff]
  have hm : MeasurableSet {x : Fin 4 | absorb4 x = x} := (Set.toFinite _).measurableSet
  refine ⟨Measure.ae_smul_measure ((ae_dirac_iff hm).2 (by decide)) _,
    Measure.ae_smul_measure ((ae_dirac_iff hm).2 (by decide)) _⟩

/-- `Statement:` so `absorb4Coarse` is reversible w.r.t. the image law (`isReversible_map_of_lumps`). -/
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

/-- `Statement:` on a finite carrier, for every kernel, every initial probability law `μ` and every
measurable observer `f`, the law of `(f (x 0), f (x 1), f (x 2))` at `(a, b, c)` is `coarseLaw3` of
`measureVec μ` and `kernelMat K`. -/
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

/-- `Statement:` on a finite carrier, if `K` is reversible w.r.t. the initial law `μ`, then for every
measurable observer `f` the observed three-time law at `(a, b, c)` equals that at `(c, b, a)`. -/
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

end Lumping

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
end PurityCheck
