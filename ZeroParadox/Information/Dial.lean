import ZeroParadox.Information.BottomTotality
import ZeroParadox.Information.StartBit
import ZeroParadox.Information.TwoRequirements
import ZeroParadox.Valuation.UltrametricView
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
the law; § VII: mean of `wait + 1` is `p⁻¹`; § VIII: columns; § IX: entropy pins `0 < p < 1`; § X: translations.
-/

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
-- (`bot_le`), the only never-firing tape (`tape_never_fires_iff`), wait ⊤ of `ℕ∞` (`wait_bot`).
-- Reading: (Tim's) ⊥ simultaneously minimally and maximally complex; the complexity rate of
-- `trials p` tapes is `brudno_ae_trials` (`ZeroParadox/Information/BrudnoBridge.lean`).
example (w : ℕ → Bool) : (⊥ : ℕ → Bool) ≤ w ∧ ((¬ ∃ k, w k = true) ↔ w = fun _ => false) ∧
    waitENat (det (⊥ : ℕ → Bool)) = ⊤ :=
  ⟨bot_le, tape_never_fires_iff w, wait_bot⟩

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
end PurityCheck
