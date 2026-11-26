import ZeroParadox.Information.BottomTotality
import ZeroParadox.Information.StartBit
import ZeroParadox.Information.TwoRequirements
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
Switch: "some stage fires" has `trials p hp` mass 0 at `p = 0`, 1 for `0 < p ≤ 1` (§ II). Volume:
"fires within `n` stages" is `1 - (1 - p) ^ n`, continuous, tending to the switch non-uniformly
(§ III). § IV: the jump in a `ZPSemilattice`, forward maps only; § V, § VI: schedules, the law.
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
`0 < p ≤ 1`. One is probability one: ⊥ of `ℕ → Bool` stays a member, of mass 0
(`trials_bot_mass_jump`). -/
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
end PurityCheck
