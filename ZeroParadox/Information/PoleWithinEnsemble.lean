-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): ⊥ of `ℕ → Bool`, the never-firing tape, inside the support of `trials p hp` and in the closure of its Martin-Löf random firing tapes, with the waiting time read as a limit and as a value. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.TapeHalting
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENat
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic

/-!
# The never-firing tape inside the firing ensemble

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
For `0 < p < 1`, ⊥ of `ℕ → Bool` is `trials p hp`-null, in its support, and a limit of random firing tapes whose waits diverge (`pole_within_ensemble` in `ℕ∞`; `pole_within_ensemble_limit` in `NInf`).
At `p = 0` the mass of `{⊥}` jumps while every cylinder's mass is continuous (§ VI); explicit non-random tapes give the limit with no measure in the statement (§ VII).
Nothing here identifies ⊥ of a `ZPSemilattice` with a tape or with `trials p hp`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open MeasureTheory Filter Topology NInf

/-! ### § I. Cylinders and support -/

/-- `Statement:` a cylinder of `ℕ → Bool` is a finite product of singletons. -/
theorem cyl_eq_pi (w : ℕ → Bool) (n : ℕ) :
    PiNat.cylinder w n = (↑(Finset.range n) : Set ℕ).pi (fun i => ({w i} : Set Bool)) := by
  ext y; simp [PiNat.cylinder]

/-- `Statement:` the `trials p hp` mass of a cylinder is the product of `p` and `1 - p` factors. -/
theorem trials_cyl (p : NNReal) (hp : p ≤ 1) (w : ℕ → Bool) (n : ℕ) :
    trials p hp (PiNat.cylinder w n) =
      ∏ i ∈ Finset.range n, (if w i then (p : ENNReal) else ((1 - p : NNReal) : ENNReal)) := by
  rw [cyl_eq_pi, trials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton _)]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases w i <;> simp [PMF.bernoulli]

/-- `Statement:` if `0 < p < 1`, every cylinder has positive `trials p hp` mass. -/
theorem trials_cyl_pos (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) (w : ℕ → Bool)
    (n : ℕ) : 0 < trials p hp (PiNat.cylinder w n) := by
  rw [trials_cyl, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  split_ifs
  · exact_mod_cast hp0.ne'
  · exact_mod_cast (tsub_pos_of_lt hp1).ne'

/-- `Statement:` if `0 < p < 1`, `trials p hp` gives every nonempty open set positive mass. -/
theorem trials_isOpenPos (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (trials p hp).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨w, hw⟩ := hne
  obtain ⟨_, ⟨x, n, rfl⟩, hwc, hsub⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open hw hU
  exact fun h => (trials_cyl_pos p hp hp0 hp1 x n).ne' (measure_mono_null hsub h)

/-- `Statement:` if `0 < p < 1`, the support of `trials p hp` is all of `ℕ → Bool`. -/
theorem trials_support_univ (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (trials p hp).support = Set.univ := by
  have := trials_isOpenPos p hp hp0 hp1
  exact Measure.support_eq_univ

/-- `Statement:` ⊥ of `ℕ → Bool` is in the support of `trials p hp` iff `p < 1`; both directions,
no lower bound on `p`. -/
theorem bot_mem_support_iff (p : NNReal) (hp : p ≤ 1) :
    (⊥ : ℕ → Bool) ∈ (trials p hp).support ↔ p < 1 := by
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro h
    by_contra hp1
    have hp1 : p = 1 := le_antisymm hp (not_lt.1 hp1)
    have := h (PiNat.cylinder ⊥ 1)
      ((PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ 1).mem_nhds (PiNat.self_mem_cylinder _ _))
    rw [trials_cyl] at this
    simp [hp1] at this
  · intro hp1 U hU
    obtain ⟨_, ⟨x, n, rfl⟩, hb, hsub⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).mem_nhds_iff.1 hU
    rw [← PiNat.mem_cylinder_iff_eq.1 hb] at hsub
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [trials_cyl]
    have hb : ∀ i, (⊥ : ℕ → Bool) i = false := fun _ => rfl
    simp only [hb, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_range]
    exact ENNReal.pow_pos (ENNReal.coe_pos.2 (tsub_pos_of_lt hp1)) n

-- Statement: CONTROL, `p < 1` is needed: under `trials 1`, ⊥ of `ℕ → Bool` is not in the support.
example : (⊥ : ℕ → Bool) ∉ (trials 1 le_rfl).support := by
  rw [bot_mem_support_iff]; exact lt_irrefl 1

-- Statement: CONTROL, `0 < p` is needed: under `trials 0`, ⊥ of `ℕ → Bool` is in the support and
-- the firing tapes are null.
example : (⊥ : ℕ → Bool) ∈ (trials 0 zero_le_one).support ∧
    trials 0 zero_le_one {w | ∃ k, w k = true} = 0 := by
  refine ⟨(bot_mem_support_iff 0 _).2 zero_lt_one, ?_⟩
  have e : {w : ℕ → Bool | ∃ k, w k = true} = ⋃ k, fires k := by ext w; simp [fires]
  rw [e]
  exact measure_iUnion_null fun k => by rw [trials_fires]; simp

/-! ### § II. Null and not random -/

/-- `Statement:` if `0 < p`, `trials p hp`-almost every tape fires somewhere. -/
theorem ae_firesOnce (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ∀ᵐ w ∂(trials p hp), ∃ k, w k = true :=
  (ae_iff_measure_eq isOpen_fires_once.measurableSet.nullMeasurableSet).2
    (by rw [trials_fires_once p hp hp0, measure_univ])

/-- `Statement:` if `0 < p`, `{⊥}` of `ℕ → Bool` is `trials p hp`-null. -/
theorem trials_bot_null (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp {(⊥ : ℕ → Bool)} = 0 := by
  have h := ae_firesOnce p hp hp0
  rw [ae_iff] at h
  refine measure_mono_null (fun w hw => ?_) h
  rw [Set.mem_singleton_iff] at hw
  subst hw
  rintro ⟨k, hk⟩
  simp at hk

-- Statement: CONTROL, the only tape that never fires is ⊥ of `ℕ → Bool`; both directions.
example (w : ℕ → Bool) : (¬ ∃ k, w k = true) ↔ w = ⊥ := by
  constructor
  · intro h; funext k
    cases hk : w k
    · rfl
    · exact absurd ⟨k, hk⟩ h
  · rintro rfl ⟨k, hk⟩
    simp at hk

/-- `Statement:` if `0 < p`, ⊥ of `ℕ → Bool` is not Martin-Löf random for `trials p hp`. -/
theorem bot_not_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ¬ MLRandom (trials p hp) (⊥ : ℕ → Bool) := fun h => by
  have h1 := fires_io_of_avoids p hp hp0 _ (fun _ hU => hU) ⊥
    (zeroBlockTypical_of_MLRandom p hp ⊥ h)
  exact (not_mem_limsup_fires_iff ⊥).2 ⟨0, fun k _ => rfl⟩ h1

/-- `Statement:` the tapes Martin-Löf random for `trials p hp` that fire somewhere. -/
def randFiring (p : NNReal) (hp : p ≤ 1) : Set (ℕ → Bool) :=
  {w | MLRandom (trials p hp) w ∧ ∃ k, w k = true}

/-- `Statement:` if `0 < p < 1`, ⊥ of `ℕ → Bool` is in the closure of `randFiring p hp`. -/
theorem bot_mem_closure_randFiring (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (⊥ : ℕ → Bool) ∈ closure (randFiring p hp) := by
  rw [mem_closure_iff_nhds]
  intro t ht
  have hpos := (Measure.mem_support_iff_forall _).1 ((bot_mem_support_iff p hp).2 hp1) t ht
  have hae : ∀ᵐ w ∂(trials p hp), w ∈ randFiring p hp :=
    (mlRandom_ae (trials p hp)).and (ae_firesOnce p hp hp0)
  rw [ae_iff] at hae
  by_contra hne
  exact hpos.ne' (measure_mono_null (fun w hw hs => hne ⟨w, hw, hs⟩) hae)

/-- `Statement:` if `0 < p < 1`, the Martin-Löf random tapes for `trials p hp` are dense. -/
theorem dense_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    Dense {w | MLRandom (trials p hp) w} := by
  have := trials_isOpenPos p hp hp0 hp1
  rw [dense_iff_inter_open]
  intro U hU hne
  have hpos := hU.measure_pos (trials p hp) hne
  have hae := mlRandom_ae (trials p hp)
  rw [ae_iff] at hae
  by_contra hn
  exact hpos.ne' (measure_mono_null (fun w hw hs => hn ⟨w, hw, hs⟩) hae)

/-! ### § III. The wait, as a value in `ℕ∞` -/

/-- `Statement:` `waitENat ∘ det` tends to ⊤ of `ℕ∞` at ⊥ of `ℕ → Bool`. -/
theorem wait_tendsto_top_at_bot :
    Tendsto (fun w : ℕ → Bool => waitENat (det w)) (𝓝 ⊥) (𝓝 ⊤) := by
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  intro N
  filter_upwards [(PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ (N + 1)).mem_nhds
    (PiNat.self_mem_cylinder _ _)] with w hw
  have h1 : ofNat (N + 1) ≤ det w := (ofNat_le_det_iff w (N + 1)).2 fun k hk => by
    simpa using hw k hk
  have h2 := (natCast_le_waitENat_iff (N + 1) (det w)).2 h1
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) h2

/-- `Statement:` a tape that fires somewhere has `waitENat (det w) ≠ ⊤`. -/
theorem wait_ne_top_of_fires (w : ℕ → Bool) (h : ∃ k, w k = true) : waitENat (det w) ≠ ⊤ := by
  obtain ⟨k, hk⟩ := h
  intro htop
  have := (natCast_le_waitENat_iff (k + 1) (det w)).1 (htop ▸ le_top)
  have := (ofNat_le_det_iff w (k + 1)).1 this k (Nat.lt_succ_self k)
  rw [hk] at this; cases this

/-- `Statement:` `waitENat (det ⊥) = ⊤`, at ⊥ of `ℕ → Bool`. -/
theorem wait_bot : waitENat (det (⊥ : ℕ → Bool)) = ⊤ := by
  rw [det_poles.1]; exact waitENat.map_top

/-- `Statement:` if `0 < p < 1`, a sequence in `randFiring p hp`, each of finite wait, tends to ⊥ of
`ℕ → Bool` with waits tending to ⊤ of `ℕ∞`; ⊥ is null, not random, in the support, of wait ⊤. -/
theorem pole_within_ensemble (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (∃ u : ℕ → (ℕ → Bool), (∀ n, u n ∈ randFiring p hp) ∧ (∀ n, waitENat (det (u n)) ≠ ⊤) ∧
      Tendsto u atTop (𝓝 ⊥) ∧ Tendsto (fun n => waitENat (det (u n))) atTop (𝓝 ⊤)) ∧
    trials p hp {(⊥ : ℕ → Bool)} = 0 ∧ ¬ MLRandom (trials p hp) ⊥ ∧
    (⊥ : ℕ → Bool) ∈ (trials p hp).support ∧ waitENat (det (⊥ : ℕ → Bool)) = ⊤ := by
  have hcl := bot_mem_closure_randFiring p hp hp0 hp1
  rw [mem_closure_iff_nhds] at hcl
  have hex : ∀ n, ∃ w, w ∈ PiNat.cylinder (⊥ : ℕ → Bool) n ∧ w ∈ randFiring p hp := fun n =>
    hcl _ ((PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ n).mem_nhds (PiNat.self_mem_cylinder _ _))
  choose u hu1 hu2 using hex
  have hlim : Tendsto u atTop (𝓝 ⊥) := by
    rw [tendsto_pi_nhds]
    intro m
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with n hn
    exact (hu1 n m hn).symm
  refine ⟨⟨u, hu2, fun n => wait_ne_top_of_fires _ (hu2 n).2, hlim,
    wait_tendsto_top_at_bot.comp hlim⟩, trials_bot_null p hp hp0, bot_not_MLRandom p hp hp0,
    (bot_mem_support_iff p hp).2 hp1, wait_bot⟩

/-! ### § IV. The wait, as a limit in `NInf` and `Computation` -/

/-- `Statement:` along any pointwise approach to ⊥ of `ℕ → Bool`, `det` eventually passes `ofNat N`,
for every `N`. -/
theorem det_ge_of_approach (u : ℕ → ℕ → Bool) (hu : ∀ m, ∃ n0, ∀ n ≥ n0, u n m = false) (N : ℕ) :
    ∃ n0, ∀ n ≥ n0, ofNat N ≤ det (u n) := by
  induction N with
  | zero => exact ⟨0, fun n _ => (ofNat_le_det_iff _ 0).2 fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨b, hb⟩ := hu N
    refine ⟨max a b, fun n hn => (ofNat_le_det_iff _ _).2 fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact (ofNat_le_det_iff _ _).1 (ha n (le_of_max_le_left hn)) k hk
    · exact hb n (le_of_max_le_right hn)

/-- `Statement:` `det`, read in `ℕ → Bool` (the carrier of `NInf`), tends to ⊤ of `NInf` at ⊥. -/
theorem det_tendsto_top_at_bot_limit :
    Tendsto (fun w : ℕ → Bool => (det w).1) (𝓝 ⊥) (𝓝 (⊤ : NInf).1) := by
  rw [tendsto_pi_nhds]; intro m
  apply tendsto_const_nhds.congr'
  filter_upwards [(PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ (m + 1)).mem_nhds
    (PiNat.self_mem_cylinder _ _)] with w hw
  have h1 : ofNat (m + 1) ≤ det w := (ofNat_le_det_iff w (m + 1)).2 fun k hk => by
    simpa using hw k hk
  rw [NInf.le_def] at h1
  exact (h1 m (by simp [ofNat])).symm

/-- `Statement:` `toComp (det ⊥)` does not terminate, and `toComp (det w)` does for a firing `w`. -/
theorem comp_bot_and_firing (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    ¬ (toComp (det (⊥ : ℕ → Bool))).Terminates ∧ (toComp (det w)).Terminates :=
  ⟨fun h => (by obtain ⟨k, hk⟩ := (toComp_det_terminates_iff _).1 h; cases hk),
    (toComp_det_terminates_iff w).2 hw⟩

/-- `Statement:` if `0 < p < 1`, a sequence in `randFiring p hp`, each of terminating computation,
approaches ⊥ of `ℕ → Bool` pointwise, its `det` passing every `ofNat N`; `toComp (det ⊥)` does not
terminate. -/
theorem pole_within_ensemble_limit (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ u : ℕ → (ℕ → Bool), (∀ n, u n ∈ randFiring p hp) ∧
      (∀ n, (toComp (det (u n))).Terminates) ∧ (∀ m, ∃ n0, ∀ n ≥ n0, u n m = false) ∧
      (∀ N, ∃ n0, ∀ n ≥ n0, ofNat N ≤ det (u n)) ∧ ¬ (toComp (det (⊥ : ℕ → Bool))).Terminates := by
  have hcl := bot_mem_closure_randFiring p hp hp0 hp1
  rw [mem_closure_iff_nhds] at hcl
  have hex : ∀ n, ∃ w, w ∈ PiNat.cylinder (⊥ : ℕ → Bool) n ∧ w ∈ randFiring p hp := fun n =>
    hcl _ ((PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ n).mem_nhds (PiNat.self_mem_cylinder _ _))
  choose u hu1 hu2 using hex
  have hu : ∀ m, ∃ n0, ∀ n ≥ n0, u n m = false := fun m => ⟨m + 1, fun n hn => hu1 n m (by omega)⟩
  exact ⟨u, hu2, fun n => (comp_bot_and_firing _ (hu2 n).2).2, hu, det_ge_of_approach u hu,
    (comp_bot_and_firing ⊤ ⟨0, rfl⟩).1⟩

/-! ### § V. Shift invariance -/

/-- `Statement:` the subtape of `w` after `k`. -/
def shiftTape (k : ℕ) (w : ℕ → Bool) : ℕ → Bool := fun n => w (k + n)

/-- `Statement:` `shiftTape k` is measurable. -/
theorem measurable_shiftTape (k : ℕ) : Measurable (shiftTape k) :=
  measurable_pi_iff.2 fun n => measurable_pi_apply (k + n)

/-- `Statement:` `trials p hp` pushed forward along `shiftTape k` is `trials p hp`. -/
theorem trials_map_shift (p : NNReal) (hp : p ≤ 1) (k : ℕ) :
    (trials p hp).map (shiftTape k) = trials p hp := by
  apply Measure.eq_infinitePi
  intro s t ht
  have hpre : shiftTape k ⁻¹' (↑s : Set ℕ).pi t =
      (↑(s.image (k + ·)) : Set ℕ).pi (fun j => t (j - k)) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro h j ⟨i, hi, rfl⟩
      have e : k + i - k = i := by omega
      rw [e]; exact h i hi
    · intro h i hi
      have := h (k + i) ⟨i, hi, rfl⟩
      have e : k + i - k = i := by omega
      rw [e] at this; exact this
  rw [Measure.map_apply (measurable_shiftTape k)
      (MeasurableSet.pi s.countable_toSet fun i _ => ht i), hpre,
    trials, Measure.infinitePi_pi _ (fun j _ => ht _),
    Finset.prod_image (fun a _ b _ h => by simpa using h)]
  refine Finset.prod_congr rfl fun x _ => ?_
  show (PMF.bernoulli p hp).toMeasure (t (k + x - k)) = (PMF.bernoulli p hp).toMeasure (t x)
  rw [Nat.add_sub_cancel_left]

/-- `Statement:` if `0 < p`, the tapes silent from `k` on are `trials p hp`-null. -/
theorem trials_localFloor_null (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (k : ℕ) :
    trials p hp (shiftTape k ⁻¹' {(⊥ : ℕ → Bool)}) = 0 := by
  rw [← Measure.map_apply (measurable_shiftTape k) (measurableSet_singleton _),
    trials_map_shift, trials_bot_null p hp hp0]

/-! ### § VI. The `p = 0` end: the mass of `{⊥}` jumps, every cylinder's mass does not -/

/-- `Statement:` `trials 0 hp` is the point mass at ⊥ of `ℕ → Bool`. -/
theorem trials_zero_eq_dirac (hp : (0 : NNReal) ≤ 1) :
    trials 0 hp = Measure.dirac (⊥ : ℕ → Bool) := by
  have hb : PMF.bernoulli (0 : NNReal) hp = PMF.pure false := by
    ext b; cases b <;> simp [PMF.bernoulli_apply, PMF.pure_apply]
  rw [trials, hb, PMF.toMeasure_pure, Measure.infinitePi_dirac]; rfl

/-- `Statement:` `trials 1 hp` is the point mass at ⊤ of `ℕ → Bool`; the named form of the
`example` after `interior_of_MLRandom` in `ZeroParadox/Information/TwoRequirements.lean`. -/
theorem trials_one_eq_dirac (hp : (1 : NNReal) ≤ 1) :
    trials 1 hp = Measure.dirac (⊤ : ℕ → Bool) := by
  have hb : PMF.bernoulli (1 : NNReal) hp = PMF.pure true := by
    ext b; cases b <;> simp [PMF.bernoulli_apply, PMF.pure_apply]
  rw [trials, hb, PMF.toMeasure_pure, Measure.infinitePi_dirac]; rfl

/-- `Statement:` `{⊥}` of `ℕ → Bool` has `trials 0 hp` mass one. -/
theorem trials_zero_bot (hp : (0 : NNReal) ≤ 1) : trials 0 hp {(⊥ : ℕ → Bool)} = 1 := by
  rw [trials_zero_eq_dirac]; simp

/-- `Statement:` the support of the point mass at a tape `x` is `{x}`. -/
theorem support_dirac_tape (x : ℕ → Bool) : (Measure.dirac x).support = {x} := by
  ext y
  rw [Measure.mem_support_iff_forall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    have hU : ({x}ᶜ : Set (ℕ → Bool)) ∈ 𝓝 y := isOpen_compl_singleton.mem_nhds hne
    have := h _ hU
    simp at this
  · rintro rfl U hU
    rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]; exact zero_lt_one

/-- `Statement:` the support of `trials 0 hp` is `{⊥}` of `ℕ → Bool`. -/
theorem trials_zero_support (hp : (0 : NNReal) ≤ 1) :
    (trials 0 hp).support = {(⊥ : ℕ → Bool)} := by
  rw [trials_zero_eq_dirac, support_dirac_tape]

/-- `Statement:` the support of `trials 1 hp` is `{⊤}` of `ℕ → Bool`. -/
theorem trials_one_support (hp : (1 : NNReal) ≤ 1) :
    (trials 1 hp).support = {(⊤ : ℕ → Bool)} := by
  rw [trials_one_eq_dirac, support_dirac_tape]

/-- `Statement:` `{⊥}` of `ℕ → Bool` has mass one at `p = 0` and mass zero at every `p > 0`. -/
theorem trials_bot_mass_jump :
    (∀ hp : (0 : NNReal) ≤ 1, trials 0 hp {(⊥ : ℕ → Bool)} = 1) ∧
    (∀ (p : NNReal) (hp : p ≤ 1), 0 < p → trials p hp {(⊥ : ℕ → Bool)} = 0) :=
  ⟨trials_zero_bot, fun p hp hp0 => trials_bot_null p hp hp0⟩

/-- `Statement:` the mass of `{⊥}` of `ℕ → Bool`, total on `NNReal` by clamping `p` to `[0, 1]`. -/
noncomputable def botMass (p : NNReal) : ENNReal :=
  trials (min p 1) (min_le_right _ _) {(⊥ : ℕ → Bool)}

/-- `Statement:` `botMass 0 = 1`. -/
theorem botMass_zero : botMass 0 = 1 := by
  unfold botMass
  have e : min (0 : NNReal) 1 = 0 := min_eq_left zero_le_one
  simp only [e]
  exact trials_zero_bot _

/-- `Statement:` `botMass p = 0` for `0 < p`. -/
theorem botMass_pos {p : NNReal} (hp0 : 0 < p) : botMass p = 0 :=
  trials_bot_null _ _ (lt_min hp0 zero_lt_one)

/-- `Statement:` `botMass` tends to 0 from the right of `p = 0`, and `botMass 0 = 1`. -/
theorem botMass_tendsto_right :
    Tendsto botMass (𝓝[>] 0) (𝓝 0) ∧ botMass 0 = 1 := by
  refine ⟨tendsto_const_nhds.congr' ?_, botMass_zero⟩
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (botMass_pos hp).symm

/-- `Statement:` `botMass` is not continuous at `p = 0`. -/
theorem botMass_not_continuousAt_zero : ¬ ContinuousAt botMass 0 := by
  intro hc
  have hcl : (0 : NNReal) ∈ closure (Set.Ioi 0) := by
    rw [closure_Ioi' ⟨1, zero_lt_one⟩]; exact Set.mem_Ici.2 le_rfl
  have h := mem_closure_image hc hcl
  have himg : botMass '' Set.Ioi 0 ⊆ {0} := by
    rintro _ ⟨p, hp, rfl⟩; exact botMass_pos hp
  have := closure_mono himg h
  rw [closure_singleton, botMass_zero] at this
  simp at this

/-- `Statement:` the support of `trials p hp` is `{⊥}` at `p = 0`, all of `ℕ → Bool` for
`0 < p < 1`, and `{⊤}` at `p = 1`. -/
theorem bot_support_three :
    (∀ hp : (0 : NNReal) ≤ 1, (trials 0 hp).support = {(⊥ : ℕ → Bool)}) ∧
    (∀ (p : NNReal) (hp : p ≤ 1), 0 < p → p < 1 → (trials p hp).support = Set.univ) ∧
    (∀ hp : (1 : NNReal) ≤ 1, (trials 1 hp).support = {(⊤ : ℕ → Bool)}) :=
  ⟨trials_zero_support, fun p hp h0 h1 => trials_support_univ p hp h0 h1, trials_one_support⟩

/-- `Statement:` CONTROL, at `p = 1` `{⊥}` of `ℕ → Bool` is null and ⊥ is outside the support. -/
theorem p_one_control (hp : (1 : NNReal) ≤ 1) :
    trials 1 hp {(⊥ : ℕ → Bool)} = 0 ∧ (⊥ : ℕ → Bool) ∉ (trials 1 hp).support :=
  ⟨trials_bot_null 1 hp zero_lt_one, by rw [bot_mem_support_iff]; exact lt_irrefl 1⟩

/-- `Statement:` ⊥ of `ℕ → Bool` is in the support of the clamped `trials` iff `p < 1`; both
directions. -/
theorem bot_mem_support_clamped (p : NNReal) :
    (⊥ : ℕ → Bool) ∈ (trials (min p 1) (min_le_right _ _)).support ↔ p < 1 := by
  rw [bot_mem_support_iff]
  constructor
  · intro h; by_contra h'; push Not at h'; rw [min_eq_right h'] at h; exact lt_irrefl _ h
  · intro h; rwa [min_eq_left h.le]

/-- `Statement:` the clamped `trials` mass of the length-`n` cylinder at ⊥ of `ℕ → Bool`. -/
noncomputable def cylMass (n : ℕ) (p : NNReal) : ENNReal :=
  trials (min p 1) (min_le_right _ _) (PiNat.cylinder (⊥ : ℕ → Bool) n)

/-- `Statement:` `cylMass n p = (1 - min p 1) ^ n`. -/
theorem cylMass_eq (n : ℕ) (p : NNReal) :
    cylMass n p = (((1 - min p 1 : NNReal)) : ENNReal) ^ n := by
  unfold cylMass
  rw [trials_cyl]
  have hb : ∀ i, (⊥ : ℕ → Bool) i = false := fun _ => rfl
  simp only [hb, Bool.false_eq_true, ite_false, Finset.prod_const, Finset.card_range]

/-- `Statement:` `cylMass n` is continuous in `p`. -/
theorem cylMass_continuous (n : ℕ) : Continuous (cylMass n) := by
  have : cylMass n = fun p => (((1 - min p 1 : NNReal)) : ENNReal) ^ n := funext (cylMass_eq n)
  rw [this]
  exact (ENNReal.continuous_pow n).comp
    (ENNReal.continuous_coe.comp (continuous_const.sub (continuous_id.min continuous_const)))

/-- `Statement:` `botMass p` is the infimum over `n` of `cylMass n p`. `Reading:` each term is
continuous in `p` (`cylMass_continuous`) and the infimum is not (`botMass_not_continuousAt_zero`). -/
theorem botMass_eq_iInf (p : NNReal) : botMass p = ⨅ n, cylMass n p := by
  unfold botMass cylMass
  have e : {(⊥ : ℕ → Bool)} = ⋂ n, PiNat.cylinder (⊥ : ℕ → Bool) n := by
    ext y; simp only [Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · rintro rfl n; exact PiNat.self_mem_cylinder _ _
    · intro h; funext k; exact h (k + 1) k (Nat.lt_succ_self k)
  rw [e]
  refine Antitone.measure_iInter (fun a b hab y hy i hi => hy i (lt_of_lt_of_le hi hab))
    (fun n => (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) ⊥ n).measurableSet.nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩

-- `Statement:` `botMass` is upper semicontinuous: an infimum of continuous functions is upper
-- semicontinuous and need not be continuous (Mathlib `upperSemicontinuous_iInf`).
example : UpperSemicontinuous botMass := by
  rw [show botMass = fun p => ⨅ n, cylMass n p from funext botMass_eq_iInf]
  exact upperSemicontinuous_iInf fun n => (cylMass_continuous n).upperSemicontinuous

/-! ### § VII. The limit with explicit witnesses: no measure in the statement -/

/-- `Statement:` the tape firing exactly at stage `n`. -/
def fireAt (n : ℕ) : ℕ → Bool := fun k => decide (k = n)

/-- `Statement:` `det (fireAt n) = ofNat n`, each `fireAt n` fires and its run halts, the family
approaches ⊥ of `ℕ → Bool` pointwise with `det` passing every `ofNat N`, and ⊥'s run does not halt. -/
theorem pole_limit_explicit :
    (∀ n, det (fireAt n) = ofNat n) ∧ (∀ n, ∃ k, fireAt n k = true) ∧
      (∀ n, (toComp (det (fireAt n))).Terminates) ∧
      (∀ m, ∃ n0, ∀ n ≥ n0, fireAt n m = false) ∧
      (∀ N, ∃ n0, ∀ n ≥ n0, ofNat N ≤ det (fireAt n)) ∧
      ¬ (toComp (det (⊥ : ℕ → Bool))).Terminates := by
  have hf : ∀ n, ∃ k, fireAt n k = true := fun n => ⟨n, decide_eq_true rfl⟩
  have hu : ∀ m, ∃ n0, ∀ n ≥ n0, fireAt n m = false :=
    fun m => ⟨m + 1, fun n hn => decide_eq_false (Nat.ne_of_lt hn)⟩
  exact ⟨det_fire, hf, fun n => (toComp_det_terminates_iff _).2 (hf n), hu,
    det_ge_of_approach fireAt hu, (comp_bot_and_firing ⊤ ⟨0, rfl⟩).1⟩

/-- `Statement:` `pole_within_ensemble_limit`'s conclusion with `u n ∈ randFiring p hp` weakened to
"`u n` fires somewhere": no `trials`, no `MLRandom` in the statement. -/
theorem stmtLimitNoRand_holds :
    ∃ u : ℕ → (ℕ → Bool), (∀ n, ∃ k, u n k = true) ∧
      (∀ n, (toComp (det (u n))).Terminates) ∧ (∀ m, ∃ n0, ∀ n ≥ n0, u n m = false) ∧
      (∀ N, ∃ n0, ∀ n ≥ n0, ofNat N ≤ det (u n)) ∧ ¬ (toComp (det (⊥ : ℕ → Bool))).Terminates :=
  let h := pole_limit_explicit
  ⟨fireAt, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- `Statement:` CONTROL, for `0 < p`, no `fireAt n` is Martin-Löf random for `trials p hp`: each
is silent from `n + 1` on. -/
theorem fireAt_not_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (n : ℕ) :
    ¬ MLRandom (trials p hp) (fireAt n) := fun h => by
  have h1 := fires_io_of_avoids p hp hp0 _ (fun _ hU => hU) (fireAt n)
    (zeroBlockTypical_of_MLRandom p hp _ h)
  refine (not_mem_limsup_fires_iff _).2 ⟨n + 1, fun k hk => ?_⟩ h1
  exact decide_eq_false (by omega)

/-! ### § VIII. A heat-bath rate supplies `0 < p`
`Reading:` this RELOCATES the residual hypothesis `0 < p` of `trials_fires_once` to the modelling
choice "Glauber-type rates at `T > 0`"; it does not remove it. Any rate with `p ∈ (0, 1]` at
`T > 0` does the same job, so the sigmoid has no special role. The form is the heat-bath (Glauber-type)
occupation of one site (Levin, Peres and Wilmer, *Markov Chains and Mixing Times*, 2nd ed., § 3.3.5,
eq. (3.11), p. 45, with `ΔE = 2S`); after R. J. Glauber, J. Math. Phys. 4, 294 (1963). -/

/-- `Statement:` `Real.sigmoid (-(ΔE / T))`: excitation across a gap `ΔE` at temperature `T`. -/
noncomputable def glauberExcite (ΔE T : ℝ) : ℝ := Real.sigmoid (-(ΔE / T))

/-- `Statement:` `glauberExcite ΔE T` as an `NNReal`. -/
noncomputable def glauberExciteNN (ΔE T : ℝ) : NNReal :=
  ⟨glauberExcite ΔE T, (Real.sigmoid_pos _).le⟩

/-- `Statement:` `glauberExciteNN ΔE T ≤ 1`. -/
theorem glauberExciteNN_le_one (ΔE T : ℝ) : glauberExciteNN ΔE T ≤ 1 :=
  show glauberExcite ΔE T ≤ 1 from (Real.sigmoid_lt_one _).le

/-- `Statement:` `0 < glauberExciteNN ΔE T`. -/
theorem glauberExciteNN_pos (ΔE T : ℝ) : 0 < glauberExciteNN ΔE T :=
  show 0 < glauberExcite ΔE T from Real.sigmoid_pos _

/-- `Statement:` at every `ΔE` and `T`, the tapes that fire somewhere have
    `trials (glauberExciteNN ΔE T)` measure one. -/
theorem glauber_fires_once (ΔE T : ℝ) :
    trials (glauberExciteNN ΔE T) (glauberExciteNN_le_one ΔE T) {w | ∃ k, w k = true} = 1 :=
  trials_fires_once _ _ (glauberExciteNN_pos ΔE T)

/-- `Statement:` at every `ΔE` and `T`, `trials (glauberExciteNN ΔE T)`-almost every tape fires. -/
theorem glauber_ae_fires (ΔE T : ℝ) :
    ∀ᵐ w ∂(trials (glauberExciteNN ΔE T) (glauberExciteNN_le_one ΔE T)), ∃ k, w k = true :=
  ae_firesOnce _ _ (glauberExciteNN_pos ΔE T)

/-- `Statement:` at every `ΔE` and `T`, `botMass (glauberExciteNN ΔE T) = 0`. -/
theorem glauber_botMass (ΔE T : ℝ) : botMass (glauberExciteNN ΔE T) = 0 :=
  botMass_pos (glauberExciteNN_pos ΔE T)

/-- `Statement:` if `0 < ΔE`, `glauberExcite ΔE T → 0` as `T → 0⁺`. -/
theorem glauberExcite_tendsto_zero {ΔE : ℝ} (hΔ : 0 < ΔE) :
    Tendsto (glauberExcite ΔE) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => ΔE / T) (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atTop hΔ tendsto_inv_nhdsGT_zero |>.congr (fun T => by ring)
  exact Real.tendsto_sigmoid_atBot.comp (tendsto_neg_atTop_atBot.comp h1)

/-- `Statement:` if `0 < ΔE`: `botMass (glauberExciteNN ΔE T) = 0` at every `T`,
    `glauberExcite ΔE T → 0` as `T → 0⁺`, and `botMass 0 = 1`. -/
theorem glauber_jump {ΔE : ℝ} (hΔ : 0 < ΔE) :
    (∀ T, botMass (glauberExciteNN ΔE T) = 0) ∧ Tendsto (glauberExcite ΔE) (𝓝[>] 0) (𝓝 0)
      ∧ botMass 0 = 1 :=
  ⟨glauber_botMass ΔE, glauberExcite_tendsto_zero hΔ, botMass_zero⟩

-- Statement: CONTROL, `glauberExcite ΔE 0 = 1 / 2`: Lean's `x / 0 = 0`, so `T = 0` is reached
-- only as the limit `T → 0⁺` of `glauberExcite_tendsto_zero`, never by substitution.
example (ΔE : ℝ) : glauberExcite ΔE 0 = 1 / 2 := by
  simp [glauberExcite, Real.sigmoid]
  norm_num

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms cyl_eq_pi
#print axioms trials_cyl
#print axioms trials_cyl_pos
#print axioms trials_isOpenPos
#print axioms trials_support_univ
#print axioms bot_mem_support_iff
#print axioms ae_firesOnce
#print axioms trials_bot_null
#print axioms bot_not_MLRandom
#print axioms randFiring
#print axioms bot_mem_closure_randFiring
#print axioms dense_MLRandom
#print axioms wait_tendsto_top_at_bot
#print axioms wait_ne_top_of_fires
#print axioms wait_bot
#print axioms pole_within_ensemble
#print axioms det_ge_of_approach
#print axioms det_tendsto_top_at_bot_limit
#print axioms comp_bot_and_firing
#print axioms pole_within_ensemble_limit
#print axioms shiftTape
#print axioms measurable_shiftTape
#print axioms trials_map_shift
#print axioms trials_localFloor_null
#print axioms trials_zero_eq_dirac
#print axioms trials_one_eq_dirac
#print axioms trials_zero_bot
#print axioms support_dirac_tape
#print axioms trials_zero_support
#print axioms trials_one_support
#print axioms trials_bot_mass_jump
#print axioms botMass
#print axioms botMass_zero
#print axioms botMass_pos
#print axioms botMass_tendsto_right
#print axioms botMass_not_continuousAt_zero
#print axioms bot_support_three
#print axioms p_one_control
#print axioms bot_mem_support_clamped
#print axioms cylMass
#print axioms cylMass_eq
#print axioms cylMass_continuous
#print axioms botMass_eq_iInf
#print axioms fireAt
#print axioms pole_limit_explicit
#print axioms stmtLimitNoRand_holds
#print axioms fireAt_not_MLRandom
#print axioms glauberExcite
#print axioms glauberExciteNN
#print axioms glauberExciteNN_le_one
#print axioms glauberExciteNN_pos
#print axioms glauber_fires_once
#print axioms glauber_ae_fires
#print axioms glauber_botMass
#print axioms glauberExcite_tendsto_zero
#print axioms glauber_jump
end PurityCheck
