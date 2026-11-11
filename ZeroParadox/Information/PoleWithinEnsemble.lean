-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): ⊥ of `ℕ → Bool`, the never-firing tape, inside the support of `trials p hp` and in the closure of its Martin-Löf random firing tapes, with the waiting time read as a limit and as a value. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.TapeHalting
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Instances.ENat
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
For `0 < p < 1`, ⊥ of `ℕ → Bool` is `trials p hp`-null, in its support, and a limit of random firing
tapes whose waits diverge (`pole_within_ensemble` in `ℕ∞`; `pole_within_ensemble_limit` in `NInf`).
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
end PurityCheck
