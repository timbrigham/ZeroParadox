-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): connectedness and the first step on a linear order with its order topology. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Reals.OrderedField
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.RatLemmas
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.Irrational

set_option maxHeartbeats 400000

/-!
# Connectedness and the first step on a linear order with its order topology

A cover `a ⋖ b` (a first step, `HasFirstStep`) makes `Set.Iio b` and `Set.Ioi a` two disjoint open
sets covering the space, so a preconnected linear order has no first step anywhere. The converse
needs conditional completeness, and ℚ is the control. Standard form: a linearly ordered space is
connected iff it is a linear continuum, densely ordered and Dedekind complete (Steen–Seebach,
*Counterexamples in Topology*); connectedness also forces completeness, which this file does not use.
Also: for closed, bounded, nonempty `S ⊆ ℝ`, span minus material is 0 iff `S` is a closed interval (`spanGap_eq_zero_iff_interval`).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

/-- `Statement:` in a linear order carrying its order topology, preconnected, no point has a first
    step. Mathlib's `denselyOrdered_of_preconnectedSpace` is the same fact in `DenselyOrdered` form
    (the `example` below); this proof keeps the footprint free of `Classical.choice`. -/
theorem no_firstStep_of_preconnected {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [PreconnectedSpace α] (bot : α) : ¬ HasFirstStep bot := by
  rintro ⟨b, h⟩
  obtain ⟨c, hcb, hac⟩ := nonempty_inter (isOpen_Iio' b) (isOpen_Ioi' bot)
    (Set.Iio_union_Ioi_of_lt h.1) ⟨bot, h.1⟩ ⟨b, h.1⟩
  exact h.2 hac hcb

-- `Statement:` Mathlib's route, through `axb1_fails_everywhere_iff_dense`, reaches the same conclusion.
example {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [PreconnectedSpace α] :
    ∀ bot : α, ¬ HasFirstStep bot :=
  axb1_fails_everywhere_iff_dense.mp denselyOrdered_of_preconnectedSpace

/-- `Statement:` the contrapositive: a first step at any point makes a linear order with its order
    topology not preconnected. -/
theorem not_preconnected_of_firstStep {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {bot : α} (h : HasFirstStep bot) : ¬ PreconnectedSpace α :=
  fun _ => no_firstStep_of_preconnected bot h

/-- `Statement:` on a conditionally complete linear order with its order topology, preconnected iff
    no point has a first step. The backward direction is Mathlib's `ordered_connected_space`. -/
theorem preconnected_iff_no_firstStep {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] :
    PreconnectedSpace α ↔ ∀ bot : α, ¬ HasFirstStep bot :=
  ⟨fun _ => no_firstStep_of_preconnected, fun h =>
    haveI : DenselyOrdered α := axb1_fails_everywhere_iff_dense.mpr h
    ordered_connected_space⟩

-- `Statement:` ℝ is preconnected, so no real has a first step; at `0` this is
-- `axb1_fails_in_ordered_field`, there by density.
example : ∀ x : ℝ, ¬ HasFirstStep x := no_firstStep_of_preconnected

-- `Statement:` control, completeness carries the backward direction: ℚ has no first step anywhere
-- and is not preconnected (Mathlib's `TotallyDisconnectedSpace ℚ`).
example : (∀ q : ℚ, ¬ HasFirstStep q) ∧ ¬ PreconnectedSpace ℚ :=
  ⟨axb1_fails_everywhere_iff_dense.mp inferInstance, fun _ =>
    not_subsingleton ℚ subsingleton_of_preconnected_totallyDisconnected⟩

-- `Statement:` control, the discrete side: every integer has a first step, and `0 : Fin 2` has one;
-- neither carrier is preconnected in its order topology.
example : (∀ n : ℤ, HasFirstStep n) ∧ ¬ PreconnectedSpace ℤ :=
  ⟨fun n => ⟨n + 1, Int.lt_succ n, fun _ h1 h2 => by omega⟩,
   not_preconnected_of_firstStep (bot := (0 : ℤ)) ⟨1, by decide, fun _ h1 h2 => by omega⟩⟩
example : HasFirstStep (0 : Fin 2) ∧ ¬ PreconnectedSpace (Fin 2) :=
  ⟨⟨1, by decide, fun _ h1 h2 => by omega⟩,
   not_preconnected_of_firstStep (bot := (0 : Fin 2)) ⟨1, by decide, fun _ h1 h2 => by omega⟩⟩

-- `Statement:` control, a first step at one point leaves the rest of the order dense: on
-- `{0} ∪ [1, 2] ⊆ ℝ`, `0` has a first step and `1` has none; with its order topology the carrier
-- is not preconnected.
example : letI : TopologicalSpace ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := Preorder.topology _
    HasFirstStep (⟨0, Or.inl rfl⟩ : ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ)) ∧
    ¬ HasFirstStep (⟨1, Or.inr ⟨le_rfl, by norm_num⟩⟩ : ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ)) ∧
    ¬ PreconnectedSpace ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := by
  letI : TopologicalSpace ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := Preorder.topology _
  haveI : OrderTopology ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ) := ⟨rfl⟩
  have h0 : HasFirstStep (⟨0, Or.inl rfl⟩ : ({0} ∪ Set.Icc (1 : ℝ) 2 : Set ℝ)) := by
    refine ⟨⟨1, Or.inr ⟨le_rfl, by norm_num⟩⟩, show (0 : ℝ) < 1 by norm_num, ?_⟩
    rintro ⟨c, hc | hc⟩ h1 h2
    · rw [Set.mem_singleton_iff] at hc; subst hc; exact lt_irrefl _ h1
    · exact absurd (show c < 1 from h2) (not_lt.2 hc.1)
  refine ⟨h0, ?_, not_preconnected_of_firstStep h0⟩
  rintro ⟨⟨a, ha | ha⟩, h1, h2⟩
  · rw [Set.mem_singleton_iff] at ha; subst ha
    exact absurd (show (1 : ℝ) < 0 from h1) (by norm_num)
  · have h1' : (1 : ℝ) < a := h1
    exact h2 (c := ⟨(1 + a) / 2, Or.inr ⟨by linarith, by linarith [ha.2]⟩⟩)
      (show (1 : ℝ) < (1 + a) / 2 by linarith) (show (1 + a) / 2 < a by linarith)

-- `Reading:` the implication runs from topology to order on every linear order with its order
-- topology, and from order to topology only under completeness. On one such carrier a continuous
-- passage (preconnected) and the snap (a first step) exclude each other. This supplies no first step
-- anywhere: AX-B1 stays a precondition (chart choice).
-- `Reading:` CARRIER. ℚ₂ carries no linear order (`LT ℚ_[2]` does not synthesize, the `#check_failure` in
-- `ZeroParadox/BottomCannotBe.lean` § ROLE), so these hypotheses are not met there; its no-path
-- fact is total disconnectedness (`disconnectedness_forbids_path`,
-- `ZeroParadox/Valuation/BranchingSnapChain.lean`), a different route.

/-! ### Span minus material on the line -/

section SpanGap

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- `Statement:` span minus material, `ediam S - volume S`; never truncates (`Real.volume_le_diam`). -/
noncomputable def spanGap (S : Set ℝ) : ℝ≥0∞ := ediam S - volume S

/-- `Statement:` material plus span-minus-material is span. -/
theorem material_add_spanGap (S : Set ℝ) : volume S + spanGap S = ediam S :=
  add_tsub_cancel_of_le (Real.volume_le_diam S)

/-- `Statement:` `spanGap S = 0` iff span equals material. -/
theorem spanGap_eq_zero_iff (S : Set ℝ) : spanGap S = 0 ↔ ediam S = volume S := by
  unfold spanGap
  rw [tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm h (Real.volume_le_diam S), fun h => h.le⟩

/-- `Statement:` a bounded order-connected `S ⊆ ℝ` has `spanGap S = 0`. -/
theorem spanGap_eq_zero_of_ordConnected {S : Set ℝ} (hS : S.OrdConnected)
    (hb : Bornology.IsBounded S) : spanGap S = 0 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [spanGap]
  rw [spanGap_eq_zero_iff, Real.ediam_eq hb]
  apply le_antisymm
  · rw [← Real.volume_Ioo]
    apply measure_mono
    rintro x ⟨h1, h2⟩
    obtain ⟨a, ha, hax⟩ := exists_lt_of_csInf_lt hne h1
    obtain ⟨b, hb', hxb⟩ := exists_lt_of_lt_csSup hne h2
    exact hS.out ha hb' ⟨hax.le, hxb.le⟩
  · rw [← Real.volume_Icc]; exact measure_mono hb.subset_Icc_sInf_sSup

/-- `Statement:` a closed, bounded, nonempty `S ⊆ ℝ` with `spanGap S = 0` is `Icc (sInf S) (sSup S)`;
    a missing point leaves a nonempty open set of positive measure (`IsOpen.measure_pos`). -/
theorem eq_Icc_of_spanGap_eq_zero {S : Set ℝ} (hc : IsClosed S) (hb : Bornology.IsBounded S)
    (hne : S.Nonempty) (h0 : spanGap S = 0) : S = Icc (sInf S) (sSup S) := by
  have hsub : S ⊆ Icc (sInf S) (sSup S) := hb.subset_Icc_sInf_sSup
  refine hsub.antisymm fun x hx => ?_
  by_contra hxS
  have hmin : sInf S ∈ S := hc.csInf_mem hne hb.bddBelow
  have hmax : sSup S ∈ S := hc.csSup_mem hne hb.bddAbove
  have hx' : x ∈ Ioo (sInf S) (sSup S) :=
    ⟨lt_of_le_of_ne hx.1 (fun h => hxS (h ▸ hmin)),
      lt_of_le_of_ne hx.2 (fun h => hxS (h ▸ hmax))⟩
  have hU : IsOpen (Ioo (sInf S) (sSup S) \ S) := isOpen_Ioo.sdiff hc
  have hpos : 0 < volume (Ioo (sInf S) (sSup S) \ S) := hU.measure_pos volume ⟨x, hx', hxS⟩
  have hvol : volume S = volume (Icc (sInf S) (sSup S)) := by
    rw [Real.volume_Icc, ← Real.ediam_eq hb]; exact ((spanGap_eq_zero_iff S).1 h0).symm
  have hfin : volume S ≠ ∞ := by rw [hvol, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hdiff : volume (Icc (sInf S) (sSup S) \ S) = 0 := by
    rw [measure_sdiff hsub hc.measurableSet.nullMeasurableSet hfin, hvol, tsub_self]
  have hle := measure_mono (μ := volume)
    (sdiff_subset_sdiff_left Ioo_subset_Icc_self :
      Ioo (sInf S) (sSup S) \ S ⊆ Icc (sInf S) (sSup S) \ S)
  rw [hdiff] at hle
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

/-- `Statement:` for `S ⊆ ℝ` closed, bounded and nonempty, `spanGap S = 0 ↔ S = Icc (sInf S) (sSup S)`. -/
theorem spanGap_eq_zero_iff_interval {S : Set ℝ} (hc : IsClosed S) (hb : Bornology.IsBounded S)
    (hne : S.Nonempty) : spanGap S = 0 ↔ S = Icc (sInf S) (sSup S) :=
  ⟨eq_Icc_of_spanGap_eq_zero hc hb hne, fun h => by
    rw [h]; exact spanGap_eq_zero_of_ordConnected ordConnected_Icc (isBounded_Icc _ _)⟩

/-- `Statement:` `spanGap (Icc a b) = 0`. -/
theorem spanGap_Icc {a b : ℝ} : spanGap (Icc a b) = 0 :=
  spanGap_eq_zero_of_ordConnected ordConnected_Icc (isBounded_Icc _ _)

/-- `Statement:` CONTROL, `spanGap {0, 1} = 1`: one gap, of length 1. -/
theorem spanGap_pair : spanGap ({0, 1} : Set ℝ) = 1 := by
  have hv : volume ({0, 1} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
  rw [spanGap, hv, tsub_zero, ediam_pair, edist_dist, Real.dist_eq]
  norm_num

/-- `Statement:` CONTROL, `IsClosed` is load-bearing in `spanGap_eq_zero_iff_interval`: the
    irrationals of `[0, 1]` have `spanGap` 0 and are not order-connected. -/
theorem irr_unit_spanGap_zero_not_ordConnected :
    spanGap (Icc (0 : ℝ) 1 ∩ {x | Irrational x}) = 0 ∧
      ¬ (Icc (0 : ℝ) 1 ∩ {x | Irrational x}).OrdConnected := by
  set S := Icc (0 : ℝ) 1 ∩ {x | Irrational x} with hSdef
  have hSeq : S = Icc (0 : ℝ) 1 \ range ((↑) : ℚ → ℝ) := by
    ext x; simp [hSdef, Irrational]
  have hvol : volume S = 1 := by
    rw [hSeq, measure_sdiff_null ((Set.countable_range _).measure_zero volume), Real.volume_Icc]; simp
  refine ⟨?_, ?_⟩
  · rw [spanGap_eq_zero_iff, hvol]
    apply le_antisymm
    · calc ediam S ≤ ediam (Icc (0 : ℝ) 1) := ediam_mono inter_subset_left
        _ = 1 := by simp
    · rw [← hvol]; exact Real.volume_le_diam S
  · intro hS
    have h2 : Irrational (√2) := irrational_sqrt_two
    have hs1 : 1 < √2 := by
      rw [Real.lt_sqrt (by norm_num)]; norm_num
    have hs2 : √2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have ha : √2 / (4 : ℕ) ∈ S :=
      ⟨⟨by positivity, by push_cast; linarith⟩, h2.div_natCast (by norm_num)⟩
    have hb : √2 / (2 : ℕ) ∈ S :=
      ⟨⟨by positivity, by push_cast; linarith⟩, h2.div_natCast (by norm_num)⟩
    have hmid : (1 / 2 : ℝ) ∈ S := hS.out ha hb ⟨by push_cast; linarith, by push_cast; linarith⟩
    exact hmid.2 ⟨1 / 2, by push_cast; ring⟩

/-- `Statement:` `1 ∈ preCantorSet n` for every `n`. -/
theorem one_mem_preCantorSet (n : ℕ) : (1 : ℝ) ∈ preCantorSet n := by
  induction n with
  | zero => simp
  | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩

/-- `Statement:` `volume (preCantorSet n) ≤ (2/3)^n`. -/
theorem volume_preCantorSet_le (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal (2 / 3) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e1 : (fun x : ℝ => x / 3) '' preCantorSet n
        = AffineMap.homothety (0 : ℝ) (1 / 3 : ℝ) '' preCantorSet n := by
      congr 1; funext x; simp [AffineMap.homothety_apply]; ring
    have e2 : (fun x : ℝ => (2 + x) / 3) '' preCantorSet n
        = AffineMap.homothety (1 : ℝ) (1 / 3 : ℝ) '' preCantorSet n := by
      congr 1; funext x; simp [AffineMap.homothety_apply]; ring
    rw [preCantorSet_succ]
    calc volume ((· / 3) '' preCantorSet n ∪ (fun x ↦ (2 + x) / 3) '' preCantorSet n)
        ≤ volume ((fun x : ℝ => x / 3) '' preCantorSet n)
          + volume ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) := measure_union_le _ _
      _ = ENNReal.ofReal (1 / 3) * volume (preCantorSet n)
          + ENNReal.ofReal (1 / 3) * volume (preCantorSet n) := by
          rw [e1, e2, Measure.addHaar_image_homothety, Measure.addHaar_image_homothety]
          simp [Module.finrank_self]
      _ = ENNReal.ofReal (2 / 3) * volume (preCantorSet n) := by
          rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
      _ ≤ ENNReal.ofReal (2 / 3) * ENNReal.ofReal (2 / 3) ^ n := by gcongr
      _ = ENNReal.ofReal (2 / 3) ^ (n + 1) := by rw [pow_succ, mul_comm]

/-- `Statement:` the Cantor set (Mathlib's `cantorSet`) has Lebesgue measure 0. Not located in
    Mathlib as of 2026-11-27: `cantorSet` occurs only in `Topology/Instances/CantorSet.lean` and
    `Topology/MetricSpace/HausdorffAlexandroff.lean`, neither stating a measure. Outside Mathlib:
    `TauCeti.volume_cantorSet` (TauCetiProject/TauCeti@1a8f1810b514b1b0b7faad7bae9aada9bab9d23a,
    `TauCeti/MeasureTheory/Measure/Lebesgue/CantorSet.lean`; source read, type not elaborated). -/
theorem volume_cantorSet : volume cantorSet = 0 := by
  have hlt : ENNReal.ofReal (2 / 3) < 1 := by
    rw [ENNReal.ofReal_lt_one]; norm_num
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  refine le_antisymm (ge_of_tendsto' ht fun n => ?_) bot_le
  exact (measure_mono (Set.iInter_subset _ n)).trans (volume_preCantorSet_le n)

/-- `Statement:` the Cantor set has diameter 1. -/
theorem ediam_cantorSet : ediam cantorSet = 1 := by
  apply le_antisymm
  · calc ediam cantorSet ≤ ediam (Icc (0 : ℝ) 1) := ediam_mono cantorSet_subset_unitInterval
      _ = 1 := by simp
  · have h := edist_le_ediam_of_mem zero_mem_cantorSet
      (Set.mem_iInter.2 one_mem_preCantorSet : (1 : ℝ) ∈ cantorSet)
    rw [edist_dist, Real.dist_eq] at h
    norm_num at h
    exact h

/-- `Statement:` CONTROL, `spanGap cantorSet = 1`: material 0, span 1. -/
theorem spanGap_cantorSet : spanGap cantorSet = 1 := by
  rw [spanGap, volume_cantorSet, ediam_cantorSet, tsub_zero]

end SpanGap

end ZeroParadox

section PurityCheck
#print axioms ZeroParadox.no_firstStep_of_preconnected
#print axioms ZeroParadox.not_preconnected_of_firstStep
#print axioms ZeroParadox.preconnected_iff_no_firstStep
#print axioms ZeroParadox.spanGap
#print axioms ZeroParadox.material_add_spanGap
#print axioms ZeroParadox.spanGap_eq_zero_iff
#print axioms ZeroParadox.spanGap_eq_zero_of_ordConnected
#print axioms ZeroParadox.eq_Icc_of_spanGap_eq_zero
#print axioms ZeroParadox.spanGap_eq_zero_iff_interval
#print axioms ZeroParadox.spanGap_Icc
#print axioms ZeroParadox.spanGap_pair
#print axioms ZeroParadox.irr_unit_spanGap_zero_not_ordConnected
#print axioms ZeroParadox.one_mem_preCantorSet
#print axioms ZeroParadox.volume_preCantorSet_le
#print axioms ZeroParadox.volume_cantorSet
#print axioms ZeroParadox.ediam_cantorSet
#print axioms ZeroParadox.spanGap_cantorSet
-- Mathlib's lemmas cited above: printed, not asserted.
#print axioms denselyOrdered_of_preconnectedSpace
#print axioms ordered_connected_space
end PurityCheck
