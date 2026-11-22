-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the limit retraction (Abate–Bedford) restricted to convergent orbits, for a continuous self-map of a Hausdorff space, as the UP leg of a die `Motion` whose OVER is one step of the map; orbit convergence is exactly finite arrival at a landing or a stage closure, with controls, conjugacy by field inversion (a strict isomorphism on `OnePoint K`; no strict map given by inversion inside `K` when `c ^ n → 0` and `1 < ‖d‖`) and the reverse direction through the ε₀ tower. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Die
import ZeroParadox.DieSameness
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Valuation.BottomInvariant
import ZeroParadox.Valuation.InfinitudeFloor
import ZeroParadox.Order.WellFoundedObstruct
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Ordinal.Epsilon0LeastFP
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Dynamics.OmegaLimit
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.Order.IsNormal
import Mathlib.Tactic

/-!
# The limit retraction as a die motion: convergence is arrival at a landing or a stage closure

Experimental probe, not a finalized layer; results are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

Metric motion sounded familiar, and that concept needed looking into. Approach becoming a landing is quite literally the shape at the heart of this. Everything has been about an asymptote becoming a final fixed value and vice versa, and if we're capturing that shape, we're very much in the right direction.

---

Formal Overview (AI-assisted), citations and prior art: the ride-along `LimitMotion.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology

/-! ## § I. The construction: UP is the limit retraction, OVER is one step -/

section LimitRetraction

universe u

/-- `Statement:` the corpus `omegaLim` (`ZeroParadox/Valuation/BottomInvariant.lean` § IV) is
    Mathlib's `omegaLimit` along `atTop` at a singleton start. -/
theorem lm_omegaLim_eq_omegaLimit {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) :
    omegaLim f x = omegaLimit atTop (fun n y => f^[n] y) {x} := by
  ext q
  rw [mem_omegaLimit_singleton_iff_mapClusterPt, mapClusterPt_iff_frequently]
  simp only [omegaLim, Set.mem_iInter, mem_closure_iff_nhds, Filter.frequently_atTop]
  constructor
  · intro h s hs N
    obtain ⟨_, hy, n, rfl⟩ := h N s hs
    exact ⟨N + n, Nat.le_add_right N n, hy⟩
  · intro h N s hs
    obtain ⟨b, hb, hbs⟩ := h s hs N
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hb
    exact ⟨_, hbs, n, rfl⟩

/-- `Statement:` in a Hausdorff space, an orbit tending to `p` has Mathlib ω-limit set `{p}`. -/
theorem lm_omegaLimit_of_tendsto {X : Type*} [TopologicalSpace X] [T2Space X] (g : X → X) (x p : X)
    (h : Tendsto (fun n => g^[n] x) atTop (𝓝 p)) :
    omegaLimit atTop (fun n y => g^[n] y) {x} = {p} := by
  ext q
  rw [mem_omegaLimit_singleton_iff_mapClusterPt, Set.mem_singleton_iff]
  constructor
  · intro hq
    have hc : ClusterPt q (map (fun n => g^[n] x) atTop) := hq
    have hle : map (fun n => g^[n] x) atTop ≤ 𝓝 p := h
    exact eq_of_nhds_neBot (hc.mono hle)
  · rintro rfl
    exact h.mapClusterPt

/-- `Statement:` in a compact Hausdorff space, Mathlib ω-limit set `{p}` forces the orbit to tend
    to `p`. -/
theorem lm_tendsto_of_omegaLimit {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (g : X → X) (x p : X) (h : omegaLimit atTop (fun n y => g^[n] y) {x} = {p}) :
    Tendsto (fun n => g^[n] x) atTop (𝓝 p) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro q hq
  have : q ∈ omegaLimit atTop (fun n y => g^[n] y) {x} :=
    (mem_omegaLimit_singleton_iff_mapClusterPt _ _ _ _).2 hq
  rw [h] at this
  exact this

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- `Statement:` the limit retraction (Abate–Bedford) restricted to convergent orbits: defined at `x` iff its orbit
    converges (the union of point basins `B({p})`), with value a limit, chosen; the limit is unique on a Hausdorff space, which `limitMotion` assumes. -/
noncomputable def limitRetraction (g : X → X) (x : X) : Part X :=
  ⟨∃ q, Tendsto (fun n => g^[n] x) atTop (𝓝 q), fun h => h.choose⟩

/-- `Statement:` `q` is the value of `limitRetraction g x` iff the orbit of `x` tends to `q`. -/
theorem lm_mem_limitRetraction_iff {g : X → X} {x q : X} :
    q ∈ limitRetraction g x ↔ Tendsto (fun n => g^[n] x) atTop (𝓝 q) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro h
    exact ⟨⟨q, h⟩, tendsto_nhds_unique
      (⟨q, h⟩ : ∃ q, Tendsto (fun n => g^[n] x) atTop (𝓝 q)).choose_spec h⟩

/-- `Statement:` for `limitRetraction g x = p`, the corpus ω-limit set of `x` is `{p}`. -/
theorem lm_omegaLim_of_mem {g : X → X} {x p : X} (h : p ∈ limitRetraction g x) :
    omegaLim g x = {p} := by
  rw [lm_omegaLim_eq_omegaLimit]
  exact lm_omegaLimit_of_tendsto g x p (lm_mem_limitRetraction_iff.1 h)

/-- `Statement:` on a compact Hausdorff space, `p` is the value of `limitRetraction g x` iff the
    corpus ω-limit set of `x` is `{p}`; both directions. -/
theorem lm_mem_iff_omegaLim [CompactSpace X] {g : X → X} {x p : X} :
    p ∈ limitRetraction g x ↔ omegaLim g x = {p} := by
  refine ⟨lm_omegaLim_of_mem, fun h => lm_mem_limitRetraction_iff.2 ?_⟩
  rw [lm_omegaLim_eq_omegaLimit] at h
  exact lm_tendsto_of_omegaLimit g x p h

/-- `Statement:` for continuous `g`, a value of the limit retraction is its own value there: the
    limit is a fixed point (`isFixedPt_of_tendsto_iterate`), so its orbit is constant. -/
theorem lm_limitRetraction_idem {g : X → X} (hg : Continuous g) (x y : X)
    (h : y ∈ limitRetraction g x) : y ∈ limitRetraction g y := by
  rw [lm_mem_limitRetraction_iff] at h ⊢
  have hfix : g y = y := isFixedPt_of_tendsto_iterate h hg.continuousAt
  have : (fun n => g^[n] y) = fun _ => y := funext fun n => Function.iterate_fixed hfix n
  rw [this]
  exact tendsto_const_nhds

/-- `Statement:` the limit motion of a continuous self-map `g` of a Hausdorff space: UP is the
    limit retraction of `g`, OVER is `y = g x`. -/
noncomputable def limitMotion (g : X → X) (hg : Continuous g) : Motion X where
  up := limitRetraction g
  up_idem := lm_limitRetraction_idem hg
  step x y := y = g x

variable {g : X → X} {hg : Continuous g}

/-- `Statement:` OVER of the limit motion is OVER of `Motion.ofFun g`, by `rfl`. -/
theorem lm_limitMotion_step : (limitMotion g hg).step = (Motion.ofFun g).step := rfl

/-- `Statement:` a landing of the limit motion is exactly a fixed point of `g`; both directions. -/
theorem lm_isLanding_iff (y : X) : (limitMotion g hg).IsLanding y ↔ g y = y := by
  show y ∈ limitRetraction g y ↔ _
  rw [lm_mem_limitRetraction_iff]
  constructor
  · intro h; exact isFixedPt_of_tendsto_iterate h hg.continuousAt
  · intro hfix
    have : (fun n => g^[n] y) = fun _ => y := funext fun n => Function.iterate_fixed hfix n
    rw [this]; exact tendsto_const_nhds

/-- `Statement:` UP is unchanged along OVER: the orbit of `g a` is the orbit of `a` shifted by one. -/
theorem lm_upStepInvariant : (limitMotion g hg).UpStepInvariant := by
  rintro a b (rfl : b = g a)
  apply Part.ext
  intro q
  show q ∈ limitRetraction g a ↔ q ∈ limitRetraction g (g a)
  rw [lm_mem_limitRetraction_iff, lm_mem_limitRetraction_iff]
  have : (fun n => g^[n] (g a)) = fun n => g^[n + 1] a :=
    funext fun n => (Function.iterate_succ_apply g n a).symm
  rw [this]
  exact (tendsto_add_atTop_iff_nat (f := fun n => g^[n] a) 1).symm

/-- `Statement:` the orbit of `x` is a run of the limit motion. -/
theorem lm_isRun (x : X) : (limitMotion g hg).IsRun (fun n => g^[n] x) :=
  fun n => Function.iterate_succ_apply' g n x

/-- `Statement:` arrival reads OVER only: two motions with the same step relation have the same
    arrivals. -/
theorem lm_arrives_of_step_eq {α : Type*} {M N : Motion α} (h : M.step = N.step) {y x : α}
    (hx : M.Arrives y x) : N.Arrives y x := by
  induction hx with
  | here => exact Motion.Arrives.here
  | next hex _ ih =>
    exact Motion.Arrives.next (h ▸ hex) (fun b hb => ih b (h ▸ hb))

/-- `Statement:` in the limit motion, `x` arrives at `y` iff some iterate of `g` sends `x` to `y`. -/
theorem lm_arrives_iff (x y : X) :
    (limitMotion g hg).Arrives y x ↔ ∃ n, g^[n] x = y :=
  ⟨fun h => (Motion.arrives_ofFun_iff g y x).1 (lm_arrives_of_step_eq lm_limitMotion_step h),
   fun h => lm_arrives_of_step_eq lm_limitMotion_step.symm ((Motion.arrives_ofFun_iff g y x).2 h)⟩

end LimitRetraction

/-! ### Continuity is consumed by `up_idem` (control) -/

/-- `Statement:` a discontinuous self-map of ℝ: `0 ↦ 2`, `2 ↦ 2`, otherwise halve. -/
noncomputable def lmJumpMap (x : ℝ) : ℝ := if x = 0 then 2 else if x = 2 then 2 else x / 2

/-- `Statement:` CONTROL. Under `lmJumpMap` the orbit of `1` tends to `0` and the orbit of `0` does
    not: the limit of an orbit need not be the limit of its own orbit, so for this discontinuous map
    the limit retraction is not idempotent; `limitMotion` takes continuity for its `up_idem`. -/
theorem lm_jumpMap_breaks_idem :
    Tendsto (fun n => lmJumpMap^[n] 1) atTop (𝓝 0) ∧
      ¬ Tendsto (fun n => lmJumpMap^[n] 0) atTop (𝓝 0) := by
  have h1 : ∀ n, lmJumpMap^[n] 1 = (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      have h0 : (1 / 2 : ℝ) ^ n ≠ 0 := by positivity
      have hle : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h2 : (1 / 2 : ℝ) ^ n ≠ 2 := by intro h; linarith
      simp only [lmJumpMap, h0, h2, ↓reduceIte, pow_succ]; ring
  have h2 : ∀ n, lmJumpMap^[n + 1] 0 = 2 := by
    intro n
    induction n with
    | zero => simp [lmJumpMap]
    | succ n ih => rw [Function.iterate_succ_apply', ih]; simp [lmJumpMap]
  refine ⟨?_, fun h => ?_⟩
  · simp only [h1]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  · have h' := (tendsto_add_atTop_iff_nat (f := fun n => lmJumpMap^[n] 0) 1).2 h
    simp only [h2] at h'
    exact two_ne_zero (tendsto_nhds_unique tendsto_const_nhds h')

/-! ## § II. Convergence is finite arrival at a landing, or a stage closure -/

section TheIff

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] {g : X → X} {hg : Continuous g}

/-- `Statement:` for continuous `g` on a Hausdorff space, the orbit of `x` tends to `p` iff EITHER
    `x` arrives at `p` along OVER and `p` is a landing, OR no stage of the orbit is a fixed point and
    the stages have a stage closure (`Motion.StageClosure`) whose value is `p`; both directions.
    Finite arrival is carried by OVER, convergence without arrival by UP. -/
theorem lm_tendsto_iff_arrival_or_closure (x p : X) :
    Tendsto (fun n => g^[n] x) atTop (𝓝 p) ↔
      ((limitMotion g hg).Arrives p x ∧ (limitMotion g hg).IsLanding p) ∨
      ((∀ n, g (g^[n] x) ≠ g^[n] x) ∧
        ∃ c, (limitMotion g hg).StageClosure (Set.range fun n => g^[n] x) c ∧ p ∈ c) := by
  rw [lm_arrives_iff, lm_isLanding_iff]
  constructor
  · intro ht
    by_cases hfixed : ∃ n, g (g^[n] x) = g^[n] x
    · left
      obtain ⟨n, hn⟩ := hfixed
      have hev : ∀ k, n ≤ k → g^[k] x = g^[n] x := by
        intro k hk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [add_comm, Function.iterate_add_apply, Function.iterate_fixed hn]
      have hq : Tendsto (fun k => g^[k] x) atTop (𝓝 (g^[n] x)) :=
        tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun k hk => (hev k hk).symm⟩)
      have hp : g^[n] x = p := tendsto_nhds_unique hq ht
      exact ⟨⟨n, hp⟩, hp ▸ hn⟩
    · right
      push Not at hfixed
      refine ⟨hfixed, (limitMotion g hg).up x, ?_, lm_mem_limitRetraction_iff.2 ht⟩
      exact Motion.stageClosure_of_run lm_upStepInvariant (lm_isRun x)
        (fun n h => hfixed n ((lm_isLanding_iff _).1 h))
  · rintro (⟨⟨n, hn⟩, hp⟩ | ⟨_, c, hc, hpc⟩)
    · have hev : ∀ k, n ≤ k → g^[k] x = p := by
        intro k hk
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
        rw [add_comm, Function.iterate_add_apply, hn, Function.iterate_fixed hp]
      exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun k hk => (hev k hk).symm⟩)
    · have hux : (limitMotion g hg).up x = c := (hc x ⟨0, rfl⟩).2
      rw [← hux] at hpc
      exact lm_mem_limitRetraction_iff.1 hpc

/-- `Statement:` the two branches are exclusive: in the closure branch `x` does not arrive at `p`
    (`Motion.not_arrives_of_stageClosure`). -/
theorem lm_not_arrives_of_closure (x p : X) {c : Part X}
    (hc : (limitMotion g hg).StageClosure (Set.range fun n => g^[n] x) c) (hp : p ∈ c) :
    ¬ (limitMotion g hg).Arrives p x :=
  Motion.not_arrives_of_stageClosure (s := fun n => g^[n] x) (lm_isRun x) hc hp

/-- `Statement:` the closure branch's first conjunct follows from its stage closure: no stage is a
    landing, and a landing is a fixed point (`lm_isLanding_iff`). -/
example (x : X) {c : Part X}
    (hc : (limitMotion g hg).StageClosure (Set.range fun n => g^[n] x) c) :
    ∀ n, g (g^[n] x) ≠ g^[n] x :=
  fun n h => (hc _ ⟨n, rfl⟩).1 ((lm_isLanding_iff _).2 h)

end TheIff

/-! ### The compactified carrier: scalings on `OnePoint K` -/

section Scaling

variable {K : Type*} [NormedField K] [ProperSpace K]

/-- `Statement:` multiplication by `c ≠ 0` on `OnePoint K`, fixing `∞` (`Homeomorph.onePointCongr`). -/
noncomputable def lmScale (c : K) (hc : c ≠ 0) : OnePoint K ≃ₜ OnePoint K :=
  Homeomorph.onePointCongr (Homeomorph.mulLeft₀ c hc)

omit [ProperSpace K] in
/-- `Statement:` `lmScale c` sends the point `x` of `K` to `c * x`, by `rfl`. -/
theorem lm_scale_some (c : K) (hc : c ≠ 0) (x : K) :
    lmScale c hc (OnePoint.some x) = OnePoint.some (c * x) := rfl

omit [ProperSpace K] in
/-- `Statement:` `lmScale c` fixes `∞`, by `rfl`. -/
theorem lm_scale_infty (c : K) (hc : c ≠ 0) : lmScale c hc OnePoint.infty = OnePoint.infty := rfl

omit [ProperSpace K] in
/-- `Statement:` the `n`-th iterate of `lmScale c` sends `x` to `c ^ n * x`. -/
theorem lm_scale_iterate_some (c : K) (hc : c ≠ 0) (x : K) (n : ℕ) :
    (lmScale c hc)^[n] (OnePoint.some x) = OnePoint.some (c ^ n * x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, lm_scale_some, pow_succ', mul_assoc]

/-- `Statement:` no point of `K` arrives at `∞` along OVER of the limit motion of `lmScale c`.
    The first unjustified step of "compactify, and approach becomes arrival" is here: for a
    scaling, adjoining `∞` adds no step into it from `K`. -/
theorem lm_not_arrives_infty (c : K) (hc : c ≠ 0) (x : K) :
    ¬ (limitMotion (lmScale c hc) (lmScale c hc).continuous).Arrives OnePoint.infty
        (OnePoint.some x) := by
  rw [lm_arrives_iff]
  rintro ⟨n, hn⟩
  rw [lm_scale_iterate_some] at hn
  exact OnePoint.coe_ne_infty _ hn

omit [ProperSpace K] in
/-- `Statement:` if `c ^ n * x` tends to `0` in `K`, the `lmScale c` orbit of `x` tends to `0` in
    `OnePoint K`. -/
theorem lm_tendsto_zero_of_field {c : K} (hc : c ≠ 0) {x : K}
    (h : Tendsto (fun n : ℕ => c ^ n * x) atTop (𝓝 0)) :
    Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some x)) atTop (𝓝 (OnePoint.some 0)) := by
  simp only [lm_scale_iterate_some]
  exact (OnePoint.continuous_coe.tendsto 0).comp h

end Scaling

/-! ## § III. Conjugacy; inversion healed on `OnePoint K`, torn inside `K` when `c ^ n → 0` and `1 < ‖d‖` -/

section Conjugacy

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X] {g : X → X} {hg : Continuous g}
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y]

/-- `Statement:` a homeomorphism `e` with `e ∘ g = h ∘ e` is a strict map (`Motion.Hom`) of limit
    motions. -/
noncomputable def lmHomOfConj {h : Y → Y} (hh : Continuous h) (e : X ≃ₜ Y)
    (hc : ∀ x, e (g x) = h (e x)) : Motion.Hom (limitMotion g hg) (limitMotion h hh) where
  toFun := e
  map_step := by
    rintro a b (rfl : b = g a)
    exact hc a
  map_up := by
    intro x
    apply Part.ext
    intro q
    show q ∈ limitRetraction h (e x) ↔ q ∈ (limitRetraction g x).map e
    have hit : ∀ n, h^[n] (e x) = e (g^[n] x) :=
      fun n => ((Function.Semiconj.iterate_right (f := e) hc n) x).symm
    simp only [lm_mem_limitRetraction_iff, Part.mem_map_iff, hit]
    constructor
    · intro ht
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      have := (e.symm.continuous.tendsto q).comp ht
      simpa [Function.comp_def] using this
    · rintro ⟨a, ha, rfl⟩
      exact (e.continuous.tendsto a).comp ha

/-- `Statement:` a homeomorphism `e` with `e ∘ g = h ∘ e` is a strict isomorphism
    (`Motion.StrictIso`) of limit motions. -/
noncomputable def lmIsoOfConj {h : Y → Y} (hh : Continuous h) (e : X ≃ₜ Y)
    (hc : ∀ x, e (g x) = h (e x)) : Motion.StrictIso (limitMotion g hg) (limitMotion h hh) where
  hom := lmHomOfConj hh e hc
  inv := lmHomOfConj hg e.symm (fun y => by
    apply e.injective
    rw [hc, e.apply_symm_apply, e.apply_symm_apply])
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply

/-- `Statement:` a topological conjugacy, a homeomorphism `e` with `e ∘ g = h ∘ e`, is a
    `Motion.HomeoIso` of limit motions (`ZeroParadox/DieSameness.lean`); its `toStrictIso` is `lmIsoOfConj`. -/
noncomputable def lmHomeoIsoOfConj {h : Y → Y} (hh : Continuous h) (e : X ≃ₜ Y)
    (hc : ∀ x, e (g x) = h (e x)) : Motion.HomeoIso (limitMotion g hg) (limitMotion h hh) :=
  { lmIsoOfConj (hg := hg) hh e hc with
    continuous_hom := e.continuous
    continuous_inv := e.symm.continuous }

/-- `Statement:` the strict isomorphism under `lmHomeoIsoOfConj` is `lmIsoOfConj`, by `rfl`. -/
theorem lmHomeoIsoOfConj_toStrictIso {h : Y → Y} (hh : Continuous h) (e : X ≃ₜ Y)
    (hc : ∀ x, e (g x) = h (e x)) :
    (lmHomeoIsoOfConj (hg := hg) hh e hc).toStrictIso = lmIsoOfConj (hg := hg) hh e hc := rfl

end Conjugacy

section Healed

variable {K : Type*} [NormedField K] [ProperSpace K]

/-- `Statement:` `onePointInv` conjugates `lmScale c` to `lmScale d` when `c * d = 1`. Over
    `ℚ_[2]` with `d = c⁻¹` this is `rInv_conj_mulLeft` (`ZeroParadox/Valuation/RiemannSphere.lean`). -/
theorem lm_onePointInv_conj_scale (c d : K) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c * d = 1)
    (z : OnePoint K) : onePointInvHomeo (lmScale c hc z) = lmScale d hd (onePointInvHomeo z) := by
  have hinv : c⁻¹ = d := inv_eq_of_mul_eq_one_right hcd
  show onePointInv (lmScale c hc z) = lmScale d hd (onePointInv z)
  induction z using OnePoint.rec with
  | infty => rw [lm_scale_infty, onePointInv_infty, lm_scale_some, mul_zero]
  | coe x =>
    by_cases hx : x = 0
    · subst hx; rw [lm_scale_some, mul_zero, onePointInv_zero, lm_scale_infty]
    · rw [lm_scale_some, onePointInv_coe_ne (mul_ne_zero hc hx), onePointInv_coe_ne hx,
        lm_scale_some, mul_inv, hinv]

/-- `Statement:` INVERSION, healed. On `OnePoint K`, `onePointInv` is a strict isomorphism of the
    limit motions of `lmScale c` and `lmScale d`, `c * d = 1`; it exchanges `0` and `∞`, two
    distinct points (`onePointInv_swaps`). -/
noncomputable def lmHealedIso (c d : K) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c * d = 1) :
    Motion.StrictIso (limitMotion (lmScale c hc) (lmScale c hc).continuous)
      (limitMotion (lmScale d hd) (lmScale d hd).continuous) :=
  lmIsoOfConj _ onePointInvHomeo (lm_onePointInv_conj_scale c d hc hd hcd)

/-- `Statement:` the forward map of `lmHealedIso` is `onePointInv`, by `rfl`. -/
theorem lm_healedIso_toFun (c d : K) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c * d = 1) :
    (lmHealedIso c d hc hd hcd).hom.toFun = onePointInv := rfl

/-- `Statement:` transport along `lmHealedIso`'s UP square: if the `lmScale c` orbit of `x ≠ 0`
    tends to `0`, the `lmScale d` orbit of `x⁻¹` tends to `∞`. -/
theorem lm_tendsto_infty_of_conj (c d : K) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c * d = 1) {x : K}
    (hx : x ≠ 0)
    (h0 : Tendsto (fun n => (lmScale c hc)^[n] (OnePoint.some x)) atTop (𝓝 (OnePoint.some 0))) :
    Tendsto (fun n => (lmScale d hd)^[n] (OnePoint.some x⁻¹)) atTop (𝓝 OnePoint.infty) := by
  have hup := (lmHealedIso c d hc hd hcd).hom.map_up (OnePoint.some x)
  have hmem : OnePoint.infty ∈ (limitMotion (lmScale d hd) (lmScale d hd).continuous).up
      ((lmHealedIso c d hc hd hcd).hom.toFun (OnePoint.some x)) := by
    rw [hup, Part.mem_map_iff]
    exact ⟨OnePoint.some 0, lm_mem_limitRetraction_iff.2 h0, by
      rw [lm_healedIso_toFun]; exact onePointInv_zero⟩
  have hto : (lmHealedIso c d hc hd hcd).hom.toFun (OnePoint.some x) = OnePoint.some x⁻¹ := by
    rw [lm_healedIso_toFun]; exact onePointInv_coe_ne hx
  rw [hto] at hmem
  exact lm_mem_limitRetraction_iff.1 hmem

end Healed

section Torn

variable {K : Type*} [NormedField K]

/-- `Statement:` field inversion is a strict isomorphism of the bare function motions
    `Motion.ofFun (c * ·)` and `Motion.ofFun (d * ·)` on `K` when `c * d = 1`. -/
noncomputable def lmBareInvIso (c d : K) (hcd : c * d = 1) :
    Motion.StrictIso (Motion.ofFun (fun z : K => c * z)) (Motion.ofFun (fun z : K => d * z)) where
  hom := ⟨fun z => z⁻¹, fun {a b} (h : b = c * a) => by
      show b⁻¹ = d * a⁻¹
      rw [h, mul_inv, inv_eq_of_mul_eq_one_right hcd], fun x => by
      simp [Motion.ofFun, Motion.ofTotal]⟩
  inv := ⟨fun z => z⁻¹, fun {a b} (h : b = d * a) => by
      show b⁻¹ = c * a⁻¹
      rw [h, mul_inv, inv_eq_of_mul_eq_one_left hcd], fun x => by
      simp [Motion.ofFun, Motion.ofTotal]⟩
  left_inv := inv_inv
  right_inv := inv_inv

/-- `Statement:` CARRIER, torn. If `c ^ n` tends to `0` in `K` and `1 < ‖d‖`, no strict map of the
    limit motions on `K` from `c`-scaling to `d`-scaling has field inversion as its map. -/
theorem lm_torn_no_hom {c d : K} (hd1 : 1 < ‖d‖)
    (h0 : Tendsto (fun n : ℕ => c ^ n * 1) atTop (𝓝 0)) :
    ¬ ∃ φ : Motion.Hom (limitMotion (fun z : K => c * z) (continuous_const_mul c))
        (limitMotion (fun z : K => d * z) (continuous_const_mul d)), ∀ x, φ.toFun x = x⁻¹ := by
  rintro ⟨φ, hφ⟩
  have hup := φ.map_up 1
  have hmem : (0 : K)⁻¹ ∈
      (limitMotion (fun z : K => d * z) (continuous_const_mul d)).up (φ.toFun 1) := by
    rw [hup, Part.mem_map_iff]
    refine ⟨0, ?_, hφ 0⟩
    show (0 : K) ∈ limitRetraction _ 1
    rw [lm_mem_limitRetraction_iff]
    simpa only [mul_left_iterate] using h0
  rw [hφ, inv_one, inv_zero] at hmem
  have ht : Tendsto (fun n => (fun z : K => d * z)^[n] 1) atTop (𝓝 0) :=
    lm_mem_limitRetraction_iff.1 hmem
  simp only [mul_left_iterate, mul_one] at ht
  have hnorm : Tendsto (fun n : ℕ => ‖d ^ n‖) atTop atTop := by
    simp only [norm_pow]
    exact tendsto_pow_atTop_atTop_of_one_lt hd1
  exact not_tendsto_nhds_of_tendsto_atTop hnorm _ ht.norm

end Torn

/-! ## § IV. Instances on `ℚ_[2]` and ℝ, each with a control on the same carrier -/

section Instances

variable {K : Type*} [NormedField K] [ProperSpace K]

/-- `Statement:` CONTROL. With `2 ≠ 0` in `K`, the orbit of `1` under `lmScale (-1)`
    (`1, -1, 1, …`) tends to no point of `OnePoint K`. -/
theorem lm_negOrbit_no_limit (h2 : (2 : K) ≠ 0) :
    ¬ ∃ q, Tendsto (fun n => (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))^[n] (OnePoint.some 1))
      atTop (𝓝 q) := by
  rintro ⟨q, hq⟩
  have hfix := isFixedPt_of_tendsto_iterate hq
    (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero)).continuous.continuousAt
  simp only [lm_scale_iterate_some, mul_one] at hq
  induction q using OnePoint.rec with
  | infty =>
    have hU : IsOpen ((OnePoint.some '' Metric.closedBall (0 : K) 1)ᶜ) :=
      OnePoint.isOpen_compl_image_coe.2 ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 1⟩
    obtain ⟨n, hn⟩ := (hq.eventually (hU.mem_nhds OnePoint.infty_notMem_image_coe)).exists
    exact hn ⟨(-1) ^ n, by simp [norm_pow], rfl⟩
  | coe y =>
    have hy : -1 * y = y := OnePoint.coe_injective hfix
    have hy0 : y = 0 := by
      have : (2 : K) * y = 0 := by linear_combination -hy
      exact (mul_eq_zero.1 this).resolve_left h2
    subst hy0
    have ht : Tendsto (fun n : ℕ => (-1 : K) ^ n) atTop (𝓝 0) :=
      (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).2 hq
    have hn := ht.norm
    simp only [norm_pow, norm_neg, norm_one, one_pow, norm_zero] at hn
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hn)

/-- `Statement:` CONTROL, the die side: for the oscillating orbit, neither branch of
    `lm_tendsto_iff_arrival_or_closure` holds at any point of `OnePoint K`. -/
theorem lm_negOrbit_fails_die (h2 : (2 : K) ≠ 0) (p : OnePoint K) :
    ¬ ((limitMotion (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero)) (lmScale _ _).continuous).Arrives
          p (OnePoint.some 1) ∧
        (limitMotion (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))
          (lmScale _ _).continuous).IsLanding p) ∧
    ¬ ∃ c, (limitMotion (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))
          (lmScale _ _).continuous).StageClosure
          (Set.range fun n => (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))^[n] (OnePoint.some 1))
          c ∧ p ∈ c := by
  have hno : ¬ Tendsto (fun n => (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))^[n]
      (OnePoint.some 1)) atTop (𝓝 p) := fun h => lm_negOrbit_no_limit h2 ⟨p, h⟩
  rw [lm_tendsto_iff_arrival_or_closure
    (hg := (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero)).continuous)] at hno
  push Not at hno
  refine ⟨fun h => ?_, fun ⟨c, hc, hp⟩ => ?_⟩
  · exact hno.1 h.1 h.2
  · have hnf : ∀ n, (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))
        ((lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))^[n] (OnePoint.some 1)) ≠
        (lmScale (-1 : K) (neg_ne_zero.2 one_ne_zero))^[n] (OnePoint.some 1) := by
      intro n hn
      rw [lm_scale_iterate_some, lm_scale_some] at hn
      have hn' := OnePoint.coe_injective hn
      have : (2 : K) * ((-1) ^ n * 1) = 0 := by linear_combination -hn'
      rcases mul_eq_zero.1 this with h | h
      · exact h2 h
      · simp at h
    exact hno.2 hnf c hc hp

/-- `Statement:` `ℚ_[2]`, doubling on `OnePoint ℚ_[2]`: for `x ≠ 0` the orbit lands at `0` by stage
    closure and does not arrive at `0` (`doubling_orbit_tendsto_zero`,
    `padic_orbit_never_reaches_zero`). -/
theorem lm_q2_doubling_closure_at_zero (x : ℚ_[2]) (hx : x ≠ 0) :
    (∃ c, (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).StageClosure
        (Set.range fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some x)) c ∧
        OnePoint.some 0 ∈ c) ∧
    ¬ (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).Arrives
        (OnePoint.some 0) (OnePoint.some x) := by
  have ht := lm_tendsto_zero_of_field (two_ne_zero : (2 : ℚ_[2]) ≠ 0)
    (doubling_orbit_tendsto_zero x)
  rcases (lm_tendsto_iff_arrival_or_closure _ _).1 ht with ⟨ha, _⟩ | ⟨_, c, hc, hp⟩
  · exfalso
    obtain ⟨n, hn⟩ := (lm_arrives_iff _ _).1 ha
    rw [lm_scale_iterate_some] at hn
    exact padic_orbit_never_reaches_zero x hx n (OnePoint.coe_injective hn)
  · exact ⟨⟨c, hc, hp⟩, lm_not_arrives_of_closure _ _ hc hp⟩

/-- `Statement:` `ℚ_[2]`, halving on `OnePoint ℚ_[2]`: for `x ≠ 0` the orbit tends to `∞`, by
    transport through `lmHealedIso`, and does not arrive at `∞`. -/
theorem lm_q2_halving_to_infty (x : ℚ_[2]) (hx : x ≠ 0) :
    Tendsto (fun n => (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))^[n] (OnePoint.some x))
      atTop (𝓝 OnePoint.infty) ∧
    ¬ (limitMotion (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero)) (lmScale _ _).continuous).Arrives
        OnePoint.infty (OnePoint.some x) := by
  refine ⟨?_, lm_not_arrives_infty _ _ x⟩
  have h := lm_tendsto_infty_of_conj (2 : ℚ_[2]) 2⁻¹ two_ne_zero (inv_ne_zero two_ne_zero)
    (mul_inv_cancel₀ two_ne_zero) (inv_ne_zero hx)
    (lm_tendsto_zero_of_field two_ne_zero (doubling_orbit_tendsto_zero x⁻¹))
  rwa [inv_inv] at h

/-- `Statement:` CARRIER, `ℚ_[2]` torn: inside `ℚ_[2]` field inversion is no strict map of limit
    motions from doubling to halving, while it is the map of a strict isomorphism of the bare
    `ofFun` motions (`lmBareInvIso`). -/
theorem lm_q2_torn :
    (∃ φ : Motion.StrictIso (Motion.ofFun (fun z : ℚ_[2] => 2 * z))
      (Motion.ofFun (fun z : ℚ_[2] => 2⁻¹ * z)), ∀ x, φ.hom.toFun x = x⁻¹) ∧
    ¬ ∃ φ : Motion.Hom (limitMotion (fun z : ℚ_[2] => 2 * z) (continuous_const_mul 2))
        (limitMotion (fun z : ℚ_[2] => 2⁻¹ * z) (continuous_const_mul 2⁻¹)),
        ∀ x, φ.toFun x = x⁻¹ := by
  refine ⟨⟨lmBareInvIso 2 2⁻¹ (mul_inv_cancel₀ two_ne_zero), fun _ => rfl⟩, lm_torn_no_hom ?_ ?_⟩
  · have h2n : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
    rw [norm_inv, h2n]; norm_num
  · simpa using doubling_orbit_tendsto_zero (1 : ℚ_[2])

-- Statement: CONTROL on `OnePoint ℚ_[2]`: the `-1` orbit fails both branches at every point.
example (p : OnePoint ℚ_[2]) := lm_negOrbit_fails_die (K := ℚ_[2]) (by norm_num) p

/-- `Statement:` in ℝ, `(1/2) ^ n * x` tends to `0`. -/
theorem lm_real_half_tendsto (x : ℝ) : Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n * x) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ) < 1)).mul_const x

/-- `Statement:` ℝ, doubling on `OnePoint ℝ`: for `x ≠ 0` the orbit tends to `∞` (transport through
    `lmHealedIso` from halving), lands there by stage closure, and does not arrive. -/
theorem lm_real_doubling_closure_at_infty (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n => (lmScale (2 : ℝ) two_ne_zero)^[n] (OnePoint.some x)) atTop
      (𝓝 OnePoint.infty) ∧
    (∃ c, (limitMotion (lmScale (2 : ℝ) two_ne_zero) (lmScale _ _).continuous).StageClosure
        (Set.range fun n => (lmScale (2 : ℝ) two_ne_zero)^[n] (OnePoint.some x)) c ∧
        OnePoint.infty ∈ c) ∧
    ¬ (limitMotion (lmScale (2 : ℝ) two_ne_zero) (lmScale _ _).continuous).Arrives OnePoint.infty
        (OnePoint.some x) := by
  have ht : Tendsto (fun n => (lmScale (2 : ℝ) two_ne_zero)^[n] (OnePoint.some x)) atTop
      (𝓝 OnePoint.infty) := by
    have h := lm_tendsto_infty_of_conj (2⁻¹ : ℝ) 2 (inv_ne_zero two_ne_zero) two_ne_zero
      (inv_mul_cancel₀ two_ne_zero) (inv_ne_zero hx)
      (lm_tendsto_zero_of_field (inv_ne_zero two_ne_zero) (lm_real_half_tendsto x⁻¹))
    rwa [inv_inv] at h
  refine ⟨ht, ?_, lm_not_arrives_infty _ _ x⟩
  rcases (lm_tendsto_iff_arrival_or_closure _ _).1 ht with ⟨ha, _⟩ | ⟨_, c, hc, hp⟩
  · exact absurd ha (lm_not_arrives_infty _ _ x)
  · exact ⟨c, hc, hp⟩

/-- `Statement:` CARRIER, ℝ torn: inside ℝ field inversion is no strict map of limit motions from
    halving to doubling, while it is the map of a strict isomorphism of the bare `ofFun` motions
    (`lmBareInvIso`). -/
theorem lm_real_torn :
    (∃ φ : Motion.StrictIso (Motion.ofFun (fun z : ℝ => 2⁻¹ * z))
      (Motion.ofFun (fun z : ℝ => 2 * z)), ∀ x, φ.hom.toFun x = x⁻¹) ∧
    ¬ ∃ φ : Motion.Hom (limitMotion (fun z : ℝ => 2⁻¹ * z) (continuous_const_mul 2⁻¹))
        (limitMotion (fun z : ℝ => 2 * z) (continuous_const_mul 2)), ∀ x, φ.toFun x = x⁻¹ :=
  ⟨⟨lmBareInvIso 2⁻¹ 2 (inv_mul_cancel₀ two_ne_zero), fun _ => rfl⟩,
    lm_torn_no_hom (by norm_num) (lm_real_half_tendsto 1)⟩

-- Statement: CONTROL on `OnePoint ℝ`: the `-1` orbit fails both branches at every point.
example (p : OnePoint ℝ) := lm_negOrbit_fails_die (K := ℝ) (by norm_num) p

end Instances

/-! ## § V. The reverse direction: one tower in the ordinal chart and in the `ℤ_[2]` chart

`Reading:` CARRIER. § II turns an approach (`Tendsto`) into a die fact inside ONE motion. Here one tower,
seeded at 0, ⊥ of `Ordinal`, is read in two charts joined by `NONote.repr` and `cnfToZp2`, never by
`=`. In `Ordinal.{0}`, with Mathlib's order topology, `ordinalTowerMotion` is the limit motion of
`α ↦ ω^α`, so § II's iff applies to it (the first `example` below), and the stages have a stage
closure (`Motion.StageClosure`, § II's closure branch) with the value ε₀ (ε₀ ≠ 0 and ε₀ ≠ ⊥ of
`Ordinal`, `epsilon0_ne_zero`, `epsilon0_ne_bot`). In `ℤ_[2]` the images start at ℤ_[2]'s 0, differ
from it from stage 1 on, and approach that same 0. -/

/-- `Statement:` at universe 0: in `Ordinal.{0}`'s order topology `α ↦ ω^α` is continuous
    (`Order.IsNormal.continuous`), `ordinalTowerMotion` equals its limit motion (each orbit tends to its `nfp`, UP of the tower), and
    § II's iff `lm_tendsto_iff_arrival_or_closure` holds for `ordinalTowerMotion`. -/
example :
    ordinalTowerMotion.{0} = limitMotion (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)
      (Ordinal.isNormal_opow Ordinal.one_lt_omega0).continuous ∧
    ∀ x p : Ordinal.{0},
      Tendsto (fun n => (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] x) atTop (𝓝 p) ↔
        (ordinalTowerMotion.{0}.Arrives p x ∧ ordinalTowerMotion.{0}.IsLanding p) ∨
        ((∀ n, Ordinal.omega0 ^ ((fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] x)
            ≠ (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] x) ∧
          ∃ c, ordinalTowerMotion.{0}.StageClosure
            (Set.range fun n => (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] x) c ∧ p ∈ c) := by
  have hn := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  have ht : ∀ x : Ordinal.{0}, Tendsto (fun n => (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] x)
      atTop (𝓝 (Ordinal.nfp (fun a => Ordinal.omega0 ^ a) x)) := fun x => by
    rw [← Ordinal.iSup_iterate_eq_nfp]
    exact tendsto_atTop_ciSup (Monotone.monotone_iterate_of_le_map hn.strictMono.monotone
      (hn.strictMono.id_le x)) Ordinal.bddAbove_of_small
  have hup : ordinalTowerMotion.{0}.up
      = (limitMotion (fun a : Ordinal.{0} => Ordinal.omega0 ^ a) hn.continuous).up := by
    funext x
    apply Part.ext
    intro q
    show q ∈ Part.some _ ↔ q ∈ limitRetraction _ x
    rw [Part.mem_some_iff, lm_mem_limitRetraction_iff]
    exact ⟨fun h => by rw [h]; exact ht x, fun h => tendsto_nhds_unique h (ht x)⟩
  have heq : ordinalTowerMotion.{0}
      = limitMotion (fun a : Ordinal.{0} => Ordinal.omega0 ^ a) hn.continuous := by
    cases h : ordinalTowerMotion.{0} with
    | mk u1 i1 s1 =>
      rw [h] at hup
      simp only at hup
      subst hup
      have hs : s1 = (limitMotion (fun a : Ordinal.{0} => Ordinal.omega0 ^ a) hn.continuous).step := by
        have : ordinalTowerMotion.{0}.step = s1 := by rw [h]
        rw [← this]; rfl
      subst hs
      rfl
  exact ⟨heq, fun x p => by rw [heq]; exact lm_tendsto_iff_arrival_or_closure x p⟩

/-- `Statement:` ordinal chart: the stages `fundamentalSeq n` have a stage closure with UP value ε₀
    in `ordinalTowerMotion` (`ordinalTowerMotion_stageClosure`), and 0 of `Ordinal` does not arrive
    at ε₀ along OVER (`Motion.not_arrives_of_stageClosure`). -/
example : ordinalTowerMotion.{0}.StageClosure (Set.range fundamentalSeq) (Part.some (Ordinal.epsilon 0)) ∧
    ¬ ordinalTowerMotion.{0}.Arrives (Ordinal.epsilon 0) 0 :=
  ⟨ordinalTowerMotion_stageClosure,
   Motion.not_arrives_of_stageClosure (s := fun n => (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] 0)
     ordinalTowerMotion_isRun ordinalTowerMotion_stageClosure (Part.mem_some _)⟩

/-- `Statement:` `ℤ_[2]` chart, the same tower: each `towerNONote n` denotes the ordinal stage
    `fundamentalSeq n` (`towerNONote_repr`), its image `cnfToZp2 (towerNONote n)` is not ℤ_[2]'s 0
    from stage 1 on, and the images tend to that 0 (`snap_arc_z2_loop`). -/
example : (∀ n, NONote.repr (towerNONote n) = fundamentalSeq n) ∧
    (∀ n, 1 ≤ n → cnfToZp2 (towerNONote n) ≠ 0) ∧
    Tendsto (fun n => cnfToZp2 (towerNONote n)) atTop (𝓝 0) :=
  ⟨towerNONote_repr, snap_arc_z2_loop.2.1, snap_arc_z2_loop.2.2⟩

/-! `Reading:` CARRIER. ε₀ gets no image in `ℤ_[2]`: `cnfToZp2` takes `NONote`, and every notation
denotes below ε₀ (`repr_lt_epsilon0`). A phase map that sends every tower stage to `c₀` (`h0`) and
whose `snapEmbed` reading is continuous along the tower sends ε₀ to `c₀`, not `c₁` (the anonymous
`example` after `hε₀`'s ℤ₂ chart in
`ZeroParadox/Ordinal/Incompleteness.lean` § II). The bound on the other side is cited, not claimed:
Escardó (preprint of JSL 78(3), 2013, § 11, p. 19) records that ε₀ cannot be embedded in `2^ℕ`
using limit structures (quote measured 2026-11-01 against the retrieved preprint). -/

/-! ## § VI. The dipole: a limit sink with its exceptional point, and a partner with OVER reversed -/

section Dipole

universe u

variable {α β : Type u}

/-- `Statement:` in `M`, every point other than `q` has UP-value `p`. -/
def lmSinkOf (M : Motion α) (p q : α) : Prop := ∀ x, x ≠ q → p ∈ M.up x

/-- `Statement:` `p ≠ q`, `p` is a limit sink of `M` with exceptional point `q`, `q` is a limit sink
    of `N` with exceptional point `p`, and `N` steps from `a` to `b` iff `M` steps from `b` to `a`. -/
def lmDipole (M N : Motion α) (p q : α) : Prop :=
  p ≠ q ∧ lmSinkOf M p q ∧ lmSinkOf N q p ∧ ∀ a b, N.step a b ↔ M.step b a

/-- `Statement:` a strict isomorphism `φ` from `M` to `N` sends a limit sink `p` of `M` with
    exceptional point `q` to the limit sink `φ p` of `N` with exceptional point `φ q`. -/
theorem lmSinkOf.map {M : Motion α} {N : Motion β} (φ : Motion.StrictIso M N) {p q : α}
    (h : lmSinkOf M p q) : lmSinkOf N (φ.hom.toFun p) (φ.hom.toFun q) := by
  intro y hy
  have hx : φ.inv.toFun y ≠ q := fun e => hy (by rw [← e, φ.right_inv])
  have h1 := h _ hx
  have h2 := φ.hom.map_up (φ.inv.toFun y)
  rw [φ.right_inv] at h2
  rw [h2]
  exact Part.mem_map _ h1

end Dipole

/-! `Reading:` INVERSION. The dipole as a magnet: field lines leave one pole and arrive at the other, and the
partner motion runs them the other way. This is north–south dynamics (prior art in the ride-along
`LimitMotion.md`), stated pointwise on the UP leg. The polarity lives only in UP, the limit leg: on
OVER both poles of `OnePoint ℚ_[2]` step only to themselves in both directions, and no point is a
step sink or a step source (`lm_dbl_step_level`). The dipole shape alone does not single out `ℚ_[2]`:
doubling and halving on `OnePoint ℝ` form a dipole too, with the poles exchanged (`lm_real_dipole`). The pole
⊥ = 0 = ∞ stays a chart claim (`ZeroParadox/BottomCannotBe.lean` § INVERSION), and nothing in this
section proves the coincidence: `lm_q2_dipole` relates two distinct points, `0` of `ℚ_[2]` and `∞`,
exchanged by `onePointInv`. -/

section DipoleInstance

variable {K : Type*} [NormedField K]

/-- `Statement:` if `c * d = 1`, then `lmScale c (lmScale d z) = z` on `OnePoint K`. -/
theorem lm_scale_cancel (c d : K) (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c * d = 1) (z : OnePoint K) :
    lmScale c hc (lmScale d hd z) = z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x => rw [lm_scale_some, lm_scale_some, ← mul_assoc, hcd, one_mul]

/-- `Statement:` on `OnePoint ℚ_[2]`, halving steps from `a` to `b` iff doubling steps from `b` to
    `a`. -/
theorem lm_hlv_step_reverse (a b : OnePoint ℚ_[2]) :
    (limitMotion (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero)) (lmScale _ _).continuous).step a b ↔
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).step b a := by
  show b = lmScale (2⁻¹ : ℚ_[2]) _ a ↔ a = lmScale (2 : ℚ_[2]) _ b
  constructor
  · rintro rfl
    exact (lm_scale_cancel 2 2⁻¹ two_ne_zero (inv_ne_zero two_ne_zero)
      (mul_inv_cancel₀ two_ne_zero) a).symm
  · rintro rfl
    exact (lm_scale_cancel 2⁻¹ 2 (inv_ne_zero two_ne_zero) two_ne_zero
      (inv_mul_cancel₀ two_ne_zero) b).symm

/-- `Statement:` on `OnePoint ℚ_[2]`, `0` of `ℚ_[2]` is the limit sink of doubling with exceptional
    point `∞`. -/
theorem lm_dbl_sinkOf :
    lmSinkOf (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous)
      (OnePoint.some 0) OnePoint.infty := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact absurd rfl hx
  | coe z =>
    show OnePoint.some 0 ∈ limitRetraction _ (OnePoint.some z)
    exact lm_mem_limitRetraction_iff.2
      (lm_tendsto_zero_of_field two_ne_zero (doubling_orbit_tendsto_zero z))

/-- `Statement:` on `OnePoint ℚ_[2]`, `∞` is the limit sink of halving with exceptional point `0` of
    `ℚ_[2]`; proved by `lmSinkOf.map` along `lmHealedIso`, from `lm_dbl_sinkOf`. -/
theorem lm_hlv_sinkOf :
    lmSinkOf (limitMotion (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero)) (lmScale _ _).continuous)
      OnePoint.infty (OnePoint.some 0) := by
  have h := lmSinkOf.map (lmHealedIso (2 : ℚ_[2]) 2⁻¹ two_ne_zero (inv_ne_zero two_ne_zero)
    (mul_inv_cancel₀ two_ne_zero)) lm_dbl_sinkOf
  rw [lm_healedIso_toFun, onePointInv_zero, onePointInv_infty] at h
  exact h

/-- `Statement:` on `OnePoint ℚ_[2]`, the limit motions of doubling and halving form a dipole with
    poles `0` of `ℚ_[2]` and `∞`. -/
theorem lm_q2_dipole :
    lmDipole (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous)
      (limitMotion (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero)) (lmScale _ _).continuous)
      (OnePoint.some 0) OnePoint.infty :=
  ⟨OnePoint.coe_ne_infty 0, lm_dbl_sinkOf, lm_hlv_sinkOf, lm_hlv_step_reverse⟩

/-- `Statement:` for doubling on `OnePoint ℚ_[2]`, `0` of `ℚ_[2]` and `∞` each step only to
    themselves, in the motion and in its reverse, and no point has no successor, in the motion or in
    its reverse. -/
theorem lm_dbl_step_level :
    (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).SelfOnlyAt
        (OnePoint.some 0) ∧
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).SelfOnlyAt
        OnePoint.infty ∧
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).reverse.SelfOnlyAt
        (OnePoint.some 0) ∧
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).reverse.SelfOnlyAt
        OnePoint.infty ∧
      (∀ y, ¬ (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).NoStepAt y) ∧
      (∀ y, ¬ (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero)
        (lmScale _ _).continuous).reverse.NoStepAt y) := by
  have f0 : lmScale (2 : ℚ_[2]) two_ne_zero (OnePoint.some 0) = OnePoint.some 0 := by
    rw [lm_scale_some, mul_zero]
  have fi : lmScale (2 : ℚ_[2]) two_ne_zero OnePoint.infty = OnePoint.infty := lm_scale_infty _ _
  refine ⟨⟨f0.symm, fun b hb => hb.trans f0⟩, ⟨fi.symm, fun b hb => hb.trans fi⟩,
    ⟨f0.symm, fun b (hb : OnePoint.some 0 = lmScale (2 : ℚ_[2]) two_ne_zero b) => ?_⟩,
    ⟨fi.symm, fun b (hb : OnePoint.infty = lmScale (2 : ℚ_[2]) two_ne_zero b) => ?_⟩,
    fun y h => h _ rfl, fun y h => h (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero) y) ?_⟩
  · exact (lmScale (2 : ℚ_[2]) two_ne_zero).injective (hb.symm.trans f0.symm)
  · exact (lmScale (2 : ℚ_[2]) two_ne_zero).injective (hb.symm.trans fi.symm)
  · exact (lm_scale_cancel 2 2⁻¹ two_ne_zero (inv_ne_zero two_ne_zero)
      (mul_inv_cancel₀ two_ne_zero) y).symm

/-- `Statement:` `∞` is not the limit sink, with exceptional point `0` of `ℚ_[2]`, of the reverse
    (`Motion.reverse`) of doubling's limit motion on `OnePoint ℚ_[2]`. -/
theorem lm_reverse_not_partner :
    ¬ lmSinkOf (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).reverse
      OnePoint.infty (OnePoint.some 0) := by
  intro h
  have h1 : OnePoint.infty ∈
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).up (OnePoint.some 1) :=
    h _ (fun e => one_ne_zero (OnePoint.coe_injective e))
  have h0 : OnePoint.some 0 ∈
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).up (OnePoint.some 1) :=
    lm_dbl_sinkOf _ (OnePoint.coe_ne_infty 1)
  exact OnePoint.coe_ne_infty 0 (Part.mem_unique h0 h1)

/-- `Statement:` the doubling orbit of `2` in `OnePoint ℚ_[2]` is the member sequence of
    `q2InfinitudeFloor`, its floor is `0` of `ℚ_[2]`, that point is the limit sink of doubling with
    exceptional point `∞`, and the complexity `cx` at the floor is `⊤` of `ℕ∞`. -/
theorem lm_fieldLine_is_members :
    (∀ n, (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some 2) =
        OnePoint.some (q2InfinitudeFloor.member n)) ∧
      q2InfinitudeFloor.floor = (0 : ℚ_[2]) ∧
      lmSinkOf (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous)
        (OnePoint.some q2InfinitudeFloor.floor) OnePoint.infty ∧
      q2InfinitudeFloor.cx q2InfinitudeFloor.floor = ⊤ := by
  refine ⟨fun n => ?_, rfl, lm_dbl_sinkOf, infinitude_forces_infinite_complexity _⟩
  rw [lm_scale_iterate_some]
  show OnePoint.some ((2 : ℚ_[2]) ^ n * 2) = OnePoint.some ((2 : ℚ_[2]) ^ (n + 1))
  rw [pow_succ]

/-- `Statement:` CONTROL. On `OnePoint ℝ`, the limit motions of doubling and halving form a dipole
    with poles `∞` and `0` of ℝ. -/
theorem lm_real_dipole :
    lmDipole (limitMotion (lmScale (2 : ℝ) two_ne_zero) (lmScale _ _).continuous)
      (limitMotion (lmScale (2⁻¹ : ℝ) (inv_ne_zero two_ne_zero)) (lmScale _ _).continuous)
      OnePoint.infty (OnePoint.some 0) := by
  have hs : lmSinkOf (limitMotion (lmScale (2⁻¹ : ℝ) (inv_ne_zero two_ne_zero))
      (lmScale _ _).continuous) (OnePoint.some 0) OnePoint.infty := by
    intro x hx
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe z =>
      show OnePoint.some 0 ∈ limitRetraction _ (OnePoint.some z)
      exact lm_mem_limitRetraction_iff.2
        (lm_tendsto_zero_of_field (inv_ne_zero two_ne_zero) (lm_real_half_tendsto z))
  refine ⟨(OnePoint.coe_ne_infty 0).symm, ?_, hs, fun a b => ?_⟩
  · intro x hx
    induction x using OnePoint.rec with
    | infty =>
      show OnePoint.infty ∈ limitRetraction _ OnePoint.infty
      rw [lm_mem_limitRetraction_iff]
      simp only [Function.iterate_fixed (lm_scale_infty (2 : ℝ) two_ne_zero)]
      exact tendsto_const_nhds
    | coe z =>
      show OnePoint.infty ∈ limitRetraction _ (OnePoint.some z)
      exact lm_mem_limitRetraction_iff.2
        (lm_real_doubling_closure_at_infty z (fun e => hx (by rw [e]))).1
  · show b = lmScale (2⁻¹ : ℝ) _ a ↔ a = lmScale (2 : ℝ) _ b
    constructor
    · rintro rfl
      exact (lm_scale_cancel 2 2⁻¹ two_ne_zero (inv_ne_zero two_ne_zero)
        (mul_inv_cancel₀ two_ne_zero) a).symm
    · rintro rfl
      exact (lm_scale_cancel 2⁻¹ 2 (inv_ne_zero two_ne_zero) two_ne_zero
        (inv_mul_cancel₀ two_ne_zero) b).symm

/-- `Statement:` CONTROL. On `OnePoint ℝ`, `0` of ℝ is not the limit sink of doubling with
    exceptional point `∞`. -/
theorem lm_real_dbl_zero_not_sink :
    ¬ lmSinkOf (limitMotion (lmScale (2 : ℝ) two_ne_zero) (lmScale _ _).continuous)
      (OnePoint.some 0) OnePoint.infty := by
  intro h
  have h0 := h (OnePoint.some 1) (OnePoint.coe_ne_infty 1)
  have hi := lm_real_dipole.2.1 (OnePoint.some 1) (fun e => one_ne_zero (OnePoint.coe_injective e))
  exact OnePoint.coe_ne_infty 0 (Part.mem_unique h0 hi)

/-- `Statement:` CONTROL. On `OnePoint ℚ_[2]`, no `p` is a limit sink with exceptional point `q` of
    the identity's limit motion, for any `p` and `q`. -/
theorem lm_id_no_sink (p q : OnePoint ℚ_[2]) :
    ¬ lmSinkOf (limitMotion (id : OnePoint ℚ_[2] → OnePoint ℚ_[2]) continuous_id) p q := by
  intro h
  have key : ∀ x, x ≠ q → p = x := fun x hx => by
    have := lm_mem_limitRetraction_iff.1 (h x hx)
    simp only [Function.iterate_id, id] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have d01 : (OnePoint.some (0 : ℚ_[2])) ≠ OnePoint.some 1 :=
    fun e => zero_ne_one (OnePoint.coe_injective e)
  have d0i : (OnePoint.some (0 : ℚ_[2])) ≠ OnePoint.infty := OnePoint.coe_ne_infty 0
  have d1i : (OnePoint.some (1 : ℚ_[2])) ≠ OnePoint.infty := OnePoint.coe_ne_infty 1
  by_cases h0 : OnePoint.some (0 : ℚ_[2]) = q
  · subst h0
    exact d1i ((key _ d01.symm).symm.trans (key _ (fun e => d0i e.symm)))
  · by_cases h1 : OnePoint.some (1 : ℚ_[2]) = q
    · subst h1
      exact d0i ((key _ h0).symm.trans (key _ (fun e => d1i e.symm)))
    · exact d01 ((key _ h0).symm.trans (key _ h1))

end DipoleInstance

/-! ## § VII. One object, two faces: `0` of `ℚ_[2]` as a step fixed point and as an asymptote -/

/-- `Statement:` `0` of `ℚ_[2]` under doubling on `OnePoint ℚ_[2]`. Value face: `0` steps only to
    itself in doubling's limit motion and in its reverse, has the least norm, and is the only point of
    that norm. Limit face: the field line `2 ^ (n + 1)` tends to `0`, is never `0`, its `cxQ2` climbs
    strictly through finite values, `cxQ2 0` is their supremum, and `cxQ2 0` is the greatest value of
    `cxQ2`.
    `Reading:` on `ℚ_[2]` the value face (least norm) and the limit face (greatest `cxQ2`, the
    valuation's `toNat` off `0`) are one order read backwards, `‖x‖ = 2 ^ (-x.valuation)`
    (`Padic.norm_eq_zpow_neg_valuation`): a change of coordinates, not a Kleene-type coincidence like
    `epsilon0_min_eq_max`. Exactly so on the unit ball `‖x‖ ≤ 1`, where valuations are `≥ 0`; off it
    `toNat` sends every negative valuation to `0`, so there `cxQ2` is constant and only coarsens the
    reversed norm order (the `example` below). The content is the asymptote: `0` is approached, never reached, through
    finite complexities climbing to it; `cx_zero_eq_iSup_of_tendsto` gives the supremum along every
    approach. In the ordinal chart the same shape runs from ⊥ of `Ordinal` up to ε₀
    (`epsilon0_eq_nfp_bot`); no identity. -/
theorem q2_zero_min_eq_max :
    ((limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).SelfOnlyAt
        (OnePoint.some 0) ∧
      (limitMotion (lmScale (2 : ℚ_[2]) two_ne_zero) (lmScale _ _).continuous).reverse.SelfOnlyAt
        (OnePoint.some 0) ∧
      IsLeast (Set.range (fun y : ℚ_[2] => ‖y‖)) ‖(0 : ℚ_[2])‖ ∧
      ∀ y : ℚ_[2], ‖y‖ = ‖(0 : ℚ_[2])‖ → y = 0) ∧
    (Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ (n + 1)) atTop (𝓝 0) ∧
      (∀ n : ℕ, (2 : ℚ_[2]) ^ (n + 1) ≠ 0) ∧
      StrictMono (fun n : ℕ => cxQ2 ((2 : ℚ_[2]) ^ (n + 1))) ∧
      (∀ n : ℕ, cxQ2 ((2 : ℚ_[2]) ^ (n + 1)) < ⊤) ∧
      cxQ2 0 = ⨆ n : ℕ, cxQ2 ((2 : ℚ_[2]) ^ (n + 1)) ∧
      IsGreatest (Set.range cxQ2) (cxQ2 0)) := by
  refine ⟨⟨lm_dbl_step_level.1, lm_dbl_step_level.2.2.1, ⟨⟨0, rfl⟩, ?_⟩, fun y h => by simpa using h⟩,
    ⟨(doubling_orbit_tendsto_zero (2 : ℚ_[2])).congr fun n => (pow_succ 2 n).symm,
     fun n => member_ne_floor (I := q2InfinitudeFloor) n,
     q2InfinitudeFloor.cx_member_strictMono,
     fun n => member_cx_lt_top (I := q2InfinitudeFloor) n,
     q2InfinitudeFloor.cx_floor_eq_iSup, ⟨⟨0, rfl⟩, ?_⟩⟩⟩
  · rintro _ ⟨y, rfl⟩; simp
  · rintro _ ⟨y, rfl⟩; rw [cxQ2_zero]; exact le_top

/-- `Statement:` `cxQ2` is `0` at `1` and at `2⁻¹`, two points of different norm. -/
example : cxQ2 (1 : ℚ_[2]) = 0 ∧ cxQ2 (2⁻¹ : ℚ_[2]) = 0 := by
  have h1 : (2⁻¹ : ℚ_[2]) = ((2 : ℚ_[2]) ^ 1)⁻¹ := by rw [pow_one]
  refine ⟨by simp [cxQ2], ?_⟩
  unfold cxQ2
  rw [ite_cond_eq_false _ _ (eq_false (inv_ne_zero two_ne_zero)), h1, Padic.valuation_inv,
    two_pow_valuation]
  rfl

/-! ## § VIII. The `PinnedLimit` role (`ZeroParadox/Die.lean` § XXIV) on the sphere `OnePoint ℚ_[2]` -/

/-- `Statement:` the preorder on the sphere lifted along `sNorm`. -/
noncomputable abbrev lmSphN : Preorder Sphere := Preorder.lift sNorm

/-- `Statement:` the preorder on the sphere lifted along `sNorm` into the order dual of `ℝ≥0∞`. -/
noncomputable abbrev lmSphV : Preorder Sphere := Preorder.lift (fun s => OrderDual.toDual (sNorm s))

/-- `Statement:` `sNorm z = ⊤ ↔ z = ∞`; both directions. -/
theorem lm_sNorm_eq_top (z : Sphere) : sNorm z = ⊤ ↔ z = OnePoint.infty := by
  induction z using OnePoint.rec with
  | infty => simp [sNorm]
  | coe x => simp [sNorm]

/-- `Statement:` `sNorm z = 0 ↔ z = 0`; both directions. -/
theorem lm_sNorm_eq_zero (z : Sphere) : sNorm z = 0 ↔ z = OnePoint.some 0 := by
  induction z using OnePoint.rec with
  | infty => simp [sNorm]
  | coe x => simp [sNorm]

/-- `Statement:` for `c ≠ 0, 1`, `lmScale c` fixes exactly `0` of `ℚ_[2]` and `∞`. -/
theorem lm_scale_fixed_iff (c : ℚ_[2]) (hc : c ≠ 0) (hc1 : c ≠ 1) (z : Sphere) :
    lmScale c hc z = z ↔ z = OnePoint.some 0 ∨ z = OnePoint.infty := by
  induction z using OnePoint.rec with
  | infty => simp [lm_scale_infty]
  | coe x =>
    rw [lm_scale_some]
    constructor
    · intro h
      left
      have h' : c * x = x := OnePoint.coe_injective h
      have : (c - 1) * x = 0 := by rw [sub_mul, h', one_mul, sub_self]
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd (sub_eq_zero.1 h0) hc1
      · rw [h0]
    · rintro (h | h)
      · rw [OnePoint.coe_injective h, mul_zero]
      · exact absurd h (OnePoint.coe_ne_infty x)

/-- `Statement:` in `lmSphV`, `∞` is least and nothing else is below it. -/
theorem lm_sphV_infty_min : @IsBot Sphere lmSphV.toLE OnePoint.infty ∧
    ∀ z : Sphere, @LE.le Sphere lmSphV.toLE z OnePoint.infty → z = OnePoint.infty := by
  refine ⟨fun z => ?_, fun z hz => ?_⟩
  · show sNorm z ≤ sNorm OnePoint.infty; simp [sNorm]
  · change sNorm OnePoint.infty ≤ sNorm z at hz
    exact (lm_sNorm_eq_top z).1 (top_le_iff.1 (by simpa [sNorm] using hz))

/-- `Statement:` in `lmSphN`, `0` of `ℚ_[2]` is least and nothing else is below it. -/
theorem lm_sphN_zero_min : @IsBot Sphere lmSphN.toLE (OnePoint.some 0) ∧
    ∀ z : Sphere, @LE.le Sphere lmSphN.toLE z (OnePoint.some 0) → z = OnePoint.some 0 := by
  refine ⟨fun z => ?_, fun z hz => ?_⟩
  · show sNorm (OnePoint.some 0) ≤ sNorm z; simp [sNorm]
  · change sNorm z ≤ sNorm (OnePoint.some 0) at hz
    exact (lm_sNorm_eq_zero z).1 (le_antisymm (by simpa [sNorm] using hz) bot_le)

/-- `Statement:` for every `c ≠ 0`, every sequence `s` and every point `p` of the sphere, `p` occupies
    `PinnedLimit (lmScale c) s` in neither `lmSphV` nor `lmSphN`. -/
theorem lm_sphere_pinnedLimit_empty (c : ℚ_[2]) (hc : c ≠ 0) (s : ℕ → Sphere) (p : Sphere) :
    ¬ @PinnedLimit Sphere lmSphV (lmScale c hc) s p ∧ ¬ @PinnedLimit Sphere lmSphN (lmScale c hc) s p :=
  ⟨@not_pinnedLimit_of_fixed_floor Sphere lmSphV _ _ lm_sphV_infty_min.1 lm_sphV_infty_min.2
      (lm_scale_infty c hc) s p,
    @not_pinnedLimit_of_fixed_floor Sphere lmSphN _ _ lm_sphN_zero_min.1 lm_sphN_zero_min.2
      (by rw [lm_scale_some, mul_zero]) s p⟩

/-- `Statement:` for `x ≠ 0` in `ℚ_[2]`, the doubling orbit of `x` is a run of doubling, `0` of
    `ℚ_[2]` occupies `PinnedLimitAbove` of doubling along it in `lmSphV`, and `0` is the least fixed
    point of doubling strictly above `∞` in `lmSphV`. -/
theorem lm_sphere_dbl_pinnedLimitAbove (x : ℚ_[2]) (hx : x ≠ 0) :
    (Motion.ofFun (lmScale (2 : ℚ_[2]) two_ne_zero)).IsRun
        (fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some x)) ∧
    @PinnedLimitAbove Sphere lmSphV (lmScale (2 : ℚ_[2]) two_ne_zero)
      (fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some x)) (OnePoint.some 0) ∧
    @IsLeast Sphere lmSphV.toLE
      {z | lmScale (2 : ℚ_[2]) two_ne_zero z = z ∧ @LT.lt Sphere lmSphV.toLT OnePoint.infty z}
      (OnePoint.some 0) := by
  letI : Preorder Sphere := lmSphV
  have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
  have hfix := lm_scale_fixed_iff (2 : ℚ_[2]) two_ne_zero (by norm_num)
  have hst : ∀ n, (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some x) =
      OnePoint.some ((2 : ℚ_[2]) ^ n * x) := fun n => lm_scale_iterate_some _ _ x n
  have hnorm : ∀ n, ‖(2 : ℚ_[2]) ^ n * x‖ = (2⁻¹ : ℝ) ^ n * ‖x‖ := fun n => by
    rw [norm_mul, norm_pow, h2]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have cmp : ∀ a b : ℚ_[2], (OnePoint.some a : Sphere) ≤ OnePoint.some b ↔ ‖b‖ ≤ ‖a‖ :=
    fun a b => by
      show sNorm (OnePoint.some b) ≤ sNorm (OnePoint.some a) ↔ _
      simp only [sNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  have infle : ∀ a : ℚ_[2], ¬ (OnePoint.some a : Sphere) ≤ OnePoint.infty := fun a h => by
    change sNorm OnePoint.infty ≤ sNorm (OnePoint.some a) at h
    simp [sNorm] at h
  refine ⟨fun n => (Function.iterate_succ_apply' _ _ _), ?_⟩
  rw [show (fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some x)) =
    fun n => OnePoint.some ((2 : ℚ_[2]) ^ n * x) from funext hst]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨n, rfl⟩
    rw [cmp]; simp
  · intro b hb
    induction b using OnePoint.rec with
    | infty => exact absurd (hb ⟨0, rfl⟩) (infle _)
    | coe y =>
      rw [cmp]
      have hle : ∀ n, ‖y‖ ≤ (2⁻¹ : ℝ) ^ n * ‖x‖ := fun n => by
        have := hb ⟨n, rfl⟩; rw [cmp, hnorm] at this; exact this
      have ht : Filter.Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n * ‖x‖) Filter.atTop (nhds 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2⁻¹ : ℝ) < 1)).mul_const ‖x‖
      have : ‖y‖ ≤ 0 := ge_of_tendsto' ht hle
      simpa using this
  · rintro ⟨n, hn⟩
    exact padic_orbit_never_reaches_zero x hx n (OnePoint.coe_injective hn)
  · exact (hfix _).2 (Or.inl rfl)
  · rw [cmp]; simp
  · rintro z ⟨hz, hz0⟩
    rcases (hfix z).1 hz with rfl | rfl
    · exact le_rfl
    · exact absurd hz0 (infle _)
  · intro m n hmn
    show (OnePoint.some _ : Sphere) ≤ OnePoint.some _
    rw [cmp, hnorm, hnorm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn)
      hxpos.le
  · refine ⟨⟨(hfix _).2 (Or.inl rfl), lt_iff_le_not_ge.2 ⟨lm_sphV_infty_min.1 _, fun h => ?_⟩⟩, ?_⟩
    · exact OnePoint.coe_ne_infty 0 (lm_sphV_infty_min.2 _ h)
    · rintro z ⟨hz, hlt⟩
      rcases (hfix z).1 hz with rfl | rfl
      · exact le_rfl
      · exact absurd hlt (lt_irrefl _)

/-- `Statement:` for `x ≠ 0` in `ℚ_[2]`, the halving orbit of `x` is a run of halving, `∞` occupies
    `PinnedLimitAbove` of halving along it in `lmSphN`, and `∞` is the least fixed point of halving
    strictly above `0` of `ℚ_[2]` in `lmSphN`. -/
theorem lm_sphere_hlv_pinnedLimitAbove (x : ℚ_[2]) (hx : x ≠ 0) :
    (Motion.ofFun (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))).IsRun
        (fun n => (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))^[n] (OnePoint.some x)) ∧
    @PinnedLimitAbove Sphere lmSphN (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))
      (fun n => (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))^[n] (OnePoint.some x))
      OnePoint.infty ∧
    @IsLeast Sphere lmSphN.toLE
      {z | lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero) z = z ∧
        @LT.lt Sphere lmSphN.toLT (OnePoint.some 0) z}
      OnePoint.infty := by
  letI : Preorder Sphere := lmSphN
  have h2' : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
  have h2 : ‖(2⁻¹ : ℚ_[2])‖ = 2 := by rw [norm_inv, h2', inv_inv]
  have hfix := lm_scale_fixed_iff (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero) (by norm_num)
  have hst : ∀ n, (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))^[n] (OnePoint.some x) =
      OnePoint.some ((2⁻¹ : ℚ_[2]) ^ n * x) := fun n => lm_scale_iterate_some _ _ x n
  have hnorm : ∀ n, ‖(2⁻¹ : ℚ_[2]) ^ n * x‖ = (2 : ℝ) ^ n * ‖x‖ := fun n => by
    rw [norm_mul, norm_pow, h2]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have cmp : ∀ a b : ℚ_[2], (OnePoint.some a : Sphere) ≤ OnePoint.some b ↔ ‖a‖ ≤ ‖b‖ :=
    fun a b => by
      show sNorm (OnePoint.some a) ≤ sNorm (OnePoint.some b) ↔ _
      simp only [sNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm]
  have letop : ∀ z : Sphere, z ≤ OnePoint.infty := fun z => by
    show sNorm z ≤ sNorm OnePoint.infty; simp [sNorm]
  refine ⟨fun n => (Function.iterate_succ_apply' _ _ _), ?_⟩
  rw [show (fun n => (lmScale (2⁻¹ : ℚ_[2]) (inv_ne_zero two_ne_zero))^[n] (OnePoint.some x)) =
    fun n => OnePoint.some ((2⁻¹ : ℚ_[2]) ^ n * x) from funext hst]
  refine ⟨⟨⟨fun _ _ => letop _, ?_⟩, ?_, ⟨⟨(hfix _).2 (Or.inr rfl), letop _⟩, ?_⟩, ?_⟩, ?_⟩
  · intro b hb
    induction b using OnePoint.rec with
    | infty => exact le_rfl
    | coe y =>
      exfalso
      have hle : ∀ n, (2 : ℝ) ^ n * ‖x‖ ≤ ‖y‖ := fun n => by
        have := hb ⟨n, rfl⟩; rw [cmp, hnorm] at this; exact this
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (‖y‖ / ‖x‖ + 1) (by norm_num : (1 : ℝ) < 2)
      have h3 := hle n
      rw [← le_div_iff₀ hxpos] at h3
      linarith
  · rintro ⟨n, hn⟩
    exact OnePoint.coe_ne_infty _ hn
  · rintro z ⟨hz, hz0⟩
    rcases (hfix z).1 hz with rfl | rfl
    · exfalso
      rw [cmp, norm_zero] at hz0
      exact absurd (norm_le_zero_iff.1 hz0) (by simpa using hx)
    · exact le_rfl
  · intro m n hmn
    show (OnePoint.some _ : Sphere) ≤ OnePoint.some _
    rw [cmp, hnorm, hnorm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hmn) hxpos.le
  · refine ⟨⟨(hfix _).2 (Or.inr rfl), lt_iff_le_not_ge.2 ⟨lm_sphN_zero_min.1 _, fun h => ?_⟩⟩, ?_⟩
    · exact OnePoint.coe_ne_infty 0 (lm_sphN_zero_min.2 _ h).symm
    · rintro z ⟨hz, hlt⟩
      rcases (hfix z).1 hz with rfl | rfl
      · exact absurd hlt (lt_irrefl _)
      · exact le_rfl

/-- `Statement:` CONTROL: for `x ≠ 0` in `ℚ_[2]`, the doubling orbit of `x` is not monotone in
    `lmSphN`. -/
theorem lm_sphere_dbl_norm_not_monotone (x : ℚ_[2]) (hx : x ≠ 0) :
    ¬ @Monotone ℕ Sphere _ lmSphN (fun n => (lmScale (2 : ℚ_[2]) two_ne_zero)^[n] (OnePoint.some x)) := by
  intro h
  have h01 := h (Nat.zero_le 1)
  change sNorm _ ≤ sNorm _ at h01
  simp only [Function.iterate_zero_apply, Function.iterate_one, lm_scale_some, sNorm,
    ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, norm_mul] at h01
  have h2 : ‖(2 : ℚ_[2])‖ = 2⁻¹ := by simpa using (Padic.norm_p (p := 2))
  rw [h2] at h01
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  linarith

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms lm_omegaLim_eq_omegaLimit
#print axioms lm_omegaLimit_of_tendsto
#print axioms lm_tendsto_of_omegaLimit
#print axioms limitRetraction
#print axioms lm_mem_limitRetraction_iff
#print axioms lm_omegaLim_of_mem
#print axioms lm_mem_iff_omegaLim
#print axioms lm_limitRetraction_idem
#print axioms limitMotion
#print axioms lm_limitMotion_step
#print axioms lm_isLanding_iff
#print axioms lm_upStepInvariant
#print axioms lm_isRun
#print axioms lm_arrives_of_step_eq
#print axioms lm_arrives_iff
#print axioms lmJumpMap
#print axioms lm_jumpMap_breaks_idem
#print axioms lm_tendsto_iff_arrival_or_closure
#print axioms lm_not_arrives_of_closure
#print axioms lmScale
#print axioms lm_scale_some
#print axioms lm_scale_infty
#print axioms lm_scale_iterate_some
#print axioms lm_not_arrives_infty
#print axioms lm_tendsto_zero_of_field
#print axioms lmHomOfConj
#print axioms lmIsoOfConj
#print axioms lmHomeoIsoOfConj
#print axioms lmHomeoIsoOfConj_toStrictIso
#print axioms lm_onePointInv_conj_scale
#print axioms lmHealedIso
#print axioms lm_healedIso_toFun
#print axioms lm_tendsto_infty_of_conj
#print axioms lmBareInvIso
#print axioms lm_torn_no_hom
#print axioms lm_negOrbit_no_limit
#print axioms lm_negOrbit_fails_die
#print axioms lm_q2_doubling_closure_at_zero
#print axioms lm_q2_halving_to_infty
#print axioms lm_q2_torn
#print axioms lm_real_half_tendsto
#print axioms lm_real_doubling_closure_at_infty
#print axioms lm_real_torn
#print axioms lmSinkOf
#print axioms lmDipole
#print axioms lmSinkOf.map
#print axioms lm_scale_cancel
#print axioms lm_hlv_step_reverse
#print axioms lm_dbl_sinkOf
#print axioms lm_hlv_sinkOf
#print axioms lm_q2_dipole
#print axioms lm_dbl_step_level
#print axioms lm_reverse_not_partner
#print axioms lm_fieldLine_is_members
#print axioms lm_real_dipole
#print axioms lm_real_dbl_zero_not_sink
#print axioms lm_id_no_sink
#print axioms q2_zero_min_eq_max
#print axioms lmSphN
#print axioms lmSphV
#print axioms lm_sNorm_eq_top
#print axioms lm_sNorm_eq_zero
#print axioms lm_scale_fixed_iff
#print axioms lm_sphV_infty_min
#print axioms lm_sphN_zero_min
#print axioms lm_sphere_pinnedLimit_empty
#print axioms lm_sphere_dbl_pinnedLimitAbove
#print axioms lm_sphere_hlv_pinnedLimitAbove
#print axioms lm_sphere_dbl_norm_not_monotone
end PurityCheck
