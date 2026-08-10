-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a first abstraction of the "invariant structure at the bottom" — a self-map with an invariant probability measure — instantiated by two already-proved dynamics (the ℤ_p odometer with Haar, and the Q₂ doubling attractor with the Dirac mass at the floor). Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicErgodic
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Reals.MarkovSpectralGap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# A first universal: the bottom carries an invariant probability measure

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

A probe of the conjecture that the *weaker invariant* (an invariant measure / "same shape from
anywhere"), rather than a Lawvere fixed point, is the universal that recurs across the framework's
faces. This file abstracts the least common denominator that is uniformly provable so far:

`BottomInvariantMeasure X` bundles a self-map `f : X → X` with an invariant Borel probability measure
`μ` (`MeasurePreserving f μ μ`). It is instantiated by **two already-proved dynamics on two different
spaces**:
- `odometerBIM` — the odometer `x ↦ 1 + x` on `ℤ_p` with the Haar measure (the *spread* invariant;
  ergodic and minimal, see `PadicErgodic`).
- `attractorBIM` — the doubling map `x ↦ 2·x` on `Q₂` with the Dirac mass `δ₀` at the floor (the
  *concentrated* invariant; every orbit converges to `0`, see `PadicAttractor`).

The point of the probe: a "spread" invariant (Haar) and a "concentrated" invariant (δ₀) — opposite in
character — fit **one** structure. That is evidence the invariant-measure shape is genuinely universal
across these two dynamics, where the fixed-*point* shape is not (Cantor blocks a genuine one on the
valuation face). **Caveat on "universal":** the two `Measure`-based instances live on the framework's *valuation* face
(`ℤ_p`, `Q₂`) — within-domain evidence, two opposite p-adic dynamics. § V then carries the same idea to
a **genuinely different domain**: the stochastic / Markov bottom (`markovBIK`, finite Markov kernels
with a stationary distribution). That gives three faces across two domains. § VI then **unifies** them:
`InvariantMarkovKernel`, a single structure over Mathlib's general `MeasureTheory.Kernel`, of which all
three faces are instances (the two deterministic p-adic faces via `Kernel.deterministic`, the
stochastic face as a genuine Markov kernel) — so the universal is now *one* structure, not two parallel
ones. The order / category / set-theory faces are not measure-theoretic and fall outside this
abstraction entirely.

**Honest scope / the fence.** This is the EXISTENCE level only — each face carries *an* invariant
probability measure. The *strong* uniform statement — that the measure is UNIQUE (unique ergodicity),
so that *every* orbit sees the same shape at the right rate — is not proved here: Mathlib has no
unique-ergodicity API. What is separately proved per face is the topological "same shape from
anywhere": the odometer's orbits are all dense (`denseRange_odometer_orbit`) and the attractor's orbits
all converge to the floor (`doubling_orbit_tendsto_zero`). Uniqueness across all faces, and additional
faces (computability, category), remain OPEN — this file is the first two data points, not the
universal in full.

`Classical.choice` is inherited from Mathlib's measure libraries (a dependency, not a new commitment).
-/

namespace ZeroParadox

open MeasureTheory

/-! ## § I — The abstraction -/

/-! ### NO-GO gauge for the three structures in this file — verdict at each declaration.

On a NONEMPTY carrier each is inhabited by the identity dynamics (measured 2026-08-09: `f := id`;
`κ := PMF.pure`; `κ := Kernel.id`). ⚠ **All three exclude the EMPTY carrier** by one argument — each
carries a probability measure or a `PMF`, and neither exists on `Fin 0`. So nonemptiness of `X` IS a
requirement all three impose, and it is generic rather than distinguishing.

**Beyond that they are BUNDLES of a dynamical system.** The content is in *which* `f` or `κ` a value
supplies (`odometerIMK`, `attractorIMK`, `markovIMK`). Cite the witness. -/

/-- **A bottom with an invariant measure.** A self-map `f` of a measurable space together with an
    invariant Borel probability measure `μ` (`MeasurePreserving f μ μ`). The candidate universal
    shape: where a Lawvere fixed *point* is blocked, this weaker invariant may still exist.
    NO-GO: `BottomInvariantMeasure` is inhabited on any nonempty `X` by `f := id`, and empty on
    `Fin 0` (no probability measure there) — a generic obstruction, not a distinguishing one. -/
structure BottomInvariantMeasure (X : Type*) [MeasurableSpace X] where
  /-- the dynamics -/
  f : X → X
  /-- the invariant measure -/
  μ : Measure X
  /-- it is a probability measure -/
  isProbability : IsProbabilityMeasure μ
  /-- the dynamics preserves it -/
  preserving : MeasurePreserving f μ μ

/-! ## § II — Face 1: the odometer on `ℤ_p` (the spread invariant, Haar) -/

variable {p : ℕ} [Fact p.Prime]

/-- The odometer face: `(ℤ_p, x ↦ 1 + x, Haar)`. The invariant measure is Haar — the *spread*
    invariant; its dynamics are ergodic (`ergodic_odometer`) and minimal
    (`denseRange_odometer_orbit`). -/
noncomputable def odometerBIM : BottomInvariantMeasure ℤ_[p] where
  f := (1 + ·)
  μ := haarZp (p := p)
  isProbability := inferInstance
  preserving := measurePreserving_odometer 1

/-! ## § III — Face 2: the doubling attractor on `Q₂` (the concentrated invariant, δ₀) -/

noncomputable instance : MeasurableSpace Q₂ := borel _

instance : BorelSpace Q₂ := ⟨rfl⟩

/-- The attractor face: `(Q₂, x ↦ 2·x, δ₀)`. The invariant measure is the Dirac mass at the floor `0`
    — the *concentrated* invariant; every orbit converges to `0` (`doubling_orbit_tendsto_zero`). `δ₀`
    is invariant because the doubling map fixes `0`. -/
noncomputable def attractorBIM : BottomInvariantMeasure Q₂ where
  f := (2 * ·)
  μ := Measure.dirac 0
  isProbability := inferInstance
  preserving := by
    have hmeas : Measurable (fun x : Q₂ => 2 * x) := by fun_prop
    exact ⟨hmeas, by rw [Measure.map_dirac' hmeas]; simp⟩

/-! ## § IV — Same shape from anywhere (the asymptotic universal) -/

open Filter Topology

/-- The **ω-limit set** of the orbit of `x` under `f`: the points the orbit accumulates at cofinally,
    `⋂ N, closure {fⁿ x | n ≥ N}`. This is Mathlib's `omegaLimit` (`Mathlib/Dynamics/OmegaLimit.lean`)
    specialized to the ℕ-orbit / `atTop` filter / singleton start; rolled lightweight here to avoid the
    flow / monoid-action API. -/
def omegaLim {X : Type*} [TopologicalSpace X] (f : X → X) (x : X) : Set X :=
  ⋂ N : ℕ, closure (Set.range fun n : ℕ => f^[N + n] x)

/-- **Same shape from anywhere.** There is a set `S` that is the ω-limit of *every* orbit — the
    asymptotic behaviour is independent of the starting point. This is the topological form of
    "start anywhere, get the same shape." -/
def SameShapeFromAnywhere {X : Type*} [TopologicalSpace X] (f : X → X) : Prop :=
  ∃ S : Set X, ∀ x, omegaLim f x = S

/-- The odometer has the same shape from anywhere: every orbit is dense, so its ω-limit is the whole
    space `univ`. -/
theorem odometer_sameShape : SameShapeFromAnywhere (fun x : ℤ_[p] => 1 + x) := by
  refine ⟨Set.univ, fun x => ?_⟩
  have hN : ∀ N : ℕ,
      closure (Set.range fun n : ℕ => (fun y : ℤ_[p] => 1 + y)^[N + n] x) = Set.univ := by
    intro N
    have hiter : (fun n : ℕ => (fun y : ℤ_[p] => 1 + y)^[N + n] x)
        = (fun n : ℕ => (x + (N : ℤ_[p])) + (n : ℤ_[p])) := by
      funext n
      rw [add_left_iterate]
      push_cast [nsmul_eq_mul]
      ring
    rw [hiter]
    exact (denseRange_odometer_orbit (x + (N : ℤ_[p]))).closure_eq
  simp only [omegaLim, hN, Set.iInter_univ]

/-- The doubling attractor has the same shape from anywhere: every orbit converges to the floor `0`,
    so its ω-limit is `{0}`. -/
theorem attractor_sameShape : SameShapeFromAnywhere (fun x : Q₂ => 2 * x) := by
  refine ⟨{0}, fun x => ?_⟩
  have hiter : ∀ N n : ℕ, (fun y : Q₂ => 2 * y)^[N + n] x = (2 : Q₂) ^ (N + n) * x := by
    intro N n; rw [mul_left_iterate]
  -- every orbit point in the N-tail has norm ≤ ‖2‖^N · ‖x‖
  have hbound : ∀ N n : ℕ, ‖(fun y : Q₂ => 2 * y)^[N + n] x‖ ≤ ‖(2 : Q₂)‖ ^ N * ‖x‖ := by
    intro N n
    rw [hiter, norm_mul, norm_pow, pow_add]
    have h2 : ‖(2 : Q₂)‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (le_of_lt doubling_norm_lt_one)
    have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
    nlinarith [pow_nonneg (norm_nonneg (2 : Q₂)) N, mul_nonneg (pow_nonneg (norm_nonneg (2:Q₂)) N) hx]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
  · -- 0 ∈ ω-limit: it is the limit of every N-tail, hence in its closure
    rw [omegaLim, Set.mem_iInter]
    intro N
    have htend : Tendsto (fun n : ℕ => (fun y : Q₂ => 2 * y)^[N + n] x) atTop (𝓝 0) := by
      have h := (doubling_orbit_tendsto_zero x).comp (tendsto_add_atTop_nat N)
      simpa [hiter, Function.comp, add_comm] using h
    exact mem_closure_of_tendsto htend (Filter.Eventually.of_forall fun _ => Set.mem_range_self _)
  · -- uniqueness: y in every N-tail closure ⇒ ‖y‖ ≤ ‖2‖^N‖x‖ ∀N ⇒ y = 0
    intro y hy
    rw [omegaLim, Set.mem_iInter] at hy
    have hyN : ∀ N : ℕ, ‖y‖ ≤ ‖(2 : Q₂)‖ ^ N * ‖x‖ := by
      intro N
      have hsub : closure (Set.range fun n : ℕ => (fun z : Q₂ => 2 * z)^[N + n] x)
          ⊆ Metric.closedBall 0 (‖(2 : Q₂)‖ ^ N * ‖x‖) := by
        apply closure_minimal _ Metric.isClosed_closedBall
        rintro _ ⟨n, rfl⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hbound N n
      have hmem := hsub (hy N)
      rwa [Metric.mem_closedBall, dist_zero_right] at hmem
    have htend0 : Tendsto (fun N : ℕ => ‖(2 : Q₂)‖ ^ N * ‖x‖) atTop (𝓝 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (2 : Q₂)) doubling_norm_lt_one
      simpa using h.mul_const ‖x‖
    have hle : ‖y‖ ≤ 0 := ge_of_tendsto htend0 (Filter.Eventually.of_forall hyN)
    simpa using le_antisymm hle (norm_nonneg y)

/-! ## § V — The kernel generalization: a genuinely different (stochastic) domain -/

/-- **A bottom with an invariant DISTRIBUTION** — the stochastic sibling of `BottomInvariantMeasure`.
    A Markov kernel `κ : X → PMF X` on a finite state space together with a *stationary* distribution
    `μ` (`μ.bind κ = μ`: one Markov step leaves `μ` invariant). This reaches the framework's stochastic
    bottom — a NON-p-adic domain. (Parallel to `BottomInvariantMeasure`: `PMF` is Mathlib's
    finite-probability framework, `Measure` the continuous one; § VI's `InvariantMarkovKernel`
    subsumes both.) NO-GO: `BottomInvariantKernel` is inhabited on any nonempty `X` by
    `κ := PMF.pure`, and empty on `Fin 0` (`bottomInvariantKernel_fin_zero_empty`) — generic. -/
structure BottomInvariantKernel (X : Type*) [Fintype X] where
  /-- the Markov kernel -/
  κ : X → PMF X
  /-- the stationary distribution -/
  μ : PMF X
  /-- one Markov step leaves `μ` invariant -/
  stationary : μ.bind κ = μ

/-- The **stochastic (Markov) face**: the full-mixing doubly-stochastic kernel on `Fin 2`
    (`MarkovSpectralGap.fullMix`: every state ↦ the uniform distribution) with the uniform
    distribution as its stationary law. A non-p-adic instance of the invariant-structure universal,
    in a third domain (finite stochastic dynamics). -/
noncomputable def markovBIK : BottomInvariantKernel (Fin 2) where
  κ := fullMix
  μ := PMF.uniformOfFintype (Fin 2)
  stationary := by unfold fullMix; exact PMF.bind_const _ _

/-- **Stochastic same shape from anywhere.** From *every* starting distribution, one step of the
    full-mixing kernel reaches the uniform stationary law — the stochastic form of "start anywhere,
    get the same shape." -/
theorem markov_sameShape (μ : PMF (Fin 2)) : μ.bind fullMix = PMF.uniformOfFintype (Fin 2) := by
  unfold fullMix; exact PMF.bind_const _ _

/-- **`Statement:` `Fin 0` carries no `BottomInvariantKernel`** — no `PMF` on the empty type. The
    proved instance of the generic obstruction; the other two fail the same way. -/
theorem bottomInvariantKernel_fin_zero_empty : IsEmpty (BottomInvariantKernel (Fin 0)) :=
  ⟨fun B => by have h := B.μ.tsum_coe; simp at h⟩

/-! ## § VI — The unification: one structure over Mathlib's general `Kernel` -/

open ProbabilityTheory

/-- **The unified invariant-structure universal.** A Markov kernel `κ : Kernel X X` on a measurable
    space together with an invariant probability measure `μ` (`Kernel.Invariant κ μ`, i.e.
    `μ.bind κ = μ`). This is Mathlib's general kernel framework, so it subsumes BOTH earlier structures
    at once: a *deterministic* self-map is the Dirac kernel `Kernel.deterministic f`, and a finite
    *Markov* kernel is a genuine `Kernel`. All three faces below — the two continuous p-adic dynamics
    and the finite stochastic one — are now instances of this *one* structure.
    NO-GO: `InvariantMarkovKernel` is inhabited on any nonempty `X` by `κ := Kernel.id`, and empty on
    `Fin 0` (no probability measure there) — generic, not distinguishing. -/
structure InvariantMarkovKernel (X : Type*) [MeasurableSpace X] where
  /-- the Markov kernel (transition dynamics) -/
  κ : Kernel X X
  /-- it is a Markov (probability) kernel -/
  markov : IsMarkovKernel κ
  /-- the invariant law -/
  μ : Measure X
  /-- it is a probability measure -/
  isProb : IsProbabilityMeasure μ
  /-- the law is invariant: one step leaves it unchanged -/
  invariant : Kernel.Invariant κ μ

private theorem measurable_odometer_map : Measurable ((1 : ℤ_[p]) + ·) := by fun_prop

/-- **Face 1** (valuation, deterministic): the odometer as a `Kernel.deterministic`, with Haar as its
    invariant law. Invariance reduces to `measurePreserving_odometer`. -/
noncomputable def odometerIMK : InvariantMarkovKernel ℤ_[p] where
  κ := Kernel.deterministic (1 + ·) measurable_odometer_map
  markov := inferInstance
  μ := haarZp (p := p)
  isProb := inferInstance
  invariant := by
    show (haarZp (p := p)).bind (Kernel.deterministic (1 + ·) measurable_odometer_map)
        = haarZp (p := p)
    rw [Measure.deterministic_comp_eq_map]
    exact (measurePreserving_odometer 1).map_eq

private theorem measurable_doubling_map : Measurable (fun x : Q₂ => 2 * x) := by fun_prop

/-- **Face 2** (valuation, deterministic): the doubling attractor as a `Kernel.deterministic`, with the
    Dirac mass `δ₀` as its invariant law. -/
noncomputable def attractorIMK : InvariantMarkovKernel Q₂ where
  κ := Kernel.deterministic (fun x => 2 * x) measurable_doubling_map
  markov := inferInstance
  μ := Measure.dirac 0
  isProb := inferInstance
  invariant := by
    show (Measure.dirac 0).bind (Kernel.deterministic (fun x : Q₂ => 2 * x) measurable_doubling_map)
        = Measure.dirac 0
    rw [Measure.deterministic_comp_eq_map]
    exact attractorBIM.preserving.map_eq

/-- **Face 3** (stochastic): the full-mixing Markov kernel as `Kernel.const`, with the uniform
    distribution as its stationary law. A genuine Markov kernel in the *same* structure as the two
    deterministic p-adic faces. -/
noncomputable def markovIMK : InvariantMarkovKernel (Fin 2) where
  κ := Kernel.const (Fin 2) ((PMF.uniformOfFintype (Fin 2)).toMeasure)
  markov := inferInstance
  μ := (PMF.uniformOfFintype (Fin 2)).toMeasure
  isProb := inferInstance
  invariant := by
    show ((PMF.uniformOfFintype (Fin 2)).toMeasure).bind
        (Kernel.const (Fin 2) ((PMF.uniformOfFintype (Fin 2)).toMeasure))
        = (PMF.uniformOfFintype (Fin 2)).toMeasure
    rw [Measure.const_comp, measure_univ, one_smul]

/-! ## § VII — Attracting kernels: convergence to the invariant law (the #2 ↔ #3 bridge)

`PadicAttractor.lean` flags the edge "#3-as-attractor → #2 (the Markov attractor)" as OPEN: the two
carry the *same descriptive vocabulary* but were never connected. § VI already made them instances of
one structure. Here we add the shared **attractor** property both discharge: from every starting
distribution, the n-step law converges (weakly) to the invariant law. The odometer (§ II) does NOT
have it — it equidistributes, it does not converge — so this predicate is exactly what separates the
attracting bottoms (#2, #3) from the equidistributing one.

This is standard Markov / ergodic theory (Mathlib's `Ergodic` family is a *different* notion —
invariance of one measure, not convergence of the law-orbit to it; unique ergodicity has no Mathlib
API). What is proved here is the shared *property* both faces discharge. It does NOT build the explicit
functor / measure-preserving *comparison* between the two systems that `PadicAttractor` also names as
missing — that half of the edge stays open. -/

open MeasureTheory Filter Topology

/-- One Markov step as a self-map of probability measures (`ρ ↦ ρ.bind κ`). -/
noncomputable def step {X : Type*} [MeasurableSpace X] (K : InvariantMarkovKernel X)
    (ρ : ProbabilityMeasure X) : ProbabilityMeasure X :=
  haveI := K.markov
  haveI : IsProbabilityMeasure (ρ : Measure X) := ρ.2
  ⟨(ρ : Measure X).bind K.κ, inferInstance⟩

/-- **Attracting kernel.** From *every* starting distribution, the n-step law converges (weakly) to
    the invariant law `μ`. The "attractor" property shared by the framework's #2 (Markov) and #3
    (p-adic) bottoms. -/
def AttractingKernel {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (K : InvariantMarkovKernel X) : Prop :=
  ∀ ν : ProbabilityMeasure X,
    Tendsto (fun n => (step K)^[n] ν) atTop (𝓝 (⟨K.μ, K.isProb⟩ : ProbabilityMeasure X))

/-- **Face #3** (p-adic): the doubling attractor is attracting — from any law, the n-step law → δ₀. -/
theorem attracting_attractor : AttractingKernel attractorIMK := by
  intro ν
  -- one step of this kernel is "push forward by the doubling map"
  have hstepmap : ∀ ρ : ProbabilityMeasure Q₂,
      (step attractorIMK ρ : Measure Q₂) = (ρ : Measure Q₂).map (fun x => 2 * x) := by
    intro ρ
    show (ρ : Measure Q₂).bind (Kernel.deterministic (fun x : Q₂ => 2 * x) measurable_doubling_map)
        = (ρ : Measure Q₂).map (fun x => 2 * x)
    exact Measure.deterministic_comp_eq_map measurable_doubling_map
  -- the n-step law is `ν` pushed forward by the n-fold doubling
  have hiter : ∀ n, ((step attractorIMK)^[n] ν : Measure Q₂)
      = (ν : Measure Q₂).map ((fun x : Q₂ => 2 * x)^[n]) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', hstepmap, ih,
          Measure.map_map measurable_doubling_map (measurable_doubling_map.iterate k),
          ← Function.iterate_succ']
  -- weak convergence, tested against bounded continuous functions
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  show Tendsto (fun n => ∫ x, f x ∂((step attractorIMK)^[n] ν : Measure Q₂)) atTop
      (𝓝 (∫ x, f x ∂(Measure.dirac (0 : Q₂))))
  rw [integral_dirac]
  -- the per-`f` integral converges to `f 0`
  have horbit : ∀ x : Q₂, Tendsto (fun n => (fun y : Q₂ => 2 * y)^[n] x) atTop (𝓝 0) := by
    intro x
    have h : (fun n => (fun y : Q₂ => 2 * y)^[n] x) = (fun n => (2 : Q₂) ^ n * x) := by
      funext n; rw [mul_left_iterate]
    rw [h]; exact doubling_orbit_tendsto_zero x
  have heq : ∀ n, ∫ x, f x ∂((step attractorIMK)^[n] ν : Measure Q₂)
      = ∫ x, f ((fun y : Q₂ => 2 * y)^[n] x) ∂(ν : Measure Q₂) := by
    intro n
    rw [hiter, integral_map (measurable_doubling_map.iterate n).aemeasurable
      f.continuous.aestronglyMeasurable]
  simp only [heq]
  have hdom : Tendsto (fun n => ∫ x, f ((fun y : Q₂ => 2 * y)^[n] x) ∂(ν : Measure Q₂)) atTop
      (𝓝 (∫ _x, f (0 : Q₂) ∂(ν : Measure Q₂))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (f.continuous.measurable.comp (measurable_doubling_map.iterate n)).aestronglyMeasurable
    · exact integrable_const _
    · intro n; filter_upwards with x using f.norm_coe_le_norm _
    · filter_upwards with x using f.continuous.continuousAt.tendsto.comp (horbit x)
  simpa using hdom

/-- Discrete topology on `Fin 2`, so `ProbabilityMeasure (Fin 2)` carries the weak topology. -/
instance : TopologicalSpace (Fin 2) := ⊥
instance : OpensMeasurableSpace (Fin 2) := ⟨le_top⟩

/-- **Face #2** (stochastic): the full-mixing Markov kernel is attracting — from any law, the n-step
    law reaches uniform (in one step, then stays). -/
theorem attracting_markov : AttractingKernel markovIMK := by
  intro ν
  have hstep : ∀ ρ : ProbabilityMeasure (Fin 2),
      step markovIMK ρ = ⟨markovIMK.μ, markovIMK.isProb⟩ := by
    intro ρ
    apply Subtype.ext
    show (ρ : Measure (Fin 2)).bind
        (Kernel.const (Fin 2) ((PMF.uniformOfFintype (Fin 2)).toMeasure))
        = (PMF.uniformOfFintype (Fin 2)).toMeasure
    haveI : IsProbabilityMeasure (ρ : Measure (Fin 2)) := ρ.2
    rw [Measure.const_comp, measure_univ, one_smul]
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Function.iterate_succ_apply']
  exact hstep _

/-! ## § VIII — Attracting ⟹ unique invariant law

Mathlib has no general unique-ergodicity API, but for an *attracting* kernel uniqueness is free: if the
n-step law converges to `μ` from every start, any invariant law `ρ` has a constant orbit (`= ρ`) that
also converges to `μ`, so `ρ = μ` by uniqueness of limits (the weak topology is Hausdorff). This gives
the attracting bottoms (#2, #3) a proved-*unique* invariant law — the strong ergodic conclusion,
obtained from the attracting structure rather than the missing library API. -/

/-- **An attracting kernel has a unique invariant probability law.** Any `ρ` fixed by one step equals
    the invariant law `μ`. -/
theorem attracting_unique_invariant {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [T2Space (ProbabilityMeasure X)]
    (K : InvariantMarkovKernel X) (hK : AttractingKernel K)
    {ρ : ProbabilityMeasure X} (hρ : step K ρ = ρ) :
    ρ = ⟨K.μ, K.isProb⟩ := by
  have hconst : ∀ n, (step K)^[n] ρ = ρ := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hρ]
  have h1 : Tendsto (fun n => (step K)^[n] ρ) atTop (𝓝 ρ) := by
    simp only [hconst]; exact tendsto_const_nhds
  exact tendsto_nhds_unique h1 (hK ρ)

/-- Uniqueness of the invariant law for face #3 (the p-adic doubling attractor): `δ₀`. -/
theorem attractor_unique_invariant {ρ : ProbabilityMeasure Q₂}
    (hρ : step attractorIMK ρ = ρ) : ρ = ⟨attractorIMK.μ, attractorIMK.isProb⟩ :=
  attracting_unique_invariant attractorIMK attracting_attractor hρ

/-- Uniqueness of the invariant law for face #2 (the full-mixing Markov kernel): uniform. -/
theorem markov_unique_invariant {ρ : ProbabilityMeasure (Fin 2)}
    (hρ : step markovIMK ρ = ρ) : ρ = ⟨markovIMK.μ, markovIMK.isProb⟩ :=
  attracting_unique_invariant markovIMK attracting_markov hρ

/-! ## § IX — The odometer is NOT attracting (the two modes are genuinely distinct)

`AttractingKernel` is not vacuous: the odometer fails it. Starting from a point mass `δ₀`, the orbit is
`δ_{↑n}` — always a point mass, wandering densely, never spreading — so it cannot converge to the
non-atomic Haar law. Formally: the point masses form a compact (`ℤ_p` compact) hence closed set that
Haar does not belong to. This proves the equidistributing bottom (odometer) is a genuinely different
dynamical mode from the attracting bottoms (#2, #3): "same shape from anywhere" splits into *converge
to the law* (attracting) versus *equidistribute to it* (ergodic/minimal), and they do not coincide. -/

/-- **The odometer is not an attracting kernel.** Its invariant (Haar) is not a global attractor of
    the law-orbit — point masses stay point masses and never converge to Haar. -/
theorem odometer_not_attracting : ¬ AttractingKernel (odometerIMK (p := p)) := by
  intro hattr
  -- the law-orbit from `δ₀` is `δ_{↑n}` (deterministic odometer on point masses)
  have hstepdp : ∀ x : ℤ_[p], step odometerIMK (MeasureTheory.diracProba x)
      = MeasureTheory.diracProba (1 + x) := by
    intro x
    apply Subtype.ext
    show (MeasureTheory.diracProba x : Measure ℤ_[p]).bind
        (Kernel.deterministic (1 + ·) measurable_odometer_map) = Measure.dirac (1 + x)
    rw [Measure.deterministic_comp_eq_map]
    show (Measure.dirac x).map (1 + ·) = Measure.dirac (1 + x)
    rw [Measure.map_dirac' measurable_odometer_map]
  have horbit : ∀ n : ℕ, (step odometerIMK)^[n] (MeasureTheory.diracProba 0)
      = MeasureTheory.diracProba ((n : ℤ_[p])) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih, hstepdp]
        push_cast
        ring_nf
  have hconv := hattr (MeasureTheory.diracProba 0)
  simp only [horbit] at hconv
  -- the limit lies in the (compact, hence closed) range of `diracProba`
  have hclosed : IsClosed (Set.range (MeasureTheory.diracProba : ℤ_[p] → ProbabilityMeasure ℤ_[p])) :=
    (isCompact_range continuous_diracProba).isClosed
  have hmem : (⟨haarZp (p := p), odometerIMK.isProb⟩ : ProbabilityMeasure ℤ_[p])
      ∈ Set.range (MeasureTheory.diracProba : ℤ_[p] → ProbabilityMeasure ℤ_[p]) :=
    hclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall fun _ => Set.mem_range_self _)
  obtain ⟨y, hy⟩ := hmem
  -- so Haar would equal a Dirac mass — impossible, Haar is non-atomic
  have hHaar : haarZp (p := p) = Measure.dirac y := by
    have := congrArg (fun m : ProbabilityMeasure ℤ_[p] => (m : Measure ℤ_[p])) hy
    simpa [MeasureTheory.diracProba] using this.symm
  -- Haar is odometer-invariant, so `δ_y = δ_{1+y}`, forcing `1 = 0`
  have hinv : (haarZp (p := p)).map (1 + ·) = haarZp (p := p) := (measurePreserving_odometer 1).map_eq
  rw [hHaar, Measure.map_dirac' measurable_odometer_map] at hinv
  have hyy : (1 : ℤ_[p]) + y = y := dirac_eq_dirac_iff.mp hinv
  simp at hyy

/-! ## § X — A NO-GO in one direction: no measure-preserving map carries the concentrated invariant
onto the spread one

`PadicAttractor.lean` names the *explicit measure-preserving comparison* between the two dynamical
systems — #3 (the p-adic doubling attractor) and #2 (the full-mixing Markov kernel) — as the remaining
open half of the bridge. § VII proved the two bottoms share the *property* (both attracting); here one
direction of the comparison is closed as an **obstruction**, not a construction. The two invariant laws
have incompatible shape: #3's invariant is the point mass `δ₀` (all mass concentrated at the floor `0`),
#2's is the uniform law (mass `2⁻¹` on each point, spread). A measure-preserving map must carry one
invariant onto the other by push-forward, and a point mass pushes forward only to a point mass — never
to a non-degenerate spread law. So no measure-preserving map exists in the concentrated→spread direction
(`no_mp_attractor_to_markov`).

The obstruction is asymmetric, and only this direction is proved. The *reverse* direction
(spread→concentrated) does admit a measure-preserving map — the degenerate constant collapse
`φ = const 0 : Fin 2 → Q₂`, for which `uniform.map φ = δ₀` — but a constant map destroys the dynamics and
is not a *faithful* comparison. So a faithful comparison in either direction is absent, but for different
reasons (concentrated→spread is impossible outright; spread→concentrated survives only as a degenerate
collapse), and a faithful reverse comparison remains OPEN.

This is analogous to the MC-1 situation, not a proof of it: the shared *shape* is real (both bottoms are
attracting), while a direct measure-preserving *identification* of their invariants is blocked in the
concentrated→spread direction. So the shared-property half of the bridge holds (§ VII); this direction of
the direct comparison provably cannot. -/

theorem no_mp_attractor_to_markov :
    ¬ ∃ φ : Q₂ → Fin 2, MeasurePreserving φ attractorIMK.μ markovIMK.μ := by
  rintro ⟨φ, hφ⟩
  -- a measure-preserving map pushes the invariant `δ₀` forward onto `markovIMK.μ`
  have hmap : (Measure.dirac (0 : Q₂)).map φ = markovIMK.μ := hφ.map_eq
  rw [Measure.map_dirac' hφ.measurable] at hmap
  -- evaluate both sides at the singleton `{φ 0}`: the point mass gives `1`, the uniform law gives `2⁻¹`
  have hlhs : (Measure.dirac (φ 0)) {φ 0} = 1 := by
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)]
  rw [hmap] at hlhs
  have hrhs : markovIMK.μ {φ 0} = (2 : ENNReal)⁻¹ := by
    show (PMF.uniformOfFintype (Fin 2)).toMeasure {φ 0} = (2 : ENNReal)⁻¹
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    norm_num
  rw [hrhs, ENNReal.inv_eq_one] at hlhs
  exact absurd hlhs (by norm_num)

end ZeroParadox

/-! ## § VII — The BOTH-AT-ONCE regime: a unit multiplier carries both characters

**Nothing here is new mathematics.** That multiplication by a unit fixes the origin and preserves norms is
elementary; the content is the **identification**, and it closes a gap this file's own § I leaves open.

§ II and § III exhibit the *spread* invariant (odometer, Haar) and the *concentrated* invariant (doubling
map, `δ₀`) — **on two different maps**. So the file shows the two characters are compatible with one
*structure*, never that one *dynamic* carries both. This section supplies a dynamic that does, and it is
already in the corpus: multiplication by a 2-adic **unit** (`Valuation/ContractionRate.lean`,
`unit_orbit_norm_const`, witnessed by `three_is_unit : ‖(3 : Q₂)‖ = 1`).

**The three regimes, decided by the valuation of the multiplier:**
| multiplier | orbit behaviour | invariant character |
|---|---|---|
| ideal, `‖c‖ < 1` (e.g. `×2` — the framework's own `selfApp` on `ℚ₂`, `q2_unique_fp`) | contracts to `0` | **concentrated only** |
| **unit, `‖u‖ = 1` (e.g. `×3`)** | norm constant on every orbit | **BOTH** |
| odometer `x ↦ 1 + x` | no fixed point, orbits dense | **spread only** |

**Why the unit row carries both.** It **fixes the floor** (`unitMul_fixes_floor`), so `δ₀` is invariant —
the concentrated character, proved below. And it **preserves every sphere** (`unitMul_norm_const`), so it is
a norm-preserving additive bijection of `ℤ_p` and therefore preserves the Haar probability measure — the
spread character.

**⚠ HONEST FENCE — the Haar half is NOT formalized here.** That an automorphism of a compact group
preserves its Haar probability measure is standard, but this file does not prove it for `unitMul`; only the
`δ₀` half is machine-checked below. Do not cite this section for the Haar claim.

**The standard result IS available in the pin, and this fence should be closable rather than merely
declared** (prior-art gate, 2026-07-30): `mulEquivHaarChar_eq_one_of_compactSpace`
(`Mathlib/MeasureTheory/Measure/Haar/MulEquivHaarChar.lean:136`,
`[CompactSpace G] (φ : G ≃ₜ* G) : mulEquivHaarChar φ = 1`), whose additive alias
`addEquivAddHaarChar_eq_one_of_compactSpace` is the one that applies here — `ℤ_p` is a compact additive
topological group and `unitMul u` is a topological additive automorphism for `u` a unit. So the gap is a
*build*, not an absence. Stated as adjacency, not as a claim: nothing below is proved from it.

**And note what sphere-preservation costs:** the spheres are invariant sets of intermediate measure, so
`unitMul` is **not ergodic** for Haar — it admits *many* invariant measures. That is the failure of unique
ergodicity, which § I flags as the strong statement it cannot prove (Mathlib has no unique-ergodicity API).
This section only *locates* a dynamic where the failure is visible; it proves neither the failure nor the
uniqueness. Reading: `.claude-local/notes/paradox_as_simultaneous_inversion_2026-07-30.md`. -/

section BothAtOnce
variable {p : ℕ} [Fact p.Prime]

/-- Multiplication by a `p`-adic unit **fixes the floor**, so the concentrated invariant `δ₀` is available
    to it. (True of any multiplier; stated here because it is one half of the both-at-once claim.) -/
theorem unitMul_fixes_floor (u : ℤ_[p]) : u * 0 = 0 := mul_zero u

/-- Multiplication by a **unit preserves every sphere**: the norm is unchanged. This is
    `ContractionRate.unit_orbit_norm_const` at one step, on `ℤ_[p]`. It is what makes the map
    Haar-preserving (not formalized here) and simultaneously **non-ergodic** — each sphere is an
    invariant set. -/
theorem unitMul_norm_const {u : ℤ_[p]} (hu : ‖u‖ = 1) (x : ℤ_[p]) : ‖u * x‖ = ‖x‖ := by
  rw [norm_mul, hu, one_mul]

/-- **The concentrated character, machine-checked.** Multiplication by `u` preserves the Dirac mass at the
    floor, because it fixes the floor. Together with `unitMul_norm_const` (the spread character's
    precondition) this is the both-at-once regime — one dynamic, two invariant characters.

    Prior art (cited, not reproved): the pushforward step is discharged by `simp`, which has BOTH
    Dirac pushforward lemmas registered — `MeasureTheory.Measure.map_dirac'`
    (`Mathlib/MeasureTheory/Measure/Dirac.lean:86`, `@[simp]`, takes `(hf : Measurable f)`) and the
    instance-based sibling `Measure.map_dirac` (`:224`, `@[simp]`, `[MeasurableSingletonClass _]`,
    no measurability hypothesis). Either closes it, because `unitMul` FIXES the point, so the
    pushforward returns the same Dirac.

    **⚠ This proof previously read `simpa using Measure.map_dirac hm 0`, and that term was
    ill-typed** — `map_dirac` takes one explicit argument, not two. It was silently discarded
    because `simpa`'s `simp` closed the goal unaided; the build's standing
    `try 'simp' instead of 'simpa'` warning was the only trace. Caught 2026-07-30 by the prior-art
    gate running the term through `lake env lean` instead of reading it — a probe beat a read. The
    proof is now plainly `simp`, so the docstring and the tactic agree. Note that `hm` is still
    needed: it is the first component of the `MeasurePreserving` structure.

    The same argument appears at `attractorBIM.preserving` above. This file's other `map_dirac'`
    uses rewrite in a hypothesis at `:473` and `:507`, and in the goal at `:448`. -/
theorem unitMul_preserving_dirac (u : ℤ_[p]) :
    MeasureTheory.MeasurePreserving (fun x : ℤ_[p] => u * x)
      (MeasureTheory.Measure.dirac 0) (MeasureTheory.Measure.dirac 0) := by
  have hm : Measurable (fun x : ℤ_[p] => u * x) := by fun_prop
  refine ⟨hm, ?_⟩
  simp

end BothAtOnce

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms unitMul_fixes_floor
#print axioms unitMul_norm_const
#print axioms unitMul_preserving_dirac
#print axioms odometer_not_attracting
#print axioms odometerBIM
#print axioms attractorBIM
#print axioms odometer_sameShape
#print axioms attractor_sameShape
#print axioms markovBIK
#print axioms markov_sameShape
#print axioms bottomInvariantKernel_fin_zero_empty
#print axioms odometerIMK
#print axioms attractorIMK
#print axioms markovIMK
#print axioms attracting_attractor
#print axioms attracting_markov
#print axioms attracting_unique_invariant
#print axioms attractor_unique_invariant
#print axioms markov_unique_invariant
#print axioms no_mp_attractor_to_markov
end PurityCheck
