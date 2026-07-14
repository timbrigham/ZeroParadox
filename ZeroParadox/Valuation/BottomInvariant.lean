-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a first abstraction of the "invariant structure at the bottom" — a self-map with an invariant probability measure — instantiated by two already-proved dynamics (the ℤ_p odometer with Haar, and the Q₂ doubling attractor with the Dirac mass at the floor). Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicErgodic
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Reals.MarkovSpectralGap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Kernel.Invariance
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

/-- **A bottom with an invariant measure.** A self-map `f` of a measurable space together with an
    invariant Borel probability measure `μ` (`MeasurePreserving f μ μ`). The candidate universal
    shape: where a Lawvere fixed *point* is blocked, this weaker invariant may still exist. -/
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
    bottom — a NON-p-adic domain. (It is a parallel structure to `BottomInvariantMeasure`: `PMF` is
    Mathlib's finite-probability framework, `Measure` the continuous one. A single structure over
    Mathlib's general `MeasureTheory.Kernel` subsumes both — realized in § VI, `InvariantMarkovKernel`.) -/
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

/-! ## § VI — The unification: one structure over Mathlib's general `Kernel` -/

open ProbabilityTheory

/-- **The unified invariant-structure universal.** A Markov kernel `κ : Kernel X X` on a measurable
    space together with an invariant probability measure `μ` (`Kernel.Invariant κ μ`, i.e.
    `μ.bind κ = μ`). This is Mathlib's general kernel framework, so it subsumes BOTH earlier structures
    at once: a *deterministic* self-map is the Dirac kernel `Kernel.deterministic f`, and a finite
    *Markov* kernel is a genuine `Kernel`. All three faces below — the two continuous p-adic dynamics
    and the finite stochastic one — are now instances of this *one* structure. -/
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

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms odometerBIM
#print axioms attractorBIM
#print axioms odometer_sameShape
#print axioms attractor_sameShape
#print axioms markovBIK
#print axioms markov_sameShape
#print axioms odometerIMK
#print axioms attractorIMK
#print axioms markovIMK
end PurityCheck
