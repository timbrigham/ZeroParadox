import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Tactic

/-!
# ZP-C: Information Theory

## Engineer's Take

ZPC doesn't build on ZPA or ZPB. It just follows the same conceptual ground.
Each state can be represented by a distribution of probability. All probability
exists either on null or all on the first state, where all mass exists. We're
then looking at the way that the distribution between the two of them lays out
mathematically. Specifically, this comes back to log two or exactly one bit,
which is the information distance between existence and nonexistence. The deeper
that you go requires more information. Just like you would in computer
programming. You need n bits to describe your position if you're n steps away.
The null state is the limit in the hierarchy. Basically infinite depth. The
surprisal isn't finite. You cannot describe it with any fixed number of bits.
There's no finite external description. No limited number of entries covers an
infinite value. L-RUN and TQ-IH look at this like a machine. An initial
configuration and when it's running. Crossing from the initial to the running is
a state change in and of itself. It's a non-null value. You cannot execute
without that crossing having occurred.

---

## Formal Overview
T1, T1b (JSD = log 2), D5, T2, L-RUN and TQ-IH over binary ontological states. Self-contained within
information theory and real analysis; ZP-B enters conceptually, not as a Lean dependency. Argument,
fences and prior art: `ZeroParadox/Information/Surprisal.md`.
-/

namespace ZeroParadox

/-! ## Setup: Binary States (AX-B1) -/

-- [ZP-CUSTOM] replaces: Fin 2 | reason: ZPC is self-contained (no ZPB import); BinaryState is a local copy of the same free-inductive encoding used by OntologicalStates in ZPB. Fin 2 would import ℕ arithmetic into an information-theoretic file whose proofs should not depend on it.
/-- The two ontological states: non-existence (⊥) and existence.
    A free inductive type — no natural-number dependency. -/
inductive BinaryState where
  | null  : BinaryState
  | exist : BinaryState
  deriving DecidableEq, Fintype

/-- Null State: non-existence, ⊥. -/
def nullSt : BinaryState := .null

/-- First Atomic State: existence. -/
def firstSt : BinaryState := .exist

/-- Unfold finite sums over BinaryState (replaces Fin.sum_univ_two). -/
@[simp] theorem BinaryState.sum_univ {M : Type*} [AddCommMonoid M] (f : BinaryState → M) :
    ∑ i : BinaryState, f i = f .null + f .exist := by
  rw [show (Finset.univ : Finset BinaryState) = {.null, .exist} from by decide]
  rw [Finset.sum_insert (by decide : BinaryState.null ∉ ({.exist} : Finset BinaryState))]
  simp

/-! ## Section II: State Representations and JSD -/

/-- P: The Null State distribution — point mass at 0 (non-existence). -/
noncomputable def distP : PMF BinaryState := PMF.pure nullSt

/-- Q: The First Atomic State distribution — point mass at 1 (existence). -/
noncomputable def distQ : PMF BinaryState := PMF.pure firstSt

/-- T1: P and Q are distinct distributions.
    Each is the unique point-mass representation of its ontological state (RP-1). -/
theorem t1_distributions_distinct : distP ≠ distQ := by
  intro heq
  have h : distP nullSt = distQ nullSt := by rw [heq]
  simp [distP, distQ, PMF.pure_apply, nullSt, firstSt] at h

-- T1b: JSD(P, Q) = log 2 (= 1 bit in base-2).
-- KL divergence computed directly over BinaryState using the branching mixture M = (1/2, 1/2).

/-- Mixture M = (1/2, 1/2): uniform over BinaryState. -/
noncomputable def mixtureM : BinaryState → ℝ := fun _ => 1 / 2

/-- P as ℝ-valued function: (1, 0). -/
noncomputable def P_real : BinaryState → ℝ :=
  fun i => if i = nullSt then 1 else 0

/-- Q as ℝ-valued function: (0, 1). -/
noncomputable def Q_real : BinaryState → ℝ :=
  fun i => if i = firstSt then 1 else 0

/-- KL divergence (in nats) of p from q, summed over BinaryState. -/
noncomputable def klDiv (p q : BinaryState → ℝ) : ℝ :=
  ∑ i : BinaryState, p i * Real.log (p i / q i)

/-- T1b: KL(P ‖ M) = log 2. -/
theorem t1b_kl_P : klDiv P_real mixtureM = Real.log 2 := by
  simp [klDiv, P_real, mixtureM, nullSt]

/-- T1b: KL(Q ‖ M) = log 2. -/
theorem t1b_kl_Q : klDiv Q_real mixtureM = Real.log 2 := by
  simp [klDiv, Q_real, mixtureM, firstSt]

/-- JSD(P, Q) = (1/2)·KL(P ‖ M) + (1/2)·KL(Q ‖ M). -/
noncomputable def jsdPQ : ℝ :=
  (1 / 2) * klDiv P_real mixtureM + (1 / 2) * klDiv Q_real mixtureM

/-- T1b: JSD(P, Q) = log 2 (= 1 bit). -/
theorem t1b_jsd : jsdPQ = Real.log 2 := by
  simp [jsdPQ, t1b_kl_P, t1b_kl_Q]; ring

/-! ## Section III: Discrete Surprisal Field on Q₂ -/

/-- D4: Surprisal at ball-hierarchy depth n: I(n) = n (bits).
    The branching measure assigns P(x) = 2⁻ⁿ at depth n, so I(n) = -log₂(2⁻ⁿ) = n. -/
noncomputable def surprisal : ℕ → ℝ := fun n => (n : ℝ)

/-- D4 formula verification: surprisal n = -log₂(2⁻ⁿ).
    At ball-hierarchy depth n the binary branching measure assigns each branch probability
    2⁻ⁿ. Shannon information: -log₂(2⁻ⁿ) = n. This proves the D4 docstring claim
    formally — `surprisal n = n` is the correct information-theoretic formula, not an
    arbitrary choice. The correspondence between depth n and Q₂ ball-hierarchy depth
    is a design identification (not a formal import of ZPB). -/
theorem surprisal_eq_binary_info (n : ℕ) :
    surprisal n = -Real.log ((1 / 2 : ℝ) ^ n) / Real.log 2 := by
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [surprisal]
  rw [show (1 / 2 : ℝ) = 2⁻¹ from by norm_num, Real.log_pow, Real.log_inv]
  field_simp [hlog2]

/-- D5: DF antisymmetry — DF(x, y) = I(y) − I(x) = −DF(y, x). -/
theorem surprisal_sub_antisymm (m n : ℕ) :
    surprisal n - surprisal m = -(surprisal m - surprisal n) := by ring

/-- D6: Partial circulation at step n: C_n = I(n+1) − I(1). -/
noncomputable def circPartial : ℕ → ℝ :=
  fun n => surprisal (n + 1) - surprisal 1

/-- T2: The partial circulation equals n. -/
theorem t2_partial_eq (n : ℕ) : circPartial n = (n : ℝ) := by
  simp [circPartial, surprisal]

/-- T2: Telescoping identity — partial sums of consecutive differences. -/
theorem t2_telescoping (n : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- T2: DF is conservative on finite loops — circulation = 0 by telescoping. -/
theorem t2_finite_loop (n : ℕ) (a : ℕ → ℝ) (hloop : a n = a 0) :
    ∑ i ∈ Finset.range n, (a (i + 1) - a i) = 0 := by
  rw [t2_telescoping]; linarith

/-- T2: The partial circulation is unbounded above (diverges to +∞).
    For any M there exists n with C_n > M. -/
theorem t2_diverges : ∀ M : ℝ, ∃ n : ℕ, M < circPartial n := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt M
  exact ⟨n, by rw [t2_partial_eq]; exact_mod_cast hn⟩

/-! ## Section III-B: L-INF — Informational Extremity of the Null State -/

/-- L-INF — Informational Extremity of ⊥.

    The surprisal I(n) = n at ball-hierarchy depth n is unbounded: for any finite
    bound M, there exist depths n with I(n) > M. The null state ⊥ = c₀ corresponds
    to the limit point 0 ∈ Q₂ — the limit of the binary ball hierarchy at infinite
    depth. At this limit, surprisal is not finite.

    Formal content: surprisal is unbounded above.
    Semantic content: ⊥ is informationally extreme — it is the compressed limit of
    all possible binary programs. No finite program bounds its informational content,
    so no finite external interpreter can hold ⊥ as a static description. This is
    the mathematical premise for DA-1 in ZP-E.

    Note: the connection from informational extremity to forced execution is a named
    design principle (DA-1 in ZP-E), not a mathematical consequence of L-INF alone.
    L-INF supplies the formal premise; DA-1 supplies the ontological bridge. -/
theorem l_inf : ∀ M : ℝ, ∃ n : ℕ, M < surprisal n := by
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt M
  exact ⟨n, by simp only [surprisal]; exact_mod_cast hn⟩

/-! ## Section IV: The Hardware Lemma (L-RUN) -/

/-- D7: Machine configuration phases. -/
inductive MachinePhase where
  | initial : MachinePhase  -- c₀: machine exists; no instruction fetched
  | running : MachinePhase  -- c₁: first instruction fetched; execution begun
  deriving DecidableEq

/-- c₀: the initial configuration. -/
def c₀ : MachinePhase := .initial

/-- c₁: the first running configuration. -/
def c₁ : MachinePhase := .running

/-- L-RUN: c₀ ≠ c₁ — the transition from initial to running is a non-null,
    irreducible state change. Derived from AX-B1 and D7. -/
theorem l_run : c₀ ≠ c₁ := by decide

/-! ## Section V: TQ-IH -/

/-- TQ-IH: c₁ is not the null (initial) configuration.
    Any execution passes through c₁; by L-RUN c₁ ≠ c₀ (≠ ⊥).
    No program can produce ⊥ without a non-null intermediate state. -/
theorem tq_ih : c₁ ≠ c₀ := Ne.symm l_run

/-! ## Section VI: The Binary Alphabet is Forced — the minimal non-degenerate distribution

⊥ is a *degenerate* distribution: a point mass with all weight on a single outcome (`distP = pure null`),
carrying zero information. Any *non-degenerate* statistical state needs at least two distinct outcomes, so
the minimal non-⊥ statistical structure is binary. There is no "half state": the outcome space has exactly
two values, and every distribution is either one of the two point masses (the ⊥-like endpoints) or a genuine
mixture over both. This is the *information-theoretic* forcing of the discrete binary jump — a distinct
mechanism from the order forcing (`t_snap_derived`), the incompressibility forcing (`l_inf`), and the
self-execution route (ZP-K). Every route constrains the same transition — its shape, not its occurrence; none of the four makes
the step happen, and `tsnap_holds_but_nothing_moves` (`Order/Snap.lean`) exhibits a model in which
the order route holds and nothing moves. They also do not all rest on the same kind of ground — the README states each one's requirement alongside its witness, and the self-execution
route's requirement is the load-bearing one: `da1_closed_concrete` proves ⊥ is the unique Quine atom of
MachinePhase and mentions no `Code` and no execution, so "⊥ must execute itself" rests on ZP-K's
`KleeneStructure` commitment rather than on that theorem. -/

/-- No half-state: every ontological state is `null` or `exist`; there is no third, intermediate value. -/
theorem binaryState_exhaustive (s : BinaryState) : s = nullSt ∨ s = firstSt := by
  cases s
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The outcome space has exactly two values — the minimal alphabet for a non-degenerate distribution. -/
theorem binaryState_card_two : Fintype.card BinaryState = 2 := by decide

/-- ⊥ (the null distribution) is degenerate: a point mass supported on the single outcome `null`. -/
theorem distP_support_singleton : distP.support = {nullSt} := by
  rw [distP, PMF.support_pure]

/-- The first-atomic-state distribution is likewise a point mass, supported on the single outcome `exist`. -/
theorem distQ_support_singleton : distQ.support = {firstSt} := by
  rw [distQ, PMF.support_pure]

/-- THE FORCING (checkable direction): a distribution exhibiting two *distinct* outcomes with positive
    probability is not a point mass — it is genuinely non-degenerate. Contrapositive: a point mass (⊥) has a
    single outcome, so to leave the degenerate ⊥ you need at least two outcomes. The binary jump. -/
theorem not_pure_of_two_support {α : Type*} {p : PMF α} {x y : α}
    (hx : x ∈ p.support) (hy : y ∈ p.support) (hxy : x ≠ y) : ∀ a, p ≠ PMF.pure a := by
  intro a hpa
  rw [hpa, PMF.support_pure, Set.mem_singleton_iff] at hx hy
  exact hxy (hx.trans hy.symm)

/-- **THE CONSTRUCTOR — what supplies `not_pure_of_two_support`'s hypotheses.** For *any* two points
of *any* type there is a distribution whose support contains both **and nothing else**: a fair
Bernoulli pushed forward along `fun b => if b then x else y`. The support bound is what lets such a
distribution be confined to a single fiber of some other map.

⚠ **Distinctness is deliberately NOT assumed here, and the linter is what caught it.** A first draft
took `x ≠ y`; the hypothesis went unused, because when `x = y` the construction is simply the point
mass and both memberships still hold. So existence of a distribution needs nothing, and distinctness is
exactly what upgrades it to **non-degenerate** — see the corollary.

**Prior art.** In this file, `not_pure_of_two_support` (above) already proves two support points imply
non-pureness; **no construction supplying its hypotheses was located in this corpus as of `d6a1ece`**
(the nearest are `markovBIK` in `ZeroParadox/Valuation/BottomInvariant.lean` and `fullMix` in
`ZeroParadox/Reals/MarkovSpectralGap.lean`, both of which build a specific two-point distribution
for their own purpose rather than the general constructor). Stated as a dated search result, not as a
universal negative.
⚠ **Not missing from Mathlib** — `PMF.uniformOfFinset` with `PMF.support_uniformOfFinset`
(`Mathlib/Probability/Distributions/Uniform.lean`) constructs the same thing directly. It is cited
rather than swapped in: that route needs a heavier import and there is no purity gain (both carry
`Classical.choice`, measured).

⚠ **It is NOT stronger than what is proved here, and a first draft of this paragraph said it was.** The
three conjuncts below give `p.support = {x, y}` **exactly** — the two memberships supply `⊇` and the
third supplies `⊆` — so the `⊆` form understates this theorem rather than being understated by
Mathlib's. -/
theorem exists_spread_pmf {α : Type*} (x y : α) :
    ∃ p : PMF α, x ∈ p.support ∧ y ∈ p.support ∧ p.support ⊆ {x, y} := by
  have hle : (1/2 : NNReal) ≤ 1 := by norm_num
  refine ⟨(PMF.bernoulli (1/2) hle).map (fun b => if b then x else y), ?_, ?_, ?_⟩
  · rw [PMF.mem_support_map_iff]
    exact ⟨true, by rw [PMF.mem_support_bernoulli_iff]; norm_num, rfl⟩
  · rw [PMF.mem_support_map_iff]
    exact ⟨false, by rw [PMF.mem_support_bernoulli_iff]; norm_num, rfl⟩
  · intro z hz
    rw [PMF.mem_support_map_iff] at hz
    obtain ⟨b, _, rfl⟩ := hz
    cases b
    · exact Set.mem_insert_of_mem _ rfl
    · exact Set.mem_insert _ _

/-- **`Statement:` two DISTINCT points admit a non-degenerate distribution.** Immediate from the
constructor plus this file's own `not_pure_of_two_support` — the two halves finally meet.

`Reading:` (Tim, 2026-08-05, conjectural) the framework reads this as where **statistics can enter**: a
non-injective *representation* has a fiber with two distinct points, and a distribution can live
entirely inside that fiber.

⚠ **State the fiber's role correctly; an earlier draft did not, and the correction was applied to the
sibling site in `ZeroParadox/Ordinal/PricedInterface.lean` before it was applied here.** It is NOT that
a two-point fiber "lifts `pmf_subsingleton_isPure`'s obstruction" — the carriers in question are
already non-subsingleton, so that obstruction was never binding, and the declaration below does not go
through it (it uses `not_pure_of_two_support`). What a *collision* supplies, beyond what any two
distinct points supply, is **confinement to a single denotation**: a spread distribution all of whose
support has one image. ⚠ **A distribution over REPRESENTATIONS, never over
histories** — nothing here posits that anything moved, and the no-traversal commitment is untouched.
Witnesses for the fiber: `e0Repr_not_injective` (`ZeroParadox/Ordinal/PricedInterface.lean`, with
`1 + ω` vs `ω`) and `hilbert_seq_collision`
(`ZeroParadox/Multihomed/SeparatedSuccession.lean`). -/
theorem nontrivial_admits_non_pure_pmf {α : Type*} {x y : α} (hne : x ≠ y) :
    ∃ p : PMF α, ∀ a, p ≠ PMF.pure a := by
  obtain ⟨p, hx, hy, _⟩ := exists_spread_pmf x y
  exact ⟨p, not_pure_of_two_support hx hy hne⟩

/-- THE FORCING (full converse): on a one-outcome space every distribution is the point mass — you cannot
    have a non-degenerate distribution with fewer than two outcomes. So a non-degenerate state forces ≥2
    outcomes; binary is the minimal. -/
theorem pmf_subsingleton_isPure {α : Type*} [Subsingleton α] (p : PMF α) (a : α) :
    p = PMF.pure a := by
  have hpa : p a = 1 := by
    have h := p.tsum_coe
    rwa [tsum_eq_single a (fun c hc => absurd (Subsingleton.elim c a) hc)] at h
  ext b
  rw [Subsingleton.elim b a, hpa]
  simp [PMF.pure_apply]

/-! ### The converse — the collision is NECESSARY, not decorative

Under an **injective** map a distribution confined to one fiber has at most one support point, so a spread
confined distribution refutes injectivity. ⚠ A collision is not the only source of a spread distribution
— the **confinement** hypothesis does all the work and must not be dropped when quoted. Scope, prior art
and the standard name (`Setoid.ker`): `ZeroParadox/Information/Surprisal.md`. -/

/-- **`Statement:` injectivity collapses any confined support to a single point.** -/
theorem injective_forces_confined_support_subsingleton
    {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (p : PMF α) (o : β) (hconf : ∀ x ∈ p.support, f x = o) :
    ∀ x ∈ p.support, ∀ y ∈ p.support, x = y :=
  fun x hx y hy => hf ((hconf x hx).trans (hconf y hy).symm)

/-- **`Statement:` and so a spread confined distribution refutes injectivity.** The contrapositive,
stated separately because it is the direction the framework actually uses: exhibiting a non-degenerate
distribution over one denotation *is* exhibiting a failure of faithfulness. -/
theorem confined_non_pure_refutes_injective
    {α β : Type*} (f : α → β) (p : PMF α) (o : β)
    (hconf : ∀ x ∈ p.support, f x = o)
    (hx : ∃ x ∈ p.support, ∃ y ∈ p.support, x ≠ y) :
    ¬ Function.Injective f := by
  obtain ⟨x, hxs, y, hys, hne⟩ := hx
  intro hf
  exact hne (injective_forces_confined_support_subsingleton f hf p o hconf x hxs y hys)

/-! ### The two readings run CONCURRENTLY — spread in the source, certain in the target

Both readings hold at once on this object, which makes the Two-Pole rule checkable here rather than a
framing. ⚠ The necessity half — that such a boundary *cannot* run one direction only — is **not** proved
and not claimed. Origin, the open no-go and prior art: `ZeroParadox/Information/Surprisal.md`. -/

/-- **`Statement:` a distribution confined to one fiber pushes forward to a POINT MASS.** Not a
support computation — a full `PMF` equality.

⚠ **NO KIND is tagged on this theorem, deliberately.** It carries **no spread hypothesis** — it holds
at `p = PMF.pure x`, where both readings are certain and nothing coincides — so a COINCIDENCE tag
here would be vacuous over part of its own range, and an earlier draft wrongly asserted one under a
`Statement:` label. The COINCIDENCE is real but belongs to the **composite**, where the spread half is
conjoined on a single `p`: `repr_spread_source_certain_target`
(`ZeroParadox/Ordinal/PricedInterface.lean`). -/
theorem confined_map_eq_pure {α β : Type*} (f : α → β) (p : PMF α) (o : β)
    (hconf : ∀ x ∈ p.support, f x = o) : p.map f = PMF.pure o := by
  ext b
  rw [PMF.map_apply, PMF.pure_apply]
  by_cases hb : b = o
  · subst hb
    rw [if_pos rfl, ← p.tsum_coe]
    refine tsum_congr fun a => ?_
    by_cases ha : p a = 0
    · simp [ha]
    · rw [if_pos (hconf a ha).symm]
  · rw [if_neg hb]
    refine (tsum_congr fun a => ?_).trans tsum_zero
    by_cases ha : p a = 0
    · simp [ha]
    · rw [if_neg]; intro h; exact hb (h.trans (hconf a ha))

/-! ### § The repeated crossing — what repetition does and does not buy

Borel–Cantelli already gives that almost every realization crosses at a **finite** trial; what the
theorems below add is strictly weaker and worth having — **no FIXED DEADLINE is certain**. ⚠ And nothing
here says the crossing HAS a probability, so the gap named at `l_inf`'s docstring stands, for want of the
`p` rather than any failure of repetition. Fences, the independence commitment and prior art: `ZeroParadox/Information/Surprisal.md`. -/

/-- **`Statement:` the survival recurrence closes to a power.** `q n` is the probability of NOT having
crossed after `n` trials. Stated over an arbitrary `CommRing` because the argument is pure
algebra — the ordered and topological hypotheses below are what actually cost something. -/
theorem survival_eq_pow {F : Type*} [CommRing F] {p : F} (q : ℕ → F)
    (hq0 : q 0 = 1) (hstep : ∀ n, q (n + 1) = (1 - p) * q n) (n : ℕ) :
    q n = (1 - p) ^ n := by
  induction n with
  | zero => simpa using hq0
  | succ n ih => rw [hstep n, ih]; ring

/-- **`Statement:` at EVERY finite stage, not-having-crossed retains positive probability.** This is
the no-go half: no finite number of trials makes the crossing certain. -/
theorem survival_pos {p : ℝ} (hp1 : p < 1) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hstep : ∀ n, q (n + 1) = (1 - p) * q n) (n : ℕ) :
    0 < q n := by
  rw [survival_eq_pow q hq0 hstep n]
  exact pow_pos (by linarith) n

/-- **`Statement:` and in the limit the survival probability vanishes.** -/
theorem survival_tendsto_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hstep : ∀ n, q (n + 1) = (1 - p) * q n) :
    Filter.Tendsto q Filter.atTop (nhds 0) := by
  have hq : q = fun n => (1 - p) ^ n := funext (survival_eq_pow q hq0 hstep)
  rw [hq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)

/-- **`Statement:` the crossing probability is below `1` at every stage and tends to `1`.** Both
conjuncts in one statement, so the second cannot be dropped when the first is quoted.

⚠ **This does NOT say the crossing fails to occur at a finite stage.** Under independence the second
Borel-Cantelli lemma gives an almost-surely finite crossing time (§ above). What is denied here is a
**fixed deadline**: no `n` can be named in advance by which the crossing is certain. An earlier name
for this theorem asserted the stronger, false reading. -/
theorem crossing_prob_lt_one_tendsto_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (q : ℕ → ℝ)
    (hq0 : q 0 = 1) (hstep : ∀ n, q (n + 1) = (1 - p) * q n) :
    (∀ n, 1 - q n < 1) ∧ Filter.Tendsto (fun n => 1 - q n) Filter.atTop (nhds 1) := by
  refine ⟨fun n => by linarith [survival_pos hp1 q hq0 hstep n], ?_⟩
  have h := survival_tendsto_zero hp0 (le_of_lt hp1) q hq0 hstep
  simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := Filter.atTop)).sub h

/-! ### § The Archimedean fence — repetition works in exactly the Archimedean carriers

`Statement:` **CARRIER kind** — `archimedean_iff_survival_eventually_lt` below is a biconditional on the
typeclass: the repeated-trials argument holds in an ordered field **iff that field is Archimedean**.
⚠ This does NOT contradict `ZeroParadox/Reals/OrderedField.lean`, whose subject is the *snap* and whose
obstruction is DENSITY. Five fences and the published prior art (Kantrowitz–Neumann 2015): `ZeroParadox/Information/Surprisal.md`. -/

/-- **`Statement:` the union bound.** After `n` trials the accumulated crossing probability is at most
`n • p`. Bernoulli's inequality in survival dress.

⚠ No `0 ≤ p` hypothesis: Bernoulli needs only `-2 ≤ -p`, and an unearned hypothesis is a defect this
file has already been caught on once (see `exists_spread_pmf` above). -/
theorem crossing_le_nsmul {F : Type*} [CommRing F] [LinearOrder F] [IsStrictOrderedRing F]
    {p : F} (hp1 : p ≤ 1) (q : ℕ → F)
    (hq0 : q 0 = 1) (hstep : ∀ n, q (n + 1) = (1 - p) * q n) (n : ℕ) :
    1 - q n ≤ n • p := by
  rw [survival_eq_pow q hq0 hstep n, nsmul_eq_mul]
  have hb := one_add_mul_le_pow (a := -p) (by linarith) n
  have hre : (1 : F) + -p = 1 - p := by ring
  rw [hre] at hb
  linarith

/-- **`Statement:` an INFINITESIMAL crossing probability never accumulates.** If no finite multiple of
`p` reaches `1`, then no finite multiple of the accumulated crossing probability does either — at
every standard `n`. The infinitesimality is an explicit **hypothesis** (`hinf`), visible on the
signature, never bundled into a definition or a class field.

⚠ No `p ≤ 1` hypothesis: it follows from `hinf 1`, and an earlier draft carried it unearned — the
same defect this file flags one docstring above. -/
theorem crossing_stays_infinitesimal {F : Type*} [CommRing F] [LinearOrder F]
    [IsStrictOrderedRing F] {p : F}
    (hinf : ∀ k : ℕ, k • p < 1)
    (q : ℕ → F) (hq0 : q 0 = 1) (hstep : ∀ n, q (n + 1) = (1 - p) * q n) (n : ℕ) :
    ∀ m : ℕ, m • (1 - q n) < 1 := by
  intro m
  have hp1 : p ≤ 1 := by have h := hinf 1; simp at h; linarith
  have h1 : 1 - q n ≤ n • p := crossing_le_nsmul hp1 q hq0 hstep n
  have hk := hinf (m * n)
  simp only [nsmul_eq_mul, Nat.cast_mul] at *
  have hm : (0 : F) ≤ (m : F) := Nat.cast_nonneg m
  calc (m : F) * (1 - q n) ≤ (m : F) * ((n : F) * p) := mul_le_mul_of_nonneg_left h1 hm
    _ = (m : F) * (n : F) * p := by ring
    _ < 1 := hk

/-- **`Statement:` Mathlib's notion of infinitesimal, in elementary form.** `∀ k, k • |p| < 1` is
`0 < ArchimedeanClass.mk p` — `ArchimedeanClass.mk_lt_mk`
(`Mathlib/Algebra/Order/Archimedean/Class.lean`) with `mk_one`
(`Mathlib/Algebra/Order/Ring/Archimedean.lean`). Stated as a theorem rather than asserted in prose,
so that a wrong identification would fail to elaborate.

⚠ **This is about `|p|`; `crossing_stays_infinitesimal` above takes the UNSIGNED `∀ k, k • p < 1`, so
the two coincide only for `0 ≤ p`.** An earlier draft of this docstring called them the same
hypothesis. They are not: at `p = -5` in ℝ the unsigned form holds while `0 < ArchimedeanClass.mk p`
fails. Supply `0 ≤ p` when moving between them. -/
theorem infinitesimal_iff_archimedeanClass_pos {F : Type*} [CommRing F] [LinearOrder F]
    [IsStrictOrderedRing F] {p : F} :
    (∀ k : ℕ, k • |p| < 1) ↔ 0 < ArchimedeanClass.mk p := by
  rw [← ArchimedeanClass.mk_one, ArchimedeanClass.mk_lt_mk]
  simp

/-- **`Statement:` THE REPEATED-TRIALS ARGUMENT IS THE ARCHIMEDEAN PROPERTY.** An ordered field is
Archimedean **if and only if** every crossing probability strictly between `0` and `1` eventually
drives the survival probability below any positive bound. The dependency is not described here — it
is the biconditional.

⚠ Stated in the order-theoretic `∀ e > 0, ∃ N, ∀ n ≥ N` form rather than with `Filter.Tendsto`
deliberately: a bare ordered field carries no topology, so no `Tendsto` statement is available at
this generality. This is the honest analogue, not an oversight.

`Reading:` (conjectural) the framework reads this as why an infinitely-slim-but-non-zero crossing
chance cannot be rescued by repetition — the engine that converts a positive chance into eventual
certainty is exactly the property such a chance denies. -/
theorem archimedean_iff_survival_eventually_lt {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] :
    Archimedean F ↔
      ∀ p : F, 0 < p → p < 1 → ∀ e : F, 0 < e → ∃ N : ℕ, ∀ n ≥ N, (1 - p) ^ n < e := by
  constructor
  · intro _ p hp0 hp1 e he
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one he (show (1:F) - p < 1 by linarith)
    exact ⟨N, fun n hn => lt_of_le_of_lt
      (pow_le_pow_of_le_one (by linarith) (by linarith) hn) hN⟩
  · intro H
    rw [archimedean_iff_nat_lt]
    intro x
    rcases le_or_gt x 1 with hx | hx
    · exact ⟨2, by push_cast; linarith⟩
    · have hx0 : (0:F) < x := lt_trans zero_lt_one hx
      set p : F := x⁻¹ with hp
      have hp0 : 0 < p := inv_pos.mpr hx0
      have hp1 : p < 1 := by rw [hp]; exact inv_lt_one_of_one_lt₀ hx
      obtain ⟨N, hN⟩ := H p hp0 hp1 (1/2) (by norm_num)
      have hpow := hN N le_rfl
      have hb := one_add_mul_le_pow (a := -p) (by linarith) N
      have hre : (1 : F) + -p = 1 - p := by ring
      rw [hre] at hb
      have hhalf : (1:F)/2 < (N : F) * p := by nlinarith
      refine ⟨2 * N, ?_⟩
      rw [hp, ← div_eq_mul_inv, lt_div_iff₀ hx0] at hhalf
      push_cast
      linarith

end ZeroParadox


/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms t1_distributions_distinct
#print axioms t1b_kl_P
#print axioms t1b_kl_Q
#print axioms t1b_jsd
#print axioms surprisal_eq_binary_info
#print axioms surprisal_sub_antisymm
#print axioms t2_partial_eq
#print axioms t2_finite_loop
#print axioms t2_diverges
#print axioms l_inf
#print axioms l_run
#print axioms tq_ih
#print axioms binaryState_exhaustive
#print axioms binaryState_card_two
#print axioms distP_support_singleton
#print axioms distQ_support_singleton
#print axioms exists_spread_pmf
#print axioms nontrivial_admits_non_pure_pmf
#print axioms not_pure_of_two_support
#print axioms pmf_subsingleton_isPure
#print axioms injective_forces_confined_support_subsingleton
#print axioms confined_non_pure_refutes_injective
#print axioms confined_map_eq_pure
#print axioms survival_eq_pow
#print axioms survival_pos
#print axioms survival_tendsto_zero
#print axioms crossing_prob_lt_one_tendsto_one
#print axioms crossing_le_nsmul
#print axioms crossing_stays_infinitesimal
#print axioms infinitesimal_iff_archimedeanClass_pos
#print axioms archimedean_iff_survival_eventually_lt

end PurityCheck
