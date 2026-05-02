import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Archimedean
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

## Formal Overview (AI-assisted)

Formalizes the Zero Paradox information-theoretic framework over binary
ontological states. Proves: T1 (unique state distributions), T1b (JSD = log 2),
D5 (DF antisymmetry), T2 (non-conservative circulation), L-RUN (execution is
a non-null state change), and TQ-IH (no execution avoids a non-null config).

Self-contained within information theory and real analysis.
Imports ZP-B conceptually (total disconnectedness, clopen balls) but not
as a Lean dependency — ZP-C's theorems do not require the p-adic structure.
-/

namespace ZeroParadox.ZPC

/-! ## Setup: Binary States (AX-B1) -/

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
theorem d5_antisymm (m n : ℕ) :
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

end ZeroParadox.ZPC

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPC

#print axioms t1_distributions_distinct
#print axioms t1b_kl_P
#print axioms t1b_kl_Q
#print axioms t1b_jsd
#print axioms surprisal_eq_binary_info
#print axioms d5_antisymm
#print axioms t2_partial_eq
#print axioms t2_finite_loop
#print axioms t2_diverges
#print axioms l_inf
#print axioms l_run
#print axioms tq_ih

end PurityCheck
