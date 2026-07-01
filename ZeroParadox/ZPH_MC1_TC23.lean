-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_PerronFrobenius
import ZeroParadox.ZPH_MeanErgodic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H / TC20: does the Markov node (#2) get a ν (terminal/unique-fixed-point) universal property?

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This is a single go/no-go cycle on the placement of node #2 (the Markov-dynamical attractor — the
stationary distribution in the probability simplex) in the bottom-diagram μ/ν tree.

**The pre-registered question.** The order ambient blocks #2 from any universal property: the simplex
is a coordinate-order antichain (`ZPH_MC1_TreeObstructions.simplex_antichain`), so the stationary
point is neither order-least (μ) nor order-greatest (ν). TC20 asked whether *changing the ambient*
from the order to the **dynamics** rescues a universal property: the stationary distribution is a
*fixed point* of the Kleisli transfer action `μ ↦ μ.bind f`, and a **unique** fixed point of an
endomorphism is a terminal-flavoured (ν / final-coalgebra) universal object. The GO conjecture was
that the fixed-point predicate is a *subsingleton* (unique) under the doubly-stochastic hypothesis
already in scope (`MeanErgodic.DoublyStochastic`); the NO-GO obstruction was that doubly-stochastic
is **not enough** for uniqueness — a **reducible** chain has a whole simplex of stationary
distributions (one per communicating class), so #2 is a fixed *set*, not a fixed *point*, and resists
any μ/ν placement.

**What the Lean decides: the NO-GO is the truth, sharply — witnessed by a genuinely reducible chain.**
The load-bearing theorem `markov_node_no_universal_property` exhibits a *concrete* doubly-stochastic
kernel on `Fin 4` that actually *moves mass* and is reducible into non-communicating classes: the
permutation kernel `blockKernel` that fixes states `0` and `1` (two distinct absorbing classes) and
swaps states `2 ↔ 3` (an internally non-trivial third class). This is not the degenerate identity
kernel — it has real dynamics inside one block and two separate absorbing classes. Its stationary set
is at least two-dimensional: `pure 0` and `pure 1` are two *distinct* stationary distributions (each
absorbing class is its own fixed point). So the fixed-point predicate is **not** a subsingleton, hence
there is no terminal/unique-fixed-point universal property for #2 in the dynamical ambient. The
obstruction is reducibility — multiple communicating classes — exactly the structural feature the
identity kernel would have hidden. The antichain obstruction survives the change of ambient.

What DOES hold is only the existence half (`markov_node_stationary_inhabited`, re-exporting
`exists_stationary`): the stationary set is always inhabited, never empty. Existence without
uniqueness is exactly a fixed *set*, not a terminal object.

**Honest scope.** The GO conjecture (subsingleton ⇒ terminal) is **refuted as stated**: it is false
for the doubly-stochastic hypothesis it was registered under, and the refutation is by a reducible
chain with genuine dynamics, not by the do-nothing identity. Uniqueness genuinely needs a strictly
stronger hypothesis (irreducibility/primitivity), which the campaign's doubly-stochastic ergodic
machinery does not supply. The Lean witnesses the failure with a named counterexample; it does **not**
prove "no stronger hypothesis works" — under primitivity uniqueness does hold (Perron–Frobenius), but
that is a *different, narrower* node than "the Markov attractor" and is not what was registered.
Verdict: **NO-GO** — #2 is dynamical-only, structurally outside the μ/ν universal-property tree, the
obstruction being reducibility.
-/

namespace ZeroParadox.ZPH_MC1_TC23

open scoped BigOperators
open ZeroParadox.MeanErgodic

variable {n : ℕ}

/-- A PMF `μ` is **stationary** for the kernel `f` iff it is a fixed point of the Kleisli transfer
    action `μ ↦ μ.bind f`. This is the dynamical (ν-flavoured) fixed-point predicate whose
    subsingleton-ness was the TC20 GO conjecture. -/
def IsStationaryPMF (f : Fin n → PMF (Fin n)) (μ : PMF (Fin n)) : Prop := μ.bind f = μ

/-! ## GO half (holds): the stationary set is inhabited -/

/-- **GO half — existence.** Every finite stochastic action has at least one stationary
    distribution. Re-export of `PerronFrobenius.exists_stationary`. This is the only half of the
    pre-registered GO conjecture that survives: inhabited, but (see below) **not** subsingleton. -/
theorem markov_node_stationary_inhabited [Nonempty (Fin n)] (f : Fin n → PMF (Fin n)) :
    ∃ μ : PMF (Fin n), IsStationaryPMF f μ :=
  ZeroParadox.PerronFrobenius.exists_stationary f

/-! ## The reducible doubly-stochastic counterexample: the block-permutation kernel

This is the substantive witness. On `Fin 4` define the involution `σ` that **fixes** `0` and `1`
(two distinct absorbing communicating classes) and **swaps** `2 ↔ 3` (a third class with genuine
internal dynamics — it actually moves mass, unlike the identity kernel). `blockKernel j := pure (σ j)`
is a permutation kernel, hence doubly stochastic, but it is **reducible**: states `0`, `1`, and
`{2,3}` never communicate. So the stationary set contains at least `pure 0` and `pure 1`, two distinct
fixed points. -/

/-- The block involution on `Fin 4`: fixes `0`, fixes `1`, swaps `2 ↔ 3`. -/
def σ : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

/-- `σ` is an involution. -/
lemma σ_involutive : Function.Involutive σ := by
  intro x; fin_cases x <;> rfl

/-- The **block-permutation kernel** on `Fin 4`: `j ↦ pure (σ j)`. Non-trivial (moves mass `2 ↔ 3`)
    and reducible (`0`, `1`, `{2,3}` are three non-communicating classes). -/
noncomputable def blockKernel : Fin 4 → PMF (Fin 4) := fun j => PMF.pure (σ j)

/-- The block kernel is **not** the identity kernel: it sends `2` to `pure 3 ≠ pure 2`. So this
    counterexample genuinely moves mass, in contrast to the degenerate identity kernel. -/
theorem blockKernel_ne_id : blockKernel 2 ≠ PMF.pure 2 := by
  intro h
  have e : (PMF.pure (3 : Fin 4)) 2 = (PMF.pure (2 : Fin 4)) 2 := by
    rw [show PMF.pure (3 : Fin 4) = blockKernel 2 from rfl, h]
  rw [PMF.pure_apply_of_ne (3 : Fin 4) 2 (by decide), PMF.pure_apply_self 2] at e
  exact zero_ne_one e

/-- The block-permutation kernel is doubly stochastic: each column `k` of its transfer matrix is the
    indicator of `j = σ k` (since `σ` is an involution), which sums to `1`. -/
theorem blockKernel_doublyStochastic : DoublyStochastic blockKernel := by
  intro k
  -- column k: ∑_j (pure (σ j)) k = ∑_j [σ j = k] = 1, with the unique hit at j = σ k.
  rw [Finset.sum_eq_single (σ k)]
  · -- σ (σ k) = k, so the term at j = σ k is (pure k) k = 1
    show ((PMF.pure (σ (σ k))) k).toReal = 1
    rw [σ_involutive k, PMF.pure_apply_self, ENNReal.toReal_one]
  · intro j _ hj
    -- for j ≠ σ k we have σ j ≠ k, so (pure (σ j)) k = 0
    show ((PMF.pure (σ j)) k).toReal = 0
    rw [PMF.pure_apply_of_ne (σ j) k ?_, ENNReal.toReal_zero]
    intro hσ
    -- hσ : k = σ j ⇒ σ k = σ (σ j) = j, so j = σ k
    exact hj (by rw [hσ, σ_involutive j])
  · intro h; exact absurd (Finset.mem_univ (σ k)) h

/-- `pure 0` is stationary for the block kernel: `0` is an absorbing state (`σ 0 = 0`). -/
theorem blockKernel_pure0_stationary : IsStationaryPMF blockKernel (PMF.pure 0) := by
  show (PMF.pure (0 : Fin 4)).bind blockKernel = PMF.pure 0
  rw [PMF.pure_bind]; rfl

/-- `pure 1` is stationary for the block kernel: `1` is a *second*, distinct absorbing state
    (`σ 1 = 1`). This is the second communicating class — the source of non-uniqueness. -/
theorem blockKernel_pure1_stationary : IsStationaryPMF blockKernel (PMF.pure 1) := by
  show (PMF.pure (1 : Fin 4)).bind blockKernel = PMF.pure 1
  rw [PMF.pure_bind]; rfl

/-! ## NO-GO (the load-bearing theorem): no unique-fixed-point / terminal property for #2 -/

/-- **NO-GO — the load-bearing theorem.** There is a *doubly-stochastic* kernel that is **not** the
    identity (it moves mass `2 ↔ 3`) and is **reducible** (three non-communicating classes
    `0`, `1`, `{2,3}`), whose stationary-distribution predicate is **not a subsingleton**: it has two
    *distinct* witnesses, `pure 0` and `pure 1`, one per absorbing class.

    A unique fixed point of an endomorphism is a terminal (ν / final-coalgebra) universal object; a
    *non-unique* fixed set is not. So node #2 has **no** terminal/unique-fixed-point universal
    property in the dynamical ambient under the doubly-stochastic hypothesis. The witness is a genuine
    reducible chain with internal dynamics — the obstruction is reducibility (multiple communicating
    classes), not the degenerate "does-nothing" identity. The pre-registered GO conjecture
    (subsingleton) is refuted, and the antichain obstruction survives the change of ambient. -/
theorem markov_node_no_universal_property :
    ∃ f : Fin 4 → PMF (Fin 4),
      DoublyStochastic f ∧ f ≠ (fun j => PMF.pure j) ∧
      ¬ (∀ μ ν : PMF (Fin 4), IsStationaryPMF f μ → IsStationaryPMF f ν → μ = ν) := by
  refine ⟨blockKernel, blockKernel_doublyStochastic, ?_, ?_⟩
  · -- the witness is genuinely not the identity kernel
    intro h
    exact blockKernel_ne_id (by rw [h])
  · intro hsub
    -- pure 0 and pure 1 are both stationary, yet distinct
    have h := hsub (PMF.pure 0) (PMF.pure 1)
      blockKernel_pure0_stationary blockKernel_pure1_stationary
    -- evaluate both sides at 0: (pure 0) 0 = 1 ≠ 0 = (pure 1) 0
    have e : (PMF.pure (0 : Fin 4)) 0 = (PMF.pure (1 : Fin 4)) 0 := by rw [h]
    rw [PMF.pure_apply_self 0, PMF.pure_apply_of_ne (1 : Fin 4) 0 (by decide)] at e
    exact one_ne_zero e

/-- **Restatement** of the NO-GO as the negation of the GO conjecture *as registered*: it is **not**
    the case that, for every doubly-stochastic kernel on `Fin 4`, the stationary predicate is a
    subsingleton. (`Subsingleton`-flavoured statement, packaged for the campaign ledger.) -/
theorem doublyStochastic_stationary_not_subsingleton :
    ¬ (∀ f : Fin 4 → PMF (Fin 4), DoublyStochastic f →
        ∀ μ ν : PMF (Fin 4), IsStationaryPMF f μ → IsStationaryPMF f ν → μ = ν) := by
  intro h
  obtain ⟨f, hf, _, hbad⟩ := markov_node_no_universal_property
  exact hbad (h f hf)

end ZeroParadox.ZPH_MC1_TC23

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib PMF / simplex / finite-dimensional libraries
(`exists_stationary` uses compactness + subsequence extraction) — a library dependency, not a new
commitment. The counterexample theorems are choice-light. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC23

#print axioms markov_node_stationary_inhabited
#print axioms blockKernel_doublyStochastic
#print axioms blockKernel_ne_id
#print axioms blockKernel_pure0_stationary
#print axioms blockKernel_pure1_stationary
#print axioms markov_node_no_universal_property
#print axioms doublyStochastic_stationary_not_subsingleton

end PurityCheck
