-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import ZeroParadox.Valuation.PadicAttractor
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Nat.SuccPred
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Well-foundedness obstructs the attractor character of the μ floor

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview
The complementary test to `ZeroParadox/Valuation/PadicAttractor.lean`: the μ floor is reached in
**finite time**, where the ν orbit converges to one it never reaches — both under the single predicate
`ReachesFloorInFiniteTime`. Gauge, verdict and scope: `ZeroParadox/Order/WellFoundedObstruct.md`.
-/

namespace ZeroParadox

open ZeroParadox
open Filter Topology

/-! ## The obstruction-killer — no infinite descent on the well-founded μ floor -/

/-- **The structural obstruction, stated in general. ⚠ ZERO call sites — nothing below uses it.**
    There is no infinite strictly-decreasing sequence `ℕ → ℕ`: the well-founded μ floor cannot host
    the order-theoretic analogue of the infinite shrinking 2-adic orbit `2ⁿ·x`. This is
    `not_strictAnti_of_wellFoundedLT` specialised to ℕ (which is `WellFoundedLT`), and it is *false*
    in any non-well-founded ambient (e.g. the 2-adic norms of `2ⁿ·x`).

    It states the obstruction the μ side rests on **conceptually**;
    `descent_with_strict_steps_reaches_floor` below proves its own case by induction on the bound and
    does **not** call this. Contrast
    `doubling_norm_lt_one`, which genuinely IS invoked downstream: the mirror is asymmetric. -/
theorem no_infinite_descent : ∀ f : ℕ → ℕ, ¬ StrictAnti f :=
  fun f => not_strictAnti_of_wellFoundedLT f

/-- **The load-bearing bridge — the descent reaches the floor.** Any orbit `g : ℕ → ℕ` that strictly
    decreases at every nonzero step (`g k ≠ 0 → g (k+1) < g k`) must reach the floor: `∃ N, g N = 0`.

    **Proved by induction on the bound `g 0`, deliberately, not through `no_infinite_descent`.**
    An earlier version routed the μ side through that lemma — `by_contra`, then "if the floor were
    never reached, every step is strict, so `g` is the forbidden `StrictAnti` orbit." That reading is
    conceptually right and the statement is unchanged, but it borrowed a general well-foundedness
    lemma (Mathlib's `not_strictAnti_of_wellFoundedLT`, for an arbitrary `Preorder` with
    `WellFoundedLT`) for a statement about `ℕ` whose descent is already bounded by a natural number
    *in the hypothesis*. The counter's value **is** the step budget, so the induction is available
    directly. Measured consequence: `[propext, Classical.choice, Quot.sound]` → `[propext, Quot.sound]`.

    The conceptual claim survives intact — well-foundedness is still what closes the descent; on `ℕ`
    it is the induction principle rather than an imported lemma. See `no_infinite_descent` above for
    the general statement, which keeps its own footprint. -/
theorem descent_with_strict_steps_reaches_floor (g : ℕ → ℕ)
    (hstep : ∀ k, g k ≠ 0 → g (k + 1) < g k) : ∃ N, g N = 0 := by
  have key : ∀ b n, g n ≤ b → ∃ N, g N = 0 := by
    intro b
    induction b with
    | zero => intro n hn; exact ⟨n, Nat.le_zero.mp hn⟩
    | succ m ih =>
        intro n hn
        rcases Nat.eq_zero_or_pos (g n) with h0 | h0
        · exact ⟨n, h0⟩
        · exact ih (n + 1) (by have := hstep n h0.ne'; omega)
  exact key (g 0) 0 le_rfl

/-! ## The deflation side — descent on the μ floor terminates in finite time -/

/-- **Finite-time termination (mirror of `doubling_orbit_tendsto_zero`, but in finite steps).**
    For the canonical descent map `Nat.pred` (`x ↦ x-1`), the orbit reaches the floor `0` after at
    most `n` steps and stays: `pred^[k] n = 0` for every `k ≥ n`. Contrast `ZeroParadox/Valuation/PadicAttractor.lean`, where the orbit
    `2ⁿ·x` converges to `0` only in the limit and (for `x ≠ 0`) never reaches it. -/
theorem pred_descent_terminates (n : ℕ) : ∀ k, n ≤ k → Nat.pred^[k] n = 0 := by
  intro k hk
  rw [Nat.pred_iterate]
  omega

/-- The `Nat.pred` orbit is **eventually constant** at `0`: there is a step `N` (namely `n`) past
    which every orbit value equals the value at `N`. The descent *terminates* — this is the precise
    sense in which the μ floor's "attractor" is reached in finite time, not approached as a limit. -/
theorem pred_orbit_eventually_constant (n : ℕ) :
    ∃ N, ∀ k, N ≤ k → Nat.pred^[k] n = Nat.pred^[N] n := by
  refine ⟨n, fun k hk => ?_⟩
  rw [pred_descent_terminates n k hk, pred_descent_terminates n n le_rfl]

/-! ## The contrasting half — the 2-adic ν-orbit never reaches its limit -/

/-- **The contrast (load-bearing, in-statement).** For `x ≠ 0`, the `ZeroParadox/Valuation/PadicAttractor.lean` doubling orbit `2ⁿ·x` is
    *never* `0`: it converges to the floor only as a topological limit and never reaches it in finite
    time. So the 2-adic (#3, ν) orbit is **not** eventually constant — the opposite of the μ floor's
    `Nat.pred` orbit, which terminates. This is the precise behavioural separator across Axis I. -/
theorem padic_orbit_never_reaches_zero (x : Q₂) (hx : x ≠ 0) :
    ∀ n : ℕ, (2 : Q₂) ^ n * x ≠ 0 := by
  intro n
  exact mul_ne_zero (pow_ne_zero n (by norm_num)) hx

/-! ## The single comparison predicate — reaching the floor in finite time

The fix for the "conjunction of unrelated facts" pattern: one predicate, instantiated on both
ambients, with the μ orbit satisfying it and the ν orbit satisfying its negation. The contrast is now
in the *definition*, not the prose. -/

/-- **The single dynamical predicate the two ambients are compared under.** An orbit
    `orbit : ℕ → α` (into a type with a distinguished floor `0`) *reaches the floor in finite time* iff
    it is eventually exactly equal to `0`: `∃ N, ∀ k ≥ N, orbit k = 0`. This is the order-theoretic
    "termination" character (μ); its negation — an orbit that is never `0` from any point on — is the
    "approaches a limit it never reaches" character (ν). One definition, two ambients. -/
def ReachesFloorInFiniteTime {α : Type*} [Zero α] (orbit : ℕ → α) : Prop :=
  ∃ N, ∀ k, N ≤ k → orbit k = 0

/-- The `Nat.pred` orbit strictly decreases at every nonzero step — the hypothesis of
    `descent_with_strict_steps_reaches_floor`. (`Nat.pred^[k] n = n - k`, and `n - k ≠ 0` gives
    `n - (k+1) < n - k`.) This is what lets the μ side be closed *through* well-foundedness. -/
theorem pred_orbit_strict_steps (n : ℕ) :
    ∀ k, Nat.pred^[k] n ≠ 0 → Nat.pred^[k + 1] n < Nat.pred^[k] n := by
  intro k hk
  rw [Nat.pred_iterate, Nat.pred_iterate] at *
  omega

/-- The μ floor's canonical descent orbit `k ↦ Nat.pred^[k] n` **satisfies**
    `ReachesFloorInFiniteTime`. The existence of a step reaching the floor is obtained from
    `descent_with_strict_steps_reaches_floor` (proved by induction on the bound, **not** through
    `no_infinite_descent`, which has no call sites — see that lemma's own docstring; the orbit cannot
    strictly decrease forever), and once the floor is reached the orbit stays (`pred_descent_terminates`
    monotonicity). So well-foundedness is genuinely in this proof term. -/
theorem pred_orbit_reaches_floor (n : ℕ) :
    ReachesFloorInFiniteTime (fun k => Nat.pred^[k] n) := by
  -- existence of a zero step, forced by well-foundedness:
  obtain ⟨N, hN⟩ :=
    descent_with_strict_steps_reaches_floor (fun k => Nat.pred^[k] n) (pred_orbit_strict_steps n)
  -- `Nat.pred^[N] n = 0` means `n - N = 0`, i.e. `n ≤ N`; use that `N` as the witness and stay there.
  rw [Nat.pred_iterate] at hN
  have hnN : n ≤ N := by omega
  refine ⟨N, fun k hk => ?_⟩
  exact pred_descent_terminates n k (le_trans hnN hk)

/-- The 2-adic ν-orbit `n ↦ 2ⁿ·x` (`x ≠ 0`) **satisfies the negation** of the *same* predicate:
    `¬ ReachesFloorInFiniteTime`. It is never `0` (`padic_orbit_never_reaches_zero`), so there is no
    `N` past which it equals `0`. Under one definition, the ν orbit lands on the opposite side from the
    μ orbit. -/
theorem padic_orbit_not_reaches_floor (x : Q₂) (hx : x ≠ 0) :
    ¬ ReachesFloorInFiniteTime (fun n => (2 : Q₂) ^ n * x) := by
  rintro ⟨N, hN⟩
  exact padic_orbit_never_reaches_zero x hx N (hN N le_rfl)

/-! ## Capstone — the contrast in one statement, under one predicate -/

/-- **Axis-I separation (one predicate, with the real dynamical contrast in-statement).** Under
    the single definition `ReachesFloorInFiniteTime`, the μ floor's canonical descent (`Nat.pred^[·] n`)
    **satisfies** it (finite-time termination), while the 2-adic ν-orbit (`2ⁿ·x`, `x ≠ 0`) both
    **converges to the floor** topologically (`Tendsto … (nhds 0)` `doubling_orbit_tendsto_zero`)
    **and satisfies the negation** `¬ ReachesFloorInFiniteTime`. So the in-statement contrast is the
    real one — *reaches the floor in finite time* (μ, #1) vs *converges to the floor as a limit it never
    reaches* (ν, #3) — not the weak eventually-0 vs never-0. The μ side is routed through
    `descent_with_strict_steps_reaches_floor` (induction on the bound, **not** via
    `no_infinite_descent`); the ν
    side's convergence is contraction and its non-arrival is `padic_orbit_never_reaches_zero`.
    The Axis-I cut is not collapsed: recast as the same dynamical question, #1 and #3 answer it
    oppositely. -/
theorem floor_reach_separates_mu_nu :
    ∀ x : Q₂, x ≠ 0 →
      (∀ n : ℕ, ReachesFloorInFiniteTime (fun k => Nat.pred^[k] n)) ∧
      (Tendsto (fun n => (2 : Q₂) ^ n * x) atTop (nhds 0) ∧
        ¬ ReachesFloorInFiniteTime (fun n => (2 : Q₂) ^ n * x)) :=
  fun x hx =>
    ⟨pred_orbit_reaches_floor,
      doubling_orbit_tendsto_zero x, padic_orbit_not_reaches_floor x hx⟩

/-! ### Where the SAME question is asked in the other formal faces

*Can the floor be departed?* is asked in more than one carrier and the answers are not interchangeable:
the step-function face derives an **obstruction**, this face takes the orbit as **given**, and neither
derives motion. The comparison and its prior art: `ZeroParadox/Order/WellFoundedObstruct.md`. -/

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` enters through the Mathlib well-foundedness (`not_strictAnti_of_wellFoundedLT`,
`RelEmbedding`) and p-adic field libraries — a library dependency, not a new commitment of this
construction. -/

section PurityCheck
open ZeroParadox

#print axioms no_infinite_descent
#print axioms descent_with_strict_steps_reaches_floor
#print axioms pred_descent_terminates
#print axioms pred_orbit_eventually_constant
#print axioms pred_orbit_strict_steps
#print axioms padic_orbit_never_reaches_zero
#print axioms pred_orbit_reaches_floor
#print axioms padic_orbit_not_reaches_floor
#print axioms floor_reach_separates_mu_nu

end PurityCheck
