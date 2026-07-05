-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import ZeroParadox.ZPH_MC1_TC05
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Nat.SuccPred
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC28 — well-foundedness obstructs the attractor character of the μ floor

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file is the **complementary test to TC05**, refining **Axis I** of the bottom-diagram tree
(`thread_obstruction_table_2026-06-29.md`). TC05 gave node #3 (the p-adic floor `{0} ⊆ Q₂`) a genuine
**dynamical attractor** character: `0` is the global attractor of the doubling map `x ↦ 2·x`, because
`‖2‖₂ = ½ < 1` makes the map a strict contraction, so every orbit `2ⁿ·x` is an **infinite,
non-terminating** sequence converging to `0` *in the limit topology* — and (for `x ≠ 0`) it never
actually reaches `0`. That is a ν-flavoured (limit / contraction) character.

The question here: does the **well-founded μ floor** (node #1 — the floor `0` of ℕ, base of the
proof-theory descent the framework uses for Goodstein / Kirby–Paris / Kruskal) carry the *same*
attractor/contraction character in its own ambient? If it did, the dynamical (ν) and well-founded (μ)
characters would collapse and the Axis-I cut between #1 and the ν-dynamical nodes #2/#3 would be
undermined.

**Pre-registered GO conjecture (the deflation side):** the well-founded floor admits descent maps that
reach `0` from every point, but every orbit hits `0` in **finitely many steps** and is then constant —
there is no infinite non-terminating orbit converging to `0` in the TC05 sense, so the "attractor"
character is *vacuous* on the μ floor.

**Pre-registered NO-GO obstruction:** a genuine contraction/attractor with infinite non-terminating
orbits converging to `0`, matching TC05's topological `Tendsto`, IS constructible on the ℕ/Ordinal
floor — collapsing the μ/ν distinction.

**Verdict: GO.** The NO-GO is *refuted at the structural level*: well-foundedness of ℕ forbids the
infinite descending orbit that TC05's contraction produces.

**Honest framing of the capstone.** The capstone `floor_reach_separates_mu_nu` is, syntactically, a
conjunction (`μ-side ∧ ν-side`). Its content is not "two unrelated facts": both sides are stated under
the *same* predicate `ReachesFloorInFiniteTime`, and the in-statement contrast is sharpened from the
weak "eventually 0 vs never 0" to the real dynamical contrast — the ν side carries TC05's topological
`Tendsto … (nhds 0)` *together with* `¬ ReachesFloorInFiniteTime`, so the separation read in the
statement is "reaches the floor in finite time" (μ) vs "converges to the floor as a limit it never
reaches" (ν). That `ReachesFloorInFiniteTime` is *the* formalization of "attractor character" remains
the framework reading, not a Lean claim.

What the Lean proves (load-bearing, in the statements):

- `no_infinite_descent` — `∀ f : ℕ → ℕ, ¬ StrictAnti f`: there is no infinite strictly-decreasing
  orbit on the μ floor (`not_strictAnti_of_wellFoundedLT` at ℕ). The obstruction-killer, mirror of
  TC05's `doubling_norm_lt_one`.
- `descent_with_strict_steps_reaches_floor` — **the load-bearing bridge that puts well-foundedness in
  the proof term.** Any orbit `g : ℕ → ℕ` that strictly decreases at every nonzero step
  (`∀ k, g k ≠ 0 → g (k+1) < g k`) reaches the floor: `∃ N, g N = 0`. Proved *through*
  `no_infinite_descent` — if `g` never hit `0` it would be `StrictAnti`, the forbidden infinite
  descent. This is why the μ side is forced by well-foundedness rather than by arithmetic alone.
- `pred_descent_terminates` — for the canonical descent map `Nat.pred` (`x ↦ x-1`), the orbit
  `pred^[k] n` equals `0` for **every** `k ≥ n`: it reaches the floor and stays.
- `pred_orbit_reaches_floor` — the μ floor's `Nat.pred` orbit **satisfies** `ReachesFloorInFiniteTime`,
  proved via `descent_with_strict_steps_reaches_floor` (i.e. via well-foundedness) plus the
  stays-at-floor fact, so `no_infinite_descent` is genuinely in the proof term, not decorative.
- `padic_orbit_never_reaches_zero` — for `x ≠ 0` the TC05 doubling orbit `2ⁿ·x` is **never** `0`.
- `ReachesFloorInFiniteTime` — **a single formal predicate** on a generic orbit `orbit : ℕ → α` into
  a type with a `Zero`: `∃ N, ∀ k ≥ N, orbit k = 0`. The one definition both ambients are compared
  under.
- `padic_orbit_not_reaches_floor` — the p-adic ν-orbit `2ⁿ·x` (`x ≠ 0`) **satisfies the negation**
  `¬ ReachesFloorInFiniteTime`.
- `floor_reach_separates_mu_nu` — the capstone: the μ orbit satisfies `ReachesFloorInFiniteTime` while the
  ν orbit both **converges to the floor** (`Tendsto … (nhds 0)`, imported from TC05's
  `doubling_orbit_tendsto_zero`) and **satisfies `¬ ReachesFloorInFiniteTime`**. The in-statement
  contrast is therefore finite-time termination vs convergence-without-arrival, not the weaker
  eventually-0 vs never-0. The μ side is routed through `no_infinite_descent`.

**Honest scope (interpretation, NOT proved here).** "Attractor" and "contraction" remain the
*framework reading* — the file does not build a full dynamical-systems contraction framework, nor does
it prove that `ReachesFloorInFiniteTime` is the unique formalization of "attractor character." What is
proved in-statement is the concrete, single-definition separation, with the ν side additionally
carrying TC05's topological convergence. The claim that this separation *is* the μ/ν cut of Axis I is
the framework reading; the Lean proves the separation under the stated predicate, with the
well-foundedness obstruction in the proof term of the μ side.
-/

namespace ZeroParadox

open ZeroParadox
open Filter Topology

/-! ## The obstruction-killer — no infinite descent on the well-founded μ floor -/

/-- **The structural obstruction (mirror of TC05's `doubling_norm_lt_one`).** There is no infinite
    strictly-decreasing sequence `ℕ → ℕ`: the well-founded μ floor cannot host the order-theoretic
    analogue of TC05's infinite shrinking orbit `2ⁿ·x`. This is `not_strictAnti_of_wellFoundedLT`
    specialised to ℕ (which is `WellFoundedLT`); it is the load-bearing fact behind the whole
    separation — it is *false* in any non-well-founded ambient (e.g. the 2-adic norms of `2ⁿ·x`). -/
theorem no_infinite_descent : ∀ f : ℕ → ℕ, ¬ StrictAnti f :=
  fun f => not_strictAnti_of_wellFoundedLT f

/-- **The load-bearing bridge — well-foundedness forces the descent to reach the floor.** Any orbit
    `g : ℕ → ℕ` that strictly decreases at every nonzero step (`g k ≠ 0 → g (k+1) < g k`) must reach
    the floor: `∃ N, g N = 0`. This routes the μ side *through* `no_infinite_descent`: if `g` never
    hit `0`, every step would be strict, making `g` the forbidden `StrictAnti` orbit. So
    well-foundedness — not arithmetic alone — is what closes the descent. -/
theorem descent_with_strict_steps_reaches_floor (g : ℕ → ℕ)
    (hstep : ∀ k, g k ≠ 0 → g (k + 1) < g k) : ∃ N, g N = 0 := by
  by_contra h
  -- if the floor is never reached, every step is strict, so `g` is StrictAnti — forbidden.
  have hne : ∀ k, g k ≠ 0 := fun k hk => h ⟨k, hk⟩
  refine no_infinite_descent g (strictAnti_nat_of_succ_lt (fun k => ?_))
  exact hstep k (hne k)

/-! ## The deflation side — descent on the μ floor terminates in finite time -/

/-- **Finite-time termination (mirror of TC05's `doubling_orbit_tendsto_zero`, but in finite steps).**
    For the canonical descent map `Nat.pred` (`x ↦ x-1`), the orbit reaches the floor `0` after at
    most `n` steps and stays: `pred^[k] n = 0` for every `k ≥ n`. Contrast TC05, where the orbit
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

/-! ## The contrasting half — the p-adic ν-orbit never reaches its limit -/

/-- **The contrast (load-bearing, in-statement).** For `x ≠ 0`, the TC05 doubling orbit `2ⁿ·x` is
    *never* `0`: it converges to the floor only as a topological limit and never reaches it in finite
    time. So the p-adic (#3, ν) orbit is **not** eventually constant — the opposite of the μ floor's
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
    `descent_with_strict_steps_reaches_floor` (i.e. *through* `no_infinite_descent` — the orbit cannot
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

/-- The p-adic ν-orbit `n ↦ 2ⁿ·x` (`x ≠ 0`) **satisfies the negation** of the *same* predicate:
    `¬ ReachesFloorInFiniteTime`. It is never `0` (`padic_orbit_never_reaches_zero`), so there is no
    `N` past which it equals `0`. Under one definition, the ν orbit lands on the opposite side from the
    μ orbit. -/
theorem padic_orbit_not_reaches_floor (x : Q₂) (hx : x ≠ 0) :
    ¬ ReachesFloorInFiniteTime (fun n => (2 : Q₂) ^ n * x) := by
  rintro ⟨N, hN⟩
  exact padic_orbit_never_reaches_zero x hx N (hN N le_rfl)

/-! ## Capstone — the contrast in one statement, under one predicate -/

/-- **TC28 Axis-I separation (one predicate, with the real dynamical contrast in-statement).** Under
    the single definition `ReachesFloorInFiniteTime`, the μ floor's canonical descent (`Nat.pred^[·] n`)
    **satisfies** it (finite-time termination), while the p-adic ν-orbit (`2ⁿ·x`, `x ≠ 0`) both
    **converges to the floor** topologically (`Tendsto … (nhds 0)`, TC05's `doubling_orbit_tendsto_zero`)
    **and satisfies the negation** `¬ ReachesFloorInFiniteTime`. So the in-statement contrast is the
    real one — *reaches the floor in finite time* (μ, #1) vs *converges to the floor as a limit it never
    reaches* (ν, #3) — not the weak eventually-0 vs never-0. The μ side is routed through
    `no_infinite_descent` (well-foundedness of ℕ, via `descent_with_strict_steps_reaches_floor`); the ν
    side's convergence is TC05's contraction and its non-arrival is `padic_orbit_never_reaches_zero`.
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
