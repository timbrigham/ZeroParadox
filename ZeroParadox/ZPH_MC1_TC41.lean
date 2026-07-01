-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC41 — Axis IV: convergence-rate class as a cross-root invariant

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC33/TC34 established that the p-adic ν-floor (#3, geometric orbit `2⁻ⁿ`) and the Markov
attractor (#2, absorbing) are *rate*-obstructed. This file probes a finer question: among
sequences that all reach the floor, is **convergence-rate class** (geometric vs linear) a
separating invariant that cuts *across* the well-founded/non-well-founded root (Axis I)?

The objects under test are three concrete descent sequences to the floor:

- **geometric** `g n = 2⁻ⁿ` (the #3 p-adic orbit's rate; never reaches `0` over ℝ);
- **linear / Goodstein-style** `a₀ - n` (the canonical finite well-founded descent, #1);
- **binary-halving** `⌊a₀ / 2ⁿ⌋` (a well-founded ℕ-descent that is *also* geometric base ½).

"Rate-preserving correspondence" between two nonnegative sequences `s, t` is taken to be a
**bounded ratio**: `∃ C, ∀ n, s n ≤ C · t n`. Two sequences are *rate-matched* when each
bounds the other up to a constant; *rate-separated* when no such constant exists in (at least)
one direction.

### What is proved (load-bearing, in-statement)

- `linear_overtakes_geometric` — **the NO-GO (Axis IV separation).** No constant `C` makes the
  linear count `n` bounded by `C · 2⁻ⁿ`: for every `C` there is an `n` with `(n:ℝ) > C · 2⁻ⁿ`.
  Geometric decay strictly out-paces linear, so there is *no* rate-preserving map from a linear
  descent into the geometric orbit. This is a genuine cross-root wall (linear descent is #1, a
  μ/well-founded object; geometric orbit is #3, a ν object) that is **finer than Axis I** —
  it separates by rate class, not by well-foundedness.

- `halving_dominated_by_geometric` — **the refined GO (one direction only).** The binary-halving
  ℕ-descent *is* in the geometric rate class from above: `(⌊a₀/2ⁿ⌋ : ℝ) ≤ a₀ · 2⁻ⁿ` for all `n`.
  So a geometric μ-descent is bounded by a constant times the geometric ν-orbit — the within-class
  reconciliation the GO conjecture predicted, but **only as an upper envelope**.

- `halving_terminates` / `halving_not_matched_below` — **the honest twist that defeats the literal
  two-sided GO.** The binary-halving descent over ℕ *reaches `0` in finitely many steps*
  (`⌊a₀/2ⁿ⌋ = 0` once `a₀ < 2ⁿ`), whereas `2⁻ⁿ > 0` for every `n`. Hence there is **no** lower
  rate-match `∃ c > 0, ∀ n, c · 2⁻ⁿ ≤ ⌊a₀/2ⁿ⌋`: the well-founded ℕ-descent and the real geometric
  orbit are rate-separated *below* even when they share the base ½. Well-foundedness reasserts
  itself as a tail phenomenon: terminating descent cannot two-sidedly track a non-terminating orbit.

### Honest verdict — NO-GO (with a one-sided GO), opening Axis IV

The pre-registered GO ("a geometric ℕ-descent rate-MATCHES the geometric orbit") holds only as an
*upper* envelope; the literal two-sided match is **false** because the ℕ-descent terminates. The
pre-registered NO-GO (linear is rate-incompatible with geometric) **proves**. Together:
convergence-rate class is a real separating invariant (Axis IV) — but the cleanest reading is that
*termination* (the μ/well-founded signature) is what blocks the two-sided match, so Axis IV does not
fully decouple from Axis I; it refines it. No single constant reconciles a terminating descent with
a non-terminating orbit, in either the linear or the geometric base.

### What is interpretation, not Lean

The labels "#1/#2/#3", "Axis IV", "cross-root", and the tree placement are framework reading. The
Lean content is exactly: three explicit real/ℕ sequences and two-sided bounded-ratio (non-)existence
facts about them. No categorical or p-adic object is invoked here — the claim is purely about the
*rate functions* those bottoms converge at.
-/

namespace ZeroParadox.ZPH_MC1_TC41

/-- The geometric rate `2⁻ⁿ : ℝ` — the #3 p-adic orbit's convergence rate. -/
noncomputable def geo (n : ℕ) : ℝ := (2 : ℝ) ^ (-(n : ℤ))

theorem geo_pos (n : ℕ) : 0 < geo n := by
  unfold geo; positivity

theorem geo_le_one (n : ℕ) : geo n ≤ 1 := by
  unfold geo
  rw [zpow_neg, zpow_natCast]
  rw [inv_le_one_iff₀]
  right
  exact one_le_pow₀ (by norm_num)

/-! ### NO-GO — linear descent is rate-incompatible with the geometric orbit (Axis IV wall) -/

/-- **NO-GO (the Axis IV separation, load-bearing).** No constant `C` bounds the linear count `n`
    by `C · 2⁻ⁿ`: for every `C` there is an `n` with `(n : ℝ) > C · geo n`. So there is no
    rate-preserving (bounded-ratio) correspondence sending a *linear* well-founded descent into the
    *geometric* p-adic orbit. Geometric strictly out-paces linear — a wall finer than Axis I
    (well-founded vs not), since it ranks two descents that both reach the floor. -/
theorem linear_overtakes_geometric (C : ℝ) : ∃ n : ℕ, (n : ℝ) > C * geo n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  refine ⟨n, ?_⟩
  have hCn : C ≤ (n : ℝ) := le_trans (le_max_left C 0) hn.le
  have hgeo : geo n ≤ 1 := geo_le_one n
  -- C * geo n ≤ |C| · 1 ... cleanest: split on sign of C
  rcases le_or_gt C 0 with hC | hC
  · -- C ≤ 0, geo n > 0, so C * geo n ≤ 0 < n
    have h0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right C 0) hn
    have : C * geo n ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC (geo_pos n).le
    linarith
  · -- 0 < C: C * geo n ≤ C * 1 = C < n  (n > max C 0 ≥ C, strictly)
    have hlt : C < (n : ℝ) := lt_of_le_of_lt (le_max_left C 0) hn
    have hstep : C * geo n ≤ C * 1 := by
      apply mul_le_mul_of_nonneg_left hgeo hC.le
    rw [mul_one] at hstep
    linarith

/-- Corollary phrasing: the ratio function `n ↦ n / geo n` is unbounded above (no constant
    dominates it), which is the standard "no rate-preserving map" statement for the linear→geometric
    direction. -/
theorem linear_geo_ratio_unbounded :
    ∀ C : ℝ, ∃ n : ℕ, C < (n : ℝ) / geo n := by
  intro C
  obtain ⟨n, hn⟩ := linear_overtakes_geometric C
  refine ⟨n, ?_⟩
  rw [lt_div_iff₀ (geo_pos n)]
  linarith [hn]

/-! ### Refined GO — binary halving is dominated by the geometric orbit (upper envelope only) -/

/-- **Refined GO (one-sided, load-bearing).** The binary-halving ℕ-descent `⌊a₀ / 2ⁿ⌋` is in the
    geometric rate class *from above*: `(⌊a₀/2ⁿ⌋ : ℝ) ≤ a₀ · 2⁻ⁿ` for every `n`. A geometric
    μ-descent is bounded by a constant (`a₀`) times the geometric ν-orbit — the within-rate-class
    upper-envelope match the GO conjecture predicted. -/
theorem halving_dominated_by_geometric (a₀ : ℕ) (n : ℕ) :
    ((a₀ / 2 ^ n : ℕ) : ℝ) ≤ (a₀ : ℝ) * geo n := by
  have hcast : ((a₀ / 2 ^ n : ℕ) : ℝ) ≤ (a₀ : ℝ) / ((2 ^ n : ℕ) : ℝ) := Nat.cast_div_le
  refine le_trans hcast ?_
  unfold geo
  rw [zpow_neg, zpow_natCast, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]

/-! ### The honest twist — binary halving TERMINATES, so the two-sided match FAILS -/

/-- The binary-halving ℕ-descent reaches `0` in finitely many steps: once `a₀ < 2ⁿ`,
    `⌊a₀ / 2ⁿ⌋ = 0`. (`a₀ < 2^(a₀)` always, so `n = a₀` suffices.) -/
theorem halving_terminates (a₀ : ℕ) : ∃ N : ℕ, a₀ / 2 ^ N = 0 := by
  refine ⟨a₀, ?_⟩
  apply Nat.div_eq_of_lt
  exact Nat.lt_two_pow_self

/-- **The honest twist (load-bearing NO-GO below).** There is *no* lower rate-match between the
    binary-halving ℕ-descent and the geometric real orbit: no positive constant `c` satisfies
    `c · 2⁻ⁿ ≤ ⌊a₀/2ⁿ⌋` for all `n`, because the left side stays strictly positive while the right
    side becomes `0` once the descent terminates. So even sharing base ½, the *terminating*
    well-founded ℕ-descent (#1, μ) and the *non-terminating* geometric orbit (#3, ν) are
    rate-separated below — termination (the μ signature) blocks the two-sided match. -/
theorem halving_not_matched_below (a₀ : ℕ) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * geo n ≤ ((a₀ / 2 ^ n : ℕ) : ℝ) := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨N, hN⟩ := halving_terminates a₀
  have hlhs : 0 < c * geo N := mul_pos hc (geo_pos N)
  have hrhs : ((a₀ / 2 ^ N : ℕ) : ℝ) = 0 := by rw [hN]; simp
  have := hbound N
  rw [hrhs] at this
  linarith

/-- **TC41 capstone (Axis IV, witnessed not narrated).** The three rate facts, bundled:
    (a) linear descent overtakes any constant multiple of the geometric orbit — no rate-preserving
    map linear→geometric (the NO-GO wall); (b) binary halving is dominated by the geometric orbit
    up to constant `a₀` (the one-sided GO); (c) binary halving has *no* lower rate-match with the
    geometric orbit because it terminates. So convergence-rate class is a genuine separating
    invariant, but the two-sided match is blocked by termination — Axis IV refines, rather than
    decouples from, the well-founded fork (Axis I). -/
theorem tc41_rate_class_axis (a₀ : ℕ) :
    (∀ C : ℝ, ∃ n : ℕ, (n : ℝ) > C * geo n) ∧
    (∀ n : ℕ, ((a₀ / 2 ^ n : ℕ) : ℝ) ≤ (a₀ : ℝ) * geo n) ∧
    (¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, c * geo n ≤ ((a₀ / 2 ^ n : ℕ) : ℝ)) :=
  ⟨linear_overtakes_geometric, halving_dominated_by_geometric a₀, halving_not_matched_below a₀⟩

end ZeroParadox.ZPH_MC1_TC41

/-! ## Axiom Purity Check

Expected footprint `[propext, Classical.choice, Quot.sound]` — `Classical.choice` enters via
Mathlib's real-analysis / archimedean library (`exists_nat_gt`, `zpow`, ordered-field lemmas), a
library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC41

#print axioms geo_le_one
#print axioms linear_overtakes_geometric
#print axioms linear_geo_ratio_unbounded
#print axioms halving_dominated_by_geometric
#print axioms halving_terminates
#print axioms halving_not_matched_below
#print axioms tc41_rate_class_axis

end PurityCheck
