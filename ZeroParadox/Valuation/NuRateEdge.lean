-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The within-ν edge at the orbit-RATE level (#3 ↔ #2)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file is the **rate-level sharpening** of the OPEN within-ν edge `T2`
(`ZeroParadox/Multihomed/TreeT2.lean`). `T2` placed the p-adic floor (#3) and the Markov attractor (#2)
in the same "attractor" vocabulary and proved only the *coarse* global-ambient wall
(connected simplex vs totally-disconnected `Q₂`), which the cold audit correctly flagged as
the **generic** connected/disconnected fact — leaving the genuine ν-edge OPEN.

Here we test the strongest natural bridge between the two ν-systems: a **rate-matching
conjugacy** of their convergence orbits. The two orbits compared are:

- **p-adic orbit** (the doubling map `x ↦ 2x` on `Q₂`, started at `x ≠ 0`): its
  distance-to-floor at step `n` is `padicRate x n := ‖(2 : Q₂)^n * x‖`. Because `Q₂` is a
  normed field with `‖(2:Q₂)‖ = 1/2`, this is `2⁻ⁿ ‖x‖` — a **strictly positive geometric**
  rate at *every* finite step (`padicRate_pos`), strictly decreasing (`padicRate_strictAnti`),
  never reaching the floor in finite time.
- **absorbing Markov orbit** (a chain started at its absorbing/stationary state): its
  distance-to-limit is `markovRate n := 0` — **at the limit from step 0** (`markovRate_zero`).

**What is proved: a strictly positive sequence is never the zero sequence.**

- `no_rate_conjugacy` — for `x ≠ 0` there is no `φ : ℕ → ℕ` with
  `∀ n, padicRate x n = markovRate (φ n)`: the p-adic value is positive at every step and every
  `markovRate` value is `0`.
- `no_rate_orderIso` — for `x ≠ 0` no pair `n, m` has `padicRate x n = markovRate m`.

**SCOPE FENCE: the mismatch is set by the two STARTS, not by the two dynamics.** The chain started
at its absorbing state is at its limit from step 0, and the p-adic orbit from `x ≠ 0` is not.
Started at its floor, the p-adic orbit has the identical profile, `padicRate 0 n = markovRate n`
(the `example` after `no_rate_orderIso`). The rate comparison of the two dynamics is
`padic_markov_shared_rate_envelope` (`ZeroParadox/Valuation/NuRateMatch.lean`): an irreducible
chain whose imbalance decays at the p-adic envelope `(1/2)ⁿ`. So this file is no evidence that the
within-ν edge #3↔#2 is obstructed at the rate level, and it does not change T2's status.

`markovRate` is the distance-to-limit of one start of one chain (constantly `0`), not #2's
convergence-rate sequence. The p-adic side is the doubling-map orbit on `Q₂` from `x`.
-/

namespace ZeroParadox

open ZeroParadox

/-- The p-adic doubling orbit's **distance-to-floor** at step `n`, started at `x`:
    `‖(2:Q₂)^n · x‖`. This is the deterministic-ν (#3) convergence-rate sequence. -/
noncomputable def padicRate (x : Q₂) (n : ℕ) : ℝ := ‖(2 : Q₂) ^ n * x‖

/-- The absorbing/stationary Markov orbit's **distance-to-limit** at step `n`: `0`.
    Started at its absorbing state, the chain is at its limit from step `0` onward.
    This records the START, not a rate of #2: the chain of `padic_markov_shared_rate_envelope`
    decays at `(1/2)ⁿ` off balance and is `0` throughout from a balanced start. -/
def markovRate (_n : ℕ) : ℝ := 0

/-- Closed form: the p-adic rate is the geometric sequence `2⁻ⁿ ‖x‖`. -/
theorem padicRate_eq (x : Q₂) (n : ℕ) :
    padicRate x n = (2 : ℝ) ^ (-(n : ℤ)) * ‖x‖ := by
  unfold padicRate
  have h2 : ((2 : Q₂)) = ((2 : ℕ) : Q₂) := by norm_num
  rw [norm_mul, h2, Padic.norm_p_pow]
  norm_num

/-- **Geometric, strictly positive at every finite step.** For `x ≠ 0`, the p-adic orbit's
    distance to the floor is `> 0` at *every* `n` — it never reaches the floor in finite time. -/
theorem padicRate_pos {x : Q₂} (hx : x ≠ 0) (n : ℕ) : 0 < padicRate x n := by
  rw [padicRate_eq]
  apply mul_pos
  · positivity
  · exact norm_pos_iff.mpr hx

/-- The p-adic rate is **strictly decreasing** (genuine geometric decay) for `x ≠ 0`. -/
theorem padicRate_strictAnti {x : Q₂} (hx : x ≠ 0) : StrictAnti (padicRate x) := by
  intro a b hab
  rw [padicRate_eq, padicRate_eq]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  apply mul_lt_mul_of_pos_right _ hxpos
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
  omega

/-- Every Markov rate value is `0` — at the limit from step `0` onward. -/
theorem markovRate_zero (n : ℕ) : markovRate n = 0 := rfl

/-- **The per-step value clash.** For `x ≠ 0`, no `padicRate x n` equals any `markovRate m`:
    the first is positive (`padicRate_pos`), the second `0`. The two starts differ, `x ≠ 0`
    against the absorbing state; at `x = 0` the values agree. -/
theorem padic_ne_markov {x : Q₂} (hx : x ≠ 0) (n m : ℕ) :
    padicRate x n ≠ markovRate m := by
  rw [markovRate_zero]
  exact ne_of_gt (padicRate_pos hx n)

/-- `Statement:` for `x ≠ 0` there is no `φ : ℕ → ℕ` with `padicRate x n = markovRate (φ n)`
    at every `n`. `Reading:` the pre-registered no-go proves for these two STARTS only; from
    `x = 0` the match holds with `φ = id` (the `example` below), and the two dynamics share the
    envelope `(1/2)ⁿ` (`padic_markov_shared_rate_envelope`). Not an obstruction of edge #3↔#2. -/
theorem no_rate_conjugacy {x : Q₂} (hx : x ≠ 0) :
    ¬ ∃ φ : ℕ → ℕ, ∀ n, padicRate x n = markovRate (φ n) := by
  rintro ⟨φ, hφ⟩
  exact padic_ne_markov hx 0 (φ 0) (hφ 0)

/-- `Statement:` for `x ≠ 0`, no `(n, m)` has `padicRate x n = markovRate m`
    (`padic_ne_markov`): the two sequences share no value. -/
theorem no_rate_orderIso {x : Q₂} (hx : x ≠ 0) :
    ¬ ∃ (n m : ℕ), padicRate x n = markovRate m := by
  rintro ⟨n, m, h⟩
  exact padic_ne_markov hx n m h

-- Statement: CONTROL: started at its floor, the p-adic orbit has `markovRate`'s profile, step by step.
example (n : ℕ) : padicRate 0 n = markovRate n := by simp [padicRate, markovRate]

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's `ℚ_[p]` normed-field / p-adic norm
library (`padicNormE.norm_p`, `norm_mul`, `norm_pow`, `norm_pos_iff`), the same dependency
carried by ZP-B. It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox

#print axioms padicRate_eq
#print axioms padicRate_pos
#print axioms padicRate_strictAnti
#print axioms padic_ne_markov
#print axioms no_rate_conjugacy
#print axioms no_rate_orderIso

end PurityCheck
