-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC33 — the within-ν edge at the orbit-RATE level (#3 ↔ #2)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file is the **rate-level sharpening** of the OPEN within-ν edge `T2`
(`ZPH_MC1_TreeT2.lean`). `T2` placed the p-adic floor (#3) and the Markov attractor (#2)
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

**Race outcome: NO-GO (the pre-registered obstruction proves).** The two convergence
*profiles* are value-incompatible:

- `no_rate_conjugacy` — for `x ≠ 0` there is **no reparametrization** `φ : ℕ → ℕ` matching the
  two orbit value-sequences, i.e. no `φ` with `∀ n, padicRate x n = markovRate (φ n)`. The
  p-adic value is positive at every step while every Markov value is `0`. This is the honest
  load-bearing statement: a rate-preserving conjugacy of the orbits cannot exist.
- `no_rate_orderIso` — even at one step the "is-at-limit" predicate clashes: there is no `n, m`
  with `padicRate x n = markovRate m` (`x ≠ 0`). So the orbits do not even share a single rate
  *value*, hence no order-isomorphism of their value-sets can exist.

**WITNESS / SCOPE FENCE.** The load-bearing content is *in* the theorem statements (the
non-existence of a value-matching reparametrization `φ`, and the per-step value clash), not in
the docstring. What this proves is precisely: **the doubling orbit's geometric-positive rate
profile is incompatible with an absorbing chain's at-the-limit-from-step-0 profile** — they
cannot be put in rate-preserving correspondence. What it does NOT claim: that *every* Markov
attractor fails (this is the absorbing/stationary-start representative, the natural ν extreme),
nor that #2 and #3 fail to *glue* in some non-rate sense (T2's singleton-bottoms caveat stands).
It refines the within-ν wall **at the dynamical rate level**: the deterministic-ν orbit and the
stochastic-ν orbit do not share a convergence-rate structure.

`markovRate` is the concrete distance-to-limit sequence of the absorbing chain (constantly `0`);
it is a *representative* of #2's attractor, chosen as the natural extreme (limit reached
immediately). The p-adic side is the genuine doubling-map orbit on `Q₂`.
-/

namespace ZeroParadox.ZPH_MC1_TC33

open ZeroParadox.ZPB

/-- The p-adic doubling orbit's **distance-to-floor** at step `n`, started at `x`:
    `‖(2:Q₂)^n · x‖`. This is the deterministic-ν (#3) convergence-rate sequence. -/
noncomputable def padicRate (x : Q₂) (n : ℕ) : ℝ := ‖(2 : Q₂) ^ n * x‖

/-- The absorbing/stationary Markov orbit's **distance-to-limit** at step `n`: `0`.
    Started at its absorbing state, the chain is at its limit from step `0` onward.
    This is the stochastic-ν (#2) convergence-rate sequence (the natural extreme
    representative — limit reached immediately). -/
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

/-- **The per-step value clash (the obstruction core).** For `x ≠ 0`, no p-adic-orbit step
    value equals any Markov-orbit step value: the deterministic-ν orbit is strictly positive
    at every finite step while the stochastic-ν (absorbing) orbit is `0` at every step. So the
    two ν-orbits do not share even a single convergence-rate value. -/
theorem padic_ne_markov {x : Q₂} (hx : x ≠ 0) (n m : ℕ) :
    padicRate x n ≠ markovRate m := by
  rw [markovRate_zero]
  exact ne_of_gt (padicRate_pos hx n)

/-- **NO-GO (pre-registered): no rate-matching conjugacy.** For `x ≠ 0` there is no
    reparametrization `φ : ℕ → ℕ` carrying the p-adic doubling orbit's rate sequence onto the
    absorbing Markov orbit's rate sequence. A rate-preserving conjugacy of the two ν-attractor
    orbits would require exactly such a `φ` (matching distance-to-limit step by step); the
    geometric-positive p-adic profile cannot be matched to the at-the-limit Markov profile.

    This is the load-bearing refinement of T2 at the dynamical rate level: the within-ν edge
    #3↔#2 is **obstructed** when compared by orbit rate, not merely by global ambient topology. -/
theorem no_rate_conjugacy {x : Q₂} (hx : x ≠ 0) :
    ¬ ∃ φ : ℕ → ℕ, ∀ n, padicRate x n = markovRate (φ n) := by
  rintro ⟨φ, hφ⟩
  exact padic_ne_markov hx 0 (φ 0) (hφ 0)

/-- **No order-isomorphism of the rate value-sets.** Since the two ν-orbits share no rate
    value (`padic_ne_markov`), there is no `(n, m)` placing a p-adic rate equal to a Markov
    rate — a fortiori no order-isomorphism between the two orbits' value-sequences can exist.
    Stated as the non-existence of a single common value. -/
theorem no_rate_orderIso {x : Q₂} (hx : x ≠ 0) :
    ¬ ∃ (n m : ℕ), padicRate x n = markovRate m := by
  rintro ⟨n, m, h⟩
  exact padic_ne_markov hx n m h

end ZeroParadox.ZPH_MC1_TC33

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's `ℚ_[p]` normed-field / p-adic norm
library (`padicNormE.norm_p`, `norm_mul`, `norm_pow`, `norm_pos_iff`), the same dependency
carried by ZP-B. It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC33

#print axioms padicRate_eq
#print axioms padicRate_pos
#print axioms padicRate_strictAnti
#print axioms padic_ne_markov
#print axioms no_rate_conjugacy
#print axioms no_rate_orderIso

end PurityCheck
