import ZeroParadox.ZPH_MC1_TC05
import ZeroParadox.ZPH_MeanErgodic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Direction A, Cycle A3 — the place is load-bearing in the DYNAMICS: ⊥ as a place-relative limit

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

A1/A2 put the place into the *static* structure (norms, the product formula). A3 makes it deeper: the
place is load-bearing in the **dynamics** — *how each bottom is reached* — and the same map behaves
oppositely at the two place-types, which is the framework's 0/∞ duality made concrete.

- `node3_contracts_2adic` — #3's floor `0` is reached as the limit of the doubling orbit `x ↦ 2x` in the
  **non-archimedean** 2-adic metric (cite TC05): `2ⁿx → 0`. Multiplication by 2 is a *contraction* at p=2.
- `doubling_expands_archimedean` — doubling at the **archimedean** place *expands*: `|2ⁿx| → ∞` for
  `x ≠ 0`. (New.)
- `doubling_place_dichotomy` — the statement: the same **rational orbit** `2ⁿx`, embedded into the two
  completions of ℚ, converges oppositely — to **⊥ (0) in `Q₂`** (the 2-adic place) and to **∞ in ℝ**
  (the archimedean place). (Honest: these are two different maps — `·` in ℚ₂ vs in ℝ — that agree on the
  embedded ℚ; the theorem is the conjunction of the two halves sharing source `x : ℚ`.) The
  interpretive reading: this is the 0/∞ duality (the Riemann-sphere keystone), i.e. the consequence of
  `‖2‖₂ < 1 < |2|` — the place-type fixes contraction-to-⊥ vs escape-to-∞. The norm inequality is the
  fact; "0/∞ duality" is its reading. (New content over the re-exports = `doubling_expands_archimedean`
  plus this shared-source packaging.)
- `markov_attractor_archimedean` — #2's stationary bottom is reached as the limit of Birkhoff averages
  in the **archimedean** (ℝ/ℂ) metric (cite the mean-ergodic theorem). So #2 is an archimedean-metric
  contraction limit, #3 a non-archimedean one: ⊥ is a *place-relative* limit in both.

**Honest scope.** `node3_contracts_2adic` and `markov_attractor_archimedean` are re-exports (TC05,
mean-ergodic) — included so both bottoms' dynamics sit in one file. The genuine new content is
`doubling_expands_archimedean` + `doubling_place_dichotomy`: the place-dependence of the same map's
dynamics. Still within the number-theoretic bottoms (the ℝ/ℚ₂ places); does not touch the categorical
bottoms (walled).
-/

namespace ZeroParadox.ZPH_PlaceMetric

open Filter Topology

/-- #3 reached by contraction in the **non-archimedean** metric: the doubling orbit `2ⁿx → 0` in `Q₂`
    (cite TC05). Multiplication by 2 contracts to the floor at the 2-adic place. -/
theorem node3_contracts_2adic (x : ℚ_[2]) :
    Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n * x) atTop (𝓝 0) :=
  ZeroParadox.ZPH_MC1_TC05.doubling_orbit_tendsto_zero x

/-- The **same** map `x ↦ 2x` at the **archimedean** place EXPANDS: `|2ⁿx| → ∞` for `x ≠ 0`. -/
theorem doubling_expands_archimedean (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => |(2 : ℝ) ^ n * x|) atTop atTop := by
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hx' : 0 < |x| := abs_pos.mpr hx
  have hmul : Tendsto (fun n : ℕ => (2 : ℝ) ^ n * |x|) atTop atTop :=
    h2.atTop_mul_const hx'
  refine hmul.congr (fun n => ?_)
  rw [abs_mul, abs_pow]
  norm_num

/-- **A3 — the place dichotomy.** The same rational orbit `2ⁿx`, embedded into the two completions of
    ℚ, converges oppositely: to **⊥ (0) in `Q₂`** (2-adic place) and to **∞ in ℝ** (archimedean place).
    (These are two maps — multiplication in ℚ₂ vs ℝ — agreeing on the embedded ℚ; this bundles the two
    halves sharing source `x : ℚ`.) Interpretive reading: the 0/∞ duality, i.e. the consequence of
    `‖2‖₂ < 1 < |2|`. -/
theorem doubling_place_dichotomy (x : ℚ) (hx : x ≠ 0) :
    Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n * (x : ℚ_[2])) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => |(2 : ℝ) ^ n * (x : ℝ)|) atTop atTop :=
  ⟨node3_contracts_2adic (x : ℚ_[2]),
    doubling_expands_archimedean (x : ℝ) (by exact_mod_cast hx)⟩

/-- #2 reached by contraction in the **archimedean** metric: the Markov stationary bottom is the limit
    of Birkhoff averages of the transfer operator in the ℝ/ℂ norm (cite the mean-ergodic theorem). -/
theorem markov_attractor_archimedean {n : ℕ} (f : Fin n → PMF (Fin n))
    (hd : ZeroParadox.MeanErgodic.DoublyStochastic f) (x : EuclideanSpace ℂ (Fin n)) :
    ∃ y, Tendsto (fun N => birkhoffAverage ℂ (ZeroParadox.MeanErgodic.T₂ f) id N x)
      atTop (𝓝 y) :=
  ZeroParadox.MeanErgodic.doubly_stochastic_mean_ergodic f hd x

end ZeroParadox.ZPH_PlaceMetric

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_PlaceMetric

#print axioms node3_contracts_2adic
#print axioms doubling_expands_archimedean
#print axioms doubling_place_dichotomy
#print axioms markov_attractor_archimedean

end PurityCheck
