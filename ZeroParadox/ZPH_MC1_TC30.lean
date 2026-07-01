-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import ZeroParadox.ZPH_MC1_TC05
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC30 — the contraction-rate dichotomy at the p-adic floor #3

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC05 showed that the p-adic floor #3 (`{0} ⊆ Q₂`) is a *global attractor* of the single
doubling map `x ↦ 2·x`: every orbit `2ⁿ·x → 0`. That result used the multiplier `c = 2`.
TC30's modest contribution is to specialize standard normed-field dynamics to the `ℚ_[2]`
floor and read the contraction criterion as the *valuation ideal* (`‖c‖ < 1`, equivalently
`2 ∣ c`): which scalar multipliers see the snap floor as an attractor, in valuation terms.

**Honest scope.** The central convergence iff (`pure_orbit_tendsto_zero_iff_norm_lt_one`) is
**not** an original result of this file. It is a verbatim re-export of Mathlib's
`tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` specialized to `Q₂`. The genuine, citable delta
of this file is narrow and is witnessed *in-statement* by `nat_orbit_tendsto_zero_iff_two_dvd`:
(i) reading the general normed-field criterion `‖c‖ < 1` as the 2-adic valuation ideal `2 ∣ c`
(via Mathlib's `Padic.norm_natCast_lt_one_iff`) and composing it with the convergence iff so
that the load-bearing claim — *a natural multiplier `k` sees the floor as an attractor iff
`2 ∣ k`* — lives in the theorem statement, and (ii) the short specializations of standard
normed-multiplicativity to the two regimes (ideal vs unit) at the `ℚ_[2]` floor.

The re-exported dichotomy, stated as an iff in the theorem (Mathlib lemma, specialized):

- `pure_orbit_tendsto_zero_iff_norm_lt_one` — for any `c : Q₂`,
  `Tendsto (fun n => c^n) atTop (nhds 0) ↔ ‖c‖ < 1`. This is Mathlib's
  `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` at the type `Q₂` (no new mathematical content);
  the pure-multiplier orbit collapses to `0` exactly when the multiplier lies strictly inside
  the unit ball. The value added here is reading the `‖c‖ < 1` side as `2 ∣ c`.

The two halves of the dichotomy, each witnessed in-statement:

- **Attractor half (GO).** `contraction_orbit_tendsto_zero` — for `‖c‖ < 1`, the *global*
  attractor property holds: `∀ x, Tendsto (fun n => c^n * x) atTop (nhds 0)`. Generalizes
  `ZPH_MC1_TC05.doubling_orbit_tendsto_zero` from `c = 2` to every ideal element.
- **Non-attractor half (GO).** `unit_orbit_norm_const` — for a 2-adic unit `u` (`‖u‖ = 1`)
  and any `x`, `‖u^n * x‖ = ‖x‖` for all `n`: the orbit's norm is *constant*, so for `x ≠ 0`
  it never enters a small ball around `0` and `unit_orbit_not_tendsto_zero` shows it does NOT
  tend to `0`.

The valuation reading of the criterion (`‖c‖ < 1 ↔ 2 ∣ c`) is recorded in
`norm_lt_one_iff_two_dvd`, and the concrete witnesses for both regimes are
`two_is_contraction` (`‖2‖ < 1`, the ideal case) and `three_is_unit` (`‖3‖ = 1`, the unit
case, via coprimality of `2` and `3`).

This is an edge test on node #3 of the bottom-diagram tree (`tree_test_campaign_2026-06-29.md`):
it reads the standard normed-field convergence dichotomy in valuation terms at the `ℚ_[2]`
floor. It is a specialization of library results, not an original theorem; it carries no
cross-node identity claim.
-/

namespace ZeroParadox.ZPH_MC1_TC30

open ZeroParadox.ZPB
open Filter Topology

/-! ### The valuation criterion -/

/-- The contraction criterion is the valuation ideal: `‖c‖ < 1 ↔ 2 ∣ c` (i.e. `c` lies in the
    maximal ideal of the 2-adic integers). This is what makes the dichotomy a *valuation* fact
    rather than a fact about the number `2`. -/
theorem norm_lt_one_iff_two_dvd (k : ℕ) : ‖((k : ℕ) : Q₂)‖ < 1 ↔ 2 ∣ k :=
  Padic.norm_natCast_lt_one_iff (p := 2) (n := k)

/-- Witness, ideal regime: `‖2‖ < 1`. The doubling multiplier of TC05 is one element of the
    ideal, not the source of the attractor property. -/
theorem two_is_contraction : ‖(2 : Q₂)‖ < 1 := ZPH_MC1_TC05.doubling_norm_lt_one

/-- Witness, unit regime: `‖3‖ = 1`. `3` is a 2-adic unit (coprime to `2`), so its orbit is
    norm-preserving, not contracting. -/
theorem three_is_unit : ‖(3 : Q₂)‖ = 1 := by
  have h : ‖((3 : ℕ) : Q₂)‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    decide
  simpa using h

/-! ### The convergence dichotomy (re-exported Mathlib lemma, specialized to `Q₂`) -/

/-- **Re-export of a Mathlib lemma, specialized to `Q₂`.** For every multiplier `c : Q₂`, the
    pure orbit `n ↦ cⁿ` converges to the snap floor `0` exactly when `‖c‖ < 1`. This is
    `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` at the type `Q₂` — a verbatim term-mode
    re-export with **no new mathematical content**. It is kept here only as the named anchor
    for reading the `‖c‖ < 1` side as the 2-adic valuation ideal `2 ∣ c`
    (`norm_lt_one_iff_two_dvd`); the iff itself is library, not a finding of this file. -/
theorem pure_orbit_tendsto_zero_iff_norm_lt_one (c : Q₂) :
    Tendsto (fun n : ℕ => c ^ n) atTop (nhds 0) ↔ ‖c‖ < 1 :=
  tendsto_pow_atTop_nhds_zero_iff_norm_lt_one

/-- **The valuation reading, in-statement.** This is the file's actual delta over the library
    re-export: for a natural-number multiplier `k`, the pure orbit `n ↦ kⁿ` collapses to the
    snap floor `0` **exactly when `2 ∣ k`**. The convergence side is Mathlib's iff
    (`pure_orbit_tendsto_zero_iff_norm_lt_one`); the divisibility side is the 2-adic valuation
    reading of `‖·‖ < 1` (`norm_lt_one_iff_two_dvd`). Composing them puts the load-bearing
    valuation claim — *which multipliers see the floor as an attractor, in arithmetic terms* —
    inside the theorem statement, not only the docstring. The two named witnesses below
    instantiate the two sides: `2` (`2 ∣ 2`, attractor) and `3` (`¬ 2 ∣ 3`, unit). -/
theorem nat_orbit_tendsto_zero_iff_two_dvd (k : ℕ) :
    Tendsto (fun n : ℕ => ((k : Q₂)) ^ n) atTop (nhds 0) ↔ 2 ∣ k := by
  rw [pure_orbit_tendsto_zero_iff_norm_lt_one, norm_lt_one_iff_two_dvd]

/-! ### Attractor half (GO): the global attractor for any ideal multiplier -/

/-- Global attractor for the whole ideal (standard normed-field decay, specialized). For any
    multiplier with `‖c‖ < 1`, the orbit of every starting point converges to the snap floor
    `0`: `∀ x, cⁿ·x → 0`. Proof is the routine `‖cⁿ·x‖ = ‖c‖ⁿ·‖x‖ → 0`. This generalizes
    `ZPH_MC1_TC05.doubling_orbit_tendsto_zero` (the `c = 2` case) to every element of the
    valuation ideal `2 ∣ c`. -/
theorem contraction_orbit_tendsto_zero {c : Q₂} (hc : ‖c‖ < 1) (x : Q₂) :
    Tendsto (fun n : ℕ => c ^ n * x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun n : ℕ => ‖c ^ n * x‖) = fun n : ℕ => ‖c‖ ^ n * ‖x‖ := by
    funext n; rw [norm_mul, norm_pow]
  rw [hnorm]
  have hbase : Tendsto (fun n : ℕ => ‖c‖ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hc
  simpa using hbase.mul_const ‖x‖

/-! ### Non-attractor half (GO): unit multipliers preserve norm, so they are NOT attractors -/

/-- Non-attractor for units (routine normed-multiplicativity). For a 2-adic unit `u` (`‖u‖ = 1`)
    and any starting point `x`, the orbit's norm is constant: `‖uⁿ·x‖ = ‖x‖` for all `n`. Used
    below to show the unit orbit does not converge to `0` from a nonzero start. -/
theorem unit_orbit_norm_const {u : Q₂} (hu : ‖u‖ = 1) (x : Q₂) (n : ℕ) :
    ‖u ^ n * x‖ = ‖x‖ := by
  rw [norm_mul, norm_pow, hu, one_pow, one_mul]

/-- Units are non-attractors. For a 2-adic unit `u` and any `x ≠ 0`, the orbit `uⁿ·x` does NOT
    converge to the snap floor `0`: convergence to `0` would force the norm to tend to `0`, but
    `‖uⁿ·x‖ = ‖x‖ > 0` is constant (above). The contrast with `contraction_orbit_tendsto_zero`
    is decided by the valuation: ideal multipliers attract, units do not. -/
theorem unit_orbit_not_tendsto_zero {u : Q₂} (hu : ‖u‖ = 1) {x : Q₂} (hx : x ≠ 0) :
    ¬ Tendsto (fun n : ℕ => u ^ n * x) atTop (nhds 0) := by
  intro htend
  rw [tendsto_zero_iff_norm_tendsto_zero] at htend
  have hconst : (fun n : ℕ => ‖u ^ n * x‖) = fun _ : ℕ => ‖x‖ := by
    funext n; exact unit_orbit_norm_const hu x n
  rw [hconst] at htend
  have hlim : (0 : ℝ) = ‖x‖ := tendsto_nhds_unique htend tendsto_const_nhds
  exact hx (norm_eq_zero.mp hlim.symm)

/-- The concrete dichotomy witness: `3` (a unit) has a non-converging nonzero orbit, while `2`
    (in the ideal) is the TC05 contraction. Stated for the unit half at `x = 1`. -/
theorem three_orbit_not_tendsto_zero :
    ¬ Tendsto (fun n : ℕ => (3 : Q₂) ^ n * 1) atTop (nhds 0) :=
  unit_orbit_not_tendsto_zero three_is_unit (one_ne_zero)

end ZeroParadox.ZPH_MC1_TC30

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's analysis/topology library
(`Padic` norms, `Tendsto`, the specific-limits lemmas) — the same dependency carried by
ZP-B and by TC05. It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC30

#print axioms norm_lt_one_iff_two_dvd
#print axioms two_is_contraction
#print axioms three_is_unit
#print axioms pure_orbit_tendsto_zero_iff_norm_lt_one
#print axioms nat_orbit_tendsto_zero_iff_two_dvd
#print axioms contraction_orbit_tendsto_zero
#print axioms unit_orbit_norm_const
#print axioms unit_orbit_not_tendsto_zero
#print axioms three_orbit_not_tendsto_zero

end PurityCheck
