-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_TC39
import ZeroParadox.ZPH_MC1_TC36
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC43 — within-ν geometric-rate match: #2 (irreducible Markov) and #3 (p-adic) share rate 1/2

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file runs one go/no-go cycle on the within-ν rate edge between bottom-diagram nodes #2 (the
Markov stationary attractor, ν-dynamical) and #3 (the p-adic floor `{0} ⊆ Q₂`, ν-limit).

**Background — the obstruction TC43 answers.** TC33 obstructed the #3↔#2 edge *at the rate level* by
comparing the p-adic GEOMETRIC orbit (distance `2^(-n)`) against an ABSORBING Markov orbit (distance
identically `0`): geometric-vs-absorbing is a rate mismatch. TC39 then built a genuinely GEOMETRIC
Markov attractor on `Fin 2 → ℝ`: the symmetric doubly-stochastic kernel `P_a` contracts the imbalance
`v 0 - v 1` by the subdominant eigenvalue `1 - 2a` per step, so
`imb (P_aᵏ v₀) = (1 - 2a)ᵏ · imb v₀` (`ZPH_MC1_TC39.markov_imbalance_pow`). TC43 tests the natural
follow-up: **choose the spectral gap to match the p-adic rate.** Set `a = 1/4`, so `1 - 2a = 1/2`.
Then the Markov imbalance decays as `(1/2)ᵏ` — the SAME geometric envelope TC36 showed bounds the
p-adic #3 orbit (`padic_orbit_norm`: `‖2ⁿ·x‖ = 2^(-n)·‖x‖`, and `2^(-n) = (1/2)ⁿ`).

**GO half (the within-ν rate match, in-statement).**
- `markov_imbalance_quarter`: with `a = 1/4`, `imb (P^ᵏ v₀) = (1/2)ᵏ · imb v₀` (exact).
- `padic_orbit_half`: `‖2ⁿ·x‖ = (1/2)ⁿ · ‖x‖` (exact; `padic_orbit_norm` restated with `2^(-n)=(1/2)ⁿ`).
- `tc43_shared_rate_half`: BOTH distance sequences are exactly `C · (1/2)ⁿ` (the Markov side with
  `C₂ = imb v₀` on the imbalance functional, the p-adic side with `C₃ = ‖x‖`), and the single envelope
  `(1/2)ⁿ → 0` dominates both. The two ν-attractors share the rate **constant** `1/2`, witnessed
  in-statement — an **envelope match**, NOT an orbit isomorphism. This is the within-ν analog of TC36's
  cross-root envelope match, and the rate-level COMPLEMENT to TC33's mismatch: geometric-vs-geometric
  matches where geometric-vs-absorbing did not.

**NO-GO residue (the honest fence, also in-statement).** The matched rate does NOT dissolve the
within-ν wall:
- `tc43_no_orbit_correspondence` — for `x ≠ 0` the p-adic orbit distance is **strictly positive at
  every finite step** (`ZPH_MC1_TC36.padic_orbit_pos`), whereas the Markov imbalance, started balanced
  (`imb v₀ = 0`, e.g. the uniform vector), is **identically 0** at every step. So even at matched rate
  1/2 there is no step-for-step distance correspondence: the same envelope can carry a strictly-positive
  p-adic orbit and a degenerate (already-at-floor) Markov orbit. The shared rate is a coincident
  envelope, not an orbit profile — exactly as TC36's cross-root match did not dissolve the μ/ν wall.

**Honest scope — interpretation vs Lean.** What the Lean proves: two real-valued distance sequences are
each exactly `C·(1/2)ⁿ`, dominated by one envelope `→ 0`. The shared rate constant `1/2` is genuine and
in-statement. What is interpretation, NOT Lean: that #2 and #3 are "the same ν-attractor" — they are
not (one lives in a connected simplex `stdSimplex ℝ (Fin 2)`, the other in the totally-disconnected
normed field `Q₂`; `ZPB.t5_totallyDisconnected`). No category, inverse limit, final coalgebra, or
cross-ambient map is built. TC43 is an envelope/rate test on the #2↔#3 ν-edge; the edge stays OPEN at
the orbit level — the rate match is the COMPLEMENT to TC33, not a closure of the wall.
-/

namespace ZeroParadox.ZPH_MC1_TC45

open ZeroParadox.ZPH_MC1_TC39
open ZeroParadox.ZPH_MC1_TC36
open ZeroParadox.ZPB
open Filter Topology

/-! ### The shared envelope `n ↦ (1/2)ⁿ` -/

/-- The shared geometric envelope `n ↦ (1/2)ⁿ` tends to `0`. -/
theorem env_tendsto : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- `(2:ℝ)^(-n) = (1/2)ⁿ`: the p-adic envelope is the shared envelope. -/
theorem padic_env_eq (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = ((1 : ℝ) / 2) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]

/-! ### GO half: the matched-rate identities -/

/-- **Markov side, matched rate.** With `a = 1/4` (spectral gap `|1 - 2a| = 1/2`), the irreducible
    Markov orbit's imbalance is exactly `(1/2)ᵏ · imb v₀`. Specialization of `markov_imbalance_pow`. -/
theorem markov_imbalance_quarter (v₀ : Fin 2 → ℝ) (k : ℕ) :
    imb ((step (1/4))^[k] v₀) = ((1 : ℝ) / 2) ^ k * imb v₀ := by
  rw [markov_imbalance_pow]
  norm_num

/-- **p-adic side, matched rate.** The doubling orbit distance is exactly `(1/2)ⁿ · ‖x‖`. Restatement
    of `padic_orbit_norm` via `padic_env_eq`. -/
theorem padic_orbit_half (x : Q₂) (n : ℕ) :
    ‖(2 : Q₂) ^ n * x‖ = ((1 : ℝ) / 2) ^ n * ‖x‖ := by
  rw [padic_orbit_norm x n, padic_env_eq]

/-- **GO capstone (witness, not narration).** Both ν-attractor distance sequences are exactly the
    single shared envelope `(1/2)ⁿ` scaled by a per-orbit constant (Markov: `imb v₀`; p-adic: `‖x‖`),
    and that envelope `→ 0`. The shared rate **constant** `1/2` is exhibited in-statement — an envelope
    match across the two ν-attractors #2 and #3, NOT an orbit isomorphism. Rate-level complement to
    TC33's geometric-vs-absorbing mismatch. -/
theorem tc43_shared_rate_half (x : Q₂) (v₀ : Fin 2 → ℝ) :
    -- the shared envelope tends to 0
    Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) ∧
    -- #2 (Markov, a = 1/4): imbalance distance is exactly the envelope · (imb v₀)
    (∀ k : ℕ, imb ((step (1/4))^[k] v₀) = ((1 : ℝ) / 2) ^ k * imb v₀) ∧
    -- #3 (p-adic doubling): orbit distance is exactly the envelope · ‖x‖
    (∀ n : ℕ, ‖(2 : Q₂) ^ n * x‖ = ((1 : ℝ) / 2) ^ n * ‖x‖) :=
  ⟨env_tendsto, markov_imbalance_quarter v₀, padic_orbit_half x⟩

/-! ### NO-GO residue: the matched rate does not give an orbit correspondence -/

/-- **The honest NO-GO residue (in-statement).** The matched rate `1/2` is a coincident *envelope*, not
    an orbit profile. For `x ≠ 0` the p-adic orbit distance is strictly positive at every finite step,
    while the Markov imbalance started balanced (`imb v₀ = 0`, e.g. the uniform vector) is identically
    `0` at every step. So the single envelope `(1/2)ⁿ` simultaneously carries a strictly-positive
    p-adic orbit and a degenerate at-floor Markov orbit: there is no step-for-step distance
    correspondence even at matched rate. The within-ν #2↔#3 edge stays OPEN at the orbit level — exactly
    as TC36's cross-root envelope match did not dissolve the wall. -/
theorem tc43_no_orbit_correspondence (x : Q₂) (hx : x ≠ 0)
    {v₀ : Fin 2 → ℝ} (hbal : imb v₀ = 0) :
    (∀ n, 0 < ‖(2 : Q₂) ^ n * x‖) ∧
    (∀ k, imb ((step (1/4))^[k] v₀) = 0) := by
  refine ⟨padic_orbit_pos hx, ?_⟩
  intro k
  rw [markov_imbalance_quarter, hbal, mul_zero]

/-- The uniform vector `unif = ![1/2,1/2]` is balanced (`imb unif = 0`), so it instantiates the NO-GO
    residue: the Markov #2 orbit from the stationary vector sits at the floor while the p-adic #3 orbit
    (from `x ≠ 0`) stays strictly positive, both under the same `(1/2)ⁿ` envelope. -/
theorem unif_balanced : imb unif = 0 := by
  simp only [imb, unif, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end ZeroParadox.ZPH_MC1_TC45

/-! ## Axiom Purity Check

`Classical.choice` enters through the Mathlib analysis/topology library inherited from TC36 (`Q₂`
norm, `tendsto_pow…`) and TC39 (`Tendsto`) — a library dependency, not a new commitment of this
construction. The matched-rate identities themselves are algebraic specializations. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC45

#print axioms env_tendsto
#print axioms padic_env_eq
#print axioms markov_imbalance_quarter
#print axioms padic_orbit_half
#print axioms tc43_shared_rate_half
#print axioms tc43_no_orbit_correspondence
#print axioms unif_balanced

end PurityCheck
