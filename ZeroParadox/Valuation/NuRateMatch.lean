-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Order.MarkovContractionDual
import ZeroParadox.Valuation.RateTransport
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Within-ν geometric-rate match: #2 (irreducible Markov) and #3 (p-adic) share rate 1/2

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---
## Formal Overview (AI-assisted)
At `a = 1/4` the kernel of `ZeroParadox/Order/MarkovContractionDual.lean` scales the imbalance by
`1 - 2a = 1/2` (`step_imb`), the p-adic doubling rate. The match is `padic_markov_shared_rate_envelope`;
the `example` after `padic_markov_no_orbit_correspondence` states that match step by step, for every
start. Both sides are real numbers: no category, inverse limit or map between `Fin 2 → ℝ` and `Q₂` is
built. -/

namespace ZeroParadox

open ZeroParadox
open ZeroParadox
open ZeroParadox
open Filter Topology

/-! ### The shared envelope `n ↦ (1/2)ⁿ` -/

/-- The shared geometric envelope `n ↦ (1/2)ⁿ` tends to `0`. -/
theorem env_tendsto : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- `(2:ℝ)^(-n) = (1/2)ⁿ`: the p-adic envelope is the shared envelope. -/
theorem padic_env_eq (n : ℕ) : (2 : ℝ) ^ (-(n : ℤ)) = ((1 : ℝ) / 2) ^ n := by
  rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]

/-! ### GO half: the matched-rate identities -/

/-- **Markov side, matched rate.** With `a = 1/4` (so `1 - 2a = 1/2`), the irreducible
    Markov orbit's imbalance is exactly `(1/2)ᵏ · imb v₀`. Specialization of `markov_imbalance_pow`. -/
theorem markov_imbalance_quarter (v₀ : Fin 2 → ℝ) (k : ℕ) :
    imb ((markovStep (1/4))^[k] v₀) = ((1 : ℝ) / 2) ^ k * imb v₀ := by
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
    `ZeroParadox/Valuation/NuRateEdge.lean`'s geometric-vs-absorbing mismatch. -/
theorem padic_markov_shared_rate_envelope (x : Q₂) (v₀ : Fin 2 → ℝ) :
    -- the shared envelope tends to 0
    Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) ∧
    -- #2 (Markov, a = 1/4): imbalance distance is exactly the envelope · (imb v₀)
    (∀ k : ℕ, imb ((markovStep (1/4))^[k] v₀) = ((1 : ℝ) / 2) ^ k * imb v₀) ∧
    -- #3 (p-adic doubling): orbit distance is exactly the envelope · ‖x‖
    (∀ n : ℕ, ‖(2 : Q₂) ^ n * x‖ = ((1 : ℝ) / 2) ^ n * ‖x‖) :=
  ⟨env_tendsto, markov_imbalance_quarter v₀, padic_orbit_half x⟩

/-! ### The balanced start -/

/-- At a balanced start (`hbal`) and `x ≠ 0`: the p-adic orbit distance stays positive while the
    `markovStep (1/4)` imbalance is `0` at every step. The start, not the rate, sets the Markov
    constant to `0`; the `example` below holds for every start, so the name's "no correspondence"
    is this balanced start only. -/
theorem padic_markov_no_orbit_correspondence (x : Q₂) (hx : x ≠ 0)
    {v₀ : Fin 2 → ℝ} (hbal : imb v₀ = 0) :
    (∀ n, 0 < ‖(2 : Q₂) ^ n * x‖) ∧
    (∀ k, imb ((markovStep (1/4))^[k] v₀) = 0) := by
  refine ⟨padic_orbit_pos hx, ?_⟩
  intro k
  rw [markov_imbalance_quarter, hbal, mul_zero]

-- Statement: for every `x` and every start `v₀`, at every step `n`,
-- `‖2ⁿ·x‖ · imb v₀ = imb (P^ⁿ v₀) · ‖x‖`, the p-adic norm and the signed imbalance cross-multiplied.
example (x : Q₂) (v₀ : Fin 2 → ℝ) (n : ℕ) :
    ‖(2 : Q₂) ^ n * x‖ * imb v₀ = imb ((markovStep (1/4))^[n] v₀) * ‖x‖ := by
  rw [padic_orbit_half, markov_imbalance_quarter]; ring

/-- The uniform vector `unif = ![1/2,1/2]` is balanced (`imb unif = 0`), so it meets the hypothesis
    `hbal` of `padic_markov_no_orbit_correspondence`. -/
theorem unif_balanced : imb unif = 0 := by
  simp only [imb, unif, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` enters through the Mathlib analysis/topology library inherited from `ZeroParadox/Valuation/RateTransport.lean` (`Q₂`
norm, `tendsto_pow…`) and `ZeroParadox/Order/MarkovContractionDual.lean` (`Tendsto`) — a library dependency, not a new commitment of this
construction. The matched-rate identities themselves are algebraic specializations. -/

section PurityCheck
open ZeroParadox

#print axioms env_tendsto
#print axioms padic_env_eq
#print axioms markov_imbalance_quarter
#print axioms padic_orbit_half
#print axioms padic_markov_shared_rate_envelope
#print axioms padic_markov_no_orbit_correspondence
#print axioms unif_balanced

end PurityCheck
