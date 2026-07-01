-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC34 — within-Axis-I positive rate-transport via the shared geometric rate `2^(-n)`

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file tests **TC34**: although the proof-theory floor (#1, `0 : ℕ`, a μ / well-founded-descent
bottom) and the p-adic floor (#3, `{0} = ⋂ q2Ball n ⊆ Q₂`, a ν / inverse-limit bottom) sit on
**opposite roots** of the bottom-diagram tree (the cross-root wall TC04/E4 stands — this file does not
touch it), they nevertheless share a **common quantitative invariant**: the same geometric rate
`n ↦ 2^(-n)` (ratio `c = 1/2 < 1`) bounds the distance-to-floor of a canonical orbit on each side.

This refines TC33: where #3↔#2 (p-adic vs Markov absorbing) was a rate-level **mismatch**
(the absorbing state's distance is *constant* `1` away from the geometric envelope), #3↔#1 is a
rate-level **match** — both descend to their floor at rate `1/2`.

**What is proved (load-bearing, in the theorem statements):**

- **ν-attractor leg (p-adic, #3).** `padic_orbit_norm`: for every `x : Q₂` and `n`, the
  doubling-orbit distance to the floor is *exactly* the geometric sequence
  `‖(2:Q₂)^n * x‖ = (2:ℝ)^(-n) * ‖x‖`. `padic_orbit_tendsto`: this distance tends to `0`.
- **μ-descent leg (ℕ floor, #1).** `nat_descent_bound`: any well-founded ℕ-orbit with
  `a (n+1) ≤ a n / 2` (Nat floor-halving) is bounded by the **same** envelope,
  `(a n : ℝ) ≤ (a 0 : ℝ) * (2:ℝ)^(-n)`. `nat_descent_tendsto`: its distance tends to `0`.
- **Shared-rate capstone.** `tc34_shared_rate`: *both* distance sequences are dominated by the single
  envelope `C · (2:ℝ)^(-n)` (with `C = ‖x‖` on the p-adic side, `C = a 0` on the ℕ side), and that
  envelope `→ 0`. The common rate `n ↦ 2^(-n)` is exhibited in-statement as a quantitative invariant
  shared across the μ/ν root.

**Honest scope — what this is NOT.**
- This is **not** a structure-preserving map between the two orbits, and it does **not** dissolve the
  cross-root wall. The orbits live in different categories (a totally-disconnected normed field vs the
  discrete order ℕ); only the *real-valued rate function* is shared.
- The shared rate is a **bound/envelope match**, not an orbit isomorphism. On the p-adic side the bound
  is an exact equality; on the ℕ side it is an inequality (Nat floor-halving can drop faster, and — see
  below — the ℕ orbit reaches `0` in *finite* time, after which its distance is identically `0`).
- **The pre-registered NO-GO is partially real and is recorded honestly.** A well-founded ℕ-descent
  *terminates*: once `a k = 0` the orbit is stuck at `0`, so the ℕ distance is eventually exactly `0`,
  whereas the p-adic orbit (for `x ≠ 0`) is strictly positive at every finite step
  (`padic_orbit_pos`). So the two orbits are **not** in geometric-rate *correspondence* (no step-for-
  step matching of strictly-positive distances). What survives — and all this file claims — is the
  weaker, true statement: a **common upper envelope** at rate `1/2` dominates both. The "shared rate"
  is a shared *bound*, not a shared *orbit profile*. We do not overclaim a positive bridge.
-/

namespace ZeroParadox.ZPH_MC1_TC36

open ZeroParadox.ZPB
open Filter Topology

/-- The shared geometric envelope rate: `n ↦ (2:ℝ)^(-n)`, ratio `1/2 < 1`. Tends to `0`. -/
theorem rate_tendsto : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine h.congr (fun n => ?_)
  rw [zpow_neg, zpow_natCast, one_div, ← inv_pow]

/-- `(2:ℝ)^(-(n+1)) = (2:ℝ)^(-n) / 2`: the per-step contraction of the envelope. -/
theorem rate_step (n : ℕ) : (2 : ℝ) ^ (-((n : ℤ) + 1)) = (2 : ℝ) ^ (-(n : ℤ)) / 2 := by
  rw [neg_add, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), div_eq_mul_inv]
  norm_num

/-! ### ν-attractor leg: the p-adic doubling orbit (#3) -/

/-- **p-adic ν leg, exact rate.** The doubling-orbit distance to the floor is exactly the geometric
    sequence: `‖(2:Q₂)^n * x‖ = (2:ℝ)^(-n) * ‖x‖`. The p-adic absolute value of `2^n` is `2^(-n)`
    (`padicNormE.norm_p_pow`), and the norm is multiplicative. -/
theorem padic_orbit_norm (x : Q₂) (n : ℕ) :
    ‖(2 : Q₂) ^ n * x‖ = (2 : ℝ) ^ (-(n : ℤ)) * ‖x‖ := by
  have h2 : ((2 : ℕ) : Q₂) = (2 : Q₂) := by norm_num
  rw [norm_mul]
  congr 1
  rw [show ((2 : Q₂) ^ n) = (((2 : ℕ) : Q₂)) ^ n by rw [h2]]
  rw [Padic.norm_p_pow]
  norm_num

/-- The p-adic orbit distance tends to `0` (the floor is the ν-attractor of doubling). -/
theorem padic_orbit_tendsto (x : Q₂) :
    Tendsto (fun n : ℕ => ‖(2 : Q₂) ^ n * x‖) atTop (𝓝 0) := by
  have hC : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ)) * ‖x‖) atTop (𝓝 (0 * ‖x‖)) :=
    rate_tendsto.mul_const ‖x‖
  rw [zero_mul] at hC
  exact hC.congr (fun n => (padic_orbit_norm x n).symm)

/-- For `x ≠ 0` the p-adic orbit is strictly positive at every finite step — the floor is approached
    but never reached in finite time (the NO-GO side: there is no finite-time collapse to match the
    terminating ℕ-descent). -/
theorem padic_orbit_pos {x : Q₂} (hx : x ≠ 0) (n : ℕ) : 0 < ‖(2 : Q₂) ^ n * x‖ := by
  rw [padic_orbit_norm x n]
  apply mul_pos
  · positivity
  · exact norm_pos_iff.mpr hx

/-! ### μ-descent leg: a well-founded ℕ-orbit (#1) -/

/-- **ℕ μ leg, same envelope.** Any well-founded ℕ-orbit that floor-halves each step
    (`a (n+1) ≤ a n / 2`, Nat division) is bounded by the SAME geometric envelope:
    `(a n : ℝ) ≤ (a 0 : ℝ) * (2:ℝ)^(-n)`. Proof: induction; the cast of Nat floor-halving is
    `≤` the real halving (`Nat.cast_div_le`). -/
theorem nat_descent_bound (a : ℕ → ℕ) (hdesc : ∀ n, a (n + 1) ≤ a n / 2) (n : ℕ) :
    (a n : ℝ) ≤ (a 0 : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hcast : (a (k + 1) : ℝ) ≤ (a k : ℝ) / 2 := by
      calc (a (k + 1) : ℝ) ≤ ((a k / 2 : ℕ) : ℝ) := by exact_mod_cast hdesc k
        _ ≤ (a k : ℝ) / 2 := Nat.cast_div_le
    calc (a (k + 1) : ℝ) ≤ (a k : ℝ) / 2 := hcast
      _ ≤ ((a 0 : ℝ) * (2 : ℝ) ^ (-(k : ℤ))) / 2 := by gcongr
      _ = (a 0 : ℝ) * (2 : ℝ) ^ (-((k : ℤ) + 1)) := by
          rw [rate_step]; ring

/-- The ℕ-descent distance tends to `0` (the well-founded orbit reaches its floor). -/
theorem nat_descent_tendsto (a : ℕ → ℕ) (hdesc : ∀ n, a (n + 1) ≤ a n / 2) :
    Tendsto (fun n : ℕ => (a n : ℝ)) atTop (𝓝 0) := by
  have henv : Tendsto (fun n : ℕ => (a 0 : ℝ) * (2 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := rate_tendsto.const_mul (a 0 : ℝ)
    simpa using this
  refine squeeze_zero (fun n => by positivity) (fun n => nat_descent_bound a hdesc n) henv

/-! ### Shared-rate capstone -/

/-- **TC34 capstone (witness, not narration).** The single geometric envelope `C · (2:ℝ)^(-n)`
    dominates the distance-to-floor of BOTH a μ-descent orbit (#1, `C = a 0`) and the
    ν-attractor orbit (#3, `C = ‖x‖`), and that envelope tends to `0`. The shared rate
    `n ↦ 2^(-n)` is the common quantitative invariant across the μ/ν root — exhibited in-statement
    as a simultaneous bound, NOT as a structure-preserving map between the orbits. -/
theorem tc34_shared_rate
    (x : Q₂) (a : ℕ → ℕ) (hdesc : ∀ n, a (n + 1) ≤ a n / 2) :
    -- the shared rate envelope tends to 0
    Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) ∧
    -- ν leg: the p-adic distance equals the envelope scaled by ‖x‖ (exact), hence ≤ it
    (∀ n : ℕ, ‖(2 : Q₂) ^ n * x‖ = ‖x‖ * (2 : ℝ) ^ (-(n : ℤ))) ∧
    -- μ leg: the ℕ distance is ≤ the envelope scaled by a 0
    (∀ n : ℕ, (a n : ℝ) ≤ (a 0 : ℝ) * (2 : ℝ) ^ (-(n : ℤ))) :=
  ⟨rate_tendsto,
   fun n => by rw [padic_orbit_norm x n]; ring,
   nat_descent_bound a hdesc⟩

/-- **The honest NO-GO residue (recorded in-statement).** The "shared rate" is a shared *envelope*,
    not a shared *orbit profile*: for `x ≠ 0` the p-adic orbit is strictly positive at every step,
    while a terminating ℕ-descent (any orbit that ever hits `0`, e.g. via `a (n+1) ≤ a n / 2`) is
    eventually identically `0`. So no step-for-step geometric-rate *correspondence* exists between the
    two orbits — only the common upper bound does. This is the TC33 obstruction, localized: rate-MATCH
    at the envelope level, rate-MISMATCH at the orbit level. -/
theorem tc34_no_orbit_correspondence (x : Q₂) (hx : x ≠ 0) :
    (∀ n, 0 < ‖(2 : Q₂) ^ n * x‖) ∧
    (∀ a : ℕ → ℕ, (∀ n, a (n + 1) ≤ a n / 2) → ∀ k, a k = 0 → ∀ m, a (k + m) = 0) := by
  refine ⟨padic_orbit_pos hx, ?_⟩
  intro a hdesc k hk m
  induction m with
  | zero => simpa using hk
  | succ j ih =>
    have : a (k + j + 1) ≤ a (k + j) / 2 := hdesc (k + j)
    rw [ih] at this
    simp at this
    omega

end ZeroParadox.ZPH_MC1_TC36

/-! ## Axiom Purity Check

`Classical.choice` enters through Mathlib's analysis/topology library (`Padic`/`Q₂` norm,
`tendsto_pow_atTop_nhds_zero_of_lt_one`, `squeeze_zero`) — the same dependency the ZP-B layer carries.
It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC36

#print axioms rate_tendsto
#print axioms padic_orbit_norm
#print axioms padic_orbit_tendsto
#print axioms padic_orbit_pos
#print axioms nat_descent_bound
#print axioms nat_descent_tendsto
#print axioms tc34_shared_rate
#print axioms tc34_no_orbit_correspondence

end PurityCheck
