import ZeroParadox.ZPH_ArchPlace
import ZeroParadox.ZPH_PlaceForcing
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Direction A, Cycle A5 (depth c) — the framework's OWN bottom family = all places of ℚ

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

A1–A4 worked with #2 (archimedean) and #3 (the p = 2 floor) — two of ℚ's places. The honest fence on
A2/A4 was "the product formula runs over ALL places; the framework only lights up 2 of them." A5 removes
that fence by generalizing the framework's finite-floor construction from p = 2 to **every prime p**: a
p-adic floor for each place, so the framework's number-theoretic bottom family is the *complete* set of
places (the archimedean #2 + a p-adic floor per prime), and the product formula (A2) is then a statement
over the framework's **own** bottoms, not over ℚ's places with two lit up.

**Genuinely new content.**
- `qp_floor_is_limit` — **the per-prime floor OBJECT**: for every prime p, `⋂ n, qpBall p n = {0}`.
  Generalizes `ZPH_TopFunctor.fB_bottom_is_limit` (built only at p = 2) to a constructed floor object at
  *every* finite place. This is what genuinely earns "the framework's finite-floor family for all primes"
  — the floor objects are built, not asserted. (New; the core A5 result.)
- `padic_contraction_all_primes` — for **every** prime p, multiplication by p contracts to the floor ⊥ at
  the p-adic place: `pⁿx → 0` in `ℚ_[p]` (because `‖p‖_p < 1`). Generalizes TC05's p = 2 doubling
  attractor — the *dynamics* reaching each per-prime floor. (New.)
- `padic_place_eq_norm_all_primes` — the p-adic place is the `ℚ_[p]`-norm, for every prime p (generalizes
  A1's `node3_place_eq_q2_norm`).

**Assembly (Ostrowski + A2, honestly).**
- `every_finite_place_is_padic` — every nontrivial *bounded* (= non-archimedean) place of ℚ is a `padic p`
  (Ostrowski). So the framework's finite-floor family (one per prime) is *exhaustive* of the finite places.
- `framework_family_complete` — the capstone reading: every nontrivial place is the archimedean one (#2) or
  some p-adic one (a framework finite floor), and each finite one carries a contracting floor. The
  framework's number-theoretic bottoms ARE ℚ's places; the product formula (A2) is the constraint over
  this own family.

**Honest scope.** Still within the number-theoretic bottoms. A5 genuinely *constructs* the finite-floor
object at every prime (`qp_floor_is_limit`, generalizing the p = 2 `fB_bottom_is_limit`) plus the
all-primes contraction dynamics — so "the framework's finite-place family for all primes" is now built,
not asserted. The exhaustiveness (`every_finite_place_is_padic`) and the product formula (A2) are
Ostrowski/Mathlib re-exports; `framework_family_complete` is the ∃-weakening of A1's `place_dichotomy`
(strictly weaker — kept only as the bundled "real or p-adic" reading). Does NOT touch the
categorical/order bottoms (#1/#4/#5, walled). The product formula itself remains Mathlib's.
-/

namespace ZeroParadox.ZPH_PlaceAllPrimes

open Rat.AbsoluteValue Filter Topology

/-- For **every** prime `p`, multiplication by `p` contracts to the floor ⊥ at the p-adic place:
    `pⁿx → 0` in `ℚ_[p]` (since `‖p‖_p < 1`). Generalizes TC05's p = 2 attractor to all finite places. -/
theorem padic_contraction_all_primes (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) :
    Tendsto (fun n : ℕ => (p : ℚ_[p]) ^ n * x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : ∀ n : ℕ, ‖(p : ℚ_[p]) ^ n * x‖ = ‖(p : ℚ_[p])‖ ^ n * ‖x‖ := by
    intro n; rw [norm_mul, norm_pow]
  simp only [hnorm]
  have h0 : Tendsto (fun n : ℕ => ‖(p : ℚ_[p])‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) Padic.norm_p_lt_one
  simpa using h0.mul_const ‖x‖

/-- The p-adic place is the `ℚ_[p]`-norm, for every prime `p` (generalizes A1's `node3_place_eq_q2_norm`). -/
theorem padic_place_eq_norm_all_primes (p : ℕ) [Fact p.Prime] (q : ℚ) :
    padic p q = ‖(q : ℚ_[p])‖ := by
  rw [padic_eq_padicNorm, Padic.eq_padicNorm]

/-- The p-adic floor ball at depth `n`: `B(0, p⁻ⁿ) ⊆ ℚ_[p]`. Generalizes ZP-B's `q2Ball` to every prime. -/
noncomputable def qpBall (p : ℕ) [Fact p.Prime] (n : ℕ) : Set ℚ_[p] :=
  Metric.closedBall 0 ((p : ℝ) ^ (-(n : ℤ)))

/-- **The per-prime floor OBJECT** (the genuine all-primes generalization, not just dynamics): for every
    prime `p`, the intersection of the shrinking p-adic balls is exactly the floor `{0}`. Generalizes
    `ZPH_TopFunctor.fB_bottom_is_limit` (built only at p = 2) to a floor object at *every* finite place —
    so the framework's finite-floor family is genuinely constructed for all primes, not asserted. -/
theorem qp_floor_is_limit (p : ℕ) [hp : Fact p.Prime] :
    (⋂ n, qpBall p n) = {(0 : ℚ_[p])} := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  simp only [qpBall]
  ext x
  simp only [Set.mem_iInter, Metric.mem_closedBall, Set.mem_singleton_iff]
  constructor
  · intro h
    have htend : Filter.Tendsto (fun n : ℕ => (p : ℝ) ^ (-(n : ℤ))) Filter.atTop (nhds 0) := by
      simp only [zpow_neg, zpow_natCast]
      exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hp1)
    have hle : dist x 0 ≤ 0 := ge_of_tendsto' htend (fun n => h n)
    exact dist_eq_zero.mp (le_antisymm hle dist_nonneg)
  · rintro rfl n
    simp

/-- Every nontrivial **bounded** (non-archimedean) place of ℚ is a `padic p` (Ostrowski). The framework's
    finite-floor family (one per prime) is exhaustive of the finite places. -/
theorem every_finite_place_is_padic (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial)
    (hb : ∀ n : ℕ, f n ≤ 1) : ∃ p, ∃ (_ : Fact p.Prime), f ≈ padic p :=
  (equiv_padic_of_bounded hf hb).exists

/-- **A5 capstone.** Every nontrivial place of ℚ is the archimedean one (#2) or some p-adic one (a
    framework finite floor) — so the framework's number-theoretic bottom family IS ℚ's complete set of
    places. With the per-prime contracting floors (`padic_contraction_all_primes`) and the product formula
    (A2), the framework's own bottoms carry the global constraint, not "ℚ's places with two lit up". -/
theorem framework_family_complete (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ real ∨ ∃ p, ∃ (_ : Fact p.Prime), f ≈ padic p :=
  (ZeroParadox.ZPH_ArchPlace.place_dichotomy f hf).imp id (fun h => h.exists)

end ZeroParadox.ZPH_PlaceAllPrimes

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_PlaceAllPrimes

#print axioms padic_contraction_all_primes
#print axioms padic_place_eq_norm_all_primes
#print axioms qp_floor_is_limit
#print axioms every_finite_place_is_padic
#print axioms framework_family_complete

end PurityCheck
