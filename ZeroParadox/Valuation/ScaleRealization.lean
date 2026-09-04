-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the realization map carrying an abstract scale step to 2-adic doubling, and the valuation law derived from it. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Valuation.InfinitudeFloor
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Valuation.Scale
import ZeroParadox.Valuation.ScaleBridge
import ZeroParadox.Valuation.RiemannSphere
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Realizing an abstract scale step as 2-adic doubling

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---
## Formal Overview (AI-assisted)

ZP-I asserts that lattice motion and 2-adic valuation are the same motion. Here that is an explicit
HYPOTHESIS (`Function.Semiconj`) rather than a class field, and every valuation fact is DERIVED from
it. Fences, and why the equality form is not statable, are in `ScaleRealization.md`.
-/

namespace ZeroParadox

open Filter Topology

/-! ## § I. The realization, as a hypothesis

`R-COMMIT`: the framework asserts an abstract step is realized by doubling, and reality might not
comply, so it is a commitment and belongs on the theorems that need it. `Function.Semiconj ρ f g` is
Mathlib's `∀ x, ρ (f x) = g (ρ x)`. -/

/-- **The orbit is computed by the realization.** Semiconjugacy alone forces the `n`-step image to be
    `2 ^ n` times the base point — so the realized orbit IS the doubling orbit. -/
theorem realized_orbit {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) (n : ℕ) :
    ρ (scale^[n] x) = 2 ^ n * ρ x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', hsemi, ih]
      ring

/-- Non-degeneracy propagates along the orbit. -/
theorem realized_orbit_ne_zero {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0) (n : ℕ) :
    ρ (scale^[n] x) ≠ 0 := by
  rw [realized_orbit ρ scale hsemi x n]
  exact mul_ne_zero (pow_ne_zero n (by norm_num)) hx

/-! ## § II. The valuation law is DERIVED, never asserted -/

/-- **One step raises the valuation by exactly one.** The increment law on the metric side is a
    CONSEQUENCE of equivariance, not a second axiom. -/
theorem realized_valuation_step {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0) :
    (ρ (scale x)).valuation = (ρ x).valuation + 1 := by
  have hv2 : (2 : Q₂).valuation = 1 := by simp
  have h : ρ (scale x) = 2 * ρ x := hsemi x
  rw [h, Padic.valuation_mul (by norm_num : (2 : Q₂) ≠ 0) hx, hv2]
  ring

/-- **The `n`-step form.** The valuation shifts by `n` from wherever the base point sat — the offset
    `(ρ x).valuation` is never pinned, which is the whole point. -/
theorem realized_valuation_orbit {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0) (n : ℕ) :
    (ρ (scale^[n] x)).valuation = (ρ x).valuation + n := by
  have hv2 : (2 : Q₂).valuation = 1 := by simp
  rw [realized_orbit ρ scale hsemi x n,
    Padic.valuation_mul (pow_ne_zero n (by norm_num : (2 : Q₂) ≠ 0)) hx,
    Padic.valuation_pow, hv2]
  ring

/-! ## § III. ZP-I's conclusion, reached without a depth chain -/

/-- **Strict ascent, with no `IsDepthChain` anywhere.** This is exactly `h_strict`, the hypothesis
    ZP-I's geometric bound consumes, obtained from equivariance instead of from an asserted equality
    between a lattice index and a valuation. -/
theorem realized_strict {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0) (n : ℕ) :
    (ρ (scale^[n] x)).valuation < (ρ (scale^[n + 1] x)).valuation := by
  rw [realized_valuation_orbit ρ scale hsemi x hx n,
    realized_valuation_orbit ρ scale hsemi x hx (n + 1)]
  push_cast
  linarith

/-- **The realized orbit converges to the floor.** ⚠ The limit is not the new part —
    `PadicAttractor.doubling_orbit_tendsto_zero` gives it for every orbit. What is new is that the
    hypothesis reaching it is equivariance, not a depth chain. -/
theorem realized_tendsto_zero {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) :
    Tendsto (fun n => ρ (scale^[n] x)) atTop (nhds 0) := by
  have h : (fun n => ρ (scale^[n] x)) = fun n : ℕ => (2 : Q₂) ^ n * ρ x :=
    funext (realized_orbit ρ scale hsemi x)
  rw [h]
  exact doubling_orbit_tendsto_zero (ρ x)

/-! ## § IV. FALSIFIERS — the conditions under which this says nothing

`R-CONTROLS`: objects satisfying the same inputs for which the conclusion is FALSE. -/

/-- `Statement:` the constant map to `0` is semiconjugate to doubling, and its image never moves.
    `Reading:` **INVARIANT** — equivariance ALONE is empty. The load is carried by `ρ x ≠ 0`, and
    this is the carrier where dropping that hypothesis makes every ascent conclusion false. -/
theorem trivial_realization_is_semiconj_and_static {L : Type*} (scale : L → L) :
    Function.Semiconj (fun _ : L => (0 : Q₂)) scale (fun q => 2 * q) ∧
    ∀ (x : L) (n : ℕ), (fun _ : L => (0 : Q₂)) (scale^[n] x) = 0 :=
  ⟨fun _ => by simp, fun _ _ => rfl⟩

/-- Dropping `ρ x ≠ 0` does not merely leave `realized_strict` unproved — it makes it FALSE. -/
example : ¬ (∀ (L : Type) (ρ : L → Q₂) (scale : L → L),
    Function.Semiconj ρ scale (fun q => 2 * q) → ∀ (x : L) (n : ℕ),
      (ρ (scale^[n] x)).valuation < (ρ (scale^[n + 1] x)).valuation) := by
  intro h
  have hc : Function.Semiconj (fun _ : ℕ => (0 : Q₂)) id (fun q => 2 * q) := fun n => by simp
  have := h ℕ (fun _ => (0 : Q₂)) id hc 0 0
  simp at this

/-- And dropping equivariance makes it false too: the constant map to `1` is nowhere zero, is NOT
    semiconjugate to doubling, and has a flat valuation. So neither hypothesis is decorative. -/
example : ¬ Function.Semiconj (fun _ : ℕ => (1 : Q₂)) id (fun q => 2 * q) := by
  intro h
  have h0 : (1 : Q₂) = 2 * 1 := h 0
  norm_num at h0

example : ¬ (∀ (L : Type) (ρ : L → Q₂) (scale : L → L),
    (∀ x : L, ρ x ≠ 0) → ∀ (x : L) (n : ℕ),
      (ρ (scale^[n] x)).valuation < (ρ (scale^[n + 1] x)).valuation) := by
  intro h
  have := h ℕ (fun _ => (1 : Q₂)) id (fun _ => one_ne_zero) 0 0
  exact lt_irrefl _ this

/-! ## § V. NON-VACUITY — the hypotheses are jointly satisfiable

Without this the file says nothing: every theorem above would hold empty. The witness is the powers
of two on `ℕ` with the successor as the abstract step, which is `ScaleDepthWitness.scaleChain`. -/

/-- `Statement:` the successor on `ℕ` is realized by doubling, via `n ↦ 2 ^ n`, and the base point is
    nonzero — so every hypothesis above is jointly satisfiable.
    `Reading:` **INVARIANT** — non-vacuity, nothing more. It exhibits one realization; it says
    nothing about how many there are. -/
theorem succ_realized_by_doubling :
    Function.Semiconj (fun n : ℕ => (2 : Q₂) ^ n) (· + 1) (fun q => 2 * q) ∧
    (fun n : ℕ => (2 : Q₂) ^ n) 0 ≠ 0 :=
  ⟨fun n => by show (2 : Q₂) ^ (n + 1) = 2 * 2 ^ n; ring, by norm_num⟩

/-- `Statement:` `WithTop ℤ` has an element strictly below `0`.
    `Reading:` **CARRIER** — so it is not order-isomorphic to `ℕ∞`; see `ScaleRealization.md`. -/
theorem withTopInt_has_negative : ∃ z : WithTop ℤ, z < 0 :=
  ⟨((-1 : ℤ) : WithTop ℤ), by exact_mod_cast (by norm_num : (-1 : ℤ) < 0)⟩

/-! ## § VI. BOTH BANKS — two valuations, independently supplied, advancing together

The residue `ScaleDepthWitness.depthchain_iff_nonneg` exposed is that a depth index can be read back
off the chain. `ValBridge.val` cannot: it is a CLASS FIELD, fixed when the instance is built, before
anyone chooses a realization. So the two sides below are genuinely separate structures, and the
theorem is that the realization makes them advance in lockstep. -/

/-- **The bridge, with a bank on each side.** The abstract valuation climbs by `n` from its own
    origin (`ScaleBridge.orbit_ne_bot_and_val_free`, no realization anywhere in it), and the metric
    valuation climbs by `n` from ITS own origin (equivariance). Two independent citations; neither
    conjunct is derived from the other. The origins differ and are never identified — they do not
    even share a value monoid (`withTopInt_has_negative`). -/
theorem realization_bridges_both_valuations {L : Type*} [ValBridge L] (ρ : L → Q₂)
    (hsemi : Function.Semiconj ρ ValBridge.scale (fun q => 2 * q))
    (x : L) (hxb : x ≠ ValBridge.bot) (hx : ρ x ≠ 0) (n : ℕ) :
    ValBridge.val (ValBridge.scale^[n] x) = ValBridge.val x + n ∧
    (ρ (ValBridge.scale^[n] x)).valuation = (ρ x).valuation + n :=
  ⟨(orbit_ne_bot_and_val_free x hxb n).2,
   realized_valuation_orbit ρ ValBridge.scale hsemi x hx n⟩

/-- `Statement:` the abstract bank holds while the metric bank fails, for the constant realization
    at `1`.
    `Reading:` **INVARIANT** — this is what "independently supplied" MEANS. One side needs no `ρ` at
    all, so it cannot have been read off the chain, and the coupling is what the realization buys. -/
theorem banks_are_independent {L : Type*} [ValBridge L] (x : L) (hxb : x ≠ ValBridge.bot) :
    ValBridge.val (ValBridge.scale^[1] x) = ValBridge.val x + 1 ∧
    ¬ ((fun _ : L => (1 : Q₂)) (ValBridge.scale^[1] x)).valuation
        = ((fun _ : L => (1 : Q₂)) x).valuation + 1 := by
  refine ⟨by simpa using (orbit_ne_bot_and_val_free x hxb 1).2, ?_⟩
  simp

/-! ## § VII. The abstract MONOID orbit embeds in the sphere's ℤ-action

`ValBridge.scale` iterates forward only; `RiemannSphere.rScale` is defined for every `n : ℤ` and
composes additively, so it is a GROUP. The realization carries the first into the second.

⭐ The backward direction is not unsupplied but REFUSED: `ScaleBridge.scale_not_surjective` proves
the valuation-`0` layer has no scale-predecessor, so the abstract family cannot be a group. That is
the one-wayness as an algebraic fact. Which arrow, and why it is the INBOUND one, is in
`ScaleRealization.md`. -/

/-- **The embedding.** The realized `n`-step orbit is the sphere's `rScale n` orbit of the base
    point, so the abstract step and the sphere's ℤ-action agree wherever both are defined. -/
theorem realized_orbit_is_rScale_orbit {L : Type*} (ρ : L → Q₂) (scale : L → L)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) (x : L) (n : ℕ) :
    rScale (n : ℤ) (OnePoint.some (ρ x)) = OnePoint.some (ρ (scale^[n] x)) := by
  rw [realized_orbit ρ scale hsemi x n]
  simp [rScale, zpow_natCast]

/-! ## § VIII. NON-VACUITY for §§ VI–VII

§ V witnesses §§ I–V, where `scale` is a bare parameter. §§ VI–VII additionally need a `ValBridge`
AND a realization of it, so they need their own witness or they hold empty. -/

/-- `Statement:` the coercion `ℤ_[2] → ℚ_[2]` realizes `instZ2ValBridge`'s scale as doubling, at a
    point that is neither the bottom nor sent to `0`.
    `Reading:` **INVARIANT** — non-vacuity for §§ VI–VII, on the corpus's own 2-adic carrier. -/
theorem z2_realizes_into_q2 :
    Function.Semiconj (fun z : ℤ_[2] => (z : Q₂)) ValBridge.scale (fun q => 2 * q) ∧
    (1 : ℤ_[2]) ≠ ValBridge.bot ∧ ((1 : ℤ_[2]) : Q₂) ≠ 0 := by
  have h2c : ((2 : ℤ_[2]) : Q₂) = 2 := by norm_cast
  refine ⟨fun z => ?_, ?_, ?_⟩
  · show ((2 * z : ℤ_[2]) : Q₂) = 2 * (z : Q₂)
    rw [PadicInt.coe_mul, h2c]
  · show (1 : ℤ_[2]) ≠ (0 : ℤ_[2])
    exact one_ne_zero
  · push_cast
    exact one_ne_zero

/-- The bridge fires on it — both banks, on `ℤ_[2]`. -/
example (n : ℕ) :
    ValBridge.val (ValBridge.scale^[n] (1 : ℤ_[2])) = ValBridge.val (1 : ℤ_[2]) + n ∧
    (((ValBridge.scale^[n] (1 : ℤ_[2])) : ℤ_[2]) : Q₂).valuation
      = (((1 : ℤ_[2]) : Q₂)).valuation + n :=
  realization_bridges_both_valuations (fun z : ℤ_[2] => (z : Q₂))
    z2_realizes_into_q2.1 1 z2_realizes_into_q2.2.1 z2_realizes_into_q2.2.2 n

/-- And the one-wayness is non-vacuous there: `1` has valuation `0`, so `scale` misses it. -/
example : ¬ Function.Surjective (ValBridge.scale (L := ℤ_[2])) :=
  scale_not_surjective (1 : ℤ_[2]) (by show q2Val (1 : ℤ_[2]) = 0; simp [q2Val])

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms realized_orbit
#print axioms realized_orbit_ne_zero
#print axioms realized_valuation_step
#print axioms realized_valuation_orbit
#print axioms realized_strict
#print axioms realized_tendsto_zero
#print axioms trivial_realization_is_semiconj_and_static
#print axioms withTopInt_has_negative
#print axioms succ_realized_by_doubling
#print axioms realization_bridges_both_valuations
#print axioms banks_are_independent
#print axioms realized_orbit_is_rScale_orbit
#print axioms z2_realizes_into_q2
end PurityCheck
