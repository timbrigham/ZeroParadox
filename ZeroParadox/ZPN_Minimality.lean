/-!
# ZP-N minimality (Path B) — ε₀ as the LEAST fixed point of ω^·, choice-free (STUB)

PRIVATE / quarantined (private/physics-bridge) for now — exploratory Path B of the
"realization is the choice" experiment. The DELIVERABLE is the `#print axioms` footprint of
`epsilonZero_least_fixed`: a choice-free footprint in a choice-free carrier breaks the thesis
(eliminable direction); choice traceable to the realization (not the carrier) is the first clean
positive. Either way decisive — so when filled this is a real named-killer experiment for
`/experiment-review`. Prior art + plan: `.claude-local/notes/prior_art_constructive_epsilon0_lfp_2026-06-27.md`.

## Why this carrier (Brouwer trees), not Mathlib `Ordinal` and not Pataraia
- Mathlib `Ordinal` is choice-saturated (`epsilon_zero_eq_nfp` carries `Classical.choice`) — confounded.
- Pataraia/predicative-Tarski need *small* dcpos; the ordinal carrier is large (arXiv:2401.00841,
  TypeTopology Pataraia–Taylor). Wrong axis (predicativity, not choice). Dropped.
- **Brouwer trees** `zero | succ | lim (ℕ → ·)`: a concrete inductive whose constructors are exactly
  what ε₀ needs (ε₀ = `lim tower`, a countable limit), and on which **case analysis is ordinary
  constructive pattern matching** — dodging the LEM taboo that the *general* zero/succ/limit split incurs
  (de Jong–Kraus–Nordvall Forsberg–Xu, arXiv:2501.14542, Prop 9 / KNX23 Thm 63).

## The map (the familiar shape)
α ↦ ω^α is monotone and supremum-continuous (arXiv:2501.14542, Lemma 8 + the sup universal property,
choice-free; ω ≥ 1 so the base-ω map dodges the LEM obstruction on *general* exponentiation). Then
ε₀ = sup of the ω-chain ω, ω^ω, ω^(ω^ω), … = a **Kleene / domain-theoretic least fixed point**
(`lfp f = sup_n fⁿ(⊥)`) — the same choice-free `lfp` shape ZPP.lean uses via Mathlib `OrderHom.lfp`.

## Harvest map for Phase 2 (what to port from arXiv:2501.14542)
- **Lemma 8** — sup clause ⇒ ω^· monotone in the exponent.  → `omegaPow` monotone.
- **Supremum universal property (§2.4)** — sup is a genuine least upper bound.  → `epsilonZero_is_fixed`
  (ω^(lim tower) = lim tower by continuity) and the ≤-direction of leastness.
- **Lemma 4** — every ordinal = sup of successors of its predecessors (the CONSTRUCTIVE replacement for
  the zero/succ/limit case-split).  → `epsilonZero_least_fixed` WITHOUT LEM.
- **Prop 9** — general `exp` needs LEM; base-ω is fine (the fence to respect).

## OBSTRUCTION (found on reading the source — the main Phase-2 risk)
arXiv:2501.14542 is HoTT + univalence + set quotients; its `Ord` ≠ Mathlib `Ordinal`. The paper uses
univalence "crucially for proving equations of ordinals." Lean has no univalence, so the ported results
likely must be stated up to **≤-antisymmetry / propositional facts on this concrete inductive**, not
HoTT equalities. Hence `BLe` (a real constructive order on Brouwer trees, cf. Kraus et al
arXiv:2104.02549) is load-bearing and the fixed-point fact may need to be a `≤`-biconditional, not `=`.

STATUS: STUB (Path B, 2026-06-27). `omegaPow` and `BLe` are `sorry` placeholders; both theorems `sorry`.
Builds-clean rollback point per the stub-first protocol. NOT wired into Basic.lean.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox.ZPNMin

/-- **Brouwer trees** — the constructive ordinal carrier: `zero`, `succ`, and countable limits.
    Chosen because its case analysis is ordinary pattern matching (no LEM), and `lim` names ε₀. -/
inductive Brouwer : Type
  | zero : Brouwer
  | succ : Brouwer → Brouwer
  | lim  : (Nat → Brouwer) → Brouwer

namespace Brouwer

/-- The finite Brouwer trees `0, 1, 2, …` (= `succ^[n] zero`). -/
def ofNat : Nat → Brouwer
  | 0     => zero
  | n + 1 => succ (ofNat n)

/-- `ω` as a Brouwer tree: the limit of the finite trees. -/
def omegaB : Brouwer := lim ofNat

/-- **`ω^·` — PLACEHOLDER.** Phase 2: port the choice-free, monotone, sup-continuous base-ω
    exponentiation (arXiv:2501.14542, Lemma 8 + §2.4) to the Brouwer carrier:
    `ω^0 = 1`, `ω^(succ x) = ω^x · ω`, `ω^(lim f) = lim (n ↦ ω^(f n))`. -/
noncomputable def omegaPow : Brouwer → Brouwer := sorry

/-- The ω-tower: `tower 0 = ω`, `tower (n+1) = ω^(tower n)`. Its limit is ε₀.
    `noncomputable` only because the placeholder `omegaPow` is; Phase 2 makes it computable. -/
noncomputable def tower : Nat → Brouwer
  | 0     => omegaB
  | n + 1 => omegaPow (tower n)

/-- **ε₀** as the limit of the ω-tower — the fixed point ω^· cannot reach from below. -/
noncomputable def epsilonZero : Brouwer := lim tower

/-- **`≤` on Brouwer trees — PLACEHOLDER.** Phase 2: the constructive Brouwer order
    (cf. Kraus–Nordvall Forsberg–Xu, arXiv:2104.02549). Load-bearing because Lean lacks univalence,
    so leastness is stated via `≤`, and the fixed point may be a `≤`-biconditional rather than `=`. -/
def BLe : Brouwer → Brouwer → Prop := sorry

/-- **ε₀ is a fixed point of `ω^·`.** Phase 2: from sup-continuity (the universal property of `lim`). -/
theorem epsilonZero_is_fixed : omegaPow epsilonZero = epsilonZero := sorry

/-- **ε₀ is the LEAST fixed point of `ω^·`.** Phase 2 via Lemma 4 (sup-of-successors), avoiding the
    LEM case-split. THE deliverable — its `#print axioms` footprint is the experiment's verdict. -/
theorem epsilonZero_least_fixed (x : Brouwer) (hx : omegaPow x = x) : BLe epsilonZero x := sorry

end Brouwer

section PurityCheck
open Brouwer
-- STUB: both carry `sorryAx` until Phase 2. The PAYOFF check is whether the FILLED
-- `epsilonZero_least_fixed` is choice-free (`[propext]`/`[propext, Quot.sound]`) or carries
-- `Classical.choice` — the named killer of the "realization is the choice" thesis.
#print axioms epsilonZero_is_fixed
#print axioms epsilonZero_least_fixed
end PurityCheck

end ZeroParadox.ZPNMin
