import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Epsilon0LeastFP

set_option maxHeartbeats 400000

/-!
# ε₀ is min ≡ max: the snap ⊥ → ε₀ is one Kleene chain (seed → closure)

## Engineer's Take

The fact that epsilon zero is the minimum step above zero was originally only proved in computability
theory, where we started our modeling. This lets us use epsilon zero as a fixed point and Gentzen for a
redundant and believed to be stronger representation.

---

## Formal Overview (AI-assisted)

"ε₀ is both a minimum and a maximum, depending on your point of view" is not a tension — it is the
defining signature of a **least fixed point** (Knaster–Tarski / Kleene): the least fixed point of a
monotone map reached from a seed *is* the supremum of the ascending iterates. This file bundles the two
halves the framework already proves, in two separate files, into one statement about the one object.

- **max reading:** ε₀ is the supremum of the ω-tower `ω, ω^ω, ω^(ω^ω), …` (`epsilonZero_eq_iSup`,
  `ZeroParadox/Ordinal/Gentzen.lean`).
- **min reading:** ε₀ is the least ordinal fixed by `α ↦ ω^α` (`epsilon0_least_fixedpoint`,
  `ZeroParadox/Ordinal/Epsilon0LeastFP.lean`).

Since `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`), the seed of that tower is the ordinal bottom ⊥, so
the snap `⊥ → ε₀` reads literally as `⊥ → ⨆ₙ (ω^·)ⁿ(⊥)`: the floor ⊥ is the *seed* and ε₀ its *closure*
(`epsilon0_eq_nfp_bot`). This is a *placement* of ε₀ as the μ (least fixed point) of the ascent operator
seeded at ⊥ — a bundling of already-proved in-repo results and Mathlib's `nfp` theory, not a new
theorem, and it does not close the separate CNF/ℤ₂ value-bridge (`Gentzen.lean`, item 4, open).

## Structure

- § I  ε₀ as the near-fixed-point iteration seeded at ⊥ (seed → closure)
- § II the min ≡ max capstone (one object, both readings)
-/

namespace ZeroParadox

open Ordinal

/-! ### § I. ε₀ as the ω-tower seeded at the ordinal bottom ⊥ -/

/-- ε₀ is the near-fixed-point iteration of `α ↦ ω^α` seeded at the ordinal bottom ⊥ (not merely `0`).
    Since `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`), this reseeds `epsilonZero_eq_nfp`: the snap
    `⊥ → ε₀` is the seed → closure of one Kleene chain — ⊥ the seed, ε₀ the closure. -/
theorem epsilon0_eq_nfp_bot :
    epsilonZero = Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) := by
  rw [Ordinal.bot_eq_zero]
  exact epsilonZero_eq_nfp

/-! ### § I-b. Two fences on the "⊥ the seed" reading (Tim, 2026-07-31)

**The seed is not load-bearing.** `nfp` is by construction the least fixed point `≥` its seed, so
**every** seed at or below the closure reaches the same closure — verified by probe: for
`F = (ω ^ ·)`, `nfp F 1 = nfp F 0`, and generally `a ≤ nfp F 0 → nfp F a = nfp F 0` (two lines from
Mathlib's `Ordinal.nfp_le_fp` and `Ordinal.nfp_fp`; standard, claimed as no novelty). So ⊥ is *a*
seed, not a distinguished one: **the operator determines the destination, and the starting point is
incidental.** § I's "⊥ the seed, ε₀ the closure" is true and its emphasis overstates ⊥'s role.
*(Also: "seeded at the ordinal bottom ⊥ (not merely `0`)" claims a distinction this carrier lacks —
`Ordinal.bot_eq_zero` makes them definitionally identical.)*

**And the snap runs on the operator that does NOT fix ⊥.** `Computability/SelfApp.lean:73` assumes
`fixed_bot : selfApp bot = bot` as a **class field**, and every "the bottom cannot move" result
descends from it. Here the opposite holds and is provable: `ω ^ (0 : Ordinal) = 1 ≠ 0`, so `α ↦ ω^α`
does **not** fix the ordinal bottom (this is the argument already inside
`Epsilon0LeastFP.epsilon0_ne_zero`). **Two operators, opposite behaviour at ⊥, and the snap is the
action of the one that moves it.** Neither observation is stated anywhere else in the corpus.
Full record: `.claude-local/notes/tower_seed_is_not_load_bearing_2026-07-31.md` and
`.claude-local/notes/forced_movement_two_operators_2026-07-31.md`. -/

/-! ### § II. The min ≡ max capstone -/

/-- **The min ≡ max capstone.** One theorem, one object: ε₀ (`epsilonZero`) is simultaneously the
    **supremum** of the ω-tower (the *max* reading) and the **least** fixed point of `α ↦ ω^α` (the
    *min* reading). That an object is both at once is the defining signature of a least fixed point:
    the least fixed point reached from a seed *is* the supremum of the ascending iterates. Bundles
    `epsilonZero_eq_iSup` (max, `Gentzen.lean`) with `epsilonZero_fixedPoint` and
    `epsilon0_least_fixedpoint` (min, `Epsilon0LeastFP.lean`) — previously an impression spread across
    two files, here one statement.

    **⚠ CORRECTED TWICE, 2026-07-30 (adversary gate, bedrock). Read the whole of this before citing
    any "min≡max family".** An earlier revision called `epsilon0_min_eq_max` an instance of
    `fork_collapse_iff`; a second revision fixed that but then called `selfApp_bot_is_both_extremal` and the
    categorical zero object instances instead. **BOTH claims are false, for the same reason: nothing here
    satisfies `fork_collapse_iff`'s hypotheses.** It requires `[CompleteLattice α]` and a *monotone*
    `f : α →o α` (`Settheory/FixedPointFork.lean`). Measured against that:
    * `epsilon0_min_eq_max` — `α ↦ ω^α` on `Ordinal` has a **proper class** of fixed points (`ε₁, ε₂, …`
      all satisfy `ω ^ ε_ o = ε_ o`, Mathlib `omega0_opow_epsilon`), so the uniqueness side of (iii)
      fails. The case is in fact stronger than that and the earlier wording under-stated it: `Ordinal`
      carries no `CompleteLattice` instance in the pin, so `lfp` and `gfp` are not defined there at all
      and `lfp ≠ gfp` is not even a well-formed proposition. The hypotheses fail before the conclusion
      can be stated.
    * `selfApp_bot_is_both_extremal` — `ZPSemilattice` is a **bare join-semilattice**, not a complete
      lattice, and `AbstractSelfApp.selfApp : L → L` is **not an `OrderHom`**.
    * `catseam_is_frameflip` — lives in `ModuleCat ℂ`, a **category**, not a lattice at all.

    **So there is no common instance and no "four witnesses of one phenomenon".** What these share is a
    SHAPE — one object carrying both extremal characterizations at once — and per this project's standing
    rule a shared shape across distinct structures is a **type boundary**, never a common theorem. State
    the shape; do not state an instance-of relation. Each fact stands on its own carrier:
    ε₀ is least-fixed-point **and** tower-supremum (the Kleene shape); ⊥ is least **and** greatest fixed
    point of `selfApp`; the seam is initial **and** terminal. `fork_collapse_iff` is a *fourth*, separate
    fact about complete lattices — the general condition under which a fork collapses — and is **not** the
    genus of the other three. -/
theorem epsilon0_min_eq_max :
    epsilonZero = ⨆ n : ℕ, fundamentalSeq n
      ∧ IsLeast {o : Ordinal | Ordinal.omega0 ^ o = o} epsilonZero := by
  refine ⟨epsilonZero_eq_iSup, epsilonZero_fixedPoint, fun o ho => ?_⟩
  exact epsilon0_least_fixedpoint o ho

end ZeroParadox

/-! ## Axiom Purity Check

Both results are corollaries of Mathlib's `Ordinal` fixed-point theory (`nfp`, `epsilon`), which is
classically built, so `Classical.choice` is expected here. **Status: UNCLASSIFIED** — calling it
"representational, not intrinsic" (as an earlier version of this note did) is an *eliminability* claim,
and no choice-free re-proof of these results exists. Note also that the choice is NOT in the `Ordinal`
type, which measures `[propext, Quot.sound]`; it enters through the order instance and the operations.
ZP-N's choice-free snap-from-below on `ONote` is suggestive for these results without being a re-proof of
them (cf. `ZeroParadox/Ordinal/ConstructiveOrdinals.lean`). Recorded honestly below. -/

section PurityCheck
open ZeroParadox
#print axioms epsilon0_eq_nfp_bot
#print axioms epsilon0_min_eq_max
end PurityCheck
