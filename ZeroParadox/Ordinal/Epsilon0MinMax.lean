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

## Formal Overview
Minimum and maximum are the two faces of a **least fixed point** (Knaster–Tarski / Kleene), so ε₀
carrying both is a signature rather than a tension. Why, and the two fences on reading ⊥ as *the*
seed: `ZeroParadox/Ordinal/Epsilon0MinMax.md`.
-/

namespace ZeroParadox

open Ordinal

/-! ### § I. ε₀ as the ω-tower seeded at the ordinal bottom ⊥ -/

/-- ε₀ is the near-fixed-point iteration of `α ↦ ω^α` seeded at the ordinal bottom ⊥. Since
    `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`, definitionally — this carrier draws no distinction
    between them), this restates `epsilonZero_eq_nfp` at ⊥: the snap `⊥ → ε₀` is the seed → closure
    of one Kleene chain. **§ I-b fences the emphasis: the seed is not load-bearing.** -/
theorem epsilon0_eq_nfp_bot :
    epsilonZero = Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) := by
  rw [Ordinal.bot_eq_zero]
  exact epsilonZero_eq_nfp

/-! ### § I-b. Two fences on the "⊥ the seed" reading (Tim, 2026-07-31)

⊥ is *a* seed, not a distinguished one — for a normal `F` every seed at or below the closure reaches
the same closure — and `α ↦ ω^α` does **not** fix ⊥. Both fences, with their hypotheses and scope:
`ZeroParadox/Ordinal/Epsilon0MinMax.md`. -/

/-! ### § II. The min ≡ max capstone

`Statement:` **COINCIDENCE** — `epsilon0_min_eq_max` proves that one object, ε₀, carries both
extremal characterisations simultaneously: the least fixed point of `α ↦ ω^α` and the supremum of
the ω-tower. -/

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
and no choice-free re-proof of these results was located as of 2026-08-02. Note also that the choice is NOT in the `Ordinal`
type, which measures `[propext, Quot.sound]`; it enters through the order instance and the operations.
ZP-N's choice-free snap-from-below on `ONote` is suggestive for these results without being a re-proof of
them (cf. `ZeroParadox/Ordinal/ConstructiveOrdinals.lean`). Recorded honestly below. -/

section PurityCheck
open ZeroParadox
#print axioms epsilon0_eq_nfp_bot
#print axioms epsilon0_min_eq_max
end PurityCheck
