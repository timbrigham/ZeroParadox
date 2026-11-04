import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Epsilon0LeastFP

set_option maxHeartbeats 400000

/-!
# ε₀ is min ≡ max: the snap from ⊥ of `Ordinal` to ε₀ is one Kleene chain (seed → closure)

## Engineer's Take

The fact that epsilon zero is the minimum step above zero was originally only proved in computability
theory, where we started our modeling. This lets us use epsilon zero as a fixed point and Gentzen for a
redundant and believed to be stronger representation.

---

## Formal Overview
Minimum and maximum are the two faces of a **least fixed point**, so ε₀
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
    *min* reading). That an object is both at once is the signature of a least fixed point reached
    by iterating a normal map: the least fixed point at or above a seed *is* the supremum of the
    ascending iterates (the `example` after `isLeastFixedPointFrom_nfp`,
    `ZeroParadox/Order/LeastFixedPoint.lean`). Bundles
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

/-! ### Statement controls

Each statement below, written as a `Prop` with no proof attached, so that the purity block prints the
footprint the STATEMENT carries by itself (the statement control of
`ZeroParadox/Category/ChoiceCannotBe.md`). The `example`s tie each control to its theorem: they stop
compiling if the theorem's statement changes. -/

/-- `Statement:` the statement of `epsilon0_eq_nfp_bot`, at universe 0, as a bare proposition. -/
def epsilon0EqNfpBotStatement : Prop :=
  epsilonZero = Ordinal.nfp (fun α : Ordinal.{0} => Ordinal.omega0 ^ α) (⊥ : Ordinal.{0})

/-- `Statement:` the statement of `epsilon0_min_eq_max`, at universe 0, as a bare proposition. -/
def epsilon0MinMaxStatement : Prop :=
  epsilonZero.{0} = ⨆ n : ℕ, fundamentalSeq.{0} n
    ∧ IsLeast {o : Ordinal.{0} | Ordinal.omega0 ^ o = o} epsilonZero

example : epsilon0EqNfpBotStatement := epsilon0_eq_nfp_bot
example : epsilon0MinMaxStatement := epsilon0_min_eq_max

/-! ### § III. ε₀ occupies the die role `PinnedLimit` (`ZeroParadox/Die.lean` § XXIV)

`Statement:` COINCIDENCE, the two faces of § II as one role: the tower from ⊥ of `Ordinal` is a climbing
run of `α ↦ ω^α` (`Monotone s`, a property of the run, distinct from the motion property
`Motion.Climb`), and ε₀ is its least upper bound, is not a stage, and is the least fixed point. Under
`α ↦ ω^α` every occupant of `PinnedLimit`, over any run, is ε₀ (`pinnedLimit_opow_eq_epsilon0`). -/

universe u

/-- `Statement:` `fundamentalSeq` is a run of `Motion.ofFun (ω^·)`, and ε₀ occupies
    `PinnedLimit (ω^·) fundamentalSeq`, by `epsilon0_min_eq_max`, `epsilonZero_tower_lt` and
    `fundamentalSeq_strictMono`. -/
theorem epsilon0_pinnedLimit :
    (Motion.ofFun fun α : Ordinal => Ordinal.omega0 ^ α).IsRun fundamentalSeq ∧
    PinnedLimit (fun α : Ordinal => Ordinal.omega0 ^ α) fundamentalSeq epsilonZero := by
  obtain ⟨hsup, hleast⟩ := epsilon0_min_eq_max
  refine ⟨fun n => ?_, ?_, fun ⟨n, hn⟩ => (epsilonZero_tower_lt n).ne hn, hleast,
    (strictMono_nat_of_lt_succ fundamentalSeq_strictMono).monotone⟩
  · show fundamentalSeq (n + 1) = Ordinal.omega0 ^ fundamentalSeq n
    simp only [fundamentalSeq, Function.iterate_succ_apply']
  · rw [hsup]
    exact isLUB_ciSup ⟨epsilonZero, fun _ ⟨n, hn⟩ => hn ▸ (epsilonZero_tower_lt n).le⟩

/-- `Statement:` ε₀ does not occupy `PinnedLimitUnique (ω^·) fundamentalSeq`: ε₁ is another fixed
    point (Mathlib `Ordinal.omega0_opow_epsilon`). -/
theorem epsilon0_not_pinnedLimitUnique :
    ¬ PinnedLimitUnique (fun α : Ordinal => Ordinal.omega0 ^ α) fundamentalSeq epsilonZero :=
  fun ⟨_, h⟩ => (Ordinal.veblen_right_strictMono 1 (show (0 : Ordinal) < 1 from zero_lt_one)).ne
    (h _ (Ordinal.omega0_opow_epsilon 1)).symm

/-- `Statement:` under `α ↦ ω^α`, for every run `s`, an occupant of `PinnedLimit (ω^·) s` is ε₀:
    clause (c) is leastness over all of `Ordinal`, and ε₀ is that least fixed point. -/
theorem pinnedLimit_opow_eq_epsilon0 (s : ℕ → Ordinal.{u}) (c : Ordinal.{u})
    (h : PinnedLimit (fun α : Ordinal.{u} => Ordinal.omega0 ^ α) s c) : c = epsilonZero :=
  h.2.2.1.unique ⟨epsilonZero_fixedPoint, fun o ho => epsilon0_least_fixedpoint o ho⟩

-- `Statement:` ε₀'s occupancy is closure ordinal ω for `α ↦ ω^α` from ⊥ of `Ordinal`: the tower's
-- least upper bound is fixed and no stage is (`pinnedLimit_iff_closure_omega`).
example : PinnedLimit (fun α : Ordinal.{u} => Ordinal.omega0 ^ α) fundamentalSeq.{u} epsilonZero.{u} ↔
    (IsLUB (Set.range fundamentalSeq.{u}) epsilonZero.{u} ∧ Ordinal.omega0 ^ epsilonZero.{u} = epsilonZero ∧
      ∀ n, Ordinal.omega0 ^ fundamentalSeq.{u} n ≠ fundamentalSeq n) := by
  have := pinnedLimit_iff_closure_omega (fun α : Ordinal.{u} => Ordinal.omega0 ^ α)
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.monotone epsilonZero
  rw [Ordinal.bot_eq_zero] at this
  exact this

end ZeroParadox

/-! ## Axiom Purity Check

Both results are corollaries of Mathlib's classically built `Ordinal` fixed-point theory (`nfp`,
`epsilon`). **Status: STATEMENT-CARRIED** (`ZeroParadox/Category/ChoiceCannotBe.md`): both statements,
with no proof attached, carry `Classical.choice` (the statement controls `epsilon0EqNfpBotStatement` and
`epsilon0MinMaxStatement`, printed below). The choice is NOT in the `Ordinal` type; it enters through the
order instance and the operations. The remaining question is a restatement on a carrier whose statements
are choice-free, with two readings: a defined one, in Lean on `E0Note`, and a derived one, on a well-founded
carrier, not located as of 2026-10-13; both, with the search record: `ZeroParadox/Ordinal/SnapNucleus.md` § "Axiom footprint". ZP-N's ascent on
`ONote` (`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`) is evidence for it, not a re-proof. -/

section PurityCheck
open ZeroParadox
#print axioms epsilon0_eq_nfp_bot
#print axioms epsilon0_min_eq_max
-- The statement controls: the statements alone.
#print axioms epsilon0EqNfpBotStatement
#print axioms epsilon0MinMaxStatement
#print axioms epsilon0_pinnedLimit
#print axioms epsilon0_not_pinnedLimitUnique
#print axioms pinnedLimit_opow_eq_epsilon0
end PurityCheck
