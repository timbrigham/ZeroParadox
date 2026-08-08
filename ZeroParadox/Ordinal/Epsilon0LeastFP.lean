import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 400000

/-!
# Batch 2 / G1 (pipeline, T6): ε₀ is the LEAST fixed point of α ↦ ωᵅ — the snap sits at minimal closure

Experiment G1 (T6 compute-the-invariant), independent of the MC-1 arc. ε₀ is where the ω-tower closes —
its **minimal** closure. **Do not call it a "ceiling" or "a large ordinal"** (an earlier revision of this
line said "the snap ceiling"): positionally ε₀ is the FIRST — `Ordinal.epsilon 0`, index zero in the
epsilon enumeration, Veblen coordinates (1,0), the **least fixed point** of `α ↦ ω^α` — and that
is exactly what `epsilon0_least_fixedpoint` below proves.

⚠ **"Minimum step" means a STABLE LANDING — a fixed point of `α ↦ ω^α` — and in that sense ε₀
IS the minimum distinct step above ⊥.** `nothing_between_is_a_step` below makes it checkable: **no**
ordinal strictly under ε₀ is fixed by the operator, and `bot_is_not_a_step` says ⊥ is not one either.
The ordinals in between — `ω`, `ω^ω`, … — are **stages of the ascent, not landings**: the operator
fixes none of them, so nothing stops there. That is also why `snapNucleus ⊥ = ε₀`
(`ZeroParadox/Ordinal/SnapNucleus.lean`) reaches it in one application — a closure operator's image
*is* its fixed points, so the first landing is the least one.

⚠ **What is NOT claimed is ORDER-adjacency** (`⊥ ⋖ ε₀`), and `epsilon0_least_fixedpoint` must not be
cited as if it proved a covering relation. Ordinals sit strictly between (`epsilonZero_tower_lt` with
`fundamentalSeq_strictMono`, `ZeroParadox/Ordinal/Gentzen.lean`); applied to `Ordinal`,
`HasFirstStep` is witnessed by `1`. Both readings are true and they are about **different orders**:
least in the FIXED-POINT order, not least in the ordinal order.

⚠ **And `epsilon0_least_fixedpoint` alone is only the lower-bound half.** `IsLeast {o | ω^o = o} ε₀`
needs membership too (`epsilon0_is_fixedpoint`); the bundled form is `epsilon0_min_eq_max`
(`ZeroParadox/Ordinal/Epsilon0MinMax.lean`). Cite that when the full `IsLeast` is wanted.

**Result: CONFIRMED.** `epsilon0_is_fixedpoint` (`ω ^ ε₀ = ε₀`) and `epsilon0_least_fixedpoint` (any
`o` with `ω^o = o` has `ε₀ ≤ o`) together pin ε₀ as the least fixed point. So the snap closure is minimal —
the framework's "snap at the minimum fixed-point closure" (Veblen-angle) as a two-line theorem. Both reuse
Mathlib (`omega0_opow_epsilon`, `epsilon_zero_le_of_omega0_opow_le`), cited not reproved.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

open Ordinal

/-- ε₀ is a fixed point of `α ↦ ω^α` (= Mathlib `omega0_opow_epsilon` at 0). -/
theorem epsilon0_is_fixedpoint : ω ^ ε₀ = ε₀ :=
  omega0_opow_epsilon 0

/-- **ε₀ is the LEAST fixed point.** Any ordinal `o` closed under exponentiation (`ω^o = o`) satisfies
    `ε₀ ≤ o`. With `epsilon0_is_fixedpoint`, ε₀ is the minimal closure — the snap sits at the least
    ordinal fixed by `α ↦ ω^α`, not a larger Veblen point. -/
theorem epsilon0_least_fixedpoint (o : Ordinal) (h : ω ^ o = o) : ε₀ ≤ o :=
  epsilon_zero_le_of_omega0_opow_le (le_of_eq h)

/-- **`Statement:` nothing strictly below ε₀ is a landing.** No ordinal under ε₀ is fixed by
`α ↦ ω^α`, so the intermediate ordinals are stages of the ascent rather than steps. This is the
checkable half of "ε₀ is the minimum distinct step above ⊥". -/
theorem nothing_between_is_a_step (o : Ordinal) (hlt : o < Ordinal.epsilon 0) :
    Ordinal.omega0 ^ o ≠ o :=
  fun h => absurd (epsilon0_least_fixedpoint o h) (not_le.mpr hlt)

/-- **`Statement:` and ⊥ is not a landing either**, so ε₀ is the first. -/
theorem bot_is_not_a_step : Ordinal.omega0 ^ (0 : Ordinal) ≠ (0 : Ordinal) := by simp

/-! ### The rungs are the structure — the seed does no work

`nothing_between_is_a_step` says **no point below ε₀ is a landing**. The two theorems below say the
complementary thing: **every point below ε₀ reaches the SAME landing.** Together they give the shape
of the interval — undifferentiated by the operator, collapsing onto its ceiling.

**Why this is worth stating.** `ε₀ = nfp (ω^·) ⊥` (`epsilon0_eq_nfp_bot`) is read across the corpus as
*the snap seeded at the bottom*, and `ZeroParadox/Order/LeastFixedPoint.lean` § IV calls it *"genuine
ascent μ (seed ⊥ ≠ closure ε₀)"*. That ascent is genuine. **But ⊥ is not a distinguished seed** —
seeding at `1`, at `ω`, at `ω^ω` gives exactly the same ε₀. Measured 2026-08-07; the corpus had noted
the tension (`nfp` is seed-parametric via `isLeastFixedPointFrom_nfp`) and never measured it.

`Reading:` (conjectural) this is **"iterative bottoms"** — the ratified name for the rungs of the snap
succession, *a bottom relative to its iteration, never ⊥ itself*. Under that reading ⊥ is **rung zero**
rather than a privileged origin, and the same shape is a theorem in a different carrier:
`every_node_is_a_floor` (`ZeroParadox/Valuation/LocalFloor.lean`) proves every node of the binary tree
roots a floor of infinite complexity, with the global floor merely the empty-prefix case.

⚠ **SHAPE, never instance-of.** The two live over different carriers by different mechanisms —
`LocalFloor`'s runs on self-similarity (`shiftEnd` / `prependEnd`), this one on there being no fixed
point below ε₀. `ℕ → Fin 2` is not `Ordinal`; a common theorem across them would be the type boundary
this corpus refuses everywhere else. ⚠ **And `ε₀ ≠ ⊥` is untouched bedrock** (`epsilon0_ne_bot`): the
rungs are *not* ⊥, which is exactly why they need a role name rather than an identity.
⚠ **Do NOT write "local bottom"** for this — that phrase is taken for the per-domain MC-1 family
(`ZeroParadox/Category/GlobalZero.lean`). The ratified term is **iterative bottom**. -/

/-- **`Statement:` every seed at or below ε₀ reaches ε₀.** The least fixed point *from* `a` is ε₀ for
every `a ≤ ε₀`, so the seed carries no information: `≤` because ε₀ is itself a fixed point at or above
`a`, and `≥` because ε₀ is the least fixed point outright (`epsilon0_least_fixedpoint`). -/
theorem nfp_seed_independent_below_epsilon0 (a : Ordinal) (ha : a ≤ ε₀) :
    Ordinal.nfp (fun α => ω ^ α) a = ε₀ := by
  have hnorm := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  refine le_antisymm ?_ ?_
  · exact Ordinal.nfp_le_fp hnorm.strictMono.monotone ha (le_of_eq epsilon0_is_fixedpoint)
  · exact epsilon0_least_fixedpoint _ (Ordinal.nfp_fp hnorm a)

/-- **`Statement:` concretely — seeding at `1` is seeding at `⊥`.** The witness that makes the
seed-independence visible without a quantifier. -/
theorem nfp_seed_one_eq_seed_bot :
    Ordinal.nfp (fun α => ω ^ α) 1 = Ordinal.nfp (fun α => ω ^ α) (⊥ : Ordinal) := by
  rw [nfp_seed_independent_below_epsilon0 1 (Order.one_le_iff_ne_zero.mpr (Ordinal.epsilon_pos 0).ne'),
      nfp_seed_independent_below_epsilon0 ⊥ bot_le]

/-- **Invariant — ε₀ ≠ 0.** ε₀ can never be zero, in any reading. It is a fixed point of `α ↦ ω^α`
    (`epsilon0_is_fixedpoint`); were it 0, that would say `ω^0 = 0`, i.e. `1 = 0`. This is the bedrock
    guard beneath every ε₀ characterization. -/
theorem epsilon0_ne_zero : ε₀ ≠ 0 := by
  intro h
  have hf := epsilon0_is_fixedpoint
  rw [h, opow_zero] at hf
  exact one_ne_zero hf

/-- **Invariant — ε₀ ≠ ⊥.** Since `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`) and ε₀ ≠ 0, ε₀ is never
    the bottom ⊥. ⊥ is *a* base the ε₀-tower is seeded at (`epsilon0_eq_nfp_bot`), never its closure.
    It is the *least* such base and not the only one: for **normal** `F`, every seed at or below the
    closure reaches the same closure (`ZeroParadox/Ordinal/Epsilon0MinMax.lean` § I-b). The invariant
    does not depend on that. -/
theorem epsilon0_ne_bot : ε₀ ≠ (⊥ : Ordinal) := by
  rw [Ordinal.bot_eq_zero]
  exact epsilon0_ne_zero

/-- **ε₀'s Veblen coordinates are (1, 0).** ε₀ = `veblen 1 0` (Mathlib `epsilon := veblen 1`, so this is
    definitional): the element at index 0 of level 1 — the origin of the Veblen coordinate system, hence
    the *minimum* fixed-point closure (matching `epsilon0_least_fixedpoint`), not a definitional pick of a
    large ordinal. The hierarchy continues above ε₀ (ε₁, ε₂, …, ζ₀ = `veblen 2 0`, …) up to Γ₀, the
    Feferman–Schütte ordinal closing the two-argument Veblen hierarchy; the framework lives below Γ₀. -/
theorem epsilon0_eq_veblen_one_zero : ε₀ = Ordinal.veblen 1 0 := rfl

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms epsilon0_is_fixedpoint
#print axioms epsilon0_least_fixedpoint
#print axioms nothing_between_is_a_step
#print axioms bot_is_not_a_step
#print axioms nfp_seed_independent_below_epsilon0
#print axioms nfp_seed_one_eq_seed_bot
#print axioms epsilon0_ne_zero
#print axioms epsilon0_ne_bot
#print axioms epsilon0_eq_veblen_one_zero
end PurityCheck
