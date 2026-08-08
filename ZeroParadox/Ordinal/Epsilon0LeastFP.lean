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

/-! ### The rungs are the structure — the seed is not load-bearing

`nothing_between_is_a_step` says **no point strictly below ε₀ is a landing**. The theorems below say
the complementary thing: **every point at or below ε₀ reaches the SAME landing.**

**Provenance — this is NOT a new observation, and an earlier revision of this block said it was.**
`ZeroParadox/Ordinal/Epsilon0MinMax.lean` § I-b (*"Two fences on the '⊥ the seed' reading"*,
**Tim, 2026-07-31**) already states the implication `a ≤ nfp F 0 → nfp F a = nfp F 0`, describes the
same route (two `nfp_le_fp` applications with `nfp_fp`; the proof below uses one plus
`epsilon0_least_fixedpoint`), fences **normality** as load-bearing (*"the displayed implication is false
without it"*), and draws the same conclusion — *"⊥ is **a** seed, not a distinguished one"* — under its
own verdict, ***"Elementary and not novel."*** ⚠ That earlier revision claimed the corpus *"never
measured it"*; **false**, and refuted both by § I-b and by `epsilon0_ne_bot`'s docstring **in this
file**, which already cites § I-b. Three independent gates caught it. **What is new below is only that
the prose becomes a checkable declaration.**

**Prior art — and the statement below is CLASSICAL, seed-range and all.** Veblen, *Continuous
increasing functions of finite and transfinite ordinals*, Trans. Amer. Math. Soc. 9 (1908) — read from
source, filed in the project's paper library:

* **Corollary 1**: *"if `f'(x) < a < f'(x+1)`, then `f'(x+1)` is the least upper bound of
  `f(a), f[f(a)], …`"* — iterating a normal function from a seed strictly **between two consecutive
  derived values** reaches the next one. ⚠ **That range is ABOVE the first fixed point and therefore
  does NOT cover `[0, ε₀]`**, which is what the declaration below states; an earlier draft claimed it
  did. The shape is the same; the range is not.
* **Corollary 4**: *"The first derived function of ωˣ is the function ε"*.
  ⚠ **Veblen's "derived function" is Mathlib's `deriv`, NOT `nfp`** — they are different objects, and
  an earlier draft wrote *"`nfp (ω^·)` **is** the ε-enumeration"*, which is **false**:
  `nfp (ω^·) 1 = ε₀` while `Ordinal.epsilon 1 = ε₁`. The corpus's own bridge between them is
  `epsilon_eq_deriv`.

Veblen credits these outward to **Cantor**, *Beiträge zur Begründung der transfiniten Mengenlehre*,
Math. Ann. 49 (1897) — his footnotes on the corollary page read *"Cantor, loc. cit., § 20."* and
*"Cantor, theorems G and H, p. 245."*

⚠ **An earlier draft of this line declared that locus "not reproducible from the filed copy" and
withdrew it. That was FALSE and the retraction is itself retracted.** Both footnotes are present; the
OCR renders `§` as a backslash and the dagger markers as `t`/`I`, and **the search that "failed" was
truncated to its first three results**. Three gates caught it. **This is the same defect the
neighbouring `InfinitudeFloor.lean` docstring already records against a different source — a truncated
search recorded as an absence — recurring one file away, and written into a docstring in the same
session that added the rule against it.**

Mathlib carries the same statement shape twice — `Ordinal.nfp_add_eq_mul_omega0` and
`Ordinal.nfp_mul_eq_opow_omega0` (`Mathlib/SetTheory/Ordinal/FixedPoint.lean`), same naming idiom and
same `le_antisymm` + `nfp_le_fp` route. ⚠ **What is absent from the pin is the SEED-RANGED ω-power
entry** (searched 2026-08-07): `Ordinal.epsilon_zero_eq_nfp` (seed `0`) and `epsilon_succ_eq_nfp`
(successor seeds) both exist. **So the gap being filled is a FORMALIZATION gap in Mathlib, not a
mathematical one** — the mathematics is Veblen's, and the framework invented none of it.

⚠ Scope correction to an earlier draft, which said *"the very file these proofs draw their lemmas
from"* (`FixedPoint.lean` supplies `nfp_le_fp` and
`nfp_fp`; `isNormal_opow` is in `Exponential.lean`, the ε₀ lemmas in `Veblen.lean`).

**Why state it here at all.** `ε₀ = nfp (ω^·) ⊥` (`epsilon0_eq_nfp_bot`) is read across the corpus as
*the snap seeded at the bottom*, and `ZeroParadox/Order/LeastFixedPoint.lean` § IV calls it *"genuine
ascent μ (seed ⊥ ≠ closure ε₀)"*. **That ascent is genuine.** What the declarations below add is that
**within `[0, ε₀]` the seed carries no information**: seeding at `1`, at `ω`, at `ω^ω` gives the same
ε₀. ⚠ **Scope it — at or below ε₀ ONLY.**

⚠ **An earlier draft said "above ε₀ the seed does all the work", which is FALSE**, and illustrated it
with `nfp (ω^·) ε₁ = ε₁` — the one family that hides the error, since ε₁ is itself a fixed point and
`nfp` returns any fixed point unchanged. **The general fact is that `nfp (ω^·) a` is the least ε-number `≥ a`**, and that statement is complete
on its own. Below ε₀ it is constantly ε₀; `epsilon_succ_eq_nfp` gives `nfp (ω^·) (succ ε₀) = ε₁`.

⚠ Two glosses bolted onto that statement in an earlier draft were **false** and are withdrawn:
*"above ε₀ the answer is not the seed"* (it **is** the seed at every ε-number — `nfp (ω^·) ε₁ = ε₁`),
and *"the rungs partition"* (the intervals `(ε_o, ε_(o+1)]` miss every **limit**-index ε-number, e.g.
`ε_ω`). **Neither gloss is needed; the least-ε-number-≥-`a` form already says everything true here.**
⚠ **And normality is essential**, per § I-b's fence: the implication fails for a non-normal operator.

`Reading:` **INVARIANT** (conjectural) — the framework reads this as the ratified **"iterative
bottoms"** picture: the rungs of the succession are bottoms *relative to their iteration*, **never ⊥
itself**, and ⊥ sits at the base of the interval without being distinguished within it. The same
**shape** is a theorem in another carrier, `every_node_is_a_floor`
(`ZeroParadox/Valuation/LocalFloor.lean`).

⚠ **SHAPE, never instance-of.** Different carriers, different mechanisms — self-similarity there, the
absence of fixed points strictly below ε₀ here — and the two theorems conclude **different
propositions**. `ℕ → Fin 2` is not `Ordinal`; only the moral is shared.
⚠ **`ε₀ ≠ ⊥` is untouched bedrock** (`epsilon0_ne_bot`), and the ratified vocabulary exists precisely
because the rungs are **not** ⊥. **Nothing here identifies any rung with ⊥.**
⚠ **"Iterative bottom" is the ratified term for the ITERATION sense.** Do not substitute "local
bottom" *there* — that phrase is taken for the per-domain MC-1 family
(`ZeroParadox/Category/GlobalZero.lean`). (`ZeroParadox/Valuation/LocalFloor.lean` uses it for a
third, subtree-local sense; that is that file's own usage and not what the iteration rule governs.) -/

/-- **`Statement:` every seed at or below ε₀ reaches ε₀.** The least fixed point *from* `a` is ε₀ for
every `a ≤ ε₀`, so within that range the seed carries no information: `≤` because ε₀ is itself a
fixed point at or above `a` (`epsilon0_is_fixedpoint` with `Ordinal.nfp_le_fp`), and `≥` because ε₀ is
the least fixed point outright (`epsilon0_least_fixedpoint` applied to `Ordinal.nfp_fp`). ⚠ Normality
of `α ↦ ω^α` is load-bearing, and `nothing_between_is_a_step` is **not** used. -/
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
