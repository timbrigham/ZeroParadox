# Least in which order, Veblen's Corollary 1, and three traps around the seed range

Argument, prior art and fences for `ZeroParadox/Ordinal/Epsilon0LeastFP.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## What is confirmed, and what "least" means

Experiment G1 (T6 compute-the-invariant), independent of the MC-1 arc. ε₀ is where the ω-tower closes —
its **minimal** closure. **Do not call it a "ceiling" or "a large ordinal"**: positionally ε₀ is the
FIRST — `Ordinal.epsilon 0`, index zero in the epsilon enumeration, Veblen coordinates (1,0), the
**least fixed point** of `α ↦ ω^α` — and that is exactly what `epsilon0_least_fixedpoint` proves.

⚠ **"Minimum step" means a STABLE LANDING** — a fixed point of `α ↦ ω^α` — and in that sense ε₀ IS the
minimum distinct step above ⊥. `nothing_between_is_a_step` makes it checkable: **no** ordinal strictly
under ε₀ is fixed by the operator, and `bot_is_not_a_step` says ⊥ is not one either. The ordinals in
between — `ω`, `ω^ω`, … — are **stages of the ascent, not landings**: the operator fixes none of them,
so nothing stops there. That is also why `snapNucleus ⊥ = ε₀` (`ZeroParadox/Ordinal/SnapNucleus.lean`)
reaches it in one application — a closure operator's image *is* its fixed points, so the first landing
is the least one.

⚠ **What is NOT claimed is ORDER-adjacency** (`⊥ ⋖ ε₀`), and `epsilon0_least_fixedpoint` must not be
cited as if it proved a covering relation. Ordinals sit strictly between (`epsilonZero_tower_lt` with
`fundamentalSeq_strictMono`, `ZeroParadox/Ordinal/Gentzen.lean`); applied to `Ordinal`, `HasFirstStep`
is witnessed by `1`. Both readings are true and they are about **different orders**: least in the
FIXED-POINT order, not least in the ordinal order.

⚠ **And `epsilon0_least_fixedpoint` alone is only the lower-bound half.** `IsLeast {o | ω^o = o} ε₀`
needs membership too (`epsilon0_is_fixedpoint`); the bundled form is `epsilon0_min_eq_max`
(`ZeroParadox/Ordinal/Epsilon0MinMax.lean`). Cite that when the full `IsLeast` is wanted.

**Result: CONFIRMED.** `epsilon0_is_fixedpoint` (`ω ^ ε₀ = ε₀`) and `epsilon0_least_fixedpoint` (any `o`
with `ω^o = o` has `ε₀ ≤ o`) together pin ε₀ as the least fixed point. So the snap closure is minimal —
the framework's "snap at the minimum fixed-point closure" (Veblen-angle) as a two-line theorem. Both
reuse Mathlib (`omega0_opow_epsilon`, `epsilon_zero_le_of_omega0_opow_le`), cited not reproved.

## The rungs are the structure — the seed is not load-bearing

`nothing_between_is_a_step` says **no point strictly below ε₀ is a landing**. The seed-independence
theorems say the complementary thing: **every point at or below ε₀ reaches the SAME landing.**

**Provenance.** `ZeroParadox/Ordinal/Epsilon0MinMax.md` (**Tim, 2026-07-31**) already states the
implication `a ≤ nfp F 0 → nfp F a = nfp F 0`, describes the same route — ⚠ **though not identically:
that argument uses two `nfp_le_fp` applications with `nfp_fp`, where the proof here uses one plus
`epsilon0_least_fixedpoint`** — fences **normality** as load-bearing (*"the displayed implication is
false without it"*), and draws the same conclusion, *"⊥ is **a** seed, not a distinguished one"*,
claiming no novelty for it. **What the declarations add is only that the prose becomes checkable.**

## Prior art — the statement is CLASSICAL, seed-range and all

Veblen, *Continuous increasing functions of finite and transfinite ordinals*, Trans. Amer. Math. Soc. 9
(1908), read from source and filed in the project's paper library:

* **Corollary 1** has **two** clauses: *"If `f'` is the first derived function of `f`, **(A)** `f'(1)`
  is the least upper bound of `f(1), f[f(1)], ⋯`, and **(B)** if `f'(x) < a < f'(x+1)`, then `f'(x+1)`
  is the least upper bound of `f(a), f[f(a)], ⋯`."* **Veblen indexes from 1** (Cor 4: *"ε(x) stands for
  the ε-number ε_{x-1}"*), so `1` is his least ordinal and `f'(1)` the first fixed point. At `f = ωˣ`,
  **clause (A) is `nfp (ω^·) 1 = ε₀`** — which is `nfp_seed_independent_below_epsilon0` at `1`.
  Clause (B) is the between-consecutive-rungs case.
* **Corollary 4**: *"The first derived function of ωˣ is the function ε"* — what licenses reading (A) at
  `f = ωˣ`.

⚠ **Veblen's "derived function" is `deriv`, NOT `nfp`.** They are different objects:
`nfp (ω^·) 1 = ε₀` while `Ordinal.epsilon 1 = ε₁`. Mathlib's bridge is `epsilon_eq_deriv`
(`Mathlib/SetTheory/Ordinal/Veblen.lean`); the corpus uses it, it is not the corpus's.

**Residual delta against Veblen: the seed `0`, and the strict interior `1 < a < ε₀`.** Veblen's indexing
starts at `1`, so `a = 0` is outside his range — Mathlib's `epsilon_zero_eq_nfp` is its home — and the
interior is routine monotone filling between (A) and (B).

Veblen credits these outward to **Cantor**, *Beiträge zur Begründung der transfiniten Mengenlehre*,
Math. Ann. 49 (1897) — footnotes on the corollary page: *"Cantor, loc. cit., § 20."* and *"Cantor,
theorems G and H, p. 245."* ⚠ **In those two footnotes the OCR renders `§` as a backslash and the dagger
markers as `t` / `I`** (other `§` on the page survive), so a literal pattern misses them. Grep loosely.

**Mathlib carries this statement shape twice** — `Ordinal.nfp_add_eq_mul_omega0` and
`Ordinal.nfp_mul_eq_opow_omega0` (`Mathlib/SetTheory/Ordinal/FixedPoint.lean`), same naming idiom and
same `le_antisymm` + `nfp_le_fp` route. ⚠ **Absent from the pin is the SEED-RANGED ω-power entry**
(searched 2026-08-07): `Ordinal.epsilon_zero_eq_nfp` (seed `0`) and `epsilon_succ_eq_nfp` (successor
seeds) both exist. **So this closes a FORMALIZATION gap in Mathlib, not a mathematical one** — the
classical anchor is Corollary 1 clause (A) plus monotonicity, and the declaration is that in Lean.

Lemma locations: `FixedPoint.lean` supplies `nfp_le_fp` and `nfp_fp`; `isNormal_opow` is in
`Exponential.lean`; the ε₀ lemmas are in `Veblen.lean`.

## Why state it at all

`ε₀ = nfp (ω^·) ⊥` (`epsilon0_eq_nfp_bot`) is read across the corpus as *the snap seeded at the bottom*,
and `ZeroParadox/Order/LeastFixedPoint.lean` calls that the genuine ascent μ, seed ⊥ ≠ closure ε₀.
**That ascent is genuine.** What the declarations add is that **within `[0, ε₀]` the seed carries no
information**: seeding at `1`, at `ω`, at `ω^ω` gives the same ε₀.

**The general fact is that `nfp (ω^·) a` is the least ε-number `≥ a`**, and that statement is complete
on its own. Below ε₀ it is constantly ε₀; `epsilon_succ_eq_nfp` gives `nfp (ω^·) (succ ε₀) = ε₁`.

⚠ **Three traps around that statement, all mathematical:**

* **No ε-number can test it.** Every ε-number is a fixed point, so `nfp (ω^·) ε₁ = ε₁` and likewise at
  every rung — the whole family is blind to the difference between the general fact and *"above ε₀ the
  seed does all the work"*, which is false. Test above ε₀ with a **non**-fixed point such as `succ ε₀`.
* **The rungs do NOT partition.** The intervals `(ε_o, ε_(o+1)]` miss every **limit**-index ε-number,
  e.g. `ε_ω`.
* **Normality is essential**: the implication fails for a non-normal operator.

`Reading:` **INVARIANT** (conjectural) — the framework reads this as the ratified **"iterative bottoms"**
picture: the rungs of the succession are bottoms *relative to their iteration*, **never ⊥ itself**, and
⊥ sits at the base of the interval without being distinguished within it. The same **shape** is a
theorem in another carrier, `every_node_is_a_floor` (`ZeroParadox/Valuation/LocalFloor.lean`).

⚠ **SHAPE, never instance-of.** Different carriers, different mechanisms — self-similarity there, the
absence of fixed points strictly below ε₀ here — and the two theorems conclude **different
propositions**. `ℕ → Fin 2` is not `Ordinal`; only the moral is shared.

⚠ **`ε₀ ≠ ⊥` is untouched bedrock** (`epsilon0_ne_bot`), and the ratified vocabulary exists precisely
because the rungs are **not** ⊥. **Nothing here identifies any rung with ⊥.**

⚠ **"Iterative bottom" is the ratified term for the ITERATION sense.** Do not substitute "local bottom"
*there* — that phrase is taken for the per-domain MC-1 family
(`ZeroParadox/Category/GlobalZero.lean`). (`ZeroParadox/Valuation/LocalFloor.lean` uses it for a third,
subtree-local sense; that is that file's own usage and not what the iteration rule governs.)
