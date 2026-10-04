# Epsilon0CannotBe — ride-along documentation

Moved from `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## Formal Overview (AI-assisted)

**This is the ε₀-characterization object.** ε₀ is not a "large ordinal" chosen by fiat; it is the
*first (least) fixed point of the ω-tower operator `α ↦ ω^α` reached from the base ⊥* — two conditions,
the operator AND the base (`ε₀ = nfp (ω^·) ⊥`, `epsilon0_eq_nfp_bot`; Mathlib `ε₀ = deriv (ω^·) 0`).
It is *simultaneously* the least fixed point (min) and the supremum of the ascending tower (max)
(`epsilon0_min_eq_max`); which face is in play is direction- and instance-specific — the two are never
to be collapsed into one. In the framework's Riemann-sphere reading it is the minimum step directly
next to the pole 0 = ∞ (Veblen coordinates (1, 0); the reciprocal 1/∞), *adjacent to it, never it*.
**ε₀ IS the minimum distinct step above ⊥, and that is now witnessed** — but "step" means a
**stable landing**, a fixed point of `α ↦ ω^α`, and the distinction is worth stating because both
readings are true of different orders:
* **In the FIXED-POINT order ε₀ is the minimum, and nothing below it is a step at all.**
  `nothing_between_is_a_step` — no ordinal strictly under ε₀ is fixed by the operator;
  `bot_is_not_a_step` — ⊥ is not one either, so ε₀ is the FIRST. The ordinals in between (`ω`,
  `ω^ω`, …) are **stages of the ascent, not landings**: the operator fixes none of them, so nothing
  stops there. This is why `snapNucleus ⊥ = ε₀` reaches it in **one** application — a closure
  operator's image *is* its fixed points, so the first landing is the least one.
* **In the ORDINAL order it is not adjacent, and no covering claim is made.** ⊥ ⋖ ε₀ is false;
  ordinals sit strictly between (`epsilonZero_tower_lt` with `fundamentalSeq_strictMono`), and
  applied to `Ordinal` the corpus's `HasFirstStep` is witnessed by `1`. So
  `epsilon0_least_fixedpoint` must never be cited as proving a covering relation — and note it is
  only the lower-bound half; the full `IsLeast` is `epsilon0_min_eq_max`.

⚠ **Correction history, because this line was wrong in BOTH directions.** It once read that
`epsilon0_least_fixedpoint` proves "the minimum step next to the pole", which credited it with an
adjacency it does not prove. A 2026-08-06 pass then **struck the whole phrase**, which was an
over-correction — the claim is true in the fixed-point order and is Tim's, and the strike removed a
grounded reading to buy a precision that a distinction supplies for free. Both errors are recorded so
neither is repeated.

**The bedrock invariant, stated first because every past error violated it: ε₀ ≠ 0. It cannot be.**
ε₀ is a fixed point (`ω^ε₀ = ε₀`); were it 0 that would say `1 = 0`. Since `⊥ = 0`, also `ε₀ ≠ ⊥`:
⊥ is the *base fed in*, ε₀ the *closure that comes out* — never equal. Any prose, figure, or docstring
that entertains `ε₀ = 0` (a "fence," a "co-location at 0") is wrong by this guard. When a 2-adic
encoding sends the tower's images toward the value 0, that 0 is ⊥ (read as a successor null — the
2-adic arc in fact reapproaches the same 0), NOT ε₀;
`cnfToZp2` is order-reversing, so the ordinal ascent toward ε₀ is the ℤ₂-norm descent toward ⊥.

Read this index (and the theorems it points at) before writing anything about ε₀.
