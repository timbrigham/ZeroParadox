# What ε₀ is and is not: the long form of the ε₀ index

Long form of `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`.

## Formal Overview (AI-assisted)

**This is the ε₀-characterization object.** ε₀ is not a "large ordinal" chosen by fiat; it is the
*first (least) fixed point of the ω-tower operator `α ↦ ω^α` reached from the base ⊥ of `Ordinal`* — two conditions,
the operator AND the base (`ε₀ = nfp (ω^·) ⊥`, `epsilon0_eq_nfp_bot`; Mathlib `ε₀ = deriv (ω^·) 0`).
It is *simultaneously* the least fixed point (min) and the supremum of the ascending tower (max)
(`epsilon0_min_eq_max`); which face is in play is direction- and instance-specific — the two are never
to be collapsed into one.
**ε₀ IS the minimum distinct step above ⊥ of `Ordinal`, and that is witnessed** — but "step" means a
**stable landing**, a fixed point of `α ↦ ω^α`, and the distinction is worth stating because both
readings are true of different orders:
* **In the FIXED-POINT order ε₀ is the minimum, and nothing below it is a step at all.**
  `nothing_between_is_a_step` — no ordinal strictly under ε₀ is fixed by the operator;
  `bot_is_not_a_step` — ⊥ of `Ordinal` is not one either, so ε₀ is the FIRST. The ordinals in between (`ω`,
  `ω^ω`, …) are **stages of the ascent, not landings**: the operator fixes none of them, so nothing
  stops there. This is why `snapNucleus` reaches ε₀ from ⊥ of `Ordinal` (`snapNucleus_bot`) in **one** application — a closure
  operator's image *is* its fixed points, so the first landing is the least one.
* **In the ORDINAL order it is not adjacent, and no covering claim is made.** ⊥ ⋖ ε₀ is false;
  ordinals sit strictly between (`epsilonZero_tower_lt` with `fundamentalSeq_strictMono`), and
  applied to `Ordinal` the corpus's `HasFirstStep` is witnessed by `1`. So
  `epsilon0_least_fixedpoint` must never be cited as proving a covering relation — and note it is
  only the lower-bound half; the full `IsLeast` is `epsilon0_min_eq_max`.

**The bedrock invariant: ε₀ ≠ 0. It cannot be.**
ε₀ is a fixed point (`ω^ε₀ = ε₀`); were it 0 that would say `1 = 0`. Since ⊥ of `Ordinal` is 0, also
`ε₀ ≠ ⊥` there (`epsilon0_ne_bot`): that ⊥ is the *base fed in*, ε₀ the *closure that comes out* —
never equal. Any prose, figure, or docstring that entertains `ε₀ = 0` (a "fence," a "co-location at
0") is wrong by this guard. When `cnfToZp2` sends the tower's images toward the value 0, that 0 is
ℤ_[2]'s 0, least in ℤ_[2] read by its norm (read as a successor null — the 2-adic arc in fact
reapproaches the same 0), NOT ε₀. Along the tower, `cnfToZp2` agrees with ordinal order in the 2-adic
valuation (`tower_orders_agree`; at the seed only by Mathlib's `valuation 0 = 0`) and reverses it in
the norm from stage 1 on, so from stage 1 the ordinal ascent toward ε₀ is the descent of the images'
norm toward ℤ_[2]'s 0. At the seed the norm rises from 0 at stage 0 (`snap_arc_z2_loop`;
both directions are `example`s in § V of the Lean file).

Read `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` (and the theorems it points at) before writing
anything about ε₀.
