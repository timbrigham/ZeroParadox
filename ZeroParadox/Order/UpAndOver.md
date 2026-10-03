# The up-and-over shape: prior art, controls and fences

Ride-along for `ZeroParadox/Order/UpAndOver.lean`. The Lean file holds the declarations, the Engineer's
Take and a `Statement:` per declaration; this file holds the standard framing and the fences.

## Standard framing

- UP is a **closure operator** (Mathlib `ClosureOperator`, `Mathlib/Order/Closure.lean`): monotone,
  inflationary, idempotent. Its closed points (`ClosureOperator.IsClosed`) are the landings. nLab,
  *closure operator*: "A closure operator is a monad on a poset".
- OVER is a **cover in the carrier order** (`CovBy`). Measured from a landing `y` read as the least
  element of its own up-set `Set.Ici y`, a cover of `y` is an atom of that up-set (Mathlib
  `covBy_iff_atom_Ici`). Read from above, the same cover `y ⋖ b` makes `y` a coatom of the down-set
  `Set.Iic b` (Mathlib `covBy_iff_coatom_Iic`). `Statement:` COINCIDENCE — the from-below and
  from-above readings hold of one cover at once, in two charts (the `example` in § II of the Lean file).
- The corner law `UpAndOver.up_eq_of_mem_Icc` is a closure-operator fact, two lines from Mathlib
  `ClosureOperator.le_closure_iff`; the shape adds nothing to it.
- On the ordinals, UP from 0 (Mathlib `Ordinal.deriv_zero_right`), then OVER-then-UP at each successor
  index, and the supremum of earlier values at limit indices (Mathlib `Ordinal.deriv_limit`), is
  **Veblen's derivative** of `ω^·` (Veblen 1908): Mathlib `Ordinal.deriv_add_one`, restated
  as `deriv_add_one_eq_up_succ`; the `ε`-indexed form is `succession_succ`
  (`ZeroParadox/Ordinal/SnapSuccession.lean`). Massmann and Kwon, *Extending the Veblen Function*,
  arXiv:2310.12832v2, Lemma 3.14 states the successor clause. Freund and Rathjen, *Derivatives of normal
  functions in reverse mathematics*, APAL 172(2) 2021, characterize the derivative of a normal
  (prae-)dilator as its initial upper derivative.
- The cells of the ordinal instance are already in the corpus and are pointed at, not re-proved:
  `nfp_seed_successor_cell` (Veblen 1908, Corollary 1 to Theorem 4, clause (B)) and
  `seed_eq_of_nfp_eq_epsilon_limit` (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`).
- `up` on the ordinals is `snapNucleus` (`ZeroParadox/Ordinal/SnapNucleus.lean`) through Mathlib's
  `Nucleus.toClosureOperator`. A nucleus is not required by the shape: meet preservation needs
  `SemilatticeInf`.

## Why each field is there

The fields are `up`, `corner` and `cover`. Each of `corner` and `cover` refuses a control in § III of
the Lean file that the other passes.

| field | controls it refuses |
|---|---|
| `corner` | `ClosureOperator.id`; `Unit`; `Empty`; a closure sending every point to `⊤`; two disjoint copies of `WithTop ℚ`, each sent to its own `⊤`; ℕ below `WithTop ℚ` with the `WithTop ℚ` part sent to its `⊤`, which passes `cover`; the ceiling map on ℝ |
| `cover` | the ceiling map on ℝ; `Fin 3 ⊕ ℚ` with `1` sent to `2`, which passes `corner` |

`corner` asks for a landing `y`, a cover `b` of `y`, and `up b ≠ b`: a place where OVER then UP moves.
It refuses the closure on ℕ below `WithTop ℚ`, which moves a point, has a non-maximal landing and a
cover at every non-maximal landing, while no OVER step is followed by a moving UP step. Some point moves (`UpAndOver.moves`, take `b`) and some
landing is not maximal (`UpAndOver.open_landing`, since `y ⋖ b`) are theorems. The cover in `corner`
refuses every densely ordered carrier (`isEmpty_of_denselyOrdered`), so the ceiling map on ℝ fails
`corner` as well as `cover`.

`cover` is asked only at a landing that is not maximal. A closure operator always fixes `⊤`
(Mathlib `ClosureOperator.isClosed_top`), and `⊤` has no cover, so an unscoped field would refuse
every carrier with a top. The scope matches AX-B1's: a state with nothing above it owes no step
(`ZeroParadox/Order/SnapCannotBe.lean` § V). On the two copies of `WithTop ℚ`, a densely ordered
carrier, every landing is maximal, so `cover` holds there vacuously and `corner` refuses it. Two
distinct landings follow from `corner` and `cover` (the `example` in § II).

## Fences

- SHAPE across carriers, never a cross-type identity. `UpAndOver α` is a structure on one carrier;
  two instances on different carriers share the fields, and no `=` between their points is stated.
- An over-then-up step from a rung `ε_ p` arrives at the successor rung `ε_ (succ p)` (`succession_succ`),
  never at a limit rung (`limit_rung_no_over_leg`); the cell of a limit rung is the rung alone
  (`seed_eq_of_nfp_eq_epsilon_limit`).
- The ordinals' least element 0 is not a landing: `bot_is_not_a_step` (0 is not a fixed point of
  `ω^·`). UP from 0 lands on ε₀ (`snapNucleus_bot`), and no fixed point of `ω^·` lies below ε₀
  (`nothing_between_is_a_step`); ε₀ ≠ 0 (`epsilon0_ne_zero`, `epsilon0_ne_bot`).
- A landing `ε_ o` plays the least-element role in `Set.Ici (ε_ o)` without being the ordinals'
  least element. In the ordinals the re-floored landing is a different point from every earlier
  floor (`succession_strictMono`, `Ordinal.epsilon_pos`); reading it as a NEW bottom in the
  snap-arc sense is C-DA2, a commitment, never a theorem (`t_iz_limit_is_new_null` is the role half
  only).
- Not in this file: the atlas over charts, the `WithBot` Phase instance, carrier enrichment as an
  inverse system, and the universe climb.
