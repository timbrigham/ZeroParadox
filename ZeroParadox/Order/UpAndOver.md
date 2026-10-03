# The up-and-over shape: prior art, controls and fences

Ride-along for `ZeroParadox/Order/UpAndOver.lean`. The Lean file holds the declarations, the Engineer's
Take and a `Statement:` per declaration; this file holds the standard framing and the fences.

## Standard framing

- UP is a **closure operator** (Mathlib `ClosureOperator`, `Mathlib/Order/Closure.lean`): monotone,
  inflationary, idempotent. Its closed points (`ClosureOperator.IsClosed`) are the landings. nLab,
  *closure operator*: "A closure operator is a monad on a poset".
- OVER is a **cover in the carrier order** (`CovBy`). Measured from a landing `y` read as the least
  element of its own up-set `Set.Ici y`, a cover of `y` is an atom of that up-set (Mathlib
  `covBy_iff_atom_Ici`).
- The corner law `UpAndOver.up_eq_of_mem_Icc` is a closure-operator fact, two lines from Mathlib
  `ClosureOperator.le_closure_iff`; the shape adds nothing to it.
- On the ordinals, UP-then-OVER iterated is **Veblen's derivative** of `ω^·` (Veblen 1908): Mathlib
  `Ordinal.deriv_add_one`, restated as `deriv_add_one_eq_up_succ`; the `ε`-indexed form is
  `succession_succ` (`ZeroParadox/Ordinal/SnapSuccession.lean`). Massmann and Kwon, *Extending the
  Veblen Function*, arXiv:2310.12832v2, Lemma 3.14, state the same recursion. Freund and Rathjen,
  *Derivatives of normal functions in reverse mathematics*, APAL 172(2) 2021, characterize the
  derivative as the initial upper derivative.
- The cells of the ordinal instance are already in the corpus and are pointed at, not re-proved:
  `nfp_seed_successor_cell` (Veblen 1908 Cor. 1 clause B) and `seed_eq_of_nfp_eq_epsilon_limit`
  (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`).
- `up` on the ordinals is `snapNucleus` (`ZeroParadox/Ordinal/SnapNucleus.lean`) through Mathlib's
  `Nucleus.toClosureOperator`. A nucleus is not required by the shape: meet preservation needs
  `SemilatticeInf`.
- Full search record: `.claude-local/notes/prior_art_atlas_core_2026-10-02.md` (private).

## Why each field is there

Each field is refused by a control in § III of the Lean file.

| field | control it refuses |
|---|---|
| `moves` | `ClosureOperator.id`; every closure on `Unit`; and it keeps `Empty` from passing vacuously |
| `two_landings` | a closure sending every point to `⊤` |
| `cover` | the ceiling map on ℝ, which passes the other three (`isEmpty_of_denselyOrdered`) |

`cover` is asked only at a landing that is not maximal. A closure operator always fixes `⊤`
(Mathlib `ClosureOperator.isClosed_top`), and `⊤` has no cover, so an unscoped field would refuse
every carrier with a top. The scope matches AX-B1's: a state with nothing above it owes no step
(`ZeroParadox/Order/SnapCannotBe.lean` § V).

## Fences

- SHAPE across carriers, never a cross-type identity. `UpAndOver α` is a structure on one carrier;
  two instances on different carriers share the fields, and no `=` between their points is stated.
- Limit rungs have no over leg: `limit_rung_no_over_leg`. The shape recurs at successor steps only.
- The ordinals' floor 0 is a landing's seed, not a landing: `bot_is_not_a_step`. The first landing
  is ε₀, and ε₀ ≠ 0 (`epsilon0_ne_zero`, `epsilon0_ne_bot`).
- A landing `ε_ o` plays the least-element role in `Set.Ici (ε_ o)` without being the ordinals'
  floor. That the next instance is new at the bottom is a commitment, never a theorem
  (`t_iz_limit_is_new_null` is the role half only).
- Not in this file: the atlas over charts, the `WithBot` Phase instance, carrier enrichment as an
  inverse system, and the universe climb.
