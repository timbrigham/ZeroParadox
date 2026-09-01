# The schema, its three faces, and why the seed is a role rather than an origin

Argument, fences and prior art for `ZeroParadox/Order/LeastFixedPoint.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## What is abstracted

The *μ construction* the framework keeps re-instantiating: **the least fixed point of a
monotone/progressive operator, reached from a seed ⊥, is the closure of the ascending iterates.**
`AbstractSelfApp` (`ZeroParadox/Computability/SelfApp.lean`) captured the *floor* face — the unique
fixed point *is* the bottom. This captures the *ceiling / ascent* face — the least fixed point *above*
the seed — as one order-generic schema, and places the framework's recurring μ-instances against it.

## The schema

`IsLeastFixedPointFrom r f seed mu` (a `Prop` predicate, deliberately NOT a typeclass — see the fence)
says: with respect to a relation `r`, `mu` is a fixed point of `f` that is the **least** fixed point at
or above `seed`. This is the Knaster–Tarski / μ-calculus characterization of a least fixed point (the
least *pre*fixed point), stated over a bare relation so it applies across the framework's distinct
carriers (Ordinal, the ZP semilattice `L`) rather than one lattice. The "closure = supremum of the
ascending iterates" content (the Kleene construction of that μ) is exposed per-face where it holds — for
ε₀ via `nfp` — since the supremum lives in a different type for each face.

## The faces

- **ε₀ face** (`epsilon0_isLeastFixedPointFrom`): ε₀ is the least fixed point of `α ↦ ω^α` from the
  ordinal bottom ⊥. Reuses the in-repo results `epsilonZero_fixedPoint`, `epsilonZero_le_fixedPoint`
  (`ZeroParadox/Ordinal/Gentzen.lean`) and `epsilon0_eq_nfp_bot`
  (`ZeroParadox/Ordinal/Epsilon0MinMax.lean`); nothing reproved. This is the genuine ascent μ
  (seed ⊥ ≠ closure ε₀).
- **Self-reference face** (`selfApp_isLeastFixedPointFrom`): ⊥ is the least fixed point of `selfApp`
  from the seed ⊥. Here seed = closure = ⊥: the μ construction collapses onto the seed. This is the
  degenerate/floor μ — the Gödel-inversion content that self-reference sits *at* the floor.
- **Kleene face** (FENCED — `kleene_fixed_point_from_exists`): Rogers'/Kleene's recursion fixed point on
  `Code`. Same *shape* (a self-map has a fixed point), different *setting*: `Code` carries no
  complete-lattice order for `lfp`, its fixed points are NOT unique (`infinite_quine_family`), and there
  is no seed→closure ascent. It cannot form an `IsLeastFixedPointFrom`; recorded as an existence
  statement with the fence.

## The honest fence — no cross-face identity is claimed

The faces share the μ-**shape**, not one object. Their carriers — `Ordinal`, the semilattice `L`, `Code`
— are distinct types, so `x = y` across them is not a well-formed proposition: a **type boundary**,
exactly the ZP-P / MC-1 "retired as ill-typed" fence. `IsLeastFixedPointFrom` is a **placement /
schema**, NOT a proved cross-domain unification. `IsLeastFixedPointFrom.unique` shows the schema pins a
unique object *within one carrier* (given antisymmetry); it says nothing across carriers. The grounding
`lfp_isLeastFixedPointFrom` shows the schema *is* Mathlib's `OrderHom.lfp` (Knaster–Tarski least fixed
point) on a complete lattice — the schema is recognized order theory, not ZP-invented structure.

## The ε₀ face — the ascent is genuine; the seed is not distinguished

⚠ *"Seed ⊥ ≠ closure ε₀"* is true and is what separates this face from the degenerate one. It does
**not** mean ⊥ is a privileged starting point: `nfp_seed_independent_below_epsilon0`
(`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) proves `∀ a ≤ ε₀, nfp (ω^·) a = ε₀`, with
`nfp_seed_one_eq_seed_bot` as the concrete witness.

⚠ **Scope: at or below ε₀ only.** The general fact is that `nfp (ω^·) a` is the **least ε-number `≥ a`**
— e.g. `nfp (ω^·) (succ ε₀) = ε₁` (Mathlib `epsilon_succ_eq_nfp`). ⚠ Above ε₀ the answer **is** the seed
at every ε-number, so no fixed point can distinguish *least-ε-number-≥-`a`* from the false *"the seed
does all the work"*; use a non-fixed point such as `succ ε₀`. ⚠ **Normality is load-bearing.**

**Provenance:** stated in prose, with this conclusion and this proof route, at
`ZeroParadox/Ordinal/Epsilon0MinMax.md` (**Tim, 2026-07-31**), which claims no novelty for it; the
declarations only make it checkable. ⚠ The routes differ in detail: that argument goes by `le_antisymm`
of two `Ordinal.nfp_le_fp` applications, where the schema section abstracts the seed. **And the corpus's
own seed-parametric general statement is one section up:** `isLeastFixedPointFrom_nfp` — with
`IsLeastFixedPointFrom.unique` the ε₀ result is its instantiation, needing no separate proof idea.

The classical form is Veblen 1908 — **Corollary 1 clause (A)** (*"`f'(1)` is the least upper bound of
`f(1), f[f(1)], ⋯`"*) is the **seed-`1`** case — Veblen indexes from 1, so seed `0` lies outside his
range and Mathlib's `epsilon_zero_eq_nfp` is its home — **Corollary 1 clause (B)** the
between-consecutive-rungs case, and **Corollary 4** names the ω-power instance (*"the first derived
function of ωˣ is the function ε"*); the underlying properties are credited by Veblen to Cantor. See
`ZeroParadox/Ordinal/Epsilon0LeastFP.lean` for the full quotation of Corollary 1 and the residual delta
against it. Mathlib carries the same shape for `+` and `*` (`Ordinal.nfp_add_eq_mul_omega0`,
`Ordinal.nfp_mul_eq_opow_omega0`), the seed-ranged ω-power entry being the one not located in the pin.

`Reading:` **INVARIANT** (conjectural) — read the seed as a **role**, not an origin: the ratified
*"iterative bottoms"* picture, in which the rungs are bottoms relative to their iteration and **never ⊥
itself**. The same **shape** is a theorem in another carrier: `every_node_is_a_floor`
(`ZeroParadox/Valuation/LocalFloor.lean`).

⚠ **SHAPE, never instance-of** — different carriers, different mechanisms, and different conclusions.
⚠ `ε₀ ≠ ⊥` is untouched bedrock (`epsilon0_ne_bot`); nothing here identifies a rung with ⊥. ⚠ The
ratified term for the iteration sense is **iterative bottom**; do not substitute "local bottom" *there*
— that phrase is taken for the per-domain MC-1 family (`ZeroParadox/Category/GlobalZero.lean`).
(`ZeroParadox/Valuation/LocalFloor.lean` uses it for a third, subtree-local sense; that is that file's
own usage and not what the iteration rule governs.)
