# SnapSuccession — the ε-numbers as the snap's successive targets

Ride-along companion to `ZeroParadox/Ordinal/SnapSuccession.lean`.

`ZeroParadox/Ordinal/SnapNucleus.lean` builds the snap as a modality `snapNucleus : Nucleus Ordinal`
sending ⊥ to ε₀. The snap does not stop there: it re-seeds above where it landed and runs again.
That file makes the succession precise.

## The rungs are targets, never ⊥

**Read this distinction before anything else; an earlier draft of the header got it wrong.** The
ε-numbers are the ordinals the snap runs **to** — its successive closed points, the targets. They
are **not** ⊥. `ε₀ ≠ ⊥` is a bedrock invariant (`epsilon0_ne_bot`): ⊥ is the base fed in, ε₀ the
closure that comes out, and **the base is never its own closure**.

**The standard term for a rung is an ITERATIVE BOTTOM** (ratified 2026-07-19). Each rung serves as
the base the *next* iteration re-seeds above — a bottom relative to its iteration, never ⊥ itself.
The qualifier is load-bearing: "iterative bottom" names the role, where the bare noun would assert
the identity.

⚠ Do **not** call these "local bottoms". That phrase is already in use for the *per-domain* MC-1
family (`ZeroParadox/Category/GlobalZero.lean`) and would collapse family-versus-succession; it also
collides with the locale vocabulary this file's neighbours use.

This is the role/identity distinction, the same shape as the family-versus-instance reading: the
rungs are all *of the same kind*, and they are *provably distinct* members (`succession_lt_succ`), so
no two of them — and none of them and ⊥ — may be identified.

## The other succession, and why the two readings must not merge

The bottom the snap-arc returns to is a `ZPSemilattice` fact, not a fact about an ordinal ε-number.
⚠ And `t_iz_limit_is_new_null` gives the **ROLE half only** — anything satisfying the join-identity
IS that lattice's bottom, the one already present. Reading that occupant as a **NEW** bottom is
**C-DA2, a commitment**, and `Order/SnapCannotBe.lean:43` forbids citing that theorem as a novelty
witness. Do not merge the two readings.

## Why re-seeding, not iteration

A nucleus is a **closure** — idempotent — so iterating `snapNucleus` alone does nothing; it has
already run to completion. The succession comes instead from **re-seeding one step above the current
target**: the next target is the snap applied just above the last. That operation is exactly
Mathlib's fixed-point enumerator, `ε_ = Ordinal.epsilon = deriv (α ↦ ω^α)`, whose successor step is
`ε_ (succ o) = nfp (ω^·) (succ (ε_ o))` (`epsilon_succ_eq_nfp`) — "snap from just past the current
rung."

So the succession of snap targets is the **ε-hierarchy** `ε₀ < ε₁ < ε₂ < …`, and:

- its rungs are exactly the **closed points** of `snapNucleus` (the fixed points of the snap-step) —
  `snapNucleus_isClosed_iff`;
- it climbs **strictly** — each target is genuinely above the last (`succession_lt_succ`), never the
  same one;
- its first rung is ε₀ (`succession_zero`) — the target of the snap seeded at ⊥, not a bottom itself.

This is Tim's "when one instance ends, another begins" as a strictly increasing chain of closed
points.

## Scope — what is here and what is deferred

This file formalizes the succession as a strict chain of closed points. The stronger claim that
successive instances are *orthogonal* — the "orthogonal tangent", that the next rung is transverse to
the old rather than merely above it — needs a transversality/complementation statement in the coframe
of sublocales that is not attempted here. It is the open next step.

Everything in the file is a strict-chain fact, cited to Mathlib's `deriv`/`epsilon` theory (the
ε-numbers are Cantor/Veblen, recognized). The framework contribution is the **reading** of the chain
as the snap's succession of targets, each re-seeding the next.
