# A modality on a chain: the recognized structure, its scope, and what is owed outward

Argument, scope and credit for `ZeroParadox/Ordinal/SnapNucleus.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The recognized structure

A **nucleus** on a meet-semilattice is an inflationary, idempotent, meet-preserving endomap — the
point-free (locale-theoretic) form of a **Lawvere–Tierney topology** / a modality
(`Mathlib/Order/Nucleus.lean`; nLab: *nucleus*, *sublocale*). This is the object
`ZeroParadox/Category/DifferenceGeneratesSystem.lean` identifies with "a predicated difference
generates a system."

## The framework instance

The snap-step `α ↦ ω^α` is a normal ordinal operator (`isNormal_opow`). Its **next-fixed-point**
operator `Ordinal.nfp (α ↦ ω^α)` — "iterate the step from a seed until it settles" — is inflationary
(`Ordinal.le_nfp`), idempotent (`Ordinal.nfp_fp` at a normal `f`), and, because the ordinals are a
**linear order** (a chain), automatically **meet-preserving** (a monotone map on a chain sends `min` to
`min`).

All three nucleus conditions hold, so `snapNucleus : Nucleus Ordinal` is a genuine nucleus, and it sends
the ordinal bottom ⊥ to ε₀ (`epsilon0_eq_nfp_bot`). So the framework's own snap is a concrete instance of
the difference-generator: **⊥ the seed, the snap the modality, ε₀ the fixed point it generates.**

⚠ ⊥ is the *least* seed, not a distinguished one — every seed at or below the closure reaches the same
closure (`nfp_seed_independent_below_epsilon0`, `ZeroParadox/Ordinal/Epsilon0LeastFP.lean`). **The
modality carries the content, not the seed.**

This realizes, on the framework's own objects, the move from bottom as a noun (the floor) to bottom as a
verb (an action): the nucleus *is* that verb, ⊥ the noun it acts on, ε₀ what it produces.

## Honest scope — the frame versus the semilattice

A `Nucleus` requires only `SemilatticeInf` — which the ordinals have — so the individual snap-nucleus is
genuine on the bare ordinals, no top needed.

What the ordinals lack is a **top / frame** structure (they ascend without bound), and that is needed
only for the *lattice of all such nuclei* to itself be a locale — the "systems form a lattice"
meta-level. That missing top is not an absence but a **boundary of a higher type**: the point at infinity
the unbounded ascent manufactures, which by the self-dual pole (0 = ∞, `rInv_swaps`) is the next bottom.
Completing the meta-lattice by that boundary is a separate construction, not attempted here.

## Credit outward

`nfp`-as-closure/nucleus is textbook fixed-point theory (Knaster–Tarski / Kleene; nuclei = point-free
Lawvere–Tierney), which Mathlib happens not to package for `nfp`. The framework contribution is the
**instance** — its own ⊥ / snap / ε₀ triad exhibited as this modality — and the **placement** (seeded at
the self-dual pole), not a new theorem of the general theory.
