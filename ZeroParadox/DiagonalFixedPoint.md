# The μ/ν split, the host verdict, and what this index does not claim

Argument and fences for `ZeroParadox/DiagonalFixedPoint.lean`. The Lean file is `#check`-only: it holds
the routing lines and their labelled glosses, and creates no declarations.

## What the index is

⊥ (the bottom), the snap, and ε₀ each have a `#check`-only object (`ZeroParadox/BottomCannotBe.lean`,
`ZeroParadox/Order/SnapCannotBe.lean`, `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`). Those are the three
core *objects*; the keystone index is the front door to the *phenomenon* they share a shape with —
**self-reference**, the diagonal fixed point on which the whole framework rests. Self-reference
otherwise lives one-face-per-domain with no direct route in. This is that route.

Like the three object indexes, it states no new results and reproduces no logic: every line `#check`s an
already-proven theorem in its home file, so the `import`s recompile those files and the index cannot
point at a dead or renamed result. A `#check`-only index creates no declarations and so *structurally
cannot overclaim* — of the declarations. The `--` glosses beside them are ordinary prose and can, which
is why each carries a `Statement:` or `Reading:` label.

## The split — the μ/ν fork

Self-reference runs off one **engine** — Lawvere's fixed-point construction — and forks in two:

- **Wall faces (μ) — self-reference CANNOT close.** No fixed point exists; the reflexive object is
  impossible. The classical negative diagonal arguments: Cantor, Russell, Turing, Tarski, Curry.
- **Floor faces (ν) — self-reference CLOSES, and the fixed point lands at ⊥.** The fixed point is
  genuinely produced and it is the bottom: the Quine atom, the Kleene quine, Löb / Gödel's second, Rice.

This mirrors the ZP-R Diagonal Family Addendum exactly. As with the bottom family (MC-1), the roster is a
matrix of domain cells; the cells present are the ones currently formalized, and other domains' cells
remain to be filled in over time — the same open-cell structure the framework carries elsewhere.

## The fence — built in, load-bearing

Each face is a proven theorem; the index only *routes* them. That the faces are **one** self-reference is
**Lawvere (1969) / Yanofsky (2003)** — cited prior art, a recognized connection, NOT a Zero Paradox
theorem. The cross-face identity across domains stays a **type boundary**, never a Lean `=`. So this is a
machine-checked *view* over the existing diagonal family, not a new synthesis claim.

## Scope note — `wf_no_selfloop` is not a μ engine face

It sits in the wall section, and conflating it with the engine faces was a live contradiction in this
corpus. The engine faces have a fixed-point-free map (negation), so *no object forms anywhere*.
`wf_no_selfloop` says something different: it is a **verdict a HOST renders on the engine's ν output**.
A well-founded host refuses the self-loop (`no_quine_atom`), while a host that carries it is thereby not
well-founded (`quineHost_not_wellFounded`, `floor_not_wellFounded`, both in the ν family). Same theorem,
two hosts.

It is kept in the wall section because the *signature* is a refusal, but do not read it as "no fixed
point exists" — the object exists and is refused, which is the ν object seen from a well-founded host.

Standard framing: Aczel 1988 p. 6 (Foundation vs Anti-Foundation); Adámek–Milius–Moss 2020 Thm 7.6
(*"the only well-founded fixed point is the initial algebra"*). **Well-foundedness is not a second root
of self-reference; it is the axis on which the host renders its verdict on the fixed point the one
engine produces.**
