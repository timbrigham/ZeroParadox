# Least fixed point as a signature, and two fences on the seed

Argument and fences for `ZeroParadox/Ordinal/Epsilon0MinMax.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## Why "both a minimum and a maximum" is a signature rather than a tension

"ε₀ is both a minimum and a maximum, depending on your point of view" is the defining signature of a
**least fixed point** (Knaster–Tarski / Kleene): the least fixed point of a monotone map reached from a
seed *is* the supremum of the ascending iterates. The Lean file bundles the two halves the framework
already proves, in two separate files, into one statement about the one object.

- **max reading:** ε₀ is the supremum of the ω-tower `ω, ω^ω, ω^(ω^ω), …` (`epsilonZero_eq_iSup`,
  `ZeroParadox/Ordinal/Gentzen.lean`).
- **min reading:** ε₀ is the least ordinal fixed by `α ↦ ω^α` (`epsilon0_least_fixedpoint`,
  `ZeroParadox/Ordinal/Epsilon0LeastFP.lean`).

Since `(⊥ : Ordinal) = 0` (`Ordinal.bot_eq_zero`), the seed of that tower is the ordinal bottom ⊥, so
the snap `⊥ → ε₀` reads literally as `⊥ → ⨆ₙ (ω^·)ⁿ(⊥)`: the floor ⊥ is the *seed* and ε₀ its *closure*
(`epsilon0_eq_nfp_bot`). This is a *placement* of ε₀ as the μ (least fixed point) of the ascent operator
seeded at ⊥ — a bundling of already-proved in-repo results and Mathlib's `nfp` theory, not a new
theorem, and it does not close the separate CNF/ℤ₂ value-bridge (`ZeroParadox/Ordinal/Gentzen.lean`,
item 4, open).

## Two fences on the "⊥ the seed" reading (Tim, 2026-07-31)

**Fence 1 — the seed is not load-bearing.** For a **normal** `F` — which `α ↦ ω^α` is — `nfp F` is the
least fixed point `≥` its seed, so every seed at or below the closure reaches the *same* closure:
`a ≤ nfp F 0 → nfp F a = nfp F 0`, by `le_antisymm` of two `Ordinal.nfp_le_fp` applications (which want
`Monotone F`), with `Ordinal.nfp_fp` (which wants `IsNormal F`) supplying the fixed point at each end.
**The normality hypothesis is load-bearing and the displayed implication is false without it.**
Elementary and not novel — `ZeroParadox/Order/LeastFixedPoint.lean`'s `isLeastFixedPointFrom_nfp` is the
seed-parametric statement, built from those same lemmas. So ⊥ is *a* seed, not a distinguished one:
`epsilon0_eq_nfp_bot` is true, and the emphasis "⊥ the seed" overstates ⊥'s role.

**Fence 2 — `α ↦ ω^α` does not fix ⊥.** Provable here: `ω ^ (0 : Ordinal) = 1 ≠ 0`, which is the
argument already inside `epsilon0_ne_zero`. Contrast `ZeroParadox/Computability/SelfApp.lean`, where
`fixed_bot : selfApp bot = bot` is a **class field** — an assumption, the shape CLAUDE.md's
commitments-in-hypotheses rule warns about. `Reading:` the snap is the action of an operator that moves
⊥ rather than one that fixes it.

**Scope, and it is narrow.** The `AbstractSelfApp` family rests on `fixed_bot`; the determinism family
does **not** — `machine_snap_impossible` is powered by single-valuedness
(`ZeroParadox/Computability/Occurrence.lean`), a separate obstruction, and attributing it to the fixed
point is the error CLAUDE.md's determinism section names. Already-proved neighbours, so neither fence is
new mathematics: `ZeroParadox/Ordinal/SnapNucleus.lean`'s `snapNucleus_bot_ne_bot` (*"it does not fix
the floor"* — in a file that imports the Lean file) and the choice-free
`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`'s `omegaPow_no_fixedpoint`.

Long form: `.claude-local/notes/future-research/tower_seed_is_not_load_bearing_2026-07-31.md`,
`.claude-local/notes/future-research/forced_movement_two_operators_2026-07-31.md`.
