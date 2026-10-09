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
the unbounded ascent manufactures. `Reading:` **INVERSION** — the framework reads that boundary as the
next bottom, by the antipodal exchange `rInv_swaps` fixes between the zero and infinity poles. ⚠ That
is a CHART claim about two measurements of one object, never a point identity: in that carrier `some 0`
and `∞` are provably distinct, which is what makes the swap non-trivial.
Completing the meta-lattice by that boundary is a separate construction, not attempted here.

## Axiom footprint

`snapNucleus` and the results about it are STATEMENT-CARRIED (`ZeroParadox/Category/ChoiceCannotBe.md`):
each statement, only assumed, already reports `Classical.choice` (statement control, measured 2026-10-08).
The choice is **not** in the `Ordinal` type — `#print axioms Ordinal` reports `[propext, Quot.sound]`. It
enters through the *order instance and the operations*: `Ordinal.instLinearOrder`, `Ordinal.nfp`,
`Ordinal.omega0` and `Ordinal.epsilon` each measure `[propext, Classical.choice, Quot.sound]`, and
`snapNucleus` is built from `nfp` over `omega0 ^ ·` on that order.

The open question is a restatement on a carrier whose statements are choice-free. Its state, part by
part (measured 2026-10-08):

* **The ascent below ε₀ is restated, choice-free.** On `ONote`, ZP-N proves the ascent (`exp_lt_term`,
  `omegaPow_no_fixedpoint`, `tower_strictMono`, the counterpart of `fundamentalSeq_strictMono`), and
  `synCollapse_epsN` (`ZeroParadox/Ordinal/SyntacticCollapse.md`) restates the tower's convergence
  content. The statement and the proof of `tower_strictMono` and of `synCollapse_epsN` each measure
  `[propext]`. That is the ascent, not the nucleus.
* **The results that name ε₀ cannot be stated on `ONote`.**
  `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` shows the natural counterpart route there is
  **blocked** (`no_snap_closure`: no idempotent endomap of the notation carrier has the ε-numbers as
  closed points), and that obstruction is about **expressive reach, not choice** (its own proofs are
  `[propext]`). It concerns `ONote` only and says nothing about a carrier that reaches ε₀. One such
  carrier is constructive and outside Lean: Kraus, Nordvall Forsberg and Xu (MFCS 2021,
  arXiv:2104.02549) build Brouwer trees with exponentiation at every base (Thm 18), and their cubical
  Agda development defines ε₀ as the limit of the ω-tower and proves ε₀ = ω^ε₀; every Cantor normal
  form lies below it (Thm 22). A lemma that ε₀ is the *least* fixed point of `ω^·` was not located
  there as of 2026-10-08 (searched: the paper, and the Agda module
  `BrouwerTree.Arithmetic.Properties`).
* **Open: a choice-free restatement in Lean of the results that name ε₀, leastness included.** None
  located as of 2026-10-08, searched in this corpus, by three `theoremsearch` phrasings and by one web
  search.

## Credit outward

`nfp`-as-closure/nucleus is textbook fixed-point theory (Knaster–Tarski / Kleene; nuclei = point-free
Lawvere–Tierney), which Mathlib happens not to package for `nfp`. The framework contribution is the
**instance** — its own ⊥ / snap / ε₀ triad exhibited as this modality — and the **placement** (seeded at
the self-dual pole), not a new theorem of the general theory.
