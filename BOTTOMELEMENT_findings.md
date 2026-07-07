# The Bottom Element (⊥) — Structural Findings

*Companion to [The Bottom Element (⊥) — Dictionary and Map](BOTTOMELEMENT.md). That page is the chart; this
page is the **why** behind two of its columns — `GEN` and `dynamics`. Every theorem named here is linked to
its Lean source from the map's dictionary.*

The bottom-element matrix sorts each ⊥-construction (p-adic floor, Kleene quine, ε₀ tower, the categorical
zero object, …) against a set of **aspects** (kinds of ⊥-fact). Two of those aspects — generation and
dynamics — turned out not to be independent slots but two readings of a single structural axis: the
**μ / ν polarity** of the bottom. This page states what that means and why the columns look the way they do.

---

## μ and ν — the one axis behind two columns

Every fixed point of a construction sits on a fork:

- **μ** — the *least* fixed point, built **up from** ⊥ (the initial object / colimit / generation side).
- **ν** — the *greatest* fixed point, closed **down to** ⊥ (the terminal object / limit / attractor side).

A construction's bottom is a **source** (μ), a **sink** (ν), or — where the two coincide — a **seam**
(μ = ν). This single polarity is what the `GEN` and `dynamics` columns each measure, from two angles.

---

## Finding 1 — GEN is the μ face (generation by iteration)

`GEN` asks: does ⊥ **generate** the structure above it? The precise content is the least-fixed-point-by-
iteration schema

> `lfp F = ⊔ₙ Fⁿ(⊥)` — iterate the operator `F` from the floor and take the supremum.

That schema is **Kleene's fixed-point theorem**, the founding construction of computability / domain theory.
It is realized in the matrix at three levels:

- **Order-theoretic** (the abstract engine): `lfp F = ⊔ₙ Fⁿ(⊥)` for a monotone `F` — this is a standard
  library result (Mathlib's `fixedPoints.lfp_eq_sSup_iterate`), cited, not rebuilt.
- **Ordinal** (the headline instance): `ε₀ = nfp(ω^·)(0) = ⊔ₙ (ω^·)ⁿ(0)` (`epsilonZero_eq_nfp`) — the floor
  `0` generates the ceiling `ε₀` by iterating ordinal exponentiation.
- **Categorical** (Adámek): the initial algebra is the colimit of the initial chain `0 → F0 → F²0 → …`.
  This is the one form not carried by Mathlib; the matrix now builds a concrete instance,
  `node4_generates_nat` — **ℕ is the colimit of the successor chain `Fin 0 → Fin 1 → Fin 2 → …`** rooted at
  the empty type `Fin 0` (node #4's Kleisli floor), i.e. the initial algebra of `X ↦ X + 1`. Choice-free.

**Why `GEN` is filled only at ε₀ (and now node #4), not everywhere.** Generation is a **μ** property. The
`ν`-bottoms — the p-adic inverse limit, the Markov attractor, the topological `{0}`-limit — are the *opposite*
pole: they are *reached*, they do not *generate*. Asking them for `GEN` is asking a ν-object for a μ-property,
so those cells are structural non-applicabilities (`∅`), not gaps. And the *self-coincident* fixed points
(the Kleene quine, the abstract `selfApp`) are their **own** fixed point — the floor **is** the fixed point,
so there is no distinct ceiling to generate; they carry `SELF` / `CONC` (the still point), not `GEN`. So `GEN`
is genuinely a μ-only column, and its emptiness elsewhere is the μ/ν fork showing through, not missing work.

*(That the categorical Adámek `GEN` and the computational Kleene fixed point are "the same construction in two
languages" is a recognized connection — Kleene's recursion theorem and the ordinal `ε₀ = nfp` sit on parallel
axiom footprints — but the matrix states it as a connection, not a proved cross-domain identity.)*

---

## Finding 2 — dynamics is single-directional, set by μ/ν

The matrix's `dynamics` column has **two sub-senses**, drawn as one directional symbol:

- **↓ inbound** — orbits converge **to** ⊥ (an attractor). ⊥ is a **sink** (ν).
- **↑ outbound** — structure departs **from** ⊥ irreversibly (the snap). ⊥ is a **source** (μ).
- **↕ both** — ⊥ is a **seam** (μ = ν): things flow both in and out.

**The claim: a non-seam ⊥ has exactly one direction.** ⊥ cannot be both a pure source and a pure sink, so its
arrow of time points one way, fixed by its μ/ν polarity; both directions coincide only at a seam. Reading each
dynamics witness for what it actually asserts confirms this:

| construction | ⊥ nature | witness (what it says) | direction |
|---|---|---|---|
| Lat ⊥, #4 Kleisli, Info | source (μ / initial) | `t_snap_derived`, `fC_no_return` — departs / no return | **↑ outbound** |
| p-adic, Markov, #3 TopCat | sink (ν / limit / attractor) | `contraction_orbit_tendsto_zero`, `doubly_stochastic_mean_ergodic` — converge in | **↓ inbound** |
| #5 Hilbert (zero object) | **seam** (μ = ν) | terminal (`seam_has_Pin`, maps in) **and** initial (maps out) | **↕ both** |

**The correction the claim forced.** Two constructions — p-adic and Markov — *looked* like they had both
directions, because two "irreversibility" theorems sat in the outbound column that don't belong there:

- `c3_irreversible` ("no continuous path *to* 0") is about the **arrival** at ⊥ being a discontinuous jump —
  an **inbound** fact, not a departure.
- `fullMix_not_injective` (the mixing *toward* the stationary state loses information) is the **inbound**
  convergence being irreversible — again inbound, not outbound.

Reading them correctly re-sorts both to `↓`, and p-adic and Markov become cleanly inbound-only: pure sinks. So
`↕` is a **seam diagnostic** — the only genuine `↕` is the Hilbert zero object. (ε₀ also shows `↕`, but for a
different reason: its row *is* the transition arc `0 → ε₀`, spanning a floor and a ceiling, not a single
seam.) The reach-in / can't-return-out asymmetry between the two sub-senses is exactly the arrow of time.

---

## Why the cell vocabulary is five states, not a checkmark

A relationship between a construction and an aspect is a **claim with a status**, not a yes/no box. A blank
would conflate three completely different situations — an open question, a settled structural non-applicability,
and a proved impossibility — so the matrix distinguishes them:

- **✓ established** — a sorry-free Lean witness.
- **✓\* conditional** — holds under a modelling commitment / bridge, or is cited from a library.
- **✗ refuted** — a *proved obstruction*; the aspect provably fails here (the matrix's news).
- **∅ n/a — structural** — a category error (a ν-object asked for a μ-property; a bare order asked for a
  metric): not a gap.
- **? open probe** — genuinely unknown, worth pursuing.

The value of the matrix is in the non-`✓` cells — the questions (`?`) and the news (`✗`) — **not** the filled
count. Filling cells for their own sake is the failure mode the design guards against.
