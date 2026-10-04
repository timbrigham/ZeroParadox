# Incompleteness — ride-along documentation

Moved from `ZeroParadox/Ordinal/Incompleteness.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** It has since carried corrective edits, but its claims are unverified until a claim review says otherwise.

## § I. The snapEmbed Morphism

snapEmbed sends the snap state c₁ to 0 in ℤ_[2] (the 2-adic limit of the tower
encodings) and the pre-snap state c₀ to 1 (a nonzero 2-adic integer).

This formalizes the embedding: c₁ maps to 0 ∈ ℤ_[2], the 2-adic limit of the tower
encodings. Within the ZP framework, 0 here plays the role of ⊥; in the Scale.lean chart (⊥ = 0)
0 fills ℤ_[2]'s bottom role (a ZPSemilattice on ℤ_[2] with ⊥ = 0 is built in
`ZeroParadox/Valuation/Scale.lean` § V), and in the multiplicative reading `snapEmbed c₀ = 1` is
the identity, and that reading is not a ZPSemilattice, since multiplication on ℤ_[2] is not idempotent (2 · 2 ≠ 2) — the identification is a modelling commitment, not a
ring-theoretic fact.

The morphism property: join on MachinePhase (c₁ is absorbing) corresponds to
multiplication on ℤ_[2] (0 is absorbing). Both structures have the same absorbing
element pattern: c₁ absorbs all joins, 0 absorbs all products.

## Remark R-M.1: DA-1 Path 2 and the Limits of the Diagonalization Frame

`both_fixed_points_exist` shows that Kleene diagonalization (a code acting on its own
Gödel number) and ordinal diagonalization (ε₀ = ω^ε₀, least fixed point) each produce a
fixed point in their own domain. The statement is a conjunction of two existentials, so
it establishes that both exist, not that they are one structural pattern; reading them as
the same pattern is the framework's interpretation, and no equation between a `Code` and
an `Ordinal` is well-formed.

L-INF (ZP-C Lemma L-INF: the surprisal of ⊥ is unbounded above) is structurally
analogous. The Kleene and
ordinal cases are both textbook instances of the diagonalization schema; whether
L-INF fits the same schema formally is the open question this remark is tracking.

The formally unconnected instance is L-INF. L-INF is a measure-theoretic statement
(surprisal under a probability measure on ZP-B's binary space), while the Kleene quine is
a computability-theoretic statement (partial recursive functions, Gödel encoding), and
neither this remark nor `both_fixed_points_exist` links them. ZP-C keeps the surprisal measure and
Kolmogorov complexity as independent routes (ZP-C Remark R-BRIDGE). Kolmogorov complexity
itself was not located as a definition in `ZeroParadox/**/*.lean` as of 2026-10-04 (searched
for declarations named for Kolmogorov, prefix or description-length complexity, and for
"incompressib"); `ZPSurprisal` in `ZeroParadox/Category/Category.lean` abstracts only its
skeleton.

DA-1 Path 2 is a different matter. In ZP-E (DA-1 insert § IV) it is the step from
unbounded surprisal to executing: a bridge principle of its own, a missing principle and not
a missing proof, which the framework does not adopt and which is not the occurrence
commitment.
