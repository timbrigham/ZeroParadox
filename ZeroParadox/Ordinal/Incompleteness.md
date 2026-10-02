# Incompleteness — ride-along documentation

Moved from `ZeroParadox/Ordinal/Incompleteness.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## § I. The snapEmbed Morphism

snapEmbed sends the snap state c₁ to 0 in ℤ_[2] (the 2-adic limit of the tower
encodings) and the pre-snap state c₀ to 1 (a nonzero 2-adic integer).

This formalizes the embedding: c₁ maps to 0 ∈ ℤ_[2], the 2-adic limit of the tower
encodings. Within the ZP framework, 0 here plays the role of ⊥; in the ZP-B chart 0 fills
ℤ_[2]'s bottom role (a ZPSemilattice on ℤ_[2] with ⊥ = 0 is built in
`ZeroParadox/Valuation/Scale.lean` § V) — the identification is a modelling commitment, not a
ring-theoretic fact.

The morphism property: join on MachinePhase (c₁ is absorbing) corresponds to
multiplication on ℤ_[2] (0 is absorbing). Both structures have the same absorbing
element pattern: c₁ absorbs all joins, 0 absorbs all products.
