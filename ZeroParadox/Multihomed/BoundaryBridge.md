# Which theorem carries which direction, and the survey's limits

Citations and scope for `ZeroParadox/Multihomed/BoundaryBridge.lean`. The Lean file holds the
declaration, the Engineer's Take and the per-declaration commentary.

## Registers

The snap ⊥→ε₀ as the crossing of the well-foundedness boundary, in two registers —
`ZeroParadox/Multihomed/Boundary.lean` (`snap_crossing`) and `ZeroParadox/Settheory/Coalgebra.lean`
(`categorical_fork_strict`) — bundled by `snap_boundary_two_registers`.

## NOT the full Taylor statement

The General Recursion Theorem is the ⇒ direction alone — every
well-founded coalgebra is recursive (Adámek–Milius–Moss 2020, arXiv:1910.09401v2, Thm 7.2 p. 27). The
converse is their § 8. It always asks the endofunctor to preserve inverse images, then takes one of
three routes: universally smooth monos with a pre-fixed point (Thm 8.1, p. 32), a subobject
classifier (Thm 8.6, Taylor's, p. 34), or functors on vector spaces, which have neither (Thm 8.12,
p. 36). Under Thm 8.1's assumptions the equivalence including the initial-algebra leg is Cor 8.2
(p. 32). Taylor states necessity in a topos (Prop 111, p. 6).

## The survey's limits

The Mathlib negatives in the Lean header were measured on 2026-08-12 against the pinned Mathlib, by
an environment sweep over declaration names and declaration types, and are stated as "not located",
never as absent. A type sweep matches only declarations whose type mentions the named constant, so
an operator stated over a bare structure map would be invisible to it; the next-time operator's
negative also rested on name sweeps, and that operator has since been built in this repository
(`ZeroParadox/Category/NextTimeCategorical.lean`, `nextTimeCat`). For Pataraia's theorem the nearest
Mathlib result was Bourbaki–Witt; the classical route from it, and where the choice-free proofs are
formalized, is in `ZeroParadox/Order/PataraiaFromBourbakiWitt.md`.
