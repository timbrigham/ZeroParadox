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
converse is their § 8, needing inverse-image preservation plus either a subobject classifier (Thm 8.6)
or universally smooth monos and a pre-fixed point (Thm 8.1); the equivalence including the
initial-algebra leg is Cor 8.2. Taylor states necessity in a topos (Prop 111, p. 6).

Detail, sources and the survey's limits: `.claude-local/notes/boundarybridge_scope_2026-08-12.md`.
