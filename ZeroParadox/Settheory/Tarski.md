# The liar as the exact negation of the closing self-reference

Argument, placement and attribution for `ZeroParadox/Settheory/Tarski.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The face

Tarski (1936): no consistent *internal* truth predicate. The Lean file names Tarski as a member of the
diagonal family whose engine is `ZeroParadox/Settheory/Wall.lean` (`negation_no_fixedpoint`,
`lawvere_fixedpoint`, `cantor_via_engine`). Tarski is the **TRUTH face**, the exact dual of Gödel's
**PROVABILITY face**: both diagonalize, but truth is undefinable (the T-schema at the liar is
inconsistent) where provability is merely incomplete.

## Placement on the wall

Tarski sits on the **μ / wall branch** — *negation has no fixed point* (`negation_no_fixedpoint`), so the
liar `p ↔ ¬p` has no truth value. It is the exact negation of the **ν / Quine floor** (⊥ = {⊥}, in the
ZF+AFA metatheory, where self-reference *does* close): the liar is where self-reference *cannot* close.
So Tarski is the wall-face and the Quine atom is the floor-face of the one diagonal.

## Honest delta

The engine is Lawvere (1969), via Yanofsky (2003) § 1 p. 1, and already in the repo; Cantor /
Russell / Turing are already named there. The new content is (a) exhibiting the **liar sentence
explicitly** from a truth-naming and (b) the **T-schema** absurdity — Tarski named and placed, completing
the diagonal-family roster on the truth axis. Every theorem reduces to the engine; no new axiomatic
content.
