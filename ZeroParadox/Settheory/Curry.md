# Why unrestricted comprehension yields every conclusion, and its floor dual

Argument, placement and attribution for `ZeroParadox/Settheory/Curry.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The face

Curry's paradox: a self-referential proposition `p ↔ (p → C)` proves `C` — for *any* `C`. This is the
diagonal family's **explosion face**: where the liar (`negation_no_fixedpoint`,
`ZeroParadox/Settheory/Wall.lean`) yields a contradiction, Curry yields *anything at all*, and it needs
no negation — only implication and self-reference.

## Relation to the engine

The liar is exactly Curry at `C = False` (`Not p` is `p → False`), so `curry_paradox` is a strict
**generalization** of `negation_no_fixedpoint` — genuinely new content on top of the existing engine,
not a re-pointing. Via the Lawvere naming (`lawvere_fixedpoint` / `cantor_via_engine`), a
point-surjective internal comprehension proves every `C` — the sharpest statement of why unrestricted
comprehension / a reflexive object is inconsistent (the type-level cousin is `reflexive_object_refuted`).

## Placement

Curry is a **wall / μ** face — self-reference that cannot be internalized — and the most violent form:
not "no truth value" but "every value at once". Its floor dual (ν) is the Quine-atom role in the
die, `SelfOnlyAt`, a point stepping to itself and to nothing else: occupied in the coalgebra chart
(`cofix_quine_role_occupied`, `ZeroParadox/Settheory/Coalgebra.lean`), where self-reference closes
without exploding, and unoccupied in `ZFSet` (`zfset_quine_role_unoccupied`,
`ZeroParadox/Settheory/Wall.lean`).

## Honest delta

`curry_paradox` is a real generalization of the repo's engine (arbitrary conclusion `C`);
`curry_from_naming` routes it through the existing Lawvere naming. Attribution: conventionally credited to Curry (1942; not consulted here). In the
diagonal family, Yanofsky (2003, arXiv:math/0305282v1, p. 18) applies the diagonalization lemma to get,
for an arbitrary sentence A, a sentence C with ⊢ C ↔ (C ⇒ A); with his C read as `p` and his A as
`C`, that has the shape of `curry_paradox`'s hypothesis `p ↔ (p → C)`, and he derives A from it. He names it "Löb's Paradox" and remarks that it
"is related to Curry's paradox", the only mention of Curry in that copy (text search, 2026-11-01).
Lawvere (1969) treats Cantor, Russell, Tarski and an incompleteness theorem; Curry was not located in our
copy of his paper (text search of the TAC reprint, 2026-11-01). Axiom-free.
