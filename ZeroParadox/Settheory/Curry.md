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
not "no truth value" but "every value at once". Its floor dual is again the Quine atom (ν), where
self-reference closes harmlessly instead of exploding.

## Honest delta

`curry_paradox` is a real generalization of the repo's engine (arbitrary conclusion `C`);
`curry_from_naming` routes it through the existing Lawvere naming. Attribution: Curry (1942); the
diagonal-family framing is Lawvere (1969), via Yanofsky (2003) p. 5 Remark 3. Axiom-free.
