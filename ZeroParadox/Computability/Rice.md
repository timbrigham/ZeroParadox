# ν-existence beside Rice undecidability: two conjuncts, two uses of the recursion theorem

Argument, placement and attribution for `ZeroParadox/Computability/Rice.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## What is cited, not re-proved

Rice (1953): every *non-trivial extensional* (semantic) property of partial computable functions is
undecidable. Rice's theorem is **already in Mathlib** (`ComputablePred.rice`, `ComputablePred.rice₂`,
`Mathlib/Computability/Halting.lean`), and its proof runs through `fixed_point₂` — Kleene's second
recursion theorem. The Lean file does not re-prove it; it **cites** Mathlib and connects Rice to the
framework's computability face.

## The connection — the genuine content

The framework's computability face is the one place the diagonal fixed point is *genuinely produced*,
not walled: `computability_face_fixedPoint` (`ZeroParadox/Category/Lawvere.lean`) is **Rogers'
fixed-point theorem** (Mathlib `Nat.Partrec.Code.fixed_point`; Mathlib reserves *Kleene's second
recursion theorem* for `fixed_point₂`, which it derives from it), read as the Kleene quine
(ν-existence); a program that prints its own code takes one further s-m-n step, not in that declaration.
The fixed point is machine-checked; that it is an instance of Lawvere's theorem is cited (Yanofsky
2003, Theorem 5; Bauer 2017, a version of Lawvere's theorem for multi-valued maps, in synthetic
computability).

Mathlib's proof of Rice uses the recursion theorem again, on the **decidability** axis: the quine
*exists*, and *which* programs have any non-trivial semantic property is *undecidable*.
`quine_exists_yet_rice` states the two as a conjunction whose second conjunct does not mention `f`: it is
`rice_face C …` exactly. So nothing is stated about membership at `f`'s fixed point. The standard
recursion-theorem proof of Rice's theorem (Yanofsky 2003, p. 19 of arXiv:math/0305282v1; Mathlib's
`ComputablePred.rice`, via `fixed_point₂`) turns on membership at the fixed point of a different map, one
built from the assumed decider for `C`. Rice's 1953 proof instead reduces from the emptiness problem: his
Theorem 5 shows the unit class of the empty set is not completely recursively enumerable, and his
Theorem 6 derives the general case from it by a reduction (H. G. Rice, Trans. Amer. Math. Soc. 74(2) (1953) 358–366). Gloss:
`ZeroParadox/Computability/ComputationCannotBe.lean` § V.

So on the wall map: the total faces (lattice, 2-adic) *posit* the fixed point and it is *refuted* as a
Lawvere instance in Set (Cantor); the computability face *has* the fixed point (recursion theorem), and
beside it sits undecidability (Rice). Reading: the "exists-but-undecidable" pivot face. No theorem here
makes either half depend on the other.

## Honest delta

Rice's theorem is Rice's (1953); its Lean proof is Mathlib's. Its diagonal-family framing is Yanofsky (2003), p. 19 of
arXiv:math/0305282v1, an application of his Theorem 5 (the recursion theorem); Lawvere (1969) does not
treat it. New here: the framework restatement, a concrete face (the halting problem), and the
`quine_exists_yet_rice` pairing, which states the ν-existence and the undecidability as two independent
conjuncts.
