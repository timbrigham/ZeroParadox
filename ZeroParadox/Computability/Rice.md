# The price of ν-existence: one recursion-theorem fixed point read on two axes

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
recursion theorem* for `fixed_point₂`, which it derives from it), giving the Kleene quine (ν-existence).

Rice is the **same** recursion-theorem fixed point read on the **decidability** axis: the quine *exists*,
yet *which* programs have any non-trivial semantic property is *undecidable*. That pairing — ∃ but
¬decidable — is the "exists-but-undecidable" signature of the computability row of the wall taxonomy: the
**pivot** face, where the fixed point is posited and neither refuted nor decidable.

So on the wall map: the total faces (lattice, 2-adic) *posit* the fixed point and it is *refuted* as a
Lawvere instance in Set (Cantor); the computability face *has* the fixed point (recursion theorem) but
pays for it with undecidability (Rice). **Rice is the price of the ν-existence.**

## Honest delta

Rice itself is Mathlib's (Rice 1953; the diagonal-family framing is Lawvere (1969), via Yanofsky (2003)
p. 5 Remark 3). New here: the framework restatement, a concrete face (the halting problem), and the
`quine_exists_yet_rice` pairing that states the ν-existence and the undecidability as two faces of one
recursion-theorem setting.
