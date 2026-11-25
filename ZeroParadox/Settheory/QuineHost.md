# Why AFA, and what the forcing does not choose

Overview for `ZeroParadox/Settheory/QuineHost.lean`. The Lean file holds the declarations, the Engineer's Take
and the per-declaration glosses.

## Non-well-foundedness is forced; the axiom is not

With membership as the step, a host meeting `QuineAtomHost` has a membership relation that is not
well-founded (`quineAtomHost_not_wellFounded`), and no `ZFSet` is its own sole member
(`zfSet_no_singleton_bottom`). That much is forced. Which anti-foundation axiom supplies the host is not.

As cited in ZP-E (Remark R-AFA), Aczel records four anti-foundation axioms, and AFA, FAFA and SAFA each admit
exactly one reflexive set (x = {x}) while being pairwise incompatible (Aczel 1988, *Non-Well-Founded Sets*,
CSLI Lecture Notes 14, Corollary 4.28, p. 55; Appendix A, p. 108). Supplying exactly one Quine atom therefore does not single AFA out: AFA is adopted as the canonical
host, not selected by the membership structure.

## Boffa, and the mechanism that is checked

As cited in ZP-E, Boffa's axiom implies BA₁ (Aczel 1988, Exercise 5.14(i), p. 65: BAFA ⇔ BA₁ + BA₂), and BA₁ alone makes the reflexive sets a proper class (Aczel 1988, Proposition 5.1, p. 57, as
`boffa_fails_reflexive_unique`'s docstring cites it). No part of either Boffa axiom is formalized here. The
checked part is the mechanism, that (Y') does not force (Z'): `boffa_fails_reflexive_unique`, a two-element
toy in which every element is its own only member.

## What stays a commitment

Adopting AFA is CC-2's commitment. Its Lean abstraction is `QuineAtomHost`, whose two fields demand a host
bottom b = {b} and its uniqueness among reflexive sets. `Reading:` a host bottom b = {b, x} with x ≠ b would add members carrying their own
membership chains; b = {b} is the minimal option. Every inhabited carrier meets `QuineAtomHost`
(`trivialQuineAtomHost`), so membership in the class carries no information without the `mem` named.
