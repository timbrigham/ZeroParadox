# ZP-N, the ε₀ snap on ordinal notations: the probe, the result and its fences

Ride-along documentation for [`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`](ConstructiveOrdinals.lean).
The Lean file holds the declarations, the Engineer's Take and a statement per declaration; this file holds
the probe, the result, its fences, the scope and the prior art. Where the two would overlap, **the Lean is
authoritative**.

## The probe

The probe (2026-06-15; its `Ordinal`-side measurements are reprinted by the purity blocks of
`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` and `ZeroParadox/Ordinal/PricedInterface.lean`;
`ONote.cmp` is printed in neither, and re-measured `[propext]` on 2026-10-09) showed that ZP-L's `Classical.choice` at ε₀ is *inherited* from Mathlib's classically-built `Ordinal` machinery — the order
instance and the operations, NOT the type, which measures `[propext, Quot.sound]` — but the
syntactic notation substrate (`ONote.cmp`) is choice-free (`propext`-only). ZP-N rebuilds the
snap-from-below **syntactically**, never touching `repr`/`Ordinal`, so the three ascent results below are
choice-free; `tower_NF` is not (side finding below).

Key move: ω^x at the notation level is just `oadd x 1 0` (the CNF term with leading exponent x,
coefficient 1, remainder 0) — no general `opow` needed. ε₀ itself is NOT an `ONote` element (the
notations name exactly the ordinals < ε₀); ε₀ is their limit. So the snap threshold is characterised
*from below*: the ω-tower climbs without bound, and **no notation is a fixed point of ω^·** — the fixed
point (ε₀) is precisely what the notation system cannot reach.

## Result (proved, this build)

The snap-from-below is **choice-free**: `exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono` all
report `[propext]` only — no `Classical.choice` — in contrast to every ε₀ result in ZP-L (all carry
`Classical.choice`, inherited from Mathlib's `Ordinal` machinery). What that shows is narrow and worth
stating narrowly: **the snap's downward structure is constructive** (the ω-tower climbs without bound; no
notation is a fixed point of `ω^·`).

**It does NOT classify ZP-L's footprint as "representational, not intrinsic"**. That is an
*eliminability* claim, and
it cannot be asked of those ε₀ results as stated: they are **STATEMENT-CARRIED**
(`ZeroParadox/Category/ChoiceCannotBe.md`). ZP-L's `epsilonZero_fixedPoint`, `epsilonZero_eq_nfp`,
`epsilonZero_tower_lt` and `epsilonZero_le_fixedPoint` (`ZeroParadox/Ordinal/Gentzen.lean`), and the
invariants `epsilon0_ne_zero`, `epsilon0_ne_bot`, `epsilon0_is_fixedpoint`
(`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) and `epsilon0_eq_nfp_bot`
(`ZeroParadox/Ordinal/Epsilon0MinMax.lean`), each only assumed in a theorem that proves `True`, already
report `Classical.choice` (statement control, measured 2026-10-08), so no re-proof of them can drop it.

A restatement cannot be had on `ONote`, which does not name ε₀: inside the carrier no notation bounds
the tower (`tower_no_upper_bound`, `ZeroParadox/Ordinal/SnapNucleusConstructive.lean`, `[propext]`), and
across the crossing every notation denotes below ε₀ (`repr_lt_epsilon0`,
`ZeroParadox/Ordinal/PricedInterface.lean`, whose statement carries choice); what `ONote` carries is the ascent, whose statements (`omegaPow_no_fixedpoint`, `tower_strictMono`), measured the same way, report
`[propext]` only. The restatement has two readings. The **defined** one is in Lean: on `E0Note`
(`ZeroParadox/Ordinal/PricedInterface.lean`), the notations with one top adjoined, the fixed point of
`e0OmegaPow` (ω^· extended to fix ⊤ by definition) is unique by theorem (`e0OmegaPow_fixedpoint_iff`, `[propext]`) and exists by definition
(`e0OmegaPow_top`, proved by `rfl`), on an order that is not well-founded (the `example` stating
`¬ WellFoundedLT E0Note`). The **derived** one is open: a choice-free, well-founded Lean carrier on which
ε₀'s fixed point is derived, leastness included, is not located as of 2026-10-08 (searched
2026-10-08: `ZeroParadox/**/*.lean` for `WellFounded`, `IsWellOrder` and `Acc`; the Mathlib pin's
notation systems were surveyed 2026-08-02 in `ZeroParadox/Ordinal/SnapNucleusConstructive.md`), and the crossing into `Ordinal`,
`e0Repr`, carries choice. The current state is in `ZeroParadox/Ordinal/SnapNucleus.md` § Axiom footprint.

Two further corrections. `Ordinal` itself is `[propext, Quot.sound]` — **choice is not in the
type**; it enters through `Ordinal.instLinearOrder`, `nfp`, `omega0`, `epsilon`. And a choice-free result *about the ascent* is
suggestive for the ε₀ results without being a re-proof of them.

Side finding: `tower_NF` (well-formedness) *does* carry `Classical.choice` — because Mathlib's `NF`
predicate is defined through `repr` into `Ordinal`. The snap facts do not depend on `NF`, so they stay
choice-free; but even "this notation is well-formed" inherits choice in Mathlib, through `NF`'s statement
(statement control, `[propext, Classical.choice, Quot.sound]`, measured 2026-10-09). That is one site
where choice enters, not the only one: ε₀'s leastness is not routed through `tower_NF`, and its choice
is carried by its own statement (`ZeroParadox/Ordinal/SnapNucleus.md` § Axiom footprint).

## Scope

This is the snap *from below* (ε₀ is the unreachable fixed point). On `ONote` the matching
*minimality* ("ε₀ is the LEAST fixed point") cannot be stated, because it quantifies over the limit,
which no notation names. Leastness is proved on `Ordinal` (`epsilon0_min_eq_max`, with choice); a
choice-free proof of it on a well-founded carrier was not located as of 2026-10-08. The other carriers
are in `ZeroParadox/Ordinal/SnapNucleus.md` § Axiom footprint.

## Prior art

`ONote`, its comparator `ONote.cmp`, its denotation `ONote.repr` and the normal-form predicate `NF` are
Mathlib's (`Mathlib/SetTheory/Ordinal/Notation.lean`). ZP-N's `omegaPow`, `tower` and the three
choice-free theorems are built on them.

The closest located source for the mathematics is N. Kraus, F. Nordvall Forsberg and C. Xu, "Connecting
Constructive Notions of Ordinals in Homotopy Type Theory", MFCS 2021 (LIPIcs 202), arXiv:2104.02549,
formalised in cubical Agda. Their abstract states a related split: in a constructive
setting the classically equivalent notions of ordinal "split apart", and "for Cantor normal forms, most
properties are decidable, whereas for wellfounded extensional transitive orders, most are undecidable".
Read from the arXiv v2 PDF:

* **Theorem 1** (p. 6): on their Cantor normal forms `Cnf`, `<` is trichotomous and `≤` connex; for the
  set-theoretic ordinals `Ord` these statements are equivalent to excluded middle. ZP-N works on the
  decidable side, with Mathlib's comparator `ONote.cmp`.
* **Theorem 9** (p. 9, proof p. 18): `Cnf` has no suprema or limits, shown with the tower ω↑↑k; limits of
  bounded increasing sequences would give WLPO. Its counterpart here is "ε₀ is not a notation" above, and
  `tower_no_upper_bound` in `ZeroParadox/Ordinal/SnapNucleusConstructive.lean`.
* **Theorem 18** (p. 11, definition p. 12): exponentiation with base ω on `Cnf` is ω^a :≡ ω^a ✚ 0,
  where the bold ✚ is their notation for the tree constructor, not addition (footnote 3, p. 11): the
  term with remainder 0. ZP-N's `omegaPow x := oadd x 1 0` is the same move, with Mathlib's coefficient
  set to 1.
* **Theorem 22** (p. 13): every `Cnf`, embedded into their Brouwer trees `Brw`, lies below
  `limit (λk. ω↑↑k)`, which they call ε₀. `Brw`'s order is well-founded (their Theorem 4, p. 7), so `Brw`
  names ε₀ on a well-founded carrier, in Agda rather than Lean. Their Agda module `BrouwerTree.Arithmetic.Properties`
  (bitbucket.org/nicolaikraus/constructive-ordinals-in-hott, commit
  `2308dc82dca10c8bfc04030974b5e506f710783e`, `BrouwerTree/Arithmetic/Properties.agda` line 811)
  states `ε₀≡ω^ε₀ : ε₀ ≡ ω^ ε₀`, and the proof of Theorem 22 (p. 26) uses ε₀ = ω^ε₀; a leastness
  lemma was not located there (`ZeroParadox/Ordinal/SnapNucleus.md` § Axiom footprint).

The Coq precedent on the same carrier is Castéran and Contejean's *hydra-battles*; its credit, including
the comparator and the order construction, is in `ZeroParadox/Ordinal/SnapNucleusConstructive.md`
§ Prior art.

**The delta, stated narrowly.** Their split is decidability and constructive taboos (excluded middle,
WLPO) in homotopy type theory; ZP-N's is a `Classical.choice` footprint in Lean, measured by
`#print axioms` against Mathlib's `Ordinal`. The instruments differ: a taboo result says a statement
implies excluded middle or WLPO, while a footprint is about one proof, or, under the statement control,
about one statement's type. Their `Cnf` is the binary trees cut out by a predicate `isCNF` (§ 3.1, p. 4), the same shape as
Mathlib's `NONote`, the notations cut out by `NF`. The side finding above arises because Mathlib's `NF` is
defined through `repr` into `Ordinal`; `isCNF` is stated with the lexicographic order on trees. What is ZP-N's is the measurement on these Lean declarations, not the
mathematics.
