# Prior art for the classical route, and where the choice-free proofs are formalized

Citations for `ZeroParadox/Order/PataraiaFromBourbakiWitt.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration statements.

## The statements are standard; the Bourbaki–Witt route is this file's

Every monotone map on a chain-complete poset has a least fixed point: Zermelo's theorem as stated
by Adámek, Milius and Moss, *Initial Algebras Without Iteration*, CALCO 2021 (LIPIcs, Article 6;
arXiv:2104.09837), Thm 2.1, p. 6:3, proved through Hartogs' lemma and stated there to be "not
constructive". A directed-complete poset with a least element is chain-complete (Bauer and
Lumsdaine, *On the Bourbaki-Witt principle in toposes*, arXiv:1201.0340, p. 3). Adámek, Milius and
Moss state both targets of this file for such a poset: Pataraia's theorem (Thm 2.4, p. 6:4) and
the Pataraia induction principle (Cor 2.6, p. 6:5). The Lean file reaches both through Mathlib's
Bourbaki–Witt, applied to the post-fixed points lying below every fixed point. A source stating
that route to the LEAST fixed point was not located as of 2026-09-28, searched in Adámek–Milius–Moss
2021, Bauer–Lumsdaine, Dubut–Yamada and Taylor; Bauer and Lumsdaine derive from Bourbaki–Witt the
Knaster–Tarski principle for chain-complete posets (Prop 3.4, p. 5), which gives a fixed point
above every post-fixed point, not the least one. What the Lean file adds is the machine-checked
adapter to Mathlib's `CompletePartialOrder`, not the mathematics.

## Three settings, kept apart

- **Classical, with choice** (Lean and Mathlib by default). Done in the Lean file. `#print axioms`
  reports `Classical.choice` for both theorems, which measures these proofs, not the principle:
  the same two statements hold with no axioms (third item).
- **Classical, without choice.** Lang's proof of Bourbaki–Witt is "classically but without choice"
  (Bauer and Lumsdaine, p. 8), and Dubut and Yamada's Isabelle/HOL library, checked with the axiom
  of choice excluded, proves a generalization of Pataraia's theorem
  (`mono_imp_fp_directed_complete`; *Fixed-point theorems for non-transitive relations*, LMCS
  18(1), 2022, pp. 30:3 and 30:19). In Lean, `Classical.em` is itself proved from
  `Classical.choice` (Diaconescu's argument, Lean core `Init/Classical.lean`), so a Lean proof using
  only Lean's built-in axioms and free of `Classical.choice` cannot appeal to that excluded middle;
  excluded middle postulated as a separate axiom would be reported as itself, not as
  `Classical.choice`.
- **Intuitionistic.** Pataraia's proof (Taylor, *Well founded coalgebras and recursion*, Prop 117
  with Thm 118, p. 8). Formalized in Agda in TypeTopology: `Various.Pataraia` (Escardó, 2024,
  assuming propositional resizing) and `Various.Pataraia-Taylor` (Escardó and de Jong, 2024, a
  predicative version after Taylor, whose module notes that predicatively there are no non-trivial
  dcpos of the required size to apply it to). In Lean, `ZeroParadox/Order/PataraiaChoiceFree.lean`
  ports `Various.Pataraia-Taylor`, and `#print axioms` reports no axioms for
  `pataraia_least_prefixedPoint` and `pataraia_induction_constructive`. No other Lean formalization
  was located as of 2026-09-28, searched in the pinned Mathlib (eight `exact?` statement-shape
  probes and a name search) and in Lean core.

## Adjacent in Lean core

Lean core (not Mathlib), `Init/Internal/Order/Basic.lean`, carries `Lean.Order.fix`,
`Lean.Order.fix_eq` and `Lean.Order.fix_induct`: a fixed point of a monotone map on a
`Lean.Order.CCPO` and fixpoint induction for admissible predicates. They are internal to
`partial_fixpoint` ("not meant to be used otherwise"), and no leastness theorem for `fix` was
located in that file.
