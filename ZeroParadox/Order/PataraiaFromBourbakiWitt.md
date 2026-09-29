# Prior art for the classical route, and where the choice-free proofs are formalized

Citations for `ZeroParadox/Order/PataraiaFromBourbakiWitt.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration statements.

## Standard statements; Markowsky 1976 gives the Bourbaki–Witt route to the least fixed point

Every monotone map on a chain-complete poset has a least fixed point: Zermelo's theorem as stated
by Adámek, Milius and Moss, *Initial Algebras Without Iteration*, CALCO 2021 (LIPIcs, Article 6;
arXiv:2104.09837), Thm 2.1, p. 6:3, proved through Hartogs' lemma and stated there to be "not
constructive". A directed-complete poset with a least element is chain-complete (Bauer and
Lumsdaine, *On the Bourbaki-Witt principle in toposes*, arXiv:1201.0340, p. 3). Adámek, Milius and
Moss state both targets of this file for such a poset: Pataraia's theorem (Thm 2.4, p. 6:4) and
the Pataraia induction principle (Cor 2.6, p. 6:5). Markowsky, *Chain-complete posets and directed
sets with applications*, Algebra Universalis 6 (1976) 53–68, Thm 9(i), p. 65, reaches the least
fixed point on a chain-complete poset (every chain, "including the empty chain", has a sup, p. 53)
by applying Bourbaki's theorem (his Thm 8) to the post-fixed points lying below every fixed point,
without "the axiom of choice" (p. 65). Dubut and Yamada report that Markowsky showed the fixed
points of a chain-complete poset are again chain-complete and that his proof uses the Bourbaki–Witt
theorem (LMCS 18(1), 2022, p. 30:1). `dcpo_exists_least_fixedPoint` uses Markowsky's set, with
Mathlib's Bourbaki–Witt. `pataraia_induction` restricts `f` to the post-fixed points in `U` below
the least fixed point, where it is inflationary, and applies Bourbaki–Witt there; Adámek, Milius and
Moss's proof of Thm 2.4 (items 3–4, pp. 6:4–6:5) likewise restricts `f` to a set of post-fixed
points on which it is inflationary, taking the fixed point from Pataraia's step (their item 2)
instead. Goubault-Larrecq, *Bourbaki, Witt, and Dito Pataraia* (web note, June 13th, 2013), reaches
the least common fixed point, above a given point, of a family of inflationary monotone maps on a
dcpo, by Pataraia's route rather than Bourbaki–Witt, and credits it to Escardó (2003). What the Lean
file adds is the machine-checked adapter to Mathlib's `CompletePartialOrder`, not the mathematics.

## Three settings, kept apart

- **Classical, with choice** (Lean and Mathlib by default). Done in the Lean file. `#print axioms`
  reports `Classical.choice` for both theorems, which measures these proofs, not the principle:
  the same two statements hold with no axioms (third item).
- **Classical, without choice.** Markowsky's Thm 9(i), cited above, gives the least fixed point
  without the axiom of choice (p. 65). Lang's proof of Bourbaki–Witt is "classically but without choice"
  (Bauer and Lumsdaine, p. 8), and Dubut and Yamada's Isabelle/HOL library, checked with the axiom
  of choice excluded, proves a generalization of Pataraia's theorem
  (`mono_imp_fp_directed_complete`; *Fixed-point theorems for non-transitive relations*, LMCS
  18(1), 2022, pp. 30:3 and 30:19). In Lean, `Classical.em` is itself proved from
  `Classical.choice` (Diaconescu's argument, Lean core `Init/Classical.lean`), so a Lean proof using
  only Lean's built-in axioms and free of `Classical.choice` cannot appeal to that excluded middle;
  excluded middle postulated as a separate axiom would be reported as itself, not as
  `Classical.choice`.
- **Intuitionistic.** Pataraia's proof (Taylor, *Well founded coalgebras and recursion*, Prop 117
  with Thm 118, p. 8). Pataraia did not publish it (Taylor, p. 8). Its first full published proof
  is Escardó, *Joins in the frame of nuclei*, Applied Categorical Structures 11 (2003) 117–124:
  Pataraia's theorem is his Cor 2.1, and the induction principle is the second clause of his
  Thm 2.2, stated there for sets of inflationary maps. Escardó notes that only a brief sketch had
  been published before (Taylor, *Practical Foundations of Mathematics*, 1999, Exercises 3.44 and
  3.45). Formalized in Agda in TypeTopology: `Various.Pataraia` (Escardó, 2024, following the 2003
  paper and assuming propositional resizing) and `Various.Pataraia-Taylor` (Escardó and de Jong,
  2024, a predicative version replacing the second step with Taylor's condition `TC`, whose module
  notes that predicatively there are no non-trivial dcpos of the required size to apply it to). In
  Lean, `ZeroParadox/Order/PataraiaChoiceFree.lean` ports `Various.Pataraia-Taylor` (`TC`) together
  with the `γ` step, `lemma₂·₁` of `Various.Pataraia`, which that module imports, and
  `#print axioms` reports no axioms for
  `pataraia_least_prefixedPoint` and `pataraia_induction_constructive`. No other Lean formalization
  was located as of 2026-09-28, searched in the pinned Mathlib (eight `exact?` statement-shape
  probes and a name search) and in Lean core.

## Adjacent in Lean core

Lean core (not Mathlib), `Init/Internal/Order/Basic.lean`, carries `Lean.Order.fix`,
`Lean.Order.fix_eq` and `Lean.Order.fix_induct`: a fixed point of a monotone map on a
`Lean.Order.CCPO` and fixpoint induction for admissible predicates. They are internal to
`partial_fixpoint` ("not meant to be used otherwise"), and no leastness theorem for `fix` was
located in that file.
