# Building an abstract provability logic, and Gödel's second as a corollary

Argument, design and attribution for `ZeroParadox/Settheory/Loeb.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

## The face

Löb (1955): in a system with a provability predicate `□` satisfying the Hilbert–Bernays–Löb derivability
conditions and given a Löb diagonal ψ (hypotheses hfix1, hfix2), `⊢ (□A → A)` implies `⊢ A`. In
arithmetic, Löb's setting, the diagonal lemma supplies ψ with `⊢ ψ ↔ (□ψ → A)`; hfix1 and hfix2 are
the two halves of that equivalence, which this file takes as hypotheses. This is the diagonal
family's **provability-modal face** — the self-referential fixed point of the map `p ↦ (□p → A)`
(the Löb sentence). It is the ONLY sibling of the four with no Mathlib support located as of 2026-08-17, so it is built from scratch as an abstract
provability logic. Searched as follows: `Löb`, `GL`, `provability`, `□`/`box` as a modality, and
`derivability` across the pinned Mathlib; `#check` on the names those would carry. No modal or
provability logic found.

## Placement in the family

Tarski is the TRUTH face (undefinable — the wall), Gödel/Löb the PROVABILITY face (definable but
self-constrained). Löb subsumes **Gödel's second incompleteness**: at `A = falsum`, given a Löb diagonal for
falsum, a consistent system cannot prove `□falsum → falsum` — its own consistency (`godel_two`). That reading is
Gödel's second theorem when the class is instantiated at a theory of arithmetic and falsum is its falsum. In
the class, `godel_two` binds falsum as an arbitrary sentence (`ProvabilityLogic` has no falsum
constant and no ex-falso), so it covers any unprovable sentence with a Löb diagonal, including one
that does not imply every sentence, and without a Löb diagonal its conclusion can fail (the two
`example`s directly after `godel_two` in `ZeroParadox/Settheory/Loeb.lean`). The Löb sentence
`ψ ↔ (□ψ → A)` is a diagonal fixed point up to provability (`ProvabilityLogic.loeb_sentence_is_fixedpoint`)
(ν: in arithmetic, by the diagonal lemma; here the hypotheses hfix1, hfix2), and Löb is what it forces
(`ProvabilityLogic.loeb`). On the Lindenbaum quotient its class is a literal fixed point of the induced map
(`ProvabilityLogic.selfOnlyAt_loebMapQuot_iff` and the `example` after it). The family's table files the face as a
floor (ν) because that diagonal closes; `godel_two`'s docstring calls the unprovability of consistency the wall on the
provability axis. That wall is a limitation, not one of the μ wall faces.

## Design

`ProvabilityLogic` is a typeclass carrying sentences `S`, connective `imp`, modality `box`, and a
provability predicate `Thm`, with the axioms the derivation of `loeb` uses — the implicational Hilbert base (`ax_K`,
`ax_S`) with modus ponens (`mp`), and the three derivability conditions (`nec` = D1, `ax_D2` =
distribution, `ax_D3` = D3). The diagonal lemma is taken as a hypothesis (`hfix1`/`hfix2`), the standard
separation of concerns: Löb from the derivability conditions plus a diagonal.

Diagonal and principle: `ProvabilityLogic.loeb_diagonal_of_loeb_axiom` takes Löb's principle
`⊢ □(□A → A) → □A` at `A` as an explicit hypothesis and gives `□A → A` as a Löb diagonal for `A`;
`ProvabilityLogic.loeb_axiom_of_loeb_diagonal` is its converse, so in the class some Löb diagonal for `A` exists
iff Löb's principle holds at `A`. That pair is not `loeb` and its converse: `loeb` concludes Löb's RULE at `A`,
and a control after `godel_two` has the rule at one `A` with no Löb diagonal for it, so the converse of
`loeb` at one `A` is false in the class (the last `example` of § IV of the Lean file).
`loeb_diagonal_of_loeb_axiom` trades one input of `loeb` for another and constructs no arithmetic diagonal.
Its hypothesis is needed: without it, its first conjunct is false in the class, failing at `A = false` in the
one-point reflexive control after `godel_two` (the `example` after that control).
`loeb_axiom_of_loeb_diagonal` is the formalized Löb theorem, `⊢ □(□A → A) → □A` (Saitou and Noguchi,
arXiv:2609.13780, Prop 2.9), at one `A` and from a diagonal taken as a hypothesis;
FormalizedFormalLogic/Foundation proves it uniformly in `σ` as
`FFL.FirstOrder.ProvabilityAbstraction.formalized_löb_theorem`
(`Foundation/FirstOrder/Incompleteness/ProvabilityAbstraction/Basic.lean` at commit c3eb37ae, retrieved
2026-11-01), for a provability predicate `𝔅` of a theory `T` in a theory `T₀`, under `[𝔅.HBL]`, `[T₀ ⪯ T]`
and `[L.DecidableEq]`, with its Löb diagonal, the Kreisel sentence `kreisel`, taken from a
`Diagonalization T₀` instance. In arithmetic the diagonal lemma is formalized in Lean 4 as `diagonal` in
FormalizedFormalLogic/Foundation (`Foundation/FirstOrder/Arithmetic/Bootstrapping/FixedPoint.lean` at commit
c3eb37ae, retrieved 2026-11-01).

## Honest delta

No modal or provability logic was located in the pinned Mathlib as of 2026-08-17, searched as in § The face
(re-run on three axes 2026-08-30, as recorded in `LEAN_CUSTOM_REGISTRY.md`).
Attribution: Löb (1955); Hilbert–Bernays–Löb derivability conditions; diagonal-family framing:
Yanofsky (2003, arXiv:math/0305282v1, p. 18), who treats Löb's paradox in that family, extending
Lawvere (1969), whose paper does not name Löb (TAC reprint text searched for "Löb", 2026-11-05; it
treats Gödel's incompleteness and Tarski, § 3). The classical Löb derivation is standard.
Prior art: Popescu & Traytel, CADE-27 (2019) and AFP Goedel_Incompleteness (abstract Hilbert–Bernays–Löb (HBL) derivability conditions, Gödel 2
and Löb in Isabelle); Saitou & Noguchi, arXiv:2609.13780 (Lean 4 Foundation: abstract Provability and Diagonalization
classes; more exactly, `Provability` is a structure with the derivability conditions as classes over it (`HBL2`,
`HBL3`) and `Diagonalization` a class, § 2.4, with abstract Gödel 2 and Löb as Propositions 2.8 and 2.9). On diagonal and principle: the Stanford Encyclopedia of Philosophy entry "Provability Logic", § 2.2,
states that in GL fixed points of formulas modalized in `p` exist and are unique up to GL-equivalence (de Jongh and
Sambin, 1975); Litak and Visser (arXiv:1905.09450, § 1) credit uniqueness also to Bernardi (1976). In Lean 4 that
theorem for GL is `FFL.ProvabilityLogic.Logic.GL.fixpoint_theorem` in FormalizedFormalLogic/Foundation
(`Foundation/ProvabilityLogic/GL/Fixedpoint.lean` at commit c3eb37ae), giving existence and uniqueness, not an
explicit fixed point. Litak and Visser § 1 state that GL is the smallest extension of K4 in which guarded
fixpoints are definable, which follows because, by Löb's argument, Löb's principle is entailed by the presence of
guarded fixed points in combination with the de Jongh–Sambin result. That is a statement about logics, with
fixed points for every guarded formula; `loeb_axiom_of_loeb_diagonal` uses one diagonal, for the one map
`p ↦ (□p → A)`, and gives the principle at that one `A`, with D3 as its K4 ingredient and no use of the
de Jongh–Sambin theorem; `loeb_diagonal_of_loeb_axiom` gives a diagonal back from the principle at that `A`.
Compare Kumasaka and Kurahashi (arXiv:2608.29914, Thm 7.14, Prop 7.17): in a meet abstract provability
structure satisfying (C3*), the parametrized fixed-point condition (FP), that for every `x` some `p` has
`p = ⊠(p ∧ x)`, gives their (Löb), the abstract counterpart of Löb's rule; and there is a consistent meet APS
with (C3*) and (Löb) in which no one-variable term of odd degree has a fixed point. The hypothesis of
`loeb_diagonal_of_loeb_axiom` is the internal principle, not the rule. A source stating that `□A → A` solves
`p ↔ (□p → A)` was not located as of 2026-11-01, searched as follows: that SEP section (whose one worked example
is the falsum instance `¬□⊥`), Litak and Visser § 1, Kumasaka and Kurahashi, Fitting's GL fixed-point program
note (the retrieved copy is dated October 4, 1995), and theoremsearch, ten phrasings over three
prior-art review rounds of 2026-11-01 (four, four and two). Not retrieved: Boolos (1993) ch. 8, Smoryński (1985),
Lindström (2006, J. Phil. Logic 35). The Lean theorem is the check.
