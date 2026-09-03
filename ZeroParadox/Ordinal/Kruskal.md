# Where the choice comes from, and which half of the axiom-free proof transfers

Argument, scope and credit for `ZeroParadox/Ordinal/Kruskal.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses, and its `PurityCheck` block
EMITS the axiom footprints this document reasons about — so the locator claim below is checked
at the site rather than asserted here.

## The proof

Every infinite sequence of trees has `i < j` with `Tᵢ` embedding into `Tⱼ` (the unlabeled case is
`α = Unit`). The argument is Nash-Williams' **minimal bad sequence**: a minimal bad sequence of
trees has WQO immediate-subtrees (by minimality), so Higman's lemma makes the *lists of subtrees*
WQO, and the labels are WQO by hypothesis — contradicting badness at the roots.

## What is reused vs. built
Mathlib supplies the heavy reusable engine, on which this file builds (and which it cites, not
re-proves):
- `Set.PartiallyWellOrderedOn` — the WQO predicate (`Mathlib.Order.WellFoundedSet`).
- `Set.PartiallyWellOrderedOn.IsBadSeq` / `exists_min_bad_of_exists_bad` — the Nash-Williams minimal
  bad sequence construction.
- `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` — **Higman's lemma** (lists under
  `List.SublistForall₂` are WQO when the alphabet is).

Kruskal's tree theorem is **not located in the pinned Mathlib as of 2026-09-03**, searched THREE
ways. **By NAME**, over the whole pinned tree: 33 hits in 6 files, every one Kruskal–Katona —
`SetFamily/KruskalKatona`, `SetFamily/Shadow`, `SetFamily/LYM`, `SetFamily/Compression/UV` and
`Combinatorics/Colex` under `Mathlib/`, plus the root import in `Mathlib.lean`. **By statement
SHAPE**, with `exact?`, which a name grep cannot do: it returns only this file's own declaration.
**By CONCEPT**, the axis a name search misses entirely: no `tree theorem`, no rose trees, and
`nash.?williams` in exactly one file, there as the attribution on Higman's lemma. The rose-tree type, the embedding order, and the Nash-Williams assembly
on top of Mathlib's Higman are the original *formalization* content here; the mathematics is classical
and credited under Prior art below.

## Prior art — the theorem is classical; whether THIS proof's `Classical.choice` is removable is OPEN

Kruskal's tree theorem (Kruskal 1960) and Higman's lemma (Higman 1952) are classical results; this file
formalizes the labeled tree theorem on Mathlib's WQO machinery. Two threads must be credited:

- **The Nash-Williams route this file takes.** The minimal bad sequence argument is Nash-Williams
  (1963), and Mathlib's `exists_min_bad_of_exists_bad` / `minBadSeqOfBadSeq` is that argument. It
  carries `Classical.choice`, and it is NOT the only carrier — the `PurityCheck` block in the Lean
  file emits four routes and every one of them reports choice.

  ⚠⚠ **BUT THE FOOTPRINT DOES NOT DISTINGUISH THEM, AND THIS DOCUMENT MUST NOT PRETEND IT DOES.**
  `#print axioms` reports which axioms a term's dependency closure CONSUMES; it has no way to
  express REACHABILITY, so it cannot say whether a route passes through the minimal bad sequence
  construction. Measured: `exists_min_bad_of_exists_bad`, `exists_monotone_subseq` and `Nat.sInf_le`
  all report the IDENTICAL `[propext, Classical.choice, Quot.sound]`, and `Classical.choose` differs
  only by being smaller. What separates them is read from **Mathlib's own source order**, not
  emitted: `exists_monotone_subseq` is proved at `Mathlib/Order/WellFoundedSet.lean:366`, four
  hundred lines ABOVE `IsBadSeq` is defined (:768) and `exists_min_bad_of_exists_bad` proved (:795),
  so it cannot depend on either; `Classical.choose` and `Nat.sInf_le` are general-purpose
  declarations in unrelated files. **On that basis** — a one-directional bound from declaration
  order, not a footprint — three of the four routes do not reach the machinery, and a choice-free
  minimal bad sequence would leave them standing. Sternagel's Isabelle/HOL *Certified Kruskal's
  Tree Theorem* takes this route.
- **The constructive route, and why its HYPOTHESIS side does not transfer to this statement.**
  Kruskal's theorem and Higman's lemma have choice-free proofs built on the inductively defined
  **almost-full** predicate `af`. Bar induction is not a rival CHARACTERISATION but an
  intuitionistically equivalent presentation of the same notion, and in JAR2020 that is a THEOREM
  rather than a remark — `bar_t_af_t_eq : af_t (R⇑l) ↔ bar_t (good R) l` (p. 10), beside § 3.3's
  *"these two equivalent inductive characterizations"* and CCC2017's *"intuitionistically
  equivalent formulation in terms of Bar inductive predicates"*. (Equivalent as PREDICATES; the two
  developments are still separate rows in Larchey-Wendling's comparison, and Coquand & Fridlender
  1993 — Higman's lemma for a two-letter alphabet via `Bar`, and no Kruskal proof at all — is one
  of them.) The notion of almost-full is **Veldman & Bezem** (*Ramsey's Theorem and the Pigeonhole
  Principle in Intuitionistic Mathematics*, J. London Math. Soc. s2-47(2), 193–211, 1993 — cited
  second-hand via Larchey-Wendling and Coquand, and not held here); Coquand's *A Direct Proof of
  Ramsey's Theorem* (2011) already carries the inductive definition; and Vytiniotis, Coquand &
  Wahlstedt, *Stop When You Are Almost-Full* (ITP 2012, LNCS 7406, 250–265) is the reference
  Larchey-Wendling cites for the inductive `af` predicate this argument runs on.

  What Larchey-Wendling's comparison marks as inequivalent is a **definition** — Seisenberger's is
  *"not equiv. to Coquand&Fridlender for undecidable R"* — and the restrictions travel with the
  developments that assume them. *Coq-Kruskal* is what removes both: a mechanized, **axiom-free**
  proof of the tree theorem with no decidability assumption, no Brouwer's Thesis, and no
  restriction to a ground type. Seisenberger's (*On the
  Constructive Content of Proofs*, PhD thesis, Munich 2003) requires decidable quasiorders
  (Remark 4.1(3)) — an earlier paper covering the same material is *Kruskal's Tree Theorem in a
  Constructive Theory of Inductive Definitions*, Synthese Library 306, 2001, a DIFFERENT work
  rather than a different date; Goubault-Larrecq's *A Constructive Proof of the Topological Kruskal
  Theorem* (MFCS 2013, LNCS 8087, 22–41), the peer CCC2017 names beside it, is likewise over a
  decidable wqo; and Veldman's uses Brouwer's Thesis AND works for a relation over ℕ rather than
  over arbitrary types — cited second-hand via Larchey-Wendling and not held here.

  ⚠⚠ **It proves a DIFFERENT statement, and only ONE SIDE transports.** Coq-Kruskal establishes
  `af R → af (embed_tree_homeo R)` for the inductively defined predicate; this file proves the
  sequence form. **The CONCLUSION side does transport**, and JAR2020 p. 10 names the lemma:
  `af_t_inf_chain : af_t R → ∀ f : ℕ → X, {n : ℕ | ∃ i j, i < j < n ∧ f i R f j}`
  — from `af` you get the good pair in every sequence, effectively and under a computed bound.
  (The sig type `{n : ℕ | …}` is the source's, and is why the bound COMPUTES rather than merely
  existing.) What does NOT transport is the HYPOTHESIS side: using Coq-Kruskal from a sequence-form
  hypothesis needs the converse, `WellQuasiOrdered r → af r`, and CCC2017 records that the
  classically equivalent WQO definitions are *"(for most of them) not intuitionistically
  equivalent"*. **So whether the choice HERE is removable is UNCLASSIFIED** — the corpus's own tier
  word (`ZeroParadox/Category/ChoiceCannotBe.lean`), and the right one, because removability is a
  NECESSITY question and a footprint can never witness necessity.

  ⚠ **THE OBVIOUS BRIDGE IS NOT FREE, AND THAT IS EMITTED NOW RATHER THAN LEFT TO A READER.**
  `Set.PartiallyWellOrderedOn` **does not depend on any axioms** — it is a pure interface, so the
  question is open rather than foreclosed. But `Set.partiallyWellOrderedOn_univ_iff`, which puts
  `WellQuasiOrdered` one rewrite from this file's statement, is itself
  `[propext, Classical.choice, Quot.sound]`. **The rewrite moves the STATEMENT without moving the
  FOOTPRINT**, so it is not a step toward the constructive side. Both are in the `PurityCheck` block.

  Seisenberger 2003 uses **dependent choice** at both of the steps this file routes through: § 4.1
  Lemma 4.2, *"using the axiom of dependent choice, we can build our weakly increasing infinite
  sequence"*, the step `exists_monotone_subseq` plays; and the minimal bad sequence construction
  itself, *"Assuming the axiom of dependent choice this process yields an infinite sequence (wᵢ)
  which we call minimal"*, the step `exists_min_bad_of_exists_bad` plays. ⚠ **That is a statement
  about Seisenberger's INFORMAL proof, not a measurement of this file.** Lean has a single
  `Classical.choice` axiom and nothing here separates dependent choice from full choice, so no
  footprint in this corpus can witness the difference; and the other two routes are not the minimal
  bad sequence argument at all. Open induction (Berger) is second-hand and not held.
