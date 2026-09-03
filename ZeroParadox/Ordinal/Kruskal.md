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

Kruskal's tree theorem is **not located in the pinned Mathlib as of 2026-09-03**, searched TWO
ways. By name across `Mathlib/`: 33 hits in 6 files, all Kruskal–Katona — `SetFamily/KruskalKatona`,
`SetFamily/Shadow`, `SetFamily/LYM`, `SetFamily/Compression/UV`, plus `Combinatorics/Colex` (which
is NOT under `SetFamily/`) and a root import. And by statement SHAPE with `exact?`, which the name
grep cannot do: it returns only this file's own declaration. The rose-tree type, the embedding order, and the Nash-Williams assembly
on top of Mathlib's Higman are the original *formalization* content here; the mathematics is classical
and credited under Prior art below.

## Prior art — the theorem is classical; whether THIS proof's `Classical.choice` is removable is OPEN

Kruskal's tree theorem (Kruskal 1960) and Higman's lemma (Higman 1952) are classical results; this file
formalizes the labeled tree theorem on Mathlib's WQO machinery. Two threads must be credited:

- **The Nash-Williams route this file takes.** The minimal bad sequence argument is Nash-Williams
  (1963), and Mathlib's `exists_min_bad_of_exists_bad` / `minBadSeqOfBadSeq` is that argument. It
  carries `Classical.choice`, and it is NOT the only carrier: the `PurityCheck` block below emits
  each route, and most never reach the minimal bad sequence machinery, so a choice-free MBS would
  leave them standing. Sternagel's Isabelle/HOL *Certified Kruskal's Tree Theorem* takes this route.
- **The constructive route, and why its HYPOTHESIS side does not transfer to this statement.**
  Kruskal's theorem and Higman's lemma have choice-free proofs built on the inductively defined
  **almost-full** predicate `af`. Bar induction is not a rival technique but the SAME ONE in a
  second presentation: CCC2017 calls the two *"intuitionistically equivalent"* and JAR2020 § 3.3
  *"these two equivalent inductive characterizations"* — which is why Coquand & Fridlender 1993,
  Higman's lemma for a two-letter alphabet via `Bar` and no Kruskal proof at all, sits on the bar
  side of ONE technique rather than as a second one. The notion of almost-full is **Veldman &
  Bezem** (*Ramsey's Theorem and the Pigeonhole Principle in Intuitionistic Mathematics*, J. London
  Math. Soc. s2-47(2), 193–211, 1993); Coquand's *A Direct Proof of Ramsey's Theorem* (2011)
  already carries the inductive definition; and Vytiniotis, Coquand & Wahlstedt, *Stop When You Are
  Almost-Full* (ITP 2012, LNCS 7406, 250–265) is the reference Larchey-Wendling cites for the
  inductive `af` predicate this argument runs on.

  What Larchey-Wendling's table marks as genuinely inequivalent is the **side conditions**, and
  that is what *Coq-Kruskal* removes: a mechanized, **axiom-free**, unrestricted proof of the tree
  theorem with no decidability assumption and no Brouwer's Thesis. Seisenberger's (*On the
  Constructive Content of Proofs*, PhD thesis, Munich 2003) requires decidable quasiorders
  (Remark 4.1(3)) — an earlier paper covering the same material is *Kruskal's Tree Theorem in a
  Constructive Theory of Inductive Definitions*, Synthese Library 306, 2001, a DIFFERENT work
  rather than a different date; Goubault-Larrecq's *A Constructive Proof of the Topological Kruskal
  Theorem* (MFCS 2013, LNCS 8087, 22–41), the peer CCC2017 names beside it, is likewise over a
  decidable wqo; and Veldman's uses Brouwer's Thesis — cited second-hand via Larchey-Wendling
  and not held here.

  ⚠⚠ **It proves a DIFFERENT statement, and only ONE SIDE transports.** Coq-Kruskal establishes
  `af R → af (embed_tree_homeo R)` for the inductively defined predicate; this file proves the
  sequence form. **The CONCLUSION side does transport**, and JAR2020 p. 10 names the lemma:
  `af_t_inf_chain : af_t R → ∀ f : ℕ → X, {n | ∃ i j, i < j < n ∧ f i R f j}`
  — from `af` you get the good pair in every sequence, effectively and under a computed bound.
  What does NOT transport is the HYPOTHESIS side: using Coq-Kruskal from a sequence-form hypothesis
  needs the converse, `WellQuasiOrdered r → af r`, and CCC2017 records that the classically
  equivalent WQO definitions are *"(for most of them) not intuitionistically equivalent"*. **So
  whether the choice HERE is removable is UNMEASURED.** `Set.PartiallyWellOrderedOn` is axiom-free
  as a type, so the question is open rather than foreclosed, and
  `Set.partiallyWellOrderedOn_univ_iff` puts `WellQuasiOrdered` one rewrite from this file's
  statement. The residual content is **dependent choice**, and Seisenberger 2003 uses it at BOTH
  steps this file's footprints reach: § 4.1 Lemma 4.2, *"using the axiom of dependent choice, we
  can build our weakly increasing infinite sequence"*, the step `exists_monotone_subseq` plays;
  and the minimal bad sequence construction itself, *"Assuming the axiom of dependent choice this
  process yields an infinite sequence (wᵢ) which we call minimal"*, the step
  `exists_min_bad_of_exists_bad` plays. Open induction (Berger) is second-hand and not held.
