# Where the choice comes from, and why the axiom-free proof does not transfer

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
ways. By name across `Mathlib/`: 33 hits in 6 files, all Kruskal—Katona — `SetFamily/KruskalKatona`,
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
  Kruskal's theorem and Higman's lemma have choice-free proofs by two DISTINCT techniques, and
  they are separate rows in Larchey-Wendling's own table: **bar induction** (Coquand & Fridlender
  1993, which proves Higman's lemma for a two-letter alphabet via `Bar` and contains no Kruskal
  proof), and the inductively defined **almost-full** predicate (Vytiniotis, Coquand & Wahlstedt,
  *Stop When You Are Almost-Full*, ITP 2012, LNCS 7406, 250—265 — the origin of the `af`
  predicate this argument runs on). Larchey-Wendling's *Coq-Kruskal* is a mechanized,
  **axiom-free**, unrestricted proof of the tree theorem on the af technique, with no decidability
  assumption and no Brouwer's Thesis, removing the restrictions of the earlier intuitionistic
  proofs: Seisenberger's (*On the Constructive Content of Proofs*, PhD thesis, Munich 2003), which
  requires decidable quasiorders (Remark 4.1(3)) — its Kruskal chapter was published as
  *Kruskal's Tree Theorem in a Constructive Theory of Inductive Definitions*, Synthese Library 306,
  2001, a DIFFERENT work rather than a different date; Goubault-Larrecq's *A Constructive Proof of
  the Topological Kruskal Theorem* (MFCS 2013, LNCS 8087, 22—41), the peer CCC2017 names beside
  it, likewise over a decidable wqo; and Veldman's, which uses Brouwer's Thesis — cited
  second-hand via Larchey-Wendling and not held here.

  ⚠⚠ **It proves a DIFFERENT statement, and only ONE SIDE transports.** Coq-Kruskal establishes
  `af R → af (embed_tree_homeo R)` for the inductively defined predicate; this file proves the
  sequence form. Larchey-Wendling's design criterion is that an intuitionistic WQO definition
  *"should intuitionistically imply almost full"*, so `af → sequence form` is the AVAILABLE
  direction and a CONCLUSION in af form transports down — CCC2017 derives Vazsonyi's conjecture,
  itself sequence-form, from the af theorem. What does not transport is the HYPOTHESIS side: using
  Coq-Kruskal from a sequence-form hypothesis needs `WellQuasiOrdered r → af r`, the converse,
  and CCC2017 records that the classically equivalent WQO definitions are *"not intuitionistically
  equivalent"*. **So whether the choice HERE is removable is UNMEASURED.**
  `Set.PartiallyWellOrderedOn` is axiom-free as a type, so the question is open rather than
  foreclosed, and `Set.partiallyWellOrderedOn_univ_iff` puts `WellQuasiOrdered` one rewrite from
  this file's statement. The residual content of the minimal bad sequence argument is **dependent
  choice**, stated directly by a source held here — Seisenberger 2003 § 4.1 Lemma 4.2, *"using the
  axiom of dependent choice, we can build our weakly increasing infinite sequence"* — which is the
  step `exists_monotone_subseq` plays above. Open induction (Berger) is second-hand and not held.
