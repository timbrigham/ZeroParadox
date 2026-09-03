# Kruskal's tree theorem: the reused engine, the prior art, and an open question about choice

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

Kruskal's tree theorem is **not located in the pinned Mathlib as of 2026-09-03**, searched by
name across `Mathlib/`: 32 hits in 5 files, every one under `Combinatorics/SetFamily/` (Colex, UV
compression, LYM, Shadow, KruskalKatona) — Kruskal-Katona, an unrelated set-family result. The rose-tree type, the embedding order, and the Nash-Williams assembly
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
- **The constructive route, and why it does not transfer to THIS statement.** Kruskal's theorem and
  Higman's lemma have choice-free proofs by a different technique — almost-full relations and bar
  induction (Coquand & Fridlender 1993). Larchey-Wendling's *Coq-Kruskal* is a mechanized,
  **axiom-free**, unrestricted proof of the tree theorem on that technique, with no decidability
  assumption and no Brouwer's Thesis, removing the restrictions of the earlier intuitionistic proofs:
  Seisenberger's (*On the Constructive Content of Proofs*, PhD thesis, Munich 2003), which assumes
  decidability of the ground relation, and Veldman's, which uses Brouwer's Thesis — both cited
  second-hand via Larchey-Wendling and not held here. — **It proves a DIFFERENT statement.**
  Coq-Kruskal establishes `af R — af (embed_tree_homeo R)` for the inductively defined almost-full
  predicate; this file proves the sequence form. Transport needs `WellQuasiOrdered r — af r`, and
  CCC2017 records that the classically equivalent WQO definitions are *"not intuitionistically
  equivalent"*. **So the axiom-free proof is evidence about the af formulation, not about this one,
  and whether the choice HERE is removable is UNMEASURED.** `Set.PartiallyWellOrderedOn` is
  axiom-free as a type, so the question is open rather than foreclosed. The residual content of the
  minimal bad sequence argument is dependent choice / open induction (Berger — second-hand, not held).
