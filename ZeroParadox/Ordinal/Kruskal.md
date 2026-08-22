# Kruskal's Tree Theorem (labeled) — what is reused, what is built, and the choice footprint

Ride-along documentation for `ZeroParadox/Ordinal/Kruskal.lean`.

## What is reused vs. built

Mathlib supplies the heavy reusable engine, on which this file builds (and which it cites, not
re-proves):

- `Set.PartiallyWellOrderedOn` — the WQO predicate (`Mathlib.Order.WellFoundedSet`).
- `Set.PartiallyWellOrderedOn.IsBadSeq` / `exists_min_bad_of_exists_bad` — the Nash-Williams minimal
  bad sequence construction.
- `Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂` — **Higman's lemma** (lists under
  `List.SublistForall₂` are WQO when the alphabet is).

Mathlib does **not** contain Kruskal's tree theorem (its `Kruskal*` lemmas are Kruskal-Katona, an
unrelated set-family result). The rose-tree type, the embedding order, and the Nash-Williams assembly
on top of Mathlib's Higman are the original *formalization* content here; the mathematics is classical
and credited under Prior art below.

## Prior art — the theorem is classical

Kruskal's tree theorem (Kruskal 1960) and Higman's lemma (Higman 1952) are classical results; this file
formalizes the labeled tree theorem on Mathlib's WQO machinery. Two threads must be credited.

**The Nash-Williams route this file takes.** The minimal bad sequence argument is Nash-Williams
(1963). Mathlib's `exists_min_bad_of_exists_bad` / `minBadSeqOfBadSeq` is that argument, and it is
where `Classical.choice` enters — a `Nat.find` / `Classical.choose` selection over infinite bad
sequences, iterated by `Nat.rec`. Sternagel's Isabelle/HOL *Certified Kruskal's Tree Theorem* takes
the same classical route.

**The constructive route.** Kruskal's theorem and Higman's lemma both have choice-free constructive
proofs by a different technique — almost-full relations (Coquand) and bar induction (Fridlender) —
that avoid the minimal bad sequence argument entirely. Larchey-Wendling's *Coq-Kruskal* is a
mechanized, **axiom-free**, unrestricted proof of the tree theorem on that technique, with no
decidability assumption on the ground relation and no Brouwer's Thesis. It removes the restrictions of
the two earlier intuitionistic proofs: Seisenberger's, via an inductive characterization of
well-quasi-orders (*Kruskal's Tree Theorem in a Constructive Theory of Inductive Definitions*,
Synthese Library 306, 2001), which assumes decidability of the ground relation; and Veldman's (*An
intuitionistic proof of Kruskal's theorem*, Arch. Math. Logic 43(2), 2004, pp. 215-264), which uses
Brouwer's Thesis. Coquand & Fridlender (1993) give the constructive Higman's lemma.

## The `Classical.choice` footprint

The `Classical.choice` this file inherits through Mathlib's route is a route **artifact** rather than
a requirement of the theorem, and the witness is exhibited rather than asserted: Larchey-Wendling's
mechanized *Coq-Kruskal* is the axiom-free witness. This file does not build that route; it uses
Mathlib's. The residual content of the minimal bad sequence argument is dependent choice / open
induction (Berger), a choice principle, not a logical taboo.

⚠ **Two attribution errors were made in the note that grandfathered this claim, both while
correcting attributions.** (a) "Berger (Sternagel-style…)" — Sternagel takes the same **classical**
Nash-Williams route, not a constructive one; (b) then "Berger (almost-full relations, Synthese
Library 306, 2001)" — that volume is **Seisenberger's**. Berger is credited here only for the
residual dependent choice / open induction. Read this section before citing any of these again.
