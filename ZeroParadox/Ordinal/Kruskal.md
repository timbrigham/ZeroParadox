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

Mathlib does not contain Kruskal's tree theorem — **not located as of 2026-08-22**, searched by
concept, by name, and by the inverse phrasing (its `Kruskal*` lemmas are Kruskal-Katona, an
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
proofs, stated over **almost-full relations** (Coquand) and **bar inductive predicates**
(Fridlender). ⚠ These are *reformulations* of the minimal-bad-sequence argument, not replacements
for it: Coquand & Fridlender describe their 1993 constructive Higman's lemma (stated for a
two-letter alphabet) as *"a constructive version of Nash-Williams' proof"*. Note also that **bar
inductive predicates are not Brouwer's bar induction**, which is the principle Veldman's proof rests
on.

Larchey-Wendling's *Coq-Kruskal* is a mechanized, **axiom-free**, unrestricted proof of the tree
theorem in the almost-full formulation, with no decidability assumption on the ground relation and no
Brouwer's Thesis. ⚠ It is not a different *argument* from Veldman's — *"Our proof follows the pattern
of Veldman's"* — the delta is the **formulation**. It removes the restrictions of the two earlier
intuitionistic proofs: Seisenberger's, via an inductive characterization of well-quasi-orders
(*Kruskal's Tree Theorem in a Constructive Theory of Inductive Definitions*, Synthese Library 306,
2001), which assumes decidability of the ground relation; and Veldman's (*An intuitionistic proof of
Kruskal's theorem*, Arch. Math. Logic 43(2), 2004, pp. 215-264), which uses Brouwer's Thesis.

⚠ **That the formulation is the delta is exactly why the axiom-free result does not transfer to
`Kruskal.lean`** — see the footprint section below.

## The `Classical.choice` footprint — and why its eliminability here is an OPEN QUESTION

What is measured: `Kruskal.lean` inherits `Classical.choice` through Mathlib's minimal-bad-sequence
machinery. This file does not build a constructive route; it uses Mathlib's. The residual content of
the minimal bad sequence argument is dependent choice / open induction (Berger), a choice principle,
not a logical taboo.

⚠ **What is NOT established: that the choice is eliminable from *this* statement.** That is an open
question, not a result, and it is NOT claimed here. The obstruction is that "well-quasi-ordered" has two
formulations which are classically equivalent and **intuitionistically inequivalent** — Larchey-Wendling's
own abstract: *"the several classically equivalent definitions of the notion of WQO are (for most of
them) not intuitionistically equivalent. Hence, the statement of the theorem depends
(intuitionistically) on the choice of a particular definition."*

- **Sequential** — for every infinite sequence, some later term embeds an earlier one. This is
  Mathlib's `WellQuasiOrdered` / `Set.PartiallyWellOrderedOn`, and it is what `Kruskal.lean` proves.
- **Almost-full (`af`)** — an inductive predicate, a finite constructive certificate. This is what
  Coq-Kruskal proves: `af R → af (ltree_homeo_embed R)`.

`af` is **constructively stronger**: sequential follows from it, not the reverse. So transferring
Coq-Kruskal's axiom-free result to the statement in `Kruskal.lean` would require `sequential → af` on
the *hypothesis* side — exactly the direction that is not constructively available, and exactly what
Brouwer's Thesis was postulated for in Veldman's proof. **The axiom-free witness therefore does not
discharge the claim about this file's theorem.**

Status: **open**, not refuted. The type is axiom-free, so nothing structurally forbids a clean proof;
what is missing is a constructive proof of the *sequential* form, or a reduction showing there is
none. Falsifier: a choice-free proof of `Set.univ.PartiallyWellOrderedOn r → … (TreeEmbeds r)` in
Lean, or a taboo reduction from it.

**Berger** is credited here for one thing only: the residual dependent choice / open induction in the
minimal-bad-sequence argument. He is not the source of the almost-full technique (that is Coquand),
and Synthese Library 306 (2001) is Seisenberger's volume.
