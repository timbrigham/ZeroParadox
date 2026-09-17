# Prior art and fences for `PoleRegistration.lean`

Ride-along for `ZeroParadox/Valuation/PoleRegistration.lean`. Written 2026-09-16 after
`/prior-art-review` returned FAIL-BEDROCK on the file carrying zero external references.

## The object already has a name: the Sierpiński domain

`Part Unit` is a proposition packaged with a map into the one-element type — the **type of truth
values**, the Sierpiński domain of constructive domain theory. So `PoleDiscriminator` is not a
statement about partiality at all. It says a `Bool`-valued test decides **every proposition**, and
the two `example`s in § II prove that, both directions:

- `PoleDiscriminator ↔ ∃ d : Prop → Bool, ∀ p, d p = true ↔ p` — the `Part` packaging is inert.
- `PoleDiscriminator → ChoiceFragment` and `ChoiceFragment → PoleDiscriminator`, both as `example`s
  in § II. So § II's hypothesis and the one already in
  `ZeroParadox/Category/ExcludedMiddleBridge.lean` are **inter-derivable**, not two principles.

**The return leg runs on the chooser's DATA, and uses no excluded middle at all.** Diaconescu's two
predicates are each constructively inhabited, so `decide (ch A = ch B)` is already data.
`em_of_choiceFragment` plays no part: it runs `ChoiceFragment → ExcludedMiddle`, forward, and
composing it with the first bullet would run forward twice and never return.

**What the two legs establish is COST, not the arrows.** Both sides are theorems of the ambient
system, so the inter-derivability alone is near-vacuous — `poleDiscriminator_of_classical` proves
`PoleDiscriminator` outright, which makes *every* implication into it available at
`[propext, Classical.choice, Quot.sound]`. The content is that both legs are **choice-free** —
measured 2026-09-17 by naming the anonymous `example`s: forward `[propext]`, return
`[propext, Quot.sound]`, and the inert-packaging leg at no axioms at all — and that
`PoleDiscriminator` is the pole vocabulary for `ChoiceFragment` —
the relationship `uniformChartSelection_iff_choiceFragment` already records for chart selection, and
already stated in prose at `ExcludedMiddleBridge.lean` and `ChoiceCannotBe.lean`. Witnessed here,
not discovered here.

⚠ **A failed elaboration measures a CONSTRUCTION, never a route** — and it is the axiom budget, never
the arrow, that is ever in question here. The natural construction of a discriminator from excluded
middle alone does not elaborate, dying at `Decidable x.Dom`; that is a fact about the construction.
Whether `PoleDiscriminator` follows from excluded middle **choice-free** is not settled in this file,
and no failed elaboration could settle it.

**§ II does NOT remove the stipulation `PoleChartSelection.em_of_uniformChartSelection` needs.**
`poleAdmissible` appears nowhere in that theorem's binders or proof term; its hypothesis is
`ChoiceFragment` by `Iff.rfl`, universally quantified over `S : Bool → Prop`. The narrower true
statement: this proof does not route through Diaconescu, a fact about proof structure and not about
strength.

## Sources, read at rung D

**T. de Jong, "Apartness, sharp elements, and the Scott topology of domains," MSCS 2023**
(arXiv:2106.05064v5), filed in `.claude-local/papers/`. Page 7, § 2.3, verbatim: *"decidable equality
on all of S is equivalent to excluded middle"*.

That sentence is an **equivalence of principles over a constructive base**, and this file proves one
of its two directions. `em_of_poleDiscriminator` runs decider → excluded middle, at no axioms at all.
`poleDiscriminator_of_classical` supplies the source end **classically**, so the implication is not
vacuous; it is an unconditional theorem spending `Classical.choice`, **not** the constructive
converse, which §§ above leave open. **The taboo is his, not ours.**

Definition 15 (p. 6) is where `Part Unit` gets its name: *"The Sierpiński
domain S is the free pointed dcpo on a single generator… realize S as the set of truth values."*

**The principle has a standard name too, and it is topos-theoretic.** § II's inert-packaging
`example` proves `PoleDiscriminator ↔ ∃ d : Prop → Bool, ∀ p, d p = true ↔ p`, at no axioms at all.
The topos-theoretic counterpart of that statement is **"the subobject classifier Ω is decidable"**,
equivalently **Ω ≅ 1 + 1**, equivalently **the topos is Boolean**. **C. Berger and V. Iwaniack, "On
the profinite fundamental group of a connected Grothendieck topos"** (arXiv:2304.05338v6), filed,
**Lemma 1.2**, read at the PDF: *"The following four conditions on a topos are equivalent: (1) all
subobjects are complemented; (2) all objects are decidable; (3) the subobject classifier Ω is
decidable; (4) the inclusion (⊤,⊥) : 1 + 1 ↣ Ω is an isomorphism."*

⚠ **No originator is asserted here.** Berger–Iwaniack open that section *"This section is a review of
known properties of decidable objects, see Acuña-Linton"* — **O. Acuña-Ortega and F. E. J. Linton,
"Finiteness and Decidability I," Lect. Notes Math. 753 (1979), 80–100** — and cite Johnstone's
*Elephant* elsewhere but not for this lemma. nLab attributes the equivalences to Johnstone, *Sketches
of an Elephant* A4.5.22; that is **not read here and not corroborated by the source that is**.

⚠ **In a topos those four are EQUIVALENT; this file proves one direction.** The converse is exactly
what §§ above leave open, and the reason is the `Prop`/`Type` stratification — a `Bool`-valued
decider is data, `ExcludedMiddle` is `Prop`-valued, and a topos has no such split. The canonical
statement of that fence is `ZeroParadox/Category/ExcludedMiddleBridge.lean`'s `ChoiceFragment`
docstring; it is not restated here.

**T. de Jong and M. H. Escardó, "Predicative Aspects of Order Theory in Univalent Foundations,"
FSCD 2021** (arXiv:2102.08812v5) and *"On Small Types in Univalent Foundations"* (arXiv:2111.00482v5,
LMCS 2023), both filed. Same neighbourhood, and **this file makes no claim about what either proves**
— a previous version characterised their Corollary 39 / Theorem 42 and that characterisation was
withdrawn as unverified. Read them before citing them.

**C. Knapp, "Partial Functions and Recursion in Univalent Type Theory," 2020** (arXiv:2011.00272),
filed. **Definition 5.17** (p. 92): a *dominance* is a **set of propositions** `d : U → U` closed
under the unit type and conditional conjunction — the notion is Rosolini's. Knapp lists three
*trivial* examples with their liftings, and two of them are the objects in play here:
`L_{d₂}(X) = X + 1` is `Option X`, and `L_{d_Ω}(X) = L(X)` is `Part X`. So **`Option` and `Part` are
liftings of dominances, not dominances**, and "the Rosolini dominance" is a third object again —
the semidecidable propositions (§ 5.7). § IV of the Lean file exhibits the Mathlib half
(`Part.ofOption` total and instance-free, `Part.toOption` carrying `[Decidable o.Dom]`,
`Part.equivOption` noncomputable). **Exhibited, never discovered here.**

## The end-selection pairing is NOT this framework's

**That which end the discriminator sits on decides which taboo you get — bottom end giving the weak
form, defined end the full one — is prior art in constructive and predicative domain theory.** This
file claims no part of it. § II proves one instance of the top-end half, at `Part Unit`, as an
implication.

**The closest prior art for `em_of_poleDiscriminator` is de Jong 2023's Proposition 63**, read at the
PDF 2026-09-17. Proposition 62 (p. 15): *"An element x of an algebraic dcpo D is sharp if and only if
for every compact c ∈ D it is decidable whether c ⊑ x holds."* Proposition 63 (p. 15): *"The sharp
elements of the Sierpiński domain S are exactly ⊥ and ⊤. Hence, if every element of S is sharp, then
excluded middle follows"* — and from its proof, *"an element x ∈ S is sharp if and only if
⊤ = {∗} ⊑ x is decidable."* In `Part Unit`, `⊤ ⊑ x` **is** `x.Dom`, so the two together state the
taboo `em_of_poleDiscriminator` proves. What is added here is the machine-checked instance at
`Part Unit`, wired to ZP-K's floor — an instance joining his programme, never a generalization of it.

⚠ **No strength comparison is claimed between the two ends.** Against de Jong's Proposition 22
instantiated at S, § II's hypothesis is the **stronger** one: the top-end test gives full excluded
middle, which gives the bottom-end test, while the converse would need weak excluded middle to imply
excluded middle, unavailable constructively. A stronger conclusion from a stronger hypothesis is
unremarkable. No separating model is exhibited, so no inequivalence is asserted.

## What actually survives, stated as what it is

A clean, **choice-free Lean formalization of known results, wired to ZP-K's floor.** Infrastructure
value, no novelty claim. Three things are genuinely here:

1. **The top-end instance, machine-checked at `Part Unit`.** `em_of_poleDiscriminator` depends on **no
   axioms at all**, and `poleDiscriminator_of_classical` supplies the source end so the implication is
   not vacuous. A formalization, not an observation.
2. **A modesty result, WITNESSED here and stated in prose elsewhere already.** `PoleDiscriminator`
   and the corpus's own `ChoiceFragment` are inter-derivable, both legs now `example`s in § II, and
   both choice-free. So § II introduces **no new principle** — it is the pole vocabulary for a
   hypothesis the corpus already had. ⚠ Not a discovery: `ExcludedMiddleBridge.lean` and
   `ChoiceCannotBe.lean` already say in prose that `ChoiceFragment` is really `∀ p, Decidable p`.
   What is added is the machine-checked witness, not the observation.
3. **The consequence at the computational floor**, § III: what § II costs constructively, ZP-K's floor
   cannot buy at any price — no *computable* discriminator decides self-application, by reduction to
   `self_halting_undecidable`.

## The two-pole reading (`R-TWOPOLE`), run rather than assumed

**Q1 — where is the zero that runs to infinity?** In the `Dom` field. `Option` registers the point at
infinity as a **constructor**, so "am I at infinity?" is decided by pattern-matching — finite, uniform
in the carrier, no instance required. `Part` holds an arbitrary **proposition** there, so the same
question ranges over all of `Prop`. One slot, and the whole of logic fits inside it: that is the zero
that runs to infinity in this chart.

**Q2 — the one-way arrow, and backwards?** `Part.ofOption` is total and instance-free; `Part.toOption`
takes `[Decidable o.Dom]` and `Part.equivOption` is `noncomputable`. **Forgetting registration is
free; registering costs a decision.** Run backwards, the arrow is exactly the taboo: demand the return
map uniformly and you have demanded excluded middle.

⚠ **Applied to the retraction itself, which is what `R-TWOPOLE` is for.** Stated in the other chart,
the deleted claim reads: *the bottom-end condition and the top-end condition force the same taboo, and
the end makes no difference.* **The literature settles that, and settles it AGAINST that reading** —
in someone else's names, not ours. de Jong 2023's Proposition 22 (p. 7) takes the **bottom** end:
*"If y = ⊥ is decidable for every y ∈ D, then weak excluded middle follows."* Proposition 63 (p. 15)
takes the **defined** end and gets **full** excluded middle. One paper, one author, two ends, **two
different taboos** — so the end does make a difference. Both read at the PDF 2026-09-17. So the defect
here is **not** a missing chart, and the fix is a citation rather than a second pole. Recorded so a
later round does not re-add the starred sentence in the belief that a pole is absent.

⚠ **Tim's read is load-bearing on one point**: whether this file earns a place in
`ZeroParadox/BottomCannotBe.lean`'s index at all, now that its only novelty claim is withdrawn and
what remains is a formalization of cited results plus one witnessed modesty result. That is a
judgement about what the index is for, not a fact the Lean can settle.

## Vocabulary

"Sierpiński domain" and "dcpo" were **not located outside this file and its `.lean` as of
2026-09-17**, searched with `python tools/verify/check_paths.py --full --claim` over 472 tracked
surfaces including 40 rendered PDFs: the stem `Sierpi` at 9 sites, `dcpo` at 2, all inside the two
files. The sweep runs on the **stem**, which catches both spellings in one pass — see below.

⚠ **A claim about the WORDS, not about the ideas.** The same instrument finds "Scott domain" in
`ZP-R_Cross_Category_Fixed_Point.pdf` and `ZeroParadox/Valuation/PricedPadicInterface.md`, so the
domain-theoretic neighbourhood was in the corpus before this file was; only this vocabulary is new.

⚠ **Grep an accented name BOTH ways.** `Sierpiński` and `Escardó` do not match sweeps written
`Sierpinski` and `Escardo`, and an absence measured with the unaccented form reports zero for the
wrong reason.
