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

⛔ **An earlier version named `em_of_choiceFragment` as closing the return leg. It does not, and the
claim was corrected 2026-09-16 by building the real proof.** That theorem runs
`ChoiceFragment → ExcludedMiddle`, forward; composing it with the first bullet runs forward twice and
never returns. The return leg is built instead from the **data** the fragment carries — the chooser
`ch` — with excluded middle used only to inhabit the predicate, a `Prop`-valued side condition.
Measured at the artifact: the leg elaborates at `[propext, Quot.sound]`, and the route the old comment
named, `ExcludedMiddle → PoleDiscriminator`, fails at `failed to synthesize Decidable x.Dom` —
verbatim the `Prop`/`Type` stratification barrier `ExcludedMiddleBridge.lean` records as its own
headline finding. Both runs are in the session log, not inferred from the comment.

**The consequence is a modesty result, and it is the useful half.** `PoleDiscriminator` is the pole
vocabulary for `ChoiceFragment` at a different carrier — the same relationship
`uniformChartSelection_iff_choiceFragment` already records for the chart-selection principle.
Renaming a hypothesis does not make it true.

⛔ **An earlier gloss claimed § II "removes the stipulation" that
`PoleChartSelection.em_of_uniformChartSelection` needs. That was false** and is corrected in place.
`poleAdmissible` appears nowhere in that theorem's binders or proof term; its hypothesis is
`ChoiceFragment` by `Iff.rfl`, universally quantified over `S : Bool → Prop`. The surviving true
half is narrower: this proof does not route through Diaconescu, which is a fact about proof
structure and not about strength.

## Sources, read at rung D

**T. de Jong, "Apartness, sharp elements, and the Scott topology of domains," MSCS 2023**
(arXiv:2106.05064v5), filed in `.claude-local/papers/`. Page 7, § 2.3, verbatim: *"decidable equality
on all of S is equivalent to excluded middle"*; Proposition 22 gives the weak-excluded-middle form.
That sentence is `em_of_poleDiscriminator` together with `poleDiscriminator_of_classical`. **The
taboo is his, not ours.** Definition 15 (p. 6) is where `Part Unit` gets its name: *"The Sierpiński
domain S is the free pointed dcpo on a single generator… realize S as the set of truth values."*

**T. de Jong and M. H. Escardó, "Predicative Aspects of Order Theory in Univalent Foundations,"
FSCD 2021** (arXiv:2102.08812v5), filed. **Theorem 42** (p. 12) and **Corollary 39** (p. 11) pair the
two ends with the two taboos, as matched biconditionals: a locally small poset with decidable equality
that is *nontrivial* exists **iff** weak excluded middle holds, and one that is *positive* exists
**iff** excluded middle holds. Definition 40 supplies the axis — *nontrivial* is the negative
(⊥-side) form, *positive* its inhabited counterpart. Same result as Theorem 4.31 / Theorem 4.26 in
their *"On Small Types in Univalent Foundations"* (arXiv:2111.00482v5, LMCS 2023), also filed.

**C. Knapp, "Partial Functions and Recursion in Univalent Type Theory," 2020** (arXiv:2011.00272),
filed. **Definition 5.17** (p. 92): a *dominance* is a **set of propositions** `d : U → U` closed
under the unit type and conditional conjunction — the notion is Rosolini's. Knapp lists three
*trivial* examples with their liftings, and two of them are the objects in play here:
`L_{d₂}(X) = X + 1` is `Option X`, and `L_{d_Ω}(X) = L(X)` is `Part X`. So **`Option` and `Part` are
liftings of dominances, not dominances**, and "the Rosolini dominance" is a third object again —
the semidecidable propositions (§ 5.7). § IV of the Lean file exhibits the Mathlib half
(`Part.ofOption` total and instance-free, `Part.toOption` carrying `[Decidable o.Dom]`,
`Part.equivOption` noncomputable). **Exhibited, never discovered here.**

## ⛔ RETRACTED: the end-selection "delta" was never ours

**An earlier version of this file starred the following as the framework's own observation:**
*"Which END the discriminator sits on decides which taboo you get — de Jong places it at the bottom
end and obtains weak excluded middle; § II places it at the defined end and obtains full excluded
middle."*

**That is de Jong–Escardó 2021, Corollary 39 and Theorem 42**, stated four years earlier, more
strongly (two matched biconditionals rather than one implication), over a whole class of posets
rather than one carrier, by authors this file already cited. Retracted 2026-09-16. It is an instance
joining that programme, not a delta over it.

⚠ **"Strictly weaker" is retracted with it, and it pointed the wrong way.** Against de Jong's
Proposition 22 instantiated at S — the comparison that sentence itself set up — § II's hypothesis is
**stronger**: the top-end test gives full excluded middle, which gives the bottom-end test, while the
converse would need weak excluded middle to imply excluded middle, which is unavailable
constructively. A stronger conclusion from a stronger hypothesis is unremarkable and is not claimed.
No separating model is exhibited anywhere in this file, so no inequivalence is asserted either.

**How the error got in, recorded because the shape recurs.** The pointer to Corollary 39 sits three
lines below a sentence this file already quotes — de Jong 2023 p. 7, immediately after Proposition 22:
*"we showed in (de Jong and Escardó, 2021b, Corollary 39) that this implies (weak) excluded middle,
unless the dcpo is trivial."* The first review round logged that pointer as *"Not retrieved"* and the
remediation shipped the starred claim anyway. The rung that verifies — retrieve and read the document —
was skipped at exactly the place it was load-bearing.

## What actually survives, stated as what it is

A clean, **choice-free Lean formalization of known results, wired to ZP-K's floor.** Infrastructure
value, no novelty claim. Three things are genuinely here:

1. **The top-end instance, machine-checked at `Part Unit`.** `em_of_poleDiscriminator` depends on **no
   axioms at all**, and `poleDiscriminator_of_classical` supplies the source end so the implication is
   not vacuous. A formalization, not an observation.
2. **A modesty result that did not exist before.** `PoleDiscriminator` and the corpus's own
   `ChoiceFragment` are inter-derivable, both legs now `example`s in § II. So § II introduces **no new
   principle** — it is the pole vocabulary for a hypothesis the corpus already had.
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
the end makes no difference.* That is false, and de Jong–Escardó's Theorem 42 is precisely what
settles it — in **their** names, not ours. So the defect here is **not** a missing chart, and the fix
is therefore a citation, not a second pole. Recorded so a later round does not re-add the starred
sentence in the belief that a pole is absent.

⚠ **Tim's read is load-bearing on one point**: whether this file earns a place in
`ZeroParadox/BottomCannotBe.lean`'s index at all, now that its only novelty claim is withdrawn and
what remains is a formalization of cited results plus one modesty result. That is a judgement about
what the index is for, not a fact the Lean can settle.

## Not located

"Sierpinski", "dcpo" and "lifting monad" appeared at **0 sites across 471 tracked surfaces**
including 40 rendered PDFs, measured 2026-09-16 with `check_paths.py --full --claim`. So this
vocabulary enters the corpus here, and a reader looking for the standard names will not find them
anywhere earlier. Not a claim that the ideas are absent — a claim about the words, with the
instrument named.
