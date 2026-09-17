# Prior art and fences for `PoleRegistration.lean`

Ride-along for `ZeroParadox/Valuation/PoleRegistration.lean`. Written 2026-09-16 after
`/prior-art-review` returned FAIL-BEDROCK on the file carrying zero external references.

## The object already has a name: the Sierpiński domain

`Part Unit` is a proposition packaged with a map into the one-element type — the **type of truth
values**, the Sierpiński domain of constructive domain theory. So `PoleDiscriminator` is not a
statement about partiality at all. It says a `Bool`-valued test decides **every proposition**, and
the two `example`s in § II prove that, both directions:

- `PoleDiscriminator ↔ ∃ d : Prop → Bool, ∀ p, d p = true ↔ p` — the `Part` packaging is inert.
- `PoleDiscriminator → ChoiceFragment`, with `em_of_choiceFragment` closing the return leg. So § II's
  hypothesis and the one already in `ZeroParadox/Category/ExcludedMiddleBridge.lean` are
  **inter-derivable**, not two principles.

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
taboo is his, not ours.**

**C. Knapp, "Partial Functions and Recursion in Univalent Type Theory," 2020** (arXiv:2011.00272),
filed. The `Option`/`Part` pair — a class of propositions closed under the operations that make
partial functions compose — is a **dominance**, due to Rosolini. § IV of the Lean file exhibits the
Mathlib half (`Part.ofOption` total and instance-free, `Part.toOption` carrying
`[Decidable o.Dom]`, `Part.equivOption` noncomputable). **Exhibited, never discovered here.**

## What is actually ours, and its fence

⭐ **Which END the discriminator sits on decides which taboo you get.** de Jong places it at the
BOTTOM end (`y = ⊥`) and obtains *weak* excluded middle. § II places it at the DEFINED end (`Dom`)
and obtains *full* excluded middle, from a hypothesis that is strictly weaker (`Part Unit` rather
than an arbitrary carrier).

⚠ **FENCE, and it is load-bearing: the two ends are NOT shown inequivalent here.** This is a delta
between two cited results, never a no-go. Proving that the bottom-end discriminator cannot reach
full excluded middle would need a model separating the two taboos, and no such model is exhibited.
Read it as a difference in what each hypothesis has been shown to buy, not as a proved separation.

⭐ The reading that makes this a ZP result rather than a curiosity is `R-TWOPOLE`'s: the same
apparatus interrogated at the top and at the bottom returns two different strengths. The standard
framing handed that to the framework rather than the other way round — the file did not notice it
until the literature was read.

## Not located

"Sierpinski", "dcpo" and "lifting monad" appeared at **0 sites across 471 tracked surfaces**
including 40 rendered PDFs, measured 2026-09-16 with `check_paths.py --full --claim`. So this
vocabulary enters the corpus here, and a reader looking for the standard names will not find them
anywhere earlier. Not a claim that the ideas are absent — a claim about the words, with the
instrument named.
