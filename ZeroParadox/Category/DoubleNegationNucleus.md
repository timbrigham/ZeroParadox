# The excluded-middle modality: its credit, its choice-free footprint, and what it is not

Ride-along for `ZeroParadox/Category/DoubleNegationNucleus.lean`: its long header. The Lean file holds
the declarations, the Engineer's Take and the per-declaration docstrings; where the two overlap, the
Lean is authoritative.

Everything below is the Lean file's long header, moved, with edits at the attribution sites. In it,
"this file", "here", "below" and "this file's one proved lemma" refer to
`ZeroParadox/Category/DoubleNegationNucleus.lean`.

## Formal Overview (AI-assisted)

`ZeroParadox/Category/DifferenceGeneratesSystem.lean` identifies "a predicated difference generates a system" with the
nucleus/sublocale (Lawvere–Tierney) machinery, and machine-checks with `example`s that double negation
sends the constructive base into the classical (Boolean) core. This file builds the **object** those
examples were about: the double-negation map `a ↦ aᶜᶜ` as a genuine `Nucleus` on any Heyting algebra.

This is the exact parallel to `snapNucleus` (`ZeroParadox/Ordinal/SnapNucleus.lean`). Both are concrete
difference-generators — inflationary, idempotent, meet-preserving modalities — of two of the framework's
threads: the **snap** (the ordinal difference `α ↦ ω^α`, generating ε₀) and **double negation** (the
logical difference `a ↦ aᶜᶜ`, generating the classical core). Applying the modality collapses to the
classical core: `aᶜᶜ` is the element after excluded middle has settled it to a definite value. The
generated system — the nucleus's closed points — is exactly the **regular elements** `{a | aᶜᶜ = a}`, the
Boolean core (`Heyting.Regular`).

**Honest scope / credit outward.** The double-negation nucleus is textbook: it is the Boolean (¬¬-dense)
subtopos / the Lawvere–Tierney topology whose sheaves are the classical objects, and its regular-element
core is Glivenko's theorem in algebraic form. Mathlib carries the pieces (`le_compl_compl`,
`compl_compl_compl`, `Heyting.Regular`) but not the packaged `Nucleus`; this file only assembles it, as
the excluded-middle / classical-collapse modality, parallel to the snap. It states no new theorem of the
general theory — every ingredient is a known intuitionistic fact about Heyting algebras.

**The constructive footprint (the point of this file's one proved lemma).** The assembled nucleus has
axiom footprint `[propext]` — no `Classical.choice`, no `Quot.sound`. That did not come for free.
Mathlib's `compl_compl_inf_distrib` proves meet-preservation via `sup`/`compl_sup_distrib` and so reports
`Classical.choice`; `dneg_inf_distrib` below re-proves it using only the meet side, dropping the footprint
to `[propext]`. The result: **the modality that generates classical logic is itself built with no
classical input** — where "generates classical logic" means precisely that its closed points are the
regular elements, the Boolean core, and nothing more (see the Fence below). This matters here
specifically because of the direction of Diaconescu's theorem —
choice implies excluded middle, and Lean's own kernel derives `Classical.em` from `Classical.choice`
(`Init/Classical.lean`, whose docstring calls it "Diaconescu's theorem") by a two-predicate argument. So a proof of the excluded-middle modality that leaked `Classical.choice` was
tacitly routing through Diaconescu to build the very thing Diaconescu delivers. Cutting that path is what
makes the construction's independence a real statement rather than a circular one.

**Fence.** `[propext]` is a fact about *this construction*, not about excluded middle. That `a ↦ aᶜᶜ` is a
nucleus on any Heyting algebra is an intuitionistic theorem; it does not make excluded middle
constructively valid, and the closed points are the regular elements precisely because the base in general
is *not* Boolean. Nothing here derives LEM, and nothing here bears on whether any framework theorem
*requires* it (that is the essential-vs-accidental question, tracked separately).

**What this is and is NOT (the excluded-middle / choice distinction).** This modality generates classical
*logic* — excluded middle. It is NOT the axiom of *choice*: **full** choice is strictly stronger, which is
Cohen's 1963 independence result (with Fraenkel–Mostowski), **not** Diaconescu's. What Diaconescu (1975)
proved is an *equivalence* between two topos properties (p. 176), and it already concerns a two-point
shape; the analogue in intuitionistic set theory is Goodman–Myhill (1978), who state the restriction
explicitly, choice "for sets B, C of at most two elements" (p. 461). With unique choice into `Bool`,
`ChoiceFragment` and `ExcludedMiddle` are inter-derivable (the `example` after `em_of_choiceFragment` in
`ZeroParadox/Category/ExcludedMiddleBridge.lean`). Attributing "the converse fails" to Diaconescu is a misreading; see
`ZeroParadox/Category/ChoiceCannotBe.lean` for the full statement and for why the restricted fragment
nonetheless comes apart from excluded middle in Lean specifically. The framework's conversational
"choice = which way you view the self-dual split" reading is the looser, informal thread — discussed in
`ZeroParadox/Category/DifferenceGeneratesSystem.lean`, not asserted here; the object built here is the double-negation
(excluded-middle) nucleus, nothing stronger.

**Correction of record: this file once made that error itself.** It was originally titled "Choice as a
difference-generator" and named this object the framework's *choice modality*. That was wrong — choice is
strictly stronger than what `a ↦ aᶜᶜ` delivers — and it was corrected in commit `655c761` off an adversary
kill-list. Recorded here rather than quietly rewritten, because a reader checking the framework's claims
is entitled to know which ones it previously got wrong. The arrow that actually connects the two is built
in `ZeroParadox/Category/ExcludedMiddleBridge.lean`.
