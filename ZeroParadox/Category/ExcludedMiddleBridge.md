# Why the arrow is scoped to `Prop`, how the instance is pinned, and whose argument it is

Ride-along for `ZeroParadox/Category/ExcludedMiddleBridge.lean`: its long header. The Lean file holds
the declarations, the Engineer's Take and the per-declaration docstrings; where the two overlap, the
Lean is authoritative.

Everything below is the Lean file's long header, moved. In it, "this file", "here", "below", "the
bottom" and every § number refer to `ZeroParadox/Category/ExcludedMiddleBridge.lean`.

## Formal Overview (AI-assisted)

`Category/DoubleNegationNucleus.lean` builds `dnegNucleus X : Nucleus X`, the map `a ↦ aᶜᶜ` on any
Heyting algebra, choice-free (`[propext]`), whose closed points are the regular elements
(`dnegNucleus_isClosed_iff`). It is the **excluded-middle** modality, not the choice modality.

This file builds the arrow that separates those two, in three steps and a fence.

**The scope constraint — read this before reading any statement below.** Excluded middle does **not**
make an arbitrary Heyting algebra Boolean. It makes the **`Prop`** Heyting algebra Boolean. Every
statement in §§ I-III is therefore scoped to `Prop`, and § IV machine-checks that the general claim
fails: a concrete Heyting algebra, exhibited inside Mathlib's classical metatheory (so with excluded
middle fully available), carrying an element with `aᶜᶜ ≠ a`. The nucleus stays nontrivial there. The
general statement "excluded middle collapses the double-negation nucleus" is FALSE and is not asserted
anywhere in this file.

**Correction of record.** This file was first drafted in exactly that general (wrong) form — "choice →
excluded middle → the double-negation nucleus is trivial", unscoped — and the `Prop`-vs-arbitrary-Heyting
distinction was caught before it was built. § IV exists because of that near-miss, which is why the fence
is the load-bearing part of the file rather than a footnote. Recorded rather than quietly avoided.

**The instance hazard, and how it is handled.** `Prop` carries two relevant instances:
`Prop.instHeytingAlgebra` (Mathlib/Order/Heyting/Basic.lean) and `Prop.instBooleanAlgebra`
(Mathlib/Order/BooleanAlgebra/Defs.lean). The Boolean one discharges its `top_le_sup_compl` field with
`Classical.em`, so **it carries `Classical.choice` in its own term**. If `dnegNucleus Prop` or
`Heyting.IsRegular (p : Prop)` were allowed to resolve through the Boolean instance, every theorem here
would silently pick up choice and the whole point — that the choice → excluded middle arrow is a real
implication and not an identity — would be lost. Every `Prop`-scoped statement below therefore **pins the
instance explicitly** as `@… Prop Prop.instHeytingAlgebra`. The measured footprints of both instances are
recorded in the purity-check section at the bottom.

**Prior art — the framework claims only the packaging.** § II is Diaconescu's theorem (Diaconescu 1975,
"Axiom of choice and complementation"; adapted to intuitionistic set theory by Goodman-Myhill 1978,
"Choice implies excluded middle"). It is not a new result and is not claimed as one. A search of Mathlib and the other `.lake`
dependencies found **no** hypothesis-form statement of it (no `Diaconescu`, no `em_of_choice`); Lean's own
kernel realizes the arrow concretely — `Classical.em` is *derived* from `Classical.choice`
(`Init/Classical.lean`, whose docstring calls it "Diaconescu's theorem") by the two-predicate argument
§ II adapts to `Bool` — but as a derivation of the classical axioms, not as a reusable theorem taking the
choice principle as a hypothesis. This file supplies that hypothesis form so the arrow can be composed
with § I. § I and § IV are elementary and equally not new; the contribution is the assembly.

**A correction to how this file first stated its prior art (2026-07-19).** It originally said Diaconescu
proved "choice ⇒ excluded middle, one direction only, converse fails." That is wrong twice over. First,
Diaconescu's theorem is an **equivalence** — a coequalizer of two nonintersecting monomorphisms has a
section *iff* subobjects have complements (1975, p. 176), the choice direction being his corollary
(p. 178). The two-element restriction is Goodman-Myhill's (1978, p. 461: choice "for sets B, C of at
most two elements"); read as an equivalence, choice for inhabited subobjects of a two-element object
**is** excluded middle, a gloss stated on neither page.
Second, that *full* AC is strictly stronger than excluded middle is **Cohen 1963** / Fraenkel–Mostowski
independence, not Diaconescu.
**This matters here because `ChoiceFragment` has exactly that two-element restricted shape** — choice for
inhabited predicates on `Bool` — so in a topos it would be equivalent to `ExcludedMiddle`, and the
faithfulness check below would have to fail. It does not fail. The reason is that Lean stratifies `Prop`
and `Type`: `ChoiceFragment` selects into `Bool`, making it data-valued excluded middle
(`∀ p, Decidable p`), while `ExcludedMiddle` is the `Prop`-valued form, and `Or` in `Prop` does not
eliminate into `Bool`. A topos has no such split. **So the one-way-ness measured below is a fact about
Lean's stratification, and is this file's own small finding — not, as first written, a restatement of
Diaconescu.**

**No new axioms.** The choice principle in § II is a `def ... : Prop` hypothesis, discharged by the caller.
Nothing here is declared `axiom`, and nothing here uses `sorry`.

## Structure

- § I   Excluded middle ↔ every `Prop` is regular ↔ the `Prop` double-negation nucleus is the identity
- § II  Diaconescu: a choice fragment (as a hypothesis) implies excluded middle
- § III Composition: the choice fragment collapses the `Prop` nucleus
- § IV  The fence: a concrete Heyting algebra that is NOT Boolean, in the classical metatheory
