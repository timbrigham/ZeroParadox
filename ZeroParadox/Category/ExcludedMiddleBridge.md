# Why the arrow is scoped to `Prop`, how the instance is pinned, and whose argument it is

Ride-along for `ZeroParadox/Category/ExcludedMiddleBridge.lean`: its long header. The Lean file holds
the declarations, the Engineer's Take and the per-declaration docstrings; where the two overlap, the
Lean is authoritative.

Everything below is the Lean file's long header, moved, with edits at the attribution sites. In it,
"this file", "here", "below" and every § number refer to `ZeroParadox/Category/ExcludedMiddleBridge.lean`.

## Formal Overview (AI-assisted)

`ZeroParadox/Category/DoubleNegationNucleus.lean` builds `dnegNucleus X : Nucleus X`, the map `a ↦ aᶜᶜ` on any
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
recorded in the purity-check section at the end of this file.

**Prior art — the framework claims only the Lean packaging.** § II is Diaconescu's argument (Diaconescu 1975,
"Axiom of choice and complementation"; the analogue in intuitionistic set theory is Goodman-Myhill
1978, "Choice implies excluded middle"). It is not a new result and is not claimed as one. A search of Mathlib and the other `.lake`
dependencies found **no** hypothesis-form statement of it (no `Diaconescu`, no `em_of_choice`); Lean's own
kernel realizes the arrow concretely — `Classical.em` is *derived* from `Classical.choice`
(`Init/Classical.lean`, whose docstring calls it "Diaconescu's theorem") by the two-predicate argument
§ II adapts to `Bool` — but as a derivation of the classical axioms, not as a reusable theorem taking the
choice principle as a hypothesis. Outside Lean the hypothesis form exists: the Rocq standard library's
`theories/Logic/Diaconescu.v` states the argument with the choice principle as a hypothesis, in three
variants. Its Part C, `extensional_epsilon_imp_EM`, takes an extensional choice operator as section
hypotheses (`epsilon_spec`, `epsilon_extensionality`) and runs it at `bool` on the predicates
`y = false \/ P` and `y = true \/ P`, the pair § II uses; its Part A, `prop_ext_and_rel_choice_imp_EM`,
takes relational choice and propositional extensionality. Closer still to `ChoiceFragment` is the
file's backward-compatibility section `PredExt_RelChoice_imp_EM`, which chooses through
`AC_bool_subset_to_bool` ("a functional relation which chooses an element in any non empty subset of
bool") on the same pair, in `pred_ext_and_rel_choice_imp_EM`. The file credits Part C to Bell (1993;
not read here). This file supplies the hypothesis form in
Lean, so the arrow can be composed with § I. § I and § IV are elementary and equally not new; the
contribution is the assembly.

**A correction to how this file first stated its prior art (2026-07-19).** It originally said Diaconescu
proved "choice ⇒ excluded middle, one direction only, converse fails." That is wrong twice over. First,
Diaconescu's theorem is an **equivalence** — a coequalizer of two nonintersecting monomorphisms has a
section *iff* subobjects have complements (1975, p. 176), the choice direction being his corollary
(p. 178). The theorem already concerns a two-point shape: such a coequalizer has fibres of at most two
points, and its proof runs over pp. 176-177. Goodman-Myhill state the restriction explicitly, choice
"for sets B, C of at most two elements" (1978, p. 461). With unique choice into `Bool`, `ChoiceFragment`
and `ExcludedMiddle` are inter-derivable (see `ZeroParadox/Category/ExcludedMiddleBridge.lean`, the `example`
after `em_of_choiceFragment`).
Second, that *full* AC is strictly stronger than excluded middle is **Cohen 1963** / Fraenkel–Mostowski
independence, not Diaconescu.
**This matters here because `ChoiceFragment` is a choice principle into the two-element `Bool`** — a
chooser on every inhabited predicate on `Bool` — so in a topos, where unique choice holds (see
`ZeroParadox/Category/ExcludedMiddleBridge.lean`, the `example` after `em_of_choiceFragment`), it would be equivalent to `ExcludedMiddle`, and the
faithfulness check below would have to fail. It does not fail. A candidate explanation is that Lean
stratifies `Prop` and `Type`: `ChoiceFragment` is equivalent to `Nonempty (∀ p, Decidable p)` and
`ExcludedMiddle` to `∀ p, Nonempty (Decidable p)` (the `example`s after `ChoiceFragment`; the forward
leg of the second is the `match` inside Lean core's `Classical.propDecidable`, `Init/Classical.lean`,
before core applies `Classical.choice`), and `Or` in
`Prop` does not eliminate into `Bool` (the `#check_failure` after `ChoiceFragment`). The two differ
only in whether `Nonempty` sits outside or inside `∀ p`, and since each `Decidable p` has at most one
element, moving it outward is an instance of unique choice. That unique choice carries excluded middle
from `Prop` to data is standard in type theory: the Rocq standard library's
`theories/Logic/ChoiceFacts.v` proves `constructive_definite_descr_excluded_middle` and states that
"constructive definite description transports excluded-middle from [Prop] to [Set]", crediting the
idea of its proof to L. Chicli, L. Pottier and C. Simpson, "Mathematical Quotients and Quotient Types
in Coq", TYPES 2002, LNCS 2646. Read in the authors' preprint (preprint page numbers): § 5, pp. 12-13,
shows the axiom of unique choice with values in `Prop` contradicts excluded middle in `Prop` in Coq,
completing the proof with the § 4.2 argument, pp. 10-11; their § 6, p. 13, says the impredicativity
of `Set` is essential to it. Following the Rocq file, the credit is for that proof idea, not for the
transport result. In a topos a decided proposition determines an element of 1 + 1 (this form not
located in a source as of 2026-11-01; searched in topos-theory notes and theses held locally and on
the open web, while the theorem-search and Lean-library queries targeted unique choice, not this
form), while Ω itself is 1 + 1 only when the topos is Boolean
(`ZeroParadox/Category/ChoiceCannotBe.md`, § "The headline fence"). A failed elaboration measures one
construction, and neither pole of the converse, `ExcludedMiddle → ChoiceFragment`, is established here
for Lean without `Classical.choice` and without a unique-choice hypothesis: no derivation is given, and
no proof that none exists. **So Lean's stratification is a candidate
explanation of the one-way-ness observed below, not a finding — and not, as first written, a
restatement of Diaconescu.**

**No new axioms.** The choice principle in § II is a `def ... : Prop` hypothesis, discharged by the caller.
Nothing here is declared `axiom`, and nothing here uses `sorry`.

## Structure

- § I   Excluded middle ↔ every `Prop` is regular ↔ the `Prop` double-negation nucleus is the identity
- § II  Diaconescu: a choice fragment (as a hypothesis) implies excluded middle
- § III Composition: the choice fragment collapses the `Prop` nucleus
- § IV  The fence: a concrete Heyting algebra that is NOT Boolean, in the classical metatheory
