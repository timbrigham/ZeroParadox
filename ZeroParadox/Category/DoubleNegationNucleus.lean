import Mathlib.Order.Nucleus
import Mathlib.Order.Heyting.Regular

/-!
# The double-negation nucleus: the excluded-middle modality

`Category/DifferenceGeneratesSystem.lean` identifies "a predicated difference generates a system" with the
nucleus/sublocale (Lawvere–Tierney) machinery, and machine-checks with `example`s that double negation
sends the constructive base into the classical (Boolean) core. This file builds the **object** those
examples were about: the double-negation map `a ↦ aᶜᶜ` as a genuine `Nucleus` on any Heyting algebra.

This is the exact parallel to `snapNucleus` (`Ordinal/SnapNucleus.lean`). Both are concrete
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
choice implies excluded middle, and Lean's own kernel derives `Classical.em` from `Classical.choice` by
exactly that argument. So a proof of the excluded-middle modality that leaked `Classical.choice` was
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
proved is an *equivalence*: in a topos, choice for inhabited subobjects of a two-element object **is**
excluded middle. Attributing "the converse fails" to him is a misreading; see
`ZeroParadox/Category/ChoiceCannotBe.lean` for the full statement and for why the restricted fragment
nonetheless comes apart from excluded middle in Lean specifically. The framework's conversational
"choice = which way you view the self-dual split" reading is the looser, informal thread — discussed in
`DifferenceGeneratesSystem.lean`, not asserted here; the object built here is the double-negation
(excluded-middle) nucleus, nothing stronger.

**Correction of record: this file once made that error itself.** It was originally titled "Choice as a
difference-generator" and named this object the framework's *choice modality*. That was wrong — choice is
strictly stronger than what `a ↦ aᶜᶜ` delivers — and it was corrected in commit `655c761` off an adversary
kill-list. Recorded here rather than quietly rewritten, because a reader checking the framework's claims
is entitled to know which ones it previously got wrong. The arrow that actually connects the two is built
in `ZeroParadox/Category/ExcludedMiddleBridge.lean`.

## Engineer's Take

Why is Diaconescu not applied here? That was where this started, and the answer was that it already was
applied, just not visibly.

The question that came out of it is whether we are defining the excluded middle itself using the negation
operator against the bottom element. We are.
-/

namespace ZeroParadox

/-- **Double negation preserves meets** — a choice-free proof. Mathlib's `compl_compl_inf_distrib`
    routes through `sup`/`compl_sup_distrib` and so carries `Classical.choice`. This proof stays on the
    meet side throughout, using only `le_compl_iff_disjoint_right`, `disjoint_iff_inf_le`,
    `compl_inf_self` and `inf_assoc` — all `[propext]`-only — which keeps the whole nucleus at
    `[propext]`. The `sup`-free route is the essential constraint: `compl_sup_distrib` is where the
    classical dependency enters. -/
theorem dneg_inf_distrib {X : Type*} [HeytingAlgebra X] (a b : X) :
    (a ⊓ b)ᶜᶜ = aᶜᶜ ⊓ bᶜᶜ := by
  refine le_antisymm (le_inf (compl_le_compl (compl_le_compl inf_le_left))
      (compl_le_compl (compl_le_compl inf_le_right))) ?_
  have h1 : (a ⊓ b)ᶜ ⊓ a ≤ bᶜ :=
    le_compl_iff_disjoint_right.2 <| disjoint_iff_inf_le.2 <| by
      calc (a ⊓ b)ᶜ ⊓ a ⊓ b = (a ⊓ b)ᶜ ⊓ (a ⊓ b) := by rw [inf_assoc]
        _ ≤ ⊥ := (compl_inf_self _).le
  have h2 : bᶜᶜ ⊓ (a ⊓ b)ᶜ ≤ aᶜ :=
    le_compl_iff_disjoint_right.2 <| disjoint_iff_inf_le.2 <| by
      calc bᶜᶜ ⊓ (a ⊓ b)ᶜ ⊓ a = bᶜᶜ ⊓ ((a ⊓ b)ᶜ ⊓ a) := by rw [inf_assoc]
        _ ≤ bᶜᶜ ⊓ bᶜ := inf_le_inf_left _ h1
        _ = ⊥ := compl_inf_self _
  have h3 : aᶜᶜ ⊓ bᶜᶜ ⊓ (a ⊓ b)ᶜ ≤ ⊥ := by
    calc aᶜᶜ ⊓ bᶜᶜ ⊓ (a ⊓ b)ᶜ = aᶜᶜ ⊓ (bᶜᶜ ⊓ (a ⊓ b)ᶜ) := by rw [inf_assoc]
      _ ≤ aᶜᶜ ⊓ aᶜ := inf_le_inf_left _ h2
      _ = ⊥ := compl_inf_self _
  exact le_compl_iff_disjoint_right.2 (disjoint_iff_inf_le.2 h3)

/-- **The double-negation nucleus** `a ↦ aᶜᶜ` on a Heyting algebra: the canonical predicated difference —
    the modality that collapses the constructive base toward the classical (Boolean) core. A genuine
    `Nucleus` (needs only that meets exist): inflationary (`le_compl_compl`), idempotent
    (`compl_compl_compl`), meet-preserving (`dneg_inf_distrib`). The double-negation-side parallel of
    `snapNucleus`. Axiom footprint `[propext]` — choice-free; see the file header. -/
def dnegNucleus (X : Type*) [HeytingAlgebra X] : Nucleus X where
  toFun a := aᶜᶜ
  map_inf' := dneg_inf_distrib
  idempotent' a := le_of_eq (congrArg compl (compl_compl_compl a))
  le_apply' _ := le_compl_compl

@[simp] theorem dnegNucleus_apply {X : Type*} [HeytingAlgebra X] (a : X) :
    dnegNucleus X a = aᶜᶜ := rfl

/-- **The generated system is the classical core.** The closed points of the double-negation nucleus are
    exactly the **regular elements** `aᶜᶜ = a` — the ones that have already picked a side (the Boolean
    core, `Heyting.Regular`). "Difference (double negation) generates system (the classical core)," with
    the system named. -/
theorem dnegNucleus_isClosed_iff {X : Type*} [HeytingAlgebra X] (a : X) :
    dnegNucleus X a = a ↔ Heyting.IsRegular a := Iff.rfl

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms dneg_inf_distrib
#print axioms dnegNucleus
#print axioms dnegNucleus_isClosed_iff
end PurityCheck
