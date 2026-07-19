import Mathlib.Order.Nucleus
import Mathlib.Order.Heyting.Regular

/-!
# Choice as a difference-generator: the double-negation nucleus

`Category/DifferenceGeneratesSystem.lean` identifies "a predicated difference generates a system" with the
nucleus/sublocale (Lawvere–Tierney) machinery, and machine-checks with `example`s that double negation
sends the constructive base into the classical (Boolean) core. This file builds the **object** those
examples were about: the double-negation map `a ↦ aᶜᶜ` as a genuine `Nucleus` on any Heyting algebra.

This is the exact parallel to `snapNucleus` (`Ordinal/SnapNucleus.lean`). Both are concrete
difference-generators — inflationary, idempotent, meet-preserving modalities — of the framework's two
threads: the **snap** (the ordinal difference `α ↦ ω^α`, generating ε₀) and **choice** (the logical
difference `a ↦ aᶜᶜ`, generating the classical core). "Choosing" is applying this modality: `aᶜᶜ` is the
element that has picked a side. The generated system — the nucleus's closed points — is exactly the
**regular elements** `{a | aᶜᶜ = a}`, the Boolean core (`Heyting.Regular`).

**Honest scope / credit outward.** The double-negation nucleus is textbook: it is the Boolean (¬¬-dense)
subtopos / the Lawvere–Tierney topology whose sheaves are the classical objects, and its regular-element
core is Glivenko's theorem in algebraic form. Mathlib carries the pieces (`le_compl_compl`,
`compl_compl_compl`, `compl_compl_inf_distrib`, `Heyting.Regular`) but not the packaged `Nucleus`; this
file only assembles it and names it as the framework's "choice modality," parallel to the snap. It states
no new theorem of the general theory. The step from this classical *logic* up to the axiom of *choice* is
the Diaconescu line (see `DifferenceGeneratesSystem.lean`), not asserted here.

## Engineer's Take

TODO (Tim): your take on choice being a difference-generator in the same sense the snap is — the modality
`a ↦ aᶜᶜ` that picks a side, whose closed points are the elements that have already picked one.
-/

namespace ZeroParadox

/-- **The double-negation nucleus** `a ↦ aᶜᶜ` on a Heyting algebra: the canonical predicated difference —
    the modality that collapses the constructive base toward the classical (Boolean) core. A genuine
    `Nucleus` (needs only that meets exist): inflationary (`le_compl_compl`), idempotent
    (`compl_compl_compl`), meet-preserving (`compl_compl_inf_distrib`). The choice-side parallel of
    `snapNucleus`. -/
def dnegNucleus (X : Type*) [HeytingAlgebra X] : Nucleus X where
  toFun a := aᶜᶜ
  map_inf' := compl_compl_inf_distrib
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
#print axioms dnegNucleus
#print axioms dnegNucleus_isClosed_iff
end PurityCheck
