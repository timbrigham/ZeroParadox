import Mathlib.Order.Nucleus
import Mathlib.Order.Heyting.Regular

/-!
# The double-negation nucleus: the excluded-middle modality

## Engineer's Take

Why is Diaconescu not applied here? That was where this started, and the answer was that it already was
applied, just not visibly.

The question that came out of it is whether we are defining the excluded middle itself using the negation
operator against the bottom element. We are.

---

`dnegNucleus` is the double-negation map `a ↦ aᶜᶜ` as a `Nucleus` on any Heyting algebra; its closed
points are the regular elements (`dnegNucleus_isClosed_iff`). It is the excluded-middle modality, not
choice. Scope, credit, the footprint and the fence: `ZeroParadox/Category/DoubleNegationNucleus.md`.
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
