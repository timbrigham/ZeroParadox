import ZeroParadox.ZPH_PlaceForcing
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Direction A, Cycle A4 (depth b) — the adele ring as the global object for ℚ's places (assembly)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

A1–A3 placed the framework's number-theoretic bottoms over ℚ's places and made the place load-bearing.
A4 supplies the **global object** the local-global picture was missing: not a bare product-formula
constraint, but an actual ring whose components ARE the place-completions — **the adele ring of ℚ**.

Mathlib: `NumberField.AdeleRing ℤ ℚ := InfiniteAdeleRing ℚ × FiniteAdeleRing ℤ ℚ` — the archimedean
component × the finite (p-adic) component. The framework's nodes sit inside it:

- `adele_is_infinite_times_finite` — the adele ring splits as archimedean × finite. #2 (archimedean)
  lives in the first component; #3 (the 2-adic place) is one factor of the second.
- `principal_injective` — the **principal-adele embedding** `algebraMap ℚ (AdeleRing ℤ ℚ)` (the
  localization map: a global rational to its values at all places) is **injective**: the adele ring
  faithfully contains the global rationals (the diagonal). The global object genuinely sits above the
  local completions. (The per-component values are Mathlib's `algebraMap_fst_apply`/`algebraMap_snd_apply`
  — the v-component is `x` embedded in the v-completion; not restated here to avoid exposing the
  `WithAbs`/`WithVal` completion wrappers.)
- `adele_global_assembly` — bundles the two Mathlib facts under the framework reading: the adele ring
  contains ℚ faithfully AND the product formula (A2) holds. This is a *conjunction of existing facts*,
  not new Lean content — the value is the assembly/interpretation (the global object is the adele ring;
  its components are the places #2/#3 inhabit; the product formula is its constraint), not a new theorem.

**What the Lean adds (honest): essentially nothing beyond Mathlib + A2.** `adele_is_infinite_times_finite`
is the *definition* (rfl); `principal_injective` is a verbatim Mathlib re-export; `adele_global_assembly`
is a tuple of that plus A2's product-formula rearrangement. **No theorem statement references node #2/#3,
the Markov simplex, or the p-adic floor** — the "components ARE #2/#3" identification is *interpretation*,
in the docstrings only. A4's contribution is to *name and assemble* the global object (the adele ring)
under the framework reading, not to prove anything new about the bottoms.

**Honest scope.** This is Mathlib's adele ring of ℚ — the global object for ℚ's places, ALL of them. The
framework lights up #2 (the unique archimedean/infinite component) and #3 (the p = 2 finite component) as
two of its components. The adele ring does NOT contain the categorical/order bottoms (#1/#4/#5), which the
campaign proved are walled from the number-theoretic ones — so A4 realizes the local-global picture for
the number-theoretic sub-family only, not the whole diagram. Mathlib-anchored result + framework
interpretation (the components ARE #2/#3); not a from-scratch framework construction.
-/

namespace ZeroParadox.ZPH_AdeleGlobal

open NumberField IsDedekindDomain

/-- The global object splits as **archimedean × finite**: #2 (archimedean) in the first component,
    #3 (the 2-adic place) one factor of the second. -/
theorem adele_is_infinite_times_finite :
    AdeleRing ℤ ℚ = (InfiniteAdeleRing ℚ × FiniteAdeleRing ℤ ℚ) := rfl

/-- The global object faithfully contains ℚ: the principal-adele (localization) map is injective. -/
theorem principal_injective : Function.Injective (algebraMap ℚ (AdeleRing ℤ ℚ)) :=
  NumberField.AdeleRing.algebraMap_injective ℤ ℚ

/-- **A4 — the assembly** (a conjunction of existing facts, NOT new content). Under the framework
    reading: the adele ring is the global object — it faithfully contains ℚ (`principal_injective`) AND
    the product formula (A2) is the global constraint, #2's archimedean factor balancing the finite
    product. This bundles the two Mathlib/A2 facts; it proves nothing new and references no framework
    object in-statement (the #2/#3 component identification is interpretation). -/
theorem adele_global_assembly (x : ℚ) (hx : x ≠ 0) :
    Function.Injective (algebraMap ℚ (AdeleRing ℤ ℚ)) ∧
    ((∏ w : InfinitePlace ℚ, w x ^ w.mult) = (∏ᶠ w : FinitePlace ℚ, w x)⁻¹) :=
  ⟨principal_injective, ZeroParadox.ZPH_PlaceForcing.archimedean_factor_forced x hx⟩

end ZeroParadox.ZPH_AdeleGlobal

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_AdeleGlobal

#print axioms adele_is_infinite_times_finite
#print axioms principal_injective
#print axioms adele_global_assembly

end PurityCheck
