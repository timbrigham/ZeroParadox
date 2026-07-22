-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.MC1Bridge

set_option maxHeartbeats 400000

/-!
# The free ℂ-module on the empty type is initial, hence isomorphic to the Hilbert bottom

**Proves.** `lin_carries_bottom`: `linObj (Fin 0)` (the free ℂ-module `Fin 0 →₀ ℂ`) is isomorphic to
`fD_functor.obj 0` (the Hilbert bottom), because both are initial objects of `ModuleCat ℂ` and initial
objects are unique up to iso. That is the content: two initial objects coincide (true of *any* two
initial objects). `linObj` is just the free-module object assignment `A ↦ (A →₀ ℂ)`.

**Reaching for (intent, NOT proved here).** This was *aimed at* a "linearization comparison functor"
`KleisliCat PMF ⥤ ModuleCat ℂ` (a Markov kernel `A → PMF B` is its stochastic matrix `ℂ^A → ℂ^B`; the
FinStoch ↪ Vect embedding) realizing a real inter-domain edge that carries the Info bottom onto the
Hilbert bottom — the constructive half of the Global-Zero gluing.

**Gap (as far as this reaches).** No functor is built. `lin_carries_bottom` only uses that both objects are
initial — it does not exhibit `linObj` acting on morphisms, and the "this is the linearization of the Info
bottom" reading is asserted, not proved. The full functor is genuinely obstructed on infinite types (a
general `PMF B` has countable support, so its pushforward is not finitely supported), clean only on finite
types — that limit is real and stated here, but the functor (and thus the inter-domain comparison) is NOT
built. Conjecture/intent: `mc1_global_zero_construction_spec_2026-06-28.md` (see its cold-audit correction).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

open CategoryTheory Limits ZeroParadox

/-- **Object map of the linearization comparison**: the free ℂ-module on a type `A`, `A ↦ (A →₀ ℂ)`. On
    finite `A = Fin n` this is `ℂ^n`; a finite stochastic map becomes its stochastic-matrix linear map.
    (This is exactly the object map of Mathlib's free-module functor `ModuleCat.free ℂ`
    (`Algebra/Category/ModuleCat/Adjunctions.lean`); re-inlined here for a self-contained probe.) -/
noncomputable def linObj (A : Type) : ModuleCat ℂ := ModuleCat.of ℂ (A →₀ ℂ)

/-- The linearization sends the Info bottom `Fin 0` to a zero/initial object of `ModuleCat ℂ`
    (`Fin 0 →₀ ℂ` is the zero module — finitely supported functions on the empty type). -/
noncomputable def lin_bottom_isInitial : IsInitial (linObj (Fin 0)) := by
  haveI : Subsingleton (Fin 0 →₀ ℂ) := ⟨fun a b => Finsupp.ext (fun i => i.elim0)⟩
  exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ (Fin 0 →₀ ℂ))).isInitial

/-- Proves: `linObj (Fin 0)` ≅ `fD_functor.obj 0`, since both are initial objects of `ModuleCat ℂ`
    (unique up to iso). Reaching for (intent): the linearization edge "Info bottom ↦ Hilbert bottom".
    Gap: this holds of ANY two initial objects; it uses no functorial action and does not prove `linObj`
    is the linearization of the Info bottom — that reading is asserted, not established. -/
noncomputable def lin_carries_bottom : linObj (Fin 0) ≅ fD_functor.obj 0 :=
  lin_bottom_isInitial.uniqueUpToIso fD_zero_isInitial

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms lin_carries_bottom
end PurityCheck
