-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1

set_option maxHeartbeats 400000

/-!
# F_D's bottom admits a (zero) morphism back; F_C's does not

**Proves.** `fD_has_return`: in `ModuleCat ℂ` there is a morphism `fD_functor.obj n ⟶ fD_functor.obj 0` —
namely the zero morphism `⟨0⟩`. `irreversibility_not_uniform`: for `n > 0`, F_D admits such a morphism
back while F_C does not (`fC_no_return`). The content: a zero object has a zero morphism into it, a strict
initial object has none.

**Reaching for (intent, NOT proved here).** This was *meant to* show the snap's irreversibility is
non-uniform across the MC-1 bottoms — F_C strict-initial (irreversible), F_D a zero object
(bidirectional) — so "the same single bottom" hides a categorical difference in the *type* of bottom.

**Gap (as far as this reaches).** The F_D "return" is the **zero morphism** — the trivial map present for
*any* zero object — so "F_D's bottom is bidirectional, a richer character" overstates what the witness
gives (a single trivial map, not genuine reversibility). The fact that F_C and F_D bottoms differ in
strict-vs-non-strict initiality is real; the broader "heterogeneous, not interchangeable, irreversibility
is domain-specific" reading is interpretation, and bears on the MC-1 commitment only as such.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor

/-- Proves: there is a morphism `fD_functor.obj n ⟶ fD_functor.obj 0` — the zero morphism `⟨0⟩` (it exists
    because the target is a zero object). Contrast `fC_no_return`. (NB: this is the trivial zero morphism,
    not genuine reversibility — "bidirectional" would overstate it.) -/
theorem fD_has_return {n : ℕ} : Nonempty (fD_functor.obj n ⟶ fD_functor.obj 0) :=
  ⟨0⟩

/-- Proves: for `0 < n`, `fD_functor.obj n ⟶ fD_functor.obj 0` is inhabited (the zero morphism) while
    `fC_functor.obj n ⟶ fC_functor.obj 0` is empty (`fC_no_return`). Intent: read this as "irreversibility
    is non-uniform / the bottoms are heterogeneous". NOT proved here: that reading rests on the trivial
    zero morphism (see `fD_has_return`); it bears on the MC-1 commitment as interpretation only. -/
theorem irreversibility_not_uniform {n : ℕ} (hn : 0 < n) :
    Nonempty (fD_functor.obj n ⟶ fD_functor.obj 0) ∧
      IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0) :=
  ⟨⟨0⟩, fC_no_return hn⟩

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms irreversibility_not_uniform
end PurityCheck
