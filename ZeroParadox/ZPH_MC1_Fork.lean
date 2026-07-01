-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1
import Mathlib.Topology.Category.TopCat.Limits.Basic

set_option maxHeartbeats 400000

/-!
# Restating two `IsInitial` and one `IsTerminal` witness as `IsColimit` / `IsLimit`

**Proves.** `fork_mu_nu` re-expresses three prior witnesses through Mathlib's *definitional* equalities
`IsInitial X := IsColimit (asEmptyCocone X)` and `IsTerminal X := IsLimit (asEmptyCone X)`: the Info and
Hilbert bottoms are colimits (via `fC_zero_isInitial`, `fD_zero_isInitial`), the one-point Top object is a
limit (via `TopCat.isTerminalPUnit`). No new theorem — a definitional unfolding of existing witnesses.

**Reaching for (intent, NOT proved here).** This was *meant to* identify the bottoms' colimit-vs-limit
split with ZP-P's μ/ν (least/greatest fixed point) fork, and to check whether that split is
choice-discriminating the way ZP-P's coalgebra layer is.

**Gap (as far as this reaches).** The "split IS the μ/ν fork" claim is a conceptual identification, not a
Lean theorem connecting this file to `ZPP_Coalgebra`. And the choice-discrimination is **masked** here:
all three witnesses footprint `[propext, Classical.choice, Quot.sound]` (inherited library choice), so the
μ-free/ν-choice signature is invisible at this level — it lives in ZP-P's abstract W/M-types, not these
realizations. The fork identification is conjecture; this file only restates initiality as a (co)limit.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory Limits ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor

/-- Proves: restates three existing witnesses as (co)limits via Mathlib's definitional
    `IsInitial = IsColimit (asEmptyCocone _)` / `IsTerminal = IsLimit (asEmptyCone _)` — Info and Hilbert
    bottoms as colimits, the one-point Top object as a limit. Intent: read this colimit-vs-limit split as
    ZP-P's μ/ν fork. NOT proved here: any link to ZP-P's μ/ν machinery — that identification is conceptual,
    not a Lean theorem. -/
theorem fork_mu_nu :
    Nonempty (IsColimit (asEmptyCocone (fC_functor.obj 0))) ∧
      Nonempty (IsColimit (asEmptyCocone (fD_functor.obj 0))) ∧
      Nonempty (IsLimit (asEmptyCone (TopCat.of PUnit))) :=
  ⟨⟨fC_zero_isInitial⟩, ⟨fD_zero_isInitial⟩, ⟨TopCat.isTerminalPUnit⟩⟩

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check — the choice-discrimination is MASKED here (uniform library choice) -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms fork_mu_nu
end PurityCheck
