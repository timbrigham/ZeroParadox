-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1
import Mathlib.Topology.Category.TopCat.Limits.Basic

set_option maxHeartbeats 400000

/-!
# A 3-field structure bundling three objects, plus three pre-existing universal-property witnesses

**Proves.** Defines `GlobalZero`, a `structure` with three fields (`top : TopCat`, `hilb : ModuleCat ℂ`,
`info : KleisliCat PMF`), and `globalZero`, one inhabitant (`TopCat.of PUnit`, `fD_functor.obj 0`,
`fC_functor.obj 0`). `globalZero_mixed_character` records three already-proved facts: the Top component is
terminal (`TopCat.isTerminalPUnit`), the Hilbert and Info components are initial (`fD_zero_isInitial`,
`fC_zero_isInitial`). The formal content is a tuple definition plus a conjunction of prior witnesses.

**Reaching for (intent, NOT proved here).** This was *meant to be* the "Global Zero as a section of the
Grothendieck fibration over the domains" — with the discrete index collapsing the fibration to a plain
tuple, and the mixed character (terminal in one fiber, initial in two) read as the "trenchcoat" floor of
the construction (one object, no uniform universal property).

**Gap (as far as this reaches).** There is no Grothendieck construction, no fibration, and no section in
the Lean — only a 3-field structure. Calling `GlobalZero` "a section of the fibration / the discrete-index
Grothendieck object" is intent, not a built object. The genuine cross-domain identification (a non-discrete
index, the obstruction class) is entirely conjecture: `mc1_global_zero_construction_spec_2026-06-28.md`
(read its cold-audit correction).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory Limits ZeroParadox.ZPH_InfoFunctor ZeroParadox.ZPH_HilbFunctor

/-- A 3-field structure bundling one object from each domain category. Intent: a "section over the discrete
    domain index" / "the discrete-index Grothendieck object" — but NO Grothendieck construction or fibration
    is built here; this is just a tuple. -/
structure GlobalZero where
  /-- Top fiber object. -/
  top : TopCat
  /-- Hilbert fiber object (`ModuleCat ℂ`). -/
  hilb : ModuleCat ℂ
  /-- Info fiber object (`KleisliCat PMF`). -/
  info : KleisliCat PMF

/-- One inhabitant of `GlobalZero`: the tuple `(TopCat.of PUnit, fD_functor.obj 0, fC_functor.obj 0)`.
    Intent: "the (cheap) Global Zero" bundling the three local bottoms — a tuple, not a constructed
    cross-domain object. -/
noncomputable def globalZero : GlobalZero where
  top := TopCat.of PUnit
  hilb := fD_functor.obj 0
  info := fC_functor.obj 0

/-- Proves: the three components of `globalZero` carry the universal properties of their existing
    witnesses — Top component terminal (`TopCat.isTerminalPUnit`), Hilbert and Info components initial
    (`fD_zero_isInitial`, `fC_zero_isInitial`). A conjunction of prior witnesses about a tuple. Intent: the
    "mixed character / trenchcoat" reading. NOT proved here: any cross-domain object or "section". -/
theorem globalZero_mixed_character :
    Nonempty (IsTerminal globalZero.top) ∧
      Nonempty (IsInitial globalZero.hilb) ∧
      Nonempty (IsInitial globalZero.info) :=
  ⟨⟨TopCat.isTerminalPUnit⟩, ⟨fD_zero_isInitial⟩, ⟨fC_zero_isInitial⟩⟩

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms globalZero_mixed_character
end PurityCheck
