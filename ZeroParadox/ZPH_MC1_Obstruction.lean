-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_Linearize
import Mathlib.Topology.Category.TopCat.Limits.Basic

set_option maxHeartbeats 400000

/-!
# Two Finsupp facts (one ℂ-linearization stand-in pair, one opposite-category initiality)

**Proves.** Two small, true facts: (1) `dualized_top_floor_initial` — the one-point space `TopCat.of PUnit`
(terminal in `TopCat`) is an initial object of `TopCatᵒᵖ` (= `TopCat.isTerminalPUnit.op`). (2)
`top_floor_lin_dim_obstruction` — the type `PUnit →₀ ℂ` is not in bijection with `Fin 0 →₀ ℂ`, because the
first is nontrivial (`single unit 1 ≠ 0`) and the second is a subsingleton. That is the whole formal content:
"a nontrivial Finsupp type ≄ a subsingleton Finsupp type", plus a terminal-becomes-initial-in-the-opposite.

**Reaching for (intent, NOT proved here).** This file was *aimed at* the capstone of the Global-Zero
construction: the claim that, after the 0=∞ flip aligns Top's polarity, the framework bottoms still fail to
glue because the Top floor carries a "dimension" the others lack — separating a gluing cluster (Info/Hilbert)
from an obstructed Top, with the obstruction read as a gauge-invariant the multimeter framing pointed at.

**Gap (as far as this reaches).** The Lean does NOT establish any of that. The statements reference
`PUnit →₀ ℂ` and `Fin 0 →₀ ℂ`, NOT the real framework bottoms (`fB_functor`, `fD_functor`) — those are
asserted *stand-ins*, an identification this file does not prove. There is no `Module.rank`, no linearization
*functor*, no 0=∞ flip, and no gluing in either proof. So "dimension obstruction / Exit A / MC-1's identity
is not a gluable object" is an interpretation layered on a `1 ≠ 0` fact, not a result. The cross-domain claim
remains a CONJECTURE; see `mc1_global_zero_construction_spec_2026-06-28.md` (read its cold-audit correction).
A cold audit (2026-06-28) named this file's prior docstring the batch's worst overreach.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory Limits

/-- Proves: the one-point space (terminal in `TopCat`) is initial in `TopCatᵒᵖ` — `IsTerminal.op`.
    Reaching for (intent): the "dualizing Top realigns its polarity" step. Gap: this is the generic
    terminal↦initial-under-opposite fact; it says nothing specific about the framework's Top bottom. -/
noncomputable def dualized_top_floor_initial : IsInitial (Opposite.op (TopCat.of PUnit)) :=
  TopCat.isTerminalPUnit.op

/-- Proves: `PUnit →₀ ℂ` (nontrivial: `single unit 1 ≠ 0`) is not in bijection with `Fin 0 →₀ ℂ`
    (a subsingleton). I.e. a nontrivial type ≄ a subsingleton type — at root, `1 ≠ 0`.
    Reaching for (intent): the "Top floor carries a dimension the cluster bottoms lack, so they don't glue"
    obstruction. Gap: the two types are ASSERTED stand-ins for the real bottoms (`fB`/`fD`); no functor,
    rank, flip, or gluing appears in the proof. The cross-domain obstruction is conjecture, not this fact. -/
theorem top_floor_lin_dim_obstruction :
    IsEmpty ((PUnit →₀ ℂ) ≃ (Fin 0 →₀ ℂ)) := by
  constructor
  intro e
  haveI hsub : Subsingleton (Fin 0 →₀ ℂ) := ⟨fun a b => Finsupp.ext fun i => i.elim0⟩
  -- both images land in the subsingleton cluster bottom, so they are equal; injectivity then forces
  -- the nonzero indicator `single unit 1` to be `0` — contradiction.
  have h1 : e (Finsupp.single PUnit.unit (1 : ℂ)) = e 0 := Subsingleton.elim _ _
  have h2 : Finsupp.single PUnit.unit (1 : ℂ) = 0 := e.injective h1
  exact (Finsupp.single_ne_zero.mpr one_ne_zero) h2

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms dualized_top_floor_initial
#print axioms top_floor_lin_dim_obstruction
end PurityCheck
