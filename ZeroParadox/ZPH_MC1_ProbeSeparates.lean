-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1

set_option maxHeartbeats 400000

/-!
# `Fin 0` is empty; the zero ℂ-module on `Fin 0` is inhabited

**Proves.** `probe_separates`: `IsEmpty (Fin 0)` and `Nonempty (EuclideanSpace ℂ (Fin 0))` (the zero
vector). The supporting lemmas note the Top floor `{0}` is also inhabited. The content: the Info bottom's
underlying type is empty, the Hilbert/Top bottoms' underlying types are not.

**Reaching for (intent, NOT proved here).** This was *meant to* be the crudest common probe (underlying
points / `Hom(1,−)`), to test whether it separates the bottoms — and it does, at the level of "has an
element": `∅` for Info, a point for the others.

**Gap — and this file already states it.** Probe-separation does NOT discriminate a genuine obstruction
from genuine gluing: the completions `ℝ`, `ℚ_p` of `0 ∈ ℚ` are wildly separated yet glue, so separation is
generic to localization. So this rules out only the cheapest "they are literally one set" reading; it says
nothing about whether the bottoms unify. The discriminating datum (cocycle coherence) is not built. (This
docstring's honest self-correction is preserved; the surrounding M-construction is conjecture.)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open ZeroParadox.ZPB ZeroParadox.ZPH_HilbFunctor

/-- The information bottom `Fin 0` has no global point — the empty type (Set-initial `∅`). -/
theorem info_bottom_no_point : IsEmpty (Fin 0) := inferInstance

/-- The Hilbert bottom `StateSpace 0 = EuclideanSpace ℂ (Fin 0)` has a global point — the zero vector
    (Set-terminal `1`). -/
theorem hilb_bottom_has_point : Nonempty (EuclideanSpace ℂ (Fin 0)) := ⟨0⟩

/-- The Top bottom — the inverse-limit point `{0} ⊆ Q₂` — has a global point. -/
theorem top_bottom_has_point : ({(0 : Q₂)} : Set Q₂).Nonempty := Set.singleton_nonempty _

/-- **M-toy.** The global-points probe SEPARATES the MC-1 bottoms: the information bottom is the empty
    type while the Hilbert (and Top) bottoms are inhabited. The crudest common probe already distinguishes
    them — `∅` vs a point — so the bottoms are not literally one underlying set. (NB: this confirms the
    heterogeneity but does NOT discriminate Exit A vs B — separated local pieces can still glue, as the
    ℚ-completions do; see the file header.) -/
theorem probe_separates : IsEmpty (Fin 0) ∧ Nonempty (EuclideanSpace ℂ (Fin 0)) :=
  ⟨inferInstance, ⟨0⟩⟩

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms probe_separates
end PurityCheck
