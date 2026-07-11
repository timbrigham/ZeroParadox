-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the Koopman (composition) operator of a measure-preserving self-map of ℤ_p, as a linear isometry on L²(ℤ_p), with the odometer x ↦ c + x as the first witness. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicHaar
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Koopman operator on L²(ℤ_p)

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Builds the **Koopman (composition) operator** of a measure-preserving self-map `f : ℤ_p → ℤ_p`:
`g ↦ g ∘ f`, as a `ℂ`-linear isometry on `L²(ℤ_p, haarZp)` (Mathlib's `Lp.compMeasurePreservingₗᵢ`
against the Haar measure built in `PadicHaar`). The first concrete witness is the **odometer / adding
machine** `x ↦ c + x` (left translation), whose measure-preservation is exactly left-invariance of the
Haar measure (`measurePreserving_add_left`). All results are standard once the measure exists; the
operator is a linear isometry by construction (norm-preserving), so no separate isometry proof is
needed.

## Structure
- § I   The Koopman operator of a measure-preserving self-map
- § II  The odometer witness and its Koopman operator
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — The Koopman operator of a measure-preserving self-map -/

/-- The **Koopman (composition) operator** `g ↦ g ∘ f` of a measure-preserving self-map `f` of `ℤ_p`,
    as a `ℂ`-linear isometry on `L²(ℤ_p, haarZp)`. -/
noncomputable def koopman (f : ℤ_[p] → ℤ_[p])
    (hf : MeasurePreserving f (haarZp (p := p)) (haarZp (p := p))) :
    Lp ℂ 2 (haarZp (p := p)) →ₗᵢ[ℂ] Lp ℂ 2 (haarZp (p := p)) :=
  Lp.compMeasurePreservingₗᵢ ℂ f hf

/-! ## § II — The odometer witness and its Koopman operator -/

/-- The **odometer / adding machine** `x ↦ c + x` (left translation) is measure-preserving — this is
    exactly left-invariance of the Haar measure. -/
theorem measurePreserving_odometer (c : ℤ_[p]) :
    MeasurePreserving (c + ·) (haarZp (p := p)) (haarZp (p := p)) :=
  measurePreserving_add_left (haarZp (p := p)) c

/-- The Koopman operator of the odometer `x ↦ c + x`, a linear isometry on `L²(ℤ_p)`. -/
noncomputable def koopmanOdometer (c : ℤ_[p]) :
    Lp ℂ 2 (haarZp (p := p)) →ₗᵢ[ℂ] Lp ℂ 2 (haarZp (p := p)) :=
  koopman (c + ·) (measurePreserving_odometer c)

end ZeroParadox

/-! ## Axiom Purity Check

`measurePreserving_odometer` depends on `[propext, Classical.choice, Quot.sound]` — `Classical.choice`
enters through the Mathlib Haar / `MeasureTheory` libraries (a dependency, not a new commitment). No
`sorryAx` appears. -/
section PurityCheck
open ZeroParadox
#print axioms measurePreserving_odometer
end PurityCheck
