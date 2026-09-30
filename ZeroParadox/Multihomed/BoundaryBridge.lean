import ZeroParadox.Multihomed.Boundary
import ZeroParadox.Settheory.Coalgebra

/-!
# ZPJ — The snap-boundary, QPF bridge (best-effort; Rung C-QPF)

## Engineer's Take

This file is a shortcut, a quick representation of the ν versus μ relationship. Mathlib at current does
not currently provide complete Taylor machinery, so we're representing the same premise to the best of
our abilities using indexes. Please take this as an open invitation to expand both the Zero Paradox
project as well as Mathlib as a whole.

---
**PROBE.** The snap ⊥→ε₀ as the crossing of the well-foundedness boundary, in two registers, bundled by `snap_boundary_two_registers` below. **NOT the full Taylor statement** — registers, citations and which theorem carries which direction: `ZeroParadox/Multihomed/BoundaryBridge.md`.
Not located in the pinned Mathlib as of 2026-08-12 (environment sweep over names and types):
Pataraia's fixed-point theorem — proved in this corpus with no axioms, `pataraia_least_prefixedPoint`
(`ZeroParadox/Order/PataraiaChoiceFree.lean`) — and the General Recursion Theorem itself. The **next-time
operator is built** in this corpus — `ZeroParadox/Category/NextTimeCategorical.lean` (`nextTimeCat`); read it before re-deriving one.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice ZeroParadox ZeroParadox ZeroParadox

set_option maxHeartbeats 400000

/-- **Best-effort snap-boundary witness (C-QPF).** The snap crosses the well-foundedness boundary,
    witnessed in two registers: the relation/carrier level (`snap_crossing` — floor the sole
    non-accessible point, every post-snap state accessible) and the categorical μ/ν level
    (`categorical_fork_strict` — initial algebra empty, final coalgebra inhabited; the self-referential
    element lives in ν, not μ). The *depth* results — AMM Thm 7.2's ⇒ and its § 8 converse — are
    cited, not proved here; see `ZeroParadox/Multihomed/BoundaryBridge.md` for which carries which. -/
theorem snap_boundary_two_registers {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] :
    ((¬ WellFounded (floorRel (L := L)))
        ∧ (¬ Acc phaseRel Phase.floor ∧ ∀ o : Ordinal, Acc phaseRel (Phase.up o)))
      ∧ (IsEmpty (QPF.Fix idPF_Coalgebra.Obj) ∧ Nonempty (QPF.Cofix idPF_Coalgebra.Obj)) :=
  ⟨⟨floor_not_wellFounded, snap_crossing⟩, categorical_fork_strict⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms snap_boundary_two_registers
end PurityCheck
