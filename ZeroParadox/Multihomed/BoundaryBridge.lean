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

**PROBE.** The snap ⊥→ε₀ as the crossing of the well-foundedness boundary, in two registers —
`ZeroParadox/Multihomed/Boundary.lean` (`snap_crossing`) and `ZeroParadox/Settheory/Coalgebra.lean`
(`categorical_fork_strict`) — bundled by `snap_boundary_two_registers` below.
**NOT the full Taylor statement.** Its depth result is that every well-founded coalgebra is recursive
(Taylor's General Recursion Theorem; Adámek–Milius–Moss 2020, arXiv:1910.09401v2, Thm 7.2 p. 27 —
SUFFICIENCY only; the converse is their § 8, under further hypotheses).
Not located in the pinned Mathlib as of 2026-08-12 (environment sweep over declaration names and
types): Pataraia's fixed-point theorem, and the General Recursion Theorem itself. The **next-time
operator is no longer open** — `ZeroParadox/Category/NextTimeCategorical.lean` builds it
(`nextTimeCat`); read it before re-deriving one. Detail, sources and the survey's limits:
`.claude-local/notes/boundarybridge_scope_2026-08-12.md`.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice ZeroParadox ZeroParadox ZeroParadox

set_option maxHeartbeats 400000

/-- **Best-effort snap-boundary witness (C-QPF).** The snap crosses the well-foundedness boundary,
    witnessed in two registers: the relation/carrier level (`snap_crossing` — floor the sole
    non-accessible point, every post-snap state accessible) and the categorical μ/ν level
    (`categorical_fork_strict` — initial algebra empty, final coalgebra inhabited; the self-referential
    element lives in ν, not μ). The well-founded ⟺ recursive *depth* (Taylor/AMM) is cited, not proved
    here — see the scope fence. -/
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
