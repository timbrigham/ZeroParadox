import ZeroParadox.Ordinal.SnapNucleus
import Mathlib.Order.Sublocale

set_option maxHeartbeats 400000

/-!
# The lattice of systems: adjoining the point at infinity makes the ordinals a frame

`SnapNucleus.lean` builds the snap as a genuine `Nucleus Ordinal` — a single modality — on the bare
ordinals, which need only that meets exist. What the bare ordinals lack is a **top**: they ascend without
bound, so they are not a complete lattice and not a frame, and the *lattice of all such modalities* does
not exist there.

This file adjoins that missing top. `WithTop Ordinal` is the ordinals plus one point at infinity ⊤. That
single addition turns the ordinals into a **complete linear order**, and a complete linear order is a
`Order.Frame` (Mathlib: `CompleteLinearOrder → CompletelyDistribLattice → CompleteDistribLattice → Frame`,
all by instance resolution — nothing to prove). On a frame, the **nuclei** (modalities / predicated
differences) form a `Frame` and the **sublocales** (the systems they generate) form a `Coframe`: the
*lattice of systems*. So the point at infinity is exactly what completes the meta-level.

**Why this is the boundary doing the work.** The lattice-of-systems machinery fires ONLY once a top is
present — it does *not* fire on bare `Ordinal` (no top, not a frame). So it is provably the ceiling, the
point the unbounded ascent marches toward, that unlocks the lattice. By the framework's self-dual pole
(0 = ∞, `rInv_swaps`) that ceiling ⊤ is the point at infinity, which is the next bottom: the unboundedness
is its own type of boundary, and adjoining it is what turns "one modality" (the bare-ordinal `snapNucleus`)
into "one point in a lattice of systems."

**Honest scope.** The frame structure of `WithTop Ordinal` and the nucleus/sublocale lattice are recognized
Mathlib / locale theory — this file only *instantiates* them and records the placement (the top is the
framework's ∞ = 0 = ⊥ boundary). The concrete lift of the specific snap into a `Nucleus (WithTop Ordinal)`
whose sublocale is the snap-generated system is the next step (see `snap_is_a_nucleus_2026-07-18` note),
built on `OrderHom.nextFixed`. `example`-only here: states no new result.

## Engineer's Take

TODO (Tim): your take on the point at infinity completing the lattice of systems — that the ceiling the
unbounded ascent marches toward is what turns one modality into one point in a whole lattice of them.
-/

namespace ZeroParadox

open Order

/-! ### § I. The boundary at infinity makes the ordinals a frame -/

/-- Adjoining a top ⊤ (the point at infinity) makes the ordinals — which have bounded suprema but no top —
    a **complete linear order**. -/
noncomputable example : CompleteLinearOrder (WithTop Ordinal) := inferInstance

/-- A complete linear order is a **frame** (`Order.Frame`) — by instance resolution, no gap. The point at
    infinity is what supplies the completeness the bare ordinals lack. -/
noncomputable example : Order.Frame (WithTop Ordinal) := inferInstance

/-! ### § II. The lattice of systems -/

/-- On that frame the **modalities (nuclei) form a `Frame`** — the predicated differences, organized. -/
noncomputable example : Order.Frame (Nucleus (WithTop Ordinal)) := inferInstance

/-- The **systems (sublocales) form a `Coframe`** — the generated systems, organized order-dually. This is
    the lattice of systems the unbounded ascent's boundary unlocks. -/
noncomputable example : Order.Coframe (Sublocale (WithTop Ordinal)) := inferInstance

/-- Each modality **generates a system**: its sublocale. -/
noncomputable example (j : Nucleus (WithTop Ordinal)) : Sublocale (WithTop Ordinal) := j.toSublocale

-- Nuclei and sublocales are identified order-dually (`nucleusIsoSublocale`): the difference lattice and
-- the system lattice are two views of one structure.
#check @nucleusIsoSublocale (WithTop Ordinal) _

/-! ### § III. Contrast — the bare ordinals carry a modality but NOT the lattice

`snapNucleus : Nucleus Ordinal` exists on the bare ordinals (a `Nucleus` needs only `SemilatticeInf`). But
`Ordinal` is not a frame, so `Order.Frame (Nucleus Ordinal)` and `Sublocale Ordinal` do NOT fire there —
the single modality lives one level below the lattice. Adjoining the top is what lifts it into a lattice of
systems. -/

/-- The single modality on the bare ordinals (from `SnapNucleus.lean`). -/
noncomputable example : Nucleus Ordinal := snapNucleus

end ZeroParadox
