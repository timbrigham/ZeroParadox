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
Mathlib / locale theory — §§ I–II only *instantiate* them and record the placement (the top is the
framework's ∞ = 0 = ⊥ boundary). § IV then lifts the specific snap into the lattice: `snapNucleusTop` reuses
the ordinal snap-closure through `WithTop.map`, and `snapSublocale = snapNucleusTop.toSublocale` is the
snap-generated system as a named point in the lattice. The lift is a construction; the frame/lattice
machinery it lands in is recognized structure, credited outward.

## Engineer's Take

The question that led here was about the boundary. That unbounded upward system that marches toward
infinity, that very unboundedness is what creates the new instance of a new system, and that is its own
type of boundary.

What I wanted to see was what that boundary does once it is actually in place. It is what takes a single
system and sets it among all the others, so they stand together instead of alone. The point at infinity is
where one system becomes one of many.
-/

namespace ZeroParadox

open Order Ordinal

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

/-! ### § IV. The snap lifted into the lattice — the snap's own system as a named point

The bare-ordinal snap-closure `nfp (α ↦ ω^α)` pushed up through `WithTop.map` (⊤ ↦ ⊤, ↑a ↦ ↑(nfp a)) is a
genuine `Nucleus (WithTop Ordinal)` — so the snap now lives IN the lattice of systems, and its `toSublocale`
is the snap-generated system as a named object beside every other. The three nucleus conditions lift by
casing on top-vs-ordinal; meet-preservation is again free on the chain. -/

/-- The snap as a nucleus on the ordinals-with-top: `nfp (α ↦ ω^α)` lifted by `WithTop.map`. -/
noncomputable def snapNucleusTop : Nucleus (WithTop Ordinal) where
  toFun := WithTop.map (Ordinal.nfp (fun α => Ordinal.omega0 ^ α))
  map_inf' a b := by
    have hmono : Monotone (WithTop.map (Ordinal.nfp (fun α => Ordinal.omega0 ^ α))) := by
      intro x y hxy
      induction x using WithTop.recTopCoe with
      | top => rw [top_le_iff] at hxy; subst hxy; exact le_rfl
      | coe a =>
        induction y using WithTop.recTopCoe with
        | top => exact le_top
        | coe b =>
          rw [WithTop.coe_le_coe] at hxy
          simp only [WithTop.map_coe]
          exact WithTop.coe_le_coe.mpr
            (Ordinal.nfp_monotone (isNormal_opow one_lt_omega0).strictMono.monotone hxy)
    rcases le_total a b with h | h
    · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hmono h)]
    · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hmono h)]
  idempotent' x := by
    induction x using WithTop.recTopCoe with
    | top => simp
    | coe a =>
      simp only [WithTop.map_coe]
      exact le_of_eq (congrArg _
        (Ordinal.nfp_eq_self (Ordinal.nfp_fp (isNormal_opow one_lt_omega0) a)))
  le_apply' x := by
    induction x using WithTop.recTopCoe with
    | top => simp
    | coe a =>
      simp only [WithTop.map_coe]
      exact WithTop.coe_le_coe.mpr (Ordinal.le_nfp _ a)

/-- Unfolding: the lifted nucleus is `WithTop.map` of the ordinal snap-closure. -/
@[simp] theorem snapNucleusTop_apply (x : WithTop Ordinal) :
    snapNucleusTop x = WithTop.map (Ordinal.nfp (fun α => Ordinal.omega0 ^ α)) x := rfl

/-- The lift agrees with the base snap at the bottom: it sends `↑⊥` to `↑ε₀` (`epsilon0_eq_nfp_bot`),
    matching `snapNucleus_bot` one level down. -/
theorem snapNucleusTop_coe_bot :
    snapNucleusTop ((⊥ : Ordinal) : WithTop Ordinal) = (epsilonZero : WithTop Ordinal) := by
  rw [snapNucleusTop_apply, WithTop.map_coe]
  exact congrArg _ epsilon0_eq_nfp_bot.symm

/-- **The snap's generated system.** Its sublocale — a named point in the lattice of systems on
    `WithTop Ordinal`. This is "the snap generates a system," fully closed: the object exists and sits in
    the lattice. -/
noncomputable def snapSublocale : Sublocale (WithTop Ordinal) := snapNucleusTop.toSublocale

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms snapNucleusTop
#print axioms snapNucleusTop_coe_bot
#print axioms snapSublocale
end PurityCheck
