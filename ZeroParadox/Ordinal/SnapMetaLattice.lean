import ZeroParadox.Ordinal.SnapNucleus
import Mathlib.Order.Sublocale

set_option maxHeartbeats 400000

/-!
# The lattice of systems: adjoining the point at infinity makes the ordinals a frame

`ZeroParadox/Ordinal/SnapNucleus.lean` builds the snap as a genuine `Nucleus Ordinal` — a single modality — on the
bare ordinals, which need only that meets exist. What the bare ordinals lack is a **top**: they ascend without bound,
so they are not a complete lattice and not a frame, and two nuclei there can have no common upper bound (§ III).

This file adjoins that missing top. `WithTop Ordinal` is the ordinals plus one point at infinity ⊤. That single
addition turns the ordinals into a **complete linear order**, and a complete linear order is a `Order.Frame`
(Mathlib: `CompleteLinearOrder → CompletelyDistribLattice → CompleteDistribLattice → Frame`, all by instance
resolution — nothing to prove). On a frame, the **nuclei** (modalities / predicated differences) form a `Frame`
and the **sublocales** (the systems they generate) form a `Coframe`: the *lattice of systems*.

**Why this is the boundary doing the work.** Bare `Ordinal` has no top (`IsEmpty (OrderTop Ordinal)`,
`ZeroParadox/Category/DieNucleus.lean` § IV); the ceiling, ⊤ of `WithTop Ordinal`, unlocks the lattice. Reading it as
the infinite pole is a placement Reading (`ZeroParadox/Multihomed/BoundaryOrder.lean` § I): the pole chart's coincidence
witness `infinitude_forces_infinite_complexity` (`ZeroParadox/BottomCannotBe.lean` § INVERSION) takes an `InfinitudeFloor`
carrier, and every infinite carrier admits one (`infinitudeFloor_nonempty_iff_infinite`), so the class cannot single out
⊤ of `WithTop Ordinal`. The placement is a theorem: `phaseEquivWithTop` sends `Phase.floor` to the greatest element
(the `IsTop` half of `phaseEquivWithTop_floor_covers_nothing`, BoundaryOrder § I). Its NOVELTY, a NEXT bottom, is
the framework's commitment, not a theorem (`ZeroParadox/Order/SnapCannotBe.lean` § IV): `phaseFloorToTop`, defined as
`phaseEquivWithBot.symm.trans phaseEquivWithTop`, re-places one `Phase.floor`, sending ⊥ of `WithBot Ordinal` to ⊤ of
`WithTop Ordinal` (`phaseFloorToTop_apply.1`); in the 2-adic realization the arc reapproaches the same 0 (`snap_arc_z2_loop`).

**Honest scope.** The frame structure of `WithTop Ordinal` is Mathlib's, and that the nuclei on a frame form a frame
is locale theory (Escardó, "Joins in the frame of nuclei", Applied Categorical Structures 11 (2003), § 1 of the author's
preprint); §§ I–II only *instantiate* them. § IV lifts the specific snap: `snapNucleusTop` reuses the ordinal snap-closure
through `WithTop.map`, and `snapSublocale = snapNucleusTop.toSublocale` is the snap-generated system as a named point in it.

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

/-- The single modality on the bare ordinals (from `ZeroParadox/Ordinal/SnapNucleus.lean`). -/
noncomputable example : Nucleus Ordinal := snapNucleus

/-- `Statement:` two nuclei on `Ordinal` have no common upper bound in the pointwise order: `snapNucleus`
    (closed points the `x` with `ω ^ x = x`, `snapNucleus_isClosed_iff` in
    `ZeroParadox/Ordinal/SnapSuccession.lean`) and the nucleus `k` fixing each successor ordinal and
    sending any other `x` to `succ x`, so that every value of `k` is a successor. A nucleus `m` above
    both fixes `m 0`, so both fix it (a larger nucleus has fewer fixed points:
    `Motion.isLanding_ofNucleus_anti` with `Motion.isLanding_ofNucleus_iff`,
    `ZeroParadox/Category/DieNucleus.lean`, on a meet-semilattice; Mathlib's `Nucleus.range_subset_range`
    assumes a frame); so `m 0` is a successor `succ b`, and no `succ b` has `ω ^ succ b = succ b`.
    `Reading:` adjacent prior art, for closure operations on a poset rather than nuclei: Elliott,
    arXiv:1101.2462 (2011), § 4, p. 12 (`⋆₁ ≤ ⋆₂` iff the fixed set of `⋆₁` contains that of `⋆₂`), and
    Lemma 4.2, p. 13 (on a bounded complete poset, joins of BOUNDED families of closure operations). -/
example : ∃ j k : Nucleus Ordinal, ∀ m : Nucleus Ordinal, ¬ (j ≤ m ∧ k ≤ m) := by
  classical
  let kf : Ordinal → Ordinal := fun x => if ∃ b, succ b = x then x else succ x
  have hsucc : ∀ x, ∃ b, succ b = kf x := fun x => by
    by_cases h : ∃ b, succ b = x
    · simp only [kf, if_pos h]; exact h
    · simp only [kf, if_neg h]; exact ⟨x, rfl⟩
  have hle : ∀ x, x ≤ kf x := fun x => by
    by_cases h : ∃ b, succ b = x
    · simp only [kf, if_pos h, le_refl]
    · simp only [kf, if_neg h]; exact le_succ x
  have hfix : ∀ x, (∃ b, succ b = x) → kf x = x := fun x h => by simp only [kf, if_pos h]
  have hmono : Monotone kf := fun x y hxy => by
    by_cases h : ∃ b, succ b = x
    · rw [hfix x h]; exact hxy.trans (hle y)
    · rcases hxy.lt_or_eq with hlt | rfl
      · simp only [kf, if_neg h]; exact (succ_le_of_lt hlt).trans (hle y)
      · exact le_rfl
  let k : Nucleus Ordinal :=
    { toFun := kf
      map_inf' := fun a b => by
        rcases le_total a b with h | h
        · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hmono h)]
        · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hmono h)]
      idempotent' := fun x => (hfix _ (hsucc x)).le
      le_apply' := hle }
  refine ⟨snapNucleus, k, fun m ⟨hj, hk⟩ => ?_⟩
  set z := m 0 with hz
  have hmz : m z = z := m.idempotent 0
  have hjz : snapNucleus z = z := le_antisymm ((hj z).trans hmz.le) snapNucleus.le_apply
  have hkz : kf z = z := le_antisymm ((hk z).trans hmz.le) (hle z)
  obtain ⟨b, hb⟩ := hsucc z
  rw [hkz] at hb
  have hfp : Ordinal.omega0 ^ z = z := by
    have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) z
    rwa [← snapNucleus_apply, hjz] at this
  rw [← hb] at hfp
  have hl : IsSuccLimit (Ordinal.omega0 ^ succ b) := by
    rw [Ordinal.opow_succ]
    exact Ordinal.isSuccLimit_mul_right (Ordinal.opow_pos _ Ordinal.omega0_pos)
      Ordinal.isSuccLimit_omega0
  rw [hfp] at hl
  exact Order.not_isSuccLimit_succ b hl

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

/-- The lift agrees with the base snap at ⊥ of `Ordinal` lifted: it sends `↑⊥` to `↑ε₀` (`epsilon0_eq_nfp_bot`),
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
