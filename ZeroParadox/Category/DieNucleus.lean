import ZeroParadox.Die
import ZeroParadox.Category.DoubleNegationNucleus
import ZeroParadox.Category.ExcludedMiddleBridge
import ZeroParadox.Ordinal.SnapMetaLattice
import ZeroParadox.Ordinal.SnapSuccession
import ZeroParadox.Ordinal.SnapNucleusConstructive
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Multihomed.BoundaryOrder
import Mathlib.Order.Nucleus
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# UP legs as nuclei: the die on a frame, the lifted snap as a member, the notation carrier as a non-member

## Engineer's Take

The die has evolved, and it is on version two now, so it is worth reevaluating what the die is and
what it means. We had a four-corner version of the ordinal towers, and that sounds very much like the
same structure we are building here. I thought we had built quite a bit on the nuclei already, and my
question was how much of this was mapped from those preexisting files. It should be mapped from them.

---
## Formal Overview (AI-assisted)
On a frame, a die motion with total, raising, `⊓`-preserving UP is a Mathlib `Nucleus` and back (§ I);
landings are its fixed points, the order on UP legs the corpus's lattice of systems (§ II). Members (§ III):
`snapNucleusTop` on `WithTop Ordinal`, landings `⊤` and the lifted ε-numbers; `dnegNucleus Prop`, all
points landings iff excluded middle. Non-member (§ IV): `SynONote`, no top, so no frame (`no_snap_nucleus`).
-/

namespace ZeroParadox

namespace Motion

variable {X : Type*} [Order.Frame X]

/-! ### § I. A motion with a `⊓`-preserving raising total UP is a nucleus, and back -/

/-- `Statement:` on a frame, a motion whose UP is total, raises, and preserves `⊓` gives the Mathlib
    `Nucleus` `x ↦ up x`. -/
-- [ZP-CUSTOM] extends: Mathlib.Order.Nucleus | reason: reads the die's UP leg as a `Nucleus`;
-- idempotence comes from the `Motion` field `up_idem`, inflation and `⊓`-preservation are hypotheses.
def toNucleus (M : Motion X) (ht : M.UpTotal) (hr : M.UpRaises)
    (hinf : ∀ x y, (M.up (x ⊓ y)).get (ht _) = (M.up x).get (ht x) ⊓ (M.up y).get (ht y)) :
    Nucleus X where
  toFun x := (M.up x).get (ht x)
  map_inf' := hinf
  idempotent' x := by
    have h1 := M.up_idem x _ (Part.get_mem (ht x))
    exact (Part.get_eq_of_mem h1 (ht _)).le
  le_apply' x := hr x _ (Part.get_mem (ht x))

/-- `Statement:` a nucleus `n` and any relation `s` give the motion with UP `n` and OVER `s`. -/
-- [ZP-CUSTOM] extends: Mathlib.Order.Nucleus | reason: the inverse reading of `toNucleus`, through
-- the die's `Motion.ofTotal`. Idempotence from the primed fields: Mathlib's `Nucleus.idempotent`
-- routes through `toClosureOperator` and carries `Classical.choice` (measured 2026-10-21).
def ofNucleus (n : Nucleus X) (s : X → X → Prop) : Motion X :=
  ofTotal n (fun x => le_antisymm (n.idempotent' x) (n.le_apply' (n x))) s

/-- `Statement:` UP of `ofNucleus n s` is total. -/
theorem ofNucleus_upTotal (n : Nucleus X) (s : X → X → Prop) : (ofNucleus n s).UpTotal :=
  fun _ => trivial

/-- `Statement:` UP of `ofNucleus n s` raises. -/
theorem ofNucleus_upRaises (n : Nucleus X) (s : X → X → Prop) : (ofNucleus n s).UpRaises :=
  fun _ _ hy => (Part.mem_some_iff.1 hy) ▸ n.le_apply' _

/-- `Statement:` `toNucleus` of `ofNucleus n s` is `n`. -/
theorem toNucleus_ofNucleus (n : Nucleus X) (s : X → X → Prop) :
    toNucleus (ofNucleus n s) (ofNucleus_upTotal n s) (ofNucleus_upRaises n s)
      (fun _ _ => Nucleus.map_inf) = n := by
  ext x
  rfl

/-! ### § II. Landings, and the order on UP legs is the lattice of systems

The order `n ≤ m` below is the frame of nuclei, `Order.Frame (Nucleus X)`, with its two ends
`⊥ ≤ ⊤` and its order-dual identification with the coframe of sublocales (`nucleusIsoSublocale`):
`ZeroParadox/Category/DifferenceGeneratesSystem.lean`, and on `WithTop Ordinal`
`ZeroParadox/Ordinal/SnapMetaLattice.lean` § II. Nothing of it is re-derived here. -/

/-- `Statement:` `y` is a landing of `ofNucleus n s` iff `n y = y`; both directions. -/
theorem isLanding_ofNucleus_iff (n : Nucleus X) (s : X → X → Prop) (y : X) :
    (ofNucleus n s).IsLanding y ↔ n y = y :=
  ⟨fun h => (Part.mem_some_iff.1 h).symm, fun h => Part.mem_some_iff.2 h.symm⟩

/-- `Statement:` if `n ≤ m`, every landing of `ofNucleus m s` is a landing of `ofNucleus n s`. -/
theorem isLanding_ofNucleus_anti {n m : Nucleus X} (hnm : n ≤ m) (s : X → X → Prop) (y : X) :
    (ofNucleus m s).IsLanding y → (ofNucleus n s).IsLanding y := by
  rw [isLanding_ofNucleus_iff, isLanding_ofNucleus_iff]
  intro hm
  exact le_antisymm (le_trans (hnm y) hm.le) (n.le_apply' y)

-- `Statement:` both directions: the landings of `ofNucleus m s` lie among those of `ofNucleus n s`
-- iff `n ≤ m` (Mathlib `Nucleus.range_subset_range`, `Nucleus.mem_range`). The order on UP legs runs
-- opposite to the inclusion of landing sets; `isLanding_ofNucleus_anti` is the `←` half.
example (n m : Nucleus X) (s : X → X → Prop) :
    (∀ y, (ofNucleus m s).IsLanding y → (ofNucleus n s).IsLanding y) ↔ n ≤ m := by
  rw [← Nucleus.range_subset_range]
  constructor
  · intro h x hx
    exact Nucleus.mem_range.2 ((isLanding_ofNucleus_iff _ _ _).1
      (h x ((isLanding_ofNucleus_iff _ _ _).2 (Nucleus.mem_range.1 hx))))
  · intro h y hy
    exact (isLanding_ofNucleus_iff _ _ _).2 (Nucleus.mem_range.1
      (h (Nucleus.mem_range.2 ((isLanding_ofNucleus_iff _ _ _).1 hy))))

/-- `Statement:` at the end `⊥` of the lattice of systems, UP of `ofNucleus ⊥ s` is the identity
    (every point is then a landing: the `example` below). -/
theorem ofNucleus_bot_up (s : X → X → Prop) (x : X) : (ofNucleus ⊥ s).up x = Part.some x := rfl

-- Statement: every point is a landing of `ofNucleus ⊥ s`.
example (s : X → X → Prop) (x : X) : (ofNucleus ⊥ s).IsLanding x := Part.mem_some x

/-- `Statement:` at the end `⊤` of the lattice of systems, UP of `ofNucleus ⊤ s` is the constant ⊤. -/
theorem ofNucleus_top_up (s : X → X → Prop) (x : X) : (ofNucleus ⊤ s).up x = Part.some ⊤ := rfl

end Motion

/-! ### § III. Members and controls -/

/-- `Statement:` MEMBER: on the frame `WithTop Ordinal` (`ZeroParadox/Ordinal/SnapMetaLattice.lean`
    § I), for any OVER `s`, `x` is a landing of `ofNucleus snapNucleusTop s` iff `x = ⊤` or
    `x = ↑(ε_ o)` for some `o`: the closed points of the base nucleus by `snapNucleus_isClosed_iff`,
    enumerated by Mathlib's `mem_range_deriv`. `Reading:` `⊤`, the point at infinity, is the one
    landing the lift adds; the `example`s after it place it in the floor-above chart, exclude the
    ordinals' `⊥`, and give the round trip. -/
theorem snapNucleusTop_isLanding_iff (s : WithTop Ordinal → WithTop Ordinal → Prop)
    (x : WithTop Ordinal) :
    (Motion.ofNucleus snapNucleusTop s).IsLanding x ↔
      x = ⊤ ∨ ∃ o : Ordinal, x = (Ordinal.epsilon o : WithTop Ordinal) := by
  rw [Motion.isLanding_ofNucleus_iff]
  induction x using WithTop.recTopCoe with
  | top => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | coe a =>
    have h1 : snapNucleusTop (a : WithTop Ordinal) = ((snapNucleus a : Ordinal) : WithTop Ordinal) :=
      rfl
    rw [h1, WithTop.coe_eq_coe, snapNucleus_isClosed_iff]
    constructor
    · intro h
      obtain ⟨o, ho⟩ := (Ordinal.mem_range_deriv (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).2 h
      exact Or.inr ⟨o, by rw [Ordinal.epsilon_eq_deriv, ho]⟩
    · rintro (h | ⟨o, ho⟩)
      · exact absurd h WithTop.coe_ne_top
      · rw [WithTop.coe_eq_coe] at ho
        subst ho
        exact Ordinal.omega0_opow_epsilon o

-- `Statement:` COINCIDENCE: `⊤` is a landing, and in the floor-above order of the boundary model it
-- is the floor, `phaseEquivWithTop Phase.floor` (`ZeroParadox/Multihomed/BoundaryOrder.lean` § I):
-- the point at infinity and the floor read from above are one landing in two charts.
example (s : WithTop Ordinal → WithTop Ordinal → Prop) :
    (Motion.ofNucleus snapNucleusTop s).IsLanding ⊤ ∧
      (⊤ : WithTop Ordinal) = phaseEquivWithTop Phase.floor :=
  ⟨(snapNucleusTop_isLanding_iff s ⊤).2 (Or.inl rfl), rfl⟩

-- `Statement:` the ordinals' `⊥` lifted, `↑⊥`, is not a landing: UP sends it to `↑ε₀`
-- (`snapNucleusTop_coe_bot`) and `ε₀ ≠ ⊥` in `Ordinal` (`epsilon0_ne_bot`).
example (s : WithTop Ordinal → WithTop Ordinal → Prop) :
    ¬ (Motion.ofNucleus snapNucleusTop s).IsLanding ((⊥ : Ordinal) : WithTop Ordinal) := by
  rw [Motion.isLanding_ofNucleus_iff, snapNucleusTop_coe_bot]
  intro h
  exact epsilon0_ne_bot (WithTop.coe_injective h)

-- `Statement:` UP of this member at `↑a` is UP of the die's ordinal motion `ordinalTowerMotion`
-- (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) at `a`, pushed through `↑` (`Part.map`), and at `⊤`
-- it is `Part.some ⊤`; both by `rfl`. The OVER `s` is any relation on `WithTop Ordinal`.
example (s : WithTop Ordinal → WithTop Ordinal → Prop) (a : Ordinal) :
    (Motion.ofNucleus snapNucleusTop s).up (a : WithTop Ordinal) =
      (ordinalTowerMotion.up a).map ((↑) : Ordinal → WithTop Ordinal) := rfl
example (s : WithTop Ordinal → WithTop Ordinal → Prop) :
    (Motion.ofNucleus snapNucleusTop s).up ⊤ = Part.some ⊤ := rfl

-- `Statement:` the round trip: `toNucleus` of this member is `snapNucleusTop`
-- (`toNucleus_ofNucleus`), `⊓`-preservation supplied by the nucleus itself (`Nucleus.map_inf`).
example (s : WithTop Ordinal → WithTop Ordinal → Prop) :
    Motion.toNucleus (Motion.ofNucleus snapNucleusTop s) (Motion.ofNucleus_upTotal _ _)
      (Motion.ofNucleus_upRaises _ _) (fun _ _ => Nucleus.map_inf) = snapNucleusTop :=
  Motion.toNucleus_ofNucleus _ _

/-- `Statement:` MEMBER: excluded middle iff every proposition is a landing of
    `ofNucleus (dnegNucleus Prop) s`, for any OVER `s`: `em_iff_dnegNucleus_trivial` through
    `isLanding_ofNucleus_iff`, the Heyting instance pinned to `Prop.instHeytingAlgebra` as there.
    `Reading:` `em_iff_dnegNucleus_trivial` measures `[propext]`; this statement carries the
    `Order.Frame Prop` instance `ofNucleus` takes, which by `inferInstance` measures
    `[propext, Classical.choice, Quot.sound]` (2026-10-21), the footprint printed below. -/
theorem em_iff_ofNucleus_dneg_isLanding (s : Prop → Prop → Prop) :
    ExcludedMiddle ↔ ∀ p : Prop,
      (Motion.ofNucleus (@dnegNucleus Prop Prop.instHeytingAlgebra) s).IsLanding p := by
  rw [em_iff_dnegNucleus_trivial]
  exact forall_congr' fun p => (Motion.isLanding_ofNucleus_iff _ _ _).symm

-- Statement: MEMBER: the double-negation nucleus on `Prop` (`dnegNucleus`) read as a motion with the
-- empty OVER; `True` is a landing.
example : (Motion.ofNucleus (dnegNucleus Prop) (fun _ _ => False)).IsLanding True :=
  (Motion.isLanding_ofNucleus_iff _ _ _).2 (by simp [dnegNucleus])

-- Statement: CONTROL: on the frame `Bool × Bool`, the map sending `(false, false)` to itself and every
-- other point to `(true, true)` is inflationary, idempotent and monotone, and is no nucleus: it does
-- not preserve `⊓` at `(true, false) ⊓ (false, true)`.
example :
    let c : Bool × Bool → Bool × Bool := fun p => if p.1 || p.2 then (true, true) else (false, false)
    ((∀ p, p ≤ c p) ∧ (∀ p, c (c p) = c p) ∧ Monotone c) ∧ ¬ ∃ n : Nucleus (Bool × Bool), ⇑n = c := by
  intro c
  refine ⟨⟨by decide, by decide, fun p q h => by revert p q; decide⟩, ?_⟩
  rintro ⟨n, hn⟩
  have := n.map_inf (x := (true, false)) (y := (false, true))
  rw [hn] at this
  revert this
  decide

-- Statement: CONTROL: on `Bool`, the constant map `false` preserves `⊓` and is idempotent, and is no
-- nucleus: it is not inflationary.
example : ¬ ∃ n : Nucleus Bool, ⇑n = fun _ => (⊥ : Bool) := by
  rintro ⟨n, hn⟩
  have := n.le_apply (x := true)
  rw [hn] at this
  exact absurd this (by decide)

/-! ### § IV. Non-member, and the fence: no top, so no frame over the given order

`toNucleus` and `ofNucleus` are stated on a frame, and a frame has a top (`isMax_top`). Two corpus
carriers have none over their given order, so § I–II do not reach them as stated: bare `Ordinal`,
where `snapNucleus` is one nucleus (`ZeroParadox/Ordinal/SnapMetaLattice.lean` § III) and
`ordinalTowerMotion`, `ordinalSuccMotion` are motions; and `SynONote`
(`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`). Adjoining ⊤ to the ordinals gives § III's frame.
On `SynONote` the obstruction is sharper and order-free, `no_snap_nucleus`; the corpus's lift of it by
a top, `E0Note` (`ZeroParadox/Ordinal/PricedInterface.lean`), is not examined here. -/

-- `Statement:` no `OrderTop` over the ordinals' order: no greatest element (Mathlib `NoMaxOrder`).
example : IsEmpty (OrderTop Ordinal) := ⟨fun h => by
  haveI := h
  exact not_isMax (⊤ : Ordinal) isMax_top⟩

-- `Statement:` none over the comparator order on `SynONote`: every notation is strictly below a
-- tower stage (`tower_no_upper_bound`).
example : NoMaxOrder SynONote := ⟨fun x => by
  obtain ⟨n, hn⟩ := tower_no_upper_bound (ofSyn x)
  exact ⟨toSyn (tower n), (syn_cmp_gt_iff_lt _ _).1 hn⟩⟩
example : IsEmpty (OrderTop SynONote) := ⟨fun h => by
  haveI := h
  obtain ⟨n, hn⟩ := tower_no_upper_bound (ofSyn (⊤ : SynONote))
  exact absurd (le_top : toSyn (tower n) ≤ ⊤) (not_le_of_gt ((syn_cmp_gt_iff_lt _ _).1 hn))⟩

-- `Statement:` NON-MEMBER, the die form of `no_snap_nucleus` with no order on the motion: for every
-- nucleus `j` on `SynONote` and any OVER `s`, it is not the case that every landing of `ofTotal j _ s`
-- is fixed by `omegaPow`. The theorem does not say `j` has no landings: `idNucleus` has every point.
example (j : Nucleus SynONote) (s : SynONote → SynONote → Prop) :
    ¬ ∀ x : SynONote,
      (Motion.ofTotal j (fun x => le_antisymm (j.idempotent' x) (j.le_apply' (j x))) s).IsLanding x →
        omegaPow (ofSyn x) = ofSyn x :=
  fun h => no_snap_nucleus j fun x hx => h x (Part.mem_some_iff.2 hx.symm)

-- `Statement:` the landings of `ofTotal j _ s` are the closed points of `j`; both directions.
example (j : Nucleus SynONote) (s : SynONote → SynONote → Prop) (x : SynONote) :
    (Motion.ofTotal j (fun x => le_antisymm (j.idempotent' x) (j.le_apply' (j x))) s).IsLanding x ↔
      j x = x :=
  ⟨fun h => (Part.mem_some_iff.1 h).symm, fun h => Part.mem_some_iff.2 h.symm⟩

end ZeroParadox

/-! ## Axiom Purity Check

§ I–II measure `[propext, Quot.sound]` except `ofNucleus_bot_up`: its proof is `rfl`, so its footprint
is the statement's, through Mathlib's `⊥ : Nucleus X` (`ofNucleus_top_up`, the same proof at `⊤`, is
the control). `snapNucleusTop_isLanding_iff` and `em_iff_ofNucleus_dneg_isLanding` are
STATEMENT-CARRIED (statement control, measured 2026-10-21): the first through Mathlib's `Ordinal`
fixed-point theory, as recorded for `snapNucleus` in `ZeroParadox/Ordinal/SnapNucleus.lean`; the second
through the `Order.Frame Prop` instance. -/

section PurityCheck
open ZeroParadox

#print axioms Motion.toNucleus
#print axioms Motion.ofNucleus
#print axioms Motion.ofNucleus_upTotal
#print axioms Motion.ofNucleus_upRaises
#print axioms Motion.toNucleus_ofNucleus
#print axioms Motion.isLanding_ofNucleus_iff
#print axioms Motion.isLanding_ofNucleus_anti
#print axioms Motion.ofNucleus_bot_up
#print axioms Motion.ofNucleus_top_up
#print axioms snapNucleusTop_isLanding_iff
#print axioms em_iff_ofNucleus_dneg_isLanding

end PurityCheck
