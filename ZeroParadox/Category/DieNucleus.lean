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
# UP legs as nuclei: the die on a meet-semilattice, the snap and its lift as members, the notation carrier as a non-member

## Engineer's Take

The die has evolved, and it is on version two now, so it is worth reevaluating what the die is and
what it means. We had a four-corner version of the ordinal towers, and that sounds very much like the
same structure we are building here. I thought we had built quite a bit on the nuclei already, and my
question was how much of this was mapped from those preexisting files. It should be mapped from them.

---
## Formal Overview (AI-assisted)
On a meet-semilattice a die motion with total, raising, `⊓`-preserving UP is a Mathlib `Nucleus`; a nucleus
with any OVER is a motion, and that round trip returns the nucleus (§ I). Landings are its fixed points,
and the order on UP legs is Mathlib's order on nuclei (§ II). Members (§ III): `snapNucleus` on `Ordinal`,
its lift `snapNucleusTop`, `dnegNucleus Prop`; non-member (§ IV): `SynONote` (`no_snap_nucleus`).
-/

namespace ZeroParadox

universe u

namespace Motion

variable {X : Type*} [SemilatticeInf X]

/-! ### § I. A motion with a `⊓`-preserving raising total UP is a nucleus, and back -/

/-- `Statement:` on a meet-semilattice, a motion whose UP is total, raises, and preserves `⊓` gives
    the Mathlib `Nucleus` `x ↦ up x`. -/
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

/-- `Statement:` `toNucleus` of `ofNucleus n s` is `n`: the round trip nucleus → motion → nucleus. -/
theorem toNucleus_ofNucleus (n : Nucleus X) (s : X → X → Prop) :
    toNucleus (ofNucleus n s) (ofNucleus_upTotal n s) (ofNucleus_upRaises n s)
      (fun _ _ => Nucleus.map_inf) = n := by
  ext x
  rfl

/-! ### § II. Landings, and the order on UP legs

The order `n ≤ m` below is Mathlib's `PartialOrder (Nucleus X)`, on any meet-semilattice. When `X` is
a frame it is the frame of nuclei, `Order.Frame (Nucleus X)`, the corpus's lattice of systems, with
its two ends `⊥ ≤ ⊤` and its order-dual identification with the coframe of sublocales
(`nucleusIsoSublocale`): `ZeroParadox/Category/DifferenceGeneratesSystem.lean`, and on `WithTop Ordinal`
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

/-- `Statement:` both directions: the landings of `ofNucleus m s` lie among those of `ofNucleus n s`
    iff `n ≤ m`; `isLanding_ofNucleus_anti` is the `←` half, and the `→` half takes `n` monotone from
    `map_inf'` at `y ⊓ m y = y`. The order on UP legs runs opposite to the inclusion of landing sets.
    `Reading:` on a frame the same iff is Mathlib's `Nucleus.range_subset_range` with
    `Nucleus.mem_range`, which Mathlib files in its frame section; a meet-semilattice suffices here. -/
theorem isLanding_ofNucleus_subset_iff (n m : Nucleus X) (s : X → X → Prop) :
    (∀ y, (ofNucleus m s).IsLanding y → (ofNucleus n s).IsLanding y) ↔ n ≤ m := by
  constructor
  · intro h y
    have hmm : m (m y) = m y := le_antisymm (m.idempotent' y) (m.le_apply' (m y))
    have hfix : n (m y) = m y :=
      (isLanding_ofNucleus_iff _ _ _).1 (h (m y) ((isLanding_ofNucleus_iff _ _ _).2 hmm))
    have hy : y ⊓ m y = y := inf_eq_left.mpr (m.le_apply' y)
    calc n y = n (y ⊓ m y) := by rw [hy]
      _ = n y ⊓ n (m y) := n.map_inf' y (m y)
      _ ≤ n (m y) := inf_le_right
      _ = m y := hfix
  · intro hnm y hy
    exact isLanding_ofNucleus_anti hnm s y hy

/-- `Statement:` at ⊥ of `Nucleus X`, the identity nucleus (Mathlib `instBot`, on any meet-semilattice), UP
    of `ofNucleus ⊥ s` is the identity, so every point is a landing (the `example` below). -/
theorem ofNucleus_bot_up (s : X → X → Prop) (x : X) : (ofNucleus ⊥ s).up x = Part.some x := rfl

-- Statement: every point is a landing of `ofNucleus ⊥ s`.
example (s : X → X → Prop) (x : X) : (ofNucleus ⊥ s).IsLanding x := Part.mem_some x

section
variable [OrderTop X]

/-- `Statement:` given `[OrderTop X]`, at ⊤ of `Nucleus X` (Mathlib `instTop`) UP of `ofNucleus ⊤ s` is ⊤. -/
theorem ofNucleus_top_up (s : X → X → Prop) (x : X) : (ofNucleus ⊤ s).up x = Part.some ⊤ := rfl

end

end Motion

/-! ### § III. Members and controls -/

/-- `Statement:` UP of `ordinalTowerMotion` (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) is total. -/
theorem ordinalTowerMotion_upTotal : ordinalTowerMotion.{u}.UpTotal :=
  Motion.ofTotal_upTotal _ _ _

/-- `Statement:` and it raises in `Ordinal`'s order: `a ≤ nfp (ω^·) a` (`Ordinal.le_nfp`). -/
theorem ordinalTowerMotion_upRaises : ordinalTowerMotion.{u}.UpRaises :=
  fun x _ hy => (Part.mem_some_iff.1 hy) ▸ Ordinal.le_nfp _ x

/-- `Statement:` and it preserves `⊓`: `nfp (ω^·)` is monotone and `Ordinal` is a chain, so it sends
    `min` to `min`, as `snapNucleus.map_inf'` does (`ZeroParadox/Ordinal/SnapNucleus.lean`). -/
theorem ordinalTowerMotion_up_inf (x y : Ordinal.{u}) :
    (ordinalTowerMotion.up (x ⊓ y)).get (ordinalTowerMotion_upTotal _) =
      (ordinalTowerMotion.up x).get (ordinalTowerMotion_upTotal x) ⊓
        (ordinalTowerMotion.up y).get (ordinalTowerMotion_upTotal y) := by
  show Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (x ⊓ y) =
    Ordinal.nfp (fun α => Ordinal.omega0 ^ α) x ⊓ Ordinal.nfp (fun α => Ordinal.omega0 ^ α) y
  have hmono : Monotone (Ordinal.nfp (fun α : Ordinal.{u} => Ordinal.omega0 ^ α)) :=
    Ordinal.nfp_monotone (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.monotone
  rcases le_total x y with h | h
  · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hmono h)]
  · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hmono h)]

/-- `Statement:` MEMBER on bare `Ordinal`, a meet-semilattice with no top (§ IV): `toNucleus` of
    `ordinalTowerMotion` is `snapNucleus` (`ZeroParadox/Ordinal/SnapNucleus.lean`), by `rfl`. -/
theorem toNucleus_ordinalTowerMotion :
    Motion.toNucleus ordinalTowerMotion.{u} ordinalTowerMotion_upTotal ordinalTowerMotion_upRaises
      ordinalTowerMotion_up_inf = snapNucleus := rfl

-- `Statement:` UP of `ordinalTowerMotion` at `a` is `Part.some (snapNucleus a)`, by `rfl`.
-- `Reading:` the tower motion on the ordinals IS a nucleus motion, with no top adjoined; the next
-- member is its lift through `↑ : Ordinal → WithTop Ordinal`.
example (a : Ordinal.{u}) : ordinalTowerMotion.up a = Part.some (snapNucleus a) := rfl

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
    `Reading:` measured `[propext]` (printed below). The `SemilatticeInf Prop` instance in the statement
    is the one unification reads off the pinned `Prop.instHeytingAlgebra` through `Lattice.toSemilatticeInf`,
    and that instance is choice-free; the instance `inferInstance` synthesizes for `SemilatticeInf Prop`
    routes through `Prop.instCompleteLinearOrder` and carries `Classical.choice`, as `Order.Frame Prop`
    does, and forcing it into this motion carries that footprint (measured 2026-10-21). The meet-semilattice
    binder is met from the nucleus's type, where a frame binder had to be synthesized. -/
theorem em_iff_ofNucleus_dneg_isLanding (s : Prop → Prop → Prop) :
    ExcludedMiddle ↔ ∀ p : Prop,
      (Motion.ofNucleus (@dnegNucleus Prop Prop.instHeytingAlgebra) s).IsLanding p := by
  rw [em_iff_dnegNucleus_trivial]
  exact forall_congr' fun p => (Motion.isLanding_ofNucleus_iff _ _ _).symm

-- Reading (cited, not claimed): neighbour: Fellin and Schuster, "A General Glivenko–Gödel Theorem for
-- Nuclei", EPTCS 351 (MFPS 2021), 2021, § 5.1 with Theorem 3.8 and Application 5.3(1), pp. 56, 60: for
-- `¬¬` as a nucleus over intuitionistic logic `⊢i`, the stability axiom `¬¬ϕ ⊲ ϕ` is RAA, so its
-- strong extension is classical logic `⊢c`, and `Γ ⊢c ϕ ⟺ Γ ⊢i ¬¬ϕ`; delta: theirs is conservation
-- between two provability relations and never names excluded middle, ours is the fixed-point
-- statement on the Heyting algebra `Prop` with `p ∨ ¬p` as the other side, in both directions.

-- Statement: MEMBER: the double-negation nucleus on `Prop` (`dnegNucleus`) read as a motion with the
-- empty OVER; `True` is a landing.
example : (Motion.ofNucleus (dnegNucleus Prop) (fun _ _ => False)).IsLanding True :=
  (Motion.isLanding_ofNucleus_iff _ _ _).2 (by simp [dnegNucleus])

-- Statement: CONTROL: on `Bool × Bool`, the map sending `(false, false)` to itself and every other
-- point to `(true, true)` is inflationary, idempotent and monotone, does not preserve `⊓` at
-- `(true, false) ⊓ (false, true)`, and is no nucleus.
example :
    let c : Bool × Bool → Bool × Bool := fun p => if p.1 || p.2 then (true, true) else (false, false)
    ((∀ p, p ≤ c p) ∧ (∀ p, c (c p) = c p) ∧ Monotone c) ∧
      c ((true, false) ⊓ (false, true)) ≠ c (true, false) ⊓ c (false, true) ∧
      ¬ ∃ n : Nucleus (Bool × Bool), ⇑n = c := by
  intro c
  refine ⟨⟨by decide, by decide, fun p q h => by revert p q; decide⟩, by decide, ?_⟩
  rintro ⟨n, hn⟩
  have := n.map_inf (x := (true, false)) (y := (false, true))
  rw [hn] at this
  revert this
  decide

-- Statement: CONTROL: on `Bool`, the constant map `⊥` preserves `⊓` and is idempotent, and is no
-- nucleus: it is not inflationary.
example :
    let c : Bool → Bool := fun _ => ⊥
    (∀ p q, c (p ⊓ q) = c p ⊓ c q) ∧ (∀ p, c (c p) = c p) ∧ ¬ ∃ n : Nucleus Bool, ⇑n = c := by
  intro c
  refine ⟨by decide, by decide, ?_⟩
  rintro ⟨n, hn⟩
  have := n.le_apply (x := true)
  rw [hn] at this
  exact absurd this (by decide)

/-! ### § IV. Non-member, and the fence: what bare `Ordinal` and `SynONote` lack

§ I–II are stated on a meet-semilattice, so § I reaches bare `Ordinal`: `toNucleus` of `ordinalTowerMotion` is
`snapNucleus` (§ III), the one nucleus `ZeroParadox/Ordinal/SnapMetaLattice.lean` § III places there. What bare
`Ordinal` lacks is a top over its order (the first `example` below), hence `⊤ : Nucleus Ordinal` (`ofNucleus_top_up`
takes `[OrderTop X]`) and the frame of nuclei, § II's two-ended lattice; adjoining ⊤ gives § III's frame, where
the lift `snapNucleusTop` is a member. `SynONote` (`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`) has no top
over its comparator order either (the next two `example`s), and there the obstruction is sharper: no nucleus on
it has only `omegaPow`-fixed landings, `no_snap_nucleus`, the `Nucleus`-typed corollary of the order-free
`no_snap_closure` (any idempotent endomap of `ONote`); its lift by a top, `E0Note`, is not examined here. -/

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

Measured from the build log, 2026-10-21. `toNucleus` depends on no axioms; `ofNucleus`, `ofNucleus_upTotal`,
`ofNucleus_upRaises`, `isLanding_ofNucleus_iff` and `em_iff_ofNucleus_dneg_isLanding` on `[propext]`;
`toNucleus_ofNucleus`, `isLanding_ofNucleus_anti`, `isLanding_ofNucleus_subset_iff` and `ofNucleus_top_up` on
`[propext, Quot.sound]`. `ofNucleus_bot_up` is `rfl`, so its footprint is the statement's, through Mathlib's
`⊥ : Nucleus X` (`ofNucleus_top_up`, the same proof at `⊤`, is the control). The bare-`Ordinal` member and
`snapNucleusTop_isLanding_iff` are STATEMENT-CARRIED through Mathlib's `Ordinal` fixed-point theory, as for
`snapNucleus` in `ZeroParadox/Ordinal/SnapNucleus.lean`. On `Prop` the statement's `SemilatticeInf` instance is
read off `Prop.instHeytingAlgebra`, `[propext]`; the synthesized one carries choice (both printed below). -/

section PurityCheck
open ZeroParadox

#print axioms Motion.toNucleus
#print axioms Motion.ofNucleus
#print axioms Motion.ofNucleus_upTotal
#print axioms Motion.ofNucleus_upRaises
#print axioms Motion.toNucleus_ofNucleus
#print axioms Motion.isLanding_ofNucleus_iff
#print axioms Motion.isLanding_ofNucleus_anti
#print axioms Motion.isLanding_ofNucleus_subset_iff
#print axioms Motion.ofNucleus_bot_up
#print axioms Motion.ofNucleus_top_up
#print axioms ordinalTowerMotion_upTotal
#print axioms ordinalTowerMotion_upRaises
#print axioms ordinalTowerMotion_up_inf
#print axioms toNucleus_ordinalTowerMotion
#print axioms snapNucleusTop_isLanding_iff
#print axioms em_iff_ofNucleus_dneg_isLanding
-- Mathlib, the two `Prop` instances contrasted above: the pinned one and the synthesized one.
#print axioms Prop.instHeytingAlgebra
#print axioms Prop.instCompleteLinearOrder

end PurityCheck
