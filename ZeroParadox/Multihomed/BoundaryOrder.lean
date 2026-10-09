import ZeroParadox.Order.UpAndOver
import ZeroParadox.Multihomed.Boundary
import ZeroParadox.Order.LeastFixedPoint
import ZeroParadox.Ordinal.SnapMetaLattice
import Mathlib.Order.Cover
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The boundary model ordered: floor below (`WithBot Ordinal`), floor above (`WithTop Ordinal`)

## Engineer's Take

Bottom is a role. Calling it strictly the lattice floor is not correct.

I think epsilon zero is just as much of a role as bottom itself is.. all of our units here are
relative

a top element with nothing above it owes no next step. It's hit its boundary.

---

## Formal Overview (AI-assisted)
`Phase` (`ZeroParadox/Multihomed/Boundary.lean`) is equivalent to `WithBot Ordinal` and to
`WithTop Ordinal`; both agree with `phaseRel` on the ascent, neither is `phaseRel`, in each `↑ε₀` is
the least landing above the least element (§ I, § IV); `phaseUpAndOver` is on the first (§ III).
-/

namespace ZeroParadox

open Order Ordinal

/-! ### § I. Two orders on `Phase`: the floor below, the floor above -/

/-- `Statement:` `Phase` and `WithBot Ordinal` are equivalent: `floor ↦ ⊥ : WithBot Ordinal`,
    `up o ↦ ↑o`, both round trips by `rfl` on each constructor. -/
def phaseEquivWithBot : Phase ≃ WithBot Ordinal where
  toFun
    | Phase.floor => ⊥
    | Phase.up o => (o : WithBot Ordinal)
  invFun
    | ⊥ => Phase.floor
    | (o : Ordinal) => Phase.up o
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

/-- `Statement:` `Phase` and `WithTop Ordinal` are equivalent: `floor ↦ ⊤ : WithTop Ordinal`,
    `up o ↦ ↑o`, both round trips by `rfl` on each constructor. -/
def phaseEquivWithTop : Phase ≃ WithTop Ordinal where
  toFun
    | Phase.floor => ⊤
    | Phase.up o => (o : WithTop Ordinal)
  invFun
    | ⊤ => Phase.floor
    | (o : Ordinal) => Phase.up o
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

-- `Statement:` the two members are Mathlib's ordinal sums `1 ⊕ₗ Ordinal` and `Ordinal ⊕ₗ 1`.
example : WithBot Ordinal ≃o Lex (PUnit ⊕ Ordinal) := WithBot.orderIsoPUnitSumLex
example : WithTop Ordinal ≃o Lex (Ordinal ⊕ PUnit) := WithTop.orderIsoSumLexPUnit

/-- `Statement:` on ascent states `phaseRel` is the strict order of `WithBot Ordinal` read through
    `phaseEquivWithBot`. -/
theorem phaseRel_up_iff_withBot (a b : Ordinal) :
    phaseRel (Phase.up a) (Phase.up b) ↔
      phaseEquivWithBot (Phase.up a) < phaseEquivWithBot (Phase.up b) :=
  WithBot.coe_lt_coe.symm

/-- `Statement:` on ascent states `phaseRel` is the strict order of `WithTop Ordinal` read through
    `phaseEquivWithTop`. -/
theorem phaseRel_up_iff_withTop (a b : Ordinal) :
    phaseRel (Phase.up a) (Phase.up b) ↔
      phaseEquivWithTop (Phase.up a) < phaseEquivWithTop (Phase.up b) :=
  WithTop.coe_lt_coe.symm

-- `Reading:` Tim (2026-10-02): the floor's placement is "a selection with a collection of mandatory
-- members". The collection is the placements of `Phase` in a linear order compatible with `phaseRel`
-- on the ascent; the mandatory members are the two where the floor is an extreme, least element
-- (floor below, `phase_floor_isBot`) and greatest element (floor above,
-- `phaseEquivWithTop_floor_covers_nothing`). Their existence is the two equivalences and their
-- compatibility the two theorems above. Middle placements are allowed members, not mandatory ones
-- (the `example` after `phase_placement_extreme_iff`). Read as poles, floor below is the empty pole
-- and floor above the infinite pole; that is a reading of placement, not the relation chart's pole
-- forms (the COINCIDENCE `example` at the end of § I).

/-- `Statement:` for an injective map of `Phase` into a linear order that agrees with `phaseRel` on
    ascent states, the floor's image is the least image iff it lies below the snap's image, and the
    greatest image iff it lies above every ascent state's image. -/
theorem phase_placement_extreme_iff {β : Type*} [LinearOrder β] (f : Phase → β)
    (hf : Function.Injective f)
    (hc : ∀ a b : Ordinal, phaseRel (Phase.up a) (Phase.up b) ↔ f (Phase.up a) < f (Phase.up b)) :
    ((∀ x, f Phase.floor ≤ f x) ↔ f Phase.floor < f snap) ∧
      ((∀ x, f x ≤ f Phase.floor) ↔ ∀ o, f (Phase.up o) < f Phase.floor) := by
  refine ⟨⟨fun h => lt_of_le_of_ne (h snap) (fun e => Phase.noConfusion (hf e)), fun h x => ?_⟩,
    ⟨fun h o => lt_of_le_of_ne (h _) (fun e => Phase.noConfusion (hf e)), fun h x => ?_⟩⟩
  · cases x with
    | floor => exact le_rfl
    | up o =>
      rcases eq_zero_or_pos o with rfl | ho
      · exact h.le
      · exact (h.trans ((hc 0 o).1 ho)).le
  · cases x with
    | floor => exact le_rfl
    | up o => exact (h o).le

-- `Reading:` in the standard terminology the floor-least and floor-greatest placements are the empty
-- cut `(∅, I)` and the full cut `(I, ∅)` of the ascent `I`, its two improper cuts, each realized by the
-- one added element (Kuhlmann, Nart, "Cuts and small extensions of abelian ordered groups", arXiv
-- 2109.12528 (2021): § 1 for the improper cuts, § 4.2 eq. (8) and Lemma 4.6 for one-element extensions).

-- `Statement:` a middle placement: `floor ↦ 1`, `up 0 ↦ 0`, `up a ↦ a + 1` for `a ≠ 0`, injective
-- and compatible with `phaseRel` on the ascent, puts the floor strictly between the snap `up 0` and
-- `up 1`, so by `phase_placement_extreme_iff` its image is neither least nor greatest.
example : ∃ f : Phase → Ordinal.{0}, Function.Injective f ∧
    (∀ a b : Ordinal, phaseRel (Phase.up a) (Phase.up b) ↔ f (Phase.up a) < f (Phase.up b)) ∧
    f snap < f Phase.floor ∧ f Phase.floor < f (Phase.up 1) := by
  let f : Phase → Ordinal := fun x => match x with
    | Phase.floor => 1
    | Phase.up a => if a = 0 then 0 else a + 1
  have one_lt : ∀ {a : Ordinal}, a ≠ 0 → (1 : Ordinal) < a + 1 := fun ha =>
    Order.lt_add_one_iff.2 (Order.one_le_iff_ne_zero.2 ha)
  have hc : ∀ a b : Ordinal,
      phaseRel (Phase.up a) (Phase.up b) ↔ f (Phase.up a) < f (Phase.up b) := by
    intro a b
    change a < b ↔ (if a = 0 then 0 else a + 1) < (if b = 0 then 0 else b + 1)
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · subst ha; subst hb; simp
    · subst ha; rw [if_pos rfl, if_neg hb]
      exact ⟨fun _ => lt_of_lt_of_le (pos_iff_ne_zero.2 hb) le_self_add,
        fun _ => pos_iff_ne_zero.2 hb⟩
    · subst hb; rw [if_neg ha, if_pos rfl]
      exact ⟨fun h => absurd h (not_lt.2 (zero_le _)), fun h => absurd h (not_lt.2 (zero_le _))⟩
    · rw [if_neg ha, if_neg hb, ← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_lt_succ_iff.symm
  have key : ∀ b, (1 : Ordinal) ≠ f (Phase.up b) := fun b h => by
    change (1 : Ordinal) = if b = 0 then 0 else b + 1 at h
    by_cases hb : b = 0
    · rw [if_pos hb] at h; exact one_ne_zero h
    · rw [if_neg hb] at h; exact (one_lt hb).ne h
  refine ⟨f, fun x y h => ?_, hc, ?_, ?_⟩
  · cases x with
    | floor => cases y with
      | floor => rfl
      | up b => exact absurd h (key b)
    | up a => cases y with
      | floor => exact absurd h.symm (key a)
      | up b =>
        congr 1
        rcases lt_trichotomy a b with hab | hab | hab
        · exact absurd h ((hc a b).1 hab).ne
        · exact hab
        · exact absurd h ((hc b a).1 hab).ne'
  · change (if (0 : Ordinal) = 0 then 0 else (0 : Ordinal) + 1) < 1
    rw [if_pos rfl]; exact zero_lt_one
  · change (1 : Ordinal) < if (1 : Ordinal) = 0 then 0 else 1 + 1
    rw [if_neg one_ne_zero]; exact one_lt one_ne_zero

/-- `Statement:` in the floor-below order the boundary model's floor is below every ascent state. -/
theorem phaseEquivWithBot_floor_lt_up (o : Ordinal) :
    phaseEquivWithBot Phase.floor < phaseEquivWithBot (Phase.up o) :=
  WithBot.bot_lt_coe o

/-- `Statement:` in the floor-below order the ascent states compare as their ordinals do. -/
theorem phaseEquivWithBot_up_le_up (a b : Ordinal) :
    phaseEquivWithBot (Phase.up a) ≤ phaseEquivWithBot (Phase.up b) ↔ a ≤ b :=
  WithBot.coe_le_coe

/-- `Statement:` in the floor-above order the boundary model's floor is the greatest element and
    covers nothing: no `x : WithTop Ordinal` has `x ⋖ ⊤` (the ordinals have no greatest element). -/
theorem phaseEquivWithTop_floor_covers_nothing :
    IsTop (phaseEquivWithTop Phase.floor) ∧
      ∀ x : WithTop Ordinal, ¬ x ⋖ phaseEquivWithTop Phase.floor := by
  refine ⟨fun _ => le_top, fun x h => ?_⟩
  induction x using WithTop.recTopCoe with
  | top => exact lt_irrefl _ h.lt
  | coe a => exact not_isMax a (WithTop.coe_covBy_top.1 h)

-- `Statement:` the same snap closure lifted in the floor-above member is `snapNucleusTop`
-- (`ZeroParadox/Ordinal/SnapMetaLattice.lean`): it sends the snap `↑0` to `↑ε₀`
-- (`snapNucleusTop_coe_bot`) and fixes the floor `⊤ : WithTop Ordinal`.
example : snapNucleusTop (phaseEquivWithTop snap) = (epsilonZero : WithTop Ordinal) ∧
    snapNucleusTop (phaseEquivWithTop Phase.floor) = phaseEquivWithTop Phase.floor :=
  ⟨snapNucleusTop_coe_bot, rfl⟩

/-- `Statement:` in the floor-above order the snap `↑0` is the least element of `WithTop Ordinal`,
    and `↑ε₀` is the least closed point of `snapNucleusTop` strictly above it.
    `Reading:` ruling (A) in this member: `↑ε₀` is the first stable landing above the order's least
    element in both members; the least element is the floor `⊥ : WithBot Ordinal` in one
    (`phase_epsilon0_isLeast_landing_above_floor`) and the snap `↑0` in the other. -/
theorem phaseTop_epsilon0_isLeast_landing_above_snap :
    IsBot (phaseEquivWithTop snap) ∧
      IsLeast {x : WithTop Ordinal | snapNucleusTop x = x ∧ phaseEquivWithTop snap < x}
        (epsilonZero : WithTop Ordinal) := by
  refine ⟨fun x => ?_, ⟨?_, ?_⟩, ?_⟩
  · induction x using WithTop.recTopCoe with
    | top => exact le_top
    | coe a => exact WithTop.coe_le_coe.2 (zero_le a)
  · show WithTop.map _ ((epsilonZero : Ordinal) : WithTop Ordinal) = _
    rw [WithTop.map_coe]; exact congrArg _ (Ordinal.nfp_eq_self epsilonZero_fixedPoint)
  · exact WithTop.coe_lt_coe.2 (Ordinal.epsilon_pos 0)
  · rintro x ⟨hx, -⟩
    induction x using WithTop.recTopCoe with
    | top => exact le_top
    | coe a =>
      have ha : Ordinal.nfp (fun α => Ordinal.omega0 ^ α) a = a := WithTop.coe_injective hx
      have hfp : Ordinal.omega0 ^ a = a := by
        have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) a
        rwa [ha] at this
      exact WithTop.coe_le_coe.2 (epsilonZero_le_fixedPoint hfp)

/-- `Statement:` the floor's move from bottom to top, `phaseEquivWithBot.symm.trans
    phaseEquivWithTop`: it sends `⊥ : WithBot Ordinal` to `⊤ : WithTop Ordinal` and `↑o` to `↑o`. -/
def phaseFloorToTop : WithBot Ordinal ≃ WithTop Ordinal :=
  phaseEquivWithBot.symm.trans phaseEquivWithTop

/-- `Statement:` `phaseFloorToTop` sends the floor `⊥ : WithBot Ordinal` to `⊤ : WithTop Ordinal`,
    fixes every `↑o`, and is not monotone. -/
theorem phaseFloorToTop_apply :
    phaseFloorToTop ⊥ = ⊤ ∧ (∀ o : Ordinal, phaseFloorToTop o = o) ∧ ¬ Monotone phaseFloorToTop :=
  ⟨rfl, fun _ => rfl, fun h =>
    WithTop.not_top_le_coe (0 : Ordinal)
      (h (bot_le : (⊥ : WithBot Ordinal) ≤ ((0 : Ordinal) : WithBot Ordinal)))⟩

-- `Statement:` on the shared carrier `Option Ordinal` the map is the identity.
example : ∀ x : Option Ordinal, phaseFloorToTop x = x := by intro x; cases x <;> rfl

-- `Statement:` neither order is `phaseRel`: `phaseRel` relates the floor and an ascent state in
-- neither direction, while the floor-below order puts the floor below it and the floor-above order
-- above it; and `phaseRel` relates the floor to itself, which neither strict order does.
example (o : Ordinal) :
    (¬ phaseRel Phase.floor (Phase.up o) ∧ ¬ phaseRel (Phase.up o) Phase.floor) ∧
    phaseEquivWithBot Phase.floor < phaseEquivWithBot (Phase.up o) ∧
    phaseEquivWithTop (Phase.up o) < phaseEquivWithTop Phase.floor ∧
    (phaseRel Phase.floor Phase.floor ∧
      ¬ phaseEquivWithBot Phase.floor < phaseEquivWithBot Phase.floor ∧
      ¬ phaseEquivWithTop Phase.floor < phaseEquivWithTop Phase.floor) :=
  ⟨⟨id, id⟩, WithBot.bot_lt_coe o, WithTop.coe_lt_top o, trivial, lt_irrefl _, lt_irrefl _⟩

-- `Statement:` COINCIDENCE within `phaseRel` at the floor, in the pole labels of
-- `ZeroParadox/Multihomed/Boundary.lean`: the floor self-loops and is not accessible (the empty-pole
-- form, as `bot_not_acc` for `floorRel`), and a descent issues from it (the infinite-pole form, as
-- `floor_descent_from_bot` for `floorRel`), witnessed by the constant chain, the degenerate descent.
example : (phaseRel Phase.floor Phase.floor ∧ ¬ Acc phaseRel Phase.floor) ∧
    ∃ f : ℕ → Phase, f 0 = Phase.floor ∧ ∀ n, phaseRel (f (n + 1)) (f n) :=
  ⟨⟨trivial, snap_crossing.1⟩, fun _ => Phase.floor, rfl, fun _ => trivial⟩

/-! ### § II. The lifted closure -/

/-- `Statement:` a closure operator `c` on `α` lifts to `WithBot α` by `WithBot.map c`, fixing the
    adjoined `⊥ : WithBot α`; its monotone part is Mathlib's `OrderHom.withBotMap`. -/
def withBotClosure {α : Type*} [PartialOrder α] (c : ClosureOperator α) :
    ClosureOperator (WithBot α) :=
  ClosureOperator.mk' (WithBot.map c) c.monotone.withBot_map
    (fun x => by
      induction x using WithBot.recBotCoe with
      | bot => exact le_rfl
      | coe a => exact WithBot.coe_le_coe.2 (c.le_closure a))
    (fun x => by
      induction x using WithBot.recBotCoe with
      | bot => exact le_rfl
      | coe a => exact WithBot.coe_le_coe.2 (c.idempotent a).le)

-- `Statement:` the lift's underlying map is `OrderHom.withBotMap` of `c`.
example {α : Type*} [PartialOrder α] (c : ClosureOperator α) :
    ⇑(OrderHom.withBotMap c.toOrderHom) = ⇑(withBotClosure c) :=
  rfl

/-- `Statement:` the lifted closure fixes `⊥ : WithBot α` and acts as `c` on `↑a`. -/
theorem withBotClosure_apply {α : Type*} [PartialOrder α] (c : ClosureOperator α) :
    withBotClosure c ⊥ = ⊥ ∧ ∀ a : α, withBotClosure c a = (c a : WithBot α) :=
  ⟨rfl, fun _ => rfl⟩

/-! ### § III. The instance on the floor-below member: the corner at the floor

`Reading:` selected: this file's order and `phaseUpAndOver` use the floor-below member. -/

/-- `Statement:` `WithBot Ordinal` carries the shape with `up` the lifted `ordinalUpAndOver.up`
    (`nfp (ω^·)` on `↑o`, the floor `⊥ : WithBot Ordinal` fixed), the corner at the landing
    `⊥ : WithBot Ordinal` and its cover the snap `↑0`, which `up` sends to `↑ε₀ ≠ ↑0`, and covers
    `⊥ ⋖ ↑0`, `↑o ⋖ ↑(succ o)`. -/
noncomputable def phaseUpAndOver : UpAndOver (WithBot Ordinal) where
  up := withBotClosure ordinalUpAndOver.up
  corner := ⟨⊥, ((0 : Ordinal) : WithBot Ordinal), (withBotClosure _).isClosed_iff.2 rfl,
    WithBot.bot_covBy_coe.2 (fun b _ => zero_le b), fun h => by
      have h' : Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 0 = 0 := WithBot.coe_injective h
      rw [← epsilonZero_eq_nfp] at h'
      exact epsilon0_ne_zero h'⟩
  cover := fun y _ _ => by
    induction y using WithBot.recBotCoe with
    | bot => exact ⟨_, WithBot.bot_covBy_coe.2 (fun b _ => zero_le b)⟩
    | coe o =>
      exact ⟨((Order.succ o : Ordinal) : WithBot Ordinal), WithBot.coe_covBy_coe.2 (Order.covBy_succ o)⟩

/-! ### § IV. The floor, the snap `↑0` and `↑ε₀` in the floor-below order -/

/-- `Statement:` the boundary model's floor is the least element of the floor-below order. -/
theorem phase_floor_isBot : IsBot (phaseEquivWithBot Phase.floor) :=
  fun _ => bot_le

/-- `Statement:` the snap covers the boundary model's floor: `⊥ ⋖ ↑0` in `WithBot Ordinal`, nothing
    strictly between (Mathlib `WithBot.bot_covBy_coe`, at the ordinals' least element `0`). -/
theorem phase_floor_covBy_snap : phaseEquivWithBot Phase.floor ⋖ phaseEquivWithBot snap :=
  WithBot.bot_covBy_coe.2 (fun b _ => zero_le b)

/-- `Statement:` the tower operator `ω^·` lifted to `WithBot Ordinal`, fixing the floor
    `⊥ : WithBot Ordinal`. -/
noncomputable def phaseTower : WithBot Ordinal → WithBot Ordinal :=
  WithBot.map (fun a => Ordinal.omega0 ^ a)

/-- `Statement:` seeded at the snap `↑0`, the least fixed point of the lifted tower operator is
    `↑ε₀`. -/
theorem phase_epsilon0_isLeastFixedPointFrom_snap :
    IsLeastFixedPointFrom (· ≤ ·) phaseTower (phaseEquivWithBot snap)
      ((epsilonZero : Ordinal) : WithBot Ordinal) := by
  refine ⟨WithBot.coe_le_coe.2 (zero_le _), ?_, fun b hb hle => ?_⟩
  · show ((Ordinal.omega0 ^ epsilonZero : Ordinal) : WithBot Ordinal) = _
    rw [epsilonZero_fixedPoint]
  · induction b using WithBot.recBotCoe with
    | bot => exact absurd hle (WithBot.not_coe_le_bot _)
    | coe a => exact WithBot.coe_le_coe.2 (epsilonZero_le_fixedPoint (WithBot.coe_injective hb))

/-- `Statement:` the instance's `up` sends the snap `↑0`, the floor's cover, to `↑ε₀`, the landing
    reached over the corner (`UpAndOver.exists_next_landing`). -/
theorem phaseUp_snap :
    phaseUpAndOver.up (phaseEquivWithBot snap) = (epsilonZero : WithBot Ordinal) := by
  show ((Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 0 : Ordinal) : WithBot Ordinal) = _
  rw [← epsilonZero_eq_nfp]

/-- `Statement:` `↑ε₀` is the least landing of `phaseUpAndOver.up` strictly above the boundary
    model's floor (`UpAndOver.up_le_of_covBy` at `phase_floor_covBy_snap`). -/
theorem phase_epsilon0_isLeast_landing_above_floor :
    IsLeast {x : WithBot Ordinal | phaseUpAndOver.up.IsClosed x ∧ phaseEquivWithBot Phase.floor < x}
      (epsilonZero : WithBot Ordinal) := by
  refine ⟨⟨?_, WithBot.bot_lt_coe _⟩, ?_⟩
  · rw [← phaseUp_snap]; exact phaseUpAndOver.up.isClosed_closure _
  · rintro x ⟨hx, hbx⟩
    rw [← phaseUp_snap]
    exact UpAndOver.up_le_of_covBy phaseUpAndOver phase_floor_covBy_snap hx hbx

/-- `Statement:` the seeds `↑0` and `↑1` land on the same point, so the landing `up` reaches from the
    snap does not determine the seed. -/
theorem phaseUp_zero_eq_one :
    phaseUpAndOver.up ((0 : Ordinal) : WithBot Ordinal)
      = phaseUpAndOver.up ((1 : Ordinal) : WithBot Ordinal) := by
  show ((Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 0 : Ordinal) : WithBot Ordinal)
    = ((Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 1 : Ordinal) : WithBot Ordinal)
  rw [nfp_seed_independent_below_epsilon0 0 (zero_le _),
    nfp_seed_independent_below_epsilon0 1 (Order.one_le_iff_ne_zero.2 epsilon0_ne_zero)]

-- `Statement:` the closure is idempotent and not injective (`UpAndOver.up_not_injective`).
example : (∀ x, phaseUpAndOver.up (phaseUpAndOver.up x) = phaseUpAndOver.up x) ∧
    ¬ Function.Injective phaseUpAndOver.up :=
  ⟨fun x => phaseUpAndOver.up.idempotent x, UpAndOver.up_not_injective _⟩

/-! ### § V. Controls -/

-- `Statement:` seeded at the floor `⊥ : WithBot Ordinal`, the least fixed point of the lifted tower
-- operator is that floor itself, and `up` fixes it: the degenerate face.
example : IsLeastFixedPointFrom (· ≤ ·) phaseTower ⊥ ⊥ ∧ phaseUpAndOver.up ⊥ = ⊥ :=
  ⟨⟨le_rfl, rfl, fun _ _ _ => bot_le⟩, rfl⟩

/-- `Statement:` the snap `↑0` and `↑ε₀` differ (`epsilon0_ne_zero`), and the floor
    `⊥ : WithBot Ordinal` differs from both. -/
theorem phase_floor_snap_epsilon0_ne :
    phaseEquivWithBot snap ≠ ((epsilonZero : Ordinal) : WithBot Ordinal) ∧
    phaseEquivWithBot Phase.floor ≠ phaseEquivWithBot snap ∧
    phaseEquivWithBot Phase.floor ≠ ((epsilonZero : Ordinal) : WithBot Ordinal) :=
  ⟨fun h => epsilon0_ne_zero (WithBot.coe_injective
      (h : ((0 : Ordinal) : WithBot Ordinal) = (epsilonZero : WithBot Ordinal))).symm,
    WithBot.bot_ne_coe, WithBot.bot_ne_coe⟩

-- `Statement:` generic: every point of `WithBot Ordinal` is the least element of its own up-set,
-- `↑ε₀` among them; `↑ε₀` is not the least element of `WithBot Ordinal`. What is specific to `↑ε₀`
-- is `phase_epsilon0_isLeast_landing_above_floor`.
example : (∀ x : WithBot Ordinal, IsBot (⟨x, Set.self_mem_Ici⟩ : Set.Ici x)) ∧
    ¬ IsBot ((epsilonZero : Ordinal) : WithBot Ordinal) :=
  ⟨fun _ y => y.2, fun h => WithBot.not_coe_le_bot _ (h ⊥)⟩

-- `Statement:` on `WithBot ℝ` nothing covers the floor `⊥ : WithBot ℝ` (ℝ has no least element), and
-- `WithBot ℝ`, densely ordered, carries no `UpAndOver` at all (`UpAndOver.isEmpty_of_denselyOrdered`).
example : (∀ a : ℝ, ¬ (⊥ : WithBot ℝ) ⋖ a) ∧ IsEmpty (UpAndOver (WithBot ℝ)) :=
  ⟨fun a h => not_isMin a (WithBot.bot_covBy_coe.1 h), UpAndOver.isEmpty_of_denselyOrdered⟩

end ZeroParadox

/-! ## Axiom Purity Check

`phaseEquivWithBot`, `phaseEquivWithTop`, `phaseFloorToTop`, `withBotClosure` and
`withBotClosure_apply` measure `[propext, Quot.sound]`.
The rest inherit `Classical.choice` from Mathlib's `Ordinal` order and fixed-point theory, and are
STATEMENT-CARRIED as in `ZeroParadox/Ordinal/SnapNucleus.lean` (statement control, measured 2026-10-08),
except `phaseTower`, whose statement is choice-free: it stays UNCLASSIFIED. -/

section PurityCheck
open ZeroParadox

#print axioms phaseEquivWithBot
#print axioms phaseEquivWithTop
#print axioms phaseRel_up_iff_withBot
#print axioms phaseRel_up_iff_withTop
#print axioms phaseEquivWithBot_floor_lt_up
#print axioms phaseEquivWithBot_up_le_up
#print axioms phase_placement_extreme_iff
#print axioms phaseEquivWithTop_floor_covers_nothing
#print axioms phaseTop_epsilon0_isLeast_landing_above_snap
#print axioms phaseFloorToTop
#print axioms phaseFloorToTop_apply
#print axioms withBotClosure
#print axioms withBotClosure_apply
#print axioms phaseUpAndOver
#print axioms phase_floor_isBot
#print axioms phase_floor_covBy_snap
#print axioms phaseTower
#print axioms phase_epsilon0_isLeastFixedPointFrom_snap
#print axioms phaseUp_snap
#print axioms phase_epsilon0_isLeast_landing_above_floor
#print axioms phaseUp_zero_eq_one
#print axioms phase_floor_snap_epsilon0_ne

end PurityCheck
