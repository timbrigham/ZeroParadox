-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): cut points of an order approached from one side and not reached there (joints and dual joints), with ⊤ and 0 of ℝ≥0∞, ⊤ of ℕ∞, NInf's ∞, the valuation of ℤ_[2]'s 0, and ε₀ as instances. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Die
import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Valuation.Scale
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Joints and dual joints: cut points approached from one side and not reached there

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
Cut points, joints and dual joints of an order (§ I), exchanged by the order dual (§ II); exclusions
(§ III); the ends of `ℝ≥0∞` and `ℕ∞` (§ IV); order-reversing maps and the 2-adic pole (§ V);
`PinnedLimit`, NInf's ∞ and ε₀ (§ VI). A shared shape only: no equation between these points.
-/

namespace ZeroParadox

/-! ### § I. Cut points, joints, dual joints
`Reading:` "joint" here names the order-theoretic shape only; whether it is the joint of Tim's
2026-10-22 read (`ZeroParadox/DieCannotBe.lean` § I) is not claimed. At the canonical cut of a linear
order, `IsJoint` is Mathlib's `Order.IsSuccLimit` and `IsDualJoint` is `Order.IsPredLimit` (the two
`example`s after the definitions); the general form is over an arbitrary pair `(A, B)`. -/

section Defs

variable {α : Type*} [Preorder α]

/-- `Statement:` `A` lies below `B`, and `x` is the least upper bound of `A` and the greatest lower
    bound of `B`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: a conjunction of Mathlib's `IsLUB` and `IsGLB` at one point
-- for a pair of sets; Mathlib's `DedekindCut` is the completion's cut, not a point of the carrier.
def IsCutPoint (A B : Set α) (x : α) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, a ≤ b) ∧ IsLUB A x ∧ IsGLB B x

/-- `Statement:` a cut point of `(A, B)` lying in `B`, with `A` nonempty and without a greatest
    element. -/
-- [ZP-CUSTOM] extends: IsCutPoint (ZeroParadox/Order/DieJoints.lean) | reason: the one-sided form
-- over an arbitrary pair, approached from below and not reached there; at the canonical cut
-- `(Set.Iio x, Set.Ici x)` of a linear order it is Mathlib's `Order.IsSuccLimit x`.
def IsJoint (A B : Set α) (x : α) : Prop :=
  IsCutPoint A B x ∧ A.Nonempty ∧ (¬ ∃ m, IsGreatest A m) ∧ x ∈ B

/-- `Statement:` a cut point of `(A, B)` lying in `A`, with `B` nonempty and without a least
    element. -/
-- [ZP-CUSTOM] extends: IsCutPoint (ZeroParadox/Order/DieJoints.lean) | reason: the mirror of
-- `IsJoint`, approached from above and not reached there; at the canonical cut
-- `(Set.Iic x, Set.Ioi x)` of a linear order it is Mathlib's `Order.IsPredLimit x`.
def IsDualJoint (A B : Set α) (x : α) : Prop :=
  IsCutPoint A B x ∧ B.Nonempty ∧ (¬ ∃ m, IsLeast B m) ∧ x ∈ A

end Defs

-- `Statement:` in a linear order, `a` is a joint of (`Set.Iio a`, `Set.Ici a`) iff `a` is a
-- successor limit (`Order.IsSuccLimit`); both directions.
example {α : Type*} [LinearOrder α] (a : α) :
    IsJoint (Set.Iio a) (Set.Ici a) a ↔ Order.IsSuccLimit a := by
  constructor
  · rintro ⟨⟨-, hl, -⟩, ⟨b, hb⟩, -, -⟩
    exact ⟨fun h => absurd (h (le_of_lt hb)) (not_le.2 hb), Order.isLUB_Iio_iff_isSuccPrelimit.1 hl⟩
  · intro h
    refine ⟨⟨fun x hx y hy => (le_of_lt hx).trans hy, h.isLUB_Iio, isGLB_Ici⟩, ?_, ?_, le_refl a⟩
    · obtain ⟨b, hb⟩ := not_isMin_iff.1 h.not_isMin; exact ⟨b, hb⟩
    · rintro ⟨m, hm, hmax⟩
      exact absurd (h.isLUB_Iio.2 hmax) (not_le.2 hm)

-- `Statement:` in a linear order, `a` is a dual joint of (`Set.Iic a`, `Set.Ioi a`) iff `a` is a
-- predecessor limit (`Order.IsPredLimit`); both directions.
example {α : Type*} [LinearOrder α] (a : α) :
    IsDualJoint (Set.Iic a) (Set.Ioi a) a ↔ Order.IsPredLimit a := by
  constructor
  · rintro ⟨⟨-, -, hg⟩, ⟨b, hb⟩, -, -⟩
    exact ⟨fun h => absurd (h (le_of_lt hb)) (not_le.2 hb), Order.isGLB_Ioi_iff_isPredPrelimit.1 hg⟩
  · intro h
    refine ⟨⟨fun x hx y hy => hx.trans (le_of_lt hy), isLUB_Iic, h.isGLB_Ioi⟩, ?_, ?_, le_refl a⟩
    · obtain ⟨b, hb⟩ := not_isMax_iff.1 h.not_isMax; exact ⟨b, hb⟩
    · rintro ⟨m, hm, hmin⟩
      exact absurd (h.isGLB_Ioi.2 hmin) (not_le.2 hm)

/-! ### § II. The order dual exchanges joints and dual joints
`Reading:` INVERSION. Q2: the arrow is the order; run backwards (`αᵒᵈ`) a joint reads as a dual
joint and back. Q1: the § IV pair, 0 and ⊤ of `ℝ≥0∞`, exchanged by `x ↦ x⁻¹` (§ V). -/

/-- `Statement:` `x` is a joint of `(B, A)` in `αᵒᵈ` iff it is a dual joint of `(A, B)` in `α`;
    both directions. -/
theorem isJoint_toDual_iff {α : Type*} [Preorder α] (A B : Set α) (x : α) :
    IsJoint (α := αᵒᵈ) (OrderDual.ofDual ⁻¹' B) (OrderDual.ofDual ⁻¹' A) (OrderDual.toDual x) ↔
      IsDualJoint A B x := by
  constructor
  · rintro ⟨⟨hAB, hl, hg⟩, hne, hng, hx⟩
    exact ⟨⟨fun a ha b hb => hAB b hb a ha, hg, hl⟩, hne, fun ⟨m, hm⟩ => hng ⟨m, hm⟩, hx⟩
  · rintro ⟨⟨hAB, hl, hg⟩, hne, hng, hx⟩
    exact ⟨⟨fun b hb a ha => hAB a ha b hb, hg, hl⟩, hne, fun ⟨m, hm⟩ => hng ⟨m, hm⟩, hx⟩
-- `Reading:` at the canonical cut (§ I) Mathlib's form is `Order.isSuccLimit_toDual_iff`.

/-- `Statement:` `x` is a dual joint of `(B, A)` in `αᵒᵈ` iff it is a joint of `(A, B)` in `α`;
    both directions. -/
theorem isDualJoint_toDual_iff {α : Type*} [Preorder α] (A B : Set α) (x : α) :
    IsDualJoint (α := αᵒᵈ) (OrderDual.ofDual ⁻¹' B) (OrderDual.ofDual ⁻¹' A) (OrderDual.toDual x) ↔
      IsJoint A B x := by
  constructor
  · rintro ⟨⟨hAB, hl, hg⟩, hne, hng, hx⟩
    exact ⟨⟨fun a ha b hb => hAB b hb a ha, hg, hl⟩, hne, fun ⟨m, hm⟩ => hng ⟨m, hm⟩, hx⟩
  · rintro ⟨⟨hAB, hl, hg⟩, hne, hng, hx⟩
    exact ⟨⟨fun b hb a ha => hAB a ha b hb, hg, hl⟩, hne, fun ⟨m, hm⟩ => hng ⟨m, hm⟩, hx⟩

/-! ### § III. Exclusions: a least point is never a joint; a well-order has no dual joint -/

/-- `Statement:` if `x` is least in a preorder, then `x` is a joint of no `(A, B)`. -/
theorem not_isJoint_of_isBot {α : Type*} [Preorder α] {x : α} (hx : IsBot x) (A B : Set α) :
    ¬ IsJoint A B x := by
  rintro ⟨⟨-, hl, -⟩, ⟨a, ha⟩, hng, -⟩
  exact hng ⟨a, ha, fun b hb => (hl.1 hb).trans (hx a)⟩
-- `Reading:` at the canonical cut (§ I) Mathlib's form is `IsMin.not_isSuccLimit`.

/-- `Statement:` if `x` is greatest in a preorder, then `x` is a dual joint of no `(A, B)`. -/
theorem not_isDualJoint_of_isTop {α : Type*} [Preorder α] {x : α} (hx : IsTop x) (A B : Set α) :
    ¬ IsDualJoint A B x := by
  rintro ⟨⟨-, -, hg⟩, ⟨b, hb⟩, hng, -⟩
  exact hng ⟨b, hb, fun c hc => (hx b).trans (hg.1 hc)⟩

/-- `Statement:` if a linear order is well-founded (`WellFoundedLT`), then nothing in it is a dual
    joint. -/
theorem not_isDualJoint_of_wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α]
    (A B : Set α) (x : α) : ¬ IsDualJoint A B x := by
  rintro ⟨-, hne, hng, -⟩
  obtain ⟨m, hm, hmin⟩ := (wellFounded_lt (α := α)).has_min B hne
  exact hng ⟨m, hm, fun b hb => not_lt.1 (hmin b hb)⟩

-- `Statement:` the instance at `Ordinal`: nothing in `Ordinal` is a dual joint.
example (A B : Set Ordinal.{0}) (x : Ordinal.{0}) : ¬ IsDualJoint A B x :=
  not_isDualJoint_of_wellFoundedLT A B x

-- `Statement:` CONTROL: linearity is a premise. `Finset Bool` is well-founded and not linear, and
-- `∅` is a dual joint of (`{∅}`, `{{true}, {false}}`), whose two points are incomparable.
example : WellFoundedLT (Finset Bool) ∧
    IsDualJoint ({∅} : Set (Finset Bool)) {{true}, {false}} ∅ := by
  refine ⟨inferInstance, ⟨?_, isLUB_singleton, ?_, ?_⟩, ⟨{true}, Or.inl rfl⟩, ?_, rfl⟩
  · rintro a rfl b -
    exact Finset.empty_subset b
  · rintro b -
    exact Finset.empty_subset b
  · intro y hy b hb
    have h1 := hy (Or.inl rfl) hb
    have h2 := hy (Or.inr rfl) hb
    simp only [Finset.mem_singleton] at h1 h2
    exact absurd (h1.symm.trans h2) (by decide)
  · rintro ⟨m, hm, hmin⟩
    have h1 : m ≤ {true} := hmin (Or.inl rfl)
    have h2 : m ≤ {false} := hmin (Or.inr rfl)
    rcases hm with rfl | rfl
    · exact absurd h2 (by decide)
    · exact absurd h1 (by decide)

/-! ### § IV. The ends of `ℝ≥0∞` and `ℕ∞` -/

/-- `Statement:` ⊤ of `ℝ≥0∞` is a joint of (the finite values, `{⊤}`). -/
theorem ennreal_top_isJoint : IsJoint {x : ENNReal | x ≠ ⊤} {⊤} (⊤ : ENNReal) := by
  refine ⟨⟨fun a _ b hb => hb ▸ le_top, ⟨fun _ _ => le_top, fun y hy => ?_⟩,
    ⟨fun b hb => hb ▸ le_rfl, fun y _ => le_top⟩⟩, ⟨0, ENNReal.zero_ne_top⟩, ?_, rfl⟩
  · by_contra h
    have hyt : y ≠ ⊤ := fun e => h (e ▸ le_rfl)
    have h1 : y + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hyt, ENNReal.one_ne_top⟩
    exact absurd (hy h1) (not_le.2 (ENNReal.lt_add_right hyt one_ne_zero))
  · rintro ⟨m, hm, hmax⟩
    have h1 : m + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hm, ENNReal.one_ne_top⟩
    exact absurd (hmax h1) (not_le.2 (ENNReal.lt_add_right hm one_ne_zero))

/-- `Statement:` 0 of `ℝ≥0∞` is a dual joint of (`{0}`, the positive values). -/
theorem ennreal_zero_isDualJoint : IsDualJoint {(0 : ENNReal)} {x : ENNReal | 0 < x} 0 := by
  refine ⟨⟨fun a ha b hb => ha ▸ hb.le, ⟨fun a ha => ha ▸ le_rfl, fun y hy => hy rfl⟩,
    ⟨fun b hb => zero_le b, fun y hy => ?_⟩⟩, ⟨1, show (0 : ENNReal) < 1 from zero_lt_one⟩, ?_, rfl⟩
  · by_contra h
    have hpos : 0 < y := not_le.1 h
    have hyt : y ≠ ⊤ := fun e => absurd (hy (show (0 : ENNReal) < 1 from zero_lt_one))
      (by rw [e]; exact not_le.2 ENNReal.one_lt_top)
    have := hy (show (0 : ENNReal) < y / 2 from ENNReal.half_pos hpos.ne')
    exact absurd this (not_le.2 (ENNReal.half_lt_self hpos.ne' hyt))
  · rintro ⟨m, hm, hmin⟩
    have hm0 : m ≠ 0 := (show (0 : ENNReal) < m from hm).ne'
    by_cases hmt : m = ⊤
    · exact absurd (hmin (show (0 : ENNReal) < 1 from zero_lt_one))
        (by rw [hmt]; exact not_le.2 ENNReal.one_lt_top)
    · exact absurd (hmin (show (0 : ENNReal) < m / 2 from ENNReal.half_pos hm0))
        (not_le.2 (ENNReal.half_lt_self hm0 hmt))

-- `Statement:` 0 of `ℝ≥0∞` is ⊥ of `ℝ≥0∞`, so it is a joint of no `(A, B)` (`not_isJoint_of_isBot`).
example (A B : Set ENNReal) : ¬ IsJoint A B 0 := not_isJoint_of_isBot (fun _ => zero_le _) A B

/-- `Statement:` on `ℝ≥0∞`, `x ↦ x⁻¹` reverses the order, sends ⊤ to 0 and 0 to ⊤, and `x⁻¹` is
    positive iff `x ≠ ⊤`. -/
theorem ennreal_inv_exchanges :
    (∀ a b : ENNReal, a⁻¹ ≤ b⁻¹ ↔ b ≤ a) ∧ (⊤ : ENNReal)⁻¹ = 0 ∧ (0 : ENNReal)⁻¹ = ⊤ ∧
      (∀ x : ENNReal, 0 < x⁻¹ ↔ x ≠ ⊤) :=
  ⟨fun _ _ => ENNReal.inv_le_inv, ENNReal.inv_top, ENNReal.inv_zero, fun _ => ENNReal.inv_pos⟩

/-- `Statement:` ⊤ of `ℕ∞` is a joint of (the finite values, `{⊤}`). -/
theorem enat_top_isJoint : IsJoint (Set.range (Nat.cast : ℕ → ℕ∞)) {⊤} (⊤ : ℕ∞) := by
  refine ⟨⟨fun a _ b hb => hb ▸ le_top, ⟨fun _ _ => le_top, fun y hy => ?_⟩,
    ⟨fun b hb => hb ▸ le_rfl, fun y _ => le_top⟩⟩, ⟨0, 0, rfl⟩, ?_, rfl⟩
  · induction y using ENat.recTopCoe with
    | top => exact le_rfl
    | coe k =>
      have := hy ⟨k + 1, rfl⟩
      exact absurd (by exact_mod_cast this : k + 1 ≤ k) (by omega)
  · rintro ⟨_, ⟨n, rfl⟩, hm⟩
    have := hm ⟨n + 1, rfl⟩
    exact absurd (by exact_mod_cast this : n + 1 ≤ n) (by omega)

/-! ### § V. Order-reversing maps, and the 2-adic pole -/

/-- `Statement:` if `f` is onto and `f a ≤ f b ↔ b ≤ a`, then `f` sends a dual joint `x` of `(A, B)`
    to a joint `f x` of `(f '' B, f '' A)`. -/
theorem isJoint_image_of_isDualJoint {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : ∀ a b, f a ≤ f b ↔ b ≤ a) (hs : Function.Surjective f) {A B : Set α} {x : α}
    (h : IsDualJoint A B x) : IsJoint (f '' B) (f '' A) (f x) := by
  obtain ⟨⟨hAB, hl, hg⟩, hne, hng, hx⟩ := h
  refine ⟨⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hne.image f, ?_, Set.mem_image_of_mem f hx⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    exact (hf b a).2 (hAB a ha b hb)
  · rintro _ ⟨b, hb, rfl⟩
    exact (hf b x).2 (hg.1 hb)
  · intro y hy
    obtain ⟨z, rfl⟩ := hs y
    exact (hf x z).2 (hg.2 fun b hb => (hf b z).1 (hy ⟨b, hb, rfl⟩))
  · rintro _ ⟨a, ha, rfl⟩
    exact (hf x a).2 (hl.1 ha)
  · intro y hy
    obtain ⟨z, rfl⟩ := hs y
    exact (hf z x).2 (hl.2 fun a ha => (hf z a).1 (hy ⟨a, ha, rfl⟩))
  · rintro ⟨_, ⟨m, hm, rfl⟩, hmax⟩
    exact hng ⟨m, hm, fun b hb => (hf b m).1 (hmax ⟨b, hb, rfl⟩)⟩

/-- `Statement:` under the same hypotheses on `f`, a joint `x` of `(A, B)` goes to a dual joint
    `f x` of `(f '' B, f '' A)`. -/
theorem isDualJoint_image_of_isJoint {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (hf : ∀ a b, f a ≤ f b ↔ b ≤ a) (hs : Function.Surjective f) {A B : Set α} {x : α}
    (h : IsJoint A B x) : IsDualJoint (f '' B) (f '' A) (f x) := by
  obtain ⟨⟨hAB, hl, hg⟩, hne, hng, hx⟩ := h
  refine ⟨⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hne.image f, ?_, Set.mem_image_of_mem f hx⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    exact (hf b a).2 (hAB a ha b hb)
  · rintro _ ⟨b, hb, rfl⟩
    exact (hf b x).2 (hg.1 hb)
  · intro y hy
    obtain ⟨z, rfl⟩ := hs y
    exact (hf x z).2 (hg.2 fun b hb => (hf b z).1 (hy ⟨b, hb, rfl⟩))
  · rintro _ ⟨a, ha, rfl⟩
    exact (hf x a).2 (hl.1 ha)
  · intro y hy
    obtain ⟨z, rfl⟩ := hs y
    exact (hf z x).2 (hl.2 fun a ha => (hf z a).1 (hy ⟨a, ha, rfl⟩))
  · rintro ⟨_, ⟨m, hm, rfl⟩, hmin⟩
    exact hng ⟨m, hm, fun a ha => (hf m a).1 (hmin ⟨a, ha, rfl⟩)⟩

-- `Statement:` INVERSION on `ℝ≥0∞`: `x ↦ x⁻¹` sends 0's dual joint (`ennreal_zero_isDualJoint`) to a
-- joint at `0⁻¹`, which is ⊤ of `ℝ≥0∞` (`ennreal_inv_exchanges`).
example : IsJoint ((·⁻¹) '' {x : ENNReal | 0 < x}) ((·⁻¹) '' {(0 : ENNReal)}) (0 : ENNReal)⁻¹ :=
  isJoint_image_of_isDualJoint _ (fun _ _ => ENNReal.inv_le_inv) (fun y => ⟨y⁻¹, inv_inv y⟩)
    ennreal_zero_isDualJoint

/-- `Statement:` on ℤ_[2], `q2Val` reverses the norm order, ℤ_[2]'s 0 has least norm, and its
    `q2Val` is ⊤ of `ℕ∞`, a joint of (the finite values, `{⊤}`). -/
theorem q2Val_zero_isJoint :
    (∀ x y : ℤ_[2], q2Val x ≤ q2Val y ↔ ‖y‖ ≤ ‖x‖) ∧ (∀ x : ℤ_[2], ‖(0 : ℤ_[2])‖ ≤ ‖x‖) ∧
      q2Val 0 = ⊤ ∧ IsJoint (Set.range (Nat.cast : ℕ → ℕ∞)) {⊤} (q2Val 0) := by
  refine ⟨q2Val_le_iff_norm_le, fun x => by rw [norm_zero]; exact norm_nonneg x, q2Val_bot, ?_⟩
  rw [q2Val_bot]
  exact enat_top_isJoint

/-! ### § VI. `PinnedLimit` gives a joint; NInf's ∞ and ε₀ -/

/-- `Statement:` in a partial order, if `c` occupies `PinnedLimit g s c`, then `c` is a joint of
    (the stages, the fixed points of `g`); one way. -/
theorem PinnedLimit.isJoint {α : Type*} [PartialOrder α] {g : α → α} {s : ℕ → α} {c : α}
    (h : PinnedLimit g s c) : IsJoint (Set.range s) {x | g x = x} c := by
  obtain ⟨hlub, hnot, hleast, -⟩ := h
  refine ⟨⟨fun a ha b hb => (hlub.1 ha).trans (hleast.2 hb), hlub, hleast.isGLB⟩, ⟨s 0, 0, rfl⟩,
    ?_, hleast.1⟩
  rintro ⟨m, hm, hmax⟩
  exact hnot (by rw [hlub.unique ⟨hmax, fun _ hy => hy hm⟩]; exact hm)

-- `Statement:` CONTROL: antisymmetry is a premise. Die.lean § XXIV's `Bool` preorder occupant of
-- `PinnedLimit id` (all points related) is no joint: its stages `{false}` have a greatest element.
example : ∃ inst : Preorder Bool, @PinnedLimit Bool inst id (fun _ => false) true ∧
    ¬ @IsJoint Bool inst (Set.range fun _ : ℕ => false) {x | id x = x} true :=
  ⟨{ le := fun _ _ => True, le_refl := fun _ => trivial, le_trans := fun _ _ _ _ _ => trivial,
      lt := fun _ _ => False, lt_iff_le_not_ge := fun _ _ => by simp },
    ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩, fun ⟨_, h⟩ => by simp at h, ⟨rfl, fun _ _ => trivial⟩,
      fun _ _ _ => trivial⟩,
    fun ⟨_, _, hng, _⟩ => hng ⟨false, ⟨0, rfl⟩, fun _ _ => trivial⟩⟩

/-- `Statement:` NInf's `∞` is a joint of (the finite stages, `{∞}`). -/
theorem NInf.infty_isJoint : IsJoint (Set.range NInf.ofNat) {NInf.infty} NInf.infty := by
  have h := NInf.pinnedLimitUnique_succ.2.1.isJoint
  have e : {x : NInf | NInf.succ x = x} = {NInf.infty} := Set.ext fun x => NInf.succ_fixed_iff x
  rwa [e] at h

-- `Statement:` ⊤ of `WithTop ℕ` is a joint of (the finite stages, the fixed points of `· + 1`), by
-- `pinnedLimitUnique_withTop`.
example : IsJoint (Set.range fun n : ℕ => (n : WithTop ℕ)) {x : WithTop ℕ | x + 1 = x} ⊤ :=
  pinnedLimitUnique_withTop.2.1.isJoint

/-- `Statement:` ε₀ is a joint of (the ω-tower from ⊥ of `Ordinal`, the fixed points of `ω^·`). -/
theorem epsilon0_isJoint :
    IsJoint (Set.range fundamentalSeq.{0}) {o : Ordinal.{0} | Ordinal.omega0 ^ o = o}
      epsilonZero :=
  epsilon0_pinnedLimit.{0}.2.isJoint

-- `Statement:` something lies strictly above ε₀ in `Ordinal`, so it is no greatest point; and
-- ε₀ ≠ ⊥ of `Ordinal` (`epsilon0_ne_bot`): neither end.
example : epsilonZero.{0} < Order.succ epsilonZero ∧ epsilonZero.{0} ≠ ⊥ :=
  ⟨Order.lt_succ _, epsilon0_ne_bot⟩

-- `Statement:` CONTROL: the shape alone is not special to ε₀: ω is a joint of (the naturals, `Set.Ici ω`).
example : IsJoint (Set.range (Nat.cast : ℕ → Ordinal.{0})) (Set.Ici Ordinal.omega0) Ordinal.omega0 := by
  refine ⟨⟨?_, ⟨?_, ?_⟩, ⟨fun _ hb => hb, fun y hy => hy (Set.mem_Ici.2 le_rfl)⟩⟩, ⟨0, 0, rfl⟩, ?_,
    Set.mem_Ici.2 le_rfl⟩
  · rintro _ ⟨n, rfl⟩ b hb; exact (Ordinal.natCast_lt_omega0 n).le.trans hb
  · rintro _ ⟨n, rfl⟩; exact (Ordinal.natCast_lt_omega0 n).le
  · intro y hy; exact Ordinal.omega0_le.2 fun n => hy ⟨n, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, hm⟩
    have := hm ⟨n + 1, rfl⟩
    simp at this

-- `Statement:` CONTROL (no cut point at ε₀): against the fixed points at or above ε₁, the ω-tower has no cut point
-- at ε₀.
example : ¬ IsCutPoint (Set.range fundamentalSeq.{0})
    {o : Ordinal.{0} | Ordinal.omega0 ^ o = o ∧ Ordinal.epsilon 1 ≤ o} (Ordinal.epsilon 0) := by
  rintro ⟨_, _, hglb⟩
  have h1 : Ordinal.epsilon 1 ∈ lowerBounds
      {o : Ordinal.{0} | Ordinal.omega0 ^ o = o ∧ Ordinal.epsilon 1 ≤ o} := fun _ h => h.2
  exact absurd (hglb.2 h1) (not_le.2 (Ordinal.veblen_right_strictMono 1 zero_lt_one))

-- `Reading:` CARRIER. ε₀ ≠ ⊥ of `Ordinal` (`epsilon0_ne_bot`); ε₀, ⊤ of `ℝ≥0∞`, ⊤ of `ℕ∞` and
-- NInf's `∞` share the joint shape on four carriers, and no equation across them is well-typed.

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms IsCutPoint
#print axioms IsJoint
#print axioms IsDualJoint
#print axioms isJoint_toDual_iff
#print axioms isDualJoint_toDual_iff
#print axioms not_isJoint_of_isBot
#print axioms not_isDualJoint_of_isTop
#print axioms not_isDualJoint_of_wellFoundedLT
#print axioms ennreal_top_isJoint
#print axioms ennreal_zero_isDualJoint
#print axioms ennreal_inv_exchanges
#print axioms enat_top_isJoint
#print axioms isJoint_image_of_isDualJoint
#print axioms isDualJoint_image_of_isJoint
#print axioms q2Val_zero_isJoint
#print axioms PinnedLimit.isJoint
#print axioms NInf.infty_isJoint
#print axioms epsilon0_isJoint
end PurityCheck
