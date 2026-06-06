import ZeroParadox.ZPJ_Wheel
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic

/-!
# The Wheel of Fractions `⊙_S A` (Carlström 2001:11, §4.2) — STUB

Constructs the wheel of fractions of a commutative ring `A` with respect to a multiplicative
submonoid `S`, with the goal of proving it is a `Wheel` (from `ZPJ_Wheel.lean`). This turns the
§VIII conjecture of `ZPJ_Wheel.lean` into a theorem, and is the direct construction behind the
Bergstra/Tucker question.

Construction (Carlström, source-verified): `⊙_S A = (A × A) / ≡_S`, where

  `(x,y) ≡_S (x',y')  ⟺  ∃ s s' ∈ S,  s·x = s'·x'  ∧  s·y = s'·y'`,

with `0 = [0,1]`, `1 = [1,1]`, `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`, `[x,y]·[x',y'] = [x·x', y·y']`,
and `/[x,y] = [y,x]`. Then `/0 = [1,0] = ∞`, `0·/0 = [0,0] = ⊥`, with `∞ ≠ ⊥` (the wheel, not the
meadow) — matching the ZP porthole.

**Status: STUB.** Every proof is `sorry`. Fill order: equivalence (refl/symm/trans) → operation
well-definedness → the 11 `Wheel` axioms → `inf_ne_bot`.
-/

namespace ZeroParadox.WheelFrac

open ZeroParadox.WheelTheory

set_option maxHeartbeats 400000

variable {A : Type*} [CommRing A] (S : Submonoid A)

/-- The wheel-of-fractions relation `≡_S` on `A × A`. -/
def rel (p q : A × A) : Prop :=
  ∃ s ∈ S, ∃ s' ∈ S, s * p.1 = s' * q.1 ∧ s * p.2 = s' * q.2

/-- `≡_S` is an equivalence relation (Carlström p.10; refl uses `1 ∈ S`, trans uses closure of `S`). -/
def srel : Setoid (A × A) where
  r := rel S
  iseqv := {
    refl := fun p => ⟨1, S.one_mem, 1, S.one_mem, rfl, rfl⟩
    symm := fun ⟨s, hs, s', hs', h1, h2⟩ => ⟨s', hs', s, hs, h1.symm, h2.symm⟩
    trans := fun ⟨s, hs, s', hs', a1, a2⟩ ⟨t, ht, t', ht', b1, b2⟩ =>
      ⟨t * s, S.mul_mem ht hs, t' * s', S.mul_mem ht' hs',
        by linear_combination t * a1 + s' * b1,
        by linear_combination t * a2 + s' * b2⟩
  }

/-- The wheel of fractions `⊙_S A = (A × A) / ≡_S`. -/
abbrev WheelFrac := Quotient (srel S)

/-- Class of a pair `[x, y]`. -/
def mk (p : A × A) : WheelFrac S := Quotient.mk (srel S) p

/-- Addition: `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`. -/
def waddF : WheelFrac S → WheelFrac S → WheelFrac S :=
  Quotient.lift₂ (fun p q => mk S (p.1 * q.2 + q.1 * p.2, p.2 * q.2)) (by
    rintro p q p' q' ⟨s, hs, s', hs', hp1, hp2⟩ ⟨t, ht, t', ht', hq1, hq2⟩
    refine Quotient.sound ⟨s * t, S.mul_mem hs ht, s' * t', S.mul_mem hs' ht', ?_, ?_⟩
    · calc (s * t) * (p.1 * q.2 + q.1 * p.2)
          = (s * p.1) * (t * q.2) + (t * q.1) * (s * p.2) := by ring
        _ = (s' * p'.1) * (t' * q'.2) + (t' * q'.1) * (s' * p'.2) := by rw [hp1, hp2, hq1, hq2]
        _ = (s' * t') * (p'.1 * q'.2 + q'.1 * p'.2) := by ring
    · calc (s * t) * (p.2 * q.2) = (s * p.2) * (t * q.2) := by ring
        _ = (s' * p'.2) * (t' * q'.2) := by rw [hp2, hq2]
        _ = (s' * t') * (p'.2 * q'.2) := by ring)

/-- Multiplication: `[x,y]·[x',y'] = [x·x', y·y']`. -/
def wmulF : WheelFrac S → WheelFrac S → WheelFrac S :=
  Quotient.lift₂ (fun p q => mk S (p.1 * q.1, p.2 * q.2)) (by
    rintro p q p' q' ⟨s, hs, s', hs', hp1, hp2⟩ ⟨t, ht, t', ht', hq1, hq2⟩
    refine Quotient.sound ⟨s * t, S.mul_mem hs ht, s' * t', S.mul_mem hs' ht', ?_, ?_⟩
    · calc (s * t) * (p.1 * q.1) = (s * p.1) * (t * q.1) := by ring
        _ = (s' * p'.1) * (t' * q'.1) := by rw [hp1, hq1]
        _ = (s' * t') * (p'.1 * q'.1) := by ring
    · calc (s * t) * (p.2 * q.2) = (s * p.2) * (t * q.2) := by ring
        _ = (s' * p'.2) * (t' * q'.2) := by rw [hp2, hq2]
        _ = (s' * t') * (p'.2 * q'.2) := by ring)

/-- Reciprocal / involution: `/[x,y] = [y,x]`. -/
def winvF : WheelFrac S → WheelFrac S :=
  Quotient.lift (fun p => mk S (p.2, p.1)) (by
    rintro p p' ⟨s, hs, s', hs', hp1, hp2⟩
    exact Quotient.sound ⟨s, hs, s', hs', hp2, hp1⟩)

/-- **Main goal (stub):** `⊙_S A` is a wheel (Carlström §4.2). All 11 axioms `sorry`. -/
instance instWheel : Wheel (WheelFrac S) where
  wadd := waddF S
  wmul := wmulF S
  winv := winvF S
  wzero := mk S (0, 1)
  wone := mk S (1, 1)
  wadd_assoc := by sorry
  wadd_comm := by sorry
  wadd_zero := by sorry
  wmul_assoc := by sorry
  wmul_comm := by sorry
  wmul_one := by sorry
  winv_winv := by sorry
  winv_wmul := by sorry
  weak_distrib := by sorry
  wheel_id := by sorry
  wzero_mul_wzero := by sorry

/-- Porthole: in `⊙_S A`, the infinity element `/0` and the bottom `0·/0` are distinct — the wheel
    (not meadow) behaviour, matching the ZP porthole `∞ ≠ ⊥`. (Stub.) -/
theorem inf_ne_bot : wheelInf (W := WheelFrac S) ≠ wheelBot := by sorry

end ZeroParadox.WheelFrac
