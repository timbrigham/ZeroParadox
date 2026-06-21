import ZeroParadox.ZPJ_Wheel
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic

/-!
# The Wheel of Fractions `⊙_S A` (Carlström 2001:11, pp. 4-5, 10)

Constructs the wheel of fractions of a commutative ring `A` with respect to a multiplicative
submonoid `S`, with the goal of proving it is a `Wheel` (from `ZPJ_Wheel.lean`). This turns the
§VIII conjecture of `ZPJ_Wheel.lean` into a theorem.

Construction (Carlström, source-verified): `⊙_S A = (A × A) / ≡_S`, where

  `(x,y) ≡_S (x',y')  ⟺  ∃ s s' ∈ S,  s·x = s'·x'  ∧  s·y = s'·y'`,

with `0 = [0,1]`, `1 = [1,1]`, `[x,y] + [x',y'] = [x·y' + x'·y, y·y']`, `[x,y]·[x',y'] = [x·x', y·y']`,
and `/[x,y] = [y,x]`. Then `/0 = [1,0] = ∞`, `0·/0 = [0,0] = ⊥`, with `∞ ≠ ⊥` (the wheel, not the
meadow) — matching the ZP porthole.

**Status: complete.** Fully `sorry`-free: `≡_S` is an equivalence, the five operations are
well-defined on the quotient, all 14 fields of the ZP `Wheel` typeclass hold (a faithful encoding
of Carlström's 8-axiom Def 1.1, with his two commutative-monoid axioms unbundled), and `inf_ne_bot`
holds given `0 ∉ S`.
Both `instWheel` and `inf_ne_bot` are `Classical.choice`-free (`[propext, Quot.sound]`).
-/

namespace ZeroParadox.ZPJ_WheelFrac

open ZeroParadox.ZPJ_Wheel

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

/-- **Main result:** `⊙_S A` is a wheel (Carlström 2001:11, Def 1.1, pp. 4-5). All 14 fields of the
    ZP `Wheel` typeclass proved (Carlström's eight axioms, two commutative-monoid axioms unbundled). -/
instance instWheel : Wheel (WheelFrac S) where
  wadd := waddF S
  wmul := wmulF S
  winv := winvF S
  wzero := mk S (0, 1)
  wone := mk S (1, 1)
  wadd_assoc := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_comm := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_zero := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wmul_assoc := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wmul_comm := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wmul_one := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  winv_winv := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => rfl  -- `/(/[x,y]) = [x,y]` holds definitionally (swap twice)
  winv_wmul := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => rfl  -- `/(x·y) = /x · /y` holds definitionally (both reduce to `[bd, ac]`)
  weak_distrib := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wheel_id := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wzero_mul_wzero := by
    apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_zeromul_mul := by
    intro x y z
    induction x, y, z using Quotient.inductionOn₃ with
    | _ a b c => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  winv_add_zeromul := by
    intro x y
    induction x, y using Quotient.inductionOn₂ with
    | _ a b => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring
  wadd_zeroinv_absorb := by
    intro x
    induction x using Quotient.inductionOn with
    | _ a => apply Quotient.sound; refine ⟨1, S.one_mem, 1, S.one_mem, ?_, ?_⟩ <;> ring

/-- Porthole: in `⊙_S A`, the infinity element `/0` and the bottom `0·/0` are distinct — the wheel
    (not meadow) behaviour, matching the ZP porthole `∞ ≠ ⊥`. -/
theorem inf_ne_bot (h0 : (0 : A) ∉ S) : wheelInf (W := WheelFrac S) ≠ wheelBot := by
  intro h
  obtain ⟨s, hs, s', hs', e1, _⟩ := Quotient.exact h
  have hs0 : s = 0 := by simpa using e1
  exact h0 (hs0 ▸ hs)

/-! ## Purity check -/

section PurityCheck
#print axioms instWheel
#print axioms inf_ne_bot
end PurityCheck

end ZeroParadox.ZPJ_WheelFrac
