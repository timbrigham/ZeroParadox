import ZeroParadox.Algebra.Wheel
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Tactic

/-!
# The Wheel of Fractions `⊙_S A` (Carlström 2001:11, pp. 4-5, 10)

## Engineer's Take

A ZP-J wheel sub-file. See the Engineer's Take in `ZeroParadox/Algebra/Wheel.lean`.

---

## Formal Overview
`⊙_S A = (A × A) / ≡_S`, giving `/0 = ∞` and `0·/0 = ⊥` with `∞ ≠ ⊥` — the wheel, not the meadow,
matching the ZP porthole. **Status: complete**, `sorry`-free, all 14 `Wheel` fields; `instWheel` and
`inf_ne_bot` are `Classical.choice`-free (`[propext, Quot.sound]`). Construction and argument: `ZeroParadox/Algebra/WheelFrac.md`.
-/

namespace ZeroParadox

open ZeroParadox

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

/-! ## § The involutive fork, and why it does NOT unify with the ordered μ/ν fork

`fixed_pole_forces_collapse` below witnesses the involutive-fork-with-a-fixed-pole row of the wall
taxonomy: **if the involution fixes the pole, the two poles coincide.** ⚠ That is a much SMALLER
statement than Carlström Prop. 4.4 off the same antecedent — do not present the collapse as a framework
finding. Why the two forks are different species, the prior art and the standard names: `ZeroParadox/Algebra/WheelFrac.md`. -/

/-- An **involutive fork**: an involution `dual` together with two poles it swaps. The wheel / Riemann
    fork (`z ↦ 1/z` swapping `0 ↔ ∞`) is the motivating instance.

    ⚠ **Name collision — "fork" now carries three unrelated senses.** Mathlib's
    `CategoryTheory.Limits.Fork` is an equalizer diagram; the framework's own μ/ν *fixed-point* fork
    (`ZeroParadox/Settheory/FixedPointFork.lean`) is a third. Nothing here is an instance of either.
    The full name `InvolutiveFork` is load-bearing — do not shorten it to `Fork` at any use site, and
    read "the categorical machinery" in the § above as *categorical* in the loose sense, not as a
    reference to `Limits.Fork`. -/
structure InvolutiveFork (α : Type*) where
  dual : α → α
  dual_invol : Function.Involutive dual
  pole₀ : α
  pole₁ : α
  swap : dual pole₀ = pole₁

namespace InvolutiveFork

variable {α : Type*} (F : InvolutiveFork α)

/-- The fork is **collapsed** when its two poles coincide (the diagonal point). -/
def Collapsed : Prop := F.pole₀ = F.pole₁

/-- **Collapse criterion.** The poles coincide iff `pole₀` is a fixed point of the involution.
    Parallel to the ordered fork's `fork_collapse_iff` — but honestly shallower: this proof is
    `eq_comm` after the swap, where the ordered collapse is Knaster–Tarski-deep. -/
theorem collapsed_iff_fixed : F.Collapsed ↔ F.dual F.pole₀ = F.pole₀ := by
  unfold Collapsed
  rw [F.swap]
  exact eq_comm

end InvolutiveFork

/-- **The wheel is an involutive fork.** `Statement:` **INVERSION** — the involution `winv`
    (`z ↦ 1/z`) *exchanges* the poles `0` and `∞ = /0` (`wheelInf`), and is an involution. Both halves
    are in the definition below: `swap := rfl` gives `winv wzero = wheelInf`, and `dual_invol` is
    `Wheel.winv_winv` (W7). This is the 0↔∞ exchange, not a coincidence of two readings at one
    object — contrast `epsilon0_min_eq_max`. Reuses the ZP-custom `Wheel` class plus native
    `Function.Involutive`. -/
def wheelFork (W : Type*) [Wheel W] : InvolutiveFork W where
  dual := Wheel.winv
  dual_invol := Wheel.winv_winv
  pole₀ := Wheel.wzero
  pole₁ := wheelInf
  swap := rfl

/-- In the wheel of fractions the fork poles `0` and `∞` are distinct, given `0 ∉ S` — the same
    hypothesis as `inf_ne_bot`, but for the `{0, ∞}` involution 2-cycle (`inf_ne_bot` is the
    *different* `{∞, ⊥}` pair). Choice-free, mirroring `inf_ne_bot`'s proof. -/
theorem wheelFrac_fork_open (h0 : (0 : A) ∉ S) :
    (Wheel.wzero : WheelFrac S) ≠ (wheelInf : WheelFrac S) := by
  intro h
  obtain ⟨s, hs, s', hs', e1, _⟩ := Quotient.exact h
  have hs'0 : s' = 0 := by simpa using e1.symm
  exact h0 (hs'0 ▸ hs')

/-- Restated through the abstraction: the wheel-of-fractions `InvolutiveFork` is NOT collapsed. So
    `InvolutiveFork` is a non-vacuous abstraction with a concrete, provably-open, choice-free
    instance — it is not a gauge that everything satisfies. -/
theorem wheelFork_not_collapsed (h0 : (0 : A) ∉ S) :
    ¬ (wheelFork (WheelFrac S)).Collapsed :=
  wheelFrac_fork_open S h0

/-- **The obstruction, Lean-witnessed.** An involutive fork whose pole is a FIXED point of the
    involution — the ordered-fork condition — is necessarily COLLAPSED. Hence the involutive and
    ordered forks coincide only at the diagonal point: they are different species. This is the
    no-go witness for that condition-set: hypothesis *the pole is fixed by the involution*,
    conclusion *the poles coincide*. ⚠ It proves **no** universal negative about typeclasses —
    "no non-vacuous unifier exists" quantifies over all possible typeclasses and is not a Lean
    statement at all. -/
theorem fixed_pole_forces_collapse {α : Type*} (F : InvolutiveFork α)
    (h : F.dual F.pole₀ = F.pole₀) : F.Collapsed :=
  F.collapsed_iff_fixed.mpr h

/-! ## Purity check -/

section PurityCheck
#print axioms instWheel
#print axioms inf_ne_bot
#print axioms InvolutiveFork.collapsed_iff_fixed
#print axioms wheelFrac_fork_open
#print axioms wheelFork_not_collapsed
#print axioms fixed_pole_forces_collapse
end PurityCheck

end ZeroParadox
