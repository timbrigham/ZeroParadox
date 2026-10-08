import ZeroParadox.Category.LawvereTwoAdic
import Mathlib.Dynamics.FixedPoints.Basic

set_option maxHeartbeats 400000

/-!
# Ignorance, fills, and the seam between partial and complete digit motions

## Engineer's Take

Total ignorance sounds like perfect zero point zero zero zero, with an infinite number of zeros, and I think we are onto something. This running in both directions explains why some charts appear reversed. I think we need to build them.

---
## Formal Overview (AI-assisted)
A partial stream is a `List Bool`, least-significant digit first; a tape is `ℕ → Bool`. § I fills
streams to tapes, § II carries fixed points across a semiconjugacy, § III prepends, § IV iterates
affine motions on streams from `[]`, § V negates, § VI complements. The empty stream `[]`, the
all-false tape, `botEnd : ℕ → Fin 2` and ℤ_[2]'s `0` lie in four types; no `=` between them is stated.
-/

namespace ZeroParadox

/-! ## § I. Ignorance and fills -/

/-- `Statement:` read a partial stream as a tape, filling every unknown digit with `d`. -/
def streamFill (d : Bool) (w : List Bool) : ℕ → Bool := fun n => w.getD n d

-- Statement: ignorance, the empty stream, fills with `false` to the least element of the pointwise
--   order on `ℕ → Bool`, and with `true` to its greatest element.
example : streamFill false [] = ⊥ ∧ streamFill true [] = ⊤ := ⟨rfl, rfl⟩

/-- `Statement:` a digit known in `w` is known, with the same value, in every extension of `w`. -/
theorem getElem?_append_of_known {w t : List Bool} {n : ℕ} {b : Bool} (h : w[n]? = some b) :
    (w ++ t)[n]? = some b := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h

/-- `Statement:` zero-fill is monotone from the prefix order on streams to the pointwise order. -/
theorem streamFill_false_mono {w v : List Bool} (h : w <+: v) :
    streamFill false w ≤ streamFill false v := by
  obtain ⟨t, rfl⟩ := h
  intro n
  simp only [streamFill, List.getD_eq_getElem?_getD]
  cases hw : w[n]? with
  | some b => rw [getElem?_append_of_known hw]
  | none => cases (w ++ t)[n]? with
    | none => exact le_rfl
    | some c => exact Bool.false_le c

/-- `Statement:` one-fill is antitone from the prefix order on streams to the pointwise order. -/
theorem streamFill_true_anti {w v : List Bool} (h : w <+: v) :
    streamFill true v ≤ streamFill true w := by
  obtain ⟨t, rfl⟩ := h
  intro n
  simp only [streamFill, List.getD_eq_getElem?_getD]
  cases hw : w[n]? with
  | some b => rw [getElem?_append_of_known hw]
  | none => cases (w ++ t)[n]? with
    | none => exact le_rfl
    | some c => exact Bool.le_true c

-- Statement: the two fills disagree on ignorance.
example : streamFill false [] ≠ streamFill true [] := fun h => by
  simpa [streamFill] using congrFun h 0

/-! ## § II. A fixed point crosses a semiconjugacy, in one direction -/

-- Statement: Mathlib, a semiconjugacy `g ∘ fa = fb ∘ g` carries every fixed point of `fa` to a
--   fixed point of `fb`.
#check @Function.IsFixedPt.map

/-- `Statement:` if `A` fixes some point and `B` fixes none, no map semiconjugates `A` to `B`. -/
theorem no_semiconj_of_fixed_of_fpf {P T : Type*} {A : P → P} {B : T → T} {x : P}
    (hx : Function.IsFixedPt A x) (hB : ∀ t, B t ≠ t) :
    ¬ ∃ c : P → T, Function.Semiconj c A B :=
  fun ⟨_, hc⟩ => hB _ (hx.map hc)

/-- `Statement:` no map `List Bool → ℤ_[2]` semiconjugates `partialAddOne` to add-one on ℤ_[2]. -/
theorem partialAddOne_no_semiconj :
    ¬ ∃ c : List Bool → ℤ_[2], Function.Semiconj c partialAddOne (· + 1) :=
  no_semiconj_of_fixed_of_fpf (x := []) rfl fun _ h => by simp at h

-- Statement: run backwards, the constant map to `[]` semiconjugates add-one on ℤ_[2] to
--   `partialAddOne`.
example : Function.Semiconj (fun _ : ℤ_[2] => ([] : List Bool)) (· + 1) partialAddOne :=
  fun _ => rfl

/-! ## § III. Prepends -/

/-- `Statement:` prepend the digit `e` to a tape. -/
def tapeCons (e : Bool) (x : ℕ → Bool) : ℕ → Bool := fun n =>
  match n with
  | 0 => e
  | k + 1 => x k

/-- `Statement:` every fill semiconjugates prepend-`e` on streams to prepend-`e` on tapes. -/
theorem streamFill_semiconj_cons (d e : Bool) :
    Function.Semiconj (streamFill d) (List.cons e) (tapeCons e) := fun _ => by
  funext n; cases n <;> rfl

-- Statement: at `d = e = false` the stream side is `partialDouble`.
example : Function.Semiconj (streamFill false) partialDouble (tapeCons false) :=
  streamFill_semiconj_cons false false

/-- `Statement:` the constant tape `d` is a fixed point of prepend-`d`. -/
theorem tapeCons_const (d : Bool) : Function.IsFixedPt (tapeCons d) (fun _ => d) := by
  funext n; cases n <;> rfl

/-- `Statement:` fill-with-`d` sends ignorance to a fixed point of prepend-`e` exactly when `d = e`. -/
theorem streamFill_nil_isFixedPt_iff (d e : Bool) :
    Function.IsFixedPt (tapeCons e) (streamFill d []) ↔ d = e := by
  constructor
  · intro h; simpa [streamFill, tapeCons] using (congrFun h 0).symm
  · rintro rfl; exact tapeCons_const d

/-! ## § IV. Affine motions on partial streams -/

/-- `Statement:` the natural number a stream denotes, least-significant digit first. -/
def streamVal : List Bool → ℕ
  | [] => 0
  | b :: w => b.toNat + 2 * streamVal w

/-- `Statement:` the lowest `n` binary digits of an integer, least-significant first. -/
def streamBits : ℕ → ℤ → List Bool
  | 0, _ => []
  | n + 1, m => (m % 2 == 1) :: streamBits n (m / 2)

/-- `Statement:` `streamBits n m` has length `n`. -/
theorem streamBits_length (n : ℕ) (m : ℤ) : (streamBits n m).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => simp [streamBits, ih]

/-- `Statement:` the lowest `n` digits of `m` depend only on `m` modulo `2 ^ n`. -/
theorem streamBits_add_pow_mul (n : ℕ) (m t : ℤ) :
    streamBits n (m + 2 ^ n * t) = streamBits n m := by
  induction n generalizing m t with
  | zero => rfl
  | succ n ih =>
    have e : m + 2 ^ (n + 1) * t = m + 2 * (2 ^ n * t) := by ring
    simp only [streamBits, e, Int.add_mul_emod_self_left,
      Int.add_mul_ediv_left m (2 ^ n * t) (by norm_num : (2 : ℤ) ≠ 0), ih]

/-- `Statement:` the lowest `|w|` digits of the number `w` denotes are `w`. -/
theorem streamBits_streamVal (w : List Bool) : streamBits w.length (streamVal w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have e : ((streamVal (b :: w) : ℕ) : ℤ) = (b.toNat : ℤ) + 2 * (streamVal w : ℤ) := by
      simp [streamVal]
    cases b <;>
      simp [streamBits, e, Int.add_mul_emod_self_left, ih,
        Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]

/-- `Statement:` the affine map `x ↦ a * x + b` on a stream `w`, kept to `|w| + k` digits. -/
def affineExt (k : ℕ) (a b : ℤ) (w : List Bool) : List Bool :=
  streamBits (w.length + k) (a * (streamVal w : ℤ) + b)

/-- `Statement:` `affineExt k a b` adds exactly `k` digits. -/
theorem affineExt_length (k : ℕ) (a b : ℤ) (w : List Bool) :
    (affineExt k a b w).length = w.length + k :=
  streamBits_length _ _

/-- `Statement:` when `2 ^ k ∣ a`, for every integer `m ≡ streamVal w (mod 2 ^ |w|)`, the lowest
    `|w| + k` digits of `a * m + b` are `affineExt k a b w`. -/
theorem affineExt_sound (k : ℕ) (a b : ℤ) (ha : (2 : ℤ) ^ k ∣ a) (w : List Bool) (t : ℤ) :
    streamBits (w.length + k) (a * ((streamVal w : ℤ) + 2 ^ w.length * t) + b) =
      affineExt k a b w := by
  obtain ⟨a', rfl⟩ := ha
  have e : 2 ^ k * a' * ((streamVal w : ℤ) + 2 ^ w.length * t) + b =
      (2 ^ k * a' * (streamVal w : ℤ) + b) + 2 ^ (w.length + k) * (a' * t) := by
    rw [pow_add]; ring
  rw [e, streamBits_add_pow_mul]; rfl

-- Statement: those integers are exactly parametrized by `t`: each has lowest `|w|` digits `w`.
example (w : List Bool) (t : ℤ) :
    streamBits w.length ((streamVal w : ℤ) + 2 ^ w.length * t) = w := by
  rw [streamBits_add_pow_mul, streamBits_streamVal]

/-- `Statement:` `partialAddOne` keeps the lowest `|w|` digits of `streamVal w + 1`. -/
theorem partialAddOne_eq_streamBits (w : List Bool) :
    partialAddOne w = streamBits w.length ((streamVal w : ℤ) + 1) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | true =>
      have e : ((streamVal (true :: w) : ℕ) : ℤ) + 1 = 0 + 2 * ((streamVal w : ℤ) + 1) := by
        simp [streamVal]; ring
      rw [e]
      simp [partialAddOne, streamBits, ih]
    | false =>
      have e : ((streamVal (false :: w) : ℕ) : ℤ) + 1 = 1 + 2 * (streamVal w : ℤ) := by
        simp [streamVal]; ring
      rw [e]
      simp [partialAddOne, streamBits, Int.add_mul_emod_self_left, streamBits_streamVal,
        Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]

-- Statement: so `partialAddOne` is `affineExt 0 1 1`.
example : partialAddOne = affineExt 0 1 1 := funext fun w => by
  rw [partialAddOne_eq_streamBits, affineExt, one_mul, Nat.add_zero]

/-- `Statement:` iterating `affineExt k a b` from `[]`, step `n` has exactly `n * k` digits. -/
theorem affineExt_iterate_length (k : ℕ) (a b : ℤ) (n : ℕ) :
    ((affineExt k a b)^[n] []).length = n * k := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', affineExt_length, ih, Nat.succ_mul]

/-- `Statement:` at `k = 0` every step of that iteration is `[]`. -/
theorem affineExt_zero_iterate_nil (a b : ℤ) (n : ℕ) : (affineExt 0 a b)^[n] [] = [] :=
  List.eq_nil_of_length_eq_zero (by rw [affineExt_iterate_length, Nat.mul_zero])

-- Statement: runs from `[]`, checked by `decide`: `2x` gives all `false`, `2x + 1` all `true`,
--   `2x + 2` gives `0111`, `4x + 1` gives `1010`.
example : (affineExt 1 2 0)^[3] [] = [false, false, false] := by decide
example : (affineExt 1 2 1)^[3] [] = [true, true, true] := by decide
example : (affineExt 1 2 2)^[4] [] = [false, true, true, true] := by decide
example : (affineExt 2 4 1)^[2] [] = [true, false, true, false] := by decide
-- Statement: `3x`, `x + 1` and `-x` (`k = 0`) stay at `[]`.
example : (affineExt 0 3 0)^[5] [] = [] ∧ (affineExt 0 1 1)^[5] [] = [] ∧
    (affineExt 0 (-1) 0)^[5] [] = [] :=
  ⟨affineExt_zero_iterate_nil _ _ _, affineExt_zero_iterate_nil _ _ _,
    affineExt_zero_iterate_nil _ _ _⟩
-- Reading: the digits-per-step split is proved for `affineExt` only, and no claim is made here
--   about other motions.

/-! ## § V. Negation on partial streams -/

/-- `Statement:` negation on partial streams: trailing `false` digits and the first `true` are
    kept, and every digit after that is flipped. -/
def partialNeg : List Bool → List Bool
  | [] => []
  | false :: w => false :: partialNeg w
  | true :: w => true :: w.map not

/-- `Statement:` every all-`false` stream is a fixed point of `partialNeg`, `[]` included. -/
theorem partialNeg_replicate_false (n : ℕ) :
    partialNeg (List.replicate n false) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, partialNeg, ih]

/-- `Statement:` iterating `partialNeg` from `[]` stays at `[]`. -/
theorem partialNeg_iterate_nil (n : ℕ) : partialNeg^[n] [] = [] :=
  Function.iterate_fixed rfl n

/-! ## § VI. Complement, the reversal -/

-- Statement: on tapes, pointwise `not` is the Boolean-algebra complement.
example : (fun x : ℕ → Bool => fun n => !(x n)) = compl := rfl

/-- `Statement:` complement semiconjugates prepend-`false` to prepend-`true`. -/
theorem compl_semiconj_tapeCons :
    Function.Semiconj (compl : (ℕ → Bool) → (ℕ → Bool)) (tapeCons false) (tapeCons true) :=
  fun _ => by funext n; cases n <;> rfl

-- Statement: Mathlib, complement on a Boolean algebra is antitone.
#check @compl_antitone
-- Statement: Mathlib, complement sends the least element ⊥ to the greatest element ⊤.
#check @compl_bot

-- Statement: so it carries the fixed point of prepend-`false` to the fixed point of prepend-`true`.
example : Function.IsFixedPt (tapeCons true) (fun _ => false)ᶜ :=
  (tapeCons_const false).map compl_semiconj_tapeCons

-- Statement: run backwards, complement semiconjugates prepend-`true` to prepend-`false`.
example : Function.Semiconj (compl : (ℕ → Bool) → (ℕ → Bool)) (tapeCons true) (tapeCons false) :=
  fun _ => by funext n; cases n <;> rfl

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms streamFill
#print axioms getElem?_append_of_known
#print axioms streamFill_false_mono
#print axioms streamFill_true_anti
#print axioms no_semiconj_of_fixed_of_fpf
#print axioms partialAddOne_no_semiconj
#print axioms tapeCons
#print axioms streamFill_semiconj_cons
#print axioms tapeCons_const
#print axioms streamFill_nil_isFixedPt_iff
#print axioms streamVal
#print axioms streamBits
#print axioms streamBits_length
#print axioms streamBits_add_pow_mul
#print axioms streamBits_streamVal
#print axioms affineExt
#print axioms affineExt_length
#print axioms affineExt_sound
#print axioms partialAddOne_eq_streamBits
#print axioms affineExt_iterate_length
#print axioms affineExt_zero_iterate_nil
#print axioms partialNeg
#print axioms partialNeg_replicate_false
#print axioms partialNeg_iterate_nil
#print axioms compl_semiconj_tapeCons
end PurityCheck
