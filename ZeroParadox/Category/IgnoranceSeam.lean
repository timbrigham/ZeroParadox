import ZeroParadox.Category.LawvereTwoAdic
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Data.Int.Bitwise

set_option maxHeartbeats 400000

/-!
# Fills and semiconjugacy (the seam) between partial and complete digit motions
## Engineer's Take

Total ignorance sounds like perfect zero point zero zero zero, with an infinite number of zeros, and I think we are onto something. This running in both directions explains why some charts appear reversed. I think we need to build them.

## Formal Overview (AI-assisted)
Streams are `List Bool`, least-significant digit first; tapes are `ℕ → Bool`. `[]`, the all-false tape,
`botEnd : ℕ → Fin 2` and ℤ_[2]'s `0` lie in four types, with no `=` between them. The Take's zero tape is
the all-false tape, which reads as 0 in two charts: the binary fraction 0.000… (zeros to the right of the
point) and the 2-adic digits of ℤ_[2]'s 0 (zeros to the left; `ZeroParadox/Valuation/PadicTree.lean`);
neither is the reading (neither chart's digit reading is formalized in this file). Filling with `true`
sends `[]` to the greatest tape (§ I). Complement carries prepend-false to prepend-true by a semiconjugacy
(§ VI); its order reversal is Mathlib's `compl_antitone`. § VII: local ignorance and local knowledge. -/

namespace ZeroParadox

/-! ## § I. The empty stream (ignorance) and fills -/

/-- `Statement:` read a partial stream as a tape, filling every unknown digit with `d`. -/
def streamFill (d : Bool) (w : List Bool) : ℕ → Bool := fun n => w.getD n d

-- Statement: the empty stream (ignorance) fills with `false` to the least element of the pointwise
--   order on `ℕ → Bool`, and with `true` to its greatest element.
example : streamFill false [] = ⊥ ∧ streamFill true [] = ⊤ := ⟨rfl, rfl⟩

/-- `Statement:` a digit known in `w` is known, with the same value, in every extension of `w`;
    a corollary of core `List.prefix_iff_getElem?`. -/
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

-- Statement: the two fills disagree on the empty stream.
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
--   `partialAddOne`; its content is `partialAddOne [] = []`.
example : Function.Semiconj (fun _ : ℤ_[2] => ([] : List Bool)) (· + 1) partialAddOne :=
  fun _ => rfl
-- Statement: the constant map to a fixed point of `B` semiconjugates every `A` to `B`.
example {P T : Type*} (A : P → P) (B : T → T) {x : T} (hx : Function.IsFixedPt B x) :
    Function.Semiconj (fun _ : P => x) A B := fun _ => hx.symm

/-! ## § III. Prepends -/

/-- `Statement:` prepend the digit `e` to a tape. -/
def tapeCons (e : Bool) (x : ℕ → Bool) : ℕ → Bool := fun n =>
  match n with
  | 0 => e
  | k + 1 => x k

-- Statement: `tapeCons` is Mathlib's `Stream'.cons`.
example (e : Bool) (x : ℕ → Bool) : tapeCons e x = Stream'.cons e x := rfl

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

/-- `Statement:` the constant tape `d` is the only fixed point of prepend-`d`. -/
theorem tapeCons_isFixedPt_iff (d : Bool) (x : ℕ → Bool) :
    Function.IsFixedPt (tapeCons d) x ↔ x = fun _ => d := by
  refine ⟨fun h => funext fun n => ?_, fun h => by subst h; exact tapeCons_const d⟩
  induction n with
  | zero => exact (congrFun h 0).symm
  | succ n ih => exact (congrFun h (n + 1)).symm.trans ih

/-- `Statement:` fill-with-`d` sends the empty stream to a fixed point of prepend-`e` exactly when `d = e`. -/
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

-- Reading: at `k = 0` this is an instance (p = 2, on integers) of the digit condition that
--   characterizes 1-Lipschitz maps of ℤ_p (Anashin, arXiv:1112.5089, Prop. 2.1, p. 4); ℤ_[2] is not
--   used here.

/-- `Statement:` every integer `m` is `streamVal (streamBits n m)` plus a multiple of `2 ^ n`. -/
theorem eq_streamVal_streamBits_add (n : ℕ) (m : ℤ) :
    ∃ t : ℤ, m = (streamVal (streamBits n m) : ℤ) + 2 ^ n * t := by
  induction n generalizing m with
  | zero => exact ⟨m, by simp [streamBits, streamVal]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (m / 2)
    refine ⟨t, ?_⟩
    have hm := Int.emod_add_mul_ediv m 2
    have hb : (((m % 2 == 1).toNat : ℕ) : ℤ) = m % 2 := by
      rcases Int.emod_two_eq_zero_or_one m with h | h <;> simp [h]
    simp only [streamBits, streamVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hb]
    linear_combination hm.symm + 2 * ht

/-- `Statement:` the integers whose lowest `|w|` digits are `w` are exactly the integers
    `streamVal w + 2 ^ |w| * t`, `t : ℤ`. -/
theorem streamBits_length_eq_iff (w : List Bool) (m : ℤ) :
    streamBits w.length m = w ↔ ∃ t : ℤ, m = streamVal w + 2 ^ w.length * t := by
  constructor
  · intro h
    have := eq_streamVal_streamBits_add w.length m
    rwa [h] at this
  · rintro ⟨t, rfl⟩; rw [streamBits_add_pow_mul, streamBits_streamVal]

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

/-- `Statement:` iterating `2x` from `[]`, step `n` is `n` copies of `false`. -/
theorem affineExt_double_iterate (n : ℕ) :
    (affineExt 1 2 0)^[n] [] = List.replicate n false := by
  have hv : ∀ n, streamVal (List.replicate n false) = 0 := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, streamVal, ih]
  have hz : ∀ n, streamBits n 0 = List.replicate n false := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [streamBits, ih, List.replicate_succ]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, affineExt, hv, List.length_replicate]
    simpa using hz (n + 1)

/-- `Statement:` iterating `2x + 1` from `[]`, step `n` is `n` copies of `true`. -/
theorem affineExt_doubleAddOne_iterate (n : ℕ) :
    (affineExt 1 2 1)^[n] [] = List.replicate n true := by
  have hv : ∀ n, (streamVal (List.replicate n true) : ℤ) = 2 ^ n - 1 := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, streamVal, ih]; ring
  have hm : ∀ n, streamBits n (-1) = List.replicate n true := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp [streamBits, ih, List.replicate_succ]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, affineExt, hv, List.length_replicate]
    have e : (2 : ℤ) * (2 ^ n - 1) + 1 = -1 + 2 ^ (n + 1) * 1 := by ring
    rw [e, streamBits_add_pow_mul, hm]

-- Statement: checked by `decide`, step 4 of `2x + 2` is `0111` and step 2 of `4x + 1` is `1010`.
example : (affineExt 1 2 2)^[4] [] = [false, true, true, true] := by decide
example : (affineExt 2 4 1)^[2] [] = [true, false, true, false] := by decide
-- Statement: `3x`, `x + 1` and `-x` (`k = 0`) stay at `[]`.
example : (affineExt 0 3 0)^[5] [] = [] ∧ (affineExt 0 1 1)^[5] [] = [] ∧
    (affineExt 0 (-1) 0)^[5] [] = [] :=
  ⟨affineExt_zero_iterate_nil _ _ _, affineExt_zero_iterate_nil _ _ _,
    affineExt_zero_iterate_nil _ _ _⟩

/-! ## § V. Negation on partial streams -/

/-- `Statement:` negation on partial streams (`partialNeg_eq_streamBits`): the low-order `false`
    digits and the lowest `true` are kept, and every higher digit is flipped. -/
def partialNeg : List Bool → List Bool
  | [] => []
  | false :: w => false :: partialNeg w
  | true :: w => true :: w.map not

/-- `Statement:` the lowest `n` digits of `-1 - m` are those of `m`, each flipped. -/
theorem streamBits_neg_one_sub (n : ℕ) (m : ℤ) :
    streamBits n (-1 - m) = (streamBits n m).map not := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rcases Int.emod_two_eq_zero_or_one m with h | h
    · have e : -1 - m = 1 + 2 * (-1 - m / 2) := by omega
      rw [e]
      simp [streamBits, h, ih, Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]
    · have e : -1 - m = 0 + 2 * (-1 - m / 2) := by omega
      rw [e]
      simp [streamBits, h, ih]

-- Statement: Mathlib, the bitwise form: bit `k` of `lnot n` is the negation of bit `k` of `n`.
#check @Int.testBit_lnot
-- Statement: `Int.lnot m` is `-1 - m`.
example (m : ℤ) : Int.lnot m = -1 - m := by
  cases m with
  | ofNat n => simp only [Int.lnot, Int.ofNat_eq_natCast]; omega
  | negSucc n => simp only [Int.lnot]; omega

/-- `Statement:` `partialNeg` keeps the lowest `|w|` digits of `-streamVal w`. -/
theorem partialNeg_eq_streamBits (w : List Bool) :
    partialNeg w = streamBits w.length (-(streamVal w : ℤ)) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false =>
      have e : -((streamVal (false :: w) : ℕ) : ℤ) = 0 + 2 * (-(streamVal w : ℤ)) := by
        simp [streamVal]
      rw [e]
      simp [partialNeg, streamBits, ih]
      congr 1; omega
    | true =>
      have e : -((streamVal (true :: w) : ℕ) : ℤ) = 1 + 2 * (-1 - (streamVal w : ℤ)) := by
        simp [streamVal]; ring
      rw [e]
      simp [partialNeg, streamBits, streamBits_neg_one_sub, streamBits_streamVal,
        Int.add_mul_ediv_left _ _ (by norm_num : (2 : ℤ) ≠ 0)]

-- Statement: so `partialNeg` is `affineExt 0 (-1) 0`.
example : partialNeg = affineExt 0 (-1) 0 := funext fun w => by
  rw [partialNeg_eq_streamBits]; simp only [affineExt, neg_one_mul, add_zero]

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

-- Statement: by `compl_semiconj_tapeCons` and `Function.IsFixedPt.map`, complement carries the
--   all-false tape, the only fixed point of prepend-`false` (`tapeCons_isFixedPt_iff`), to a fixed
--   point of prepend-`true`.
example : Function.IsFixedPt (tapeCons true) (fun _ => false)ᶜ :=
  (tapeCons_const false).map compl_semiconj_tapeCons

-- Statement: Mathlib, complement on a Boolean algebra is antitone.
#check @compl_antitone
-- Statement: Mathlib, complement sends ⊥ to ⊤ in a Heyting algebra; on `ℕ → Bool` these are ⊥ and
--   ⊤ of the pointwise order.
#check @compl_bot

-- Statement: run backwards, complement semiconjugates prepend-`true` to prepend-`false`.
example : Function.Semiconj (compl : (ℕ → Bool) → (ℕ → Bool)) (tapeCons true) (tapeCons false) :=
  fun _ => by funext n; cases n <;> rfl

/-! ## § VII. Local ignorance and local knowledge

In the prefix order `<+:` on `List Bool`, local ignorance at `w` is `w` as the least element of the
up-set `{v | w <+: v}`; a motion `F` respects it when `w <+: F w` (a post-fixed point), which allows
digits beyond `w`. Local knowledge at `w` is `w` as the greatest element of `{u | u <+: w}`; `F` only
forgets at `w` when `F w <+: w` (a pre-fixed point). These are least and greatest elements of such
sets in the prefix order. No `ZPSemilattice` on `List Bool` induces the prefix order (next `example`),
and no `=` is stated between them and ⊥ of a `ZPSemilattice`, `MachinePhase`'s `c₀`, or ε₀. -/

-- Statement: no `ZPSemilattice` on `List Bool` induces the prefix order (`join a b = b ↔ a <+: b`):
--   `[false]` and `[true]` have no common extension (the `List (Fin 2)` form of that incomparability is
--   `branches_incomparable`, `ZeroParadox/Valuation/BranchingRequirement.lean`).
example : ¬ ∃ inst : ZPSemilattice (List Bool),
    ∀ a b : List Bool, inst.join a b = b ↔ a <+: b := by
  rintro ⟨inst, h⟩
  have h1 : [false] <+: inst.join [false] [true] := (h _ _).1 (by
    rw [← inst.join_assoc, inst.join_idem])
  have h2 : [true] <+: inst.join [false] [true] := (h _ _).1 (by
    rw [inst.join_comm [false] [true], ← inst.join_assoc, inst.join_idem])
  rcases hj : inst.join [false] [true] with _ | ⟨b, t⟩
  · rw [hj] at h1; simp at h1
  · rw [hj] at h1 h2
    simp [List.cons_prefix_cons] at h1 h2
    exact Bool.noConfusion (h1.symm.trans h2)

/-- `Statement:` committing one digit is a cover of the empty stream in the prefix order: strictly
    above it, with nothing strictly between. -/
theorem first_digit_covers (d : Bool) :
    ([] : List Bool) <+: [d] ∧ ([] : List Bool) ≠ [d] ∧
    ∀ u : List Bool, [] <+: u → u <+: [d] → u = [] ∨ u = [d] := by
  refine ⟨List.nil_prefix, by simp, fun u _ h => ?_⟩
  rcases u with _ | ⟨b, t⟩
  · exact Or.inl rfl
  · obtain ⟨s, hs⟩ := h
    simp at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact Or.inr rfl

-- Statement: the empty stream has two distinct covers, `[false]` and `[true]`.
example : (([] : List Bool) <+: [false] ∧ ([] : List Bool) ≠ [false] ∧
      ∀ u : List Bool, [] <+: u → u <+: [false] → u = [] ∨ u = [false]) ∧
    (([] : List Bool) <+: [true] ∧ ([] : List Bool) ≠ [true] ∧
      ∀ u : List Bool, [] <+: u → u <+: [true] → u = [] ∨ u = [true]) ∧
    ([false] : List Bool) ≠ [true] :=
  ⟨first_digit_covers false, first_digit_covers true, by decide⟩

-- Statement: they are its only covers.
example (u : List Bool) (h2 : ([] : List Bool) ≠ u)
    (h3 : ∀ v : List Bool, [] <+: v → v <+: u → v = [] ∨ v = u) : u = [false] ∨ u = [true] := by
  rcases u with _ | ⟨b, t⟩
  · exact absurd rfl h2
  · rcases h3 [b] List.nil_prefix ⟨t, rfl⟩ with h | h
    · simp at h
    · cases b <;> simp_all

-- Statement: under `List Bool`'s own order, which is lexicographic, `[true]` does not cover `[]`:
--   `[false]` lies between.
example : ¬ ([] : List Bool) ⋖ [true] := fun h => h.2 (c := [false]) (by decide) (by decide)
-- Reading: the shape the OVER leg asks for (`UpAndOver.cover`, Mathlib `CovBy`), here in the prefix
--   order, for which no order instance is built (`List Bool`'s own `≤` is lexicographic, under which
--   `[false]` lies between `[]` and `[true]`); with its two covers and no join it is Winskel's
--   conflict shape (`ZeroParadox/Order/SnapCannotBe.lean` § II).

-- Statement: `w` lies in the up-set `{v | w <+: v}` and is a prefix of each of its members.
example (w : List Bool) : w <+: w ∧ ∀ v ∈ {v : List Bool | w <+: v}, w <+: v :=
  ⟨List.prefix_refl w, fun _ h => h⟩

-- Statement: respecting allows digits beyond `w`: the identity respects every `w`, and
--   `partialDouble` respects `[]` while adding a digit.
example (w : List Bool) : w <+: id w ∧ ([] : List Bool) <+: partialDouble [] :=
  ⟨List.prefix_refl w, List.nil_prefix⟩

/-- `Statement:` `partialDouble` respects local ignorance at `w` exactly when every digit of `w`
    is `false`. -/
theorem double_respects_iff (w : List Bool) : w <+: partialDouble w ↔ ∀ b ∈ w, b = false := by
  show w <+: false :: w ↔ _
  induction w with
  | nil => simp
  | cons b t ih =>
    rw [List.cons_prefix_cons]
    constructor
    · rintro ⟨rfl, h⟩ c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rfl
      · exact ih.mp h c hc
    · intro h
      have hb : b = false := h b (by simp)
      subst hb
      exact ⟨rfl, ih.mpr fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

-- Statement: every iterate of `partialDouble` from `List.replicate n false` stays above it.
example (n m : ℕ) : List.replicate n false <+: partialDouble^[m] (List.replicate n false) := by
  have h : ∀ m, partialDouble^[m] (List.replicate n false) = List.replicate (m + n) false :=
    fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Function.iterate_succ_apply', ih]
        simp [partialDouble, List.replicate_succ, Nat.succ_add]
  rw [h, Nat.add_comm, List.replicate_add]; exact List.prefix_append _ _

/-- `Statement:` `partialAddOne` respects local ignorance at `w` exactly at `w = []`. -/
theorem addOne_respects_iff (w : List Bool) : w <+: partialAddOne w ↔ w = [] := by
  constructor
  · intro h
    have heq : w = partialAddOne w := List.IsPrefix.eq_of_length h (partialAddOne_length w).symm
    cases w with
    | nil => rfl
    | cons b t => cases b <;> simp [partialAddOne] at heq
  · rintro rfl; exact List.nil_prefix
-- Reading: the prefix order has a cover of `[]` (`first_digit_covers`) and add-one, which preserves
--   length, fixes `[]`; an analogue of `tsnap_holds_but_nothing_moves` (`ZeroParadox/Order/Snap.lean`),
--   where `stuckPhase` fixes every phase.

-- Statement: `partialNeg` respects local ignorance at every all-`false` stream
--   (`partialNeg_replicate_false`).
example (n : ℕ) : List.replicate n false <+: partialNeg (List.replicate n false) := by
  rw [partialNeg_replicate_false]

-- Statement: `w` lies in `{u | u <+: w}` and each of its members is a prefix of `w`.
example (w : List Bool) : w <+: w ∧ ∀ u ∈ {u : List Bool | u <+: w}, u <+: w :=
  ⟨List.prefix_refl w, fun _ h => h⟩

-- Statement: truncation (`List.dropLast`) only forgets, at every `w`.
example (w : List Bool) : w.dropLast <+: w := List.dropLast_prefix w

/-- `Statement:` iterating truncation from `w` reaches `[]` after `|w|` steps. -/
theorem dropLast_iterate_eq_nil (w : List Bool) : List.dropLast^[w.length] w = [] := by
  have h : ∀ n, (List.dropLast^[n] w).length = w.length - n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', List.length_dropLast, ih]; omega
  exact List.eq_nil_of_length_eq_zero (by rw [h, Nat.sub_self])

/-- `Statement:` `partialDouble w` is never a prefix of `w`: doubling only forgets at no `w`. -/
theorem double_never_forgets (w : List Bool) : ¬ partialDouble w <+: w := fun h => by
  have := h.length_le
  simp [partialDouble] at this

/-- `Statement:` `partialAddOne` only forgets exactly at `w = []`; it preserves length, so forgetting
    is fixing (`partialAddOne_fixed_iff`). -/
theorem addOne_forgets_iff (w : List Bool) : partialAddOne w <+: w ↔ w = [] := by
  constructor
  · intro h
    exact (partialAddOne_fixed_iff w).1 (h.eq_of_length (partialAddOne_length w))
  · rintro rfl; exact List.nil_prefix
-- Reading: local ignorance and local knowledge at `w` are the up-set and the prefix set of one `w`;
--   doubling's climb from `[]` and truncation's descent to it are the two directions.

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
#print axioms tapeCons_isFixedPt_iff
#print axioms streamFill_nil_isFixedPt_iff
#print axioms streamVal
#print axioms streamBits
#print axioms streamBits_length
#print axioms streamBits_add_pow_mul
#print axioms streamBits_streamVal
#print axioms affineExt
#print axioms affineExt_length
#print axioms affineExt_sound
#print axioms eq_streamVal_streamBits_add
#print axioms streamBits_length_eq_iff
#print axioms partialAddOne_eq_streamBits
#print axioms affineExt_iterate_length
#print axioms affineExt_zero_iterate_nil
#print axioms affineExt_double_iterate
#print axioms affineExt_doubleAddOne_iterate
#print axioms partialNeg
#print axioms streamBits_neg_one_sub
#print axioms partialNeg_eq_streamBits
#print axioms partialNeg_replicate_false
#print axioms partialNeg_iterate_nil
#print axioms compl_semiconj_tapeCons
#print axioms first_digit_covers
#print axioms double_respects_iff
#print axioms addOne_respects_iff
#print axioms dropLast_iterate_eq_nil
#print axioms double_never_forgets
#print axioms addOne_forgets_iff
end PurityCheck
