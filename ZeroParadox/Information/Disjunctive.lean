import ZeroParadox.Information.CrossingTrials
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Disjunctive sequences: a tape on which every finite word occurs

## Engineer's Take

My one truest belief on this has always been that the bottom is infinitely complex. If that
statement is true, then all the necessary instructions are already sitting on tape. That all zero
tape has to exist so that a non-zero tape has any concept of what the reference object is, to be
able to have another tape and another program.

---

## Formal Overview (AI-assisted)
A tape `ℕ → Bool` is DISJUNCTIVE (standard term) when every finite word occurs in it.
The all-false tape fails, a primitive recursive tape passes, the fair coin passes almost surely;
under the hypothesis every code word is PRESENT, never executed. `ZeroParadox/Information/Disjunctive.md`.
-/

namespace ZeroParadox

open MeasureTheory ProbabilityTheory Filter
open Nat.Partrec Encodable

/-! ## § I. The definition, and the at-least-once form it is equivalent to -/

/-- **Disjunctive tape:** every finite word `w` occurs at infinitely many positions `n`. -/
def Disjunctive (x : ℕ → Bool) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Bool), ∃ᶠ n in atTop, ∀ i : Fin k, x (n + i) = w i

/-- **The at-least-once form:** every finite word occurs at some position. -/
def DisjunctiveOnce (x : ℕ → Bool) : Prop :=
  ∀ (k : ℕ) (w : Fin k → Bool), ∃ n, ∀ i : Fin k, x (n + i) = w i

/-- **`Statement:` an at-least-once tape has every word past every position `N`**, because `N`
falses followed by `w` occur somewhere. No `Filter` appears in this statement. -/
theorem occurs_past_of_once {x : ℕ → Bool} (h : DisjunctiveOnce x) (k : ℕ) (w : Fin k → Bool)
    (N : ℕ) : ∃ n, N ≤ n ∧ ∀ i : Fin k, x (n + i) = w i := by
  obtain ⟨n, hn⟩ := h (N + k)
    (fun i => if hi : N ≤ (i : ℕ) then w ⟨i - N, by have := i.isLt; omega⟩ else false)
  refine ⟨n + N, Nat.le_add_left N n, fun i => ?_⟩
  have hi := hn ⟨N + i, by have := i.isLt; omega⟩
  rw [dif_pos (Nat.le_add_right N i)] at hi
  rw [show n + N + (i : ℕ) = n + (N + i) by omega]
  refine hi.trans (congrArg w (Fin.ext ?_))
  show N + (i : ℕ) - N = i
  omega

/-- **`Statement:` the two forms agree.** -/
theorem disjunctive_iff_once (x : ℕ → Bool) : Disjunctive x ↔ DisjunctiveOnce x := by
  constructor
  · intro h k w
    exact (h k w).exists
  · intro h k w
    rw [Filter.frequently_atTop]
    intro a
    obtain ⟨n, hn, hw⟩ := occurs_past_of_once h k w a
    exact ⟨n, hn, hw⟩

/-! ## § II. Controls: a tape that fails, and a computable tape that passes -/

/-- **`Statement:` control, the all-false tape is not disjunctive** (`true` never occurs). -/
theorem allFalse_not_disjunctive : ¬ Disjunctive (fun _ => false) := by
  intro h
  obtain ⟨n, hn⟩ := (h 1 (fun _ => true)).exists
  exact Bool.false_ne_true (hn 0)

/-- Bit `i` of `j`, little-endian, by halving `i` times. -/
def bitAt (j i : ℕ) : Bool := (fun m => m / 2)^[i] j % 2 == 1

/-- The number whose first `k` little-endian bits spell `w`. -/
def ofBits : (k : ℕ) → (Fin k → Bool) → ℕ
  | 0, _ => 0
  | k + 1, w => 2 * ofBits k (fun i => w i.succ) + (if w 0 then 1 else 0)

/-- **`Statement:` `ofBits` is read back by `bitAt`.** -/
theorem bitAt_ofBits (k : ℕ) (w : Fin k → Bool) (i : Fin k) : bitAt (ofBits k w) i = w i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · show ((2 * ofBits k (fun i => w i.succ) + (if w 0 then 1 else 0)) % 2 == 1) = w 0
      cases h : w 0
      · rw [if_neg Bool.false_ne_true, show (2 * ofBits k (fun i => w i.succ) + 0) % 2 = 0 by omega]
        rfl
      · rw [if_pos rfl, show (2 * ofBits k (fun i => w i.succ) + 1) % 2 = 1 by omega]
        rfl
    · have hd : (2 * ofBits k (fun i => w i.succ) + (if w 0 then 1 else 0)) / 2
          = ofBits k (fun i => w i.succ) := by
        cases w 0
        · rw [if_neg Bool.false_ne_true]; omega
        · rw [if_pos rfl]; omega
      show ((fun m => m / 2)^[(j : ℕ) + 1] (2 * ofBits k (fun i => w i.succ) +
        (if w 0 then 1 else 0)) % 2 == 1) = w j.succ
      rw [Function.iterate_succ_apply, hd]
      exact ih (fun i => w i.succ) j

/-- Triangular numbers, by recursion: `tri (m + 1) = tri m + m + 1`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | m + 1 => tri m + m + 1

/-- One counting step on pairs `(m, i)` with `i ≤ m`. -/
def untriStep (p : ℕ × ℕ) : ℕ × ℕ := if p.2 < p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)

/-- Position `n` as (slot, offset), by counting up from `(0, 0)`. -/
def untri (n : ℕ) : ℕ × ℕ := untriStep^[n] (0, 0)

/-- **`Statement:` `untri` inverts `(m, i) ↦ tri m + i` on `i ≤ m`.** -/
theorem untri_tri_add (m i : ℕ) (hi : i ≤ m) : untri (tri m + i) = (m, i) := by
  have step : ∀ n, untri (n + 1) = untriStep (untri n) := fun n =>
    Function.iterate_succ_apply' untriStep n (0, 0)
  induction m generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    rfl
  | succ m ih =>
    induction i with
    | zero =>
      show untri (tri m + m + 1) = (m + 1, 0)
      rw [step, ih m le_rfl]
      exact if_neg (Nat.lt_irrefl m)
    | succ i ihi =>
      rw [show tri (m + 1) + (i + 1) = (tri (m + 1) + i) + 1 by omega, step, ihi (by omega)]
      exact if_pos (show i < m + 1 by omega)

/-- **A Champernowne-style tape.** Position `n` lies in slot `m` at offset `i`; slot `m` is the
pair `(a, b)`, and spells the `b` bits of `a - b`, then falses. -/
def champ (n : ℕ) : Bool :=
  decide ((untri n).2 < (untri (untri n).1).2) &&
    bitAt ((untri (untri n).1).1 - (untri (untri n).1).2) (untri n).2

/-- **`Statement:` every word occurs on `champ`:** `w` of length `k` starts slot
`tri (ofBits k w + k) + k`. No `Filter` appears in this statement. -/
theorem champ_disjunctiveOnce : DisjunctiveOnce champ := by
  intro k w
  refine ⟨tri (tri (ofBits k w + k) + k), fun i => ?_⟩
  have hm : untri (tri (ofBits k w + k) + k) = (ofBits k w + k, k) :=
    untri_tri_add _ _ (Nat.le_add_left k _)
  have hn : untri (tri (tri (ofBits k w + k) + k) + i) = (tri (ofBits k w + k) + k, (i : ℕ)) :=
    untri_tri_add _ _ (by have := i.isLt; omega)
  unfold champ
  rw [hn]
  dsimp only
  rw [hm]
  dsimp only
  rw [Nat.add_sub_cancel, bitAt_ofBits, decide_eq_true i.isLt]
  rfl

/-- **`Statement:` `champ` is disjunctive.** -/
theorem champ_disjunctive : Disjunctive champ :=
  (disjunctive_iff_once champ).2 champ_disjunctiveOnce

/-- **`Statement:` `champ` is primitive recursive.** -/
theorem champ_primrec : Primrec champ := by
  have hit : Primrec (fun p : ℕ × ℕ => (fun m => m / 2)^[p.2] p.1) :=
    Primrec.nat_iterate Primrec.snd Primrec.fst
      (Primrec.nat_div.comp₂ Primrec₂.right (Primrec₂.const 2))
  have hb : Primrec (fun p : ℕ × ℕ => bitAt p.1 p.2) :=
    (Primrec.beq.comp (Primrec.nat_mod.comp hit (Primrec.const 2)) (Primrec.const 1)).of_eq
      fun _ => rfl
  have hstep : Primrec untriStep :=
    Primrec.ite (primrecPred_iff_primrec_decide.2 (Primrec.nat_lt.decide.comp Primrec.snd
      Primrec.fst)) (Primrec.pair Primrec.fst (Primrec.succ.comp Primrec.snd))
      (Primrec.pair (Primrec.succ.comp Primrec.fst) (Primrec.const 0))
  have hu : Primrec untri :=
    Primrec.nat_iterate Primrec.id (Primrec.const (0, 0)) (hstep.comp₂ Primrec₂.right)
  have hv : Primrec (fun n : ℕ => untri (untri n).1) := hu.comp (Primrec.fst.comp hu)
  have hlt : Primrec (fun n : ℕ => decide ((untri n).2 < (untri (untri n).1).2)) :=
    Primrec.nat_lt.decide.comp (Primrec.snd.comp hu) (Primrec.snd.comp hv)
  have hbit : Primrec (fun n : ℕ =>
      bitAt ((untri (untri n).1).1 - (untri (untri n).1).2) (untri n).2) :=
    hb.comp (Primrec.pair (Primrec.nat_sub.comp (Primrec.fst.comp hv) (Primrec.snd.comp hv))
      (Primrec.snd.comp hu))
  exact (Primrec.and.comp hlt hbit).of_eq fun _ => rfl

-- Statement: disjunctive does not require randomness: `champ` is a closed primitive recursive
-- definition, with no measure in its statement, and it is disjunctive.
example : Disjunctive champ ∧ Primrec champ := ⟨champ_disjunctive, champ_primrec⟩

/-! ## § III. The fair-coin tape is disjunctive almost surely (infinite monkey theorem)

The fair coin is `trials (1/2)` of `ZeroParadox/Information/CrossingTrials.lean`; its four fences
stand. Each word occurs in infinitely many disjoint aligned blocks (second Borel–Cantelli). -/

/-- **The fair-coin tape:** `trials` at `p = 1/2`. -/
noncomputable abbrev fairTape : Measure (ℕ → Bool) := trials (1/2) (by norm_num)

/-- **`Statement:` a pattern on `T` has probability `(1/2)^card T`.** -/
theorem fairTape_pi_singleton (T : Finset ℕ) (t : ℕ → Bool) :
    fairTape (Set.pi (T : Set ℕ) (fun j => ({t j} : Set Bool))) =
      ((1/2 : NNReal) : ENNReal) ^ T.card := by
  have hhalf : (1 - 1/2 : NNReal) = 1/2 := tsub_eq_of_eq_add (by rw [add_halves])
  have hb : ∀ b : Bool, (PMF.bernoulli (1/2 : NNReal) (by norm_num)).toMeasure {b} =
      ((1/2 : NNReal) : ENNReal) := fun b => by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.bernoulli_apply]
    cases b
    · simp only [cond_false, hhalf]
    · simp only [cond_true]
  rw [fairTape, trials, Measure.infinitePi_pi]
  · simp only [hb, Finset.prod_const]
  · exact fun j _ => measurableSet_singleton (t j)

/-- **Pull `n`:** bits `n*k, …, n*k + k - 1` spell `w`. -/
def wordBlock (k : ℕ) (w : Fin k → Bool) (n : ℕ) : Set (ℕ → Bool) :=
  {x | ∀ i : Fin k, x (n * k + i) = w i}

/-- **`Statement:` each pull is measurable.** -/
theorem wordBlock_measurable (k : ℕ) (w : Fin k → Bool) (n : ℕ) :
    MeasurableSet (wordBlock k w n) := by
  have : wordBlock k w n = ⋂ i : Fin k, {x : ℕ → Bool | x (n * k + i) = w i} := by
    ext x; simp [wordBlock]
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_eq_fun (measurable_pi_apply _) measurable_const

/-- **`Statement:` `|S|` disjoint pulls all hit with probability `((1/2)^k)^|S|`.** -/
theorem fairTape_biInter_wordBlock (k : ℕ) (w : Fin k → Bool) (S : Finset ℕ) :
    fairTape (⋂ n ∈ S, wordBlock k w n) = (((1/2 : NNReal) : ENNReal) ^ k) ^ S.card := by
  let blockSet : ℕ → Finset ℕ := fun n => Finset.univ.image (fun i : Fin k => n * k + (i : ℕ))
  let tgt : ℕ → Bool := fun j => if h : j % k < k then w ⟨j % k, h⟩ else false
  have tgt_block : ∀ (n : ℕ) (i : Fin k), tgt (n * k + i) = w i := fun n i => by
    have h : (n * k + i) % k = i := by rw [Nat.mul_add_mod', Nat.mod_eq_of_lt i.isLt]
    simp only [tgt]
    rw [dif_pos (by rw [h]; exact i.isLt)]
    congr 1
    exact Fin.ext h
  have mem_blockSet : ∀ {n j : ℕ}, j ∈ blockSet n ↔ ∃ i : Fin k, n * k + i = j := by
    intro n j; simp [blockSet]
  have blockSet_card : ∀ n, (blockSet n).card = k := fun n => by
    simp only [blockSet]
    rw [Finset.card_image_of_injective _ (fun a b h => Fin.ext (Nat.add_left_cancel h)),
      Finset.card_univ, Fintype.card_fin]
  have hdisj : (S : Set ℕ).PairwiseDisjoint blockSet := by
    intro n _ m _ hnm
    rw [Function.onFun, Finset.disjoint_left]
    intro j hj hj'
    obtain ⟨i, rfl⟩ := mem_blockSet.1 hj
    obtain ⟨i', hi'⟩ := mem_blockSet.1 hj'
    have hk : 0 < k := i.pos
    have hd : ∀ (a : ℕ) (b : Fin k), (a * k + b) / k = a := fun a b => by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt b.isLt, zero_add]
    apply hnm
    calc n = (n * k + i) / k := (hd n i).symm
      _ = (m * k + i') / k := by rw [hi']
      _ = m := hd m i'
  have hinter : (⋂ n ∈ S, wordBlock k w n) =
      Set.pi ((S.biUnion blockSet : Finset ℕ) : Set ℕ) (fun j => ({tgt j} : Set Bool)) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_pi, Finset.mem_coe, Finset.mem_biUnion,
      Set.mem_singleton_iff]
    constructor
    · rintro h j ⟨n, hn, hj⟩
      obtain ⟨i, rfl⟩ := mem_blockSet.1 hj
      rw [tgt_block]; exact h n hn i
    · intro h n hn i
      have := h (n * k + i) ⟨n, hn, mem_blockSet.2 ⟨i, rfl⟩⟩
      rw [tgt_block] at this; exact this
  rw [hinter, fairTape_pi_singleton, Finset.card_biUnion hdisj]
  simp only [blockSet_card, Finset.sum_const, smul_eq_mul]
  rw [← pow_mul, Nat.mul_comm]

/-- **`Statement:` each pull hits the word with probability `(1/2)^k`.** -/
theorem fairTape_wordBlock (k : ℕ) (w : Fin k → Bool) (n : ℕ) :
    fairTape (wordBlock k w n) = ((1/2 : NNReal) : ENNReal) ^ k := by
  simpa using fairTape_biInter_wordBlock k w {n}

/-- **`Statement:` the disjoint aligned pulls are independent events.** -/
theorem wordBlock_iIndepSet (k : ℕ) (w : Fin k → Bool) : iIndepSet (wordBlock k w) fairTape := by
  rw [iIndepSet_iff_meas_biInter (wordBlock_measurable k w)]
  intro S
  rw [fairTape_biInter_wordBlock, Finset.prod_congr rfl (fun n _ => fairTape_wordBlock k w n),
    Finset.prod_const]

/-- **`Statement:` the word occupies infinitely many aligned blocks with probability one.** -/
theorem monkey_limsup (k : ℕ) (w : Fin k → Bool) :
    fairTape (limsup (wordBlock k w) atTop) = 1 :=
  measure_limsup_eq_one (wordBlock_measurable k w) (wordBlock_iIndepSet k w) (by
    simp only [fairTape_wordBlock]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero _ (by simp)))

/-- **`Statement:` almost every fair-coin tape is disjunctive.** An aligned block at pull `n`
is an occurrence at position `n * k`. -/
theorem fairTape_disjunctive_ae : ∀ᵐ x ∂fairTape, Disjunctive x := by
  have hall : ∀ᵐ x ∂fairTape, ∀ (k : ℕ) (w : Fin k → Bool),
      ∃ᶠ n in atTop, x ∈ wordBlock k w n := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro w
    have hm := MeasurableSet.measurableSet_limsup (wordBlock_measurable k w)
    rw [ae_iff]
    have : {x : ℕ → Bool | ¬ ∃ᶠ n in atTop, x ∈ wordBlock k w n} =
        (limsup (wordBlock k w) atTop)ᶜ := by
      ext x; simp [mem_limsup_iff_frequently_mem]
    rw [this, prob_compl_eq_zero_iff hm]
    exact monkey_limsup k w
  filter_upwards [hall] with x hx k w
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Frequently.of_forall (fun _ i => i.elim0)
  · rw [Filter.frequently_atTop]
    intro a
    obtain ⟨n, hn, hb⟩ := Filter.frequently_atTop.1 (hx k w) a
    exact ⟨n * k, le_trans hn (Nat.le_mul_of_pos_right n hk), hb⟩

/-! ## § IV. Hypothesis form: a disjunctive tape carries every program's code word -/

/-- The little-endian binary of `encode c`, of width `Nat.size (encode c)`. -/
def codeWord (c : Code) : Fin (Nat.size (encode c)) → Bool := fun i => (encode c).testBit i

/-- **`Statement:` the word determines the code:** equal widths and equal bits force `c = d`. -/
theorem codeWord_determines {c d : Code} (h : Nat.size (encode c) = Nat.size (encode d))
    (hw : ∀ i : Fin (Nat.size (encode c)), (encode c).testBit i = (encode d).testBit i) :
    c = d := by
  apply Encodable.encode_injective
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < Nat.size (encode c)
  · exact hw ⟨i, hi⟩
  · have hle : Nat.size (encode c) ≤ i := not_lt.1 hi
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right two_pos hle)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self _)
          (Nat.pow_le_pow_right two_pos (h ▸ hle)))]

/-- **`Statement:` PRESENCE.** Given `h : Disjunctive x`, every code word occurs in `x` infinitely
often. `Reading:` presence is Sense A, a description on the tape; occurrence, Sense B, is the
occurrence commitment (`ZeroParadox/Order/Snap.lean`). Nothing here executes a code. -/
theorem code_occurs_of_disjunctive {x : ℕ → Bool} (h : Disjunctive x) (c : Code) :
    ∃ᶠ n in atTop, ∀ i : Fin (Nat.size (encode c)), x (n + i) = codeWord c i :=
  h _ _

/-- **`Statement:` control, `Code.zero`'s word is EMPTY**, so its presence is vacuous. -/
theorem codeWord_zero_width : Nat.size (encode Code.zero) = 0 := by
  rw [show encode Code.zero = 0 by simp [Code.encodeCode_eq, Code.encodeCode]]
  exact Nat.size_zero

/-- **`Statement:` a code other than `Code.zero` has a `true` bit in its word.** -/
theorem codeWord_has_true {c : Code} (hc : c ≠ Code.zero) : ∃ i, codeWord c i = true := by
  have hne : encode c ≠ 0 := fun h =>
    hc (Encodable.encode_injective (h.trans (by simp [Code.encodeCode_eq, Code.encodeCode])))
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  have hlt : i < Nat.size (encode c) := by
    by_contra hge
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_size_self _)
      (Nat.pow_le_pow_right two_pos (not_lt.1 hge)))] at hi
    exact Bool.false_ne_true hi
  exact ⟨⟨i, hlt⟩, hi⟩

/-- **`Statement:` control, the all-false tape carries no such code word anywhere.** -/
theorem allFalse_misses_code {c : Code} (hc : c ≠ Code.zero) :
    ¬ ∃ n, ∀ i : Fin (Nat.size (encode c)), (fun _ : ℕ => false) (n + i) = codeWord c i := by
  rintro ⟨n, hn⟩
  obtain ⟨i, hi⟩ := codeWord_has_true hc
  have := hn i
  rw [hi] at this
  exact Bool.false_ne_true this

/-! ## § V. No full self-copy: a disjunctive tape is not periodic -/

/-- **`Statement:` a tape equal to its own shift by some `a > 0` is not disjunctive:** every
word of length `a` at position `n` is the one at `n % a`, so at most `a` of the `2 ^ a` occur.
A special case of Barnsley–Leśniak's remark that no disjunctive sequence is almost periodic
(`ZeroParadox/Information/Disjunctive.md`, Prior art): such a tape is almost periodic, the
`example` after this theorem. -/
theorem not_disjunctive_of_periodic {x : ℕ → Bool} {a : ℕ} (ha : 0 < a)
    (hper : ∀ n, x (n + a) = x n) : ¬ Disjunctive x := by
  intro h
  have hq : ∀ q m, x (m + a * q) = x m := by
    intro q
    induction q with
    | zero => intro m; rfl
    | succ q ih => intro m; rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hword : ∀ n i, x (n + i) = x (n % a + i) := by
    intro n i
    have := Nat.mod_add_div n a
    calc x (n + i) = x ((n % a + i) + a * (n / a)) := by congr 1; omega
      _ = x (n % a + i) := hq _ _
  let f : Fin a → (Fin a → Bool) := fun r i => x (r + i)
  have hns : ¬ Function.Surjective f := by
    intro hs
    have := Fintype.card_le_of_surjective f hs
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact absurd this (not_le.2 Nat.lt_two_pow_self)
  apply hns
  intro w
  obtain ⟨n, hn⟩ := (h a w).exists
  exact ⟨⟨n % a, Nat.mod_lt n ha⟩, funext fun i => (hword n i).symm.trans (hn i)⟩

-- Statement: a tape equal to its own shift by `a > 0` is almost periodic in the sense Barnsley and
-- Leśniak recall from Muchnik, Semenov and Ushakov: for each word occurring infinitely often there
-- is a length `m`, depending on the word (here `a + k`), such that every segment of length `m`
-- contains it.
example {x : ℕ → Bool} {a : ℕ} (ha : 0 < a) (hper : ∀ n, x (n + a) = x n)
    (k : ℕ) (w : Fin k → Bool) (hocc : ∃ᶠ n in atTop, ∀ i : Fin k, x (n + i) = w i) :
    ∃ m, 0 < m ∧ ∀ s, ∃ q, s ≤ q ∧ q + k ≤ s + m ∧ ∀ i : Fin k, x (q + i) = w i := by
  obtain ⟨p, hp⟩ := hocc.exists
  have hq : ∀ t n, x (n + a * t) = x n := by
    intro t
    induction t with
    | zero => intro n; rfl
    | succ t ih => intro n; rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hr : ∀ i : Fin k, x (p % a + i) = w i := fun i => by
    rw [← hp i, show p + (i : ℕ) = (p % a + i) + a * (p / a) by
      have := Nat.mod_add_div p a; omega, hq]
  refine ⟨a + k, by omega, fun s => ?_⟩
  have hpa := Nat.mod_lt p ha
  have hsa := Nat.mod_lt s ha
  have hsd := Nat.mod_add_div s a
  by_cases h : s % a ≤ p % a
  · refine ⟨p % a + a * (s / a), by omega, by omega, fun i => ?_⟩
    rw [show p % a + a * (s / a) + (i : ℕ) = (p % a + i) + a * (s / a) by omega, hq, hr]
  · refine ⟨p % a + a * (s / a + 1), ?_, ?_, fun i => ?_⟩
    · rw [Nat.mul_succ]; omega
    · rw [Nat.mul_succ]; omega
    · rw [show p % a + a * (s / a + 1) + (i : ℕ) = (p % a + i) + a * (s / a + 1) by omega, hq, hr]

/-- **`Statement:` a disjunctive tape equals its shift by no `a > 0`:** no full copy of itself at
any offset. `Reading:` copies sit side by side, told apart by an address
(`selfPrints_universal_address`, `ZeroParadox/Computability/Kleene.lean`); the ⊥-role commitment,
with both sides stated, is § VI. -/
theorem disjunctive_not_periodic {x : ℕ → Bool} (h : Disjunctive x) :
    ¬ ∃ a, 0 < a ∧ ∀ n, x (n + a) = x n :=
  fun ⟨_, ha, hper⟩ => not_disjunctive_of_periodic ha hper h

-- Statement: control, the all-false tape is periodic with `a = 1`, and not disjunctive
-- (`allFalse_not_disjunctive`, § II).
example : (∀ n, (fun _ : ℕ => false) (n + 1) = (fun _ : ℕ => false) n) ∧
    ¬ Disjunctive (fun _ => false) := ⟨fun _ => rfl, allFalse_not_disjunctive⟩

-- Statement: control, `0 < a` carries it: every tape equals its shift by `0`, `champ` included.
example : (∀ n, champ (n + 0) = champ n) ∧ Disjunctive champ := ⟨fun _ => rfl, champ_disjunctive⟩

-- Statement: so `champ`, and almost every fair-coin tape, is periodic at no offset `a > 0`.
example : ¬ ∃ a, 0 < a ∧ ∀ n, champ (n + a) = champ n := disjunctive_not_periodic champ_disjunctive
example : ∀ᵐ x ∂fairTape, ¬ ∃ a, 0 < a ∧ ∀ n, x (n + a) = x n :=
  fairTape_disjunctive_ae.mono fun _ hx => disjunctive_not_periodic hx

-- Statement: the converse fails: the tape `true` only at `0` is periodic at no `a > 0` and is not
-- disjunctive (`true, true` occurs nowhere).
example : (¬ ∃ a, 0 < a ∧ ∀ n, (fun m => decide (m = 0)) (n + a) = (fun m => decide (m = 0)) n) ∧
    ¬ Disjunctive (fun m => decide (m = 0)) := by
  refine ⟨fun ⟨a, ha, hp⟩ => ?_, fun h => ?_⟩
  · have := hp 0
    simp at this
    omega
  · obtain ⟨n, hn⟩ := (h 2 (fun _ => true)).exists
    have h0 := hn 0
    have h1 := hn 1
    simp at h0 h1

/-! ## § VI. What maximal complexity would add

Standard theory, not proved here: a Martin-Löf random sequence, prefix-free incompressible, is
disjunctive; the converse fails at `champ` (§ II). Statement and search record in the ride-along.
`Reading:` Tim's commitment concerns the framework's ⊥ role, ⊥ of a `ZPSemilattice`: read as a tape,
its occupant is MAXIMALLY complex in that sense. No map from a `ZPSemilattice` to `ℕ → Bool` is
claimed or constructed, and no order on tapes in which a maximally complex tape is least: the reading
is a commitment, not a chart. In `ℕ → Bool` under the pointwise order, ⊥ is the all-false tape, which
is not disjunctive (`allFalse_not_disjunctive`). -/

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms Disjunctive
#print axioms DisjunctiveOnce
#print axioms occurs_past_of_once
#print axioms disjunctive_iff_once
#print axioms allFalse_not_disjunctive
#print axioms bitAt
#print axioms ofBits
#print axioms bitAt_ofBits
#print axioms tri
#print axioms untriStep
#print axioms untri
#print axioms untri_tri_add
#print axioms champ
#print axioms champ_disjunctiveOnce
#print axioms champ_disjunctive
#print axioms champ_primrec
#print axioms fairTape
#print axioms fairTape_pi_singleton
#print axioms wordBlock
#print axioms wordBlock_measurable
#print axioms fairTape_biInter_wordBlock
#print axioms fairTape_wordBlock
#print axioms wordBlock_iIndepSet
#print axioms monkey_limsup
#print axioms fairTape_disjunctive_ae
#print axioms codeWord
#print axioms codeWord_determines
#print axioms code_occurs_of_disjunctive
#print axioms codeWord_zero_width
#print axioms codeWord_has_true
#print axioms allFalse_misses_code
#print axioms not_disjunctive_of_periodic
#print axioms disjunctive_not_periodic

end PurityCheck
