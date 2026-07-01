import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

set_option maxHeartbeats 800000

/-!
# Weak Goodstein termination (second-domain depth test: ordinals / proof theory)

The weak Goodstein process: write `n` in base `b`, then repeatedly bump the base (`b → b+1`, keeping the
digit list) and subtract 1. It always reaches 0. The proof is the signature ordinal-descent argument: the
digit list, evaluated at `ω` instead of the base, is a STRICTLY DECREASING ordinal measure — the natural
number can balloon (the bump increases it), yet the ordinal falls, and `Ordinal` is well-founded.

Structurally different from the Markov/analysis cycles: this is ordinal proof theory. Mathlib has the
ingredients (`Nat.digits`, `Nat.ofDigits`/`digits_ofDigits`, `Ordinal` well-foundedness) but not the
assembled theorem — the same gap shape as `exists_stationary`. STUB-FIRST.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.WeakGoodstein

open Ordinal

/-- Evaluate a (little-endian) digit list as an ordinal, substituting `ω` for the base:
    `ωeval (d :: l) = ω · ωeval l + d`. The units digit `d` is on the RIGHT of the ordinal sum: this is
    essential — `d + ω · ωeval l` would ABSORB the lower digits (ordinal `a + b = b` when `a < b`) and fail
    to be strictly monotone. -/
noncomputable def ωeval : List ℕ → Ordinal.{0}
  | [] => 0
  | d :: l => Ordinal.omega0 * ωeval l + (d : Ordinal)

/-- The ordinal measure of `n` written in base `b`. -/
noncomputable def gmeasure (b n : ℕ) : Ordinal.{0} := ωeval (Nat.digits b n)

/-- One weak-Goodstein step from base `b`: bump the base to `b+1` (same digit list), subtract 1. -/
def gstep (b n : ℕ) : ℕ := Nat.ofDigits (b + 1) (Nat.digits b n) - 1

/-- The weak-Goodstein sequence from `n`, with base `k+2` at step `k`. -/
def gseq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => gstep (k + 2) (gseq n k)

/-- `Nat.ofDigits` is monotone in the base (fixed digit list). -/
lemma ofDigits_base_mono {b₁ b₂ : ℕ} (h : b₁ ≤ b₂) :
    ∀ L : List ℕ, Nat.ofDigits b₁ L ≤ Nat.ofDigits b₂ L
  | [] => le_refl _
  | d :: l => by
    rw [Nat.ofDigits_cons, Nat.ofDigits_cons]
    exact Nat.add_le_add_left (Nat.mul_le_mul h (ofDigits_base_mono h l)) d

/-- `ωeval L = 0` iff all digits are zero. -/
lemma ωeval_eq_zero_iff (L : List ℕ) : ωeval L = 0 ↔ ∀ d ∈ L, d = 0 := by
  induction L with
  | nil => simp [ωeval]
  | cons d l ih =>
    rw [ωeval, Ordinal.add_eq_zero_iff, mul_eq_zero]
    simp only [Ordinal.omega0_ne_zero, false_or, Nat.cast_eq_zero, List.mem_cons, forall_eq_or_imp, ih]
    tauto

/-- The measure is positive for nonzero `n`. -/
lemma gmeasure_pos {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) : 0 < gmeasure b n := by
  have hne : gmeasure b n ≠ 0 := by
    rw [gmeasure, Ne, ωeval_eq_zero_iff]
    push_neg
    exact ⟨(Nat.digits b n).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hn),
      List.getLast_mem _, Nat.getLast_digit_ne_zero b hn⟩
  exact pos_iff_ne_zero.mpr hne

/-- **Crux.** The ω-evaluation of the base-`b` digits is strictly monotone in the natural (fixed base
    `b ≥ 2`): strong induction comparing high parts via `ω·A + d < ω·B`, else units. -/
lemma ωeval_strictMono {b : ℕ} (hb : 2 ≤ b) {m n : ℕ} (h : m < n) :
    gmeasure b m < gmeasure b n := by
  induction n using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    have hb1 : 1 < b := by omega
    have hn0 : 0 < n := by omega
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simpa [gmeasure, Nat.digits_zero, ωeval] using gmeasure_pos hb (by omega : n ≠ 0)
    · rw [gmeasure, gmeasure, Nat.digits_def' hb1 hn0, Nat.digits_def' hb1 hm0, ωeval, ωeval]
      have hdiv : m / b ≤ n / b := Nat.div_le_div_right (le_of_lt h)
      rcases eq_or_lt_of_le hdiv with heq | hlt
      · rw [heq]
        refine (add_lt_add_iff_left _).mpr ?_
        have hmod : m % b < n % b := by
          have e1 := Nat.div_add_mod m b
          have e2 := Nat.div_add_mod n b
          rw [← heq] at e2
          omega
        exact_mod_cast hmod
      · have hndiv : n / b < n := Nat.div_lt_self hn0 hb1
        have hA : gmeasure b (m / b) < gmeasure b (n / b) := ih (n / b) hndiv hlt
        rw [gmeasure, gmeasure] at hA
        calc Ordinal.omega0 * ωeval (Nat.digits b (m / b)) + ((m % b : ℕ) : Ordinal)
            < Ordinal.omega0 * ωeval (Nat.digits b (m / b)) + Ordinal.omega0 :=
              (add_lt_add_iff_left _).mpr (Ordinal.nat_lt_omega0 _)
          _ = Ordinal.omega0 * (ωeval (Nat.digits b (m / b)) + 1) := (mul_add_one _ _).symm
          _ ≤ Ordinal.omega0 * ωeval (Nat.digits b (n / b)) := by
              gcongr
              exact Order.add_one_le_iff.mpr hA
          _ ≤ Ordinal.omega0 * ωeval (Nat.digits b (n / b)) + ((n % b : ℕ) : Ordinal) := le_self_add

/-- **Bump invariance.** Re-basing the digit list does not change the ω-measure. -/
lemma gmeasure_bump (b n : ℕ) (hb : 2 ≤ b) :
    gmeasure (b + 1) (Nat.ofDigits (b + 1) (Nat.digits b n)) = gmeasure b n := by
  unfold gmeasure
  rw [Nat.digits_ofDigits (b + 1) (by omega) (Nat.digits b n)
    (fun l hl => by have := Nat.digits_lt_base (by omega) hl; omega)
    (fun hL => Nat.getLast_digit_ne_zero b (Nat.digits_ne_nil_iff_ne_zero.mp hL))]

/-- Each step strictly decreases the ordinal measure, as long as we have not reached 0. -/
lemma gseq_measure_lt (n : ℕ) (k : ℕ) (hk : gseq n k ≠ 0) :
    gmeasure (k + 3) (gseq n (k + 1)) < gmeasure (k + 2) (gseq n k) := by
  have hbump : gmeasure (k + 3) (Nat.ofDigits (k + 3) (Nat.digits (k + 2) (gseq n k)))
      = gmeasure (k + 2) (gseq n k) := by
    have := gmeasure_bump (k + 2) (gseq n k) (by omega); simpa using this
  have hMne : Nat.ofDigits (k + 3) (Nat.digits (k + 2) (gseq n k)) ≠ 0 := by
    have hle : gseq n k ≤ Nat.ofDigits (k + 3) (Nat.digits (k + 2) (gseq n k)) := by
      conv_lhs => rw [← Nat.ofDigits_digits (k + 2) (gseq n k)]
      exact ofDigits_base_mono (by omega) _
    omega
  have hstep : gseq n (k + 1)
      = Nat.ofDigits (k + 3) (Nat.digits (k + 2) (gseq n k)) - 1 := rfl
  rw [hstep, ← hbump]
  exact ωeval_strictMono (by omega) (Nat.sub_lt (Nat.pos_of_ne_zero hMne) one_pos)

/-- **Target.** The weak-Goodstein sequence always reaches 0. -/
theorem weak_goodstein_terminates (n : ℕ) : ∃ k, gseq n k = 0 := by
  by_contra h
  push_neg at h
  set m : ℕ → Ordinal := fun k => gmeasure (k + 2) (gseq n k) with hmdef
  have hm : ∀ k, m (k + 1) < m k := fun k => by
    have := gseq_measure_lt n k (h k); simpa [hmdef] using this
  obtain ⟨x, ⟨k, rfl⟩, hmin⟩ := wellFounded_lt.has_min (Set.range m) ⟨m 0, 0, rfl⟩
  exact hmin (m (k + 1)) ⟨k + 1, rfl⟩ (hm k)

end ZeroParadox.WeakGoodstein

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.WeakGoodstein
#print axioms weak_goodstein_terminates
end PurityCheck
