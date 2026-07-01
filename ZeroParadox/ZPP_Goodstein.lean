import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

set_option maxHeartbeats 1000000

/-!
# Goodstein's theorem (full, hereditary base) — ε₀ ordinal descent

The full Goodstein process: write `n` in **hereditary** base `b` (every exponent is itself written in
hereditary base `b`, recursively), bump the base `b → b+1` everywhere, subtract 1; iterate. Goodstein's
theorem: this always reaches 0 — a statement independent of PA (Kirby–Paris 1982).

The proof is the signature ordinal-descent argument, now at full ε₀ strength (`ZPP_WeakGoodstein` is the
ω²-strength stepping stone). The hereditary base-`b` representation, evaluated with `ω` substituted for
`b` at every level, is the Cantor normal form of an ordinal: `heval b n`. Bumping the base does not
change this ordinal (`ω` is substituted regardless of the base — `heval_bump`); subtracting 1 strictly
decreases it (`heval_strictMono`); `Ordinal` is well-founded, so the sequence terminates.

Mathlib has the ingredients (`Nat.log`, `Nat.pow_log_le_self`, `Ordinal` exponentiation and
well-foundedness) but not the assembled theorem. STUB-FIRST.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.Goodstein

open Ordinal

/-- Hereditary ω-evaluation of `n` in base `b`: substitute `ω` for `b` in the hereditary base-`b`
    representation. `heval b 0 = 0`; otherwise with `e = log b n` (the top exponent), leading coefficient
    `n / b^e` (a digit `< b`) and remainder `n % b^e`,
    `heval b n = ω^(heval b e) · (n / b^e) + heval b (n % b^e)`.
    The exponent `e` is itself evaluated hereditarily — this is what reaches ε₀. -/
noncomputable def heval (b : ℕ) : ℕ → Ordinal.{0}
  | 0 => 0
  | (n + 1) =>
      omega0 ^ heval b (Nat.log b (n + 1)) * ((n + 1) / b ^ Nat.log b (n + 1) : ℕ)
        + heval b ((n + 1) % b ^ Nat.log b (n + 1))
  decreasing_by
    · exact Nat.log_lt_self b n.succ_ne_zero
    · have hpow : 0 < b ^ Nat.log b (n + 1) := by
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · simp
        · exact Nat.pow_pos hb
      exact lt_of_lt_of_le (Nat.mod_lt _ hpow) (Nat.pow_log_le_self b n.succ_ne_zero)

/-- The hereditary base bump `b → b+1`: reinterpret the hereditary base-`b` representation of `n` in
    base `b+1` (recursively, at every level). A natural number. -/
def bump (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      (b + 1) ^ bump b (Nat.log b (n + 1)) * ((n + 1) / b ^ Nat.log b (n + 1))
        + bump b ((n + 1) % b ^ Nat.log b (n + 1))
  decreasing_by
    · exact Nat.log_lt_self b n.succ_ne_zero
    · have hpow : 0 < b ^ Nat.log b (n + 1) := by
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · simp
        · exact Nat.pow_pos hb
      exact lt_of_lt_of_le (Nat.mod_lt _ hpow) (Nat.pow_log_le_self b n.succ_ne_zero)

/-- One Goodstein step from base `b`: bump the base, subtract 1. -/
def gstep (b n : ℕ) : ℕ := bump b n - 1

/-- The Goodstein sequence from `n`, with base `k + 2` at step `k`. -/
def gseq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => gstep (k + 2) (gseq n k)

/-- `heval b 0 = 0`. -/
@[simp] lemma heval_zero (b : ℕ) : heval b 0 = 0 := by rw [heval]

/-- Unfolding of `heval` at a positive argument. -/
lemma heval_succ (b n : ℕ) :
    heval b (n + 1) = omega0 ^ heval b (Nat.log b (n + 1)) * ((n + 1) / b ^ Nat.log b (n + 1) : ℕ)
      + heval b ((n + 1) % b ^ Nat.log b (n + 1)) := by
  rw [heval]

/-- Unfolding of `bump` at a positive argument. -/
lemma bump_succ (b n : ℕ) :
    bump b (n + 1) = (b + 1) ^ bump b (Nat.log b (n + 1)) * ((n + 1) / b ^ Nat.log b (n + 1))
      + bump b ((n + 1) % b ^ Nat.log b (n + 1)) := by
  rw [bump]

/-- For `b ≥ 2` and `n ≠ 0`, the leading hereditary digit `n / b^(log b n)` is in `[1, b)`. -/
lemma lead_digit_pos {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) :
    0 < n / b ^ Nat.log b n :=
  Nat.div_pos (Nat.pow_log_le_self b hn) (Nat.pow_pos (by omega))

/-- `heval` is positive on nonzero inputs (for base `b ≥ 2`). -/
lemma heval_pos {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (hn : n ≠ 0) : 0 < heval b n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [heval_succ]
  refine lt_of_lt_of_le ?_ le_self_add
  have hc : 0 < ((m + 1) / b ^ Nat.log b (m + 1) : ℕ) := lead_digit_pos hb (by omega)
  calc (0 : Ordinal) < omega0 ^ heval b (Nat.log b (m + 1)) :=
        opow_pos _ omega0_pos
    _ = omega0 ^ heval b (Nat.log b (m + 1)) * 1 := (mul_one _).symm
    _ ≤ omega0 ^ heval b (Nat.log b (m + 1)) * ((m + 1) / b ^ Nat.log b (m + 1) : ℕ) := by
        gcongr
        exact_mod_cast hc

/-- `heval` decomposition at any nonzero argument. -/
lemma heval_eq (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    heval b n = omega0 ^ heval b (Nat.log b n) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
      + heval b (n % b ^ Nat.log b n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact heval_succ b m

/-- The hereditary leading digit is `< b`. -/
lemma lead_digit_lt {b : ℕ} (hb : 2 ≤ b) {n : ℕ} (_hn : n ≠ 0) :
    n / b ^ Nat.log b n < b := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega)), ← pow_succ']
  exact Nat.lt_pow_succ_log_self (by omega) n

/-- **Crux 1 (with its boundedness companion).** `heval` is strictly monotone in `n`, and every value
    is below `ω^(heval b (log b n) + 1)`.

    Proof: strong induction on `n` proving the conjunction, since the two halves are mutually recursive
    in the CNF order — mono's `log b m < log b n` case uses the bound on `m`; the bound needs the
    remainder fact `heval b (n % b^e) < ω^(heval b e)` (the internal `rem_bound`), which in turn uses
    mono at the smaller exponent `log b (n % b^e) < e`. The equal-leading-exponent case of mono splits
    on the leading digit, then recurses on the remainder. -/
lemma heval_mono_bound {b : ℕ} (hb : 2 ≤ b) :
    ∀ n, (∀ m, m < n → heval b m < heval b n) ∧
      (n ≠ 0 → heval b n < omega0 ^ (heval b (Nat.log b n) + 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    -- Remainder bound: `heval b (x % b^(log b x)) < ω^(heval b (log b x))`, for any `x ≠ 0`
    -- whose strict predecessors already satisfy the conjunction.
    have rem_bound : ∀ x : ℕ, x ≠ 0 →
        (∀ k, k < x → (∀ j, j < k → heval b j < heval b k) ∧
          (k ≠ 0 → heval b k < omega0 ^ (heval b (Nat.log b k) + 1))) →
        heval b (x % b ^ Nat.log b x) < omega0 ^ heval b (Nat.log b x) := by
      intro x hx0 IHx
      rcases eq_or_ne (x % b ^ Nat.log b x) 0 with h0 | h0
      · rw [h0, heval_zero]; exact opow_pos _ omega0_pos
      · have hd : 0 < b ^ Nat.log b x := Nat.pow_pos (by omega)
        have hrlt : x % b ^ Nat.log b x < b ^ Nat.log b x := Nat.mod_lt _ hd
        have hlogr : Nat.log b (x % b ^ Nat.log b x) < Nat.log b x :=
          Nat.log_lt_of_lt_pow h0 hrlt
        have hrx : x % b ^ Nat.log b x < x :=
          lt_of_lt_of_le hrlt (Nat.pow_log_le_self b hx0)
        have hex : Nat.log b x < x := Nat.log_lt_self b hx0
        have hbnd := (IHx _ hrx).2 h0
        have hmono := (IHx _ hex).1 _ hlogr
        calc heval b (x % b ^ Nat.log b x)
            < omega0 ^ (heval b (Nat.log b (x % b ^ Nat.log b x)) + 1) := hbnd
          _ ≤ omega0 ^ heval b (Nat.log b x) :=
              opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hmono)
    refine ⟨?_, ?_⟩
    · -- Monotonicity: `∀ m < n, heval b m < heval b n`.
      intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [heval_zero]; exact heval_pos hb (by omega)
      · have hn0 : n ≠ 0 := by omega
        rcases lt_or_eq_of_le (Nat.log_mono_right hm.le) with hlt | heq
        · -- Strictly smaller leading exponent: bound `m`, lift through `ω^·`.
          have hbm := (IH m hm).2 hm0
          have hee : heval b (Nat.log b m) < heval b (Nat.log b n) :=
            (IH (Nat.log b n) (Nat.log_lt_self b hn0)).1 _ hlt
          have h1 : omega0 ^ (heval b (Nat.log b m) + 1) ≤ omega0 ^ heval b (Nat.log b n) :=
            opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hee)
          have h2 : omega0 ^ heval b (Nat.log b n) ≤ heval b n := by
            rw [heval_eq b hn0]
            refine le_trans ?_ le_self_add
            exact le_mul_left _ (by exact_mod_cast lead_digit_pos hb hn0)
          exact lt_of_lt_of_le hbm (le_trans h1 h2)
        · -- Equal leading exponent `e`: compare leading digits, then remainders.
          rw [heval_eq b hm0, heval_eq b hn0, heq]
          set e := Nat.log b n with he
          have hd : 0 < b ^ e := Nat.pow_pos (by omega)
          have hcm_le : m / b ^ e ≤ n / b ^ e := Nat.div_le_div_right hm.le
          rcases lt_or_eq_of_le hcm_le with hclt | hceq
          · -- Smaller leading digit.
            have hRm : heval b (m % b ^ e) < omega0 ^ heval b e := by
              have h := rem_bound m hm0 (fun k hk => IH k (hk.trans hm))
              rwa [heq] at h
            calc omega0 ^ heval b e * ((m / b ^ e : ℕ) : Ordinal) + heval b (m % b ^ e)
                < omega0 ^ heval b e * ((m / b ^ e : ℕ) : Ordinal) + omega0 ^ heval b e :=
                  (add_lt_add_iff_left _).2 hRm
              _ = omega0 ^ heval b e * (((m / b ^ e : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
              _ ≤ omega0 ^ heval b e * ((n / b ^ e : ℕ) : Ordinal) := by
                  apply mul_le_mul_right
                  exact_mod_cast Nat.succ_le_of_lt hclt
              _ ≤ omega0 ^ heval b e * ((n / b ^ e : ℕ) : Ordinal) + heval b (n % b ^ e) :=
                  le_self_add
          · -- Equal leading digit: remainders strictly ordered.
            have hrr : m % b ^ e < n % b ^ e := by
              have dm := Nat.div_add_mod m (b ^ e)
              have dn := Nat.div_add_mod n (b ^ e)
              rw [hceq] at dm
              omega
            have hrn_lt : n % b ^ e < n :=
              lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.pow_log_le_self b hn0)
            have hRR : heval b (m % b ^ e) < heval b (n % b ^ e) :=
              (IH (n % b ^ e) hrn_lt).1 _ hrr
            rw [hceq]
            exact (add_lt_add_iff_left _).2 hRR
    · -- Boundedness: `heval b n < ω^(heval b (log b n) + 1)`.
      intro hn0
      have hrem := rem_bound n hn0 IH
      rw [heval_eq b hn0]
      set E := heval b (Nat.log b n) with hE
      calc omega0 ^ E * ((n / b ^ Nat.log b n : ℕ) : Ordinal) + heval b (n % b ^ Nat.log b n)
          < omega0 ^ E * ((n / b ^ Nat.log b n : ℕ) : Ordinal) + omega0 ^ E :=
            (add_lt_add_iff_left _).2 hrem
        _ = omega0 ^ E * (((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1) := by rw [mul_add, mul_one]
        _ ≤ omega0 ^ E * omega0 := by
            apply mul_le_mul_right
            have hcast : ((n / b ^ Nat.log b n : ℕ) : Ordinal) + 1
                = ((n / b ^ Nat.log b n + 1 : ℕ) : Ordinal) := by exact_mod_cast rfl
            rw [hcast]
            exact (natCast_lt_omega0 _).le
        _ = omega0 ^ (E + 1) := by rw [← opow_succ, Order.succ_eq_add_one]

/-- **Crux 1.** `heval` is strictly monotone in `n` (fixed base `b ≥ 2`). -/
lemma heval_strictMono {b : ℕ} (hb : 2 ≤ b) {m n : ℕ} (h : m < n) :
    heval b m < heval b n :=
  (heval_mono_bound hb n).1 m h

/-- `bump b 0 = 0`. -/
@[simp] lemma bump_zero (b : ℕ) : bump b 0 = 0 := by rw [bump]

/-- `bump` decomposition at any nonzero argument. -/
lemma bump_eq {b : ℕ} {n : ℕ} (hn : n ≠ 0) :
    bump b n = (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n)
      + bump b (n % b ^ Nat.log b n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact bump_succ b m

/-- `bump b n = 0 ↔ n = 0`. -/
lemma bump_eq_zero_iff (b n : ℕ) : bump b n = 0 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp only [bump]⟩
  by_contra hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [bump_succ] at h
  have hpow : 0 < b ^ Nat.log b (m + 1) := by
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact Nat.pow_pos hb
  have hc : 0 < (m + 1) / b ^ Nat.log b (m + 1) :=
    Nat.div_pos (Nat.pow_log_le_self b (by omega)) hpow
  have hfirst : 0 < (b + 1) ^ bump b (Nat.log b (m + 1)) * ((m + 1) / b ^ Nat.log b (m + 1)) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) hc
  omega

/-- `bump` is positive on nonzero inputs. -/
lemma bump_pos {b n : ℕ} (hn : n ≠ 0) : 0 < bump b n :=
  Nat.pos_of_ne_zero (by rw [Ne, bump_eq_zero_iff]; exact hn)

/-- Monotonicity + boundedness for `bump`, the natural-number analogue of `heval_mono_bound`:
    bumping the base preserves the hereditary-base order. Needed for the size estimate that makes
    the base-`(b+1)` decomposition of `bump b n` valid. -/
lemma bump_mono_bound {b : ℕ} (hb : 2 ≤ b) :
    ∀ n, (∀ m, m < n → bump b m < bump b n) ∧
      (n ≠ 0 → bump b n < (b + 1) ^ (bump b (Nat.log b n) + 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    have rem_bound : ∀ x : ℕ, x ≠ 0 →
        (∀ k, k < x → (∀ j, j < k → bump b j < bump b k) ∧
          (k ≠ 0 → bump b k < (b + 1) ^ (bump b (Nat.log b k) + 1))) →
        bump b (x % b ^ Nat.log b x) < (b + 1) ^ bump b (Nat.log b x) := by
      intro x hx0 IHx
      rcases eq_or_ne (x % b ^ Nat.log b x) 0 with h0 | h0
      · rw [h0, bump_zero]; exact Nat.pow_pos (show 0 < b + 1 by omega)
      · have hd : 0 < b ^ Nat.log b x := Nat.pow_pos (by omega)
        have hrlt : x % b ^ Nat.log b x < b ^ Nat.log b x := Nat.mod_lt _ hd
        have hlogr : Nat.log b (x % b ^ Nat.log b x) < Nat.log b x :=
          Nat.log_lt_of_lt_pow h0 hrlt
        have hrx : x % b ^ Nat.log b x < x :=
          lt_of_lt_of_le hrlt (Nat.pow_log_le_self b hx0)
        have hex : Nat.log b x < x := Nat.log_lt_self b hx0
        have hbnd := (IHx _ hrx).2 h0
        have hmono := (IHx _ hex).1 _ hlogr
        calc bump b (x % b ^ Nat.log b x)
            < (b + 1) ^ (bump b (Nat.log b (x % b ^ Nat.log b x)) + 1) := hbnd
          _ ≤ (b + 1) ^ bump b (Nat.log b x) := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · intro m hm
      rcases eq_or_ne m 0 with rfl | hm0
      · rw [bump_zero]; exact bump_pos (by omega)
      · have hn0 : n ≠ 0 := by omega
        rcases lt_or_eq_of_le (Nat.log_mono_right hm.le) with hlt | heq
        · have hbm := (IH m hm).2 hm0
          have hee : bump b (Nat.log b m) < bump b (Nat.log b n) :=
            (IH (Nat.log b n) (Nat.log_lt_self b hn0)).1 _ hlt
          have h1 : (b + 1) ^ (bump b (Nat.log b m) + 1) ≤ (b + 1) ^ bump b (Nat.log b n) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          have h2 : (b + 1) ^ bump b (Nat.log b n) ≤ bump b n := by
            rw [bump_eq hn0]
            refine le_trans ?_ (Nat.le_add_right _ _)
            exact Nat.le_mul_of_pos_right _ (lead_digit_pos hb hn0)
          exact lt_of_lt_of_le hbm (le_trans h1 h2)
        · rw [bump_eq hm0, bump_eq hn0, heq]
          set e := Nat.log b n with he
          have hd : 0 < b ^ e := Nat.pow_pos (by omega)
          have hcm_le : m / b ^ e ≤ n / b ^ e := Nat.div_le_div_right hm.le
          rcases lt_or_eq_of_le hcm_le with hclt | hceq
          · have hRm : bump b (m % b ^ e) < (b + 1) ^ bump b e := by
              have h := rem_bound m hm0 (fun k hk => IH k (hk.trans hm))
              rwa [heq] at h
            calc (b + 1) ^ bump b e * (m / b ^ e) + bump b (m % b ^ e)
                < (b + 1) ^ bump b e * (m / b ^ e) + (b + 1) ^ bump b e := by omega
              _ = (b + 1) ^ bump b e * (m / b ^ e + 1) := by ring
              _ ≤ (b + 1) ^ bump b e * (n / b ^ e) := Nat.mul_le_mul (le_refl _) (by omega)
              _ ≤ (b + 1) ^ bump b e * (n / b ^ e) + bump b (n % b ^ e) := Nat.le_add_right _ _
          · have hrr : m % b ^ e < n % b ^ e := by
              have dm := Nat.div_add_mod m (b ^ e)
              have dn := Nat.div_add_mod n (b ^ e)
              rw [hceq] at dm
              omega
            have hrn_lt : n % b ^ e < n :=
              lt_of_lt_of_le (Nat.mod_lt _ hd) (Nat.pow_log_le_self b hn0)
            have hRR : bump b (m % b ^ e) < bump b (n % b ^ e) :=
              (IH (n % b ^ e) hrn_lt).1 _ hrr
            rw [hceq]
            omega
    · intro hn0
      have hrem := rem_bound n hn0 IH
      rw [bump_eq hn0]
      have hclt : n / b ^ Nat.log b n < b := lead_digit_lt hb hn0
      calc (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n) + bump b (n % b ^ Nat.log b n)
          < (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n)
              + (b + 1) ^ bump b (Nat.log b n) := by omega
        _ = (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n + 1) := by ring
        _ ≤ (b + 1) ^ bump b (Nat.log b n) * (b + 1) := Nat.mul_le_mul (le_refl _) (by omega)
        _ = (b + 1) ^ (bump b (Nat.log b n) + 1) := (pow_succ _ _).symm

/-- The size estimate: the base-`b` remainder of `x`, bumped, stays below the bumped leading power. -/
lemma bump_rem_lt {b : ℕ} (hb : 2 ≤ b) {x : ℕ} (_hx : x ≠ 0) :
    bump b (x % b ^ Nat.log b x) < (b + 1) ^ bump b (Nat.log b x) := by
  rcases eq_or_ne (x % b ^ Nat.log b x) 0 with h0 | h0
  · rw [h0, bump_zero]; exact Nat.pow_pos (show 0 < b + 1 by omega)
  · have hd : 0 < b ^ Nat.log b x := Nat.pow_pos (by omega)
    have hrlt : x % b ^ Nat.log b x < b ^ Nat.log b x := Nat.mod_lt _ hd
    have hlogr : Nat.log b (x % b ^ Nat.log b x) < Nat.log b x :=
      Nat.log_lt_of_lt_pow h0 hrlt
    have hbnd := (bump_mono_bound hb (x % b ^ Nat.log b x)).2 h0
    have hmono := (bump_mono_bound hb (Nat.log b x)).1 _ hlogr
    calc bump b (x % b ^ Nat.log b x)
        < (b + 1) ^ (bump b (Nat.log b (x % b ^ Nat.log b x)) + 1) := hbnd
      _ ≤ (b + 1) ^ bump b (Nat.log b x) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Crux 2 (bump invariance).** Reinterpreting `n`'s hereditary base-`b` form in base `b+1` does not
    change the ω-evaluation. The base-`(b+1)` decomposition of `bump b n` is `(b+1)^(bump b e) · c +
    bump b r`, with leading exponent `bump b e`, the *same* leading digit `c`, and remainder `bump b r`
    (valid because `bump_rem_lt` keeps the remainder below the leading power); the recursion on `e` and
    `r` is closed by the strong induction hypothesis. -/
lemma heval_bump {b : ℕ} (hb : 2 ≤ b) (n : ℕ) : heval (b + 1) (bump b n) = heval b n := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hd : 0 < b ^ Nat.log b n := Nat.pow_pos (by omega)
      have hc_pos : 0 < n / b ^ Nat.log b n := lead_digit_pos hb hn0
      have hr_lt : n % b ^ Nat.log b n < b ^ Nat.log b n := Nat.mod_lt _ hd
      have hsize : bump b (n % b ^ Nat.log b n) < (b + 1) ^ bump b (Nat.log b n) :=
        bump_rem_lt hb hn0
      have hN : bump b n
          = (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n)
              + bump b (n % b ^ Nat.log b n) := bump_eq hn0
      have hNne : bump b n ≠ 0 := by rw [Ne, bump_eq_zero_iff]; exact hn0
      have hlog : Nat.log (b + 1) (bump b n) = bump b (Nat.log b n) := by
        rw [hN]
        apply Nat.log_eq_of_pow_le_of_lt_pow
        · calc (b + 1) ^ bump b (Nat.log b n)
              ≤ (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n) :=
                Nat.le_mul_of_pos_right _ hc_pos
            _ ≤ (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n)
                  + bump b (n % b ^ Nat.log b n) := Nat.le_add_right _ _
        · calc (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n)
                + bump b (n % b ^ Nat.log b n)
              < (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n)
                  + (b + 1) ^ bump b (Nat.log b n) := by omega
            _ = (b + 1) ^ bump b (Nat.log b n) * (n / b ^ Nat.log b n + 1) := by ring
            _ ≤ (b + 1) ^ bump b (Nat.log b n) * (b + 1) :=
                Nat.mul_le_mul (le_refl _) (by have := lead_digit_lt hb hn0; omega)
            _ = (b + 1) ^ (bump b (Nat.log b n) + 1) := (pow_succ _ _).symm
      have hdig : bump b n / (b + 1) ^ bump b (Nat.log b n) = n / b ^ Nat.log b n := by
        rw [hN, Nat.mul_add_div (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hsize, add_zero]
      have hmod : bump b n % (b + 1) ^ bump b (Nat.log b n) = bump b (n % b ^ Nat.log b n) := by
        have hdm := Nat.div_add_mod (bump b n) ((b + 1) ^ bump b (Nat.log b n))
        rw [hdig] at hdm
        omega
      rw [heval_eq (b + 1) hNne, hlog, hdig, hmod,
          IH (Nat.log b n) (Nat.log_lt_self b hn0),
          IH (n % b ^ Nat.log b n) (lt_of_lt_of_le hr_lt (Nat.pow_log_le_self b hn0))]
      exact (heval_eq b hn0).symm

/-- Each Goodstein step strictly decreases the ordinal measure, until 0 is reached. -/
lemma gseq_measure_lt (n : ℕ) (k : ℕ) (hk : gseq n k ≠ 0) :
    heval (k + 3) (gseq n (k + 1)) < heval (k + 2) (gseq n k) := by
  have hb : 2 ≤ k + 2 := by omega
  have hbump : heval (k + 3) (bump (k + 2) (gseq n k)) = heval (k + 2) (gseq n k) :=
    heval_bump hb (gseq n k)
  have hMne : bump (k + 2) (gseq n k) ≠ 0 := by rw [Ne, bump_eq_zero_iff]; exact hk
  have hstep : gseq n (k + 1) = bump (k + 2) (gseq n k) - 1 := rfl
  rw [hstep, ← hbump]
  exact heval_strictMono (by omega) (Nat.sub_lt (Nat.pos_of_ne_zero hMne) one_pos)

/-- **Goodstein's theorem.** The Goodstein sequence from any `n` reaches 0. -/
theorem goodstein_terminates (n : ℕ) : ∃ k, gseq n k = 0 := by
  by_contra h
  simp only [not_exists] at h
  set m : ℕ → Ordinal := fun k => heval (k + 2) (gseq n k) with hmdef
  have hm : ∀ k, m (k + 1) < m k := fun k => by
    have := gseq_measure_lt n k (h k); simpa [hmdef] using this
  obtain ⟨x, ⟨k, rfl⟩, hmin⟩ := wellFounded_lt.has_min (Set.range m) ⟨m 0, 0, rfl⟩
  exact hmin (m (k + 1)) ⟨k + 1, rfl⟩ (hm k)

end ZeroParadox.Goodstein

section PurityCheck
open ZeroParadox.Goodstein
#print axioms goodstein_terminates
end PurityCheck
