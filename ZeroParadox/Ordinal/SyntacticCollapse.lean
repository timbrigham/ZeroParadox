import ZeroParadox.Ordinal.ConstructiveOrdinals

/-!
# Syntactic surrogate for the 2-adic metric collapse (choice-free)

## Engineer's Take

The snap is a one way operator away from zero to epsilon zero, and eventually that value sequence that is
created returns to zero. If zero is truly infinite to start with, we are isolating only a subsection of
the whole for the duration, and it eventually returns to a new bottom.

It is definitely a separate instance that you return to, versus where you left from. It is still part of
the entire family, so the question becomes whether you are looking at it from the family or the instance
point of view.

---

`synVal`, a syntactic depth on `ONote`, and the ε-N form of the ω-tower's collapse
(`synCollapse_epsN`, `synCollapse_norm_bound`), each at `[propext]` or cleaner. The conjecture under
test, what is and is not established, the triviality assessment and the prior art are in
`ZeroParadox/Ordinal/SyntacticCollapse.md`, beside this file.
-/

namespace ZeroParadox

open ONote

set_option maxHeartbeats 400000

/-! ### The syntactic valuation -/

/-- **Leading-exponent depth of an ordinal notation.** Purely syntactic: structural recursion on the
`ONote` constructors, never through `repr`.

`synVal 0 = 0` and `synVal (ω^e · n + a) = synVal e + 1`.

This mirrors the 2-adic valuation of `Gentzen.cnfToZp2` *on the ω-tower*, where the coefficient is
`1` and the remainder is `0`. Off the tower it disagrees with the 2-adic valuation, where the
coefficient and remainder contribute (`example` after `synVal_tower_eq_valuation`,
`ZeroParadox/Ordinal/CnfBridge.lean`). -/
def synVal : ONote → ℕ
  | 0 => 0
  | oadd e _ _ => synVal e + 1

@[simp] theorem synVal_zero : synVal 0 = 0 := rfl

@[simp] theorem synVal_oadd (e : ONote) (n : ℕ+) (a : ONote) :
    synVal (oadd e n a) = synVal e + 1 := rfl

/-- Applying `ω^·` raises the syntactic valuation by exactly one. -/
@[simp] theorem synVal_omegaPow (x : ONote) : synVal (omegaPow x) = synVal x + 1 := rfl

/-! ### The tower's valuation -/

/-- The `n`-th ω-tower stage has syntactic valuation exactly `n`.

The link to the 2-adic valuation on the tower is `synVal_tower_eq_valuation`
(`ZeroParadox/Ordinal/CnfBridge.lean`); its statement carries choice, so it is not proved here. -/
theorem synVal_tower (n : ℕ) : synVal (tower n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show synVal (omegaPow (tower n)) = n + 1
      rw [synVal_omegaPow, ih]

/-- The syntactic valuation is unbounded over the notations: the tower witnesses every level. -/
theorem synVal_unbounded : ∀ k : ℕ, ∃ x : ONote, k ≤ synVal x :=
  fun k => ⟨tower k, (synVal_tower k).ge⟩

/-! ### The non-trivial step: order forces valuation -/

/-- If `oadd e₁ n₁ a₁` is not `cmp`-greater than `oadd e₂ n₂ a₂`, then neither is `e₁` above `e₂`.
Immediate from the lexicographic shape of `ONote.cmp`. -/
theorem cmp_exp_ne_gt_of_ne_gt {e₁ e₂ a₁ a₂ : ONote} {n₁ n₂ : ℕ+}
    (h : ONote.cmp (oadd e₁ n₁ a₁) (oadd e₂ n₂ a₂) ≠ Ordering.gt) :
    ONote.cmp e₁ e₂ ≠ Ordering.gt := by
  intro he
  apply h
  simp only [ONote.cmp, he, Ordering.then]

/-- **Position in the syntactic order forces the valuation.** Any notation `x` that is not strictly
`cmp`-below `tower n` has syntactic valuation at least `n`.

This is the statement doing real work: the valuation lower bound is not a feature of one chosen
sequence, it is forced for *every* notation at or above the tower stage. Choice-free — the proof is
induction on `n` using only the lexicographic structure of `ONote.cmp`. -/
theorem le_synVal_of_tower_le :
    ∀ (n : ℕ) (x : ONote), ONote.cmp (tower n) x ≠ Ordering.gt → n ≤ synVal x
  | 0, _, _ => Nat.zero_le _
  | (n + 1), 0, h => absurd (by cases n <;> rfl : ONote.cmp (tower (n + 1)) 0 = Ordering.gt) h
  | (n + 1), oadd e k a, h => by
      have hunfold : tower (n + 1) = oadd (tower n) 1 0 := rfl
      rw [hunfold] at h
      have he : ONote.cmp (tower n) e ≠ Ordering.gt := cmp_exp_ne_gt_of_ne_gt h
      have hrec := le_synVal_of_tower_le n e he
      show n + 1 ≤ synVal e + 1
      exact Nat.succ_le_succ hrec

/-- **`synVal` is monotone for the syntactic order.** Moving up in `ONote.cmp` never decreases the
syntactic valuation.

This is the property that earns `synVal` the name *valuation* rather than merely *depth counter*. Without
it, `synVal` would be an arbitrary structural statistic that happened to agree with the tower; with it,
`synVal` is order-compatible, and `le_synVal_of_tower_le` above is its specialization at the tower.
Choice-free, by induction on the lexicographic structure of `ONote.cmp`, reusing `cmp_exp_ne_gt_of_ne_gt`.

Scope: this is monotonicity of the *syntactic* valuation. It disagrees with the 2-adic valuation off
the tower — see `synVal`. -/
theorem synVal_mono :
    ∀ (x y : ONote), ONote.cmp x y ≠ Ordering.gt → synVal x ≤ synVal y
  | 0, _, _ => Nat.zero_le _
  | oadd e n a, 0, h => absurd (rfl : ONote.cmp (oadd e n a) 0 = Ordering.gt) h
  | oadd e₁ n₁ a₁, oadd e₂ n₂ a₂, h => by
      have hexp : ONote.cmp e₁ e₂ ≠ Ordering.gt := cmp_exp_ne_gt_of_ne_gt h
      have ih : synVal e₁ ≤ synVal e₂ := synVal_mono e₁ e₂ hexp
      show synVal e₁ + 1 ≤ synVal e₂ + 1
      exact Nat.succ_le_succ ih

/-! ### The ε-N collapse statement

Stated directly, not via `Filter.Tendsto` or `Metric` — that API is where the classical
dependencies live. An element of 2-adic valuation `v` has norm `2 ^ (-v)`, so "the norm drops below
`2 ^ (-k)`" is exactly "the valuation exceeds `k`", plus arithmetic. -/

/-- **ε-N form of the collapse (valuation side).** For every target level `k` there is an `N` beyond
which every tower stage has syntactic valuation at least `k`. -/
theorem synCollapse_epsN : ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k ≤ synVal (tower n) :=
  fun k => ⟨k, fun n hn => (synVal_tower n).ge.trans' hn⟩

/-- **ε-N form of the collapse (norm side), stated in `ℕ`.**

The 2-adic norm of an element of valuation `v` is `2 ^ (-v)`, so "the norm is at most `2 ^ (-k)`" is
literally "`2 ^ k ≤ 2 ^ v`". Phrased that way the statement needs no division ring at all.

The reciprocal-free phrasing is deliberate, and is itself a finding. Writing the bound as
`1 / 2 ^ v ≤ 1 / 2 ^ k` over `ℚ` *does* drag in `Classical.choice` — but for no mathematical reason:
Mathlib's `ℚ` division-ring instance is choice-tainted, so even `(1 : ℚ) / 2 ^ n = 1 / 2 ^ n` proved
by `rfl` reports `[propext, Classical.choice, Quot.sound]`. Same content, `ℕ` phrasing, clean. -/
theorem synCollapse_norm_bound :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ^ k ≤ 2 ^ synVal (tower n) := by
  intro k
  refine ⟨k, fun n hn => ?_⟩
  have hk : k ≤ synVal (tower n) := (synVal_tower n).ge.trans' hn
  exact Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le 1)) hk

/-- The bound is attained, not merely approached: at stage `n` the reciprocal of the norm is
exactly `2 ^ n`. -/
theorem synCollapse_exact (n : ℕ) : 2 ^ synVal (tower n) = 2 ^ n := by
  rw [synVal_tower]

section PurityCheck
-- Target: `[propext]` or cleaner on every theorem. Contrast the measured
-- `[propext, Classical.choice, Quot.sound]` on `tower_converges_to_zero` and
-- `cnfToZp2_valuation_unbounded` in `ZeroParadox/Ordinal/Gentzen.lean`.
#print axioms synVal_zero
#print axioms synVal_oadd
#print axioms synVal_omegaPow
#print axioms synVal_tower
#print axioms synVal_unbounded
#print axioms cmp_exp_ne_gt_of_ne_gt
#print axioms le_synVal_of_tower_le
#print axioms synVal_mono
#print axioms synCollapse_epsN
#print axioms synCollapse_norm_bound
#print axioms synCollapse_exact
end PurityCheck

end ZeroParadox
