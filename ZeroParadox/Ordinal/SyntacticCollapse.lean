import ZeroParadox.Ordinal.ConstructiveOrdinals

/-!
# Syntactic surrogate for the 2-adic metric collapse (choice-free)

## The conjecture under test

The framework carries a standing conjecture: **`Classical.choice` is structurally forced by the ZP metric
collapse**, rather than merely imposed by Mathlib. Its own stated test is whether the snap and
`tower_converges_to_zero` can be proved without choice — if yes, choice is incidental; if no, it is forced.

That test has two halves, and they are in different states. The **snap half is resolved, incidental**:
`ZeroParadox.t_snap_derived` (`ZeroParadox/Order/Snap.lean`) depends on *no axioms at all*. The **metric
half** — the half the conjecture actually names — had never been attempted before this file. This file
moves it, and moves it only as far as *evidence*: `tower_converges_to_zero` itself still carries choice,
and the bridge from what is proved here to that statement is not proved (see "What this does NOT
establish"). Nothing here settles the conjecture in either direction.

## What this file is

An **experiment**, and a **surrogate**. It asks whether the *content* of the ZP-L/Gentzen metric
collapse — "the ω-tower's 2-adic encodings converge to 0 = ⊥" — is available without
`Classical.choice`, by staying entirely on the syntactic ordinal-notation substrate (`ONote`).

Measured starting point (`ZeroParadox/Ordinal/Gentzen.lean`):

* `ZeroParadox.tower_converges_to_zero` — `[propext, Classical.choice, Quot.sound]`
* `ZeroParadox.cnfToZp2_valuation_unbounded` — `[propext, Classical.choice, Quot.sound]`

The diagnosis under test is that the choice enters *before any topology*, through `NONote`/`NF`,
which Mathlib defines via `ONote.repr` — the syntax→semantics bridge into the choice-saturated
`Ordinal` type. If so, the convergence content should be reachable choice-free on the raw-syntax side.

Everything below is defined by structural recursion on `ONote` constructors. Nothing here calls
`ONote.repr`, mentions `NONote` or `NF`, or imports the 2-adic / topology stack.

## What is actually proved here

1. `synVal : ONote → ℕ` — the **leading-exponent depth** of a notation, purely syntactic.
2. `synVal_tower : synVal (tower n) = n`.
3. `synVal_unbounded : ∀ k, ∃ x : ONote, k ≤ synVal x`.
4. `le_synVal_of_tower_le` — **the non-trivial one.** *Every* notation that is not `cmp`-below
   `tower n` has `synVal ≥ n`. So the valuation lower bound is not a property of one hand-picked
   sequence: it is forced by position in the syntactic order.
4b. `synVal_mono` — `synVal` is **monotone** for `ONote.cmp`. This is what earns it the name
   *valuation* rather than *depth counter*, and `le_synVal_of_tower_le` is its specialization at the
   tower. Added after a verification pass challenged whether the definition was faithful; the check
   was worth running, and this is what it produced.
5. `synCollapse_epsN` / `synCollapse_norm_bound` — the ε-N statement, written out directly
   (`∀ k, ∃ N, ∀ n ≥ N, …`) rather than through `Filter.Tendsto`/`Metric`, since that API is where
   the classical dependencies sit. The norm form is stated in `ℕ` as `2 ^ k ≤ 2 ^ synVal ·`, which
   is exactly "norm `≤ 2 ^ (-k)`" for an element of valuation `synVal ·`, with no division ring.

## Result

Every theorem in this file reports `[propext]` or cleaner. Two secondary findings about *where* the
choice actually was:

* The first version of `le_synVal_of_tower_le` (item 4) closed with `simpa`, and reported
  `[propext, Classical.choice, Quot.sound]`. Replacing that one tactic call with an explicit
  `show` + `Nat.succ_le_succ` made it `[propext]`. The choice was a tactic artifact, not structure.
* Stating the norm bound over `ℚ` as `1 / 2 ^ v ≤ 1 / 2 ^ k` also reported choice — and so does
  `(1 : ℚ) / 2 ^ n = 1 / 2 ^ n` proved by `rfl`, which is mathematically vacuous. Mathlib's `ℚ`
  division-ring instance is choice-tainted at the instance level. Restating in `ℕ` removed it.

Both are cases of choice arriving through Mathlib packaging rather than through the mathematics —
the same shape as the diagnosis under test, at a smaller scale.

## What this does NOT establish

This is **not** a re-proof of `tower_converges_to_zero`, and it does not replace, supersede, or
discharge it. That theorem is a statement about `Filter.Tendsto` of `cnfToZp2 : NONote → ℤ_[2]`
in the 2-adic topology; this file proves statements about a `ℕ`-valued function on raw `ONote`.
Different carrier, different statement. In particular:

* **The bridge is not verified in Lean here.** That `synVal x` agrees with
  `(cnfToZp2 x).valuation` is *not* proved in this file, and cannot be without importing the very
  stack whose choice-dependence is under investigation. Gentzen's `cnfToZp2_tower_valuation`
  computes the 2-adic valuation of the tower to be `n`, and `synVal_tower` computes the syntactic
  depth of the tower to be `n`; the two agree numerically on the tower. That agreement is an
  observation about two separate computations, not a theorem linking them. On general notations
  `synVal` is *not* claimed to equal the 2-adic valuation at all — it ignores the coefficient and
  the remainder, which contribute in general.
* **It does not show the metric collapse is choice-free.** The honest reading is bounded: *the
  convergence content is available choice-free on the syntactic side, which is evidence that the
  `Classical.choice` in the 2-adic statement is Mathlib-imposed (accidental) rather than forced by
  the ZP structure.* Evidence, not proof.

## Triviality assessment

Items 1, 2, 3 and 5 are, honestly, close to trivial (4b is elementary too — the same lexicographic
induction as item 4, generalized): `synVal (tower n) = n` is "the depth of an
`n`-fold nesting is `n`", and unboundedness/ε-N follow immediately. An unbounded-valuation claim of
that shape holds of any sequence built by iterating a depth-increasing constructor, so on its own it
is weak evidence.

Item 4 is what carries the weight. It is an order→valuation implication quantified over *all*
notations: not "some sequence has growing valuation", but "nothing sitting at or above `tower n` in
the syntactic order can have depth below `n`". That is the statement which, transported across the
bridge, would say the 2-adic collapse is forced by ordinal position rather than exhibited by a
lucky choice of sequence. It is still elementary — it is lexicographic induction on `cmp` — but it
is not vacuous, and it is the piece that is choice-free here.

## Prior art

`ONote` / `NONote` and `ONote.cmp` are Mathlib (`Mathlib.SetTheory.Ordinal.Notation`). The technique
of working on the syntactic substrate to avoid the choice inherited from Mathlib's `Ordinal` is not
new here either — it is ZP-N's (`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`), which established
it for the ordinal *ascent* (`exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono`). This file
extends that same technique to the valuation/metric side. The contribution is the instance, not the
method.

## Engineer's Take

The snap is a one way operator away from zero to epsilon zero, and eventually that value sequence that is
created returns to zero. If zero is truly infinite to start with, we are isolating only a subsection of
the whole for the duration, and it eventually returns to a new bottom.

It is definitely a separate instance that you return to, versus where you left from. It is still part of
the entire family, so the question becomes whether you are looking at it from the family or the instance
point of view.
-/

namespace ZeroParadox

open ONote

set_option maxHeartbeats 400000

/-! ### The syntactic valuation -/

/-- **Leading-exponent depth of an ordinal notation.** Purely syntactic: structural recursion on the
`ONote` constructors, never through `repr`.

`synVal 0 = 0` and `synVal (ω^e · n + a) = synVal e + 1`.

This mirrors the 2-adic valuation of `Gentzen.cnfToZp2` *on the ω-tower*, where the coefficient is
`1` and the remainder is `0`. It is **not** claimed to agree with the 2-adic valuation on general
notations, where the coefficient and remainder contribute. -/
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

Numerically this matches `Gentzen.cnfToZp2_tower_valuation` (which computes the 2-adic valuation of
the tower's encoding to be `n`), but the two are separate computations — no theorem here links them.
-/
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
Added after a verification pass questioned whether the definition was faithful — the check was worth
running, and this is what it produced. Choice-free, by induction on the lexicographic structure of
`ONote.cmp`, reusing `cmp_exp_ne_gt_of_ne_gt`.

Scope, unchanged: this is monotonicity of the *syntactic* valuation. It is still not claimed to agree
with the 2-adic valuation on general notations — see the header. -/
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
