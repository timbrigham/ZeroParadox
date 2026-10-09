# Syntactic surrogate for the 2-adic metric collapse: the conjecture, the result and its fences

Ride-along documentation for [`ZeroParadox/Ordinal/SyntacticCollapse.lean`](SyntacticCollapse.lean).
The Lean file holds the declarations, the Engineer's Take and a statement per declaration; this file holds
the conjecture under test, the result, its fences and the prior art. Where the two would overlap, **the
Lean is authoritative**.

## The conjecture under test

The framework carries a standing conjecture: **`Classical.choice` is structurally forced by the ZP metric
collapse**, rather than merely imposed by Mathlib. Inside Mathlib that cannot be tested on
`tower_converges_to_zero`: its statement itself carries `Classical.choice` (a theorem that takes
`Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0)` as a hypothesis and proves
`True` by `trivial` reports `[propext, Classical.choice, Quot.sound]`, measured 2026-10-08). So the
test is posed on ZP-N's `ONote`, whose statements can be choice-free, and both outcomes are evidence.
A choice-free result on `ONote`, carried to the 2-adic valuation form along the tower by
`synVal_tower_eq_valuation` (`ZeroParadox/Ordinal/CnfBridge.lean`, the first `example` after it), is
evidence that the convergence content does not need choice, with choice entering through the notation
type (`NONote`, `ONote.NF`) and `ℤ_[2]` rather than through the mathematics; a failure would
be evidence the other way. Neither settles it, because the 2-adic statement, and the bridge's own
statement, carry choice in Mathlib. Essential needs a reduction to a taboo
(`ZeroParadox/Category/ChoiceCannotBe.lean` § IV).

The conjecture's original test, on the snap and on the metric collapse, had two halves, and they are
in different states. The **snap half is resolved, incidental**:
`ZeroParadox.t_snap_derived` (`ZeroParadox/Order/Snap.lean`) depends on *no axioms at all*. The **metric
half** — the half the conjecture actually names — had never been attempted before the Lean file. The Lean file
moves it, and moves it only as far as *evidence*: `tower_converges_to_zero` itself carries choice,
and the bridge from what is proved in the Lean file to its valuation ε-N form is proved on the tower only,
outside the Lean file (see "What this does NOT establish"). Nothing here settles the conjecture in
either direction.

## What the Lean file is

An **experiment**, and a **surrogate**. It asks whether the *content* of the ZP-L/Gentzen metric
collapse — "the ω-tower's 2-adic encodings converge to ℤ_[2]'s 0", ⊥ of ℤ_[2] under its norm
preorder and greatest under divisibility (`ZeroParadox/Valuation/Padic.lean`) — is available without
`Classical.choice`, by staying entirely on the syntactic ordinal-notation substrate (`ONote`).

Measured starting point (`ZeroParadox/Ordinal/Gentzen.lean`):

* `ZeroParadox.tower_converges_to_zero` — `[propext, Classical.choice, Quot.sound]`
* `ZeroParadox.cnfToZp2_valuation_unbounded` — `[propext, Classical.choice, Quot.sound]`

The diagnosis under test is that the choice enters *before any topology*, through `NONote`/`NF`,
which Mathlib defines via `ONote.repr` — the syntax→semantics bridge into the classically-built
`Ordinal` type. If so, the convergence content should be reachable choice-free on the raw-syntax side.

Everything in the Lean file is defined by structural recursion on `ONote` constructors. Nothing there calls
`ONote.repr`, mentions `NONote` or `NF`, or imports the 2-adic / topology stack.

## What is actually proved in the Lean file

1. `synVal : ONote → ℕ` — the **leading-exponent depth** of a notation, purely syntactic.
2. `synVal_tower : synVal (tower n) = n`.
3. `synVal_unbounded : ∀ k, ∃ x : ONote, k ≤ synVal x`.
4. `le_synVal_of_tower_le` — **the non-trivial one.** *Every* notation that is not `cmp`-below
   `tower n` has `synVal ≥ n`. So the syntactic valuation lower bound is not a property of one hand-picked
   sequence: it is forced by position in the syntactic order.
4b. `synVal_mono` — `synVal` is **monotone** for `ONote.cmp`. This is what earns it the name
   *valuation* rather than *depth counter*, and `le_synVal_of_tower_le` is its specialization at the
   tower.
5. `synCollapse_epsN` / `synCollapse_norm_bound` — the ε-N statement, written out directly
   (`∀ k, ∃ N, ∀ n ≥ N, …`) rather than through `Filter.Tendsto`/`Metric`, since that API is where
   the classical dependencies sit. The norm form is stated in `ℕ` as `2 ^ k ≤ 2 ^ synVal ·`, which
   is exactly "norm `≤ 2 ^ (-k)`" for an element of valuation `synVal ·`, with no division ring.

## Result

Every theorem in the Lean file reports `[propext]` or cleaner. Two secondary findings about *where* the
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
in the 2-adic topology; the Lean file proves statements about a `ℕ`-valued function on raw `ONote`.
Different carrier, different statement. In particular:

* **The bridge is proved on the tower only, outside the Lean file:** `synVal_tower_eq_valuation`
  (`ZeroParadox/Ordinal/CnfBridge.lean`). Its statement carries choice, so it cannot sit in the
  choice-free Lean file; off the tower the two need not agree (fails at ω+1: the second `example`
  after it).
* **It does not show the metric collapse is choice-free.** The 2-adic statement is STATEMENT-CARRIED
  (`ZeroParadox/Category/ChoiceCannotBe.md`; measured by the statement control above), so no proof of
  it can drop the choice. The honest reading of the restatement is bounded: *the convergence content
  is available choice-free on the syntactic side, which is evidence that the `Classical.choice` in
  the 2-adic statement is Mathlib-imposed rather than forced by the ZP structure.* Evidence, not proof.

## Triviality assessment

Items 1, 2, 3 and 5 are, honestly, close to trivial (4b is elementary too — the same lexicographic
induction as item 4, generalized): `synVal (tower n) = n` is "the depth of an
`n`-fold nesting is `n`", and unboundedness/ε-N follow immediately. An unbounded-valuation claim of
that shape holds of any sequence built by iterating a depth-increasing constructor, so on its own it
is weak evidence.

Item 4 is the non-vacuous statement on the syntactic side. It is an order→valuation implication
quantified over *all* notations: not "some sequence has growing valuation", but "nothing sitting at
or above `tower n` in the syntactic order can have depth below `n`". It is elementary (lexicographic
induction on `cmp`) and choice-free. It does **not** cross to the 2-adic side: the bridge holds on the
tower only, and off the tower `cnfToZp2` has no such bound (ω + 1, the second `example` after
`synVal_tower_eq_valuation` in `ZeroParadox/Ordinal/CnfBridge.lean`). What crosses is the tower's
ε-N statement (the first `example` there).

## Prior art

**Adjacent literature, and the delta stated precisely (read from source).** Syntactic complexity measures
on ordinal notations are an established subject: Buchholz, Cichon and Weiermann, *A Uniform Approach to
Fundamental Sequences and Hierarchies*, MLQ 40 (1994) 273-286, builds fundamental sequences from the
interplay between Bachmann systems and a term-complexity function they call a **norm**.

**`synVal` is NOT a norm in their sense, and the reason is the delta.** Their Definition 1(6) (p. 275)
fixes a norm by a *finite-fibre* condition, not by counting anything:

  `N` is a norm on `τ` iff `∀ α n, card {β < α : N β ≤ n} < ω`.

`synVal` fails this outright. Every finite ordinal notation `oadd 0 n 0` has `synVal = 1`, so
`{β < ω : synVal β ≤ 1}` is infinite. `synVal` reads only the leading-exponent depth and discards the
coefficient — and it is exactly that discarded data which would keep the fibres finite. So the Lean file's
measure is a *depth function*, deliberately coarser than a norm, adequate for the tower (where the
coefficient is always `1`) and inadequate as a norm in general.

Their Lemma 2 is the near neighbour: it defines an iteration-depth function `G α := min {i : α[0]^i = 0}`
— structurally the same idea as `synVal`. **On a Bachmann system, G IS a norm**, unconditionally: Lemma
2(a)'s proof (p. 276) concludes "Thus (τ, ·[·], G) is a normed Bachmann system. By Lemma 1(b) G is a
norm." Lemma 2(b) is a *separate sufficient condition* for the weaker bare-fundamental-sequences setting,
not an extra hypothesis.

**This sharpens the delta rather than softening it.** Iteration depth is not inherently too
coarse to be a norm — in their setting it satisfies the finite-fibre condition. `synVal` fails it for a
reason specific to *this* carrier: `ONote`'s `oadd e n a` carries a coefficient slot, so infinitely many
notations (`oadd 0 n 0` for every `n`) share depth 1. Their fundamental-sequence setting has no such slot
below a given point. So the gap is not "depth is a weak measure" but "this carrier lets a coefficient
hide inside a depth class" — which is exactly the information `synVal` discards, and exactly why it
suffices for the tower (where the coefficient is pinned at 1) and nowhere else.

`ONote` / `NONote` and `ONote.cmp` are Mathlib (`Mathlib.SetTheory.Ordinal.Notation`). The technique
of working on the syntactic substrate to avoid the choice inherited from Mathlib's `Ordinal` is not
new here either — it is ZP-N's (`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`), which established
it for the ordinal *ascent* (`exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono`). The Lean file
extends that same technique to the valuation/metric side. The contribution is the instance, not the
method.
