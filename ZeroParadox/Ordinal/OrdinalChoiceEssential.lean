import Mathlib.Order.InitialSeg
import Mathlib.SetTheory.Ordinal.Basic
import ZeroParadox.Category.ExcludedMiddleBridge

/-!
# Comparability of well-orders is a constructive taboo

## Engineer's Take

We have all kinds of concrete instances of where choice is needed, just not in the core of T-SNAP.
So why is this one different.

It is different because we have instances where choice is used, not where it is needed. A footprint
tells you how a proof was written, never whether the theorem requires it. Nearly everything we have
examined is a leaf that inherits choice from upstream, and the question is not well posed until it is
traced. This is the first one we followed all the way down to a root.

Enumerating the roots rather than sampling the leaves is the next step after we finish with the
ordinals.

---

`em_of_wellOrder_comparable`: comparability of arbitrary well-orders implies excluded middle, proved
with no `Classical.choice`. The result, the prior art, the fences and the section map are in
`ZeroParadox/Ordinal/OrdinalChoiceEssential.md`, beside this file.
-/

namespace ZeroParadox

open scoped InitialSeg

/-! ## § I — The witnesses

Two well-orders. `Pt` is a single point, unconditionally. `Two p` has two elements when `p` holds
and none when it fails. Every instance below is discharged constructively — `Bool` case analysis
and proof irrelevance only — which is what lets § II come out choice-free. In particular
`Sum.Lex`'s well-order instance is *not* used: it is classical, and routing through it silently
reintroduces `Classical.choice`. -/

/-- A one-point well-order. -/
abbrev Pt : Type := PUnit

instance : Std.Trichotomous (@emptyRelation Pt) := ⟨fun a b _ _ => Subsingleton.elim a b⟩
instance : IsTrans Pt emptyRelation := ⟨fun _ _ _ h => h.elim⟩
instance : IsWellFounded Pt emptyRelation := ⟨⟨fun a => ⟨a, fun _ h => h.elim⟩⟩⟩
instance : IsWellOrder Pt emptyRelation where

/-- The Kraus-Nordvall Forsberg-Xu witness: a carrier with **two** elements when `p` holds and
**none** when it fails. `PLift p` contributes the inhabitation, `Bool` the two points. -/
def Two (p : Prop) : Type := PLift p × Bool

/-- The two points are ordered `false < true`. -/
def twoRel (p : Prop) : Two p → Two p → Prop := fun a b => a.2 = false ∧ b.2 = true

instance (p : Prop) : Std.Trichotomous (twoRel p) := by
  refine ⟨fun a b hab hba => ?_⟩
  obtain ⟨⟨_⟩, ba⟩ := a
  obtain ⟨⟨_⟩, bb⟩ := b
  cases ba <;> cases bb
  · rfl
  · exact absurd ⟨rfl, rfl⟩ hab
  · exact absurd ⟨rfl, rfl⟩ hba
  · rfl

instance (p : Prop) : IsTrans (Two p) (twoRel p) :=
  ⟨fun _ _ _ h1 h2 => absurd (h1.2.symm.trans h2.1) (by simp)⟩

instance (p : Prop) : IsWellFounded (Two p) (twoRel p) := by
  refine ⟨⟨fun a => ?_⟩⟩
  have base : ∀ c : Two p, c.2 = false → Acc (twoRel p) c :=
    fun c hc => ⟨c, fun d hd => absurd (hd.2.symm.trans hc) (by simp)⟩
  exact ⟨a, fun d hd => base d hd.1⟩

instance (p : Prop) : IsWellOrder (Two p) (twoRel p) where

/-! ## § II — The taboo

Both directions of the comparison are informative. That is the whole trick, and it is why the
witness is empty-or-*two* rather than empty-or-one: against a one-point order, `Two p ≼i Pt`
forces `p` to fail (two distinct points cannot inject into one) and `Pt ≼i Two p` forces `p` to
hold (the embedding hands back an element). Neither branch is vacuously available, so a
disjunction of the two decides `p`. -/

/-- An initial-segment embedding `Pt ≼i Two p` yields `p`: the embedding produces an element of
`Two p`, whose first component carries `p`. -/
theorem p_of_pt_le (p : Prop) (h : Nonempty (@emptyRelation Pt ≼i twoRel p)) : p := by
  obtain ⟨f⟩ := h
  exact (f PUnit.unit).1.down

/-- An initial-segment embedding `Two p ≼i Pt` yields `¬p`: were `p` to hold, the two distinct
points of `Two p` would be forced onto the single point of `Pt`, contradicting injectivity of the
underlying embedding. -/
theorem not_p_of_le_pt (p : Prop) (h : Nonempty (twoRel p ≼i @emptyRelation Pt)) : ¬p := by
  obtain ⟨f⟩ := h
  intro hp
  have : ((⟨hp⟩, false) : Two p) = (⟨hp⟩, true) :=
    f.toRelEmbedding.injective (Subsingleton.elim _ _)
  exact Bool.noConfusion (congrArg Prod.snd this)

/-- **Comparability of well-orders implies excluded middle.**

Prior art: Kraus-Nordvall Forsberg-Xu, arXiv:2104.02549, Theorem 38(d) (there in the data form
`⊎`, as a paper proof — their Agda development does not cover it). This is that theorem, with
their witnesses, for the propositional
(`∨`) form of comparability — which is the form Mathlib's `le_total` on `Ordinal` has.

Choice-free: the classical content is entirely in the hypothesis, which is what makes this an
implication rather than a restatement. `ExcludedMiddle` is
`ZeroParadox/Category/ExcludedMiddleBridge.lean`'s. -/
theorem em_of_wellOrder_comparable
    (H : ∀ (α β : Type) (r : α → α → Prop) (s : β → β → Prop)
      [IsWellOrder α r] [IsWellOrder β s], Nonempty (r ≼i s) ∨ Nonempty (s ≼i r)) :
    ExcludedMiddle := by
  intro p
  rcases H (Two p) Pt (twoRel p) emptyRelation with h | h
  · exact Or.inr (not_p_of_le_pt p h)
  · exact Or.inl (p_of_pt_le p h)

/-- **The hypothesis is not vacuous.** Mathlib's `InitialSeg.total` supplies it, so
`em_of_wellOrder_comparable` cannot be dismissed as an implication with an unsatisfiable
antecedent. Classical by construction — that is the point: this is the source end of the arrow.

`InitialSeg.total` (`Mathlib/Order/InitialSeg.lean`) is the **data** form, and spends a literal
`Classical.choice` application in its final branch. -/
theorem comparable_of_classical :
    ∀ (α β : Type) (r : α → α → Prop) (s : β → β → Prop)
      [IsWellOrder α r] [IsWellOrder β s], Nonempty (r ≼i s) ∨ Nonempty (s ≼i r) := by
  intro α β r s _ _
  rcases InitialSeg.total r s with f | f
  · exact Or.inl ⟨f⟩
  · exact Or.inr ⟨f⟩

/-! ## § III — Why this is stated about `InitialSeg` and not about `Ordinal`

The taboo above deliberately never mentions `Ordinal`'s `≤`. It cannot: **`Classical.choice` sits
in the `Ordinal.partialOrder` instance term itself**, so every statement mentioning that order
inherits it no matter how the statement is proved. `order_footprint_le` / `order_footprint_eq` below are the
demonstration — `a ≤ a`, proved by `le_refl`, carries `Classical.choice`, while `a = a` does not.

Traced to source, three independent classical entry points feed that instance:

* `InitialSeg.eq_or_principal` (`Mathlib/Order/InitialSeg.lean`) — "an initial segment is
  surjective or principal," proved by `or_iff_not_imp_right` plus `push Not`. This is the deepest
  root; it feeds `InitialSeg.toPrincipalSeg` (via `Classical.choose_spec`) and
  `InitialSeg.principalSumRelIso` (via `open Classical in if h : Surjective f`), and thence both
  the `lt_iff_le_not_ge` and `le_antisymm` fields of `Ordinal.partialOrder`.
* `InitialSeg.total` — a literal `Classical.choice` application, feeding `le_total`.
* `Ordinal.instLinearOrder`'s own `toDecidableLE := Classical.decRel _` — a data field, classical
  by fiat.

**Consequence for the framework's ledger.** The recorded `[propext, Classical.choice, Quot.sound]`
readings on `epsilon0_ne_zero`, `epsilon0_ne_bot`, `epsilon0_eq_nfp_bot` and their kin are
measuring the ambient instance, not those proofs. They are **not evidence** that the ε₀
mathematics is non-constructive, in either direction. `epsilon0_ne_zero` is the clearest case: its
own argument is `ω^0 = 1 ≠ 0`, entirely constructive, and its whole footprint is inherited from
the ε₀ term. Re-proving these choice-free *inside* Mathlib's `Ordinal` is not merely hard, it is
structurally impossible; a choice-free analogue has to be built on a notation carrier, which is
ZP-N's programme. -/

/-! **The measurement is uninformative for `Ordinal`'s order.** The next two theorems are the
demonstration, and they are deliberately stated **separately** rather than as one conjunction: a
conjunction reports the *union* of its halves' axioms, so it could only assert the contrast in prose,
never print it. Split, the purity block below exhibits it — the same statement about the same element,
differing only in whether it mentions the `Ordinal.partialOrder` instance term. Both proofs are
immediate; the difference is not in the proofs. -/

/-- Reflexivity of `≤` on `Ordinal`. Mentions the order instance, and therefore carries
`Classical.choice` however it is proved. Compare `order_footprint_eq`. -/
theorem order_footprint_le (a : Ordinal) : a ≤ a := le_refl a

/-- Reflexivity of `=` on `Ordinal`. The same element, no order instance, no choice.
Compare `order_footprint_le`. -/
theorem order_footprint_eq (a : Ordinal) : a = a := rfl

end ZeroParadox

/-! ## Axiom Purity Check

§ I-II must be choice-free: the classical content is the hypothesis, not the proof.
`comparable_of_classical` is classical by construction (the source end of the arrow), and is expected
to carry `Classical.choice` — that is not a purity claim. `order_footprint_le` and
`order_footprint_eq` are the § III demonstration: read them as a **pair**, since the contrast between
the two lines is the result. -/

section PurityCheck
open ZeroParadox

-- § II — must be choice-free.
#print axioms p_of_pt_le
#print axioms not_p_of_le_pt
#print axioms em_of_wellOrder_comparable

-- Classical by design.
#print axioms comparable_of_classical

-- § III, the contrast. Same element; only the second mentions the order instance.
#print axioms order_footprint_eq
#print axioms order_footprint_le

-- The § III trace, measured rather than asserted.
-- FIRST: the type itself, which carries NO choice. This one line is the load-bearing measurement
-- behind the whole correction of record — ZP-N v1.0 asserted the opposite ("choice-saturated") and
-- built a conclusion on it. Printed here so a reader can reproduce it rather than take it on trust.
#print axioms Ordinal
#print axioms Ordinal.partialOrder
#print axioms Ordinal.instLinearOrder
#print axioms InitialSeg.eq_or_principal
#print axioms InitialSeg.total

-- Two of the operations built on that instance. `nfp`, `deriv` and `epsilon` are named alongside
-- these in ZP-N's prose but live in `Mathlib.SetTheory.Ordinal.FixedPoint` / `Veblen`, outside this
-- file's deliberately minimal import closure; they are printed in
-- `ZeroParadox/Ordinal/PricedInterface.lean`, which already imports Veblen. Between the two purity
-- blocks all five are measured rather than asserted — the discipline whose absence is ZP-N v1.0's
-- correction of record.
#print axioms Ordinal.typein
#print axioms Ordinal.omega0

end PurityCheck
