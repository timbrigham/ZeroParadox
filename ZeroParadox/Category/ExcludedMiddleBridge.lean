import ZeroParadox.Category.DoubleNegationNucleus
import Mathlib.Order.Heyting.Regular
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# The excluded-middle bridge: choice → excluded middle → the `Prop` nucleus is trivial

## Engineer's Take

Choice itself is a representation based on a constructed model here. My point of interest is whether in
theory we could generate the same structure as choice, and with that, start replacing it at scale.

The claims that they are the same object and simultaneously true, versus one must be true and the other
false, are point of view specific. And point of view is a selection choice.

---

`em_of_choiceFragment` (§ II) is the arrow from a choice fragment to excluded middle, composed in
§ III with § I's `Prop` nucleus and fenced by § IV's `fin3_middle_not_closed_point`. Scope, the
instance hazard, prior art and the section map: `ZeroParadox/Category/ExcludedMiddleBridge.md`.
-/

namespace ZeroParadox

/-! ## § I — The landing: excluded middle and the `Prop` nucleus

All three statements here are choice-free. The instance is pinned to `Prop.instHeytingAlgebra`
throughout; see `ZeroParadox/Category/ExcludedMiddleBridge.md` on the instance hazard. -/

/-- **Excluded middle**, as a hypothesis rather than an axiom. -/
def ExcludedMiddle : Prop := ∀ p : Prop, p ∨ ¬p

/-- Unfolding lemma: under the choice-free `Prop.instHeytingAlgebra`, the complement on `Prop` *is*
negation (`compl_iff_not`), so Heyting-regularity of `p` is literally the equality `¬¬p = p`. Recorded
explicitly because it is where the pinned instance meets ordinary logical notation. -/
theorem prop_isRegular_iff (p : Prop) :
    @Heyting.IsRegular Prop Prop.instHeytingAlgebra.toCompl p ↔ ((¬¬p) = p) := Iff.rfl

/-- **Theorem (§ I).** Excluded middle holds iff every proposition is Heyting-regular, i.e.
`¬¬p = p` for all `p`. Both directions are constructive: (→) cases on `p ∨ ¬p`; (←) `¬¬(p ∨ ¬p)` is
constructively provable, so regularity of `p ∨ ¬p` returns it.

The instance is pinned to `Prop.instHeytingAlgebra` — resolving through `Prop.instBooleanAlgebra` would
import `Classical.choice` and make the statement vacuous. -/
theorem em_iff_all_props_regular :
    ExcludedMiddle ↔ ∀ p : Prop, @Heyting.IsRegular Prop Prop.instHeytingAlgebra.toCompl p := by
  constructor
  · intro hem p
    refine (prop_isRegular_iff p).mpr ?_
    exact propext ⟨fun hnn => (hem p).elim id (fun hn => absurd hn hnn), fun hp hn => hn hp⟩
  · intro hreg p
    have hnn : ¬¬(p ∨ ¬p) := fun h => h (Or.inr fun hp => h (Or.inl hp))
    exact (prop_isRegular_iff (p ∨ ¬p)).mp (hreg (p ∨ ¬p)) ▸ hnn

/-- **Theorem (§ I), nucleus form.** Excluded middle holds iff every proposition is a *closed point* of
the double-negation nucleus on `Prop` — i.e. iff the modality `a ↦ aᶜᶜ` is the identity there. This is
`em_iff_all_props_regular` restated through `dnegNucleus_isClosed_iff`.

Note the scope: this is about the nucleus on `Prop`. § IV shows the corresponding general statement about
Heyting algebras is false. -/
theorem em_iff_dnegNucleus_trivial :
    ExcludedMiddle ↔ ∀ p : Prop, (@dnegNucleus Prop Prop.instHeytingAlgebra) p = p :=
  em_iff_all_props_regular

/-! ## § II — Diaconescu: choice implies excluded middle

Prior art: Diaconescu (1975); Goodman-Myhill (1978). Stated as a hypothesis, never an axiom. -/

/-- **A choice fragment**, in operator form: a function selecting, from every inhabited predicate on
`Bool`, an element satisfying it. This is the axiom of choice for inhabited subsets of `Bool`, a global
chooser bounded only in its codomain, and it is all `em_of_choiceFragment` consumes. Goodman-Myhill
(1978, p. 461) bound both sides, choice "for sets B, C of at most two elements".

Two things make this the faithful fragment rather than a weakened stand-in. First, the chooser is a
*function of the predicate*, so extensionally equal predicates receive equal choices — that is precisely
the leverage `em_of_choiceFragment` uses. Second, it is genuinely implied by Lean's `Classical.choice`
(`choiceFragment_of_classical` below), so the hypothesis is satisfiable.

**Faithfulness check (run 2026-07-19).** The worry worth taking seriously is the converse: if
`ExcludedMiddle → ChoiceFragment` were provable without unique choice into `Bool` (with it as a second
hypothesis it is: the `example` after `em_of_choiceFragment`), the two would be equivalent and § II would
be excluded middle implying itself in costume, not a choice principle implying it. Measured result: the natural
construction `fun S => if S true then true else false` under only `ExcludedMiddle` **fails to elaborate**
— `failed to synthesize instance of type class Decidable (S true)`. That is the `Prop`→`Bool` elimination
barrier: excluded middle supplies a disjunction in `Prop`, which cannot be eliminated to produce data,
because `Or`'s eliminator takes only `Prop`-valued motives (measured 2026-10-14 by the `#check_failure` after
this definition). The same construction closes immediately under `classical`, at footprint
`[propext, Classical.choice, Quot.sound]`. So the route from a decision to a *chooser* runs through
choice, not through excluded middle, and the fragment **appears to sit above** `ExcludedMiddle` in Lean.
**Honest limit:** a failed proof attempt is not a proof of unprovability. This is strong evidence — the
failure is at the exact structural barrier that separates the two in type theory — not a formal
independence result, which would need a metatheoretic argument outside Lean.
**And note what the barrier is and is not.** A candidate explanation, not a finding, is Lean's
`Prop`/`Type` stratification: the fragment's chooser yields data (`Bool`), and the fragment is
equivalent to `Nonempty (∀ p, Decidable p)`, while `ExcludedMiddle` is equivalent to
`∀ p, Nonempty (Decidable p)` (the `example`s after this definition), and `Or` in `Prop` does not
eliminate into data. The two differ only in whether `Nonempty` sits outside or inside `∀ p`; each
`Decidable p` has at most one element, so moving `Nonempty` outward is an instance of unique choice.
It is **not** a general fact about choice versus excluded middle — in a topos,
which always has unique choice (E. J. Dubuc and M. Szyld, *Tannaka Theory for Topos*,
arXiv:1510.01775v1, Prop. 1.24, p. 10), this very fragment is *equivalent* to excluded middle (by the
Diaconescu–Goodman–Myhill argument); in Lean the equivalence holds with unique choice into `Bool` as a
hypothesis (the `example` after `em_of_choiceFragment`).
On that candidate, the gap measured here is a property of the ambient type theory, not of the two
principles. -/
def ChoiceFragment : Prop :=
  ∃ ch : (Bool → Prop) → Bool, ∀ S : (Bool → Prop), (∃ b, S b) → S (ch S)

-- Statement: case analysis on a proof of `True ∨ False` into the motive `Bool` fails to elaborate, since
-- `Or.casesOn` accepts only motives valued in `Prop`. On `Decidable True`, which is data, the same
-- case analysis into `Bool` elaborates.
#check_failure (fun h : True ∨ False =>
  (Or.casesOn (motive := fun _ => Bool) h (fun _ => true) (fun _ => false) : Bool))
example : Decidable True → Bool := fun h =>
  Decidable.casesOn (motive := fun _ => Bool) h (fun _ => false) (fun _ => true)

-- Statement: the fragment is equivalent to the propositional truncation of data-valued decidability,
-- `Nonempty (∀ p, Decidable p)`; the chooser decides `p` on the pair of predicates
-- `em_of_choiceFragment` uses.
-- Reading: both sides are theorems of Lean's classical ambient logic, so the content is the
-- construction, not the truth of the biconditional. Credit (cited, not claimed): nLab,
-- "Diaconescu-Goodman-Myhill theorem", lists among the equivalents of excluded middle "Finite sets
-- are choice (in fact, it suffices for 2 to be choice)"; this is a reading across Lean's
-- `Prop`/`Type` split.
example : ChoiceFragment ↔ Nonempty (∀ p : Prop, Decidable p) := by
  refine ⟨fun ⟨ch, hch⟩ => ⟨fun p => ?_⟩, fun ⟨dec⟩ => ?_⟩
  · have hA := hch (fun b => b = true ∨ p) ⟨true, Or.inl rfl⟩
    have hB := hch (fun b => b = false ∨ p) ⟨false, Or.inl rfl⟩
    exact if h : ch (fun b => b = true ∨ p) = ch (fun b => b = false ∨ p) then
      isTrue (hA.elim (fun hAt => hB.elim (fun hBf => absurd (hAt ▸ hBf ▸ h) (by decide)) id) id)
    else
      isFalse fun hp => h (by
        have : (fun b => b = true ∨ p) = (fun b => b = false ∨ p) :=
          funext fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
        rw [this])
  · refine ⟨fun S => @decide (S true) (dec _), fun S hS => ?_⟩
    show S (@decide (S true) (dec _))
    generalize dec (S true) = d
    cases d with
    | isTrue h => exact h
    | isFalse hn =>
      obtain ⟨b, hb⟩ := hS
      cases b with
      | true => exact absurd hb hn
      | false => exact hb

-- Statement: excluded middle is equivalent to `∀ p, Nonempty (Decidable p)`, `Nonempty` inside.
example : ExcludedMiddle ↔ ∀ p : Prop, Nonempty (Decidable p) :=
  ⟨fun h p => (h p).elim (fun hp => ⟨isTrue hp⟩) (fun hn => ⟨isFalse hn⟩),
   fun h p => (h p).elim fun d => match d with
     | isTrue hp => Or.inl hp
     | isFalse hn => Or.inr hn⟩
-- Statement: each `Decidable p` has at most one element.
example (p : Prop) : Subsingleton (Decidable p) := inferInstance

/-- **The fragment is non-vacuous.** Lean's `Classical.choice` supplies it. Footprint is classical by
construction — that is the point: this is the *source* end of the § II arrow, and it inhabits the
hypothesis of `em_of_choiceFragment`, so that implication's hypothesis is satisfiable in Lean. -/
theorem choiceFragment_of_classical : ChoiceFragment := by
  classical
  refine ⟨fun S => if h : ∃ b, S b then h.choose else true, fun S hS => ?_⟩
  simp only [dif_pos hS]
  exact hS.choose_spec

/-- **Theorem (§ II) — Diaconescu.** The choice fragment implies excluded middle.

The argument (the two-predicate form of Lean core's `Classical.em`, `Init/Classical.lean`, which uses
`True`/`False` in `Prop` where this uses `Bool`; Goodman-Myhill 1978, p. 461 argue element-wise with
one chooser on a set of at most two elements): given `p`, form the two predicates on `Bool`
`A b := (b = true ∨ p)` and `B b := (b = false ∨ p)`. Both are inhabited, so the chooser returns
`ch A` and `ch B`. Decide `ch A = ch B` — decidable, because `Bool` has decidable equality, with no
classical input. If they differ, `p` must fail: `p` would force `A = B` (by `funext` and `propext`) and
hence `ch A = ch B`. If they agree, `p` must hold: otherwise `ch A = true` and `ch B = false`, so they
would differ. Either way `p ∨ ¬p`.

Footprint: `propext` (collapsing the two predicates when `p` holds) and `Quot.sound` (via `funext`, which
Lean derives from it). No `Classical.choice` — the choice content is entirely in the hypothesis, which is
what makes this an implication rather than a restatement. -/
theorem em_of_choiceFragment (h : ChoiceFragment) : ExcludedMiddle := by
  obtain ⟨ch, hch⟩ := h
  intro p
  let A : Bool → Prop := fun b => b = true ∨ p
  let B : Bool → Prop := fun b => b = false ∨ p
  have hA : A (ch A) := hch A ⟨true, Or.inl rfl⟩
  have hB : B (ch B) := hch B ⟨false, Or.inl rfl⟩
  -- If `p` holds, the two predicates are literally equal, so the chooser agrees on them.
  have hpAB : p → ch A = ch B := by
    intro hp
    have : A = B := funext fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    rw [this]
  -- `Bool` equality is decidable with no classical input.
  rcases Bool.decEq (ch A) (ch B) with hne | heq
  · exact Or.inr fun hp => hne (hpAB hp)
  · rcases hA with hAt | hp
    · rcases hB with hBf | hp
      · exact absurd (hAt ▸ hBf ▸ heq) (by decide)
      · exact Or.inl hp
    · exact Or.inl hp

/-- Statement: with unique choice into `Bool` as a hypothesis, the choice fragment and excluded middle
are inter-derivable; the forward leg is `em_of_choiceFragment`. -/
example (uc : ∀ P : Bool → Prop, (∃! b, P b) → {b : Bool // P b}) :
    ChoiceFragment ↔ ExcludedMiddle := by
  refine ⟨em_of_choiceFragment, fun hem => ?_⟩
  have hR : ∀ S : Bool → Prop, ∃! b, (S true ∧ b = true) ∨ (¬ S true ∧ b = false) := by
    intro S
    rcases hem (S true) with h | h
    · exact ⟨true, Or.inl ⟨h, rfl⟩, fun y hy => hy.elim And.right (fun hn => absurd h hn.1)⟩
    · exact ⟨false, Or.inr ⟨h, rfl⟩, fun y hy => hy.elim (fun hs => absurd hs.1 h) And.right⟩
  refine ⟨fun S => (uc _ (hR S)).1, fun S hS => ?_⟩
  show S (uc _ (hR S)).1
  rcases (uc _ (hR S)).2 with ⟨hs, he⟩ | ⟨hn, he⟩
  · rw [he]; exact hs
  · rw [he]
    obtain ⟨b, hb⟩ := hS
    cases b with
    | true => exact absurd hb hn
    | false => exact hb
-- Reading (cited, not claimed): the Rocq standard library's `theories/Logic/ChoiceFacts.v` proves the
-- type-theoretic form, `constructive_definite_descr_excluded_middle` (definite description, that is
-- unique choice, with excluded middle gives `forall P:Prop, {P} + {~ P}`), and states that
-- "constructive definite description transports excluded-middle from [Prop] to [Set]", crediting the
-- idea of its proof to L. Chicli, L. Pottier and C. Simpson, "Mathematical Quotients and Quotient
-- Types in Coq", TYPES 2002, LNCS 2646. Read in the authors' preprint (preprint page numbers): § 5,
-- pp. 12-13, shows the axiom of unique choice with values in `Prop` contradicts excluded middle in
-- `Prop` in Coq, completing the proof with the § 4.2 argument, pp. 10-11 (the goal is `False`, so the
-- existence of a map `Prop → bool` can be eliminated to give `{P} + {~P}`); their § 6, p. 13, says the
-- impredicativity of `Set` is essential to that proof. As in `ChoiceFacts.v`, the
-- credit is for that proof idea, not for the transport result. This example, with the one after
-- `ChoiceFragment`, is the `Bool`-chooser instance of that transport.

/-! ## § III — Composition -/

/-- **Corollary (§ III).** The choice fragment implies every proposition is Heyting-regular. -/
theorem choiceFragment_all_props_regular (h : ChoiceFragment) :
    ∀ p : Prop, @Heyting.IsRegular Prop Prop.instHeytingAlgebra.toCompl p :=
  em_iff_all_props_regular.mp (em_of_choiceFragment h)

/-- **Corollary (§ III).** The choice fragment implies every proposition is a closed point of the
double-negation nucleus on `Prop`: choice → excluded middle → the `Prop` nucleus is the identity.

Scope, again: `Prop`, not Heyting algebras in general. § IV is the fence. -/
theorem choiceFragment_dnegNucleus_trivial (h : ChoiceFragment) :
    ∀ p : Prop, (@dnegNucleus Prop Prop.instHeytingAlgebra) p = p :=
  em_iff_dnegNucleus_trivial.mp (em_of_choiceFragment h)

/-! ## § IV — The fence: excluded middle does NOT make Heyting algebras Boolean

Everything in this section is stated inside Mathlib's classical metatheory, where excluded middle is
freely available. It is therefore expected — and honest — that these results carry classical axioms. That
is exactly what makes the fence meaningful: even *with* excluded middle in hand, the double-negation
nucleus on a general Heyting algebra is not the identity.

The witness is the three-element chain `Fin 3`, made a Heyting algebra by
`LinearOrder.toBiheytingAlgebra`, whose complement is `compl a = if a = ⊥ then ⊤ else ⊥`. The middle
element `1` then has `1ᶜ = ⊥ = 0` and `1ᶜᶜ = ⊤ = 2 ≠ 1`. -/

-- The bi-Heyting structure on `Fin 3` is Mathlib's own: `Fin.instBiheytingAlgebra [NeZero n]`
-- (`Mathlib/Order/Fin/Basic.lean`), itself built from `LinearOrder.toBiheytingAlgebra`. This file
-- imports it, so `ᶜ` and `dnegNucleus` resolve on `Fin 3` with nothing declared here.
-- An earlier draft declared a local instance and described Mathlib as providing this "only as a
-- reducible non-instance" — false by implicature, and a latent instance diamond. Removed 2026-07-19.

/-- **Theorem (§ IV) — the fence.** The middle element of the three-element chain is **not** regular:
`1ᶜᶜ = 2 ≠ 1`. So `Fin 3` is a Heyting algebra that is not Boolean, exhibited in a metatheory with
excluded middle available.

Consequence: § I is a statement about `Prop` specifically. The claim "excluded middle makes every Heyting
algebra Boolean" is false, and this decides a counterexample to it. -/
theorem fin3_middle_not_regular :
    ¬ @Heyting.IsRegular (Fin 3) _ (1 : Fin 3) := by decide

/-- **Theorem (§ IV), nucleus form.** The middle element of the three-element chain is not a closed
point of the double-negation nucleus. The nucleus is genuinely nontrivial on a general Heyting algebra
even in a classical metatheory — the exact statement § I is *not* making. -/
theorem fin3_middle_not_closed_point :
    (dnegNucleus (Fin 3)) (1 : Fin 3) ≠ (1 : Fin 3) :=
  fun h => fin3_middle_not_regular ((dnegNucleus_isClosed_iff (1 : Fin 3)).mp h)

end ZeroParadox

/-! ## Axiom Purity Check

The two `Prop` instances are measured first — this is the instance-hazard measurement referred to in
`ZeroParadox/Category/ExcludedMiddleBridge.md`. `Prop.instBooleanAlgebra` discharges `top_le_sup_compl` with `Classical.em`, so it carries
`Classical.choice`; `Prop.instHeytingAlgebra` does not. Every `Prop`-scoped statement in §§ I-III pins the
Heyting instance explicitly for that reason.

§ IV is expected to be classical and is not a purity claim; see the section header. -/

section PurityCheck
open ZeroParadox

-- The instance-hazard measurement.
#print axioms Prop.instHeytingAlgebra
#print axioms Prop.instBooleanAlgebra

-- § I — must be choice-free.
#print axioms ExcludedMiddle
#print axioms prop_isRegular_iff
#print axioms em_iff_all_props_regular
#print axioms em_iff_dnegNucleus_trivial

-- § II — `em_of_choiceFragment` must be choice-free (the choice content is the hypothesis).
-- `choiceFragment_of_classical` is classical by construction: it is the source end of the arrow.
#print axioms ChoiceFragment
#print axioms choiceFragment_of_classical
#print axioms em_of_choiceFragment

-- § III.
#print axioms choiceFragment_all_props_regular
#print axioms choiceFragment_dnegNucleus_trivial

-- § IV — classical by design; the fence is stated in the classical metatheory.
#print axioms fin3_middle_not_regular
#print axioms fin3_middle_not_closed_point

end PurityCheck
