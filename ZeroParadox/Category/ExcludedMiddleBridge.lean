import ZeroParadox.Category.DoubleNegationNucleus
import Mathlib.Order.Heyting.Regular
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# The excluded-middle bridge: choice → excluded middle → the `Prop` nucleus is trivial

`Category/DoubleNegationNucleus.lean` builds `dnegNucleus X : Nucleus X`, the map `a ↦ aᶜᶜ` on any
Heyting algebra, choice-free (`[propext]`), whose closed points are the regular elements
(`dnegNucleus_isClosed_iff`). It is the **excluded-middle** modality, not the choice modality.

This file builds the arrow that separates those two, in three steps and a fence.

**The scope constraint — read this before reading any statement below.** Excluded middle does **not**
make an arbitrary Heyting algebra Boolean. It makes the **`Prop`** Heyting algebra Boolean. Every
statement in §§ I-III is therefore scoped to `Prop`, and § IV machine-checks that the general claim
fails: a concrete Heyting algebra, exhibited inside Mathlib's classical metatheory (so with excluded
middle fully available), carrying an element with `aᶜᶜ ≠ a`. The nucleus stays nontrivial there. The
general statement "excluded middle collapses the double-negation nucleus" is FALSE and is not asserted
anywhere in this file.

**Correction of record.** This file was first drafted in exactly that general (wrong) form — "choice →
excluded middle → the double-negation nucleus is trivial", unscoped — and the `Prop`-vs-arbitrary-Heyting
distinction was caught before it was built. § IV exists because of that near-miss, which is why the fence
is the load-bearing part of the file rather than a footnote. Recorded rather than quietly avoided.

**The instance hazard, and how it is handled.** `Prop` carries two relevant instances:
`Prop.instHeytingAlgebra` (Mathlib/Order/Heyting/Basic.lean) and `Prop.instBooleanAlgebra`
(Mathlib/Order/BooleanAlgebra/Defs.lean). The Boolean one discharges its `top_le_sup_compl` field with
`Classical.em`, so **it carries `Classical.choice` in its own term**. If `dnegNucleus Prop` or
`Heyting.IsRegular (p : Prop)` were allowed to resolve through the Boolean instance, every theorem here
would silently pick up choice and the whole point — that the choice → excluded middle arrow is a real
implication and not an identity — would be lost. Every `Prop`-scoped statement below therefore **pins the
instance explicitly** as `@… Prop Prop.instHeytingAlgebra`. The measured footprints of both instances are
recorded in the purity-check section at the bottom.

**Prior art — the framework claims only the packaging.** § II is Diaconescu's theorem (Diaconescu 1975,
"Axiom of choice and complementation"; independently Goodman-Myhill 1978, "Choice implies excluded
middle"). It is not a new result and is not claimed as one. A search of Mathlib and the other `.lake`
dependencies found **no** hypothesis-form statement of it (no `Diaconescu`, no `em_of_choice`); Lean's own
kernel realizes the arrow concretely — `Classical.em` is *derived* from `Classical.choice` by exactly
Diaconescu's argument — but as a derivation of the classical axioms, not as a reusable theorem taking the
choice principle as a hypothesis. This file supplies that hypothesis form so the arrow can be composed
with § I. § I and § IV are elementary and equally not new; the contribution is the assembly.

**A correction to how this file first stated its prior art (2026-07-19).** It originally said Diaconescu
proved "choice ⇒ excluded middle, one direction only, converse fails." That is wrong twice over. First,
Diaconescu's theorem is an **equivalence** — a coequalizer of two nonintersecting monomorphisms has a
section *iff* subobjects have complements (1975, p. 176), the choice direction being his corollary
(p. 178); in modern terms, choice for inhabited subobjects of a two-element object **is** excluded middle.
Second, that *full* AC is strictly stronger than excluded middle is **Cohen 1963** / Fraenkel–Mostowski
independence, not Diaconescu.
**This matters here because `ChoiceFragment` has exactly Diaconescu's restricted shape** — choice for
inhabited predicates on `Bool` — so in a topos it would be equivalent to `ExcludedMiddle`, and the
faithfulness check below would have to fail. It does not fail. The reason is that Lean stratifies `Prop`
and `Type`: `ChoiceFragment` selects into `Bool`, making it data-valued excluded middle
(`∀ p, Decidable p`), while `ExcludedMiddle` is the `Prop`-valued form, and `Or` in `Prop` does not
eliminate into `Bool`. A topos has no such split. **So the one-way-ness measured below is a fact about
Lean's stratification, and is this file's own small finding — not, as first written, a restatement of
Diaconescu.**

**No new axioms.** The choice principle in § II is a `def ... : Prop` hypothesis, discharged by the caller.
Nothing here is declared `axiom`, and nothing here uses `sorry`.

## Engineer's Take

Choice itself is a representation based on a constructed model here. My point of interest is whether in
theory we could generate the same structure as choice, and with that, start replacing it at scale.

The claims that they are the same object and simultaneously true, versus one must be true and the other
false, are point of view specific. And point of view is a selection choice.

---

## Structure

- § I   Excluded middle ↔ every `Prop` is regular ↔ the `Prop` double-negation nucleus is the identity
- § II  Diaconescu: a choice fragment (as a hypothesis) implies excluded middle
- § III Composition: the choice fragment collapses the `Prop` nucleus
- § IV  The fence: a concrete Heyting algebra that is NOT Boolean, in the classical metatheory
-/

namespace ZeroParadox

/-! ## § I — The landing: excluded middle and the `Prop` nucleus

All three statements here are choice-free. The instance is pinned to `Prop.instHeytingAlgebra`
throughout; see the file header on the instance hazard. -/

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
`Bool`, an element satisfying it. This is the axiom of choice restricted to `Bool`-indexed subsets, which
is all Diaconescu's argument consumes.

Two things make this the faithful fragment rather than a weakened stand-in. First, the chooser is a
*function of the predicate*, so extensionally equal predicates receive equal choices — that is precisely
the leverage Diaconescu's argument uses. Second, it is genuinely implied by Lean's `Classical.choice`
(`choiceFragment_of_classical` below), so the hypothesis is not vacuous.

**Faithfulness check (run 2026-07-19).** The worry worth taking seriously is the converse: if
`ExcludedMiddle → ChoiceFragment` were provable, the two would be equivalent and § II would be excluded
middle implying itself in costume, not a choice principle implying it. Measured result: the natural
construction `fun S => if S true then true else false` under only `ExcludedMiddle` **fails to elaborate**
— `failed to synthesize instance of type class Decidable (S true)`. That is the `Prop`→`Bool` elimination
barrier: excluded middle supplies a disjunction in `Prop`, which cannot be eliminated to produce data.
The same construction closes immediately under `classical`, at footprint
`[propext, Classical.choice, Quot.sound]`. So the route from a decision to a *chooser* runs through
choice, not through excluded middle, and the fragment **appears to sit above** `ExcludedMiddle` in Lean.
**Honest limit:** a failed proof attempt is not a proof of unprovability. This is strong evidence — the
failure is at the exact structural barrier that separates the two in type theory — not a formal
independence result, which would need a metatheoretic argument outside Lean.
**And note what the barrier is and is not.** It is Lean's `Prop`/`Type` stratification: the fragment
yields data (`Bool`), so it is really `∀ p, Decidable p`, while `ExcludedMiddle` is `Prop`-valued and does
not eliminate into data. It is **not** a general fact about choice versus excluded middle — in a topos,
where no such split exists, Diaconescu's theorem makes this very fragment *equivalent* to excluded middle.
The gap measured here is a property of the ambient type theory, not of the two principles. -/
def ChoiceFragment : Prop :=
  ∃ ch : (Bool → Prop) → Bool, ∀ S : (Bool → Prop), (∃ b, S b) → S (ch S)

/-- **The fragment is non-vacuous.** Lean's `Classical.choice` supplies it. Footprint is classical by
construction — that is the point: this is the *source* end of the § II arrow, recorded so that
`em_of_choiceFragment` cannot be dismissed as an implication with an unsatisfiable hypothesis. -/
theorem choiceFragment_of_classical : ChoiceFragment := by
  classical
  refine ⟨fun S => if h : ∃ b, S b then h.choose else true, fun S hS => ?_⟩
  simp only [dif_pos hS]
  exact hS.choose_spec

/-- **Theorem (§ II) — Diaconescu.** The choice fragment implies excluded middle.

The argument (Diaconescu 1975): given `p`, form the two predicates on `Bool`
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
-- (`Mathlib/Order/Fin/Basic.lean:70`), itself built from `LinearOrder.toBiheytingAlgebra`. This file
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

The two `Prop` instances are measured first — this is the instance-hazard measurement referred to in the
file header. `Prop.instBooleanAlgebra` discharges `top_le_sup_compl` with `Classical.em`, so it carries
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
