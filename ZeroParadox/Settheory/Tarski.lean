import ZeroParadox.Settheory.Wall
import ZeroParadox.Category.Lawvere
import Mathlib.Tactic

/-!
# Tarski's undefinability of truth — the diagonal family's TRUTH face (probe)

## Engineer's Take

Back to basics. We're filling in everything that's left where the relationship between one over
infinity and a bottom element still wasn't fully defined, using the same structure that we have for
everything else in the family.

---

## Overview (AI-assisted)

Tarski (1936): no consistent *internal* truth predicate. This file names Tarski as a member of the
diagonal family whose engine is `Wall.lean` (`negation_no_fixedpoint`, `lawvere_fixedpoint`,
`cantor_via_engine`). Tarski is the **TRUTH face**, the exact dual of Gödel's **PROVABILITY face**: both
diagonalize, but truth is undefinable (the T-schema at the liar is inconsistent) where provability is
merely incomplete.

Placement on the wall: Tarski sits on the **μ / wall branch** — *negation has no fixed point*
(`negation_no_fixedpoint`), so the liar `p ↔ ¬p` has no truth value. It is the exact negation of the
**ν / Quine floor** (⊥ = {⊥}, where self-reference *does* close): the liar is where self-reference
*cannot* close. So Tarski is the wall-face and the Quine atom is the floor-face of the one diagonal.

Honest delta: the engine is Lawvere/Yanofsky (cited in `Wall.lean`) and already in the repo; Cantor /
Russell / Turing are already named there. The new content here is (a) exhibiting the **liar sentence
explicitly** from a truth-naming and (b) the **T-schema** absurdity — Tarski named and placed, completing
the diagonal-family roster on the truth axis. Every theorem reduces to the `Wall.lean` engine; no new
axiomatic content.

## Structure
- § I.   The liar has no truth value (the engine, re-pointed as the liar).
- § II.  A surjective internal truth-naming produces the liar sentence (the explicit diagonal).
- § III. Tarski: no internal universal truth-naming (the undefinability, off § II).
- § IV.  The T-schema at the liar is absurd (the T-schema face).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ## § I. The liar has no truth value -/

/-- **The liar has no truth value.** No proposition satisfies `p ↔ ¬p`. This is the engine
    (`negation_no_fixedpoint`) re-pointed: the liar sentence "this sentence is false" is exactly the
    fixed-point-free map (negation) with no fixed point — the μ/wall branch. -/
theorem liar_no_truth_value (p : Prop) : ¬ (p ↔ ¬ p) :=
  negation_no_fixedpoint p

/-! ## § II. A surjective internal truth-naming produces the liar sentence -/

/-- **The liar sentence, exhibited.** If a "truth-naming" `truth : A → (A → Prop)` is point-surjective
    (every predicate on sentences is named by a sentence — the internal universality of truth), then the
    liar sentence `L` exists and satisfies `truth L L ↔ ¬ truth L L`. This is the explicit diagonal
    (Gödel-numbering) step: `L` names the predicate "the sentence at hand is not true of itself." -/
theorem tarski_liar_from_naming {A : Type*} (truth : A → (A → Prop))
    (hsurj : Function.Surjective truth) : ∃ L, truth L L ↔ ¬ truth L L := by
  obtain ⟨L, hL⟩ := hsurj (fun a => ¬ truth a a)
  exact ⟨L, iff_of_eq (congrFun hL L)⟩

/-! ## § III. Tarski's undefinability -/

/-- **Tarski's undefinability of truth.** No internal universal truth-naming exists: `truth`
    cannot be point-surjective, because the liar sentence it would produce (§ II) has no truth value
    (§ I). Semantically: truth is not definable inside a system that can name all its own predicates.
    (This is `cantor_via_engine` read on the truth axis; proved here directly off § I + § II for the
    liar reading.) -/
theorem tarski_no_internal_truth {A : Type*} (truth : A → (A → Prop)) :
    ¬ Function.Surjective truth := by
  intro hsurj
  obtain ⟨L, hL⟩ := tarski_liar_from_naming truth hsurj
  exact liar_no_truth_value (truth L L) hL

/-! ## § IV. The T-schema at the liar is absurd -/

/-- **The T-schema at the liar is inconsistent.** A truth predicate `Tr` obeying its own T-schema at the
    liar sentence — `Tr liar ↔ ¬ Tr liar` — is absurd. This is Tarski's theorem in T-schema form: no
    predicate can satisfy `Tr(⌜φ⌝) ↔ φ` for the liar `φ = ¬Tr(⌜φ⌝)`. The floor dual: replace `¬` by the
    self-closing map and you get the Quine atom instead of the wall. -/
theorem tarski_Tschema_liar_absurd {A : Type*} (Tr : A → Prop) (liar : A)
    (hTschema : Tr liar ↔ ¬ Tr liar) : False :=
  liar_no_truth_value (Tr liar) hTschema

/-! ## § V. The bottom-element relationship — the wall (μ): no truth bottom -/

/-- **Tarski on the family's μ/ν fork: the truth diagonal has NO bottom element.** There is no Lawvere
    witness on `Prop` — no internal universal predicate-naming — because negation is fixed-point-free
    (`negation_no_fixedpoint`), the same wall (`no_witness_of_fixedPointFree`) that refutes
    Cantor/Russell. So on the one-over-infinity-to-bottom map, the truth face is where self-reference
    finds no floor: the μ/wall side, a bottom that does not close, stated with the same
    `HasLawvereWitness` structure the rest of the family uses. -/
theorem tarski_no_truth_bottom : ¬ HasLawvereWitness Prop :=
  no_witness_of_fixedPointFree Not (fun p h => negation_no_fixedpoint p (iff_of_eq h).symm)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms liar_no_truth_value
#print axioms tarski_liar_from_naming
#print axioms tarski_no_internal_truth
#print axioms tarski_Tschema_liar_absurd
#print axioms tarski_no_truth_bottom
end PurityCheck
