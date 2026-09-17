import ZeroParadox.Computability.Kleene
import ZeroParadox.Category.ExcludedMiddleBridge
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Data.Part
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Registering the point at infinity: `Option` versus `Part`

## Engineer's Take

A ledger saying these are the only things doing XYZ doesn't make sense. The only thing you can say is
that these are the things that have properly registered with me. That's turning a negation into a
positive.

This aligns really damn well with the Paradox itself. It turns an infinite value into a finite one, by
flipping the sign.

Bottom equals infinity is an operator, I think.

---

## Formal Overview (AI-assisted)

`OnePoint α = Option α` registers infinity as a CONSTRUCTOR, so its discriminator is data; `Part α`
holds an arbitrary `Prop` in `Dom`. First half of `PoleChartSelection` § III option (a).
-/

namespace ZeroParadox

open OnePoint

/-! ### § I — The registered pole: infinity as a constructor -/

-- Statement: `OnePoint α` is `Option α`, definitionally.
example (α : Type) : OnePoint α = Option α := rfl
-- Statement: and the point at infinity is `none`.
example (α : Type) : (∞ : OnePoint α) = (Option.none : Option α) := rfl

/-- `Statement:` `Option.isNone` separates the two ends.
    `Reading:` they are distinct because something computable tells them apart — the reading
    `infty_ne_floorG` carries, restated on the underlying type. -/
theorem registered_ends_separated {α : Type*} (a : α) :
    Option.isNone (Option.none : Option α) ≠ Option.isNone (Option.some a) := by
  simp

/-- `Statement:` a decision procedure for "am I at infinity?", uniform in `α`, no `DecidableEq α`.
    `Reading:` DATA, not a proposition — the contrast § II cannot have.
    ⚠ A `def`, not an `instance`: nothing here needs instance search changed. -/
def registeredDecider {α : Type*} (x : Option α) : Decidable (x = Option.none) :=
  match x with
  | Option.none => isTrue rfl
  | Option.some _ => isFalse (by simp)

/-- `Statement:` the separator, as an existence claim, for comparison with § II's shape. -/
theorem registered_discriminator_exists {α : Type*} :
    ∃ d : Option α → Bool, ∀ x : Option α, d x = true ↔ x ≠ Option.none :=
  ⟨fun x => x.isSome, fun x => by cases x <;> simp⟩

/-! ### § II — The unregistered pole: infinity as a `Prop` -/

/-- `Statement:` a uniform `Bool` test, correct about `Dom`, on `Part Unit`.
    ⚠ At `Unit` deliberately: a weaker hypothesis, hence a stronger theorem below. -/
def PoleDiscriminator : Prop :=
  ∃ d : Part Unit → Bool, ∀ x : Part Unit, d x = true ↔ x.Dom

/-- `Statement:` the domain of `Part.mk p f` is `p` itself. -/
theorem dom_mk (p : Prop) (f : p → Unit) : (Part.mk p f).Dom = p := rfl

/-- `Statement:` a uniform discriminator at the unregistered pole yields excluded middle.
    `Reading:` nothing is stipulated. `PoleChartSelection.em_of_uniformChartSelection` needs
    Diaconescu and an ASSUMED undecided predicate; `Part` supplies the arbitrary proposition as a
    structure field, so the proof just reads the `Bool` off.
    ⚠ The conclusion is `Prop`-valued, NOT `∀ p, Decidable p`: `Prop`/`Type` stratification forbids
    extracting data from the `∃`. See `Category/ExcludedMiddleBridge.lean` § II. -/
theorem em_of_poleDiscriminator (h : PoleDiscriminator) : ExcludedMiddle := by
  obtain ⟨d, hd⟩ := h
  intro p
  by_cases hb : d (Part.mk p (fun _ => ())) = true
  · exact Or.inl ((hd _).mp hb)
  · exact Or.inr (fun hp => hb ((hd _).mpr hp))

/-- `Statement:` classically a discriminator exists.
    `Reading:` the source end of § II's arrow, so the antecedent is not unsatisfiable. -/
theorem poleDiscriminator_of_classical : PoleDiscriminator := by
  classical
  exact ⟨fun x => decide x.Dom, fun x => by simp⟩

/-! ### § III — No COMPUTABLE discriminator at ZP-K's floor -/

-- Statement: the framework's evaluation lands in `Part`, the unregistered pole.
example (c : Nat.Partrec.Code) : Part ℕ := Nat.Partrec.Code.eval c (Encodable.encode c)

/-- `Statement:` no computable `Bool` test decides whether self-application is defined.
    `Reading:` `self_halting_undecidable` as a fact about REGISTRATION — the consequence at this
    site, not a second copy. What § II costs constructively, this floor cannot buy at all. -/
theorem no_computable_registration_at_kleene_floor :
    ¬ ∃ d : Nat.Partrec.Code → Bool, Computable d ∧
        ∀ c, d c = true ↔ (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom := by
  rintro ⟨d, hdc, hd⟩
  apply self_halting_undecidable
  have hpred : (fun c => (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom)
      = (fun c => d c = true) := funext (fun c => propext (hd c).symm)
  rw [hpred]
  exact ⟨fun c => inferInstance, by simpa using hdc⟩

/-! ### § IV — The conversion carries the instance (CITED, do not rebuild) -/

section Cited

-- Statement: `Option α → Part α`, total, no instance.
#check @Part.ofOption
-- Statement: `Part α → Option α`, and it takes `[Decidable o.Dom]`.
#check @Part.toOption
-- Statement: the equivalence of the two, and it is `noncomputable`.
#check @Part.equivOption

-- Reading: the asymmetry, elaborated — this direction needs nothing, the other cannot be written.
example (α : Type) : Option α → Part α := Part.ofOption

end Cited

/-! ### § V — The identification with ⊥ is NOT formalized here

⛔ A theorem taking `∃ c, UnregisteredFloor c` as a hypothesis was DELETED 2026-09-16. Measured: the
same proof term elaborated with the hypothesis removed AND with its negation supplied, so the binder
carried nothing and the gloss calling it conditional was false. Option (a)'s second half is OPEN and
this file does not narrow it. -/

/-- `Statement:` that self-application at `c` is undefined.
    `Reading:` the COMMITMENT, named so it has a signature. Nothing is proved conditional on it. -/
def UnregisteredFloor (c : Nat.Partrec.Code) : Prop :=
  ¬ (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms registered_ends_separated
#print axioms registeredDecider
#print axioms registered_discriminator_exists
#print axioms PoleDiscriminator
#print axioms dom_mk
#print axioms em_of_poleDiscriminator
#print axioms poleDiscriminator_of_classical
#print axioms no_computable_registration_at_kleene_floor
#print axioms UnregisteredFloor

end PurityCheck
