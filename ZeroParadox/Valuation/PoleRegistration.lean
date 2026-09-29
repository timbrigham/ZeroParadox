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

/-! ### § II — The unregistered pole: infinity as a `Prop`

⭐ **STANDARD NAMES, ADOPTED (`R-ADJACENT`).** Carrier: `Part Unit` IS the Sierpiński domain
(de Jong 2023, Def. 15) — the type of truth values, so `PoleDiscriminator` is not about partiality;
it says a `Bool` test decides EVERY proposition. Principle: the inert-packaging `example` below is,
in topos vocabulary, **the subobject classifier Ω is decidable** (`Ω ≅ 1 + 1`). ⚠ There that is
EQUIVALENT to excluded middle; here only the forward leg is proved, because a `Bool` decider is DATA
— the `Prop`/`Type` fence, stated in `ZeroParadox/Category/ExcludedMiddleBridge.lean`.
`Option`/`Part` are LIFTINGS of dominances, not dominances. Sources, attribution and scope in the
ride-along `ZeroParadox/Valuation/PoleRegistration.md`. -/

/-- `Statement:` a uniform `Bool` test, correct about `Dom`, on `Part Unit` — the Sierpiński domain.
    ⚠ At `Unit` deliberately: a weaker hypothesis, hence a stronger theorem below. -/
def PoleDiscriminator : Prop :=
  ∃ d : Part Unit → Bool, ∀ x : Part Unit, d x = true ↔ x.Dom

-- Statement: the packaging is inert — testing `Dom` on `Part Unit` is testing an arbitrary `Prop`.
example : PoleDiscriminator ↔ ∃ d : Prop → Bool, ∀ p : Prop, d p = true ↔ p :=
  ⟨fun ⟨d, hd⟩ => ⟨fun p => d (Part.mk p (fun _ => ())), fun _p => hd _⟩,
   fun ⟨d, hd⟩ => ⟨fun x => d x.Dom, fun _x => hd _⟩⟩

-- Statement: § II's hypothesis yields the corpus's existing one (`ExcludedMiddleBridge.lean`).
example : PoleDiscriminator → ChoiceFragment := by
  rintro ⟨d, hd⟩
  refine ⟨fun S => d (Part.mk (S true) (fun _ => ())), fun S hS => ?_⟩
  by_cases h : d (Part.mk (S true) (fun _ => ())) = true
  · simp only [h]
    exact (hd _).mp h
  · have hnt : ¬ S true := fun hst => h ((hd _).mpr hst)
    have hf : d (Part.mk (S true) (fun _ => ())) = false := by
      simpa using h
    simp only [hf]
    obtain ⟨b, hb⟩ := hS
    cases b with
    | true => exact absurd hb hnt
    | false => exact hb

-- Statement: and back again, so the two hypotheses are inter-derivable.
-- The content is not the inter-derivability — both sides are theorems here — it is that BOTH LEGS
-- ARE CHOICE-FREE: this one measures `[propext, Quot.sound]`, and it uses no excluded middle at
-- all. Diaconescu's two predicates are each constructively inhabited, so `decide (ch A = ch B)`
-- is already data and the chooser alone supplies it.
example : ChoiceFragment → PoleDiscriminator := by
  intro h
  obtain ⟨ch, hch⟩ := h
  refine ⟨fun x =>
    decide (ch (fun b => b = true ∨ x.Dom) = ch (fun b => b = false ∨ x.Dom)), fun x => ?_⟩
  have hA : (ch (fun b => b = true ∨ x.Dom) = true) ∨ x.Dom :=
    hch (fun b => b = true ∨ x.Dom) ⟨true, Or.inl rfl⟩
  have hB : (ch (fun b => b = false ∨ x.Dom) = false) ∨ x.Dom :=
    hch (fun b => b = false ∨ x.Dom) ⟨false, Or.inl rfl⟩
  simp only [decide_eq_true_eq]
  constructor
  · intro heq
    rcases hA with hAt | hp
    · rcases hB with hBf | hp
      · exact absurd (hAt ▸ hBf ▸ heq) (by decide)
      · exact hp
    · exact hp
  · intro hdom
    have : (fun b => b = true ∨ x.Dom) = (fun b => b = false ∨ x.Dom) :=
      funext fun b => propext ⟨fun _ => Or.inr hdom, fun _ => Or.inr hdom⟩
    rw [this]

/-- `Statement:` the domain of `Part.mk p f` is `p` itself. -/
theorem dom_mk (p : Prop) (f : p → Unit) : (Part.mk p f).Dom = p := rfl

/-- `Statement:` a uniform discriminator on the Sierpiński domain yields excluded middle.
    `Reading:` CITED, not claimed — de Jong 2023 § 2.3, and Proposition 63 with Proposition 62,
    which state this taboo at S itself. Local only in not routing through
    Diaconescu, a fact about proof STRUCTURE: the `example`s above show the hypothesis
    inter-derivable with `ChoiceFragment`.
    ⚠ The conclusion is `Prop`-valued, NOT `∀ p, Decidable p` — `Prop`/`Type` stratification. -/
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

/-! ### Prior art — a KNOWN genre, NOT claimed as new

de Jong 2023 § 2.3 has § II's taboo. That which END the discriminator sits on decides which taboo you
get is prior art in constructive/predicative domain theory, NOT this framework's; § II proves one
instance of the top-end half. Closest: **Proposition 63** with 62 — since `⊤ ⊑ x` IS `x.Dom` in
`Part Unit`, they state exactly `em_of_poleDiscriminator`'s taboo; Proposition 22 is the BOTTOM end,
yielding only the WEAK form. ⚠ That the ends are therefore DIFFERENT conditions does NOT follow from
those results — the ride-along says why. Knapp 2020 supplies the `Option`/`Part` vocabulary; the
weak-versus-full distinction is fenced in `ZeroParadox/Category/LawvereTaboo.lean`. Details:
`ZeroParadox/Valuation/PoleRegistration.md`. -/

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
-- Statement: `Part α → Option α`, and it takes `[Decidable o.Dom]`. Reading: `Option` and `Part`
-- are the LIFTINGS `L_{d₂}` and `L_{d_Ω}` of two of Knapp's three trivial dominances (Knapp 2020,
-- Def. 5.17, p. 92); a dominance is a SET OF PROPOSITIONS, and the notion is Rosolini's.
-- Exhibited here, never discovered here.
#check @Part.toOption
-- Statement: the equivalence of the two, and it is `noncomputable`.
#check @Part.equivOption

-- Reading: the asymmetry, elaborated — this direction needs nothing, the other cannot be written.
example (α : Type) : Option α → Part α := Part.ofOption

end Cited

/-! ### § V — The identification with ⊥ is NOT formalized here

Nothing below is proved conditional on `UnregisteredFloor`: it is a NAME for the commitment, carrying
a signature and no theorem. Option (a)'s second half is OPEN and this file does not narrow it. -/

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
