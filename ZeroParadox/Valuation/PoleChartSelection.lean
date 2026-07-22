import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Category.ExcludedMiddleBridge

set_option maxHeartbeats 400000

/-!
# Chart selection at the pole: free on the built sphere, choice-forcing only under an added commitment

## Engineer's Take

We were running this comparison backwards. The poles do not require choice. The selection of a pole, zero
or infinity or not selected yet, is what acts as a representation of choice itself.

---

## Formal Overview (AI-assisted)

This file tests the standing reading that *"choice is which way you view the zero/infinity split"* —
that reading the undetermined pole as definitely `0` or definitely `∞` is a chart selection, and that this
act is the same act as the axiom of choice.

**The verdict is negative for the naive form of that reading, and the negative result is the point.**

- **§ I (the finding).** On a one-point compactification `OnePoint X` with a designated floor `x₀ : X`,
  the two pole points `∞` and `some x₀` are *different constructors*. Distinguishing them is a pattern
  match, so a canonical selector exists with **no axioms at all** (§ I.a, stated generically in `X`).
  § I.b instantiates this at the framework's own built pole,
  `Sphere := OnePoint ℚ_[2]` with `rInv` swapping `0` and `∞` (`Valuation/RiemannSphere.lean`,
  `rInv_swaps`). Selecting a chart at the built pole is constructively free. The naive chart-selection
  reading is refuted by the framework's own object.
- **§ II (what it would take).** Selection forces a decision only when the two charts are
  **indistinguishable from inside** — when membership in the chart-admissibility predicate is *undecided*.
  Formalized here as the Diaconescu shape, reusing `ChoiceFragment` / `em_of_choiceFragment` from
  `Category/ExcludedMiddleBridge.lean`. This section **assumes** the indistinguishability; it does not
  derive it. See the smuggling notice below.
- **§ III (the verdict).** The chart-selection reading is not supported by the built pole. It holds only
  under the additional modeling commitment that the two charts are internally indistinguishable. That
  commitment is exactly the framework's apophatic claim about ⊥ — and it is a commitment, not a theorem.

**Smuggling notice — read before § II.** § II inserts the non-constructivity *by hypothesis*, at exactly
one place: the chart-admissibility predicate `poleAdmissible p`, which is parameterized by an arbitrary
proposition `p` and is therefore not decidable. Excluded middle then falls out of a uniform selector by
Diaconescu. This is **assumed, not derived**. § II is a conditional model of what the reading would need,
never a fact about `OnePoint ℚ_[2]`. `builtChartAdmissible_decidable` and `select_of_decidable` make the
contrast machine-checkable: when the chart predicate *is* decidable — as it is at the built pole —
selection is free, with no axioms.

**Why § I is stated generically first (a measured subtlety, and the reason for the file's shape).** A
first draft stated § I only at `ℚ_[2]`. Every statement then measured
`[propext, Classical.choice, Quot.sound]` — *including the plain discriminator* `isInfty : Sphere → Bool`,
which is a two-case constructor match with no mathematics in it. The cause is that `ℚ_[2]` is a Cauchy
completion: its very `Zero` instance is noncomputable and classical, so the type `OnePoint ℚ_[2]` drags
those axioms in before any selection happens. Reporting that footprint as the cost of *selection* would
have been wrong. § I.a therefore proves the selection results with `X` an arbitrary type — where they are
genuinely axiom-free — and § I.b instantiates. The residual classical axioms in § I.b are the price of
`ℚ_[2]` existing, not the price of choosing a chart.

There are correspondingly two distinct decidability questions at the built pole, which must not be
conflated:

1. *Which pole am I at?* — `∞` versus `some _`. **Free**: a constructor match (`isInftyG`).
2. *Is this affine point the floor?* — `x = 0` for general `x : ℚ_[2]`. **Not free**: no `DecidableEq` on
   a completion. This is also why `rInv` is `noncomputable`.

The selector needs only (1).

## Structure
- § I.a  Generic pole: `poleSelectG` — selection with no axioms, for an arbitrary carrier.
- § I.b  Instantiation at `Sphere = OnePoint ℚ_[2]`, and the `rInv` orbit.
- § II   The conditional model: an undetermined pole, and selection forcing excluded middle (ASSUMED).
- § III  The gap, named.
-/

namespace ZeroParadox

open OnePoint

/-! ## § I.a — The generic pole: selection is free

Nothing here mentions `ℚ_[2]`. `X` is an arbitrary type with a designated floor `x₀`. These are the
statements that carry the negative finding, and they are axiom-free.

**Prior art for the shape of this result.** "Selection is free once a decidable discriminator is present"
has a recognized topological shadow in Diaconescu's second corollary (1975, p. 178), which concerns
complemented subobjects in a sheaf topos. Stated as the paper states it — **one direction**, not a
biconditional; an earlier draft of this note over-read it as an iff. Cited as an adjacent shadow of the
elementary fact used here, not as its source. The elementary content here is not new; what is being established is the *negative*
framework-specific fact that the framework's own pole supplies such a discriminator by construction. -/

/-- **The pole discriminator.** Answers "am I at `∞` or at an affine point?" — a constructor match,
hence computable and axiom-free. It does *not* answer "is this affine point the floor?", which needs
`DecidableEq X` (absent for `X = ℚ_[2]`). The selector below needs only this. -/
def isInftyG {X : Type*} : OnePoint X → Bool
  | (∞ : OnePoint X) => true
  | OnePoint.some _ => false

@[simp] theorem isInftyG_infty {X : Type*} : isInftyG (∞ : OnePoint X) = true := rfl

@[simp] theorem isInftyG_coe {X : Type*} (x : X) : isInftyG (OnePoint.some x) = false := rfl

/-- The discriminator separates the two poles: the machine-checked content of "you can tell which chart
you are in, from inside". -/
theorem isInftyG_separates {X : Type*} (x₀ : X) :
    isInftyG (∞ : OnePoint X) ≠ isInftyG (OnePoint.some x₀) :=
  fun h => Bool.noConfusion h

/-- **The two poles are distinct** — not a metric or valuative fact, a constructor fact. Proved *through*
the discriminator, which is the point: the ends are distinct precisely because something computable tells
them apart. -/
theorem infty_ne_floorG {X : Type*} (x₀ : X) : (∞ : OnePoint X) ≠ OnePoint.some x₀ :=
  fun h => isInftyG_separates x₀ (congrArg isInftyG h)

/-- **The pole orbit**: the two-element set `{∞, x₀}` that an inversion would exchange. Stated as a bare
set so that § I.a does not have to mention any inversion map. -/
def poleOrbitG {X : Type*} (x₀ : X) : Set (OnePoint X) := {(∞ : OnePoint X), OnePoint.some x₀}

/-- **The selector.** Picks the floor end of the pole orbit: sends `∞` to `some x₀` and fixes every
affine point (in particular the floor itself). Total, computable, a single constructor match — no choice,
no decidable equality on `X`. -/
def poleSelectG {X : Type*} (x₀ : X) (s : OnePoint X) : OnePoint X :=
  if isInftyG s then OnePoint.some x₀ else s

@[simp] theorem poleSelectG_infty {X : Type*} (x₀ : X) :
    poleSelectG x₀ (∞ : OnePoint X) = OnePoint.some x₀ := rfl

@[simp] theorem poleSelectG_coe {X : Type*} (x₀ x : X) :
    poleSelectG x₀ (OnePoint.some x) = OnePoint.some x := rfl

/-- **Proposition (§ I.a) — the selector lands in the orbit.** Infrastructure for
`chart_selection_is_freeG`, which is the section's Theorem. -/
theorem poleSelectG_mem_orbit {X : Type*} (x₀ : X) {s : OnePoint X} (hs : s ∈ poleOrbitG x₀) :
    poleSelectG x₀ s ∈ poleOrbitG x₀ := by
  rcases hs with h | h <;> subst h
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- **Proposition (§ I.a) — the selector is constant on the pole orbit.** Both ends are sent to the same
chart, so the selection is well defined on the orbit as an unordered pair: it does not depend on which
representative you are handed. Axiom-free, and the substantive half of `chart_selection_is_freeG`, which
is the section's Theorem. -/
theorem poleSelectG_constant_on_orbit {X : Type*} (x₀ : X) {s t : OnePoint X}
    (hs : s ∈ poleOrbitG x₀) (ht : t ∈ poleOrbitG x₀) :
    poleSelectG x₀ s = poleSelectG x₀ t := by
  rcases hs with h | h <;> subst h <;> rcases ht with h | h <;> subst h <;> rfl

/-- **Theorem (§ I.a) — the headline.** Selecting a chart at a two-ended pole requires no choice: there
is a function that is constant on the pole orbit and returns a canonical element of it. Existence is
witnessed by `poleSelectG`, a constructor match.

The naive chart-selection reading — that reading the pole as definitely the floor or definitely `∞` is
itself an act of choice — is **refuted** for every one-point compactification. -/
theorem chart_selection_is_freeG {X : Type*} (x₀ : X) :
    ∃ f : OnePoint X → OnePoint X,
      (∀ s ∈ poleOrbitG x₀, f s ∈ poleOrbitG x₀) ∧
      (∀ s ∈ poleOrbitG x₀, ∀ t ∈ poleOrbitG x₀, f s = f t) :=
  ⟨poleSelectG x₀, fun _ hs => poleSelectG_mem_orbit x₀ hs, fun _ hs _ ht =>
    poleSelectG_constant_on_orbit x₀ hs ht⟩

/-! ## § I.b — Instantiation at the framework's built pole

`Sphere = OnePoint ℚ_[2]`, floor `OnePoint.some (0 : ℚ_[2])`, exchanged by `rInv` (`rInv_swaps`).

Every statement below measures `[propext, Classical.choice, Quot.sound]`. That footprint is **`ℚ_[2]`'s**,
not selection's: `ℚ_[2]` is a Cauchy completion whose `Zero` instance is already noncomputable and
classical. § I.a is the same content with the carrier abstracted, and it is axiom-free — that is the
control which makes this attribution checkable rather than asserted. -/

/-- The floor of the built sphere. `noncomputable` because `(0 : ℚ_[2])` is. -/
noncomputable def floorPole : Sphere := OnePoint.some (0 : ℚ_[2])

/-- The pole orbit of the built sphere: `{∞, 0}`. -/
noncomputable def poleOrbit : Set Sphere := poleOrbitG (0 : ℚ_[2])

/-- The chart selector at the built pole, picking the floor end. -/
noncomputable def poleSelect : Sphere → Sphere := poleSelectG (0 : ℚ_[2])

/-- **The two poles of the built sphere are distinct.** -/
theorem infty_ne_floor : (∞ : Sphere) ≠ floorPole := infty_ne_floorG _

/-- **Theorem (§ I.b) — selection at the built pole is free.** The instantiation of
`chart_selection_is_freeG`. Its classical footprint is inherited from `ℚ_[2]`; see the section header. -/
theorem chart_selection_is_free :
    ∃ f : Sphere → Sphere,
      (∀ s ∈ poleOrbit, f s ∈ poleOrbit) ∧
      (∀ s ∈ poleOrbit, ∀ t ∈ poleOrbit, f s = f t) :=
  chart_selection_is_freeG (0 : ℚ_[2])

/-- **The `rInv` connection.** The orbit really is the `rInv`-orbit of the pole — `rInv` exchanges the two
ends (`rInv_swaps`) — and the selector is `rInv`-invariant there. So the involution that realizes the
`0 = ∞` antipodality imposes no selection cost: an involution on a pair with *distinguishable* ends
determines nothing that was not already determined. -/
theorem poleSelect_rInv_invariant {s : Sphere} (hs : s ∈ poleOrbit) :
    poleSelect (rInv s) = poleSelect s := by
  rcases hs with h | h <;> subst h
  · rw [rInv_infty]; rfl
  · rw [rInv_zero]; rfl

/-! ## § II — The conditional model: what the reading WOULD need

**Everything in this section assumes what § I refutes.** The built pole's charts are distinguishable; here
they are *stipulated* indistinguishable, by parameterizing chart-admissibility over an arbitrary
proposition `p`. Excluded middle then follows from a uniform selector, by Diaconescu. That implication is
real, but its antecedent is the assumption — the non-constructivity is inserted at `poleAdmissible`, not
discovered. Do not read any statement below as a fact about `OnePoint ℚ_[2]`. -/

/-- A **chart label** at an abstract two-ended pole: one bit, `true` = the `∞` end, `false` = the floor
end. The abstract shadow of `isInftyG`. -/
abbrev Chart : Type := Bool

/-- **The built pole's chart-admissibility predicate**, abstracted: exactly one chart is admissible, and
which one is *decidable*. This is the § I situation. -/
def builtChartAdmissible : Chart → Prop := fun b => b = true

instance builtChartAdmissible_decidable : DecidablePred builtChartAdmissible :=
  fun b => inferInstanceAs (Decidable (b = true))

/-- **Theorem (§ II, contrast).** When chart-admissibility is decidable, selection is free: an inhabited
decidable predicate on `Chart` has a canonical witness, computed by `if`. No choice, no excluded middle.
This is the general form of § I, and it is the reason the built pole imposes nothing. -/
theorem select_of_decidable (S : Chart → Prop) [DecidablePred S] (h : ∃ b, S b) :
    ∃ b, S b ∧ (b = if S true then true else false) := by
  by_cases ht : S true
  · exact ⟨true, ht, by simp [ht]⟩
  · obtain ⟨b, hb⟩ := h
    cases b with
    | true => exact absurd hb ht
    | false => exact ⟨false, hb, by simp [ht]⟩

/-- **The undetermined pole (ASSUMED, not derived).** Chart-admissibility parameterized by an arbitrary
proposition `p`: the `true` end is admissible outright, and the `false` end is admissible exactly when `p`
holds. If `p` is undecided, the two charts are indistinguishable from inside — you cannot tell whether the
admissible set is `{true}` or all of `Chart`.

**This predicate is where the non-constructivity enters, and it enters by stipulation.** The built pole
has no such predicate; it has `builtChartAdmissible`, which is decidable. -/
def poleAdmissible (p : Prop) : Chart → Prop := fun b => b = true ∨ p

/-- The undetermined pole is always inhabited — there is always *a* chart. What is undetermined is
*which*. -/
theorem poleAdmissible_nonempty (p : Prop) : ∃ b, poleAdmissible p b :=
  ⟨true, Or.inl rfl⟩

/-- **Uniform chart selection (the assumed principle).** A single function selecting an admissible chart
from *every* inhabited admissibility predicate — uniformly, as a function of the predicate, so that
extensionally equal predicates receive equal charts.

Definitionally this is `ChoiceFragment` from `Category/ExcludedMiddleBridge.lean`; it is restated in pole
vocabulary so § II reads as the chart-selection claim it is modeling. Renaming a hypothesis does not make
it true: it stays a hypothesis, discharged by the caller. -/
def UniformChartSelection : Prop := ChoiceFragment

theorem uniformChartSelection_iff_choiceFragment :
    UniformChartSelection ↔ ChoiceFragment := Iff.rfl

/-- **Theorem (§ II) — the conditional model.** *Given* that poles may be undetermined in the above
sense, a uniform chart selector yields excluded middle for every proposition.

This is Diaconescu's theorem (1975), reused via `em_of_choiceFragment` — not reproved here, and not a new
result. The framework contributes only the reading of the two predicates as the two ends of an
undetermined pole.

**Honest accounting of where the non-constructivity lives.** It is in `poleAdmissible`: the floor end's
admissibility is an arbitrary undecided proposition. Feeding an undecided proposition into a selector and
recovering a decision is not a discovery about poles; it is Diaconescu's argument with pole-shaped names.
The theorem's usable content is the *converse-facing* one: chart selection can force excluded middle only
if the charts are undetermined in exactly this way — which the built pole is not. -/
theorem em_of_uniformChartSelection (h : UniformChartSelection) : ExcludedMiddle :=
  em_of_choiceFragment h

/-- **The assumption is non-vacuous** — Lean's `Classical.choice` supplies a uniform selector — so § II is
a real implication and not one with an unsatisfiable hypothesis. Classical by construction; that is the
source end of the arrow. -/
theorem uniformChartSelection_of_classical : UniformChartSelection :=
  choiceFragment_of_classical

/-- **Theorem (§ II) — the separating statement.** The undetermined pole is *not* the built pole's
situation: `builtChartAdmissible` is decidable, so its selection is settled outright, with no selector
principle invoked. -/
theorem builtChart_selection_settled :
    builtChartAdmissible true ∧ ¬ builtChartAdmissible false :=
  ⟨rfl, by simp [builtChartAdmissible]⟩

/-! ## § III — The gap, named

Collecting §§ I-II:

- **§ I, proved (axiom-free in § I.a):** at a two-ended pole `{∞, x₀}` — and in particular at
  `Sphere = OnePoint ℚ_[2]` — there is a canonical selector (`poleSelectG`) constant on the orbit.
  Reading the pole as definitely the floor costs nothing. `rInv` swapping the two (`rInv_swaps`) is an
  *involution*, and an involution on a pair with distinguishable ends imposes no choice
  (`poleSelect_rInv_invariant`).
- **§ II, assumed:** if the two ends were instead internally indistinguishable — admissibility of the
  second end an undecided proposition — then uniform selection yields excluded middle (Diaconescu).

**The gap.** Between these sits precisely one thing: the claim that the two charts at ⊥ are internally
indistinguishable. That claim is the framework's apophatic characterization of ⊥ (nothing internal
distinguishes the descriptions). On the built object it is **false** — `isInftyG` distinguishes the ends
by constructor. So the chart-selection reading is not a theorem about the p-adic Riemann sphere. It is a
statement about a *different*, hypothetical pole, one whose ends carry no discriminator.

**What would close it.** Not more proof about `OnePoint ℚ_[2]` — that direction is settled negatively.
Either (a) exhibit a construction of the pole in which no discriminator exists (the two ends quotiented,
or an ambient type genuinely lacking the constructor split), and show *that* object is the framework's ⊥;
or (b) accept the indistinguishability as a labelled modeling commitment and state the chart-selection
reading as conditional on it. Option (a) is open. Option (b) is honest today.

**Status:** the reading is a **conditional model**, not a local equivalence, and it is refuted in its
naive form at the framework's own built pole. -/

end ZeroParadox

/-! ## Axiom Purity Check

Three groups, deliberately separated (see the file header).

**Group A — § I.a, generic carrier.** Expected: no axioms (or `propext` at worst). These carry the
negative finding: selection at a two-ended pole is free.

**Group B — § I.b, the same content instantiated at `ℚ_[2]`.** Expected classical. The cause is that
`ℚ_[2]` is a Cauchy completion (its `Zero` instance is noncomputable and classical) and that `rInv`'s
`x = 0` case split needs `Classical.propDecidable`. Group A is the control showing this footprint belongs
to the carrier, not to selection.

**Group C — § II.** Classical content is the assumed hypothesis, by design.
`em_of_uniformChartSelection` should itself be choice-free: the choice lives in its antecedent. -/

section PurityCheck
open ZeroParadox

-- Group A — § I.a, the finding. Selection at a generic two-ended pole.
#print axioms infty_ne_floorG
#print axioms isInftyG
#print axioms isInftyG_separates
#print axioms poleSelectG
#print axioms poleSelectG_mem_orbit
#print axioms poleSelectG_constant_on_orbit
#print axioms chart_selection_is_freeG

-- Group B — § I.b, instantiated at `ℚ_[2]`; footprint inherited from the carrier.
#print axioms floorPole
#print axioms poleSelect
#print axioms infty_ne_floor
#print axioms chart_selection_is_free
#print axioms poleSelect_rInv_invariant

-- Group C — § II. The decidable-selection contrast: `[propext]`.
#print axioms builtChartAdmissible_decidable
#print axioms select_of_decidable
#print axioms builtChart_selection_settled
#print axioms poleAdmissible_nonempty
#print axioms uniformChartSelection_iff_choiceFragment
#print axioms em_of_uniformChartSelection
#print axioms uniformChartSelection_of_classical

end PurityCheck
