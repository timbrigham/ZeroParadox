-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the vertical dereference toward Lawvere — what Lawvere's general fixed-point theorem gives the framework's self-application fixed point (the SHAPE e a a, and the wall faces by contrapositive) and what it does not (on a ZPSemilattice with a point other than ⊥ its hypothesis fails, nontrivial_lattice_no_witness, so ⊥'s fixed point is the class field fixed_bot and its uniqueness unique_fp). Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Computability.SelfApp
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Lawvere dereference — what the general engine gives selfApp, and what it does not (probe)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview
**Lawvere's engine gives the SHAPE `e a a` and, by contrapositive, the WALL faces;** its hypothesis fails on
a nontrivial `ZPSemilattice` (`nontrivial_lattice_no_witness`), so its ⊥ is a fixed point by the class field
`fixed_bot`, the only one by `unique_fp` (`selfApp_pinnable`). ⚠ Keystone-as-Diagonal-instance stays a CONJECTURE.
-/

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. Lawvere's fixed point is a self-application -/

/-- **Lawvere's fixed point IS self-application.** Refining `lawvere_fixedpoint`: given a
point-surjection `e`, the fixed point it produces for any `f` is `e a a` — `e` applied to the diagonal
point `a` at itself. The statement mentions no `ZPSemilattice` and no ⊥, and on a `ZPSemilattice` with a
point other than ⊥ its hypothesis fails (`nontrivial_lattice_no_witness`). -/
theorem lawvere_fixedpoint_selfApp {A B : Type*} (e : A → (A → B))
    (he : Function.Surjective e) (f : B → B) : ∃ a, f (e a a) = e a a := by
  obtain ⟨a, ha⟩ := he (fun x => f (e x x))
  exact ⟨a, (congrFun ha a).symm⟩

/-! ## § II. The framework pins it — `selfApp` has a unique fixed point -/

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-- **The framework's self-application fixed point is pinned (`∃!`).** `AbstractSelfApp` supplies
both `fixed_bot` (existence, located at ⊥ of the `ZPSemilattice`) and `unique_fp` (uniqueness), so the
fixed point is unique; neither comes from Lawvere's engine, whose hypothesis fails on a `ZPSemilattice`
with a point other than ⊥ (`nontrivial_lattice_no_witness`). This `∃!` is exactly the "instance pinnable" / collapsed-fork
condition of `RequirementsGap` (`instance_pinnable_iff_fork_collapse`), one dereference down. -/
theorem selfApp_pinnable : ∃! x : L, AbstractSelfApp.selfApp x = x :=
  ⟨bot, AbstractSelfApp.fixed_bot, fun y hy => AbstractSelfApp.unique_fp y hy⟩

/-! ## § III. Uniqueness is extra — existence never forces it -/

omit [AbstractSelfApp L] in
/-- **Existence does not force uniqueness.** A self-map can have a fixed point yet not a unique one — the
identity fixes everything. So the framework's `unique_fp` is content that no existence result
supplies, whatever its source: it is the fork collapse / `(Z)`. -/
theorem existence_without_uniqueness [Nontrivial L] :
    ∃ g : L → L, (∃ x, g x = x) ∧ ¬ ∃! x, g x = x := by
  refine ⟨id, ⟨bot, rfl⟩, ?_⟩
  rintro ⟨x, _, hx⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne L
  exact hab ((hx a rfl).trans (hx b rfl).symm)

/-! ## § IV. The wall regime — the engine's trigger is refuted in well-founded Set -/

/-- **The engine cannot fire in Set.** Lawvere's trigger — a reflexive point-surjection
`e : A → (A → Prop)` — does not exist (Cantor, `cantor_via_engine`). So the ν-regime fixed point the
framework assumes (`fixed_bot`) cannot be produced in well-founded Set; assuming it is the commitment to
the non-well-founded (AFA) regime — the `QuineHost` requirement, one level down. -/
theorem lawvere_trigger_refuted {A : Type*} (e : A → (A → Prop)) :
    ¬ Function.Surjective e :=
  cantor_via_engine e

/-! ## § V. The μ/ν branches unified — the diagonal fixed point is the discriminator -/

/-- **The branch discriminator (the unification).** A self-reference relation cannot be both
well-founded (the **μ** branch — the wall: Foundation, Cantor, `wf_no_selfloop`) and carry a diagonal
fixed point / self-loop (the **ν** branch — the self-referential object: the Quine atom, `selfApp`'s
`fixed_bot`). The diagonal fixed point is exactly what discriminates the two branches of the fork: it
lands on ν and is refuted on μ. Together with `selfApp_pinnable` (ν: the fixed point exists, uniquely)
and `lawvere_trigger_refuted` (μ: the engine's trigger is Cantor-blocked), this is the μ/ν picture
in Lawvere terms, discriminated by the self-loop; the ν fixed point is supplied by the class fields
`fixed_bot` / `unique_fp`, not by the engine (§ II, § IV). (The fork's own μ↔ν duality
is `fork_is_frameflip`; the concrete ν non-well-foundedness of `selfApp` is `floor_not_wellFounded`.) -/
theorem mu_nu_branch_exclusion {γ : Type*} {r : γ → γ → Prop} (a : γ) (hself : r a a) :
    ¬ WellFounded r :=
  fun hwf => wf_no_selfloop hwf a hself

/-- **`selfApp` lands on ν, via the discriminator.** The framework's diagonal fixed point (⊥ self-looping
under `selfApp`, `fixed_bot`) forces the self-reference relation off the μ (well-founded) branch — it is
the self-referential object. Proved here by feeding `fixed_bot` to the general discriminator: the SAME
theorem that walls the μ branch produces the ν landing for `selfApp`. So the ν-existence of
`selfApp_pinnable` and this ν non-well-foundedness are two readings of one fact. -/
theorem selfApp_lands_on_nu :
    ¬ WellFounded (fun a b : L => AbstractSelfApp.selfApp b = a) :=
  mu_nu_branch_exclusion bot AbstractSelfApp.fixed_bot

/-! ## § VI. The hard bridge — located, not crossed (the wall is Cantor; the escape is the fork)

Deriving `fixed_bot` rather than assuming it needs a **reflexive object**, and
`reflexive_object_refuted` shows none exists on any carrier admitting a fixed-point-free self-map —
and type theory has those (`no_reflexive_object_bool`), so the assumption is forced, not lazy.
The escape is the monotone/domain regime, where no fixed-point-free maps exist; it is already crossed in
the computability face. Where to look and why: `ZeroParadox/Settheory/LawvereBridge.md`. -/

/-- **The reflexive object is refuted wherever a fixed-point-free map exists.** A point-surjection
`e : D → (D → D)` would, by Lawvere, force any `f : D → D` to have a fixed point; a fixed-point-free `f`
contradicts that. So no reflexive object exists on such `D` — the precise reason `fixed_bot` is assumed,
not derived from a Set-level reflexive object. -/
theorem reflexive_object_refuted {D : Type*} (f : D → D) (hf : ∀ x, f x ≠ x)
    (e : D → (D → D)) : ¬ Function.Surjective e := by
  intro he
  obtain ⟨b, hb⟩ := lawvere_fixedpoint e he f
  exact hf b hb

/-- Concrete instance of the wall: no reflexive object on `Bool` — Boolean negation is the
fixed-point-free witness (`bool_not_no_fixedpoint`). -/
theorem no_reflexive_object_bool (e : Bool → (Bool → Bool)) : ¬ Function.Surjective e :=
  reflexive_object_refuted (fun b => !b) (fun b => bool_not_no_fixedpoint b) e

/-! ## § VII. Why the wall is Set-specific — the obstruction is non-monotone -/

/-- **The Cantor obstruction is non-monotone.** The fixed-point-free map that refutes the reflexive
object in Type is negation, and `Not : Prop → Prop` is not monotone — it reverses `False ≤ True`. So the
obstruction witness simply does not live in the monotone world. Combined with `instance_always_exists`
(no monotone map on a complete lattice is fixed-point-free), this pins the wall precisely: the
refutation of the reflexive object is a *non-monotone* phenomenon, absent from the monotone/domain regime
where the framework's ⊥ lives. The crossing is on the ν side because the obstruction cannot follow it
there. -/
theorem not_monotone_not : ¬ Monotone (Not : Prop → Prop) := by
  intro h
  have hle : (False : Prop) ≤ True := by tauto
  exact (h hle) not_false trivial

/-! ## § VIII. What IS crossed — the monotone regime derives the framework's content -/

/-- **The crossing, for the framework's `∃!` content.** In the monotone/domain regime the two things
`AbstractSelfApp` assumes — that a self-application fixed point *exists* and is *unique* — are DERIVED,
not posited: existence-with-uniqueness is exactly the fork collapsing (`fork_collapse_iff`), and bare
existence is Knaster-Tarski. So the `∃!` content of the keystone is crossable via the fork
(`RequirementsGap`/`MetaFork`), with no reflexive object needed. Lawvere's hypothesis, a reflexive
point-surjection, is met not here but in the computability face
(`ZeroParadox/Computability/ComputableCrossing.lean`): the universal machine `eval` is point-surjective
onto the computable functions, and the recursion theorem gives a fixed point there, a Kleene code, a term
of another type than ⊥ of the `ZPSemilattice` (that it is a Lawvere instance is cited). So the
order/fork face gives the `∃!` content (above) and the computability face gives the reflexive-object
realization; a Scott `D∞` domain route (`D ≅ [D → D]`) is a third path, unbuilt in Mathlib and no longer
needed for the crossing. -/
theorem monotone_regime_derives_pinned {α : Type*} [CompleteLattice α] (f : α →o α)
    (hcollapse : f.lfp = f.gfp) : ∃! x, f x = x :=
  (fork_collapse_iff f).mp hcollapse

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms lawvere_fixedpoint_selfApp
#print axioms selfApp_pinnable
#print axioms existence_without_uniqueness
#print axioms lawvere_trigger_refuted
#print axioms mu_nu_branch_exclusion
#print axioms selfApp_lands_on_nu
#print axioms reflexive_object_refuted
#print axioms no_reflexive_object_bool
#print axioms not_monotone_not
#print axioms monotone_regime_derives_pinned

end PurityCheck
