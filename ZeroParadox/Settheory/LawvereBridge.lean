-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the vertical dereference toward Lawvere — what Lawvere's general fixed-point theorem gives the framework's self-application fixed point (the SHAPE e a a, and the wall faces by contrapositive) and what it does not (on a ZPSemilattice with a point other than ⊥ its hypothesis fails, nontrivial_lattice_no_witness; ⊥'s fixed point is the class field fixed_bot and its uniqueness unique_fp). Curated results indexed in ZeroParadox/MANIFEST.md.

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
a nontrivial `ZPSemilattice` (`nontrivial_lattice_no_witness`); its ⊥ is a fixed point by the class field
`fixed_bot`, the only one by `unique_fp` (`selfApp_pinnable`). ⚠ How each face relates to Lawvere: ZP-R § III.
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

/-! ## § VI. The hard bridge — located, not crossed (the wall is Cantor)

Deriving `fixed_bot` rather than assuming it needs a **reflexive object**, and
`reflexive_object_refuted` shows none exists on any carrier admitting a fixed-point-free self-map —
and type theory has those (`no_reflexive_object_bool`), so the assumption is forced, not lazy.
On a complete lattice no MONOTONE map is fixed-point-free (`instance_always_exists`), so a monotone witness is unavailable there;
a non-monotone one still refutes `e` on any nontrivial complete lattice (`x ↦ if x = ⊥ then ⊤ else ⊥`).
Lawvere's hypothesis is met in the computability face. Where to look and why:
`ZeroParadox/Settheory/LawvereBridge.md`. -/

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

-- Statement: in types the converse of `reflexive_object_refuted` holds: a type with no fixed-point-free
--   endomap has exactly one element, and it carries a surjection onto its endomaps.
example {D : Type*} (hnf : ¬ ∃ f : D → D, ∀ x, f x ≠ x) :
    (∃ d : D, ∀ x : D, x = d) ∧ ∃ e : D → (D → D), Function.Surjective e := by
  classical
  have hne : Nonempty D := by
    by_contra h0
    exact hnf ⟨id, fun x => (h0 ⟨x⟩).elim⟩
  obtain ⟨d⟩ := hne
  have hsub : ∀ a b : D, a = b := by
    intro a b
    by_contra hab
    exact hnf ⟨fun x => if x = a then b else a, fun x => by
      dsimp only
      split_ifs with hx
      · subst hx; exact fun h => hab h.symm
      · exact fun h => hx h.symm⟩
  exact ⟨⟨d, fun x => hsub x d⟩, fun _ => id, fun _ => ⟨d, funext fun _ => hsub _ _⟩⟩

/-! ## § VII. Where completeness blocks a monotone Cantor route — on a complete lattice every fixed-point-free endomap is non-monotone -/

/-- **The Cantor obstruction's witness is non-monotone.** In Cantor's refutation (`cantor_via_engine`)
the fixed-point-free map is negation, and `Not : Prop → Prop` is not monotone — it reverses
`False ≤ True`; on `Bool` the witness is Boolean negation (`no_reflexive_object_bool`), also not
monotone (example below). So that witness is not a monotone map.
`instance_always_exists` says no monotone map on a complete lattice is fixed-point-free, so on a
complete lattice the refutation needs a non-monotone witness. Off complete lattices a monotone map can
be fixed-point-free: `Nat.succ`, and the identity on the empty set (examples below). -/
theorem not_monotone_not : ¬ Monotone (Not : Prop → Prop) := by
  intro h
  have hle : (False : Prop) ≤ True := by tauto
  exact (h hle) not_false trivial

-- Statement: `Nat.succ` is monotone and fixed-point-free.
example : Monotone Nat.succ ∧ ∀ n : ℕ, Nat.succ n ≠ n :=
  ⟨fun _ _ h => Nat.succ_le_succ h, fun n => Nat.succ_ne_self n⟩

-- Statement: `ℕ` under `≤` has no element above every element (a complete lattice has one, `⊤`).
example : ¬ ∃ t : ℕ, ∀ n : ℕ, n ≤ t := fun ⟨t, h⟩ => by have := h (t + 1); omega

-- Statement: the identity on `Empty` is monotone and fixed-point-free (because `Empty` has no elements).
example : Monotone (id : Empty → Empty) ∧ ∀ x : Empty, id x ≠ x :=
  ⟨monotone_id, fun x => x.elim⟩

-- Statement: `Empty` carries no `CompleteLattice` structure (one would need an element `⊥`).
example : IsEmpty (CompleteLattice Empty) := ⟨fun h => (h.bot : Empty).elim⟩

-- Statement: no map `Empty → (Empty → Empty)` is surjective (`reflexive_object_refuted` at `f = id`).
example (e : Empty → (Empty → Empty)) : ¬ Function.Surjective e :=
  reflexive_object_refuted (id : Empty → Empty) (fun x => Empty.elim x) e

-- Statement: the function space `Empty → Empty` has exactly one element.
example : Nonempty (Unique (Empty → Empty)) := ⟨inferInstance⟩

-- Statement: `Bool` carries a `CompleteLattice` structure (Mathlib's instance; its order is `false ≤ true`).
example : Nonempty (CompleteLattice Bool) := ⟨inferInstance⟩

-- Statement: on `Bool`, negation is fixed-point-free and not monotone (it reverses `false ≤ true`).
example : (∀ b : Bool, (!b) ≠ b) ∧ ¬ Monotone (fun b : Bool => !b) :=
  ⟨fun b => by cases b <;> decide, fun h => absurd (h (show false ≤ true by decide)) (by decide)⟩

-- Statement: on the two-element chain `false ≤ true`, every monotone self-map has a fixed point (the
--   first conjunct is Knaster–Tarski, `OrderHom.lfp`), and no map from its two points onto its monotone
--   self-maps is surjective.
-- Reading: so in the monotone face the absence of a fixed-point-free monotone endomap does not suffice
--   for a reflexive object.
example : (∀ f : Bool →o Bool, ∃ b, f b = b) ∧
    ¬ ∃ e : Bool → (Bool →o Bool), Function.Surjective e := by
  refine ⟨fun f => ⟨OrderHom.lfp f, OrderHom.map_lfp f⟩, ?_⟩
  · rintro ⟨e, he⟩
    let c0 : Bool →o Bool := ⟨fun _ => false, fun _ _ _ => le_rfl⟩
    let c1 : Bool →o Bool := ⟨fun _ => true, fun _ _ _ => le_rfl⟩
    let i : Bool →o Bool := OrderHom.id
    obtain ⟨a0, h0⟩ := he c0
    obtain ⟨a1, h1⟩ := he c1
    obtain ⟨a2, h2⟩ := he i
    have d01 : c0 ≠ c1 := fun h => by
      have := congrArg (fun g : Bool →o Bool => g false) h; simp [c0, c1] at this
    have d02 : c0 ≠ i := fun h => by
      have := congrArg (fun g : Bool →o Bool => g true) h; simp [c0, i] at this
    have d12 : c1 ≠ i := fun h => by
      have := congrArg (fun g : Bool →o Bool => g false) h; simp [c1, i] at this
    cases a0 <;> cases a1 <;> cases a2 <;> simp_all

/-! ## § VIII. The monotone regime restates uniqueness as the fork collapse -/

/-- **Uniqueness as the fork collapse — restated, not derived.** For a monotone `f` on a complete
lattice, the theorem takes the collapse `f.lfp = f.gfp` as a HYPOTHESIS, which by `fork_collapse_iff` is
EQUIVALENT to `∃! x, f x = x`; so uniqueness is restated, not derived. Bare existence is Knaster-Tarski
(`instance_always_exists`); uniqueness is not free: `id` on any nontrivial lattice is monotone with many
fixed points (`existence_without_uniqueness`). Nothing here connects to `AbstractSelfApp`, where
existence and uniqueness stay the class-field commitments `fixed_bot` and `unique_fp`. Lawvere's hypothesis, a reflexive
point-surjection, is met not here but in the computability face
(`ZeroParadox/Computability/ComputableCrossing.lean`): the universal machine `eval` is point-surjective
onto the computable functions, and the recursion theorem gives a fixed point there, a Kleene code, a term
of another type than ⊥ of the `ZPSemilattice` (that it is a Lawvere instance is cited). A Scott `D∞`
domain (`D ≅ [D → D]`) would be a reflexive object in the monotone regime; it was not located in the
pinned Mathlib as of 2026-10-06 (search record: `ZeroParadox/Settheory/LawvereBridge.md`). -/
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
