-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the vertical dereference toward Lawvere — the framework's self-application fixed point as an INSTANCE of Lawvere's general fixed-point engine (existence), with location-at-⊥ and uniqueness as the framework's added content. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Computability.SelfApp
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Lawvere dereference — selfApp as an instance of the general engine (probe)

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The whole arc has been one pattern recurring at deeper and deeper dereferences: a *specific* object is
only ever a witness of a *general* schema (instance-vs-requirements, `RequirementsGap.lean`), and that
gap is scale-invariant up a tower (`MetaFork.lean`). This file probes the deepest layer reachable: the
general case at the top is **Lawvere's fixed-point theorem** (`Wall.lean` `lawvere_fixedpoint`), and the
framework's own self-referential fixed point (`AbstractSelfApp`) is an *instance* of it.

The pieces line up exactly against `AbstractSelfApp`'s three fields (`selfApp`, `fixed_bot`,
`unique_fp`):
- **Lawvere supplies EXISTENCE, as self-application.** `lawvere_fixedpoint` produces its fixed point in
  the form `e a a` — self-application at a diagonal point (`lawvere_fixedpoint_selfApp`). This is the
  ν-regime the framework already names in `negation_no_fixedpoint`'s docstring ("ν = a fixed point
  exists: Quine atom, Y combinator"). It is exactly what `fixed_bot` asserts.
- **The framework PINS it — the extra content beyond Lawvere.** `fixed_bot` + `unique_fp` upgrade
  Lawvere's `∃` to `∃!` (`selfApp_pinnable`): existence at ⊥ *and* uniqueness. Uniqueness is genuinely
  extra — existence alone never forces it (`existence_without_uniqueness`), and uniqueness is precisely
  the fork collapse of `RequirementsGap`/`fork_collapse_iff`.
- **The other regime is the wall.** The same engine used contrapositively at a fixed-point-*free* map
  (negation) is Cantor/Russell/Turing (`cantor_via_engine`); its trigger — a reflexive point-surjection
  — is *refuted* in well-founded Set (`lawvere_trigger_refuted`). So the ν fixed point the framework
  assumes cannot live in well-founded Set; `fixed_bot` is the commitment to the non-well-founded (AFA)
  regime — the same `QuineHost` commitment, one level down.

**Honest status (the fence).** None of this claims to *reduce* the framework to Lawvere, or to prove
"the keystone is Lawvere" (that stays the fenced conjecture of `Wall.lean`). What is proved: Lawvere's
fixed point is a self-application (`lawvere_fixedpoint_selfApp`); the framework's self-application fixed
point is `∃!` (`selfApp_pinnable`); existence does not force uniqueness (`existence_without_uniqueness`);
the engine's trigger is refuted in Set (`lawvere_trigger_refuted`). The *reading* — that these assemble
into "Lawvere (general, existence) + pinning (the framework's instance)" — is the interpretation, held
as a reading. `AbstractSelfApp.fixed_bot`/`unique_fp` remain assumed class fields, not derived from a
concrete reflexive object (that derivation needs an untyped-lambda / domain model — the open bridge).

## Structure
- § I   Lawvere's fixed point is a self-application (`e a a`)
- § II  The framework pins it: `selfApp` has a unique fixed point (`∃!`)
- § III Uniqueness is extra: existence never forces it
- § IV  The wall regime: the engine's trigger is refuted in well-founded Set
-/

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. Lawvere's fixed point is a self-application -/

/-- **Lawvere's fixed point IS self-application.** Refining `lawvere_fixedpoint`: the fixed point it
produces for any `f` is `e a a` — `e` applied to the diagonal point `a` at itself. Existence of the
self-referential fixed point (the ν-regime) is delivered by the engine, and delivered *as*
self-application — the abstract shadow of which is `AbstractSelfApp.selfApp`. -/
theorem lawvere_fixedpoint_selfApp {A B : Type*} (e : A → (A → B))
    (he : Function.Surjective e) (f : B → B) : ∃ a, f (e a a) = e a a := by
  obtain ⟨a, ha⟩ := he (fun x => f (e x x))
  exact ⟨a, (congrFun ha a).symm⟩

/-! ## § II. The framework pins it — `selfApp` has a unique fixed point -/

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-- **The framework's self-application fixed point is pinned (`∃!`).** Where Lawvere gives only
existence, `AbstractSelfApp` supplies both `fixed_bot` (existence, located at ⊥) and `unique_fp`
(uniqueness), so the fixed point is unique. This `∃!` is exactly the "instance pinnable" / collapsed-fork
condition of `RequirementsGap` (`instance_pinnable_iff_fork_collapse`), one dereference down. -/
theorem selfApp_pinnable : ∃! x : L, AbstractSelfApp.selfApp x = x :=
  ⟨bot, AbstractSelfApp.fixed_bot, fun y hy => AbstractSelfApp.unique_fp y hy⟩

/-! ## § III. Uniqueness is extra — existence never forces it -/

/-- **Existence does not force uniqueness.** A self-map can have a fixed point yet not a unique one — the
identity fixes everything. So the framework's `unique_fp` is genuine added content beyond Lawvere's
existence: it is the fork collapse / `(Z)`, not an automatic consequence of the engine. -/
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
and `lawvere_trigger_refuted` (μ: the engine's trigger is Cantor-blocked), this is the whole μ/ν picture
in Lawvere terms — one engine, two regimes, discriminated by the self-loop. (The fork's own μ↔ν duality
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

To *derive* `fixed_bot` from Lawvere rather than assume it, you need a **reflexive object** — a
point-surjection `e : D → (D → D)` — so that `selfApp := fun x => e x x` and Lawvere supplies its fixed
point. The theorems below prove this cannot be done in plain type theory, and say exactly why and where
to look instead.

**The wall.** `reflexive_object_refuted`: on any `D` carrying a fixed-point-free self-map, no reflexive
object exists — Lawvere's own engine, run at that map, refutes it (Cantor). Type theory always has such
maps (`no_reflexive_object_bool`), so `AbstractSelfApp.fixed_bot` genuinely *cannot* be sourced from a
Set-level reflexive object; assuming it is forced, not lazy.

**Where to look next (the escape, and we have been building it).** The obstruction is precisely the
presence of a *fixed-point-free* map. Remove those and the reflexive object returns. That is exactly the
**monotone / domain regime**: on a complete lattice every monotone map has a fixed point
(`instance_always_exists`, Knaster-Tarski) — the order cousin of Kleene's theorem that every continuous
map on a pointed CPO has a least fixed point. No fixed-point-free maps there, so reflexive objects DO
exist (Scott's `D∞`), and Lawvere fires. So the framework's ⊥ *is* a Lawvere fixed point — but in the
fork/domain regime (`RequirementsGap`/`MetaFork`), never in Set. The bridge is not missing; it lives on
the ν side, and the next concrete target is `D∞` / continuous maps on a pointed CPO. -/

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
(`RequirementsGap`/`MetaFork`), with no reflexive object needed. What is NOT reached this way is a
*literal Lawvere sourcing* of ⊥ via a reflexive object `D ≅ [D → D]` — that needs Scott's `D∞`
inverse-limit domain, which Mathlib does not provide (`Control.Fix` / ωCPO give the continuous
fixed point, not the reflexive object). That construction is the precisely-located expedition; the
existence/uniqueness bridge is already here. -/
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
