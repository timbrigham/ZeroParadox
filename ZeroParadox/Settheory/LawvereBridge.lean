-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the vertical dereference toward Lawvere — the framework's self-application fixed point as an INSTANCE of Lawvere's general fixed-point engine (existence), with location-at-⊥ and uniqueness as the framework's added content. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Settheory.Wall
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

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms lawvere_fixedpoint_selfApp
#print axioms selfApp_pinnable
#print axioms existence_without_uniqueness
#print axioms lawvere_trigger_refuted

end PurityCheck
