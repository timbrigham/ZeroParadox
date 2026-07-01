-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPJ_SelfApp
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Direction B — the two faces of ⊥ at the seam: VACUOUS (they coincide, but only as a bare singleton)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The conjecture (`structureless_point_is_bottom_2026-06-30.md`): ⊥'s two faces meet at the seam — the
**structureless** face (the bare point all domain bottoms collapse to, ≅ `PUnit`) and the
**self-referential** face (the fixed-point set of `selfApp`, which `AbstractSelfApp.unique_fp` makes
`{⊥}`). Are they the same object via a *structure-respecting* identification, or only as generic singletons?

**Correction to a first attempt (cold audit caught it).** An earlier version "refuted" this with the
observation that `x↦2x` and `x↦3x` both fix `0` in `ℚ_[2]` — but that is banal (every linear map fixes 0)
and never engaged the actual `selfApp` or the two faces. It tested nothing. This version engages the real
objects.

**What this actually proves — and the honest verdict: VACUOUS.**
(Up front: the three lemmas below are *generic singleton plumbing* — `{⊥}` is uniquely iso to `PUnit`,
true of any singleton. The FINDING is the verdict that the conjecture is vacuous, not the lemmas
themselves; the `.lean` does almost no work the prose couldn't.)
For any `AbstractSelfApp L`:
- `selfApp_face_subsingleton` — the self-referential face `{x // selfApp x = x}` is a subsingleton
  (everything in it is `⊥`, by `unique_fp`).
- `selfApp_face_equiv_punit` — the self-referential face is therefore **iso to the bare-collapse point**
  `PUnit`. So the two faces DO coincide as objects.
- `faces_iso_unique` — but that iso is the **unique** one (the equiv type is a subsingleton): there is
  no choice, no structure to respect or fail. The identification carries zero information.

**Verdict (corrected 2026-06-30 — see `reaching_bottom_vs_interpreting_it_2026-06-30.md`): the
coincidence is at the ACTUAL-⊥ layer, and it is REAL, not vacuous.** The two faces coincide as the
structureless point (`{⊥} ≅ PUnit`). This was first mislabeled VACUOUS for failing *structure-respect* —
but that is the WRONG test at ⊥. By definition ⊥ is timeless / spaceless / descriptionless /
measurementless / **structureless**; structure is the mark of an *interpretation* of ⊥, not of ⊥ itself.
**Structurelessness is the signature of having reached actual ⊥** — so the two faces reaching the same
conditionless point IS the genuine unification, in the only form ⊥ admits.

Two layers: at the **interpretation layer** the bottoms are distinct (their retained structure differs —
the campaign's walls); at the **actual-⊥ layer** all structure is stripped and they are one point (TC22's
"keep vs forget structure" is the boundary). Honest fence: the bare iso `{⊥} ≅ PUnit` is *generic*; the
non-generic content is the **uniqueness** theorem `AbstractSelfApp.unique_fp` (the fixed-point set is a
*single* point — a priori it needn't be), and the proven exception **#2** (the Markov bottom is a
simplex/set, TC23 — an interpretation that has NOT bottomed out unless collapsed, TC31). This is the
unification specifically at actual ⊥; it does NOT reopen the falsified identity-of-interpretations thesis.
-/

namespace ZeroParadox.ZPH_TwoFacesBot

open ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPJ_SelfApp

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-- The self-referential face `{x // selfApp x = x}` is a subsingleton: every fixed point is `⊥`
    (`unique_fp`). So as an object it is a bare singleton. -/
theorem selfApp_face_subsingleton :
    Subsingleton {x : L // AbstractSelfApp.selfApp x = x} :=
  ⟨fun a b => Subtype.ext <| by
    rw [AbstractSelfApp.unique_fp a.1 a.2, AbstractSelfApp.unique_fp b.1 b.2]⟩

/-- The self-referential face is iso to the bare-collapse point `PUnit`: the two faces coincide as
    objects (the face is a singleton — `⊥` via `fixed_bot`, unique via `unique_fp`). -/
def selfApp_face_equiv_punit :
    {x : L // AbstractSelfApp.selfApp x = x} ≃ PUnit :=
  haveI := selfApp_face_subsingleton (L := L)
  { toFun := fun _ => PUnit.unit
    invFun := fun _ => ⟨bot, AbstractSelfApp.fixed_bot⟩
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => rfl }

/-- The identification is the **unique** one (the equiv type is a subsingleton): no choice, no structure
    to respect. The coincidence carries zero information — it is the generic singleton iso. -/
theorem faces_iso_unique :
    Subsingleton ({x : L // AbstractSelfApp.selfApp x = x} ≃ PUnit) :=
  ⟨fun _ _ => Equiv.ext fun _ => Subsingleton.elim _ _⟩

end ZeroParadox.ZPH_TwoFacesBot

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_TwoFacesBot

#print axioms selfApp_face_subsingleton
#print axioms selfApp_face_equiv_punit
#print axioms faces_iso_unique

end PurityCheck
