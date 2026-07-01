-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree TC25 — the seam diagram-level coincidence (lim = colim at the zero object)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC12/TC13 (`ZPH_MC1_TreeSeam.hilbert_bottom_isZero`) established the **object-level** seam: node #5,
the Hilbert bottom `fD_functor.obj 0 = StateSpace 0`, is a *zero object* of `ModuleCat ℂ` — initial
(μ) AND terminal (ν). This file asks whether that point-coincidence lifts to a **diagram-level**
coincidence: do a limit and a colimit land on the same object at the seam?

The honest answer the Lean forces is a **refinement (SPLIT)**, not the flat GO that was pre-registered:

1. **`seam_empty_lim_eq_colim` — the genuinely seam-specific case (the real content).** For the *empty*
   diagram, the limit is the terminal object and the colimit is the initial object. At the zero object
   `Z = fD_functor.obj 0` these are the SAME object `Z`: `IsLimit (asEmptyCone Z)` (≡ `IsTerminal Z`)
   AND `IsColimit (asEmptyCocone Z)` (≡ `IsInitial Z`) both hold, both cones with apex `Z`. So the
   empty-diagram limit and colimit coincide on `Z`. This is the diagram-level seam coincidence, and it
   is special to a zero object.

2. **`generic_object_empty_lim_ne_colim` — the NO-GO fence (genuine separation).** At a NON-zero object
   (`ModuleCat.of ℂ ℂ`) the empty-diagram limit and colimit do NOT both land there: a zero object is
   the only object that is simultaneously the empty-limit (terminal) and the empty-colimit (initial),
   and `ModuleCat.of ℂ ℂ` is not a zero object. This is what makes (1) a real statement about the seam
   rather than a triviality — the coincidence is the *defining* property of the zero object, and it
   fails off the seam.

3. **`const_connected_lim_eq_colim_generic` — the fence on the OTHER overclaim (honesty about scope).**
   For any *connected* index `J` and *any* object `X` (a free variable, NOT pinned to the seam), the
   constant-diagram limit and colimit both exist and have apex `X` (Mathlib `isLimitConstCone` /
   `isColimitConstCocone`). So the connected-diagram lim=colim coincidence is **generic** — true at
   every object — and is therefore NOT evidence for the seam. The pre-registered NO-GO ("for
   non-discrete J the colimit escapes Z via a copower") is FALSE for connected J: the colimit of a
   connected constant diagram is the apex itself, no copower. The copower escape only appears for
   *disconnected* shapes, which is exactly the empty/discrete regime captured by (1)+(2).

**Net verdict.** The seam's μ=ν coincidence DOES lift to diagram level, but only in the empty-diagram
regime — and there it is precisely the zero-object property (1), fenced by the off-seam failure (2).
The connected-diagram coincidence is generic noise (3), not seam evidence. So this is a SPLIT: the
keystone diagram-level reading survives for the empty diagram and is fenced everywhere else.

**Honest fence.** "This diagram-level coincidence IS the diagonal-fixed-point keystone" is the
framework's interpretation. The Lean content is exactly: at the zero object the empty-limit and
empty-colimit coincide (1); off the zero object they do not (2); the connected-diagram coincidence is
a generic fact about all objects (3).
-/

namespace ZeroParadox.ZPH_MC1_TC25

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPD ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_MC1_TreeSeam

/-- The Hilbert bottom, the seam node `Z = fD_functor.obj 0`. -/
noncomputable abbrev Z : ModuleCat ℂ := fD_functor.obj 0

/-- **(1) Seam diagram-level coincidence.** At the zero object `Z`, the empty-diagram **limit** and the
    empty-diagram **colimit** both land on `Z`: `asEmptyCone Z` is a limit (≡ `Z` terminal) and
    `asEmptyCocone Z` is a colimit (≡ `Z` initial), and both cones have apex `Z`. So at the seam the
    limit and colimit of the empty diagram coincide as the single object `Z` — the μ=ν object-level
    coincidence lifted to the diagram level. -/
theorem seam_empty_lim_eq_colim :
    ∃ (_ : IsLimit (asEmptyCone Z)) (_ : IsColimit (asEmptyCocone Z)),
      (asEmptyCone Z).pt = (asEmptyCocone Z).pt := by
  have hZ : IsZero Z := hilbert_bottom_isZero
  exact ⟨hZ.isTerminal, hZ.isInitial, rfl⟩

/-- **(2) NO-GO fence — off the seam the coincidence fails.** A zero object is the *only* object that is
    simultaneously the empty-diagram limit (terminal) and the empty-diagram colimit (initial). The
    non-zero object `ModuleCat.of ℂ ℂ` is therefore NOT both: there is no pair of an empty-limit and an
    empty-colimit cone on it, because that would force it to be a zero object. This is what makes (1) a
    statement about the seam rather than a triviality. -/
theorem generic_object_empty_lim_ne_colim :
    ¬ (Nonempty (IsLimit (asEmptyCone (ModuleCat.of ℂ ℂ)))
        ∧ Nonempty (IsColimit (asEmptyCocone (ModuleCat.of ℂ ℂ)))) := by
  rintro ⟨⟨hterm⟩, ⟨hinit⟩⟩
  -- IsLimit (asEmptyCone X) = IsTerminal X; IsColimit (asEmptyCocone X) = IsInitial X.
  -- terminal gives unique morphisms INTO X; initial gives unique morphisms OUT of X;
  -- together that is exactly IsZero. Then IsZero ⇒ subsingleton carrier ⇒ ℂ subsingleton, false.
  have hZero : IsZero (ModuleCat.of ℂ ℂ) :=
    { unique_to := fun Y => ⟨⟨⟨IsInitial.to hinit Y⟩, fun f => IsInitial.hom_ext hinit f _⟩⟩
      unique_from := fun Y => ⟨⟨⟨IsTerminal.from hterm Y⟩, fun f => IsTerminal.hom_ext hterm f _⟩⟩ }
  have hsub : Subsingleton (ModuleCat.of ℂ ℂ : ModuleCat ℂ) :=
    ModuleCat.isZero_iff_subsingleton.1 hZero
  exact absurd hsub (by
    rw [not_subsingleton_iff_nontrivial]
    exact inferInstanceAs (Nontrivial ℂ))

/-- **(3) Honesty fence — the connected-diagram coincidence is GENERIC, not seam-specific.** For any
    connected index category `J` and ANY object `X : ModuleCat ℂ` (free variable — deliberately not the
    seam), the constant-diagram limit and colimit both exist with apex `X`. Hence "limit = colimit" for
    a connected diagram holds at every object and is NOT evidence for the seam. The pre-registered
    "colimit escapes via a copower" is false for connected `J`. -/
theorem const_connected_lim_eq_colim_generic
    {J : Type} [Category J] [IsConnected J] (X : ModuleCat ℂ) :
    Nonempty (IsLimit (constCone J X)) ∧ Nonempty (IsColimit (constCocone J X))
      ∧ (constCone J X).pt = (constCocone J X).pt :=
  ⟨⟨isLimitConstCone J X⟩, ⟨isColimitConstCocone J X⟩, rfl⟩

end ZeroParadox.ZPH_MC1_TC25

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `ModuleCat` / connected-limits libraries
(`isLimitConstCone` uses `Classical.arbitrary`) — a library dependency, not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC25

#print axioms seam_empty_lim_eq_colim
#print axioms generic_object_empty_lim_ne_colim
#print axioms const_connected_lim_eq_colim_generic

end PurityCheck
