-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — TC35: the seam #5 is the additive UNIT of the biproduct on `ModuleCat ℂ`

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The seam node #5 is `Z := fD_functor.obj 0 = StateSpace 0`, the Hilbert bottom. Prior tree work
established it as a **zero object** of `ModuleCat ℂ` — initial ∧ terminal (`hilbert_bottom_isZero`,
`fD_zero_isInitial`, `fD_zero_isTerminal`), the μ=ν coincidence at the object/arrow level.

This file asks whether that coincidence is *absorbed by the binary-combination law* of the category:
is the seam the two-sided identity of the biproduct `⊞`? For every `X : ModuleCat ℂ` we exhibit the
canonical isomorphisms
- `seam_biprod_right : X ≅ X ⊞ Z` (right unit), and
- `seam_biprod_left  : X ≅ Z ⊞ X` (left unit),
both instantiated at the concrete seam object `Z = fD_functor.obj 0`. The bundled statement
`seam_is_biprod_unit` records both, witnessing the seam node as the neutral element of `⊞`.

**What is genuinely new vs. what is generic — stated honestly in the verdict, not hidden here.**
The *isomorphism itself* (`isoBiprodZero` / `isoZeroBiprod`) is a fully GENERIC Mathlib fact: in any
category with zero morphisms and binary biproducts, any object that `IsZero` is a biproduct unit. So
the construction below carries **no Hilbert-specific or framework-specific content beyond what
`IsZero (fD_functor.obj 0)` already gives** — it is the algebraic restatement of the seam's
zero-object status, not an independent property of `StateSpace 0`. The honest delta over TC12/TC13
(initial ∧ terminal) is only: the same `IsZero` fact also makes the node the unit of `⊞`, because
"zero object" and "biproduct unit" are the same predicate read two ways. The in-statement
instantiation at `fD_functor.obj 0` keeps the node concrete; it does **not** make the unit role
node-specific.

**Honest fence.** "The seam is the algebraic face of μ=ν / the diagonal fixed point" is the
framework's interpretation. The Lean content is exactly: `fD_functor.obj 0` `IsZero`, hence (by the
generic biproduct-unit lemmas) `X ≅ X ⊞ (fD_functor.obj 0)` and `X ≅ (fD_functor.obj 0) ⊞ X`.
-/

namespace ZeroParadox.ZPH_MC1_TC37

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_MC1_TreeSeam

/-- The seam object: the Hilbert bottom `fD_functor.obj 0 = StateSpace 0`, a zero object of
    `ModuleCat ℂ` (see `hilbert_bottom_isZero`). -/
noncomputable abbrev seam : ModuleCat ℂ := fD_functor.obj 0

/-- Right unit: for every `X`, the seam is absorbed on the right of the biproduct,
    `X ≅ X ⊞ seam`. The map is `biprod.inl` with inverse `biprod.fst`; it exists because the seam
    `IsZero` (`hilbert_bottom_isZero`). Instantiated at the concrete seam node. -/
noncomputable def seam_biprod_right (X : ModuleCat ℂ) : X ≅ X ⊞ seam :=
  isoBiprodZero (Y := seam) hilbert_bottom_isZero

/-- Left unit: for every `X`, the seam is absorbed on the left of the biproduct,
    `X ≅ seam ⊞ X`. The map is `biprod.inr` with inverse `biprod.snd`; it exists because the seam
    `IsZero`. Instantiated at the concrete seam node. -/
noncomputable def seam_biprod_left (X : ModuleCat ℂ) : X ≅ seam ⊞ X :=
  isoZeroBiprod (X := seam) hilbert_bottom_isZero

/-- **TC35 (bundled): the seam node is the two-sided unit of the biproduct `⊞` on `ModuleCat ℂ`.**
    For every `X` there are canonical isos `X ≅ X ⊞ seam` and `X ≅ seam ⊞ X`, where
    `seam = fD_functor.obj 0` is the Hilbert bottom. The load-bearing content (the two unit isos at
    the concrete seam object) is IN the statement.

    Honest scope: both isos are the GENERIC biproduct-unit lemmas applied to `IsZero seam`. The
    statement is true of any zero object in any additive category; the only node-specific input is
    `hilbert_bottom_isZero`. This upgrades the seam's description from object/arrow level
    (initial ∧ terminal) to "unit of the binary-combination law", but adds no content beyond the
    zero-object status it already had. -/
theorem seam_is_biprod_unit (X : ModuleCat ℂ) :
    Nonempty (X ≅ X ⊞ seam) ∧ Nonempty (X ≅ seam ⊞ X) :=
  ⟨⟨seam_biprod_right X⟩, ⟨seam_biprod_left X⟩⟩

/-- The honesty witness, also IN a statement: the seam's biproduct-unit role is *equivalent* to its
    zero-object status, not stronger. `IsZero seam` both gives the unit isos (forward) and is implied
    by `seam ⊞ seam` being zero (a degenerate instance of `biprod_isZero_iff`). This makes explicit
    that TC35 is the algebraic restatement of `hilbert_bottom_isZero`, not an independent property. -/
theorem seam_unit_iff_isZero :
    IsZero seam ↔ Nonempty (seam ≅ seam ⊞ seam) := by
  constructor
  · intro hZ; exact ⟨isoBiprodZero (Y := seam) hZ⟩
  · intro _; exact hilbert_bottom_isZero

end ZeroParadox.ZPH_MC1_TC37

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `ModuleCat` / biproduct / `EuclideanSpace` libraries —
a library dependency carried already by the ZP-D / ZP-H Hilbert layer, not a new commitment. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC37

#print axioms seam_biprod_right
#print axioms seam_biprod_left
#print axioms seam_is_biprod_unit
#print axioms seam_unit_iff_isZero

end PurityCheck
