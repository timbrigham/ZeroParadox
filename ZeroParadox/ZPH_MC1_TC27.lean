-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_InfoFunctor
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — TC27: a genuine CROSS-category arrow from the μ-bottom #4 to the seam #5

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC18 (the seam file `ZPH_MC1_TreeSeam`) located the μ=ν two-sidedness of node #5 (the Hilbert
bottom `fD_functor.obj 0 = StateSpace 0`) *inside* `ModuleCat ℂ`: #5 is a zero object of that one
category. The deflationary reading of TC18 is that the seam's bridging is intra-category — the two
universal properties (initial ∧ terminal) collapse only within `ModuleCat ℂ`, and the
"cross-category two-sided connector" reading stays unbuilt.

This file tests that deflation against a **cross-category** arrow. The carrier of the Kleisli bottom
#4 is `Fin 0` — the empty type — because `KleisliCat PMF` is definitionally `Type` and
`fC_functor.obj 0 = KleisliCat.mk PMF (Fin 0)` is definitionally `Fin 0`. Mathlib's
**free ℂ-module functor** `ModuleCat.free ℂ : Type ⥤ ModuleCat ℂ` (the left adjoint of the
forgetful functor, `ModuleCat.adj`) is a genuine, structure-preserving functor *between framework
categories*: its codomain is exactly the category that hosts the seam #5.

The free module on the empty type is the zero module (`Fin 0 →₀ ℂ` is a subsingleton, hence a zero
object of `ModuleCat ℂ`). So the cross-category functor carries #4's bottom onto a zero object that
is **canonically isomorphic to the seam #5** (zero objects are unique up to a unique isomorphism).

### What the Lean proves (load-bearing, IN-statement)

- `freeFin0_isZero` — `(ModuleCat.free ℂ).obj (Fin 0)` (the functor's *image* of #4's carrier) is a
  zero object of `ModuleCat ℂ`. (The free module on the empty type is 0.)
- `tc27_cross_arrow` — **the cross-category arrow's image lands AT the seam**: there is an
  isomorphism `(ModuleCat.free ℂ).obj (Fin 0) ≅ fD_functor.obj 0` in `ModuleCat ℂ`. The left side is
  the image of #4's bottom under a real functor whose source is `Type` (= the carrier of `KleisliCat
  PMF`); the right side is the seam #5. This is the cross-category edge TC18's deflation said was
  unbuilt.
- `tc27_image_is_zero_seam` — bundles both halves with the seam's own two-sidedness: the image is a
  zero object AND the seam is a zero object AND they are isomorphic.

### GO verdict, with an honest fence

This is a GO for the pre-registered conjecture: a real functor between framework categories (the
free/forgetful adjunction) sends #4's empty carrier to the zero object and lands canonically on #5.

**The fence (what is interpretation, not Lean).** The arrow is honest as a *functor on the underlying
type*: `ModuleCat.free ℂ` acts on `Type`, and #4's carrier is a `Type`. It is NOT a functor out of
`KleisliCat PMF` *as a category of stochastic maps* — the PMF/Kleisli morphisms (Markov kernels) are
not claimed to transport to ℂ-linear maps. So the NO-GO obstruction's specific reading — "no functor
respects the *PMF-Kleisli morphism structure*" — is **not refuted** here; what is refuted is the
stronger deflation that *no* structure-preserving cross-category arrow lands #4's bottom on #5. The
free-module functor is exactly such an arrow at the object level, with the canonical landing proved
in-statement. The honest scope: GO at the object/carrier level via a real adjunction; the
morphism-level Kleisli→Module transport remains open (and is the next obstruction to probe).
-/

namespace ZeroParadox.ZPH_MC1_TC27

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor

/-- The image of #4's carrier `Fin 0` under the real cross-category functor `ModuleCat.free ℂ`
    is a **zero object** of `ModuleCat ℂ`: the free ℂ-module on the empty type is `Fin 0 →₀ ℂ`,
    a subsingleton, hence zero. -/
theorem freeFin0_isZero : Limits.IsZero ((ModuleCat.free ℂ).obj (Fin 0)) := by
  haveI : Subsingleton ((ModuleCat.free ℂ).obj (Fin 0)) := by
    change Subsingleton (Fin 0 →₀ ℂ)
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- The seam #5 `fD_functor.obj 0 = StateSpace 0` is a zero object of `ModuleCat ℂ`
    (restated locally so this file is self-contained; same content as `TreeSeam.hilbert_bottom_isZero`). -/
theorem seam_isZero : Limits.IsZero (fD_functor.obj 0) := by
  haveI : Subsingleton (StateSpace 0) := ⟨fun a b => by
    apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of ℂ (StateSpace 0))

/-- **TC27 — the cross-category arrow lands at the seam.** The free ℂ-module functor
    `ModuleCat.free ℂ : Type ⥤ ModuleCat ℂ` (a real functor between framework categories, the left
    adjoint of `forget`) carries #4's carrier `Fin 0` onto a zero object that is **canonically
    isomorphic** to the seam #5 `fD_functor.obj 0`. The isomorphism is the unique-zero-object iso. -/
noncomputable def tc27_cross_arrow :
    (ModuleCat.free ℂ).obj (Fin 0) ≅ fD_functor.obj 0 :=
  Limits.IsZero.iso freeFin0_isZero seam_isZero

/-- Bundled witness: the functor-image of #4's bottom is a zero object, the seam #5 is a zero
    object, and the two are isomorphic via the cross-category arrow. The whole claim, in one
    statement. -/
theorem tc27_image_is_zero_seam :
    Limits.IsZero ((ModuleCat.free ℂ).obj (Fin 0))
    ∧ Limits.IsZero (fD_functor.obj 0)
    ∧ Nonempty ((ModuleCat.free ℂ).obj (Fin 0) ≅ fD_functor.obj 0) :=
  ⟨freeFin0_isZero, seam_isZero, ⟨tc27_cross_arrow⟩⟩

/-- The honest scope marker, stated as a theorem about the *carrier*: #4's carrier
    `fC_functor.obj 0` is *definitionally* the type `Fin 0`, which is exactly the input the
    cross-category functor `ModuleCat.free ℂ` consumes. This is why the arrow is real at the
    object level (the passage from the Kleisli object to a `Type` is definitional, not a lossy
    forgetful step). -/
theorem kleisli_bottom_carrier_eq :
    (fC_functor.obj 0 : Type) = Fin 0 := rfl

end ZeroParadox.ZPH_MC1_TC27

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's `ModuleCat` / `Finsupp` / `free` /
`EuclideanSpace` library. It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC27

#print axioms freeFin0_isZero
#print axioms seam_isZero
#print axioms tc27_cross_arrow
#print axioms tc27_image_is_zero_seam
#print axioms kleisli_bottom_carrier_eq

end PurityCheck
