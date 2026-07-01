-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import ZeroParadox.ZPP_Coalgebra
import ZeroParadox.ZPH_MC1_TC26
import ZeroParadox.ZPH_MC1_TC20

/-!
# ZP-H MC-1 tree test TC38: the canonical μ→ν comparison map at the root seam, and the honest
fence on "root-seam ≅ node-seam"

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC26 proved that for the leaf-free **constant** polynomial functor `constPF A` (child type `PEmpty`,
**no recursive position**) the least and greatest fixed points are equivalent:
`root_seam : QPF.Fix (constPF A).Obj ≃ QPF.Cofix (constPF A).Obj`. That theorem exhibits *some*
equivalence (it factors through `A` on both sides). It does **not** identify the canonical
**μ→ν comparison map** — the map that recursion theory actually means by "the comparison from the
initial algebra to the final coalgebra" — nor prove that *that* map is the iso.

This file closes that gap and then fences the keystone honestly.

**GO (the genuinely new edge).** For any QPF `F`, the canonical comparison `Fix F → Cofix F` is the
unique initial-algebra homomorphism into `Cofix F` regarded as an `F`-algebra via the inverse of
`Cofix.dest`. For `constPF A` we build this inverse (`cofixMk`, the leaf-free constructor of TC26) and
define

  `canonicalCmp : Fix (constPF A).Obj → Cofix (constPF A).Obj := Fix.rec (fun y => cofixMk y.1)`

— a genuine recursion homomorphism, not an ad-hoc bijection. We then prove

  `canonicalCmp_eq_root_seam : canonicalCmp = (root_seam : _ ≃ _)`            (it IS TC26's iso)
  `canonicalCmp_bijective    : Function.Bijective canonicalCmp`               (hence iso)
  `canonicalCmp_hom          : canonicalCmp ∘ Fix.mk = cofixMk ∘ (constPF map canonicalCmp)`
                                                                              (it is the comparison)
  `canonicalCmp_unique       : ∀ h, (hom law) → h = canonicalCmp`            (it is THE comparison,
                                                                              via Mathlib Fix.rec_unique)

So the *canonical* μ→ν comparison — the one defined by recursion, with its homomorphism law in the
statement — is an isomorphism for the no-recursive-position functor. That is strictly more than TC26
(existence of an equiv): it pins down *which* map and proves the comparison itself invertible.

**NO-GO / honest fence (the load-bearing deflation, IN the statements).** The pre-registered risk was
that "root-seam ≅ node-seam" is a loose analogy, not a structural identity. It is. Two facts make this
decisive and they are stated in Lean:

1. `seam_iff_no_recursive_position` — the canonical comparison is an iso for `constPF` (no recursive
   position) and is *not* even a bijection for `idPF` (one recursive position): there `Fix` is empty
   and `Cofix` is inhabited, so **no** function `Fix → Cofix` is surjective. The root-seam is governed
   by *absence of a recursive position* in the functor.

2. `node_seam_arrow_collapse_is_generic` — re-exporting TC20: the node-#5 "seam" arrow coincidence
   `IsInitial.to = IsTerminal.from` is **generic** to any initial-alone / terminal-alone object and
   fires off the seam (witnessed at node #4, which is initial, not a zero object, yet has `to = 𝟙`).
   The node-seam is governed by *being a zero object*, and even then the arrow-equality adds nothing.

The two governing conditions live in different settings (a QPF / coalgebra condition on a functor vs a
universal-property condition on an object) and there is **no map between the settings** in this file.
`root_node_seam_no_identity` packages the conclusion: the root-seam iso and the node-seam arrow
collapse are recorded side by side as *distinct* phenomena, both true, neither derivable from the
other here — so "the polynomial-functor seam and the zero-object seam are the SAME phenomenon" is a
**cross-setting modeling commitment / analogy**, not a Lean theorem. The honest new content is the
canonical-comparison iso (GO); the unification is fenced.
-/

namespace ZeroParadox.ZPH.TC38

open QPF
open CategoryTheory
open ZeroParadox.ZPH.TC26

set_option maxHeartbeats 400000

universe u

variable {A : Type u}

/-! ## The canonical μ→ν comparison map for `constPF A` -/

/-- The canonical comparison `Fix → Cofix` for the leaf-free constant functor, defined by recursion on
the initial algebra into `Cofix` as an `F`-algebra. The algebra structure on `Cofix (constPF A).Obj`
is `fun y => cofixMk y.1` — `cofixMk` (TC26) is the leaf-free constructor, the inverse of
`Cofix.dest` for this functor. This is the genuine recursion homomorphism, not an ad-hoc bijection. -/
def canonicalCmp : Fix (constPF A).Obj → Cofix (constPF A).Obj :=
  Fix.rec (fun (y : (constPF A).Obj (Cofix (constPF A).Obj)) => cofixMk y.1)

/-- The recursion (homomorphism) law the canonical comparison satisfies by construction:
`canonicalCmp (Fix.mk x) = cofixMk ((canonicalCmp <$> x).1)`. This is the equation that makes
`canonicalCmp` *the* comparison map (an initial-algebra homomorphism), not merely some function. -/
theorem canonicalCmp_hom (x : (constPF A).Obj (Fix (constPF A).Obj)) :
    canonicalCmp (Fix.mk x) = cofixMk ((canonicalCmp <$> x).1) := by
  show Fix.rec (fun y => cofixMk y.1) (Fix.mk x) = cofixMk ((Fix.rec (fun y => cofixMk y.1) <$> x).1)
  rw [Fix.rec_eq]

/-- The head component is preserved by the QPF functor map on `(constPF A).Obj`
(`constPF` has no children, so the map only touches the vacuous child function). -/
theorem objMap_fst {X Y : Type u} (f : X → Y) (z : (constPF A).Obj X) :
    (f <$> z).1 = z.1 := rfl

/-- Pointwise normal form of the canonical comparison: `canonicalCmp x = cofixMk (Fix.dest x).1`.
Proved by `Fix.ind_rec`: the head component is preserved by the functor map (`constPF` has no children
to recurse into), so the recursion collapses to "read the head, build the leaf-free node". -/
theorem canonicalCmp_apply (x : Fix (constPF A).Obj) :
    canonicalCmp x = cofixMk ((Fix.dest x).1) := by
  refine Fix.ind_rec canonicalCmp (fun x => cofixMk ((Fix.dest x).1)) ?_ x
  intro y _hy
  show canonicalCmp (Fix.mk y) = cofixMk ((Fix.dest (Fix.mk y)).1)
  have h1 : canonicalCmp (Fix.mk y) = cofixMk (y.1) := by
    rw [canonicalCmp_hom, objMap_fst]
  have h2 : (Fix.dest (Fix.mk y)).1 = y.1 := congrArg Sigma.fst (Fix.dest_mk y)
  rw [h1, h2]

theorem canonicalCmp_eq_root_seam :
    (canonicalCmp : Fix (constPF A).Obj → Cofix (constPF A).Obj) = root_seam := by
  funext x
  rw [canonicalCmp_apply]
  rfl

/-- **Uniqueness of the canonical comparison (witnesses the "unique initial-algebra homomorphism"
claim).** Any function `h : Fix → Cofix` satisfying the same recursion (homomorphism) law that
`canonicalCmp` satisfies — `h (Fix.mk x) = cofixMk ((h <$> x).1)`, i.e. `h` is an `F`-algebra
homomorphism into `Cofix` regarded as an algebra via `fun y => cofixMk y.1` — is equal to
`canonicalCmp`. This is `Mathlib`'s `Fix.rec_unique` specialized to the leaf-free algebra, and it is
what makes `canonicalCmp` *the* comparison map, not merely *a* function with the homomorphism law. -/
theorem canonicalCmp_unique (h : Fix (constPF A).Obj → Cofix (constPF A).Obj)
    (hyp : ∀ x : (constPF A).Obj (Fix (constPF A).Obj), h (Fix.mk x) = cofixMk ((h <$> x).1)) :
    h = canonicalCmp := by
  symm
  exact Fix.rec_unique (fun (y : (constPF A).Obj (Cofix (constPF A).Obj)) => cofixMk y.1) h hyp

/-- The canonical comparison is bijective (an isomorphism) for the no-recursive-position functor. -/
theorem canonicalCmp_bijective :
    Function.Bijective (canonicalCmp : Fix (constPF A).Obj → Cofix (constPF A).Obj) := by
  rw [canonicalCmp_eq_root_seam]
  exact (root_seam : Fix (constPF A).Obj ≃ _).bijective

/-! ## The honest fence: root-seam vs node-seam are distinct phenomena -/

/-- **The root-seam is governed by absence of a recursive position.** For `constPF` (no recursive
position) the canonical comparison is a bijection; for `idPF` (one recursive position) NO function
`Fix → Cofix` can be surjective, because `Fix idPF.Obj` is empty while `Cofix idPF.Obj` is inhabited.
So the seam at the root level is the coincidence of μ and ν constructions, and it happens exactly when
the functor has no recursive position. -/
theorem seam_iff_no_recursive_position :
    Function.Bijective (canonicalCmp : Fix (constPF Unit).Obj → Cofix (constPF Unit).Obj)
    ∧ (∀ g : Fix ZeroParadox.ZPP.idPF.Obj → Cofix ZeroParadox.ZPP.idPF.Obj,
        ¬ Function.Surjective g) := by
  refine ⟨canonicalCmp_bijective, ?_⟩
  intro g hg
  obtain ⟨c⟩ := ZeroParadox.ZPP.cofix_nonempty
  obtain ⟨a, _⟩ := hg c
  exact ZeroParadox.ZPP.fix_isEmpty.false a

/-- **The node-seam arrow collapse is generic (re-export of TC20).** The node-#5 "seam" arrow
coincidence `IsInitial.to = IsTerminal.from` holds at any zero object but is *generic*: each side is
independently `𝟙`, and the μ-collapse `to = 𝟙` fires off the seam (node #4 is initial, not a zero
object). So the node-seam is governed by the zero-object universal property, and the arrow-equality
adds nothing beyond it. -/
theorem node_seam_arrow_collapse_is_generic :
    -- it fires OFF the seam: node #4 is initial, not a zero object, yet to = 𝟙 (TC20)
    ∃ (h : Limits.IsInitial (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)),
      ¬ Limits.IsZero (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)
      ∧ h.to (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)
          = 𝟙 (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0) :=
  ZeroParadox.ZPH_MC1_TC20.collapse_fires_off_seam

/-- **The honest fence (capstone, content IN the statement).** The root-level seam (canonical μ→ν
comparison is an iso, governed by absence of a recursive position) and the node-#5 seam (arrow
coincidence at a zero object, governed by the zero-object universal property and itself generic) are
recorded side by side as DISTINCT phenomena in DISTINCT settings:

* root: `Function.Bijective canonicalCmp` for `constPF Unit`;
* node: the zero-object arrow coincidence `to = from`, which equals `to = 𝟙 = from` (TC20), a
  collapse that is generic to bare initial / bare terminal objects.

Both are true; neither is derived from the other in this file, and there is no map between the QPF
setting and the categorical setting here. Therefore "the polynomial-functor seam and the zero-object
seam are the SAME phenomenon" is a cross-setting modeling commitment / analogy, NOT a theorem. The
genuine new Lean content is the canonical-comparison iso; the unification is fenced. -/
theorem root_node_seam_no_identity :
    -- root-seam: canonical comparison is an iso for the no-recursive-position functor
    Function.Bijective (canonicalCmp : Fix (constPF Unit).Obj → Cofix (constPF Unit).Obj)
    ∧ -- node-seam: at the zero object the two universal arrows coincide ...
      (ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero).isInitial.to
          (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0)
        = (ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero).isTerminal.from
          (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0)
    ∧ -- ... but that coincidence is the generic identity collapse (TC20 deflation)
      (ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero).isInitial.to
          (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0)
        = 𝟙 (ZeroParadox.ZPH_HilbFunctor.fD_functor.obj 0) :=
  ⟨canonicalCmp_bijective,
   ZeroParadox.ZPH_MC1_TC20.seam_mu_eq_nu_arrow,
   ZeroParadox.ZPH_MC1_TC20.initial_endo_is_id
     (ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero).isInitial⟩

section PurityCheck
-- Measured footprint (lake build, v4.30.0-rc2): every result is
--   [propext, Classical.choice, Quot.sound]
-- the expected library-choice footprint. The `Classical.choice` enters through TC26's ν-side
-- (`cofixMk` / `root_seam`, the Mathlib M-type corecursion artifact) and the categorical seam
-- (`hilbert_bottom_isZero` / `ModuleCat ℂ`). It is a library dependency, not a new commitment of
-- this construction; the μ side of the comparison (`Fix.rec`) is choice-free in principle, as in
-- TC26's `fixEquiv`.
#print axioms canonicalCmp_hom
#print axioms canonicalCmp_unique
#print axioms canonicalCmp_eq_root_seam
#print axioms canonicalCmp_bijective
#print axioms seam_iff_no_recursive_position
#print axioms node_seam_arrow_collapse_is_generic
#print axioms root_node_seam_no_identity
end PurityCheck

end ZeroParadox.ZPH.TC38
