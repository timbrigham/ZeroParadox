-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — TC38: the seam is NOT a colimit (coproduct) apex over the μ-bottoms

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This is the colimit/μ-direction sharpening of the TC18/TC27 "two-sided connector" deflation.
TC27 built a single cross-category map #4 → #5. A genuine *tree connector* on the μ side would
need more: the seam #5 (`fD_functor.obj 0`, the zero object of `ModuleCat ℂ`) would have to be the
**colimit** — concretely the coproduct — of the μ-side bottoms, receiving a *universal* cocone FROM
them. This file pre-registers and confirms that this fails.

**The load-bearing obstruction (`seam_not_mu_colimit_apex`).** In `ModuleCat ℂ`, take the two-object
diagram `{fD_functor.obj 1, fD_functor.obj 1}` (two copies of the 1-dimensional nonzero state space —
the simplest nonzero μ-side leaves transported into the seam's ambient). No binary cofan over this
diagram with apex the zero object `fD_functor.obj 0` is a colimit. Reason, fully in the proof: if such
a cofan `c` were `IsColimit`, its left injection `inl : fD.obj 1 ⟶ fD.obj 0` is forced to be the zero
map (the target is a zero object), so the universal factorization of the pair `(𝟙, 0)` would give
`𝟙 (fD.obj 1) = inl ≫ desc = 0`, making `fD.obj 1` a zero object — contradicting that `StateSpace 1`
is nontrivial. So the seam can receive at most the trivial self-cocone, not a universal cocone from
nonzero μ-bottoms.

**The honest GO companion (`seam_selfcoproduct_collapse`).** The seam's only genuine colimit role is
the vacuous one: the coproduct of the zero object with itself is again the zero object. We witness
`IsColimit` of the binary cofan `Z ← Z → Z` with apex `Z = fD.obj 0` (every leg the zero map). This
is the TC25-flavored collapse `Z ⊔ Z ≅ Z`: a real `IsColimit`, but over a diagram of zero objects,
so it carries no connector content from the μ-side leaves.

**Why this is a NO-GO for the tree hypothesis.** A μ-side colimit connector must be universal *over the
nonzero leaves*. The seam is universal only over (copies of) itself. So the colimit-direction analog of
the cross-root obstruction holds: #5's colimit role is confined to its own category and to the trivial
self-cocone — it is not a μ-side coproduct apex over #1/#4.

**Honest fence.** The Lean content is exactly: (1) no `IsColimit` binary cofan over two nonzero copies
of `fD.obj 1` has the zero object as apex; (2) the all-zero self-cofan over the zero object IS a colimit.
The reading "this confirms the seam is not a genuine μ-side tree connector" is the framework's
interpretation of that pair; #1 (ℕ-order-initial) and #4 (Kleisli `Fin 0`) are not literally objects of
`ModuleCat ℂ`, so "transported μ-bottoms" is realized here by their nonzero `ModuleCat ℂ` proxies
(`fD.obj 1`), which is the strongest honest formalization of "the seam cannot be their coproduct".
-/

namespace ZeroParadox.ZPH_MC1_TC40

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPD ZeroParadox.ZPH_HilbFunctor

/-- The seam node is a zero object of `ModuleCat ℂ` (reuse of `hilbert_bottom_isZero`). -/
theorem seam_isZero : IsZero (fD_functor.obj 0) :=
  ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero

/-- The transported μ-side leaf `fD_functor.obj 1 = StateSpace 1` is **not** a zero object:
    `EuclideanSpace ℂ (Fin 1)` is nontrivial, so it is not subsingleton. This is what makes the
    coproduct of two copies unable to collapse to the zero object. -/
theorem leaf_not_isZero : ¬ IsZero (fD_functor.obj 1) := by
  intro h
  have hsub : Subsingleton (StateSpace 1) := by
    have := ModuleCat.subsingleton_of_isZero h
    simpa [fD_functor] using this
  -- StateSpace 1 = EuclideanSpace ℂ (Fin 1) is nontrivial
  set w : StateSpace 1 := WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℂ)) with hw
  have hne : (0 : StateSpace 1) ≠ w := by
    intro hcontra
    have hcoord := congrArg (fun v : StateSpace 1 => v.ofLp ⟨0, by norm_num⟩) hcontra
    simp [hw] at hcoord
  exact hne (Subsingleton.elim _ _)

/-- **TC38 NO-GO (load-bearing).** The seam `fD_functor.obj 0` (zero object) is NOT a colimit apex
    over the two-object μ-side diagram `{fD_functor.obj 1, fD_functor.obj 1}`: no binary cofan over
    two copies of the nonzero leaf with apex the zero object is an `IsColimit`. The seam cannot be the
    coproduct of (transported) nonzero μ-bottoms. -/
theorem seam_not_mu_colimit_apex
    (c : BinaryCofan (fD_functor.obj 1) (fD_functor.obj 1))
    (hpt : c.pt = fD_functor.obj 0) :
    IsEmpty (IsColimit c) := by
  refine ⟨fun hc => ?_⟩
  -- The apex is a zero object.
  have hZ : IsZero c.pt := by rw [hpt]; exact seam_isZero
  -- The left injection into a zero object is the zero map.
  have hinl : c.inl = 0 := hZ.eq_of_tgt _ _
  -- Universal factorization of the pair (𝟙, 0).
  set d : BinaryCofan (fD_functor.obj 1) (fD_functor.obj 1) :=
    BinaryCofan.mk (𝟙 (fD_functor.obj 1)) (0 : fD_functor.obj 1 ⟶ fD_functor.obj 1) with hd
  have hfac : c.inl ≫ hc.desc d = d.inl := hc.fac d ⟨WalkingPair.left⟩
  rw [hinl] at hfac
  simp only [zero_comp] at hfac
  -- d.inl = 𝟙, so 𝟙 = 0, forcing the leaf to be a zero object.
  have hid : (𝟙 (fD_functor.obj 1)) = 0 := by
    rw [hd] at hfac; simpa using hfac.symm
  exact leaf_not_isZero ((IsZero.iff_id_eq_zero (fD_functor.obj 1)).mpr hid)

/-- **Honest GO companion.** The seam's only genuine colimit role: the coproduct of the zero object
    with itself is the zero object. The all-zero binary cofan over `(Z, Z)` with apex `Z = fD.obj 0`
    IS a colimit. A real `IsColimit`, but over zero objects — carrying no μ-side connector content
    (the TC25 self-collapse `Z ⊔ Z ≅ Z`). -/
noncomputable def seam_selfcoproduct_collapse :
    IsColimit (BinaryCofan.mk (0 : fD_functor.obj 0 ⟶ fD_functor.obj 0)
                              (0 : fD_functor.obj 0 ⟶ fD_functor.obj 0)) := by
  have hZ : IsZero (fD_functor.obj 0) := seam_isZero
  refine BinaryCofan.IsColimit.mk _ (fun {T} _ _ => hZ.to_ T) ?_ ?_ ?_
  · intro T f g; exact hZ.eq_of_src _ _
  · intro T f g; exact hZ.eq_of_src _ _
  · intro T f g m _ _; exact hZ.eq_of_src _ _

/-- The full TC38 result in one statement: the seam is a zero object, the transported μ-leaf is not,
    and consequently no zero-apex colimit cofan exists over two nonzero μ-leaves — while the
    self-collapse cofan over the zero object IS a colimit. The pair = "seam is not a μ-side coproduct
    connector, only a trivial self-cocone." -/
theorem tc38_seam_not_colimit_connector :
    IsZero (fD_functor.obj 0)
    ∧ ¬ IsZero (fD_functor.obj 1)
    ∧ (∀ (c : BinaryCofan (fD_functor.obj 1) (fD_functor.obj 1)),
        c.pt = fD_functor.obj 0 → IsEmpty (IsColimit c)) :=
  ⟨seam_isZero, leaf_not_isZero, seam_not_mu_colimit_apex⟩

end ZeroParadox.ZPH_MC1_TC40

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through the `ModuleCat` / `EuclideanSpace` / `StateSpace`
library carried from ZP-D. A library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC40

#print axioms seam_isZero
#print axioms leaf_not_isZero
#print axioms seam_not_mu_colimit_apex
#print axioms seam_selfcoproduct_collapse
#print axioms tc38_seam_not_colimit_connector

end PurityCheck
