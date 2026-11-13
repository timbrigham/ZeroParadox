import ZeroParadox.Die
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Orthogonal projection as a die motion: the inner product as an argument to UP

## Engineer's Take

---
## Formal Overview (AI-assisted)
`UpOrthogonal` relates UP (`ZeroParadox/Die.lean`) to a real inner product, as `UpRaises` does to an
order. The orthogonal projection onto `K` meets it (§ II); with it the landings determine UP (§ III);
without it an oblique projection has the same landings and a different UP (§ IV); a `StrictIso` joins
the two, so the predicate is not invariant under the die's isomorphism (§ V).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open scoped InnerProductSpace

namespace Motion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### § I. The premise. Linear counterpart: Mathlib's
`LinearMap.IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`. -/

/-- `Statement:` for every `y ∈ up x` and every landing `z`, `x - y` is orthogonal to `z`.
    `Reading:` the inner product is an argument, as the order is in `UpRaises`, not a field. -/
def UpOrthogonal (M : Motion E) : Prop :=
  ∀ x y, y ∈ M.up x → ∀ z, M.IsLanding z → ⟪x - y, z⟫_ℝ = 0

/-! ### § II. The orthogonal projection is a member -/

/-- `Statement:` the orthogonal projection onto `K` as a total UP, with OVER `s`. -/
noncomputable def ofStarProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (s : E → E → Prop) : Motion E :=
  ofTotal K.starProjection
    (fun x => congrArg (fun f : E →L[ℝ] E => f x) K.isIdempotentElem_starProjection) s

/-- `Statement:` the landings of `ofStarProjection K s` are exactly the points of `K`. -/
theorem isLanding_ofStarProjection_iff (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (s : E → E → Prop) (y : E) : (ofStarProjection K s).IsLanding y ↔ y ∈ K := by
  show y ∈ Part.some (K.starProjection y) ↔ _
  rw [Part.mem_some_iff, eq_comm, Submodule.starProjection_eq_self_iff]

/-- `Statement:` the orthogonal projection onto `K` meets `UpOrthogonal`. -/
theorem upOrthogonal_ofStarProjection (K : Submodule ℝ E) [K.HasOrthogonalProjection]
    (s : E → E → Prop) : (ofStarProjection K s).UpOrthogonal := by
  intro x y hy z hz
  rw [isLanding_ofStarProjection_iff K s z] at hz
  obtain rfl : y = K.starProjection x := Part.mem_some_iff.1 hy
  exact Submodule.starProjection_inner_eq_zero x z hz

/-! ### § III. With `UpOrthogonal`, the landings determine UP -/

/-- `Statement:` if UP is orthogonal and the landings are exactly `K`, every value of `up x` is
    `K.starProjection x`. Proof: Mathlib's `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`;
    `up_idem` makes the value a landing. `Reading:` UP need not be linear or total here; for
    symmetric linear projections the counterpart is `LinearMap.IsSymmetricProjection.ext_iff`. -/
theorem starProjection_eq_of_upOrthogonal (M : Motion E) (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (ho : M.UpOrthogonal) (hK : ∀ z, M.IsLanding z ↔ z ∈ K)
    {x y : E} (hy : y ∈ M.up x) : K.starProjection x = y :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hK y).1 (M.up_idem x y hy))
    (fun w hw => ho x y hy w ((hK w).2 hw))

end Motion

/-! ### § IV. Without it, they do not: an oblique projection onto the same line -/

/-- `Statement:` the first standard basis vector of `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def planeE0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- `Statement:` the second standard basis vector of `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def planeE1 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

/-- `Statement:` the line spanned by `planeE0`. -/
noncomputable def planeLine : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) := ℝ ∙ planeE0

/-- `Statement:` the projection onto `planeLine` along the span of `planeE0 + planeE1`. -/
noncomputable def obliqueProj (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  (v 0 - v 1) • planeE0

/-- `Statement:` UP `obliqueProj`, OVER empty. -/
noncomputable def obliqueMotion : Motion (EuclideanSpace ℝ (Fin 2)) :=
  Motion.ofTotal obliqueProj (fun v => by simp [obliqueProj, planeE0]) (fun _ _ => False)

/-- `Statement:` `v` is fixed by `obliqueProj` iff `v ∈ planeLine`. -/
theorem obliqueProj_eq_self_iff (v : EuclideanSpace ℝ (Fin 2)) : obliqueProj v = v ↔ v ∈ planeLine := by
  constructor
  · intro h
    rw [← h, planeLine]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro h
    rw [planeLine, Submodule.mem_span_singleton] at h
    obtain ⟨a, rfl⟩ := h
    simp [obliqueProj, planeE0]

/-- `Statement:` the orthogonal projection onto `planeLine` is `v ↦ v 0 • planeE0`. -/
theorem starProjection_planeLine (v : EuclideanSpace ℝ (Fin 2)) :
    planeLine.starProjection v = v 0 • planeE0 := by
  rw [planeLine, Submodule.starProjection_singleton]
  simp [planeE0, EuclideanSpace.inner_single_left, EuclideanSpace.single, PiLp.norm_single]

/-- `Statement:` UP the orthogonal projection onto `planeLine`, OVER empty. -/
noncomputable def orthoLineMotion : Motion (EuclideanSpace ℝ (Fin 2)) :=
  Motion.ofStarProjection planeLine (fun _ _ => False)

/-- `Statement:` both directions: the oblique and orthogonal motions have the same landings, the
    same OVER, both UP legs are total, the motions differ, the orthogonal one meets `UpOrthogonal`
    and the oblique one does not. -/
theorem landings_not_determine_up :
    (∀ z, obliqueMotion.IsLanding z ↔ orthoLineMotion.IsLanding z) ∧
    obliqueMotion.step = orthoLineMotion.step ∧
    obliqueMotion.UpTotal ∧ orthoLineMotion.UpTotal ∧
    obliqueMotion ≠ orthoLineMotion ∧
    orthoLineMotion.UpOrthogonal ∧ ¬ obliqueMotion.UpOrthogonal := by
  have hland : ∀ z, obliqueMotion.IsLanding z ↔ z ∈ planeLine := fun z => by
    show z ∈ Part.some (obliqueProj z) ↔ _
    rw [Part.mem_some_iff, eq_comm, obliqueProj_eq_self_iff]
  refine ⟨fun z => by rw [hland, orthoLineMotion, Motion.isLanding_ofStarProjection_iff],
    rfl, fun _ => trivial, fun _ => trivial, fun h => ?_,
    Motion.upOrthogonal_ofStarProjection _ _, fun h => ?_⟩
  · have hu : Part.some (obliqueProj planeE1) = Part.some (planeLine.starProjection planeE1) :=
      congrArg (fun M : Motion (EuclideanSpace ℝ (Fin 2)) => M.up planeE1) h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) (Part.some_injective hu)
    simp [obliqueProj, starProjection_planeLine, planeE0, planeE1] at this
  · have := h (planeE0 + planeE1) (obliqueProj (planeE0 + planeE1)) (Part.mem_some _) planeE0
      ((hland planeE0).2 (Submodule.mem_span_singleton_self _))
    simp [obliqueProj, planeE0, planeE1, EuclideanSpace.inner_single_right] at this

/-! ### § V. The die's isomorphism does not see the angle -/

/-- `Statement:` a strict isomorphism of motions from `obliqueMotion` to `orthoLineMotion`, by the
    linear map `v ↦ (v 0 - v 1) • planeE0 + v 1 • planeE1`. -/
noncomputable def obliqueOrthoIso : Motion.StrictIso obliqueMotion orthoLineMotion where
  hom := ⟨fun v => (v 0 - v 1) • planeE0 + v 1 • planeE1, fun h => h.elim, fun x => by
    show Part.some (planeLine.starProjection _) = (Part.some (obliqueProj x)).map _
    rw [Part.map_some, starProjection_planeLine]
    congr 1
    ext i; fin_cases i <;> simp [obliqueProj, planeE0, planeE1]⟩
  inv := ⟨fun w => (w 0 + w 1) • planeE0 + w 1 • planeE1, fun h => h.elim, fun y => by
    show Part.some (obliqueProj _) = (Part.some (planeLine.starProjection y)).map _
    rw [Part.map_some, starProjection_planeLine]
    congr 1
    ext i; fin_cases i <;> simp [obliqueProj, planeE0, planeE1]⟩
  left_inv v := by ext i; fin_cases i <;> simp [planeE0, planeE1]
  right_inv w := by ext i; fin_cases i <;> simp [planeE0, planeE1]

/-- `Statement:` the map of `obliqueOrthoIso` does not preserve the norm. -/
theorem obliqueOrthoIso_not_norm_preserving :
    ∃ v, ‖obliqueOrthoIso.hom.toFun v‖ ≠ ‖v‖ := by
  refine ⟨planeE0 + planeE1, fun h => ?_⟩
  have h1 : obliqueOrthoIso.hom.toFun (planeE0 + planeE1) = planeE1 := by
    show _ • planeE0 + _ • planeE1 = planeE1
    ext i; fin_cases i <;> simp [planeE0, planeE1]
  rw [h1] at h
  have h2 : ‖planeE1‖ = 1 := by simp [planeE1, EuclideanSpace.single, PiLp.norm_single]
  have h3 : ‖planeE0 + planeE1‖ ^ 2 = 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    simp [planeE0, planeE1, Fin.sum_univ_two]
    norm_num
  rw [← h, h2] at h3
  norm_num at h3

/-- `Statement:` `UpOrthogonal` is not invariant under `Motion.StrictIso`: a strictly isomorphic
    pair, one a member and one not. -/
theorem upOrthogonal_not_iso_invariant :
    ∃ M N : Motion (EuclideanSpace ℝ (Fin 2)),
      Nonempty (Motion.StrictIso M N) ∧ N.UpOrthogonal ∧ ¬ M.UpOrthogonal :=
  ⟨obliqueMotion, orthoLineMotion, ⟨obliqueOrthoIso⟩, landings_not_determine_up.2.2.2.2.2.1,
    landings_not_determine_up.2.2.2.2.2.2⟩

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms Motion.UpOrthogonal
#print axioms Motion.ofStarProjection
#print axioms Motion.isLanding_ofStarProjection_iff
#print axioms Motion.upOrthogonal_ofStarProjection
#print axioms Motion.starProjection_eq_of_upOrthogonal
#print axioms planeE0
#print axioms planeE1
#print axioms planeLine
#print axioms obliqueProj
#print axioms obliqueProj_eq_self_iff
#print axioms starProjection_planeLine
#print axioms obliqueMotion
#print axioms orthoLineMotion
#print axioms landings_not_determine_up
#print axioms obliqueOrthoIso
#print axioms obliqueOrthoIso_not_norm_preserving
#print axioms upOrthogonal_not_iso_invariant

end PurityCheck
