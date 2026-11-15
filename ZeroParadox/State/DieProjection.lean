import ZeroParadox.Die
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Orthogonal projection as a die motion: with an inner-product test on UP, landings forming a subspace with an orthogonal projection determine every value of UP; without the test they do not; strict isomorphism does not preserve the test, an inner-product-preserving one does

## Engineer's Take

A complete lit up tree and the actualized path through it are another level of being at right
angles to each other. I had to chase the dark as the choices were made at each node to see that.
The orthogonal projection is the lossy view the die uses when we go to a simpler carrier. We
should be able to tell it apart in the die. My question was whether that is a new slot, or an
argument being passed to an existing slot. That simplification action is going to be pretty
universal.

---
## Formal Overview (AI-assisted)
`UpOrthogonal` relates UP (`ZeroParadox/Die.lean`) to a real inner product, as `UpRaises` does to an
order. The orthogonal projection meets it (§ II); with it the landings determine every value of UP,
not its domain (§ III); without it an oblique projection has the same landings (§ IV); a `StrictIso`
need not carry the test, and one preserving the inner product does (§ V); the collapse (§ VI).
-/

set_option maxHeartbeats 400000

universe u

namespace ZeroParadox

open scoped InnerProductSpace

namespace Motion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### § I. The premise. Linear counterpart: Mathlib's
`LinearMap.IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`. -/

/-- `Statement:` for every `y ∈ up x` and every landing `z`, `x - y` is orthogonal to `z`.
    `Reading:` the inner product is an instance argument of this test, not of `Motion.up`. -/
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

/-! ### § III. With `UpOrthogonal`, the landings determine every value of UP -/

/-- `Statement:` if UP is orthogonal and the landings are exactly `K`, every value of `up x` is
    `K.starProjection x`. Proof: Mathlib's `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`;
    `up_idem` makes the value a landing. `Reading:` UP need not be linear or total here; for
    symmetric linear projections the counterpart is `LinearMap.IsSymmetricProjection.ext_iff`. -/
theorem starProjection_eq_of_upOrthogonal (M : Motion E) (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (ho : M.UpOrthogonal) (hK : ∀ z, M.IsLanding z ↔ z ∈ K)
    {x y : E} (hy : y ∈ M.up x) : K.starProjection x = y :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hK y).1 (M.up_idem x y hy))
    (fun w hw => ho x y hy w ((hK w).2 hw))

/-- `Statement:` with `UpOrthogonal`, landings exactly `K` and UP total, `up x` is
    `Part.some (K.starProjection x)` at every `x`. -/
theorem up_eq_starProjection_of_upOrthogonal (M : Motion E) (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] (ho : M.UpOrthogonal) (hK : ∀ z, M.IsLanding z ↔ z ∈ K)
    (ht : M.UpTotal) (x : E) : M.up x = Part.some (K.starProjection x) :=
  Part.eq_some_iff.2 (starProjection_eq_of_upOrthogonal M K ho hK (Part.get_mem (ht x)) ▸
    Part.get_mem (ht x))

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

/-- `Statement:` UP the identity defined only on `planeLine`, OVER empty. -/
noncomputable def partialLineMotion : Motion (EuclideanSpace ℝ (Fin 2)) where
  up x := ⟨x ∈ planeLine, fun _ => x⟩
  up_idem _ _ h := by obtain ⟨hx, rfl⟩ := h; exact ⟨hx, rfl⟩
  step _ _ := False

/-- `Statement:` CONTROL, § III fixes UP's values and not its domain: `partialLineMotion` and
    `orthoLineMotion` have the same landings and OVER, both meet `UpOrthogonal`, the first UP is not
    total, and the motions differ. -/
theorem upOrthogonal_values_not_domain :
    (∀ z, partialLineMotion.IsLanding z ↔ orthoLineMotion.IsLanding z) ∧
    partialLineMotion.step = orthoLineMotion.step ∧
    partialLineMotion.UpOrthogonal ∧ orthoLineMotion.UpOrthogonal ∧
    ¬ partialLineMotion.UpTotal ∧ partialLineMotion ≠ orthoLineMotion := by
  have h1 : planeE1 ∉ planeLine := fun h => by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) ha
    simp [planeE0, planeE1] at this
  refine ⟨fun z => ?_, rfl, ?_, Motion.upOrthogonal_ofStarProjection _ _, fun h => h1 (h planeE1),
    fun h => h1 ?_⟩
  · rw [orthoLineMotion, Motion.isLanding_ofStarProjection_iff]
    exact ⟨fun ⟨hz, _⟩ => hz, fun hz => ⟨hz, rfl⟩⟩
  · intro x y hy z _
    obtain ⟨_, hxy⟩ := hy
    rw [show y = x from hxy.symm, sub_self, inner_zero_left]
  · have : (partialLineMotion.up planeE1).Dom := by rw [h]; trivial
    exact this

/-! ### § V. The die's isomorphism does not see the angle
`Reading:` a real-plane counterpart of a fact for unital C*-algebras: every idempotent is similar to a
projection, and two projections are similar iff unitarily equivalent (Giordano and Sierakowski,
arXiv:1403.4385v2, Lemma 3.2, called well known there, citing Blackadar, *K-Theory for Operator
Algebras*, Props 4.6.2 and 4.6.5); `obliqueOrthoIso` is a similarity that is not unitary. -/

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

/-- `Statement:` an isometric strict isomorphism carries `UpOrthogonal`: if the forward map preserves
    the real inner product and `M` meets the test, `N` meets it. -/
theorem Motion.upOrthogonal_of_isometric_iso {E F : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] {M : Motion E}
    {N : Motion F} (e : Motion.StrictIso M N)
    (hinner : ∀ a b, ⟪e.hom.toFun a, e.hom.toFun b⟫_ℝ = ⟪a, b⟫_ℝ) (hM : M.UpOrthogonal) :
    N.UpOrthogonal := by
  have hsub : ∀ a b, e.hom.toFun (a - b) = e.hom.toFun a - e.hom.toFun b := fun a b => by
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
    simp only [inner_sub_left, inner_sub_right, hinner]
    rw [real_inner_comm a b]
    ring
  intro x y hy z hz
  obtain ⟨x, rfl⟩ : ∃ a, e.hom.toFun a = x := ⟨_, e.right_inv x⟩
  obtain ⟨z, rfl⟩ : ∃ a, e.hom.toFun a = z := ⟨_, e.right_inv z⟩
  rw [e.hom.map_up] at hy
  obtain ⟨y', hy', rfl⟩ := (Part.mem_map_iff _).1 hy
  have hz2 : e.hom.toFun z ∈ N.up (e.hom.toFun z) := hz
  rw [e.hom.map_up] at hz2
  obtain ⟨w, hw, hwz⟩ := (Part.mem_map_iff _).1 hz2
  obtain rfl : w = z := by rw [← e.left_inv w, ← e.left_inv z, hwz]
  rw [← hsub, hinner]
  exact hM _ y' hy' _ hw

/-! ### § VI. The collapse by the kernel of UP: the orthogonal instance and an oblique control
`Reading:` the general collapse is `Motion.collapseEquiv` (`ZeroParadox/Die.lean`) and needs no
inner product; here the inner product decides which points share a class (`collapses_differ`).
`Reading:` the linear counterparts are Mathlib's `Submodule.quotientEquivOfIsCompl` and
`Submodule.ker_starProjection` (`ker = Kᗮ`); `Submodule.ker_orthogonalProjectionOnto` is its
codomain-restricted form. -/

section Collapse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `Statement:` the classes of the kernel of `K.starProjection` are in bijection with `K`. -/
noncomputable def orthoCollapseEquiv (K : Submodule ℝ E) [K.HasOrthogonalProjection] :
    Quotient (Setoid.ker K.starProjection) ≃ K :=
  (Motion.collapseEquiv (r := K.starProjection)
      (fun x => congrArg (fun f : E →L[ℝ] E => f x) K.isIdempotentElem_starProjection)).trans
    { toFun := fun y => ⟨y.1, (Submodule.starProjection_eq_self_iff).1 y.2⟩
      invFun := fun y => ⟨y.1, (Submodule.starProjection_eq_self_iff).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `Statement:` `x` and `y` share a class of the kernel of `K.starProjection` iff `x - y ∈ Kᗮ`;
    both directions. -/
theorem ortho_classes (K : Submodule ℝ E) [K.HasOrthogonalProjection] (x y : E) :
    (Setoid.ker K.starProjection).r x y ↔ x - y ∈ Kᗮ := by
  show K.starProjection x = K.starProjection y ↔ _
  rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff]

end Collapse

/-- `Statement:` CONTROL, the classes of the kernel of `obliqueProj` are in bijection with
    `planeLine`, the line of `orthoCollapseEquiv planeLine`. -/
noncomputable def obliqueCollapseEquiv :
    Quotient (Setoid.ker obliqueProj) ≃ planeLine :=
  (Motion.collapseEquiv (r := obliqueProj) (fun v => by simp [obliqueProj, planeE0])).trans
    { toFun := fun y => ⟨y.1, (obliqueProj_eq_self_iff y.1).1 y.2⟩
      invFun := fun y => ⟨y.1, (obliqueProj_eq_self_iff y.1).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `Statement:` `planeE1` and `-planeE0` share a class of the kernel of `obliqueProj` and not of
    the kernel of `planeLine.starProjection`. -/
theorem collapses_differ :
    (Setoid.ker obliqueProj).r planeE1 (-planeE0) ∧
      ¬ (Setoid.ker planeLine.starProjection).r planeE1 (-planeE0) := by
  refine ⟨?_, ?_⟩
  · show obliqueProj planeE1 = obliqueProj (-planeE0)
    ext i; fin_cases i <;> simp [obliqueProj, planeE0, planeE1]
  · rw [ortho_classes]
    intro h
    have hm : planeE0 ∈ planeLine := Submodule.mem_span_singleton_self _
    have := Submodule.inner_right_of_mem_orthogonal hm h
    simp [planeE0, planeE1, EuclideanSpace.inner_single_left] at this

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
#print axioms Motion.up_eq_starProjection_of_upOrthogonal
#print axioms partialLineMotion
#print axioms upOrthogonal_values_not_domain
#print axioms Motion.upOrthogonal_of_isometric_iso
#print axioms orthoCollapseEquiv
#print axioms ortho_classes
#print axioms obliqueCollapseEquiv
#print axioms collapses_differ

end PurityCheck
