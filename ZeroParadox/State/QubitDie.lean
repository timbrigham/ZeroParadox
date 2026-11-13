import ZeroParadox.State.DieProjection
import Mathlib.Tactic

/-!
# The qubit as a die: measurement is an orthogonal-projection motion, the bit flip is an isometric strict isomorphism between the two measurements, and on lines the bit flip and the orthocomplement agree at the basis lines and differ at |0⟩ + |1⟩

## Engineer's Take

---
## Formal Overview (AI-assisted)
ℂ² is a real inner-product space by a local `InnerProductSpace.complexToReal`. Measurement onto a
basis line is a die motion meeting `UpOrthogonal` (`ZeroParadox/State/DieProjection.lean`) (§ I).
σ_x (`LinearIsometryEquiv.piLpCongrLeft` at the swap) is a strict isomorphism of the two measurements
carrying the test (§ II); on lines it agrees with the orthocomplement at both basis lines (§ III).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open scoped InnerProductSpace

/-! ### § I. Measurement as a die motion -/

/-- `Statement:` the qubit state space ℂ², as `EuclideanSpace ℂ (Fin 2)`. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- `Statement:` the real inner product on `Qubit`, the real part of the complex one; local. -/
noncomputable local instance : InnerProductSpace ℝ Qubit := InnerProductSpace.complexToReal

/-- `Statement:` no diamond: the local instance's real normed-space structure is the one `PiLp`
    already supplies, at reducible-and-instances transparency. -/
example : (InnerProductSpace.toNormedSpace : NormedSpace ℝ Qubit) = PiLp.normedSpace 2 ℝ _ := by
  with_reducible_and_instances rfl

/-- `Statement:` the basis ket `|0⟩`. -/
noncomputable def qubitKet0 : Qubit := EuclideanSpace.single 0 1

/-- `Statement:` the basis ket `|1⟩`. -/
noncomputable def qubitKet1 : Qubit := EuclideanSpace.single 1 1

/-- `Statement:` the ket `|0⟩ + |1⟩`. -/
noncomputable def qubitKetPlus : Qubit := qubitKet0 + qubitKet1

/-- `Statement:` the complex line through `|0⟩`, as a real subspace. -/
noncomputable def qubitLine0 : Submodule ℝ Qubit := (ℂ ∙ qubitKet0).restrictScalars ℝ

/-- `Statement:` the complex line through `|1⟩`, as a real subspace. -/
noncomputable def qubitLine1 : Submodule ℝ Qubit := (ℂ ∙ qubitKet1).restrictScalars ℝ

/-- `Statement:` measurement onto a real subspace `K`: UP the orthogonal projection, OVER empty. -/
noncomputable def qubitMeasure (K : Submodule ℝ Qubit) [K.HasOrthogonalProjection] : Motion Qubit :=
  Motion.ofStarProjection K (fun _ _ => False)

/-- `Statement:` the landings of `qubitMeasure K` are exactly the points of `K`. -/
theorem isLanding_qubitMeasure_iff (K : Submodule ℝ Qubit) [K.HasOrthogonalProjection] (y : Qubit) :
    (qubitMeasure K).IsLanding y ↔ y ∈ K :=
  Motion.isLanding_ofStarProjection_iff K _ y

/-- `Statement:` `qubitMeasure K` meets `UpOrthogonal`. -/
theorem upOrthogonal_qubitMeasure (K : Submodule ℝ Qubit) [K.HasOrthogonalProjection] :
    (qubitMeasure K).UpOrthogonal :=
  Motion.upOrthogonal_ofStarProjection K _

/-! ### § II. The bit flip σ_x -/

/-- `Statement:` σ_x, the coordinate swap, as Mathlib's complex linear isometry equivalence. -/
noncomputable def bitFlip : Qubit ≃ₗᵢ[ℂ] Qubit :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.swap 0 1)

/-- `Statement:` `bitFlip v` at `i` is `v` at the swapped index. -/
theorem bitFlip_apply (v : Qubit) (i : Fin 2) : bitFlip v i = v (Equiv.swap 0 1 i) := rfl

/-- `Statement:` σ_x is an involution. -/
theorem bitFlip_bitFlip (v : Qubit) : bitFlip (bitFlip v) = v := by
  ext i; fin_cases i <;> simp [bitFlip_apply]

/-- `Statement:` σ_x preserves the real inner product. -/
theorem bitFlip_real_inner (a b : Qubit) : ⟪bitFlip a, bitFlip b⟫_ℝ = ⟪a, b⟫_ℝ := by
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, LinearIsometryEquiv.inner_map_map]

/-- `Statement:` σ_x sends `|0⟩` to `|1⟩`. -/
theorem bitFlip_ket0 : bitFlip qubitKet0 = qubitKet1 := by
  unfold bitFlip qubitKet0 qubitKet1
  rw [EuclideanSpace.piLpCongrLeft_single, Equiv.swap_apply_left]

/-- `Statement:` σ_x sends `|1⟩` to `|0⟩`. -/
theorem bitFlip_ket1 : bitFlip qubitKet1 = qubitKet0 := by
  unfold bitFlip qubitKet0 qubitKet1
  rw [EuclideanSpace.piLpCongrLeft_single, Equiv.swap_apply_right]

/-- `Statement:` σ_x after the projection onto `qubitLine0` is the projection onto `qubitLine1` after
    σ_x. -/
theorem bitFlip_starProjection (x : Qubit) :
    bitFlip (qubitLine0.starProjection x) = qubitLine1.starProjection (bitFlip x) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · obtain ⟨c, hc⟩ : ∃ c : ℂ, c • qubitKet0 = qubitLine0.starProjection x :=
      Submodule.mem_span_singleton.1 (qubitLine0.starProjection_apply_mem x)
    rw [qubitLine1, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
    exact ⟨c, by rw [← hc, map_smul, bitFlip_ket0]⟩
  · intro w hw
    rw [qubitLine1, Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    have hw' : bitFlip (c • qubitKet1) ∈ qubitLine0 := by
      rw [qubitLine0, Submodule.restrictScalars_mem, Submodule.mem_span_singleton]
      exact ⟨c, by rw [map_smul, bitFlip_ket1]⟩
    have := Submodule.starProjection_inner_eq_zero (K := qubitLine0) x _ hw'
    rw [← map_sub, ← bitFlip_bitFlip (c • qubitKet1), bitFlip_real_inner]
    exact this

/-- `Statement:` σ_x as a strict isomorphism from measure-`|0⟩` to measure-`|1⟩`. -/
noncomputable def bitFlipIso : Motion.StrictIso (qubitMeasure qubitLine0) (qubitMeasure qubitLine1) where
  hom := ⟨bitFlip, fun h => h.elim, fun x => by
    show Part.some (qubitLine1.starProjection (bitFlip x)) =
      (Part.some (qubitLine0.starProjection x)).map bitFlip
    rw [Part.map_some, bitFlip_starProjection]⟩
  inv := ⟨bitFlip, fun h => h.elim, fun y => by
    show Part.some (qubitLine0.starProjection (bitFlip y)) =
      (Part.some (qubitLine1.starProjection y)).map bitFlip
    rw [Part.map_some, ← bitFlip_bitFlip (qubitLine0.starProjection (bitFlip y)),
      bitFlip_starProjection, bitFlip_bitFlip]⟩
  left_inv := bitFlip_bitFlip
  right_inv := bitFlip_bitFlip

/-- `Statement:` the test, carried by `bitFlipIso` through `Motion.upOrthogonal_of_isometric_iso`. -/
theorem upOrthogonal_qubitMeasure_line1_of_bitFlip : (qubitMeasure qubitLine1).UpOrthogonal :=
  Motion.upOrthogonal_of_isometric_iso bitFlipIso bitFlip_real_inner
    (upOrthogonal_qubitMeasure qubitLine0)

/-! ### § III. σ_x-image and orthocomplement on complex lines -/

/-- `Statement:` the orthocomplement of the line through `|0⟩` is the line through `|1⟩`. -/
theorem qubit_poles_flip_eq_perp : (ℂ ∙ qubitKet0)ᗮ = ℂ ∙ qubitKet1 := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v 1, ?_⟩
    simp [qubitKet0, EuclideanSpace.inner_single_left] at hv
    ext i; fin_cases i <;> simp [qubitKet1, hv]
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [qubitKet0, qubitKet1, EuclideanSpace.inner_single_left]

/-- `Statement:` the orthocomplement of the line through `|1⟩` is the line through `|0⟩`. -/
theorem qubit_poles_flip_eq_perp' : (ℂ ∙ qubitKet1)ᗮ = ℂ ∙ qubitKet0 := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0, ?_⟩
    simp [qubitKet1, EuclideanSpace.inner_single_left] at hv
    ext i; fin_cases i <;> simp [qubitKet0, hv]
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [qubitKet0, qubitKet1, EuclideanSpace.inner_single_left]

/-- `Statement:` σ_x fixes `|0⟩ + |1⟩`. -/
theorem qubit_flip_fixes_plus : bitFlip qubitKetPlus = qubitKetPlus := by
  rw [qubitKetPlus, map_add, bitFlip_ket0, bitFlip_ket1, add_comm]

/-- `Statement:` `|0⟩ + |1⟩` is not in the orthocomplement of its own line. -/
theorem qubit_perp_moves_plus : qubitKetPlus ∉ (ℂ ∙ qubitKetPlus)ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero]
  intro h
  have := congrArg (fun v : Qubit => v 0) h
  simp [qubitKetPlus, qubitKet0, qubitKet1] at this

/-- `Statement:` both directions on lines: at `|0⟩` and at `|1⟩` the σ_x-image of the line equals its
    orthocomplement; at `|0⟩ + |1⟩` the σ_x-image is the line itself and the orthocomplement is not. -/
theorem qubit_flip_perp_agree_at_poles :
    (ℂ ∙ qubitKet0).map bitFlip.toLinearEquiv.toLinearMap = ℂ ∙ qubitKet1 ∧
    (ℂ ∙ qubitKet0)ᗮ = ℂ ∙ qubitKet1 ∧
    (ℂ ∙ qubitKet1).map bitFlip.toLinearEquiv.toLinearMap = ℂ ∙ qubitKet0 ∧
    (ℂ ∙ qubitKet1)ᗮ = ℂ ∙ qubitKet0 ∧
    (ℂ ∙ qubitKetPlus).map bitFlip.toLinearEquiv.toLinearMap = ℂ ∙ qubitKetPlus ∧
    (ℂ ∙ qubitKetPlus)ᗮ ≠ ℂ ∙ qubitKetPlus := by
  have hmap : ∀ v : Qubit, (ℂ ∙ v).map bitFlip.toLinearEquiv.toLinearMap = ℂ ∙ bitFlip v :=
    fun v => by rw [Submodule.map_span, Set.image_singleton]; rfl
  refine ⟨by rw [hmap, bitFlip_ket0], qubit_poles_flip_eq_perp, by rw [hmap, bitFlip_ket1],
    qubit_poles_flip_eq_perp', by rw [hmap, qubit_flip_fixes_plus], fun h => ?_⟩
  apply qubit_perp_moves_plus
  rw [h]
  exact Submodule.mem_span_singleton_self _

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms Qubit
#print axioms qubitKet0
#print axioms qubitKet1
#print axioms qubitKetPlus
#print axioms qubitLine0
#print axioms qubitLine1
#print axioms qubitMeasure
#print axioms isLanding_qubitMeasure_iff
#print axioms upOrthogonal_qubitMeasure
#print axioms bitFlip
#print axioms bitFlip_apply
#print axioms bitFlip_bitFlip
#print axioms bitFlip_real_inner
#print axioms bitFlip_ket0
#print axioms bitFlip_ket1
#print axioms bitFlip_starProjection
#print axioms bitFlipIso
#print axioms upOrthogonal_qubitMeasure_line1_of_bitFlip
#print axioms qubit_poles_flip_eq_perp
#print axioms qubit_poles_flip_eq_perp'
#print axioms qubit_flip_fixes_plus
#print axioms qubit_perp_moves_plus
#print axioms qubit_flip_perp_agree_at_poles

end PurityCheck
