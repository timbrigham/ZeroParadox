import ZeroParadox.ZPH_PerronFrobenius
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 800000

/-!
# Reversible chains have real spectrum (genuine Hilbert / self-adjoint content)

A reversible Markov kernel (detailed balance w.r.t. a positive measure `μ`) gives a transfer operator that is
SELF-ADJOINT in the `μ`-weighted sesquilinear form `W x y = ∑ᵢ μᵢ⁻¹ · xᵢ · conj(yᵢ)`. Self-adjointness is
exactly detailed balance, term by term. A self-adjoint operator has REAL eigenvalues — derived elementarily:
`c·⟨v,v⟩ = ⟨Tv,v⟩ = ⟨v,Tv⟩ = c̄·⟨v,v⟩`, and `⟨v,v⟩ = ∑ |vᵢ|²/μᵢ > 0`, so `c = c̄`.

This is the genuine inner-product / self-adjointness content the cold audit found missing in the ℓ¹-spectral
bound: here the conjugate-symmetric form and self-adjointness do the work.

## Engineer's Take
This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ReversibleSpectrum

open Complex

variable {n : ℕ}

/-- The transfer operator on `Fin n → ℂ`: `(Top f x) k = ∑ⱼ (f j)(k) · xⱼ`. -/
noncomputable def Top (f : Fin n → PMF (Fin n)) (x : Fin n → ℂ) : Fin n → ℂ :=
  fun k => ∑ j, (((f j) k).toReal : ℂ) * x j

/-- The `μ`-weighted sesquilinear form `W x y = ∑ᵢ μᵢ⁻¹ · xᵢ · conj(yᵢ)`. -/
noncomputable def Wform (μ : Fin n → ℝ) (x y : Fin n → ℂ) : ℂ :=
  ∑ i, ((μ i : ℂ))⁻¹ * x i * (starRingEnd ℂ) (y i)

/-- Reversibility / detailed balance: `μⱼ · P(j→k) = μₖ · P(k→j)`. -/
def Reversible (f : Fin n → PMF (Fin n)) (μ : Fin n → ℝ) : Prop :=
  ∀ k j, (μ j) * ((f j) k).toReal = (μ k) * ((f k) j).toReal

/-- `W` is ℂ-linear in the first slot. -/
lemma Wform_smul_left (μ : Fin n → ℝ) (c : ℂ) (x y : Fin n → ℂ) :
    Wform μ (c • x) y = c * Wform μ x y := by
  simp only [Wform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `W` is conjugate-linear in the second slot. -/
lemma Wform_smul_right (μ : Fin n → ℝ) (c : ℂ) (x y : Fin n → ℂ) :
    Wform μ x (c • y) = (starRingEnd ℂ) c * Wform μ x y := by
  simp only [Wform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Self-adjointness from detailed balance.** -/
lemma Wform_selfadjoint (f : Fin n → PMF (Fin n)) (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (hrev : Reversible f μ) (v : Fin n → ℂ) : Wform μ (Top f v) v = Wform μ v (Top f v) := by
  have hL : Wform μ (Top f v) v
      = ∑ k, ∑ j, ((μ k : ℂ))⁻¹ * (((f j) k).toReal : ℂ) * v j * (starRingEnd ℂ) (v k) := by
    simp only [Wform, Top]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hR : Wform μ v (Top f v)
      = ∑ k, ∑ j, ((μ k : ℂ))⁻¹ * (((f j) k).toReal : ℂ) * v k * (starRingEnd ℂ) (v j) := by
    simp only [Wform, Top]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, Complex.conj_ofReal]; ring
  rw [hL, hR]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : (μ k : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hμ k)
  have h2 : (μ j : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hμ j)
  have hb : (μ j : ℂ) * (((f j) k).toReal : ℂ) = (μ k : ℂ) * (((f k) j).toReal : ℂ) := by
    exact_mod_cast hrev k j
  have hkey : (μ k : ℂ)⁻¹ * (((f j) k).toReal : ℂ) = (μ j : ℂ)⁻¹ * (((f k) j).toReal : ℂ) := by
    field_simp
    linear_combination hb
  rw [hkey]

/-- `W v v` is a positive real (hence nonzero) when `v ≠ 0` and `μ > 0`. -/
lemma Wform_self_ne_zero (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i) {v : Fin n → ℂ} (hv : v ≠ 0) :
    Wform μ v v ≠ 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push_neg at h; exact hv (funext h)
  have hreal : Wform μ v v = ((∑ i, (μ i)⁻¹ * Complex.normSq (v i) : ℝ) : ℂ) := by
    rw [Wform, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, Complex.mul_conj, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [hreal, Ne, Complex.ofReal_eq_zero]
  refine ne_of_gt (Finset.sum_pos' (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩)
  · exact mul_nonneg (le_of_lt (inv_pos.mpr (hμ i))) (Complex.normSq_nonneg _)
  · exact mul_pos (inv_pos.mpr (hμ i₀)) (Complex.normSq_pos.mpr hi₀)

/-- **Reversible ⟹ real spectrum.** Every eigenvalue of the transfer operator of a reversible kernel is
    real. -/
theorem reversible_real_spectrum (f : Fin n → PMF (Fin n)) (μ : Fin n → ℝ) (hμ : ∀ i, 0 < μ i)
    (hrev : Reversible f μ) {c : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (hc : Top f v = c • v) :
    c.im = 0 := by
  have hsa := Wform_selfadjoint f μ hμ hrev v
  rw [hc, Wform_smul_left, Wform_smul_right] at hsa
  have hne := Wform_self_ne_zero μ hμ hv
  have : c = (starRingEnd ℂ) c := mul_right_cancel₀ hne hsa
  exact Complex.conj_eq_iff_im.mp this.symm

end ZeroParadox.ReversibleSpectrum

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ReversibleSpectrum
#print axioms reversible_real_spectrum
end PurityCheck
