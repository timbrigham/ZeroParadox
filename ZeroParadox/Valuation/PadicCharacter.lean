-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): p-adic additive characters on ℤ_p built through the finite quotient ℤ_p → ZMod(pⁿ), and the orthogonality integral ∫ χ dHaar = 0 for a nontrivial character — the Fourier-free "crane" that underlies the Kozyrev-wavelet eigenfunctions of the Vladimirov operator. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicHaar
import Mathlib.Algebra.Group.AddChar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# p-adic additive characters and their orthogonality on ℤ_p

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Builds the **p-adic additive characters** on `ℤ_p` that the Vladimirov operator's genuine eigenfunctions
(Kozyrev wavelets) are made from — without constructing the full `ℚ_p` Fourier transform. The key
observation: the Kozyrev-relevant character `χ_p(p⁻ⁿ · x)` restricted to `ℤ_p` is exactly
`φ ∘ toZModPow n`, where `toZModPow n : ℤ_p →+* ZMod(pⁿ)` is the residue map (built in
`PadicHaar`) and `φ` is an additive character of the *finite* group `ZMod(pⁿ)`. So the character
factors through the finite quotient, sidestepping the `ℚ_p` fractional part.

The headline is the **orthogonality integral** `∫_{ℤ_p} χ dHaar = 0` for a nontrivial character `χ` —
the Fourier-free fact that makes characters an orthogonal system and that the Kozyrev eigenfunction
computation rests on. The proof pushes the integral through the finite quotient: `χ` is constant on the
`pⁿ` fibers of `toZModPow` (each a ball of Haar measure `p⁻ⁿ`), so the integral is `p⁻ⁿ ∑_r φ(r)`, and
the character sum over the finite group vanishes (`AddChar.sum_eq_zero_iff_ne_zero`).

## Structure
- § I   The p-adic additive character `paChar`
- § II  Multiplicativity and local constancy
- § III The fibers of `toZModPow` are balls of measure `p⁻ⁿ`
- § IV  Orthogonality: a nontrivial character integrates to zero
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — The p-adic additive character -/

/-- The **level-`n` p-adic additive character** attached to an additive character `φ` of `ZMod(pⁿ)`:
    `x ↦ φ (toZModPow n x)`. The Kozyrev-relevant character `χ_p(p⁻ⁿ·)` on `ℤ_p` is of this form. -/
noncomputable def paChar (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) : ℤ_[p] → ℂ :=
  fun x => φ (PadicInt.toZModPow n x)

/-- The residue map `toZModPow n` is surjective (each residue is hit by a natural-number lift). -/
theorem toZModPow_surjective (n : ℕ) :
    Function.Surjective ⇑(PadicInt.toZModPow (p := p) n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  exact fun a => ⟨(a.val : ℤ_[p]), by rw [map_natCast]; exact ZMod.natCast_rightInverse a⟩

/-- A fiber of `toZModPow n` (over any residue `r = toZModPow n x₀`) is the radius-`p⁻ⁿ` ball around
    `x₀` — a coset of the kernel `pⁿℤ_p`. -/
theorem toZModPow_fiber_eq (n : ℕ) {r : ZMod (p ^ n)} {x0 : ℤ_[p]}
    (hx0 : PadicInt.toZModPow n x0 = r) :
    {x : ℤ_[p] | PadicInt.toZModPow n x = r} = {x : ℤ_[p] | ‖x - x0‖ ≤ (p : ℝ) ^ (-(n : ℤ))} := by
  ext x
  simp only [Set.mem_setOf_eq]
  rw [← hx0, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow (x - x0) n).symm

/-! ## § II — Multiplicativity and local constancy -/

/-- `paChar` turns addition into multiplication (it is a character). -/
theorem paChar_add (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (x y : ℤ_[p]) :
    paChar (p := p) n φ (x + y) = paChar (p := p) n φ x * paChar (p := p) n φ y := by
  simp only [paChar, map_add]
  exact φ.map_add_eq_mul _ _

/-- `paChar` is **locally constant**: constant on every ball of radius `p⁻ⁿ`. -/
theorem paChar_locally_constant (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) {x x' : ℤ_[p]}
    (h : ‖x - x'‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    paChar (p := p) n φ x = paChar (p := p) n φ x' := by
  have hker : PadicInt.toZModPow n x = PadicInt.toZModPow n x' := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
      ← PadicInt.norm_le_pow_iff_mem_span_pow]
    exact h
  simp only [paChar, hker]

/-! ## § III — The fibers of `toZModPow` are balls of measure `p⁻ⁿ` -/

/-- Each fiber `{x | toZModPow n x = r}` of the residue map is a coset of the radius-`p⁻ⁿ` ball, hence
    has Haar measure `p⁻ⁿ`. -/
theorem toZModPow_fiber_measure (n : ℕ) (r : ZMod (p ^ n)) :
    haarZp (p := p) {x : ℤ_[p] | PadicInt.toZModPow n x = r} = ((p : ℝ≥0∞) ^ n)⁻¹ := by
  obtain ⟨x0, hx0⟩ := toZModPow_surjective n r
  rw [toZModPow_fiber_eq n hx0]
  have hball : {y : ℤ_[p] | ‖y‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
      = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) := by
    ext y; simp [Metric.mem_closedBall, dist_eq_norm]
  have hpre : {x : ℤ_[p] | ‖x - x0‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
      = (fun x => -x0 + x) ⁻¹' {y : ℤ_[p] | ‖y‖ ≤ (p : ℝ) ^ (-(n : ℤ))} := by
    ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, neg_add_eq_sub]
  have hnull : NullMeasurableSet {y : ℤ_[p] | ‖y‖ ≤ (p : ℝ) ^ (-(n : ℤ))} (haarZp (p := p)) := by
    rw [hball]; exact measurableSet_closedBall.nullMeasurableSet
  rw [hpre, (measurePreserving_add_left (haarZp (p := p)) (-x0)).measure_preimage hnull, haarZp_ball]

/-- Each fiber of the residue map is measurable. -/
theorem toZModPow_fiber_measurableSet (n : ℕ) (r : ZMod (p ^ n)) :
    MeasurableSet {x : ℤ_[p] | PadicInt.toZModPow n x = r} := by
  obtain ⟨x0, hx0⟩ := toZModPow_surjective n r
  rw [toZModPow_fiber_eq n hx0]
  have hball : {x : ℤ_[p] | ‖x - x0‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
      = Metric.closedBall x0 ((p : ℝ) ^ (-(n : ℤ))) := by
    ext x; simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hball]; exact measurableSet_closedBall

/-! ## § IV — Orthogonality: a nontrivial character integrates to zero -/

/-- **The crane (orthogonality).** A *nontrivial* p-adic additive character integrates to zero over
    `ℤ_p`. The integral factors through the finite quotient `ZMod(pⁿ)`: `∫ χ = p⁻ⁿ ∑_r φ(r)`, and the
    character sum over the finite group vanishes. This is the Fourier-free orthogonality on which the
    Kozyrev-wavelet eigenfunctions of the Vladimirov operator rest. -/
theorem paChar_integral_eq_zero (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ ≠ 0) :
    ∫ x, paChar (p := p) n φ x ∂(haarZp (p := p)) = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hdecomp : ∀ x : ℤ_[p], paChar (p := p) n φ x
      = ∑ r : ZMod (p ^ n), Set.indicator {y : ℤ_[p] | PadicInt.toZModPow n y = r} (fun _ => φ r) x := by
    intro x
    simp only [paChar, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hterm : ∀ r : ZMod (p ^ n),
      ∫ x, Set.indicator {y : ℤ_[p] | PadicInt.toZModPow n y = r} (fun _ => φ r) x
          ∂(haarZp (p := p)) = ((((p : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * φ r := by
    intro r
    rw [integral_indicator_const _ (toZModPow_fiber_measurableSet n r), measureReal_def,
      toZModPow_fiber_measure, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    show (((p : ℝ) ^ n)⁻¹ : ℝ) • (φ r : ℂ) = _
    rw [Complex.real_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp),
    integral_finset_sum _
      (fun r _ => (integrable_const (φ r)).indicator (toZModPow_fiber_measurableSet n r)),
    Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.mul_sum,
    AddChar.sum_eq_zero_iff_ne_zero.mpr hφ, mul_zero]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_add
#print axioms paChar_locally_constant
#print axioms toZModPow_fiber_measure
#print axioms paChar_integral_eq_zero
end PurityCheck
