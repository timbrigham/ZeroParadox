-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the ⊥-contact of the p-adic dynamics bridge — the trivial character (the 0 of the Pontryagin dual) is the joint STILL-POINT: fixed by every odometer Koopman operator and annihilated by the Vladimirov operator D^α, and it is the FLOOR of the D^α spectrum on characters (eigenvalue 0, while every primitive character has strictly positive eigenvalue λ_n). Operator-level; a fixed-point = zero identification, not an analytic limit. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicKozyrev
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The still-point: the trivial character is the joint fixed/annihilated bottom

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The p-adic dynamics bridge (`PadicKoopman`, `PadicVladimirov`, `PadicCharacter`, `PadicKozyrev`) put two
operators on `ℤ_p`: the odometer's Koopman operator `U_c f = f(c + ·)` (reversible dynamics) and the
Taibleson–Vladimirov operator `D^α` (the irreversible/diffusion generator). This file locates the
operator-face **bottom**: the **still-point**, the one function on which the reversible dynamics is
trivial and the irreversible generator vanishes.

That function is the **trivial character** `paChar n 0` — the level-`n` character attached to the zero
of the additive-character (Pontryagin dual) group `AddChar (ZMod pⁿ) ℂ`. It is the constant `1`
(`paChar_trivial`), so:

* it is **fixed by every odometer Koopman operator** (`stillPoint_koopman_fixed`); and
* it is **annihilated by `D^α`** (`stillPoint_vladimirov_zero`), i.e. it is the eigenvalue-`0`
  eigenfunction of the generator.

The headline is `stillPoint_is_spectral_floor`: the still-point sits at the **floor of the `D^α`
spectrum on characters** — eigenvalue `0`, while every *primitive* character (`n ≥ 1`) has the strictly
positive eigenvalue `λ_n` (`vladimirov_paChar_eigenvalue`, positivity `stillPoint_eigenvalue_positive`).
So the trivial character is not merely *a* fixed point; it is the bottom of the tower, and it *is* the
zero of the dual — a **fixed-point = zero** identification, the operator-face reading of the framework's
bottom, obtained without any analytic `n → ∞` limit.

**Fences.** Operator-level only, and the "floor" is over the character system (not a claim about all of
`L²`). The math is elementary (constants are killed by a difference-kernel operator and fixed by
translation); the content is the *identification* of the still-point with the zero of the Pontryagin
dual and with the floor of the `D^α` spectrum. No dynamical-equivalence or physical claim; no claim of
mathematical novelty.

## Structure
- § I   The trivial character is the constant `1`
- § II  The still-point: Koopman-fixed and `D^α`-annihilated
- § III Positivity of the primitive eigenvalue `λ_n`
- § IV  The still-point is the floor of the `D^α` spectrum
-/

namespace ZeroParadox

open MeasureTheory

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — The trivial character is the constant `1` -/

/-- The **trivial character** `paChar n 0` (the level-`n` character of the zero of the Pontryagin dual
    `AddChar (ZMod pⁿ) ℂ`) is the constant function `1`. -/
theorem paChar_trivial (n : ℕ) : paChar (p := p) n 0 = fun _ => (1 : ℂ) := by
  funext x
  simp only [paChar, AddChar.zero_apply]

/-! ## § II — The still-point -/

/-- **Koopman-fixed.** The trivial character is fixed by every odometer Koopman operator
    `U_c f = f(c + ·)`: `paChar n 0 (c + x) = paChar n 0 x`. (It is constant.) -/
theorem stillPoint_koopman_fixed (n : ℕ) (c x : ℤ_[p]) :
    paChar (p := p) n 0 (c + x) = paChar (p := p) n 0 x := by
  rw [paChar_trivial]

/-- **`D^α`-annihilated.** The trivial character is killed by the Vladimirov operator:
    `D^α (paChar n 0) = 0`. It is the eigenvalue-`0` eigenfunction of the generator. -/
theorem stillPoint_vladimirov_zero (α : ℝ) (n : ℕ) (x : ℤ_[p]) :
    vladimirov α (paChar (p := p) n 0) x = 0 := by
  rw [paChar_trivial]
  exact vladimirov_const α 1 x

/-! ## § III — Positivity of the primitive eigenvalue `λ_n` -/

/-- The primitive `D^α` eigenvalue
    `λ_n = (1 - p⁻¹) ∑_{k<n} (p^α)^k + (p^α)^{n-1} p⁻¹` is **strictly positive** for `n ≥ 1`.
    Every factor is positive: `1 - p⁻¹ > 0` (as `p ≥ 2`), the geometric sum is a nonempty sum of
    positive powers of `p^α > 0`, and the correction term is a product of positives. -/
theorem stillPoint_eigenvalue_positive (α : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
        + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  have hpa : (0 : ℝ) < (p : ℝ) ^ α := Real.rpow_pos_of_pos hp0 α
  have hlt1 : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one₀ hp0]; exact hp1
  have hfac : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
  have hsum : (0 : ℝ) < ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k := by
    apply Finset.sum_pos (fun k _ => pow_pos hpa k)
    exact Finset.nonempty_range_iff.mpr hn.ne'
  have hlast : (0 : ℝ) < ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ :=
    mul_pos (pow_pos hpa _) (inv_pos.mpr hp0)
  exact add_pos (mul_pos hfac hsum) hlast

/-! ## § IV — The still-point is the floor of the `D^α` spectrum -/

/-- **The still-point is the floor of the `D^α` spectrum on characters.** The trivial character (the `0`
    of the Pontryagin dual) is annihilated by `D^α` (eigenvalue `0`), while every primitive character
    (`n ≥ 1`) satisfies the eigen-equation `D^α (paChar n φ) = λ_n · paChar n φ` with a **strictly
    positive** eigenvalue `λ_n`. So the trivial character is the bottom of the tower, and it *is* the
    zero of the dual — a fixed-point = zero identification, without any analytic limit. -/
theorem stillPoint_is_spectral_floor (α : ℝ) {n : ℕ} (hn : 0 < n)
    (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive) :
    (∀ x : ℤ_[p], vladimirov α (paChar (p := p) n 0) x = 0)
      ∧ (∀ x : ℤ_[p], vladimirov α (paChar (p := p) n φ) x
          = (((1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
              + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ : ℝ) : ℂ) * paChar (p := p) n φ x)
      ∧ 0 < (1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
          + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ :=
  ⟨stillPoint_vladimirov_zero α n,
   fun x => vladimirov_paChar_eigenvalue n hn φ hφ α x,
   stillPoint_eigenvalue_positive α hn⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_trivial
#print axioms stillPoint_koopman_fixed
#print axioms stillPoint_vladimirov_zero
#print axioms stillPoint_eigenvalue_positive
#print axioms stillPoint_is_spectral_floor
end PurityCheck
