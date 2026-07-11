-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a genuine eigenfunction of the ℤ_p Taibleson–Vladimirov operator D^α — the level-1 p-adic additive character, with eigenvalue 1. Unlike the ball-indicator matrix entries of PadicVladimirov §IV, this is a true eigenfunction, and the character orthogonality ∫χ=0 (the "crane") is exactly what closes the computation. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicVladimirov
import ZeroParadox.Valuation.PadicCharacter
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# A genuine eigenfunction of D^α: the level-1 p-adic character

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The Vladimirov operator `D^α` (`PadicVladimirov`) has genuine eigenfunctions — the Kozyrev wavelets,
built from the p-adic additive characters (`PadicCharacter`). This file proves the first one on `ℤ_p`:
the **level-1 character `paChar 1 φ` is an eigenfunction of `D^α`, with eigenvalue 1**.

The computation is Fourier-free and rests on two facts already built: (i) `paChar 1 φ` is *constant on
every ball of radius `p⁻¹`* (`paChar_locally_constant`), so the difference `χ(x) − χ(y)` vanishes exactly
where the singular kernel `|x−y|^{-(α+1)}` is `> 1` — the difference regularizes the singularity, and the
kernel factor collapses to `1` on the whole space; (ii) a nontrivial character *integrates to zero*
(`paChar_integral_eq_zero`, the "crane"). Then
`D^α χ (x) = ∫ (χ(x) − χ(y)) dy = χ(x)·μ(ℤ_p) − ∫ χ = χ(x)·1 − 0 = χ(x)`.

**Fences.** This is the *compact* `ℤ_p` operator, whose eigenvalue here is `1` — not the full-space
symbol `|ξ|^α`. The difference is exactly the large-scale shells `‖x−y‖ > 1` that the `ℚ_p` operator
integrates over and this compact one omits; recovering `|ξ|^α` needs the `ℚ_p` operator, not built here.
The point is structural: these characters are *eigenfunctions*, where the ball indicators of § IV were
only matrix entries. No physical or dynamical claim.

## Structure
- § I   Integrability of the character
- § II  The level-1 eigenfunction `D^α (paChar 1 φ) = paChar 1 φ`
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — Integrability of the character -/

/-- A p-adic character is integrable (a finite sum of constant indicators on finite-measure fibers). -/
theorem paChar_integrable (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    Integrable (paChar (p := p) n φ) (haarZp (p := p)) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hdecomp : paChar (p := p) n φ
      = fun x => ∑ r : ZMod (p ^ n),
          Set.indicator {y : ℤ_[p] | PadicInt.toZModPow n y = r} (fun _ => φ r) x := by
    funext x
    simp only [paChar, Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [hdecomp]
  apply integrable_finset_sum
  intro r _
  exact (integrable_const (φ r)).indicator (toZModPow_fiber_measurableSet n r)

/-! ## § II — The eigenfunction property (any level) -/

/-- **Characters are eigenfunctions of `D^α`.** For any level-`n` character, `D^α (paChar n φ) x` factors
    as `paChar n φ x · D^α (paChar n φ) 0`: the value at `x` is the value at `0` times the character. This
    is the eigenfunction property, and it needs neither primitivity nor the crane — only that `paChar` is a
    character (`χ(y) = χ(x)·χ(y−x)`) and that `D^α` is translation-invariant. The eigenvalue is
    `D^α (paChar n φ) 0` (computed separately). -/
theorem vladimirov_paChar_eigen (α : ℝ) (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (x : ℤ_[p]) :
    vladimirov α (paChar (p := p) n φ) x
      = paChar (p := p) n φ x * vladimirov α (paChar (p := p) n φ) 0 := by
  have h0 : paChar (p := p) n φ 0 = 1 := by
    simp [paChar]
  unfold vladimirov
  rw [← MeasurePreserving.integral_comp (measurePreserving_add_left (haarZp (p := p)) x)
      (measurableEmbedding_addLeft x)
      (fun y => (paChar (p := p) n φ x - paChar (p := p) n φ y) * (vladimirovKernel α x y : ℂ))]
  trans (∫ z, paChar (p := p) n φ x
      * ((paChar (p := p) n φ 0 - paChar (p := p) n φ z) * (vladimirovKernel α 0 z : ℂ))
      ∂(haarZp (p := p)))
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    have hchar : paChar (p := p) n φ (x + z) = paChar (p := p) n φ x * paChar (p := p) n φ z :=
      paChar_add n φ x z
    have hker : vladimirovKernel α x (x + z) = vladimirovKernel α 0 z := by
      have h : x - (x + z) = 0 - z := by ring
      simp only [vladimirovKernel, h]
    simp only [hchar, hker, h0]
    ring
  · exact integral_const_mul (paChar (p := p) n φ x)
      (fun z => (paChar (p := p) n φ 0 - paChar (p := p) n φ z) * (vladimirovKernel α 0 z : ℂ))

/-! ## § III — The level-1 eigenfunction -/

/-- **The level-1 character is an eigenfunction of `D^α`, with eigenvalue 1.** Because `paChar 1 φ` is
    constant on radius-`p⁻¹` balls, the kernel factor collapses to `1`, and the crane `∫ χ = 0` closes
    the integral: `D^α (paChar 1 φ) = paChar 1 φ`. -/
theorem vladimirov_paChar_one (α : ℝ) (φ : AddChar (ZMod (p ^ 1)) ℂ) (hφ : φ ≠ 0) (x : ℤ_[p]) :
    vladimirov α (paChar (p := p) 1 φ) x = paChar (p := p) 1 φ x := by
  have hint : (fun y => (paChar (p := p) 1 φ x - paChar (p := p) 1 φ y)
        * (vladimirovKernel α x y : ℂ))
      = fun y => paChar (p := p) 1 φ x - paChar (p := p) 1 φ y := by
    funext y
    by_cases hxy : ‖x - y‖ ≤ (p : ℝ) ^ (-((1 : ℕ) : ℤ))
    · rw [paChar_locally_constant 1 φ hxy]; ring
    · have hnorm1 : ‖x - y‖ = 1 := by
        have hiff := PadicInt.norm_le_pow_iff_norm_lt_pow_add_one (x - y) (-((1 : ℕ) : ℤ))
        rw [show (-((1 : ℕ) : ℤ) + 1) = 0 from by norm_num, zpow_zero] at hiff
        exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp (fun h => hxy (hiff.mpr h)))
      have hker : vladimirovKernel α x y = 1 := by
        simp only [vladimirovKernel, hnorm1, Real.one_rpow, inv_one]
      rw [hker]; push_cast; ring
  have hci : Integrable (fun _ : ℤ_[p] => paChar (p := p) 1 φ x) (haarZp (p := p)) :=
    integrable_const _
  unfold vladimirov
  rw [hint, integral_sub hci (paChar_integrable 1 φ), integral_const,
    paChar_integral_eq_zero 1 φ hφ, sub_zero, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul]

/-! ## § IV — Toward the general-`n` eigenvalue: sub-ball orthogonality -/

/-- **General quotient integral.** Any function pulled back from the finite quotient `ZMod(pⁿ)` integrates
    to `p⁻ⁿ` times its sum over `ZMod(pⁿ)` (the crane, generalized from a character to arbitrary `g`). -/
theorem integral_comp_toZModPow (n : ℕ) (g : ZMod (p ^ n) → ℂ) :
    ∫ x, g (PadicInt.toZModPow n x) ∂(haarZp (p := p))
      = ((((p : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * ∑ r : ZMod (p ^ n), g r := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hdecomp : ∀ x : ℤ_[p], g (PadicInt.toZModPow n x)
      = ∑ r : ZMod (p ^ n),
          Set.indicator {y : ℤ_[p] | PadicInt.toZModPow n y = r} (fun _ => g r) x := by
    intro x
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hterm : ∀ r : ZMod (p ^ n),
      ∫ x, Set.indicator {y : ℤ_[p] | PadicInt.toZModPow n y = r} (fun _ => g r) x
          ∂(haarZp (p := p)) = ((((p : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * g r := by
    intro r
    rw [integral_indicator_const _ (toZModPow_fiber_measurableSet n r), measureReal_def,
      toZModPow_fiber_measure, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    show (((p : ℝ) ^ n)⁻¹ : ℝ) • (g r : ℂ) = _
    rw [Complex.real_smul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp),
    integral_finset_sum _
      (fun r _ => (integrable_const (g r)).indicator (toZModPow_fiber_measurableSet n r)),
    Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.mul_sum]

/-- **Primitive shift sum.** For a primitive character and `a ≠ 0`, the shifted sum `∑ₓ φ(a·x)` over
    `ZMod(pⁿ)` vanishes — it is the full-group sum of the nontrivial character `mulShift φ a`. Uses
    `AddChar.one_eq_zero` (`rfl`) to bridge primitivity's `≠ 1` to the sum lemma's `≠ 0`. -/
theorem sum_mulShift_eq_zero (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive)
    {a : ZMod (p ^ n)} (ha : a ≠ 0) :
    ∑ x : ZMod (p ^ n), φ (a * x) = 0 := by
  have hne : AddChar.mulShift φ a ≠ 0 := by
    rw [← AddChar.one_eq_zero]; exact hφ ha
  simp only [← AddChar.mulShift_apply]
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne

open Classical in
/-- **Character sum over a subgroup vanishes.** For a primitive `φ` and `q = pʲ ≠ 0`, the sum of `φ` over
    the multiples of `q` (the subgroup `H_j = qℤ/pⁿℤ`) is zero. Classic shift trick: pick `h ∈ H_j` with
    `φ(h) ≠ 1` (primitivity), then `∑ = φ(h)·∑` by reindexing `r ↦ r+h`, forcing `∑ = 0`. No subgroup
    subtype needed — the `q ∣ ·` predicate is shift-stable because `q ∣ h`. -/
theorem sum_char_multiples_eq_zero (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive)
    {j : ℕ} (hj : (p : ZMod (p ^ n)) ^ j ≠ 0) :
    ∑ r : ZMod (p ^ n), (if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0) = 0 := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (hφ hj)
  rw [AddChar.mulShift_apply, AddChar.one_apply] at hx
  have hdvd : (p : ZMod (p ^ n)) ^ j ∣ (p : ZMod (p ^ n)) ^ j * x := dvd_mul_right _ _
  have key : (∑ r : ZMod (p ^ n), (if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0))
      = φ ((p : ZMod (p ^ n)) ^ j * x)
        * ∑ r : ZMod (p ^ n), (if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight ((p : ZMod (p ^ n)) ^ j * x))
      (fun r => if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [Equiv.coe_addRight]
    by_cases hr : (p : ZMod (p ^ n)) ^ j ∣ r
    · rw [if_pos hr, if_pos (dvd_add hr hdvd), φ.map_add_eq_mul, mul_comm]
    · rw [if_neg hr, if_neg (fun hc => hr (by
        have := dvd_sub hc hdvd; rwa [add_sub_cancel_right] at this)), mul_zero]
  have hne : (1 : ℂ) - φ ((p : ZMod (p ^ n)) ^ j * x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hz : (1 - φ ((p : ZMod (p ^ n)) ^ j * x))
      * ∑ r : ZMod (p ^ n), (if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0) = 0 := by
    rw [sub_mul, one_mul, ← key, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left hne

/-- **Ball ↔ divisibility bridge.** For `j ≤ n`, a point lies in the radius-`p⁻ʲ` ball iff its level-`n`
    residue is divisible by `pʲ`. (`‖x‖ ≤ p⁻ʲ ⟺ pʲ ∣ x` in `ℤ_p`, transported to `ZMod(pⁿ)`; the reverse
    direction lifts a witness and uses `ker toZModPow n = (pⁿ)` with `pʲ ∣ pⁿ`.) -/
theorem norm_le_iff_dvd_toZModPow (n j : ℕ) (hjn : j ≤ n) (x : ℤ_[p]) :
    ‖x‖ ≤ (p : ℝ) ^ (-(j : ℤ)) ↔ (p : ZMod (p ^ n)) ^ j ∣ PadicInt.toZModPow n x := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]
  have hpimg : PadicInt.toZModPow n ((p : ℤ_[p]) ^ j) = (p : ZMod (p ^ n)) ^ j := by
    rw [map_pow, map_natCast]
  constructor
  · intro hdvd
    rw [← hpimg]; exact map_dvd _ hdvd
  · rintro ⟨s, hs⟩
    obtain ⟨ŝ, hŝ⟩ := toZModPow_surjective n s
    have hmem : x - (p : ℤ_[p]) ^ j * ŝ ∈ RingHom.ker (PadicInt.toZModPow n) := by
      rw [RingHom.mem_ker, map_sub, map_mul, hpimg, hŝ, hs, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    have hjdvd : (p : ℤ_[p]) ^ j ∣ (p : ℤ_[p]) ^ n := pow_dvd_pow _ hjn
    have hx1 : (p : ℤ_[p]) ^ j ∣ x - (p : ℤ_[p]) ^ j * ŝ := hjdvd.trans hmem
    have := dvd_add hx1 (dvd_mul_right ((p : ℤ_[p]) ^ j) ŝ)
    rwa [sub_add_cancel] at this

open Classical in
/-- **Sub-ball orthogonality.** For a primitive `φ` and `j < n`, the character integrates to zero over
    the radius-`p⁻ʲ` ball: `∫_{ball_j} paChar n φ = 0`. Reduces (via `integral_comp_toZModPow`) to the
    subgroup character sum `∑_{pʲ ∣ r} φ(r) = 0` (`sum_char_multiples_eq_zero`). Generalizes the crane
    (`j = 0`) to every ball strictly larger than the constancy radius. -/
theorem paChar_ball_integral_eq_zero (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive)
    {j : ℕ} (hjn : j < n) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p)) = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hq : (p : ZMod (p ^ n)) ^ j ≠ 0 := by
    rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h1 : p ^ n ≤ p ^ j := Nat.le_of_dvd (pow_pos ‹Fact p.Prime›.out.pos j) hdvd
    have h2 : n ≤ j := (Nat.pow_le_pow_iff_right ‹Fact p.Prime›.out.one_lt).mp h1
    omega
  have key : ∀ x : ℤ_[p],
      Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) x
        = (fun r => if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0) (PadicInt.toZModPow n x) := by
    intro x
    by_cases hx : x ∈ {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))}
    · rw [Set.indicator_of_mem hx]
      simp only [if_pos ((norm_le_iff_dvd_toZModPow n j hjn.le x).mp hx)]
      rfl
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_setOf_eq] at hx
      simp only [if_neg (fun hc => hx ((norm_le_iff_dvd_toZModPow n j hjn.le x).mpr hc))]
  rw [integral_congr_ae (Filter.Eventually.of_forall key),
    integral_comp_toZModPow n (fun r => if (p : ZMod (p ^ n)) ^ j ∣ r then φ r else 0),
    sum_char_multiples_eq_zero n φ hφ hq, mul_zero]

/-- **Innermost ball integral.** Over the constancy-radius ball `ball_n`, the character is constant `1`,
    so `∫_{ball_n} paChar n φ = μ(ball_n) = p⁻ⁿ`. (Completes the `J_j` family: `J_j = 0` for `j < n`,
    `J_n = p⁻ⁿ`.) -/
theorem paChar_ball_n_integral (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) :
    ∫ x, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))} (paChar (p := p) n φ) x
      ∂(haarZp (p := p)) = ((((p : ℝ) ^ n)⁻¹ : ℝ) : ℂ) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
  have hval : Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))} (paChar (p := p) n φ)
      = Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))} (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have h0 : (p : ZMod (p ^ n)) ^ n = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
      have hz : PadicInt.toZModPow n x = 0 := by
        have := (norm_le_iff_dvd_toZModPow n n le_rfl x).mp hx
        rwa [h0, zero_dvd_iff] at this
      simp [paChar, hz]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  rw [hval, integral_indicator_const _ (ball_measurableSet n), measureReal_def, haarZp_ball,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  show (((p : ℝ) ^ n)⁻¹ : ℝ) • (1 : ℂ) = ((((p : ℝ) ^ n)⁻¹ : ℝ) : ℂ)
  rw [Complex.real_smul, mul_one]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms paChar_integrable
#print axioms vladimirov_paChar_eigen
#print axioms vladimirov_paChar_one
#print axioms integral_comp_toZModPow
#print axioms sum_mulShift_eq_zero
#print axioms sum_char_multiples_eq_zero
#print axioms norm_le_iff_dvd_toZModPow
#print axioms paChar_ball_integral_eq_zero
#print axioms paChar_ball_n_integral
end PurityCheck
