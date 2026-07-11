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

/-! ## § V — The general-`n` eigenvalue `λ_n` (assembly, reusing M2c's shell machinery) -/

/-- The M2c ball integrand telescopes into shell loads: `vladIntegrand α n = ∑_{m<n} shellLoad α m`
    (from `vladIntegrand_succ` and `vladIntegrand α 0 = 0`). Since `vladIntegrand α n y =
    (1 − 𝟙_{ball_n}(y))·K = 𝟙_{(ball_n)ᶜ}(y)·K`, this is the annulus decomposition of the kernel — for free. -/
theorem vladIntegrand_eq_sum (α : ℝ) (n : ℕ) :
    vladIntegrand (p := p) α n = ∑ m ∈ Finset.range n, shellLoad (p := p) α m := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    funext y
    have hb : ∀ z : ℤ_[p], ballFun (p := p) 0 z = 1 := by
      intro z
      have hz : z ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((0 : ℕ) : ℤ))} := by
        simp only [Set.mem_setOf_eq, Nat.cast_zero, neg_zero, zpow_zero]
        exact PadicInt.norm_le_one z
      exact Set.indicator_of_mem hz _
    simp [vladIntegrand, hb]
  | succ m ih =>
    rw [vladIntegrand_succ, ih, Finset.sum_range_succ]
    funext y
    rw [Pi.add_apply]

/-- The character against one shell load: `∫ χ·shellLoad α m = shellConst α m · (J_m − J_{m+1})`, where
    `J_j = ∫_{ball_j} χ`. (`shellLoad = shellConst·𝟙_{shell_m}` and `𝟙_{shell_m} = 𝟙_{ball_m} − 𝟙_{ball_{m+1}}`.) -/
theorem integral_char_shellLoad (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (α : ℝ) (m : ℕ) :
    ∫ y, paChar (p := p) n φ y * shellLoad (p := p) α m y ∂(haarZp (p := p))
      = (shellConst (p := p) α m : ℂ)
        * ((∫ y, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ))} (paChar (p := p) n φ) y
              ∂(haarZp (p := p)))
          - ∫ y, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ))} (paChar (p := p) n φ) y
              ∂(haarZp (p := p))) := by
  have hsub : {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ))}
      ⊆ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(m : ℤ))} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    refine le_trans hx (zpow_le_zpow_right₀ ?_ ?_)
    · exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
    · omega
  have hpt : ∀ y, paChar (p := p) n φ y * shellLoad (p := p) α m y
      = (shellConst (p := p) α m : ℂ) * Set.indicator (shellSet (p := p) m) (paChar (p := p) n φ) y := by
    intro y
    by_cases hy : y ∈ shellSet (p := p) m
    · simp only [shellLoad, Set.indicator_of_mem hy]; ring
    · simp only [shellLoad, Set.indicator_of_notMem hy, mul_zero]
  have hind : ∀ y, Set.indicator (shellSet (p := p) m) (paChar (p := p) n φ) y
      = Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ))} (paChar (p := p) n φ) y
        - Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ))} (paChar (p := p) n φ) y := by
    intro y
    rw [shellSet, Set.indicator_diff hsub, Pi.sub_apply]
  have step1 : ∫ y, paChar (p := p) n φ y * shellLoad (p := p) α m y ∂(haarZp (p := p))
      = (shellConst (p := p) α m : ℂ)
        * ∫ y, Set.indicator (shellSet (p := p) m) (paChar (p := p) n φ) y ∂(haarZp (p := p)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_const_mul ((shellConst (p := p) α m : ℂ))
      (Set.indicator (shellSet (p := p) m) (paChar (p := p) n φ))
  have step2 : ∫ y, Set.indicator (shellSet (p := p) m) (paChar (p := p) n φ) y ∂(haarZp (p := p))
      = (∫ y, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(m : ℤ))} (paChar (p := p) n φ) y
            ∂(haarZp (p := p)))
        - ∫ y, Set.indicator {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-((m + 1 : ℕ) : ℤ))} (paChar (p := p) n φ) y
            ∂(haarZp (p := p)) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hind)]
    exact integral_sub ((paChar_integrable n φ).indicator (ball_measurableSet m))
      ((paChar_integrable n φ).indicator (ball_measurableSet (m + 1)))
  rw [step1, step2]

/-- Integrability of `χ·shellLoad α m` (a constant times a finite-measure indicator). -/
theorem char_shellLoad_integrable (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (α : ℝ) (m : ℕ) :
    Integrable (fun y => paChar (p := p) n φ y * shellLoad (p := p) α m y) (haarZp (p := p)) := by
  have hpt : (fun y => paChar (p := p) n φ y * shellLoad (p := p) α m y)
      = fun y => (shellConst (p := p) α m : ℂ)
        * Set.indicator (shellSet (p := p) m) (paChar (p := p) n φ) y := by
    funext y
    by_cases hy : y ∈ shellSet (p := p) m
    · simp only [shellLoad, Set.indicator_of_mem hy]; ring
    · simp only [shellLoad, Set.indicator_of_notMem hy, mul_zero]
  rw [hpt]
  exact ((paChar_integrable n φ).indicator (shellSet_measurable m)).const_mul _

/-- `∫ χ·vladIntegrand α n = ∑_{m<n} ∫ χ·shellLoad α m` (distribute the character over the shell sum). -/
theorem integral_char_vladIntegrand (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (α : ℝ) :
    ∫ y, paChar (p := p) n φ y * vladIntegrand (p := p) α n y ∂(haarZp (p := p))
      = ∑ m ∈ Finset.range n,
          ∫ y, paChar (p := p) n φ y * shellLoad (p := p) α m y ∂(haarZp (p := p)) := by
  have hdist : (fun y => paChar (p := p) n φ y * vladIntegrand (p := p) α n y)
      = fun y => ∑ m ∈ Finset.range n, paChar (p := p) n φ y * shellLoad (p := p) α m y := by
    funext y
    rw [vladIntegrand_eq_sum, Finset.sum_apply, Finset.mul_sum]
  rw [hdist, integral_finset_sum _ (fun m _ => char_shellLoad_integrable n φ α m)]

/-- **The split.** `D^α χ(0) = D^α 𝟙_{ball_n}(0) − ∫ χ·vladIntegrand α n`, where `vladIntegrand α n =
    𝟙_{(ball_n)ᶜ}·K` is the M2c ball integrand. (Pointwise: `(1−χ)K = (1−𝟙_{ball_n})K − χ(1−𝟙_{ball_n})K`,
    since `𝟙_{ball_n}·(1−χ) = 0`.) -/
theorem vladimirov_paChar_split (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (α : ℝ) :
    vladimirov α (paChar (p := p) n φ) 0
      = vladimirov α (ballFun (p := p) n) 0
        - ∫ y, paChar (p := p) n φ y * vladIntegrand (p := p) α n y ∂(haarZp (p := p)) := by
  have hchar_int : Integrable (fun y => paChar (p := p) n φ y * vladIntegrand (p := p) α n y)
      (haarZp (p := p)) := by
    have hdist : (fun y => paChar (p := p) n φ y * vladIntegrand (p := p) α n y)
        = fun y => ∑ m ∈ Finset.range n, paChar (p := p) n φ y * shellLoad (p := p) α m y := by
      funext y
      rw [vladIntegrand_eq_sum, Finset.sum_apply, Finset.mul_sum]
    rw [hdist]
    exact integrable_finset_sum _ (fun m _ => char_shellLoad_integrable n φ α m)
  have hpt : ∀ y, (paChar (p := p) n φ 0 - paChar (p := p) n φ y) * (vladimirovKernel α 0 y : ℂ)
      = vladIntegrand (p := p) α n y - paChar (p := p) n φ y * vladIntegrand (p := p) α n y := by
    intro y
    have h0χ : paChar (p := p) n φ 0 = 1 := by simp [paChar]
    have h0b : ballFun (p := p) n 0 = 1 := by
      have hz : (0 : ℤ_[p]) ∈ {x : ℤ_[p] | ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))} := by
        simp only [Set.mem_setOf_eq, norm_zero]; positivity
      exact Set.indicator_of_mem hz _
    by_cases hy : y ∈ {z : ℤ_[p] | ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))}
    · haveI : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
      have h0 : (p : ZMod (p ^ n)) ^ n = 0 := by rw [← Nat.cast_pow]; exact ZMod.natCast_self _
      have hz0 : PadicInt.toZModPow n y = 0 := by
        have := (norm_le_iff_dvd_toZModPow n n le_rfl y).mp hy
        rwa [h0, zero_dvd_iff] at this
      have hχy : paChar (p := p) n φ y = 1 := by simp [paChar, hz0]
      have hby : ballFun (p := p) n y = 1 := Set.indicator_of_mem hy _
      simp only [vladIntegrand, h0χ, hχy, h0b, hby]; ring
    · have hby : ballFun (p := p) n y = 0 := Set.indicator_of_notMem hy _
      simp only [vladIntegrand, h0χ, h0b, hby]; ring
  have hL : vladimirov α (paChar (p := p) n φ) 0
      = ∫ y, (paChar (p := p) n φ 0 - paChar (p := p) n φ y) * (vladimirovKernel α 0 y : ℂ)
        ∂(haarZp (p := p)) := rfl
  have hR : vladimirov α (ballFun (p := p) n) 0
      = ∫ y, vladIntegrand (p := p) α n y ∂(haarZp (p := p)) := rfl
  rw [hL, hR, integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (vladIntegrand_integrable α n) hchar_int]

/-- The correction integral: only the outermost shell (`m = n−1`) survives, since `J_m = 0` for `m < n`
    and `J_n = p⁻ⁿ`. Value `−(p^α)^{n-1}·p⁻¹ = −p^{(n-1)α−1}`. -/
theorem correction_eq (n : ℕ) (hn : 0 < n) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive) (α : ℝ) :
    ∫ y, paChar (p := p) n φ y * vladIntegrand (p := p) α n y ∂(haarZp (p := p))
      = -((((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ : ℝ) : ℂ) := by
  have hp0R : (p : ℝ) ≠ 0 := by exact_mod_cast ‹Fact p.Prime›.out.pos.ne'
  rw [integral_char_vladIntegrand n φ α, Finset.sum_eq_single (n - 1)]
  · rw [integral_char_shellLoad n φ α (n - 1),
      paChar_ball_integral_eq_zero n φ hφ (by omega : n - 1 < n),
      Nat.sub_add_cancel hn, paChar_ball_n_integral n φ, shellConst,
      zero_sub, mul_neg, ← Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_inj]
    field_simp
    rw [← pow_succ, Nat.sub_add_cancel hn]
  · intro m hm hne
    have hmn : m < n := Finset.mem_range.mp hm
    rw [integral_char_shellLoad n φ α m, paChar_ball_integral_eq_zero n φ hφ hmn,
      paChar_ball_integral_eq_zero n φ hφ (by omega : m + 1 < n)]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : n - 1 < n)) h

/-- **The general-`n` eigenvalue.** For a *primitive* character `φ` (`n ≥ 1`), `paChar n φ` is an
    eigenfunction of `D^α` with eigenvalue
    `λ_n = (1 − p⁻¹)·∑_{k<n}(p^α)^k + (p^α)^{n-1}·p⁻¹ = (1 − p⁻¹)∑_{k<n}(p^α)^k + p^{(n-1)α−1}`.
    (`D^α χ(0) = D^α 𝟙_{ball_n}(0) − ∫χ·vladIntegrand`, the M2c value plus the single surviving shell.) -/
theorem vladimirov_paChar_zero (n : ℕ) (hn : 0 < n) (φ : AddChar (ZMod (p ^ n)) ℂ)
    (hφ : φ.IsPrimitive) (α : ℝ) :
    vladimirov α (paChar (p := p) n φ) 0
      = (((1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
          + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ : ℝ) : ℂ) := by
  rw [vladimirov_paChar_split n φ α, vladimirov_ballFun_zero, correction_eq n hn φ hφ α,
    sub_neg_eq_add, ← Complex.ofReal_add]

/-- **Full eigenfunction–eigenvalue statement.** For primitive `φ` (`n ≥ 1`),
    `D^α (paChar n φ) = λ_n · paChar n φ` — a genuine eigenfunction with the explicit eigenvalue `λ_n`.
    Combines `vladimirov_paChar_eigen` (the eigenfunction property) with `vladimirov_paChar_zero`. -/
theorem vladimirov_paChar_eigenvalue (n : ℕ) (hn : 0 < n) (φ : AddChar (ZMod (p ^ n)) ℂ)
    (hφ : φ.IsPrimitive) (α : ℝ) (x : ℤ_[p]) :
    vladimirov α (paChar (p := p) n φ) x
      = (((1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
          + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ : ℝ) : ℂ) * paChar (p := p) n φ x := by
  rw [vladimirov_paChar_eigen α n φ x, vladimirov_paChar_zero n hn φ hφ α, mul_comm]

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
#print axioms vladIntegrand_eq_sum
#print axioms integral_char_shellLoad
#print axioms vladimirov_paChar_split
#print axioms correction_eq
#print axioms vladimirov_paChar_zero
#print axioms vladimirov_paChar_eigenvalue
end PurityCheck
