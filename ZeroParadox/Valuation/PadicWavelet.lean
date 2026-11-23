-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): on ℤ_p, a primitive level-n character restricted to a ball of radius p^(-j) with j < n has integral zero and is an eigenfunction of D^α on ℤ_p (the `vladimirov` operator, not the ℚ_p one) with the level-n eigenvalue of the bare character, whatever the ball's centre; character-times-ball functions on disjoint balls are orthogonal. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicBallWave
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# On ℤ_p, a primitive level-n character times the indicator of a ball of radius p^(-j), j < n, has integral zero and is an eigenfunction of D^α on ℤ_p (the `vladimirov` operator, not the ℚ_p one) with the bare character's level-n eigenvalue; any two characters times indicators of disjoint balls are orthogonal

## Engineer's Take

These move as waves, with balls at the node branches. Depths expand on themselves infinitely as they
expand outward from the center.

---

## Formal Overview (AI-assisted)
`Statement:` `kozWavelet n φ j a`, a character times a ball indicator (the shape of S. V. Kozyrev,
Izv. Math. 66 (2002) 367), on Haar `ℤ_p` with D^α on `ℤ_p` (the `vladimirov` operator, not the `ℚ_p` one).
No claim about Kozyrev's normalisation, indexing or completeness of the family is made.
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ### § I. Nodes and wavelets -/

/-- `Statement:` the closed ball `{x | ‖x - a‖ ≤ p^(-j)}` in `ℤ_p`. -/
def nodeBall (j : ℕ) (a : ℤ_[p]) : Set ℤ_[p] := {x | ‖x - a‖ ≤ (p : ℝ) ^ (-(j : ℤ))}

/-- `Statement:` `nodeBall j a` is measurable. -/
theorem nodeBall_measurableSet (j : ℕ) (a : ℤ_[p]) : MeasurableSet (nodeBall (p := p) j a) := by
  have h : nodeBall (p := p) j a = Metric.closedBall a ((p : ℝ) ^ (-(j : ℤ))) := by
    ext x; simp [nodeBall, Metric.mem_closedBall, dist_eq_norm]
  rw [h]; exact measurableSet_closedBall

/-- `Statement:` `paChar n φ` restricted to `nodeBall j a`, and `0` off it. -/
noncomputable def kozWavelet (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (j : ℕ) (a : ℤ_[p]) :
    ℤ_[p] → ℂ :=
  Set.indicator (nodeBall (p := p) j a) (paChar (p := p) n φ)

section Basic
variable (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (j : ℕ) (a : ℤ_[p])

/-- `Statement:` `kozWavelet n φ j a` is `0` off `nodeBall j a`. -/
theorem kozWavelet_eq_zero_of_not_mem {x : ℤ_[p]} (hx : x ∉ nodeBall (p := p) j a) :
    kozWavelet n φ j a x = 0 :=
  Set.indicator_of_notMem hx _

/-- `Statement:` on `nodeBall j a`, `kozWavelet n φ j a` equals `paChar n φ`. -/
theorem kozWavelet_of_mem {x : ℤ_[p]} (hx : x ∈ nodeBall (p := p) j a) :
    kozWavelet n φ j a x = paChar (p := p) n φ x :=
  Set.indicator_of_mem hx _

/-- `Statement:` for `x ∈ nodeBall j a`, `x + z ∈ nodeBall j a` iff `‖z‖ ≤ p^(-j)`; both directions. -/
theorem add_mem_nodeBall_iff {x : ℤ_[p]} (hx : x ∈ nodeBall (p := p) j a) (z : ℤ_[p]) :
    x + z ∈ nodeBall (p := p) j a ↔ ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) := by
  simp only [nodeBall, Set.mem_ofPred_eq] at hx ⊢
  constructor
  · intro h
    have := PadicInt.nonarchimedean (x + z - a) (-(x - a))
    rw [show x + z - a + -(x - a) = z by ring, norm_neg] at this
    exact this.trans (max_le h hx)
  · intro h
    have := PadicInt.nonarchimedean (x - a) z
    rw [show x - a + z = x + z - a by ring] at this
    exact this.trans (max_le hx h)

/-- `Statement:` for `x ∈ nodeBall j a`, `kozWavelet (x + z)` is `paChar n φ x` times the
`{‖w‖ ≤ p^(-j)}`-indicator of `paChar n φ` at `z`. -/
theorem kozWavelet_add {x : ℤ_[p]} (hx : x ∈ nodeBall (p := p) j a) (z : ℤ_[p]) :
    kozWavelet n φ j a (x + z)
      = paChar (p := p) n φ x
        * Set.indicator {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) z := by
  by_cases hz : ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))
  · rw [kozWavelet_of_mem n φ j a ((add_mem_nodeBall_iff j a hx z).mpr hz),
      Set.indicator_of_mem (show z ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hz), paChar_add]
  · rw [kozWavelet_eq_zero_of_not_mem n φ j a (fun h => hz ((add_mem_nodeBall_iff j a hx z).mp h)),
      Set.indicator_of_notMem (show z ∉ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hz),
      mul_zero]

/-- `Statement:` `a ∈ nodeBall j a`. -/
theorem self_mem_nodeBall : a ∈ nodeBall (p := p) j a := by
  simp only [nodeBall, Set.mem_ofPred_eq, sub_self, norm_zero]; positivity

/-- `Statement:` `∫ kozWavelet n φ j a` is `paChar n φ a` times `∫` of `paChar n φ` over `{‖w‖ ≤ p^(-j)}`. -/
theorem kozWavelet_integral :
    ∫ x, kozWavelet n φ j a x ∂(haarZp (p := p))
      = paChar (p := p) n φ a
        * ∫ z, Set.indicator {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} (paChar (p := p) n φ) z
            ∂(haarZp (p := p)) := by
  rw [← MeasurePreserving.integral_comp (measurePreserving_add_left (haarZp (p := p)) a)
      (measurableEmbedding_addLeft a) (kozWavelet (p := p) n φ j a)]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun z => kozWavelet_add n φ j a (self_mem_nodeBall j a) z))

end Basic

/-! ### § II. Mean zero and orthogonality -/

/-- `Statement:` for primitive `φ` and `j < n`, `∫ kozWavelet n φ j a = 0`. -/
theorem kozWavelet_integral_eq_zero (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive)
    {j : ℕ} (hjn : j < n) (a : ℤ_[p]) :
    ∫ x, kozWavelet n φ j a x ∂(haarZp (p := p)) = 0 := by
  rw [kozWavelet_integral, paChar_ball_integral_eq_zero n φ hφ hjn, mul_zero]

/-- `Statement:` at `j = n`, `∫ kozWavelet n φ n a = paChar n φ a * p^(-n)`, for every `φ`. -/
theorem kozWavelet_integral_level_n (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (a : ℤ_[p]) :
    ∫ x, kozWavelet n φ n a x ∂(haarZp (p := p))
      = paChar (p := p) n φ a * ((((p : ℝ) ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [kozWavelet_integral, paChar_ball_n_integral]

-- Statement: CONTROL, `j < n` is load-bearing in `kozWavelet_integral_eq_zero`: at `j = n` the
-- integral is not `0`.
example (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (a : ℤ_[p]) :
    ∫ x, kozWavelet n φ n a x ∂(haarZp (p := p)) ≠ 0 := by
  rw [kozWavelet_integral_level_n]
  refine mul_ne_zero ?_ ?_
  · intro h
    have h1 : paChar (p := p) n φ a * paChar (p := p) n φ (-a) = 1 := by
      rw [← paChar_add, add_neg_cancel]; simp [paChar]
    rw [h, zero_mul] at h1; exact zero_ne_one h1
  · have : (0 : ℝ) < ((p : ℝ) ^ n)⁻¹ := by
      have := ‹Fact p.Prime›.out.pos; positivity
    exact_mod_cast this.ne'

/-- `Statement:` if `‖a - b‖` exceeds both `p^(-j)` and `p^(-k)`, `nodeBall j a` and `nodeBall k b` are disjoint. -/
theorem nodeBall_disjoint {j k : ℕ} {a b : ℤ_[p]}
    (hj : (p : ℝ) ^ (-(j : ℤ)) < ‖a - b‖) (hk : (p : ℝ) ^ (-(k : ℤ)) < ‖a - b‖) :
    Disjoint (nodeBall (p := p) j a) (nodeBall (p := p) k b) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  simp only [nodeBall, Set.mem_ofPred_eq] at hxa hxb
  have h := PadicInt.nonarchimedean (x - b) (-(x - a))
  rw [show x - b + -(x - a) = a - b by ring, norm_neg] at h
  have h2 := h.trans (max_le_max hxb hxa)
  rcases le_max_iff.mp h2 with h3 | h3 <;> linarith

/-- `Statement:` on disjoint nodes, `∫ conj (kozWavelet n φ j a) * kozWavelet m ψ k b = 0`. -/
theorem kozWavelet_orthogonal {n m : ℕ} (φ : AddChar (ZMod (p ^ n)) ℂ)
    (ψ : AddChar (ZMod (p ^ m)) ℂ) {j k : ℕ} {a b : ℤ_[p]}
    (hdisj : Disjoint (nodeBall (p := p) j a) (nodeBall (p := p) k b)) :
    ∫ x, starRingEnd ℂ (kozWavelet n φ j a x) * kozWavelet m ψ k b x ∂(haarZp (p := p)) = 0 := by
  have h : ∀ x, starRingEnd ℂ (kozWavelet n φ j a x) * kozWavelet m ψ k b x = 0 := by
    intro x
    by_cases hx : x ∈ nodeBall (p := p) j a
    · rw [kozWavelet_eq_zero_of_not_mem m ψ k b (Set.disjoint_left.mp hdisj hx), mul_zero]
    · rw [kozWavelet_eq_zero_of_not_mem n φ j a hx, map_zero, zero_mul]
  simp only [h, integral_zero]

/-! ### § III. The eigenfunction property -/

/-- `Statement:` `paChar n φ * vladIntegrand α j` is integrable. -/
theorem char_vladIntegrand_integrable (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (α : ℝ) (j : ℕ) :
    Integrable (fun y => paChar (p := p) n φ y * vladIntegrand (p := p) α j y) (haarZp (p := p)) := by
  have hdist : (fun y => paChar (p := p) n φ y * vladIntegrand (p := p) α j y)
      = fun y => ∑ m ∈ Finset.range j, paChar (p := p) n φ y * shellLoad (p := p) α m y := by
    funext y
    rw [vladIntegrand_eq_sum, Finset.sum_apply, Finset.mul_sum]
  rw [hdist]
  exact integrable_finsetSum _ (fun m _ => char_shellLoad_integrable n φ α m)

/-- `Statement:` for primitive `φ` and `j < n`, `∫ paChar n φ * vladIntegrand α j = 0`. -/
theorem integral_char_vladIntegrand_lt (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ)
    (hφ : φ.IsPrimitive) (α : ℝ) {j : ℕ} (hjn : j < n) :
    ∫ y, paChar (p := p) n φ y * vladIntegrand (p := p) α j y ∂(haarZp (p := p)) = 0 := by
  have hdist : (fun y => paChar (p := p) n φ y * vladIntegrand (p := p) α j y)
      = fun y => ∑ m ∈ Finset.range j, paChar (p := p) n φ y * shellLoad (p := p) α m y := by
    funext y
    rw [vladIntegrand_eq_sum, Finset.sum_apply, Finset.mul_sum]
  rw [hdist, integral_finsetSum _ (fun m _ => char_shellLoad_integrable n φ α m)]
  refine Finset.sum_eq_zero (fun m hm => ?_)
  have hmj := Finset.mem_range.mp hm
  rw [integral_char_shellLoad n φ α m, paChar_ball_integral_eq_zero n φ hφ (by omega : m < n),
    paChar_ball_integral_eq_zero n φ hφ (by omega : m + 1 < n)]
  ring

/-- `Statement:` if `p^(-j) < ‖x - a‖` and `y ∈ nodeBall j a`, then `‖x - y‖ = ‖x - a‖`. -/
theorem norm_sub_eq_of_far {j : ℕ} {a x y : ℤ_[p]} (hxa : (p : ℝ) ^ (-(j : ℤ)) < ‖x - a‖)
    (hy : y ∈ nodeBall (p := p) j a) : ‖x - y‖ = ‖x - a‖ := by
  simp only [nodeBall, Set.mem_ofPred_eq] at hy
  apply le_antisymm
  · have h := PadicInt.nonarchimedean (x - a) (-(y - a))
    rw [show x - a + -(y - a) = x - y by ring, norm_neg] at h
    exact h.trans (max_le le_rfl (by linarith))
  · have h := PadicInt.nonarchimedean (x - y) (y - a)
    rw [show x - y + (y - a) = x - a by ring] at h
    rcases le_max_iff.mp h with h1 | h1
    · exact h1
    · linarith

/-- `Statement:` for primitive `φ`, `j < n`, every `a`, `α` and `x`, `D^α (kozWavelet n φ j a) x` is the
`vladimirov_paChar_eigenvalue` eigenvalue of level `n` times `kozWavelet n φ j a x`. -/
theorem vladimirov_kozWavelet (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive)
    {j : ℕ} (hjn : j < n) (a : ℤ_[p]) (α : ℝ) (x : ℤ_[p]) :
    vladimirov α (kozWavelet n φ j a) x
      = (((1 - (p : ℝ)⁻¹) * ∑ k ∈ Finset.range n, ((p : ℝ) ^ α) ^ k
          + ((p : ℝ) ^ α) ^ (n - 1) * (p : ℝ)⁻¹ : ℝ) : ℂ) * kozWavelet n φ j a x := by
  have hn : 0 < n := by omega
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast ‹Fact p.Prime›.out.one_lt.le
  by_cases hx : x ∈ nodeBall (p := p) j a
  · rw [kozWavelet_of_mem n φ j a hx]
    unfold vladimirov
    rw [← MeasurePreserving.integral_comp (measurePreserving_add_left (haarZp (p := p)) x)
      (measurableEmbedding_addLeft x)
      (fun y => (kozWavelet n φ j a x - kozWavelet n φ j a y) * (vladimirovKernel α x y : ℂ))]
    have hpt : ∀ z, (fun y => (kozWavelet n φ j a x - kozWavelet n φ j a y)
          * (vladimirovKernel α x y : ℂ)) (x + z)
        = paChar (p := p) n φ x * (vladIntegrand (p := p) α n z
            - paChar (p := p) n φ z * vladIntegrand (p := p) α n z
            + paChar (p := p) n φ z * vladIntegrand (p := p) α j z) := by
      intro z
      show (kozWavelet n φ j a x - kozWavelet n φ j a (x + z)) * (vladimirovKernel α x (x + z) : ℂ) = _
      have hker : vladimirovKernel α x (x + z) = vladimirovKernel α 0 z := by
        have h : x - (x + z) = 0 - z := by ring
        simp only [vladimirovKernel, h]
      rw [kozWavelet_of_mem n φ j a hx, kozWavelet_add n φ j a hx z, hker]
      have hb0 : ∀ m : ℕ, ballFun (p := p) m 0 = 1 := by
        intro m
        have hmem : (0 : ℤ_[p]) ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(m : ℤ))} := by
          simp only [Set.mem_ofPred_eq, norm_zero]; positivity
        exact Set.indicator_of_mem hmem _
      simp only [vladIntegrand, hb0]
      by_cases hzn : ‖z‖ ≤ (p : ℝ) ^ (-(n : ℤ))
      · have hzj : ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ)) :=
          hzn.trans (zpow_le_zpow_right₀ hp1 (by omega))
        have hχ := paChar_eq_one_of_norm_le n φ hzn
        have hbn : ballFun (p := p) n z = 1 :=
          Set.indicator_of_mem (show z ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(n : ℤ))} from hzn) _
        have hbj : ballFun (p := p) j z = 1 :=
          Set.indicator_of_mem (show z ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hzj) _
        rw [Set.indicator_of_mem (show z ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hzj),
          hχ, hbn, hbj]
        ring
      · have hbn : ballFun (p := p) n z = 0 :=
          Set.indicator_of_notMem (show z ∉ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(n : ℤ))} from hzn) _
        by_cases hzj : ‖z‖ ≤ (p : ℝ) ^ (-(j : ℤ))
        · have hbj : ballFun (p := p) j z = 1 :=
            Set.indicator_of_mem (show z ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hzj) _
          rw [Set.indicator_of_mem (show z ∈ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hzj),
            hbn, hbj]
          ring
        · have hbj : ballFun (p := p) j z = 0 :=
            Set.indicator_of_notMem (show z ∉ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hzj) _
          rw [Set.indicator_of_notMem (show z ∉ {w : ℤ_[p] | ‖w‖ ≤ (p : ℝ) ^ (-(j : ℤ))} from hzj),
            hbn, hbj]
          ring
    have hI1 := vladIntegrand_integrable (p := p) α n
    have hI2 := char_vladIntegrand_integrable (p := p) n φ α n
    have hI3 := char_vladIntegrand_integrable (p := p) n φ α j
    have hsub : Integrable (fun y => vladIntegrand (p := p) α n y
        - paChar (p := p) n φ y * vladIntegrand (p := p) α n y) (haarZp (p := p)) := hI1.sub hI2
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_add hsub hI3, integral_sub hI1 hI2,
      integral_char_vladIntegrand_lt n φ hφ α hjn, correction_eq n hn φ hφ α]
    have hR : ∫ y, vladIntegrand (p := p) α n y ∂(haarZp (p := p))
        = vladimirov α (ballFun (p := p) n) 0 := rfl
    rw [hR, vladimirov_ballFun_zero]
    push_cast
    ring
  · rw [kozWavelet_eq_zero_of_not_mem n φ j a hx, mul_zero]
    unfold vladimirov
    have hxa : (p : ℝ) ^ (-(j : ℤ)) < ‖x - a‖ := by
      simpa [nodeBall, not_le] using hx
    have hpt : ∀ y, (kozWavelet n φ j a x - kozWavelet n φ j a y) * (vladimirovKernel α x y : ℂ)
        = -((vladimirovKernel α x a : ℝ) : ℂ) * kozWavelet n φ j a y := by
      intro y
      rw [kozWavelet_eq_zero_of_not_mem n φ j a hx]
      by_cases hy : y ∈ nodeBall (p := p) j a
      · have hk : vladimirovKernel α x y = vladimirovKernel α x a := by
          simp only [vladimirovKernel, norm_sub_eq_of_far hxa hy]
        rw [hk]; ring
      · rw [kozWavelet_eq_zero_of_not_mem n φ j a hy]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      kozWavelet_integral_eq_zero n φ hφ hjn a, mul_zero]

-- Statement: the eigenvalue in `vladimirov_kozWavelet` is `vladLam p α n`, the one of the bare character in
-- `stillPoint_is_spectral_floor`; it does not depend on `j` or `a`.
example (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (hφ : φ.IsPrimitive) {j : ℕ} (hjn : j < n)
    (a : ℤ_[p]) (α : ℝ) (x : ℤ_[p]) :
    vladimirov α (kozWavelet n φ j a) x = ((vladLam p α n : ℝ) : ℂ) * kozWavelet n φ j a x := by
  rw [vladimirov_kozWavelet n φ hφ hjn a α x]; rfl

-- Statement: `kozWavelet n φ j a` is nonzero at its centre `a`, so it is not the zero function.
example (n : ℕ) (φ : AddChar (ZMod (p ^ n)) ℂ) (j : ℕ) (a : ℤ_[p]) :
    kozWavelet n φ j a a ≠ 0 := by
  rw [kozWavelet_of_mem n φ j a (self_mem_nodeBall j a)]
  intro h
  have h1 : paChar (p := p) n φ a * paChar (p := p) n φ (-a) = 1 := by
    rw [← paChar_add, add_neg_cancel]; simp [paChar]
  rw [h, zero_mul] at h1; exact zero_ne_one h1

-- Reading: over ℚ_p, Kozyrev (arXiv:math-ph/0012019, Lemma 1 and its Remark; Theorem 2, eq. (6))
-- proves the character-times-ball wavelet is a D^α eigenfunction with the bare character's
-- eigenvalue, independent of translation; for the operator integrated over a compact ball,
-- Bikulov–Zubarev (arXiv:1504.03624, Lemma 1) give character eigenvalues depending only on |k|_p;
-- Albeverio–Kozyrev (arXiv:0708.2074, Theorem 13) give ultrametric-wavelet eigenvalues.
-- `vladimirov_kozWavelet` is an instance of this known program, on ℤ_p.

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms nodeBall
#print axioms nodeBall_measurableSet
#print axioms kozWavelet
#print axioms kozWavelet_eq_zero_of_not_mem
#print axioms kozWavelet_of_mem
#print axioms add_mem_nodeBall_iff
#print axioms kozWavelet_add
#print axioms self_mem_nodeBall
#print axioms kozWavelet_integral
#print axioms kozWavelet_integral_eq_zero
#print axioms kozWavelet_integral_level_n
#print axioms nodeBall_disjoint
#print axioms kozWavelet_orthogonal
#print axioms char_vladIntegrand_integrable
#print axioms integral_char_vladIntegrand_lt
#print axioms norm_sub_eq_of_far
#print axioms vladimirov_kozWavelet
end PurityCheck
