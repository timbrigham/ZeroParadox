import ZeroParadox.ZPH_PerronFrobenius
import ZeroParadox.ZPH_MC1_TC31
import ZeroParadox.ZPH_MeanErgodic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H: Spectral-gap irreversibility of the Markov transfer operator (the #2 DYN witness)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file is the genuine **DYN / arrow-of-time** witness for the #2 Markov bottom. It establishes that
the relaxation of a *mixing* finite Markov chain toward its stationary attractor is **irreversible**:
the transfer operator `T` is non-injective, and any off-stationary mode with eigenvalue `|λ| < 1`
decays geometrically to zero and is lost.

Three results:

* **Lemma `tendsto_norm_iterate_zero` (general geometric decay).** If `v` is an eigenvector of `T f`
  with real eigenvalue `λ` and `|λ| < 1`, then `‖(T f)^[m] v‖ → 0`. (Eigenvectors iterate as
  `(T f)^[m] v = λ^m • v`, and `‖λ^m • v‖ = |λ|^m * ‖v‖ → 0`.)
* **Proposition `fullMix_eigen_zero` (a concrete mixing chain with a genuine gap).** The fully-mixing
  2-state kernel `fullMix` (every state → uniform) is doubly-stochastic and has the mean-zero vector
  `v₀ = ![1, -1]` as an eigenvector with eigenvalue `0` — the maximal spectral gap.
* **Theorem `fullMix_not_injective` (irreversibility — the DYN witness).** Since `T fullMix v₀ = 0`
  with `v₀ ≠ 0`, the transfer operator `T fullMix` is **not injective**: the mixing-chain relaxation
  provably loses information and cannot be reversed.

**Honest scope / FENCE.** Irreversibility is **not** universal for doubly-stochastic chains. A
permutation / cyclic chain (`ZPH_MC1_TC31.cycKernel`) has eigenvalues on the unit circle (no gap), is
injective, and does **not** mix (`ZPH_MC1_TC39.swap_orbit_not_convergent`). The gap — and hence
irreversibility — requires a genuinely **mixing** chain; `fullMix` is the concrete witness. So this
fills the #2 DYN cell in the spectral-gap sense, *conditional on mixing*. It is the genuine version,
not the thin "convergence = irreversible" re-reading.

**Prior art (no novelty claimed).** This is standard finite-chain Perron–Frobenius / spectral-gap theory:
an off-stationary eigenmode with `|λ| < 1` decays geometrically, and a mixing chain's relaxation loses the
off-stationary modes. The standard home is spectral-gap → geometric-ergodicity (Levin–Peres, *Markov
Chains and Mixing Times*; non-reversible case, Kontoyiannis–Meyn, arXiv:0906.5322). The value here is only
a concrete in-kernel witness (`fullMix`, eigenvalue 0, `![1,-1]`), fenced to the mixing case.

## Structure

- § I   General geometric decay from a spectral gap
- § II  A concrete mixing chain with a maximal gap (`fullMix`)
- § III Irreversibility: non-injectivity of the relaxation operator
-/

namespace ZeroParadox.MarkovSpectralGap

open scoped BigOperators
open Filter Topology
open ZeroParadox.PerronFrobenius
open ZeroParadox.MeanErgodic (DoublyStochastic)

variable {n : ℕ}

/-! ## § I — General geometric decay from a spectral gap -/

/-- **Eigenvector iterate.** If `T f v = λ • v` then `(T f)^[m] v = λ ^ m • v`. -/
lemma iterate_eigen (f : Fin n → PMF (Fin n)) {v : Fin n → ℝ} {lam : ℝ}
    (hv : T f v = lam • v) (m : ℕ) : (T f)^[m] v = lam ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply' (T f) m v, ih, map_smul, hv, smul_smul, pow_succ,
        mul_comm]

/-- **Lemma — general geometric decay.** An eigenvector with eigenvalue `|λ| < 1` decays to zero
    under iteration of the transfer operator. -/
lemma tendsto_norm_iterate_zero (f : Fin n → PMF (Fin n)) {v : Fin n → ℝ} {lam : ℝ}
    (hv : T f v = lam • v) (hlam : |lam| < 1) :
    Tendsto (fun m => ‖(T f)^[m] v‖) atTop (𝓝 0) := by
  have hrw : ∀ m : ℕ, ‖(T f)^[m] v‖ = |lam| ^ m * ‖v‖ := by
    intro m
    rw [iterate_eigen f hv m, norm_smul, Real.norm_eq_abs, abs_pow]
  simp_rw [hrw]
  have hpow : Tendsto (fun m : ℕ => |lam| ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg lam) hlam
  simpa using hpow.mul_const ‖v‖

/-! ## § II — A concrete mixing chain with a maximal gap -/

/-- The fully-mixing 2-state kernel: every state maps to the uniform distribution. -/
noncomputable def fullMix : Fin 2 → PMF (Fin 2) := fun _ => PMF.uniformOfFintype (Fin 2)

/-- `fullMix` is doubly-stochastic. -/
theorem fullMix_doublyStochastic : DoublyStochastic fullMix := by
  intro k
  have hval : ∀ j : Fin 2, ((fullMix j) k).toReal = 1 / 2 := by
    intro j
    simp only [fullMix, PMF.uniformOfFintype_apply, Fintype.card_fin]
    norm_num
  simp_rw [hval]
  norm_num

/-- The mean-zero eigenvector `v₀ = ![1, -1]`. -/
def v0 : Fin 2 → ℝ := ![1, -1]

/-- **Proposition — concrete mixing chain with a genuine (maximal) gap.** `v₀ = ![1, -1]` is an
    eigenvector of `T fullMix` with eigenvalue `0`: the averaging kernel annihilates the mean-zero
    mode. -/
theorem fullMix_eigen_zero : T fullMix v0 = (0 : ℝ) • v0 := by
  rw [zero_smul]
  funext k
  rw [T_apply, Pi.zero_apply, Fin.sum_univ_two]
  have hval : ∀ j : Fin 2, ((fullMix j) k).toReal = 1 / 2 := by
    intro j
    simp only [fullMix, PMF.uniformOfFintype_apply, Fintype.card_fin]
    norm_num
  rw [hval 0, hval 1]
  simp [v0]

/-! ## § III — Irreversibility: non-injectivity of the relaxation operator -/

/-- `v₀ ≠ 0`. -/
theorem v0_ne_zero : v0 ≠ 0 := by
  intro h
  have h0 : v0 0 = (0 : Fin 2 → ℝ) 0 := by rw [h]
  simp [v0] at h0

/-- **Theorem — irreversibility (the DYN witness).** The relaxation operator of the mixing chain
    `fullMix` is **not injective**: it sends the nonzero mean-zero mode `v₀` to `0`, so the mixing
    relaxation provably loses information and cannot be reversed. -/
theorem fullMix_not_injective : ¬ Function.Injective (T fullMix) := by
  intro hinj
  -- T fullMix v0 = 0 = T fullMix 0, but v0 ≠ 0
  have h1 : T fullMix v0 = T fullMix 0 := by
    rw [fullMix_eigen_zero, zero_smul, map_zero]
  exact v0_ne_zero (hinj h1)

/-- **The gap→decay machinery applied to the concrete witness.** `fullMix`'s mean-zero mode `v₀`
    (eigenvalue `0`, the maximal gap) decays under iteration: `‖(T fullMix)^[m] v₀‖ → 0`. This connects the
    general decay lemma `tendsto_norm_iterate_zero` to the concrete chain — the off-stationary mode is
    irreversibly relaxed away. (λ=0 is the immediate-collapse extreme; the general lemma covers any
    `|λ|<1`, genuinely geometric for `λ ∈ (0,1)` — a partial-mixing chain.) -/
theorem fullMix_mode_decays :
    Filter.Tendsto (fun m => ‖(T fullMix)^[m] v0‖) Filter.atTop (𝓝 0) :=
  tendsto_norm_iterate_zero fullMix fullMix_eigen_zero (by norm_num)

end ZeroParadox.MarkovSpectralGap

/-! ## Axiom Purity Check

All results depend only on `[propext, Classical.choice, Quot.sound]`. `Classical.choice` enters via
the Mathlib PMF / `tsum` / ENNReal / analysis libraries (a library dependency, not a new commitment);
no `sorryAx` appears. -/

section PurityCheck
open ZeroParadox.MarkovSpectralGap

#print axioms iterate_eigen
#print axioms tendsto_norm_iterate_zero
#print axioms fullMix_doublyStochastic
#print axioms fullMix_eigen_zero
#print axioms v0_ne_zero
#print axioms fullMix_not_injective
#print axioms fullMix_mode_decays

end PurityCheck
