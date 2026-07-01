-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC39 — the dual contraction dichotomy on the Markov ν-side (#2)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC30 gave a sharp *valuation* contraction criterion for node #3 (the p-adic floor): the doubling-type
map `x ↦ c·x` makes `{0} ⊆ Q₂` a global attractor **iff** `‖c‖₂ < 1`, and fails (norm is preserved)
at the boundary `‖c‖₂ = 1`. This file builds the **Markov analog** for node #2 (the stationary
attractor in the probability simplex): a sharp *spectral* dichotomy governed by the subdominant
eigenvalue modulus `|λ₂|`.

We work concretely on `Fin 2 → ℝ` with the symmetric doubly-stochastic kernel
`P_a v = ![(1-a)·v 0 + a·v 1, a·v 0 + (1-a)·v 1]` (matrix `[[1-a,a],[a,1-a]]`, eigenvalues `1` and
`λ₂ = 1 - 2a`). The uniform distribution `w = ![1/2, 1/2]` is the stationary vector. The diagnostic
functional is the **imbalance** `imb v = v 0 - v 1`; the load-bearing algebraic fact is
`imb (P_a v) = (1 - 2a) · imb v` (the subdominant eigenvalue acting on the eigenline), while the total
mass `v 0 + v 1` is preserved. So the orbit is pinned by `imb (P_aᵏ v₀) = (1-2a)ᵏ · imb v₀`.

**GO half (spectral gap `|λ₂| < 1`).** `markov_contraction_tendsto` — for `0 < a < 1` (so
`|1 - 2a| < 1`) and any start `v₀` on the line `v 0 + v 1 = 1`, the orbit `P_aᵏ v₀ → w` (uniform).
The convergence is at the explicit geometric **rate** `|1-2a|ᵏ`, witnessed in-statement by
`markov_imbalance_pow` (`imb (P_aᵏ v₀) = (1-2a)ᵏ · imb v₀`) together with
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one` on the gap. This exhibits #2 as a genuine geometric
ν-attractor with an explicit contraction rate — structurally matching TC30's p-adic `c`-contraction.

**NO-GO half (spectral boundary `|λ₂| = 1`).** `swap_orbit_not_convergent` — the cyclic-shift /
permutation kernel `S v = ![v 1, v 0]` (the `a = 1` boundary of the family; `λ₂ = -1`, `|λ₂| = 1`)
started at `v₀ = ![1, 0]` produces the **periodic** orbit `![1,0], ![0,1], ![1,0], …` which does **not**
converge: its coordinate-0 sequence is `1, 0, 1, 0, …`, whose even/odd subsequences have distinct
limits. So #2 is **not** a single attractor at the spectral boundary — exactly dual to TC30's
`‖c‖₂ = 1 ⇒ non-attractor` for #3.

**Dichotomy capstone.** `markov_contraction_dichotomy` packages both halves with the spectral reading
`|λ₂| < 1 ⇒ attractor`, `|λ₂| = 1 ⇒ non-attractor`, mirroring TC30's valuation dichotomy.

**Honest scope.** The convergence theorem and the rate are genuine, in-statement, for the concrete
symmetric `Fin 2` family (the eigenline reduction `imb (P_a v) = (1-2a)·imb v` does the work). It is a
witnessed example matching the p-adic criterion's *shape* (a sharp contraction-modulus dichotomy in a
second ambient), **not** a proof that the p-adic `‖c‖₂` and Markov `|λ₂|` criteria are literally the
same object — that cross-ambient identity is the interpretation, not the Lean claim. No category,
inverse limit, or final coalgebra is constructed; the ν reading of "unique geometric attractor" is an
interpretation. This is an edge/rate test on node #2 of the bottom-diagram tree.
-/

namespace ZeroParadox.ZPH_MC1_TC39

open Filter Topology

/-! ### The symmetric doubly-stochastic kernel on `Fin 2` -/

/-- The symmetric kernel `P_a` acting on `Fin 2 → ℝ`: matrix `[[1-a, a],[a, 1-a]]`. -/
noncomputable def step (a : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(1 - a) * v 0 + a * v 1, a * v 0 + (1 - a) * v 1]

/-- The imbalance functional `v 0 - v 1` (the subdominant eigenline coordinate). -/
def imb (v : Fin 2 → ℝ) : ℝ := v 0 - v 1

/-- The uniform stationary vector `![1/2, 1/2]`. -/
noncomputable def unif : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Total mass is preserved by `step`. -/
theorem step_sum (a : ℝ) (v : Fin 2 → ℝ) :
    (step a v) 0 + (step a v) 1 = v 0 + v 1 := by
  simp only [step, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Eigenline identity (the load-bearing algebra).** The imbalance scales by the subdominant
    eigenvalue `1 - 2a` under one step: `imb (P_a v) = (1 - 2a) · imb v`. -/
theorem step_imb (a : ℝ) (v : Fin 2 → ℝ) :
    imb (step a v) = (1 - 2 * a) * imb v := by
  simp only [imb, step, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Iterated imbalance: `imb (P_aᵏ v₀) = (1 - 2a)ᵏ · imb v₀`. The geometric rate, in-statement. -/
theorem markov_imbalance_pow (a : ℝ) (v₀ : Fin 2 → ℝ) (k : ℕ) :
    imb ((step a)^[k] v₀) = (1 - 2 * a) ^ k * imb v₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', step_imb, ih, pow_succ]
      ring

/-- Iterated mass is preserved: `(P_aᵏ v₀) 0 + (P_aᵏ v₀) 1 = v₀ 0 + v₀ 1`. -/
theorem markov_sum_pow (a : ℝ) (v₀ : Fin 2 → ℝ) (k : ℕ) :
    ((step a)^[k] v₀) 0 + ((step a)^[k] v₀) 1 = v₀ 0 + v₀ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', step_sum, ih]

/-! ### GO half: spectral gap `|λ₂| < 1` ⇒ geometric convergence to the uniform attractor -/

/-- Coordinate recovery: a vector on the line `v 0 + v 1 = s` is determined by its imbalance:
    `v 0 = (s + imb v)/2`, `v 1 = (s - imb v)/2`. -/
theorem coord_from_imb {v : Fin 2 → ℝ} {s : ℝ} (hs : v 0 + v 1 = s) :
    v 0 = (s + imb v) / 2 ∧ v 1 = (s - imb v) / 2 := by
  constructor <;> · simp only [imb]; linarith

/-- **GO — the geometric Markov attractor.** For `0 < a < 1` (spectral gap `|1 - 2a| < 1`) and any
    start `v₀` on the probability line `v₀ 0 + v₀ 1 = 1`, the iteration `P_aᵏ v₀` converges to the
    uniform stationary vector `unif = ![1/2,1/2]`. The convergence is at the explicit geometric rate
    `|1 - 2a|ᵏ` (carried by `markov_imbalance_pow` + `tendsto_pow…of_abs_lt_one` on the gap), so #2 is
    a genuine geometric ν-attractor, structurally matching TC30's p-adic `c`-contraction. -/
theorem markov_contraction_tendsto {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {v₀ : Fin 2 → ℝ} (hv : v₀ 0 + v₀ 1 = 1) :
    Tendsto (fun k => (step a)^[k] v₀) atTop (nhds unif) := by
  -- gap modulus is < 1
  have hgap : |1 - 2 * a| < 1 := by rw [abs_lt]; constructor <;> linarith
  -- the imbalance sequence tends to 0 geometrically
  have himb : Tendsto (fun k => imb ((step a)^[k] v₀)) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hgap).mul_const (imb v₀)
    simp only [zero_mul] at h
    exact h.congr (fun k => (markov_imbalance_pow a v₀ k).symm)
  -- convergence coordinate-wise via tendsto_pi_nhds
  rw [tendsto_pi_nhds]
  intro i
  -- each iterate stays on the line v 0 + v 1 = 1
  have hline : ∀ k, ((step a)^[k] v₀) 0 + ((step a)^[k] v₀) 1 = 1 := by
    intro k; rw [markov_sum_pow]; exact hv
  fin_cases i
  · -- coordinate 0 → unif 0 = 1/2
    have e0 : ∀ k, ((step a)^[k] v₀) 0 = (1 + imb ((step a)^[k] v₀)) / 2 := fun k =>
      (coord_from_imb (hline k)).1
    simp only [unif]
    have : Tendsto (fun k => (1 + imb ((step a)^[k] v₀)) / 2) atTop (nhds ((1 + 0) / 2)) := by
      exact ((tendsto_const_nhds.add himb).div_const 2)
    simpa only [add_zero] using (this.congr (fun k => (e0 k).symm))
  · -- coordinate 1 → unif 1 = 1/2
    have e1 : ∀ k, ((step a)^[k] v₀) 1 = (1 - imb ((step a)^[k] v₀)) / 2 := fun k =>
      (coord_from_imb (hline k)).2
    simp only [unif]
    have : Tendsto (fun k => (1 - imb ((step a)^[k] v₀)) / 2) atTop (nhds ((1 - 0) / 2)) := by
      exact ((tendsto_const_nhds.sub himb).div_const 2)
    simpa only [sub_zero] using (this.congr (fun k => (e1 k).symm))

/-! ### NO-GO half: spectral boundary `|λ₂| = 1` ⇒ no single attractor (periodic orbit) -/

/-- The cyclic-shift / permutation kernel `S v = ![v 1, v 0]`: the `a = 1` boundary of the family,
    `λ₂ = -1`, `|λ₂| = 1`. -/
noncomputable def swap (v : Fin 2 → ℝ) : Fin 2 → ℝ := ![v 1, v 0]

/-- The boundary start `![1, 0]`. -/
noncomputable def e0vec : Fin 2 → ℝ := ![1, 0]

/-- The swap orbit is **periodic with period 2**: even iterates are `![1,0]`, odd are `![0,1]`.
    This is the periodic structure at the spectral boundary `|λ₂| = 1`. -/
theorem swap_orbit_eq (k : ℕ) :
    swap^[k] e0vec = if Even k then (![1, 0] : Fin 2 → ℝ) else (![0, 1] : Fin 2 → ℝ) := by
  induction k with
  | zero => simp [e0vec]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      by_cases hk : Even k
      · rw [if_pos hk, if_neg (by simp [Nat.even_add_one, hk])]
        funext i; fin_cases i <;> simp [swap]
      · rw [if_neg hk, if_pos (by simp [Nat.even_add_one, hk])]
        funext i; fin_cases i <;> simp [swap]

/-- Coordinate-0 of the swap orbit: `1, 0, 1, 0, …`. -/
theorem swap_orbit_coord0 (k : ℕ) :
    (swap^[k] e0vec) 0 = if Even k then 1 else 0 := by
  rw [swap_orbit_eq]
  by_cases hk : Even k <;> simp [hk]

/-- **NO-GO — non-convergence at the spectral boundary.** The swap orbit started at `![1,0]` does NOT
    converge: its coordinate-0 sequence is `1, 0, 1, 0, …`, whose even-indexed subsequence is constant
    `1` and odd-indexed is constant `0`. A convergent limit would force `1 = 0`. So #2 is not a single
    attractor when `|λ₂| = 1` — exactly dual to TC30's `‖c‖₂ = 1 ⇒ non-attractor` for #3. -/
theorem swap_orbit_not_convergent :
    ¬ ∃ w : Fin 2 → ℝ, Tendsto (fun k => swap^[k] e0vec) atTop (nhds w) := by
  rintro ⟨w, hw⟩
  -- coordinate-0 of the orbit converges to w 0
  have hc0 : Tendsto (fun k => (swap^[k] e0vec) 0) atTop (nhds (w 0)) :=
    (tendsto_pi_nhds.mp hw) 0
  -- rewrite as 1,0,1,0,...
  have hcoord : (fun k => (swap^[k] e0vec) 0) = fun k => if Even k then (1 : ℝ) else 0 := by
    funext k; exact swap_orbit_coord0 k
  rw [hcoord] at hc0
  -- even subsequence n ↦ 2n is constant 1, odd subsequence n ↦ 2n+1 is constant 0
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩)
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    Filter.tendsto_atTop_atTop.mpr (fun b => ⟨b, fun n hn => by omega⟩)
  have h1 : Tendsto (fun n : ℕ => if Even (2 * n) then (1 : ℝ) else 0) atTop (nhds (w 0)) :=
    hc0.comp heven
  have h0 : Tendsto (fun n : ℕ => if Even (2 * n + 1) then (1 : ℝ) else 0) atTop (nhds (w 0)) :=
    hc0.comp hodd
  -- evaluate the two constant sequences
  have h1c : (fun n : ℕ => if Even (2 * n) then (1 : ℝ) else 0) = fun _ => (1 : ℝ) := by
    funext n; rw [if_pos ⟨n, by ring⟩]
  have h0c : (fun n : ℕ => if Even (2 * n + 1) then (1 : ℝ) else 0) = fun _ => (0 : ℝ) := by
    funext n
    have : ¬ Even (2 * n + 1) := by simp
    rw [if_neg this]
  rw [h1c] at h1
  rw [h0c] at h0
  -- limits are unique: w 0 = 1 and w 0 = 0
  have e1 : w 0 = 1 := tendsto_nhds_unique h1 tendsto_const_nhds
  have e0 : w 0 = 0 := tendsto_nhds_unique h0 tendsto_const_nhds
  rw [e1] at e0
  exact one_ne_zero e0

/-! ### Dichotomy capstone -/

/-- **The sharp contraction dichotomy for node #2 (spectral).** Both halves, with the spectral
    reading: spectral gap `|λ₂| < 1` (here `0 < a < 1`) ⇒ geometric attractor at the uniform vector;
    spectral boundary `|λ₂| = 1` (the swap kernel) ⇒ no single attractor (periodic orbit). This
    mirrors TC30's valuation dichotomy for #3 (`‖c‖₂ < 1` attractor / `‖c‖₂ = 1` non-attractor) in a
    second ambient — the within-ν rate structure TC31/TC33 left unbuilt. -/
theorem markov_contraction_dichotomy :
    (∀ (a : ℝ), 0 < a → a < 1 → ∀ (v₀ : Fin 2 → ℝ), v₀ 0 + v₀ 1 = 1 →
        Tendsto (fun k => (step a)^[k] v₀) atTop (nhds unif)) ∧
    (¬ ∃ w : Fin 2 → ℝ, Tendsto (fun k => swap^[k] e0vec) atTop (nhds w)) :=
  ⟨fun _ ha0 ha1 _ hv => markov_contraction_tendsto ha0 ha1 hv, swap_orbit_not_convergent⟩

end ZeroParadox.ZPH_MC1_TC39

/-! ## Axiom Purity Check

`Classical.choice` enters via the Mathlib analysis/topology library (`Tendsto`, the specific-limits
lemmas) — a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC39

#print axioms step_imb
#print axioms markov_imbalance_pow
#print axioms markov_sum_pow
#print axioms markov_contraction_tendsto
#print axioms swap_orbit_not_convergent
#print axioms markov_contraction_dichotomy

end PurityCheck
