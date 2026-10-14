-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The dual contraction dichotomy on the Markov ν-side (#2)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---
## Formal Overview (AI-assisted)
The Markov analog, on `Fin 2 → ℝ`, of `ZeroParadox/Valuation/ContractionRate.lean`'s p-adic contraction
dichotomy; both halves are `markov_contraction_dichotomy`. Convergence covers `0 < a < 1`; the
non-convergence half is one swap orbit (`swap_orbit_not_convergent`), and the `example` after it is
the other endpoint `a = 0`, where every orbit is constant. Prior art: Levin–Peres, *Markov Chains and
Mixing Times*. -/

namespace ZeroParadox

open Filter Topology

/-! ### The symmetric doubly-stochastic kernel on `Fin 2` -/

/-- The symmetric kernel `P_a` acting on `Fin 2 → ℝ`: matrix `[[1-a, a],[a, 1-a]]`. -/
noncomputable def markovStep (a : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(1 - a) * v 0 + a * v 1, a * v 0 + (1 - a) * v 1]

/-- The imbalance functional `v 0 - v 1` (the subdominant eigenline coordinate). -/
def imb (v : Fin 2 → ℝ) : ℝ := v 0 - v 1

/-- The uniform stationary vector `![1/2, 1/2]`. -/
noncomputable def unif : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Total mass is preserved by `markovStep`. -/
theorem step_sum (a : ℝ) (v : Fin 2 → ℝ) :
    (markovStep a v) 0 + (markovStep a v) 1 = v 0 + v 1 := by
  simp only [markovStep, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Eigenline identity (the load-bearing algebra).** The imbalance scales by the subdominant
    eigenvalue `1 - 2a` under one step: `imb (P_a v) = (1 - 2a) · imb v`. -/
theorem step_imb (a : ℝ) (v : Fin 2 → ℝ) :
    imb (markovStep a v) = (1 - 2 * a) * imb v := by
  simp only [imb, markovStep, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- Iterated imbalance: `imb (P_aᵏ v₀) = (1 - 2a)ᵏ · imb v₀`. The geometric rate, in-statement. -/
theorem markov_imbalance_pow (a : ℝ) (v₀ : Fin 2 → ℝ) (k : ℕ) :
    imb ((markovStep a)^[k] v₀) = (1 - 2 * a) ^ k * imb v₀ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', step_imb, ih, pow_succ]
      ring

/-- Iterated mass is preserved: `(P_aᵏ v₀) 0 + (P_aᵏ v₀) 1 = v₀ 0 + v₀ 1`. -/
theorem markov_sum_pow (a : ℝ) (v₀ : Fin 2 → ℝ) (k : ℕ) :
    ((markovStep a)^[k] v₀) 0 + ((markovStep a)^[k] v₀) 1 = v₀ 0 + v₀ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', step_sum, ih]

/-! ### GO half: `|1 - 2a| < 1` ⇒ geometric convergence to the uniform attractor -/

/-- Coordinate recovery: a vector on the line `v 0 + v 1 = s` is determined by its imbalance:
    `v 0 = (s + imb v)/2`, `v 1 = (s - imb v)/2`. -/
theorem coord_from_imb {v : Fin 2 → ℝ} {s : ℝ} (hs : v 0 + v 1 = s) :
    v 0 = (s + imb v) / 2 ∧ v 1 = (s - imb v) / 2 := by
  constructor <;> · simp only [imb]; linarith

/-- **GO — the geometric Markov attractor.** For `0 < a < 1` (so `|1 - 2a| < 1`) and any
    start `v₀` on the probability line `v₀ 0 + v₀ 1 = 1`, the iteration `P_aᵏ v₀` converges to the
    uniform stationary vector `unif = ![1/2,1/2]`. The convergence is at the explicit geometric rate
    `|1 - 2a|ᵏ` (carried by `markov_imbalance_pow` + `tendsto_pow…of_abs_lt_one`), so #2 is
    a genuine geometric ν-attractor, structurally matching `ZeroParadox/Valuation/ContractionRate.lean`'s p-adic `c`-contraction. -/
theorem markov_contraction_tendsto {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {v₀ : Fin 2 → ℝ} (hv : v₀ 0 + v₀ 1 = 1) :
    Tendsto (fun k => (markovStep a)^[k] v₀) atTop (nhds unif) := by
  -- gap modulus is < 1
  have hgap : |1 - 2 * a| < 1 := by rw [abs_lt]; constructor <;> linarith
  -- the imbalance sequence tends to 0 geometrically
  have himb : Tendsto (fun k => imb ((markovStep a)^[k] v₀)) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hgap).mul_const (imb v₀)
    simp only [zero_mul] at h
    exact h.congr (fun k => (markov_imbalance_pow a v₀ k).symm)
  -- convergence coordinate-wise via tendsto_pi_nhds
  rw [tendsto_pi_nhds]
  intro i
  -- each iterate stays on the line v 0 + v 1 = 1
  have hline : ∀ k, ((markovStep a)^[k] v₀) 0 + ((markovStep a)^[k] v₀) 1 = 1 := by
    intro k; rw [markov_sum_pow]; exact hv
  fin_cases i
  · -- coordinate 0 → unif 0 = 1/2
    have e0 : ∀ k, ((markovStep a)^[k] v₀) 0 = (1 + imb ((markovStep a)^[k] v₀)) / 2 := fun k =>
      (coord_from_imb (hline k)).1
    simp only [unif]
    have : Tendsto (fun k => (1 + imb ((markovStep a)^[k] v₀)) / 2) atTop (nhds ((1 + 0) / 2)) := by
      exact ((tendsto_const_nhds.add himb).div_const 2)
    simpa only [add_zero] using (this.congr (fun k => (e0 k).symm))
  · -- coordinate 1 → unif 1 = 1/2
    have e1 : ∀ k, ((markovStep a)^[k] v₀) 1 = (1 - imb ((markovStep a)^[k] v₀)) / 2 := fun k =>
      (coord_from_imb (hline k)).2
    simp only [unif]
    have : Tendsto (fun k => (1 - imb ((markovStep a)^[k] v₀)) / 2) atTop (nhds ((1 - 0) / 2)) := by
      exact ((tendsto_const_nhds.sub himb).div_const 2)
    simpa only [sub_zero] using (this.congr (fun k => (e1 k).symm))

/-! ### NO-GO half: the swap kernel (`a = 1`) has a non-convergent orbit -/

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
    `1` and odd-indexed is constant `0`. A convergent limit would force `1 = 0`. So under the swap
    kernel #2 is not a single attractor; the `example` below is the other endpoint `a = 0`. -/
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

-- Statement: control, at `a = 0` (where `1 - 2a = 1`) `markovStep 0` is the identity, so every orbit
-- is constant and converges.
example (v₀ : Fin 2 → ℝ) (k : ℕ) : (markovStep 0)^[k] v₀ = v₀ := by
  have h : markovStep 0 = id := by
    funext v i; fin_cases i <;> simp [markovStep]
  rw [h, Function.iterate_id]; rfl

/-! ### Dichotomy capstone -/

/-- **The sharp contraction dichotomy for node #2 (spectral).** Both halves, with the spectral
    reading: `|λ₂| < 1` (here `0 < a < 1`) ⇒ geometric attractor at the uniform vector;
    spectral boundary `|λ₂| = 1` (the swap kernel) ⇒ no single attractor (periodic orbit). This
    mirrors `ZeroParadox/Valuation/ContractionRate.lean`'s valuation dichotomy for #3 (`‖c‖₂ < 1` attractor / `‖c‖₂ = 1` non-attractor) in a
    second ambient — the within-ν rate structure `ZeroParadox/Computability/StationaryUnique.lean` and `ZeroParadox/Valuation/NuRateEdge.lean` left unbuilt. -/
theorem markov_contraction_dichotomy :
    (∀ (a : ℝ), 0 < a → a < 1 → ∀ (v₀ : Fin 2 → ℝ), v₀ 0 + v₀ 1 = 1 →
        Tendsto (fun k => (markovStep a)^[k] v₀) atTop (nhds unif)) ∧
    (¬ ∃ w : Fin 2 → ℝ, Tendsto (fun k => swap^[k] e0vec) atTop (nhds w)) :=
  ⟨fun _ ha0 ha1 _ hv => markov_contraction_tendsto ha0 ha1 hv, swap_orbit_not_convergent⟩

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` enters via Mathlib — the real carrier for the definitions, and the
analysis/topology library (`Tendsto`, the specific-limits lemmas) for the limit results — a library
dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox

#print axioms markovStep
#print axioms step_imb
#print axioms markov_imbalance_pow
#print axioms markov_sum_pow
#print axioms markov_contraction_tendsto
#print axioms swap_orbit_not_convergent
#print axioms markov_contraction_dichotomy

end PurityCheck
