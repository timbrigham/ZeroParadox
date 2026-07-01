import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# P8 re-attempt: ε₀ → 0 in ℤ₂ via a tower-rank 2-adic encoding

The parked "ZP-B route" (zpl_cantor_zp2_bridge): encode ordinals < ε₀ into ℤ₂ so the ω-tower's
encodings converge to 0 = ⊥, giving ε₀ ↦ ⊥ without Gentzen. Genuine 20-iteration re-attempt.

Strategy (stub-first): (1) the 2-adic limit core — powers of 2 shrink to 0 in ℤ₂; (2) the tower-rank
encoding `α ↦ 2 ^ (rank α)` where `rank α` is the least tower stage above α (`lt_epsilon_zero`);
(3) the tower's encodings converge to 0.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.P8

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

open Filter Topology

/-- **The 2-adic limit core.** The powers of 2 shrink to 0 in ℤ₂ — the geometric heart of "the tower's
    encoding converges to the bottom 0" (`v₂(2ⁿ) = n → ∞`, so `2ⁿ → 0`). -/
theorem two_pow_tendsto_zero :
    Tendsto (fun n : ℕ => (2 : ℤ_[2]) ^ n) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  have h : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_cast
  rw [h, PadicInt.norm_p]
  norm_num

open Ordinal

/-- The ω-tower is monotone in its index: `(ω^·)^[n] 0 ≤ (ω^·)^[m] 0` for `n ≤ m`, since `x ≤ ω^x`. -/
theorem tower_monotone : Monotone (fun n : ℕ => (fun a => ω ^ a)^[n] 0) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Function.iterate_succ_apply']
  exact (Ordinal.isNormal_opow one_lt_omega0).strictMono.le_apply

open Classical in
/-- **Tower-rank.** For `α < ε₀`, the least `n` with `α` below the `n`-th ω-tower stage
    (`lt_epsilon_zero`). The "ordinal depth" of `α` in the tower. -/
noncomputable def cnfRank (α : {α : Ordinal // α < ε₀}) : ℕ :=
  Nat.find (lt_epsilon_zero.mp α.2)

/-- **The tower-rank 2-adic encoding** `α ↦ 2 ^ (rank α) : ℤ₂`. Higher tower depth ↦ higher 2-adic
    valuation ↦ closer to the bottom 0. -/
noncomputable def cnf_encode (α : {α : Ordinal // α < ε₀}) : ℤ_[2] :=
  (2 : ℤ_[2]) ^ cnfRank α

/-- The `k`-th ω-tower stage as an element of `{α < ε₀}`. -/
noncomputable def towerOrd (k : ℕ) : {α : Ordinal // α < ε₀} :=
  ⟨(fun a => ω ^ a)^[k] 0, iterate_omega0_opow_lt_epsilon_zero k⟩

/-- The tower's rank grows without bound: `cnfRank (towerOrd k) ≥ k`. -/
theorem k_le_cnfRank_towerOrd (k : ℕ) : k ≤ cnfRank (towerOrd k) := by
  unfold cnfRank
  rw [Nat.le_find_iff]
  intro m hm hlt
  exact absurd (tower_monotone hm.le) (not_le.2 hlt)

/-- **The ε₀ → ⊥ bridge (P8 core).** The tower-rank 2-adic encodings of the ω-tower converge to 0 in
    ℤ₂: as the ordinals climb the tower toward ε₀, their encodings shrink to the bottom 0 = ⊥. -/
theorem cnf_encode_tower_tendsto_zero :
    Tendsto (fun k => cnf_encode (towerOrd k)) atTop (𝓝 0) := by
  have hrank : Tendsto (fun k => cnfRank (towerOrd k)) atTop atTop :=
    tendsto_atTop_mono k_le_cnfRank_towerOrd tendsto_id
  exact two_pow_tendsto_zero.comp hrank

end ZeroParadox.P8

/-! ## Honest scope
The encoding here is the **tower-rank** map `α ↦ 2 ^ (least tower stage above α)`, not the canonical
Cantor-Normal-Form binary encoding the parked note envisioned. It genuinely realizes the *geometric*
goal — ε₀ is the 2-adic limit of the ω-tower (`cnf_encode_tower_tendsto_zero`), so ε₀ ↦ 0 = ⊥ — but
because the rank is *defined via* the tower, the valuation growth is built in: this is a constructed
witness of the limit, not a strongly *independent* ordinal↔2-adic structural identity. The canonical-CNF
version (revealing genuine binary structure, a stronger independent route) remains the harder open piece.
What changed vs. the earlier (invalid) deferral: the note's stated goal — a map `{α<ε₀}→ℤ₂` whose tower
images converge to 0 — is now a proven theorem, built in 4 iterations. -/

section PurityCheck
open ZeroParadox.P8
#print axioms two_pow_tendsto_zero
#print axioms cnf_encode_tower_tendsto_zero
end PurityCheck
