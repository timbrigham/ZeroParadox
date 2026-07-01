import ZeroParadox.ZPN_P8

set_option maxHeartbeats 800000

/-!
# B6 (pipeline): canonical (CNF / log-ω) ordinal → 2-adic, valuation growth NOT tower-defined

P8 built `α ↦ 2 ^ (least tower stage above α)`: a real ε₀→0 limit, but the rank is defined *via the
tower*, so the valuation growth is built into the encoding — a constructed witness, not an independent
ordinal↔2-adic identity. B6 closes that gap with a measure read from the ordinal's **own** Cantor-normal
structure: `cnfLogDepth α` = the number of times you can apply `log ω` before reaching 0. `log ω α` is
the leading CNF exponent of `α`; iterating it walks down the CNF tree. The tower appears **only in the
bridge theorem**, never in the definition — so the convergence is a *theorem* about canonical structure,
not a property baked into the map.

**Falsifiable prediction:** the canonical log-depth encodings of the ω-tower still converge to 0. Would
FAIL if `log ω` did not strictly descend below ε₀ (then the depth could be ill-defined or bounded). It
descends (`log_lt_self`, from ε₀ being the least fixed point of `ω^·`), so the prediction holds.

Independence vs P8: the encoding `cnfLogDepth` makes **no reference to the tower** — it is defined by
`log ω`-iteration on the ordinal itself. The growth `k ≤ cnfLogDepth (towerOrd k)` is then earned, via
`log ω (ω^β) = β` (`log_opow`) peeling one canonical level per step.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.B6

open Ordinal Filter Topology ZeroParadox.P8

/-- Below ε₀, `ω^·` is strict: `o < ω ^ o` for `o < ε₀` (ε₀ is the least fixed point of `ω^·`,
    `epsilon_zero_le_of_omega0_opow_le`). -/
theorem self_lt_omega0_opow {o : Ordinal} (ho : o < ε₀) : o < ω ^ o := by
  by_contra h
  exact absurd (epsilon_zero_le_of_omega0_opow_le (not_lt.1 h)) (not_le.2 ho)

/-- **Strict descent of `log ω` below ε₀.** For `0 ≠ α < ε₀`, `log ω α < α`: the leading CNF exponent
    is strictly smaller, so iterating `log ω` terminates. -/
theorem log_lt_self {α : Ordinal} (h0 : α ≠ 0) (hε : α < ε₀) : Ordinal.log ω α < α := by
  have hL : Ordinal.log ω α < ε₀ := lt_of_le_of_lt (Ordinal.log_le_self _ _) hε
  calc Ordinal.log ω α < ω ^ Ordinal.log ω α := self_lt_omega0_opow hL
    _ ≤ α := Ordinal.opow_log_le_self ω h0

/-- The `log ω`-iteration reaches 0 for every `o < ε₀` (well-founded descent). -/
theorem logDepthExists : ∀ o : Ordinal, o < ε₀ →
    ∃ n : ℕ, (fun a => Ordinal.log ω a)^[n] o = 0 := by
  intro o
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    intro ho
    rcases eq_or_ne o 0 with h0 | h0
    · exact ⟨0, by simpa using h0⟩
    · have hlt : Ordinal.log ω o < o := log_lt_self h0 ho
      obtain ⟨m, hm⟩ := ih (Ordinal.log ω o) hlt (lt_trans hlt ho)
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

open Classical in
/-- **Canonical log-depth** of `α < ε₀`: the number of `log ω` steps to reach 0. Read from the
    ordinal's own CNF structure (leading-exponent descent), with NO reference to the tower. -/
noncomputable def cnfLogDepth (α : {α : Ordinal // α < ε₀}) : ℕ :=
  Nat.find (logDepthExists α.1 α.2)

/-- One canonical step: `log ω` of tower stage `k+1` is tower stage `k`, since
    `towerOrd (k+1) = ω ^ (towerOrd k)` and `log ω (ω^β) = β`. The tower's leading CNF exponent. -/
theorem log_tower_step (k : ℕ) :
    Ordinal.log ω (towerOrd (k + 1)).1 = (towerOrd k).1 := by
  show Ordinal.log ω ((fun a => ω ^ a)^[k + 1] 0) = (fun a => ω ^ a)^[k] 0
  rw [Function.iterate_succ_apply', Ordinal.log_opow one_lt_omega0]

/-- Tower stage `i+1` is positive: `towerOrd (i+1) = ω ^ _ ≥ 1`. -/
theorem towerOrd_succ_pos (i : ℕ) : (0 : Ordinal) < (towerOrd (i + 1)).1 := by
  show (0 : Ordinal) < (fun a => ω ^ a)^[i + 1] 0
  rw [Function.iterate_succ_apply']
  exact Ordinal.opow_pos _ Ordinal.omega0_pos

/-- Iterating `log ω` peels tower levels: `(log ω)^[m] (towerOrd k) = towerOrd (k - m)` for `m ≤ k`. -/
theorem iterate_log_tower : ∀ m k : ℕ, m ≤ k →
    (fun a => Ordinal.log ω a)^[m] (towerOrd k).1 = (towerOrd (k - m)).1 := by
  intro m
  induction m with
  | zero => intro k _; simp
  | succ m ih =>
    intro k hk
    have hmk : m ≤ k := Nat.le_of_succ_le hk
    rw [Function.iterate_succ_apply', ih k hmk]
    -- k - m ≥ 1 since m < k
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hk)
    have hjk : j = k - (m + 1) := by omega
    rw [hj, log_tower_step, hjk]

/-- **Canonical growth.** `k ≤ cnfLogDepth (towerOrd k)`: the canonical log-depth of tower stage `k`
    is at least `k`, because the first `k` `log ω`-iterations stay nonzero (they are higher tower
    stages). Growth earned from canonical CNF structure, not built into the encoding. -/
theorem k_le_cnfLogDepth (k : ℕ) : k ≤ cnfLogDepth (towerOrd k) := by
  unfold cnfLogDepth
  rw [Nat.le_find_iff]
  intro m hm hp
  rw [iterate_log_tower m k hm.le] at hp
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_ne_zero_of_lt hm)
  rw [hj] at hp
  exact (towerOrd_succ_pos j).ne' hp

/-- **The canonical ordinal → 2-adic encoding** `α ↦ 2 ^ (cnfLogDepth α)`. -/
noncomputable def cnf_log_encode (α : {α : Ordinal // α < ε₀}) : ℤ_[2] :=
  (2 : ℤ_[2]) ^ cnfLogDepth α

/-- **B6 — the canonical ε₀ → ⊥ bridge.** The canonical (log-ω-depth) 2-adic encodings of the ω-tower
    converge to 0 in ℤ₂ — the same ε₀ ↦ ⊥ limit as P8, now with the valuation growth read from the
    ordinal's own CNF structure rather than defined via the tower. -/
theorem cnf_log_encode_tower_tendsto_zero :
    Tendsto (fun k => cnf_log_encode (towerOrd k)) atTop (𝓝 0) := by
  have hdepth : Tendsto (fun k => cnfLogDepth (towerOrd k)) atTop atTop :=
    tendsto_atTop_mono k_le_cnfLogDepth tendsto_id
  exact two_pow_tendsto_zero.comp hdepth

end ZeroParadox.B6

/-! ## Honest scope
`cnfLogDepth` is defined purely by `log ω`-iteration on the ordinal (its leading CNF exponents) — the
tower enters only in the bridge theorem `cnf_log_encode_tower_tendsto_zero`, not in the encoding. This
is the independence P8 lacked (there the rank was defined via the tower). It is still a *depth/height*
of the CNF tree, not the full base-ω positional binary digits; a digit-faithful ℤ₂ encoding remains a
heavier construction. But B6's claim — a canonical, non-tower-defined ordinal→2-adic map whose tower
images converge to 0 — is now a proven theorem. -/

section PurityCheck
open ZeroParadox.B6
#print axioms cnf_log_encode_tower_tendsto_zero
#print axioms log_lt_self
end PurityCheck
