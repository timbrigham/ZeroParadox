-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): branch spaces of nonempty discrete levels are perfect exactly when infinitely many levels branch. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.BranchingSnapChain
import ZeroParadox.Valuation.PadicPerfect
import Mathlib.Topology.Perfect
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic

/-!
# Nonempty discrete levels: the branch space is perfect iff infinitely many levels branch

## Engineer's Take

The shape it makes is like a tree that can go to infinite denseness, from an infinite number of points
above. The branching itself is what forces the density. It feels like an elevation of a local to a global
variable. You iterate five times inside your function and you count, and the other is your instance, the
output object with a value of five.

---

## Formal Overview (AI-assisted)
`Statement:` CARRIER — a product of nonempty discrete levels is perfect iff infinitely many levels branch
(`perfectSpace_pi_iff`); on `ℕ → Bool` and, separately, on `ℤ_[2]`, perfection together with no path
joining distinct points; no map between the two carriers is stated.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Topology Filter Set

/-! ### § I. Perfect iff infinitely many levels branch -/

/-- `Statement:` for nonempty discrete levels `β n`, the branch space `∀ n, β n` has no isolated point
iff `{n | Nontrivial (β n)}` is infinite. The branching-to-perfect direction generalizes `boundary_perfect`
(`ZeroParadox/Valuation/CompletenessCriticProbe.lean`); the converse uses `Nonempty` (third control).
`∀ n, β n` is the body of the full tree with `β n` offspring at level `n`; the iff is standard for tree
bodies: Bellaïche, arXiv:2407.21763, Prop. 4.23; cf. Foreman, arXiv:2110.08881, Prop. 14.
Lean: `TauCeti.perfectSpace_pi` (TauCetiProject/TauCeti) proves the if-direction for any infinite product
of nontrivial spaces, without discreteness. -/
theorem perfectSpace_pi_iff (β : ℕ → Type) [∀ n, TopologicalSpace (β n)]
    [∀ n, DiscreteTopology (β n)] [∀ n, Nonempty (β n)] :
    PerfectSpace (∀ n, β n) ↔ {n | Nontrivial (β n)}.Infinite := by
  classical
  rw [perfectSpace_iff_forall_not_isolated]
  constructor
  · intro h hfin
    obtain ⟨N, hN⟩ := hfin.bddAbove
    let x : ∀ n, β n := fun n => Classical.arbitrary _
    have hsub : ∀ n, N < n → Subsingleton (β n) := fun n hn =>
      not_nontrivial_iff_subsingleton.mp fun hn' => absurd (hN hn') (not_le.mpr hn)
    have hopen : IsOpen ({x} : Set (∀ n, β n)) := by
      have : ({x} : Set (∀ n, β n)) = (Finset.range (N + 1) : Set ℕ).pi (fun i => {x i}) := by
        ext y
        simp only [mem_singleton_iff, Set.mem_pi, Finset.coe_range]
        refine ⟨fun h i _ => by simp [h], fun h => funext fun i => ?_⟩
        by_cases hi : i < N + 1
        · exact h i hi
        · exact (hsub i (by omega)).elim _ _
      rw [this]
      exact isOpen_set_pi (Finset.finite_toSet _) fun _ _ => isOpen_discrete _
    have := h x
    rw [(isOpen_singleton_iff_punctured_nhds x).mp hopen] at this
    exact this.ne rfl
  · intro hinf x
    rw [← mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhds]
    intro U hU
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hsub⟩ := hU
    obtain ⟨n, hn, hnI⟩ := hinf.exists_notMem_finset hI.toFinset
    have : Nontrivial (β n) := hn
    obtain ⟨b, hb⟩ := exists_ne (x n)
    refine ⟨Function.update x n b, hsub fun i hi => ?_, ?_⟩
    · have hin : i ≠ n := fun h => hnI (by simpa [h] using hi)
      rw [Function.update_of_ne hin]
      exact mem_of_mem_nhds (ht i)
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      exact hb (by simpa using congrFun h n)

/-- `Statement:` Cantor space `ℕ → Bool` is perfect. -/
theorem cantorSpace_perfect : PerfectSpace (ℕ → Bool) := by
  rw [perfectSpace_pi_iff (fun _ => Bool)]
  have : {n : ℕ | Nontrivial Bool} = univ :=
    eq_univ_of_forall fun _ => show Nontrivial Bool from inferInstance
  rw [this]; exact infinite_univ

-- Control `Statement:` no level branches: `ℕ → Unit` is not perfect.
example : ¬ PerfectSpace (ℕ → Unit) := by
  rw [perfectSpace_pi_iff (fun _ => Unit)]
  have : {n : ℕ | Nontrivial Unit} = ∅ := eq_empty_of_forall_notMem fun _ h => not_nontrivial Unit h
  rw [this]; exact not_infinite.mpr finite_empty

-- Control `Statement:` branching only at levels 0, 1, 2 is not perfect.
example : ¬ PerfectSpace (∀ n : ℕ, Fin (if n < 3 then 2 else 1)) := by
  have : ∀ n : ℕ, Nonempty (Fin (if n < 3 then 2 else 1)) := fun n => ⟨⟨0, by split <;> omega⟩⟩
  rw [perfectSpace_pi_iff]
  apply not_infinite.mpr
  apply (finite_lt_nat 3).subset
  intro n hn
  simp only [mem_ofPred_eq, Fin.nontrivial_iff_two_le] at hn
  by_contra h
  simp only [mem_ofPred_eq] at h
  simp only [h, ↓reduceIte] at hn
  omega

-- Control `Statement:` `Nonempty` is load-bearing: an empty product is vacuously perfect while
-- no level branches.
example : PerfectSpace (∀ n : ℕ, Fin (if n = 0 then 0 else 1)) := by
  constructor
  intro x _
  exact absurd (x 0).isLt (by simp)

/-! ### § II. Crowded and cut -/

/-- `Statement:` with infinitely many branching levels, the branch space is perfect and no continuous
path from `[0,1]` joins two distinct points. -/
theorem pi_crowded_and_cut (β : ℕ → Type) [∀ n, TopologicalSpace (β n)]
    [∀ n, DiscreteTopology (β n)] [∀ n, Nonempty (β n)]
    (hinf : {n | Nontrivial (β n)}.Infinite) :
    PerfectSpace (∀ n, β n) ∧ ∀ x y : (∀ n, β n), x ≠ y →
      ¬ ∃ γ : C(Set.Icc (0 : ℝ) 1, ∀ n, β n), γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y :=
  ⟨(perfectSpace_pi_iff β).mpr hinf, fun _ _ hxy => disconnectedness_forbids_path hxy⟩

/-- `Statement:` Cantor space `ℕ → Bool` is perfect and no continuous path joins two distinct points. -/
theorem cantorSpace_crowded_and_cut :
    PerfectSpace (ℕ → Bool) ∧ ∀ x y : ℕ → Bool, x ≠ y →
      ¬ ∃ γ : C(Set.Icc (0 : ℝ) 1, ℕ → Bool), γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y :=
  ⟨cantorSpace_perfect, fun _ _ hxy => disconnectedness_forbids_path hxy⟩

/-- `Statement:` the 2-adic integers `ℤ_[2]` are perfect and no continuous path joins two distinct
points. -/
theorem padicInt_crowded_and_cut :
    PerfectSpace ℤ_[2] ∧ ∀ x y : ℤ_[2], x ≠ y →
      ¬ ∃ γ : C(Set.Icc (0 : ℝ) 1, ℤ_[2]), γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y :=
  ⟨⟨padicInt_univ_perfect.2⟩, fun _ _ hxy => disconnectedness_forbids_path hxy⟩

/-! ### § III. The order chart: gaps between branches -/

/-- `Statement:` the lexicographic order on `ℕ → Bool` is not densely ordered; the proof's witnesses are
`0111…` and `1000…`. -/
theorem cantorSpace_lex_not_dense : ¬ DenselyOrdered (Lex (ℕ → Bool)) := by
  intro hd
  let a : ℕ → Bool := fun n => decide (n ≠ 0)
  let b : ℕ → Bool := fun n => decide (n = 0)
  have hab : toLex a < toLex b := ⟨0, fun j hj => absurd hj (Nat.not_lt_zero _), by decide⟩
  obtain ⟨c, hac, hcb⟩ := hd.dense _ _ hab
  obtain ⟨i, hi1, hi2⟩ := hac
  obtain ⟨k, hk1, hk2⟩ := hcb
  have k1 : ∀ z : Bool, ¬ true < z := by decide
  have k2 : ∀ z : Bool, ¬ z < false := by decide
  have k3 : ∀ z : Bool, false < z → z < true → False := by decide
  have hi2' : decide (i ≠ 0) < ofLex c i := hi2
  have hk2' : ofLex c k < decide (k = 0) := hk2
  have hi : i = 0 := by
    by_contra h; rw [decide_eq_true h] at hi2'; exact k1 _ hi2'
  have hk : k = 0 := by
    by_contra h; rw [decide_eq_false h] at hk2'; exact k2 _ hk2'
  subst hi hk
  rw [decide_eq_false (fun h : (0:ℕ) ≠ 0 => h rfl)] at hi2'
  rw [decide_eq_true rfl] at hk2'
  exact k3 _ hi2' hk2'

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms perfectSpace_pi_iff
#print axioms cantorSpace_perfect
#print axioms pi_crowded_and_cut
#print axioms cantorSpace_crowded_and_cut
#print axioms padicInt_crowded_and_cut
#print axioms cantorSpace_lex_not_dense
end PurityCheck
