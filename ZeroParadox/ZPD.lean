import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-!
# ZP-D: State Layer (Hilbert Space)

Formalizes the Zero Paradox Hilbert space state layer H = ℂⁿ and the
transition operator T: Q₂ → H. Q₂'s clopen-ball partition is abstracted
as `Fin n`, keeping this file self-contained within functional analysis
(no p-adic imports). ZP-A and ZP-B are imported conceptually, not as
Lean dependencies.

Proves: T2 (existence of T by basis assignment, all five D2 requirements),
T4 (Snap → orthogonal shift in H), T5 (monotone sequences → non-decreasing
norms). T3 (uniqueness up to unitary equivalence) is stated; proof deferred
pending OrthonormalBasis API. DP-1 (orthogonality) is proved as a theorem
of the construction — reflecting the design commitment, not a bare axiom.
-/

namespace ZeroParadox.ZPD

/-! ## I. The State-Layer Hilbert Space (D1) -/

/-- D1: The state-layer Hilbert space H = ℂⁿ.
    n is the cardinality of the clopen ball partition of Q₂ at the chosen level. -/
abbrev StateSpace (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The i-th standard basis vector eᵢ ∈ StateSpace n. -/
noncomputable def basisVec (n : ℕ) (i : Fin n) : StateSpace n :=
  EuclideanSpace.single i 1

/-! ## II. Design Principle DP-1 — Orthogonality

Topological isolation in Q₂ (disjoint clopen balls, from ZP-B T3/T5) is
represented in H by orthogonality. DP-1 is a design commitment: the basis
assignment construction is chosen precisely because it realises this property.
The orthogonality is then a provable theorem of that construction. -/

/-- DP-1 (as theorem): distinct basis vectors are orthogonal in StateSpace n.
    This reflects the design principle that topological isolation in Q₂
    maps to orthogonal separation in H. -/
theorem dp1_orthogonality (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    @inner ℂ (StateSpace n) _ (basisVec n i) (basisVec n j) = 0 := by
  simp only [basisVec, EuclideanSpace.inner_single_left, map_one, one_mul]
  simp [h.symm]

/-! ## III. The Transition Operator T: Fin n → StateSpace n (D2 + T2) -/

/-- D2 (construction): T assigns each ball-index to its corresponding basis vector.
    Fin n abstracts Q₂'s clopen ball partition at a given level k (2^k balls). -/
noncomputable def transitionOp (n : ℕ) : Fin n → StateSpace n :=
  basisVec n

/-! ### T2 — Existence of T: All Five D2 Requirements -/

/-- T2(i): T maps the null index (representing 0 ∈ Q₂) to e₀. -/
theorem t2_maps_null (n : ℕ) [NeZero n] :
    transitionOp n ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ =
    basisVec n ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ :=
  rfl

/-- T2(ii): T maps index 1 (representing ε₀ ∈ Q₂) to e₁. -/
theorem t2_maps_eps0 (n : ℕ) (hn : 2 ≤ n) :
    transitionOp n ⟨1, by omega⟩ = basisVec n ⟨1, by omega⟩ :=
  rfl

/-- T2(iii): T is injective — distinct ball-indices map to distinct vectors.
    Proved by contradiction via DP-1: if T(i) = T(j) then ⟨T(i),T(j)⟩ = 1 yet
    also = 0 (DP-1 when i ≠ j), contradicting norm = 1. -/
theorem t2_injective (n : ℕ) : Function.Injective (transitionOp n) := by
  intro i j heq
  by_contra hij
  have horth : @inner ℂ (StateSpace n) _ (transitionOp n i) (transitionOp n j) = 0 :=
    dp1_orthogonality n i j hij
  rw [heq] at horth
  have hzero : transitionOp n j = 0 := inner_self_eq_zero.mp horth
  have hnorm : ‖transitionOp n j‖ = 1 := by simp [transitionOp, basisVec]
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- T2(iv): T maps disjoint ball-indices to orthogonal vectors (DP-1). -/
theorem t2_orthogonal (n : ℕ) (i j : Fin n) (h : i ≠ j) :
    @inner ℂ (StateSpace n) _ (transitionOp n i) (transitionOp n j) = 0 :=
  dp1_orthogonality n i j h

/-- T2(v): All basis vectors have norm 1 ≥ 1 = ‖e₀‖ — T is norm-preserving. -/
theorem t2_norm_eq_one (n : ℕ) (i : Fin n) : ‖transitionOp n i‖ = 1 := by
  simp [transitionOp, basisVec]

/-- T2: Existence — transitionOp satisfies all five D2 requirements.
    (i/ii) by construction (rfl); (iii) injective; (iv) orthogonal across indices;
    (v) norm-preserving (all basis vectors have norm 1). -/
theorem t2_existence (n : ℕ) :
    Function.Injective (transitionOp n) ∧
    (∀ i j : Fin n, i ≠ j →
        @inner ℂ (StateSpace n) _ (transitionOp n i) (transitionOp n j) = 0) ∧
    (∀ i : Fin n, ‖transitionOp n i‖ = 1) :=
  ⟨t2_injective n, fun i j h => t2_orthogonal n i j h, fun i => t2_norm_eq_one n i⟩

/-! ## IV. T3 — Uniqueness of T up to Unitary Equivalence -/

/-- T3: Any other function T': Fin n → StateSpace n satisfying D2 (orthonormal values)
    is related to transitionOp by a linear isometry equivalence (unitary map) U.
    Proof: both T and T' are orthonormal families of size n in ℂⁿ, so each spans ℂⁿ and
    forms an OrthonormalBasis. The symm of T's repr isometry sends transitionOp i = e_i
    to b_T' i = T' i, giving the required unitary. -/
theorem t3_uniqueness (n : ℕ)
    (T' : Fin n → StateSpace n)
    (hT'_orth : ∀ i j : Fin n, i ≠ j →
        @inner ℂ (StateSpace n) _ (T' i) (T' j) = 0)
    (hT'_norm : ∀ i : Fin n, ‖T' i‖ = 1) :
    ∃ U : StateSpace n ≃ₗᵢ[ℂ] StateSpace n,
      ∀ i, U (transitionOp n i) = T' i := by
  have hOrth_T' : Orthonormal ℂ T' :=
    ⟨hT'_norm, fun i j hij => hT'_orth i j hij⟩
  have hSpan : ⊤ ≤ Submodule.span ℂ (Set.range T') :=
    (hOrth_T'.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by simp [StateSpace])).ge
  refine ⟨(OrthonormalBasis.mk hOrth_T' hSpan).repr.symm, fun i => ?_⟩
  rw [show transitionOp n i = EuclideanSpace.single i (1 : ℂ) from rfl,
      (OrthonormalBasis.mk hOrth_T' hSpan).repr_symm_single]
  exact congr_fun (OrthonormalBasis.coe_mk hOrth_T' hSpan) i

/-! ## V. T4 — The Binary Snap Produces an Orthogonal Shift in H -/

/-- T4: The Binary Snap 0 → ε₀ in Q₂ maps to an orthogonal shift in H.
    T(0) = e₀ and T(ε₀) = e₁ satisfy ⟨e₀, e₁⟩_ℂ = 0.
    Derived from D2(i), D2(ii), and DP-1 (disjoint ball-indices → orthogonality). -/
theorem t4_snap_orthogonal (n : ℕ) (hn : 2 ≤ n) :
    @inner ℂ (StateSpace n) _
      (transitionOp n ⟨0, by omega⟩)
      (transitionOp n ⟨1, by omega⟩) = 0 := by
  apply t2_orthogonal
  intro h
  exact absurd (congr_arg Fin.val h) (by norm_num)

/-! ## VI. T5 — Monotone State Sequences Map to Non-Decreasing Norms -/

/-- T5: For any sequence S: ℕ → Fin n, ‖T(S(k))‖ ≤ ‖T(S(k+1))‖ for all k.
    In the basis-assignment construction all T(i) have norm 1, so the norm
    sequence is constant — trivially non-decreasing. This formalises the
    ZP-A T3 (monotone state sequences) property in H under basis assignment. -/
theorem t5_monotone_norms (n : ℕ) (S : ℕ → Fin n) (k : ℕ) :
    ‖transitionOp n (S k)‖ ≤ ‖transitionOp n (S (k + 1))‖ := by
  simp [t2_norm_eq_one]

end ZeroParadox.ZPD

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPD

#print axioms dp1_orthogonality
#print axioms t2_injective
#print axioms t2_orthogonal
#print axioms t2_norm_eq_one
#print axioms t2_existence
#print axioms t4_snap_orthogonal
#print axioms t5_monotone_norms

end PurityCheck
