import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# ZP-B: p-Adic Topology

Formalizes the Zero Paradox p-adic framework over Q₂ (the 2-adic rationals).
Proves: ultrametric T1, clopen balls T2, topological isolation T3,
total disconnectedness T5, and irreversibility of the Snap C3.

Self-contained within p-adic analysis and topology; no ZP-A algebra imported.
-/

namespace ZeroParadox.ZPB

/-! ## Setup -/

instance hp2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Q₂: the 2-adic rationals. All ZP-B results are about this field. -/
notation "Q₂" => (ℚ_[2] : Type)

/-! ## AX-B1 — Binary Existence

The foundational distinction is binary: a state either exists (1) or does not (0).
Modelled as Fin 2. Status: DERIVED — follows from decidable equality on Fin 2,
which requires no classical axioms beyond propext. Not a novel commitment of this framework. -/

abbrev OntologicalStates := Fin 2

/-- 0 ∈ OntologicalStates: non-existence (the Null State, ⊥ in ZP-A). -/
def nullState : OntologicalStates := 0

/-- 1 ∈ OntologicalStates: existence (the First Atomic State). -/
def firstAtomicState : OntologicalStates := 1

/-- AX-B1: null and first atomic states are distinct. Proved by decidable equality on Fin 2 —
    no classical axioms required. -/
theorem ax_b1_distinct : nullState ≠ firstAtomicState := by decide

/-! ## Theorem T0 — p = 2 is the Unique Minimum Sufficient Base

Given exactly 2 ontological states (derived via ax_b1_distinct) and MP-1 (minimum base
without redundancy), the representational base is uniquely p = 2. -/

/-- Every prime satisfies p ≥ 2; there is no prime below 2.
    A base p < 2 cannot encode two distinct states (fails faithfulness of MP-1). -/
theorem t0_no_prime_below_two (p : ℕ) (hp : Nat.Prime p) : 2 ≤ p := hp.two_le

/-- 2 is prime — the minimum prime encoding the binary distinction of AX-B1. -/
theorem t0_two_is_prime : Nat.Prime 2 := by decide

/-- Any prime p > 2 has p coefficient values; the extras beyond {0,1} violate MP-1. -/
theorem t0_redundancy (p : ℕ) (_hp : Nat.Prime p) (hgt : 2 < p) :
    Fintype.card (Fin 2) < Fintype.card (Fin p) := by
  simp [hgt]

/-! ## Why Q₂ Rather Than a Discrete Two-Point Space

T0 fixes the representational base at p = 2. The full Q₂ structure (p-adic field,
ultrametric, clopen ball hierarchy) is not uniquely forced by AX-B1 alone — a
discrete two-point space {0, 1} would also satisfy the binary distinction. Q₂ is
chosen for three motivated reasons beyond the binary count:

- **Hierarchical approximation**: Q₂ contains nested clopen balls B(0, 2⁻ⁿ) ↘ {0}
  — a countably infinite depth hierarchy converging to the null state 0. A two-point
  discrete space has no such hierarchy. This is the geometric substrate for ZPC's
  surprisal field (depth n ↦ n bits) and for L-INF (informational extremity of ⊥).
- **Ultrametric geometry**: The strong triangle inequality (T1) and clopen ball
  structure (T2) give non-trivial topology — disjoint balls cannot be continuously
  connected (C2). Discrete spaces make this claim vacuous (no non-constant paths exist).
- **Irreversibility content**: C3 (no continuous path from x ≠ 0 to 0) uses the
  genuine total disconnectedness of Q₂ via the ultrametric; in a finite discrete
  space the argument carries no structural weight.

The formal connection from Q₂'s topology to ZPC's surprisal field and ZPD's basis
assignment is a design identification — those layers do not import ZPB as a Lean
dependency. The choice of Q₂ is a motivated modelling commitment, not a uniquely
forced consequence of AX-B1. -/

/-! ## II. The 2-Adic Field

D1 (2-adic absolute value) and D2 (2-adic metric) are standard Mathlib definitions.
`padicNormE` is the norm on Q₂; `dist x y = ‖x - y‖` is the induced metric. -/

/-! ## Theorem T1 — Strong Triangle Inequality (Ultrametric) -/

/-- T1: The 2-adic metric satisfies the strong triangle inequality:
    d(x,z) ≤ max(d(x,y), d(y,z)) for all x, y, z ∈ Q₂. -/
theorem t1_ultrametric (x y z : Q₂) :
    dist x z ≤ max (dist x y) (dist y z) :=
  dist_triangle_max x y z

/-! ## Corollary C1 — All Triangles are Isosceles

If d(x,y) ≠ d(y,z) then d(x,z) = max(d(x,y), d(y,z)):
the two largest sides are always equal in an ultrametric triangle. -/

theorem c1_isosceles (x y z : Q₂) (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [max_eq_right hlt.le]
    apply le_antisymm ((t1_ultrametric x y z).trans (max_eq_right hlt.le).le)
    by_contra hlt2
    push Not at hlt2
    have h1 : dist y z ≤ max (dist y x) (dist x z) := dist_triangle_max y x z
    rw [dist_comm y x] at h1
    linarith [max_lt hlt hlt2]
  · rw [max_eq_left hgt.le]
    apply le_antisymm ((t1_ultrametric x y z).trans (max_eq_left hgt.le).le)
    by_contra hlt2
    push Not at hlt2
    have h1 : dist x y ≤ max (dist x z) (dist z y) := dist_triangle_max x z y
    rw [dist_comm z y] at h1
    linarith [max_lt hlt2 hgt]

/-! ## Theorem T2 — Every Ball is Clopen -/

/-- T2a: Every closed ball of nonzero radius in Q₂ is also open.
    (Singleton balls r = 0 are not open; for r < 0 the ball is empty and trivially open.)
    Proof: uses the ultrametric structure. -/
theorem t2_closedBall_isOpen (a : Q₂) (r : ℝ) (hr : r ≠ 0) :
    IsOpen (Metric.closedBall a r) :=
  IsUltrametricDist.isOpen_closedBall a hr

/-- T2b: Every open ball in Q₂ is also closed. -/
theorem t2_ball_isClosed (a : Q₂) (r : ℝ) :
    IsClosed (Metric.ball a r) :=
  IsUltrametricDist.isClosed_ball a r

/-- T2: Every closed ball of nonzero radius in Q₂ is clopen. -/
theorem t2_closedBall_isClopen (a : Q₂) (r : ℝ) (hr : r ≠ 0) :
    IsClopen (Metric.closedBall a r) :=
  ⟨Metric.isClosed_closedBall, t2_closedBall_isOpen a r hr⟩

/-! ## Corollary C2 — Disjoint Balls Do Not Communicate

Disjoint closed balls in Q₂ cannot be joined by a continuous path.
Proof: B(a,r) is clopen (T2); a continuous path from a connected space
into a totally disconnected space must be constant. -/

theorem c2_disjoint_no_path (a b : Q₂) (r : ℝ)
    (hdisj : Disjoint (Metric.closedBall a r) (Metric.closedBall b r))
    (γ : C(Set.Icc (0 : ℝ) 1, Q₂))
    (hγa : γ ⟨0, by norm_num⟩ ∈ Metric.closedBall a r)
    (hγb : γ ⟨1, by norm_num⟩ ∈ Metric.closedBall b r) : False := by
  -- continuous path in totally disconnected Q₂ must be constant
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hsingl : (Set.range (γ : Set.Icc (0 : ℝ) 1 → Q₂)).Subsingleton :=
    isTotallyDisconnected_of_totallyDisconnectedSpace Set.univ
      (Set.range _) (Set.subset_univ _) (isPreconnected_range γ.continuous)
  have heq : γ ⟨0, by norm_num⟩ = γ ⟨1, by norm_num⟩ :=
    hsingl (Set.mem_range_self _) (Set.mem_range_self _)
  have hmem_b : γ ⟨0, by norm_num⟩ ∈ Metric.closedBall b r := by rw [heq]; exact hγb
  exact Set.disjoint_left.mp hdisj hγa hmem_b

/-! ## Theorem T3 — Topological Isolation of Zero

For any r > 0, the ball B(0,r) is clopen: any element outside it is separated
from 0 by a discrete gap — the topological identity of the Snap. -/

/-- T3: B(0,r) is clopen in Q₂ for nonzero r; 0 is isolated from its complement by a gap. -/
theorem t3_isolation (r : ℝ) (hr : r ≠ 0) : IsClopen (Metric.closedBall (0 : Q₂) r) :=
  t2_closedBall_isClopen 0 r hr

/-- D5: The Minimum Viable Deviation ε₀ = 2^k where k is the maximum 2-adic valuation
    accessible in the instantiation. Structural role is universal; value is contingent. -/
noncomputable def eps0 (k : ℤ) : ℝ := 2 ^ k

/-! ## Theorem T5 — Q₂ is Totally Disconnected

The only connected subsets of Q₂ are singletons.
Proof: any set with two distinct points a, b can be separated by the clopen ball B(a,s)
for any 0 < s < d(a,b), giving a clopen partition. -/

/-- T5: Q₂ is a totally disconnected topological space. -/
theorem t5_totallyDisconnected : TotallyDisconnectedSpace Q₂ := inferInstance

/-! ## Corollary C3 — The Snap is Topologically Irreversible

No continuous path γ: [0,1] → Q₂ can go from any x ≠ 0 back to 0.
Proof: γ([0,1]) is a continuous image of the connected set [0,1] in the totally
disconnected Q₂, hence a singleton; so γ(0) = γ(1), contradicting x ≠ 0. -/

/-- C3: There is no continuous path from x ≠ 0 to 0 in Q₂. -/
theorem c3_irreversible (x : Q₂) (hx : x ≠ 0) :
    ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0 := by
  intro ⟨γ, hγ0, hγ1⟩
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hsingl : (Set.range (γ : Set.Icc (0 : ℝ) 1 → Q₂)).Subsingleton :=
    isTotallyDisconnected_of_totallyDisconnectedSpace Set.univ
      (Set.range _) (Set.subset_univ _) (isPreconnected_range γ.continuous)
  have heq : γ ⟨0, by norm_num⟩ = γ ⟨1, by norm_num⟩ :=
    hsingl (Set.mem_range_self _) (Set.mem_range_self _)
  rw [hγ0, hγ1] at heq
  exact hx heq

end ZeroParadox.ZPB

/-! ## Axiom Purity Check

Expected result: T0 results depend only on decidability (no kernel axioms beyond propext).
T1–C3 depend on Mathlib's p-adic and topology instances — any classical axioms used
by those instances will appear here and are inherited from standard Mathlib, not ZP-B. -/

section PurityCheck
open ZeroParadox.ZPB

#print axioms t0_two_is_prime
#print axioms t0_no_prime_below_two
#print axioms t0_redundancy
#print axioms ax_b1_distinct
#print axioms t1_ultrametric
#print axioms c1_isosceles
#print axioms t2_closedBall_isClopen
#print axioms c2_disjoint_no_path
#print axioms t3_isolation
#print axioms t5_totallyDisconnected
#print axioms c3_irreversible

end PurityCheck
