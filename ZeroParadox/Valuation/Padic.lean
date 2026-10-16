import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# ZP-B: p-Adic Topology

## Engineer's Take

The states that we defined in ZPA either exist or they don't. There's no in
between or half existing. This models that logic. In order to model a binary
state two is the minimum number of states required. Anything else will
eventually reduce down to one of the two. The transitive relationship for
closeness doesn't degrade because of the triangle inequality. The balls behave
like a step function. You're in or you're out. There's a hard gap between the
two sides and no way to approach the boundary from either direction. C3 follows
from the totally disconnected structure of Q₂.

---

## Formal Overview (AI-assisted)

Formalizes the Zero Paradox p-adic framework over Q₂ (the 2-adic rationals).
Proves: ultrametric T1, clopen balls T2, clopen gap at 0 T3,
total disconnectedness T5, and irreversibility of the Snap C3.

Self-contained within p-adic analysis and topology; no ZP-A algebra imported.
-/

namespace ZeroParadox

/-! ## Setup -/

instance hp2 : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- Q₂: the 2-adic rationals. All ZP-B results are about this field. -/
notation "Q₂" => (ℚ_[2] : Type)

/-! ## AX-B1 — Binary Existence

The foundational distinction is binary: a state either exists or does not.
Modelled as a free two-constructor inductive type with no natural-number dependency.
AX-B1 is a modelling commitment (the choice of binary structure); distinctness of
the two states is then verified by decidable equality, requiring no classical axioms. -/

/-- The two ontological states: non-existence (⊥ in ZP-A) and existence. -/
-- [ZP-CUSTOM] replaces: Fin 2 | reason: Fin 2's constructors are ⟨0,_⟩ and ⟨1,_⟩ — natural numbers. nullState ≠ ℕ's 0 by convention; it is a semantic state with no numeric meaning. Free inductive eliminates the ℕ dependency and makes ⊥ ↦ null a structural fact, not a labelling choice.
inductive OntologicalStates where
  | null  : OntologicalStates
  | exist : OntologicalStates
  deriving DecidableEq, Fintype

/-- Non-existence: ⊥ of `OntologicalStates` under `instOntZPS` (`Settheory/OntBridge.lean`). -/
def nullState : OntologicalStates := .null

/-- Existence: the state off ⊥ of `OntologicalStates`. -/
def firstAtomicState : OntologicalStates := .exist

/-- AX-B1: the two states are distinct.
    Proved by decidable equality — no classical axioms required. -/
theorem ax_b1_distinct : nullState ≠ firstAtomicState := by decide

/-! ## Theorem T0 — p = 2 is the Unique Minimum Sufficient Base

Given exactly 2 ontological states (derived via ax_b1_distinct) and MP-1 (minimum base
without redundancy), the representational base is uniquely p = 2. -/

/-- Every prime satisfies p ≥ 2; there is no prime below 2.
    A base p < 2 cannot encode two distinct states (fails faithfulness of MP-1). -/
theorem t0_no_prime_below_two (p : ℕ) (hp : Nat.Prime p) : 2 ≤ p := hp.two_le

/-- 2 is prime — the minimum prime encoding the binary distinction of AX-B1. -/
theorem t0_two_is_prime : Nat.Prime 2 := by decide

/-- Any prime p > 2 has p coefficient values; extras beyond the binary distinction violate MP-1. -/
theorem t0_redundancy (p : ℕ) (_hp : Nat.Prime p) (hgt : 2 < p) :
    Fintype.card OntologicalStates < Fintype.card (Fin p) := by
  have hcard : Fintype.card OntologicalStates = 2 := by decide
  simp [hcard, hgt]

/-! ## Why Q₂ Rather Than a Discrete Two-Point Space

T0 fixes the representational base at p = 2. The full Q₂ structure is not uniquely
forced by AX-B1 alone: a discrete two-point space {0, 1} would also satisfy the binary
distinction. The choice of Q₂ is a motivated modelling commitment; its three reasons are
in `ZeroParadox/Valuation/Padic.md`. -/

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

/-! ## Theorem T3 — Clopen Gap at Zero

For any r > 0, the ball B(0,r) is clopen: any element outside it is separated
from 0 by a discrete gap — the topological identity of the Snap. -/

/-- T3: B(0,r) is clopen in Q₂ for nonzero r; 0 is separated from its complement by a clopen gap. -/
theorem t3_isolation (r : ℝ) (hr : r ≠ 0) : IsClopen (Metric.closedBall (0 : Q₂) r) :=
  t2_closedBall_isClopen 0 r hr

/-- D5 support: the real norm threshold `2 ^ k`. This is ZP-B's ε₀ of ℚ₂, never `Ordinal.epsilon 0`.

    ε₀ of ℚ₂ is a role, the minimum viable deviation from ℚ₂'s `0`, and its occupant is a POINT of
    ℚ₂ named only by its rung: any point whose 2-adic valuation is the chosen finest accessible
    valuation `v`. Such a point has norm `eps0 (-v)` (first `example` below), shared by every point
    at that rung, so the rung fixes the norm and not the point (second `example`). ℚ₂ supplies no
    least nonzero norm (the `¬ HasFirstStep` example in `ZeroParadox/BottomCannotBe.lean` § ROLE),
    so the role is filled only relative to the chosen `v`. The requirement list of the ordinal
    chart (`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § I-b) does not transfer to this carrier.
    Inert: nothing in the development depends on this definition. -/
noncomputable def eps0 (k : ℤ) : ℝ := 2 ^ k

-- Statement: every nonzero point `x` of ℚ₂ has norm `eps0 (-v)`, where `v` is its 2-adic valuation.
example (x : Q₂) (hx : x ≠ 0) : ‖x‖ = eps0 (-x.valuation) := by
  rw [Padic.norm_eq_zpow_neg_valuation hx, eps0]; norm_num

-- Statement: at every rung `v`, the distinct points `2 ^ v` and `-(2 ^ v)` of ℚ₂ both have
-- valuation `v` and norm `eps0 (-v)`.
example (v : ℤ) :
    ((2 : Q₂) ^ v).valuation = v ∧ (-((2 : Q₂) ^ v)).valuation = v ∧
    (2 : Q₂) ^ v ≠ -((2 : Q₂) ^ v) ∧
    ‖(2 : Q₂) ^ v‖ = eps0 (-v) ∧ ‖-((2 : Q₂) ^ v)‖ = eps0 (-v) := by
  have hv : ((2 : Q₂) ^ v).valuation = v := by
    have h := Padic.valuation_zpow (p := 2) (2 : Q₂) v
    have h2 : (2 : Q₂).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 2)
    rw [h, h2, mul_one]
  have hn : ‖(2 : Q₂) ^ v‖ = eps0 (-v) := by
    have := Padic.norm_p_zpow (p := 2) v
    simpa [eps0] using this
  have h0 : (2 : Q₂) ^ v ≠ 0 := zpow_ne_zero v two_ne_zero
  have h1 : (-1 : Q₂).valuation = 0 := by
    have := Padic.valuation_intCast (p := 2) (-1)
    push_cast at this
    rw [this]
    simp
  have hneg : (-((2 : Q₂) ^ v)).valuation = v := by
    rw [neg_eq_neg_one_mul, Padic.valuation_mul (by norm_num) h0, hv, h1, zero_add]
  refine ⟨hv, hneg, fun h => h0 ?_, hn, by rw [norm_neg, hn]⟩
  have : (2 : Q₂) * (2 : Q₂) ^ v = 0 := by
    rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel _
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

-- Statement: ZP-B T3's scope: a nonzero point of ℚ₂ lies in the ball `B(0, 2^(-j))` exactly when
-- `j` is at most its valuation.
example (x : Q₂) (hx : x ≠ 0) (j : ℤ) : ‖x‖ ≤ (2 : ℝ) ^ (-j) ↔ j ≤ x.valuation := by
  rw [Padic.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  omega

/-! ## Theorem T5 — Q₂ is Totally Disconnected

The only connected subsets of Q₂ are singletons.
Proof: any set with two distinct points a, b can be separated by the clopen ball B(a,s)
for any 0 < s < d(a,b), giving a clopen partition. -/

/-- T5: Q₂ is a totally disconnected topological space. -/
theorem t5_totallyDisconnected : TotallyDisconnectedSpace Q₂ := inferInstance

/-! ## Corollary C3 — The Snap is Topologically Irreversible
No continuous path γ: [0,1] → Q₂ goes from x ≠ 0 to 0: γ([0,1]) is connected in the totally
disconnected Q₂, hence a singleton. The proof uses no property of 0, and Q₂ is topologically
homogeneous (the `example`s after `c3_irreversible`). So topology does not single out `(0 : Q₂)`
as the occupant of ZP-A's ⊥ role: it is the additive identity (`zero_add`) and the only point of
valuation ⊤ (`padic_addVal_eq_top_iff`, `ZeroParadox/Valuation/ValuationAFA_Padic.lean`). Whether
that makes 0 least or greatest depends on the order named; the `example`s after the C3 ones fix it
for the norm preorder, ascending valuation, and divisibility on ℤ_[2]. `snapEmbed`
(`ZeroParadox/Ordinal/Incompleteness.lean`) sends c₀, ⊥ of MachinePhase's ZP-A semilattice, to 1. -/

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

-- `Statement:` every point `x` of Q₂, not only 0, is the sole point under its own nested balls
-- `B(x, 2⁻ⁿ)`, and those balls are clopen.
example (x : Q₂) : (⋂ n : ℕ, Metric.ball x ((1 / 2 : ℝ) ^ n)) = {x} := by
  ext y
  simp only [Set.mem_iInter, Metric.mem_ball, Set.mem_singleton_iff]
  refine ⟨fun h => ?_, fun hy n => by simp [hy]⟩
  by_contra hne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (dist_pos.mpr hne) (by norm_num : (1 / 2 : ℝ) < 1)
  exact absurd (h n) (not_lt.mpr hn.le)
example (x : Q₂) (r : ℝ) : IsClopen (Metric.ball x r) := IsUltrametricDist.isClopen_ball x r
-- `Statement:` translation is an isometry of Q₂.
example (a x y : Q₂) : dist (x - a) (y - a) = dist x y := dist_sub_right x y a
-- `Statement:` `c3_irreversible` with any two distinct endpoints in place of `x` and `0`.
example (x y : Q₂) (hxy : x ≠ y) :
    ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂), γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y := by
  rintro ⟨γ, hγ0, hγ1⟩
  haveI : PreconnectedSpace (Set.Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  exact hxy (hγ0 ▸ hγ1 ▸ isTotallyDisconnected_of_totallyDisconnectedSpace Set.univ
    (Set.range _) (Set.subset_univ _) (isPreconnected_range γ.continuous)
    (Set.mem_range_self _) (Set.mem_range_self _))

-- `Statement:` 0 is the unique least point of the norm preorder, on ℚ_[2] and on ℤ_[2].
example (x : ℚ_[2]) : ‖(0 : ℚ_[2])‖ ≤ ‖x‖ ∧ (‖x‖ ≤ ‖(0 : ℚ_[2])‖ → x = 0) :=
  ⟨by simp, fun h => by simpa using h⟩
example (x : ℤ_[2]) : ‖(0 : ℤ_[2])‖ ≤ ‖x‖ ∧ (‖x‖ ≤ ‖(0 : ℤ_[2])‖ → x = 0) :=
  ⟨by simp, fun h => by simpa using h⟩
-- `Statement:` 0 is the unique greatest point under valuation read ascending, on ℚ_[2].
example (x : ℚ_[2]) : Padic.addValuation x ≤ Padic.addValuation (0 : ℚ_[2]) ∧
    (Padic.addValuation (0 : ℚ_[2]) ≤ Padic.addValuation x → x = 0) :=
  ⟨by simp, fun h => by simpa using h⟩
-- `Statement:` on ℤ_[2] under divisibility, 1 is least and 0 is greatest; 1 has the greatest norm.
example (x : ℤ_[2]) : (1 : ℤ_[2]) ∣ x ∧ x ∣ 0 ∧ ‖x‖ ≤ ‖(1 : ℤ_[2])‖ :=
  ⟨one_dvd x, dvd_zero x, by simpa using x.norm_le_one⟩

/-! ## Classification Note: Non-Archimedean Fields and the Snap

The ultrametric property (T1) is the metric expression of non-Archimedean structure.
C3 (irreversibility) is the positive complement to ZP-F's f_snap_impossible:

- In **any ordered field** (ZP-F), Archimedean or not: halving is always available, so no
  minimal positive element exists — the snap is **impossible** (`f_snap_impossible`,
  `axb1_fails_in_ordered_field`). Neither theorem has an Archimedean hypothesis; see the
  ZP-B / ZP-F classification paragraph further down this docstring.
- In Q₂ (this file): the ultrametric creates a genuine topological gap at zero
  (T2, T3, C3) — the snap is **not blocked**, which is a strictly weaker statement.

**⚠ CORRECTED 2026-07-31. This line read "the snap is forced" and that is FALSE**, as
`ZeroParadox/Reals/OrderedField.lean` (§ "Classification Note", the "ZP-B does NOT force the snap"
paragraph) states directly: *"ZP-B does NOT force the snap,
and cannot."* What this file proves is topological — the gap at 0 is clopen (`t3_isolation`)
and the return across it admits no continuous path (`c3_irreversible`). **Neither yields a
first step, and no metric result could:** the 2-adic norm values accumulate at 0
(‖2ⁿ‖₂ = 2⁻ⁿ), so ℚ₂ has no closest non-zero element either. **The first step is AX-B1**, a
modelling commitment, not a consequence of the 2-adic structure. Two files gave opposite
answers here for months; `OrderedField.lean` is the one that reasoned it through.

**ZP-B / ZP-F Classification (Ostrowski's theorem):**

Ostrowski's theorem is about **absolute values on ℚ, classified up to equivalence**: every
**nontrivial** absolute value on ℚ is equivalent to either a p-adic absolute value or to the standard
Archimedean (Euclidean) one (`Mathlib/NumberTheory/Ostrowski.lean`,
`Rat.AbsoluteValue.equiv_real_or_padic`). The framework's own instance is
`ZeroParadox/Valuation/Ostrowski.lean`'s `completions_exhaustive` — cite that rather than restating
the theorem.

*(Nontriviality is load-bearing and is stated here deliberately. Mathlib's module **docstring** elides
it, but the declaration takes `hf_nontriv : f.IsNontrivial` and `completions_exhaustive` carries it as
`(hf : f.IsNontrivial)`. Quoting the docstring verbatim would reproduce the elision. Corrected 2026-08-01.)*

*(Corrected 2026-08-01. This paragraph previously read: "every complete valued field extending ℚ is
either Archimedean (isomorphic to ℝ) or non-Archimedean (isomorphic to ℚ_p for some prime p)." That is
a **different theorem** — about complete fields rather than about ℚ — and it is **false in both
halves** as written: the complete Archimedean case gives **ℝ or ℂ**, not ℝ alone, and a complete
non-Archimedean field extending ℚ need not be any ℚ_p. The correct statement was already in the corpus
at `ZeroParadox/Valuation/Ostrowski.lean` the whole time.)*

ZP-B covers the non-Archimedean case (p = 2, forced by AX-B1 and minimality).
ZP-F covers the ordered-field case. **The classification is a statement about where the snap is
RULED OUT**, not where it is supplied: **ZP-F rules it out in every ordered field** — which is
what it actually proves, and is wider than the Archimedean completion — and ZP-B removes the
topological obstruction in ℚ₂. Ultrametric structure is therefore **not sufficient** — that the snap
actually occurs is carried by AX-B1 together
with the framework's commitments, never by C3 or T5 alone. **Necessity is NOT asserted here**: the
contraposition below gives *a first step exists ⟹ not an ordered field*, which is incomparable with
*⟹ ultrametric* **over valued fields, reading "ultrametric" as the distinguished absolute value —
the pin stated in full below, and load-bearing: under a bare-field existential reading the comparison
collapses, since every field carries the trivial ultrametric**. Necessity would hold only after restricting to completions of ℚ, where Ostrowski
leaves nothing else — a restriction this paragraph does not make. *(Corrected 2026-08-02: this read
"necessary and not sufficient". The word "necessary" asserted `snap ⟹ ultrametric`, the exact
implication called incomparable thirteen lines below in this same docstring. It survived because the
fix that introduced it changed the ADJECTIVE — "non-Archimedean" → "ultrametric" — and left the claim
wrapped around it standing.)* (An earlier revision of this
paragraph asserted the biconditional "possible if and only if non-Archimedean". The direction that
fails is **non-Archimedean ⟹ a first step exists**: ℚ₂ removes the density obstruction but supplies
no closest nonzero element, so it does not yield the step.)

**What the converse actually is — and it is not about Archimedean-ness.** `f_snap_impossible`
(`ZeroParadox/Reals/OrderedField.lean` — a declaration name is self-locating, so **no line number**;
this citation carried one until 2026-08-02, when an insertion in that file moved the theorem and left
the number pointing into an unrelated proof body. **No replacement figure is given here on purpose —
a line number in a docstring is invalidated by any edit to the file it names, including edits to the
docstring itself.**) is stated over an
**arbitrary ordered field**
(`[Field F] [LinearOrder F] [IsStrictOrderedRing F]`) and carries **no Archimedean hypothesis**. It is
proved by **halving**, via `f_snap_blocked`. So what it gives by contraposition is *a first step exists
⟹ the carrier is not an ordered field at all*.

That is a **different** shape from "⟹ non-Archimedean". **Quantified over VALUED FIELDS — a field
together with a distinguished absolute value — and reading "non-Archimedean" as *that distinguished
absolute value is ultrametric*, the two are incomparable**, neither implying the other:
* ℝ(t) with the t-adic absolute value and the leading-coefficient order is a non-Archimedean **ordered**
  field, so `f_snap_impossible` covers it: non-Archimedean without being "not an ordered field";
* ℂ with its standard absolute value **is not orderable at all** (no compatible linear order) while that
  absolute value is **Archimedean**: "not an ordered field" without being non-Archimedean.

**⚠ THE DOMAIN MUST BE VALUED FIELDS, AND THE READING MUST BE THE DISTINGUISHED ABSOLUTE VALUE.
Corrected 2026-08-02 — the previous version pinned the one combination that makes the verdict FALSE.**
It quantified over *bare fields* and read "non-Archimedean" existentially ("the field carries an
ultrametric absolute value"). But **every field carries the trivial absolute value, and the trivial
absolute value is an ultrametric** — so under that reading the predicate holds of every field, "not an
ordered field ⟹ non-Archimedean" is trivially true, and the two are **not** incomparable at all. The
previous version even stated the refuting fact, in the ℂ bullet, and did not carry it back to the pin;
its ℂ argument silently switched from the existential predicate to a claim about the *standard*
absolute value, which is a predicate on a valued field, not on a bare field. Under the corrected pin
both witnesses are genuine and the ℤ example is unnecessary: ℤ is not a field, so the domain excludes
it without further argument. **This paragraph has now been corrected four times; the failure each time
was a wrong reason under a defensible conclusion.**

*(Superseded block removed 2026-08-02: a "BOTH the domain and the reading are load-bearing" passage
sat here restating the domain as bare **fields** and using **ℤ** as a witness. It contradicted the
correction immediately above and was itself the third revision of the same sentence — a separator is
exactly what refutes strictness, so "strictly stronger, witnessed by ℤ" could never have held. Deleted
rather than annotated.)*

*(Three corrections, all 2026-08-01, all caught by gates rather than by me. (i) This paragraph once
cited `f_snap_impossible` as holding "on the Archimedean side", mis-scoping a theorem that covers every
ordered field. (ii) The fix for (i) then attributed the wrong proof route — "density
(`LinearOrderedSemiField.toDenselyOrdered`, then `not_covBy`)" — which is the route of
`axb1_fails_in_ordered_field` four lines further down, whose own docstring says it is proved through
Mathlib **rather than** through `f_snap_impossible`. A wrong reason under a true conclusion breaks
nothing downstream, which is exactly why it needed a gate to find. (iii) The same fix then called the
converse a "stronger shape", re-committing the ordering error this very push corrects in
`ZeroParadox/Algebra/Wheel.lean`.)*

The ultrametric is not a technical convenience — it is the structural fact that
the Archimedean property would erase. C3's irreversibility is Ostrowski's
non-Archimedean case made topologically explicit.

See `ZeroParadox/Reals/OrderedField.lean` (`f_snap_impossible`) for the ordered-field side. -/

end ZeroParadox

/-! ## Axiom Purity Check

Measured 2026-10-08 (the output below is authoritative): `ax_b1_distinct` depends on no Lean
axioms; the T0 results do not share one footprint — `t0_no_prime_below_two` reaches only `propext`,
while `t0_two_is_prime` and `t0_redundancy` reach `[propext, Classical.choice, Quot.sound]`.
T1–C3 depend on Mathlib's p-adic and topology instances — any classical axioms used
by those instances will appear here and are inherited from standard Mathlib, not ZP-B. -/

section PurityCheck
open ZeroParadox

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
