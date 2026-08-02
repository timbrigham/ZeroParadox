import Mathlib.NumberTheory.Padics.PadicNumbers
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

/-- The Null State: non-existence, ⊥ in ZP-A. -/
def nullState : OntologicalStates := .null

/-- The First Atomic State: existence. -/
def firstAtomicState : OntologicalStates := .exist

/-- AX-B1: null and first atomic states are distinct.
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

/-! ## Theorem T3 — Clopen Gap at Zero

For any r > 0, the ball B(0,r) is clopen: any element outside it is separated
from 0 by a discrete gap — the topological identity of the Snap. -/

/-- T3: B(0,r) is clopen in Q₂ for nonzero r; 0 is separated from its complement by a clopen gap. -/
theorem t3_isolation (r : ℝ) (hr : r ≠ 0) : IsClopen (Metric.closedBall (0 : Q₂) r) :=
  t2_closedBall_isClopen 0 r hr

/-- D5: The Minimum Viable Deviation, written `2 ^ k` for an integer EXPONENT `k`.

    **Corrected 2026-07-28.** The previous docstring said "`k` is the maximum 2-adic valuation
    accessible", which contradicts this file's own ball convention `B(0, 2⁻ⁿ)`: a *maximum*
    valuation gives a *minimum* scale, so the exponent is `k = -v` where `v` is that valuation.
    `k` is the exponent, `v` is the valuation, and they differ by sign. No semantic change —
    the definition is unaltered, and `k : ℤ` was always free to be negative.

    Structural role universal; value contingent — contingent on the **chosen exponent `k`**, i.e.
    on which valuation is taken to be the finest accessible one. That is a normalisation choice,
    **not** a physical measurement and **not** a dimension: ε₀ is a *position* (the first step
    above the bottom, `Ordinal.epsilon 0`, Veblen (1,0)) and a position carries no units, exactly
    as ⊥ carries none. (Corrected 2026-07-29: an earlier revision said "it is dimensionful, so it
    depends on a choice of units", which imported a magnitude reading of ε₀ and contradicted the
    same box's own no-physical-claims disclaimer.)

    **Note this definition is inert**: nothing in the development depends on it. It records the
    framework's parameterization of the snap threshold, not a load-bearing construction. -/
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
disconnected Q₂, hence a singleton; so γ(0) = γ(1), contradicting x ≠ 0.

Note on the role of `(0 : Q₂)`: unlike the `OntologicalStates` refactor (where
`Fin 2` was replaced by a free inductive because ⊥ = ℕ's 0 was a purely
conventional label), the use of `0 : Q₂` here is structurally motivated and
deliberately retained. Q₂'s additive identity is the **unique limit point** of
the nested clopen ball hierarchy B(0, 2⁻ⁿ) ↘ {0}: no other point in Q₂ sits at
the base of an infinite convergent nesting of clopen sets. This is what gives C3
its content — the irreversibility is a theorem of Q₂'s ultrametric geometry, not
a labelling convention. The identification ⊥ ↦ (0 : Q₂) is warranted by that
metric structure (T2, T5), not by 0 being the first natural number. -/

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
`(hf : f.IsNontrivial)`. Quoting the docstring verbatim would reproduce the elision — corrected
2026-08-01 after a gate caught it.)*

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
*⟹ ultrametric*. Necessity would hold only after restricting to completions of ℚ, where Ostrowski
leaves nothing else — a restriction this paragraph does not make. *(Corrected 2026-08-02: this read
"necessary and not sufficient". The word "necessary" asserted `snap ⟹ ultrametric`, the exact
implication called incomparable thirteen lines below in this same docstring. It survived because the
fix that introduced it changed the ADJECTIVE — "non-Archimedean" → "ultrametric" — and left the claim
wrapped around it standing. All three gates flagged it.)* (An earlier revision of this
paragraph asserted the biconditional "possible if and only if non-Archimedean". The direction that
fails is **non-Archimedean ⟹ a first step exists**: ℚ₂ removes the density obstruction but supplies
no closest nonzero element, so it does not yield the step.)

**What the converse actually is — and it is not about Archimedean-ness.** `f_snap_impossible`
(`ZeroParadox/Reals/OrderedField.lean:137`) is stated over an **arbitrary ordered field**
(`[Field F] [LinearOrder F] [IsStrictOrderedRing F]`) and carries **no Archimedean hypothesis**. It is
proved by **halving**, via `f_snap_blocked`. So what it gives by contraposition is *a first step exists
⟹ the carrier is not an ordered field at all*.

That is a **different** shape from "⟹ non-Archimedean". **Quantified over FIELDS, and reading
"non-Archimedean" in the valuation-theoretic sense — the field carries an ultrametric absolute value,
the sense used throughout ZP-B — the two are incomparable**, neither implying the other:
* ℝ(t) with the leading-coefficient order is a **non-Archimedean ordered field**, so
  `f_snap_impossible` covers it while an Archimedean hypothesis would not;
* ℂ **is not orderable at all** (it has no compatible linear order), so it falls under "not an ordered
  field"; and its **standard** absolute value is Archimedean, so it is not non-Archimedean in the sense
  meant. *(Stated of the standard absolute value deliberately: every field also carries the trivial
  absolute value, which is an ultrametric, and ℂ ≅ ℂ_p as abstract fields — so "ℂ is not
  non-Archimedean" is false without naming the absolute value. Corrected 2026-08-02.)*

**BOTH the domain and the reading are load-bearing, and both are pinned deliberately.**
* **Domain — fields.** Over arbitrary carriers the comparison is not even well-posed in the intended
  direction: **ℤ is not an ordered field and IS Archimedean**, so "not an ordered field" cannot imply
  "non-Archimedean" there.
* **Reading.** Under the *plain* reading of "non-Archimedean" as bare `¬Archimedean`, ℂ separates
  nothing and the witness would have to be ℤ — which the field restriction excludes.

*(Corrected 2026-08-02. The previous version said that under the plain reading "not an ordered field"
is strictly **stronger**, while naming **ℤ** as its separating witness — two claims that cannot both
hold, since a separator is exactly what refutes strictness. It also never stated the domain, in the
sentence instructing readers to state the reading. Originates in a prior-art suggestion that was itself
imprecise and which was implemented faithfully; editorial and adversary both caught it a round later.)*

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

Expected result: T0 results depend only on decidability (no kernel axioms beyond propext).
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
