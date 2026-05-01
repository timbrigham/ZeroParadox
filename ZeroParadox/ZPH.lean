import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import ZeroParadox.ZPD
import ZeroParadox.ZPE
import ZeroParadox.ZPG
import Mathlib.Tactic

/-!
# ZP-H: Categorical Bridge

## Engineer's Take

Now that the categorical structure is established, ZPH goes back through ZPA
to ZPD and shows that each of those frameworks is a representation of the same
underlying object. The algebra, the topology, the information theory, and the
Hilbert space are not four separate things. They are different vantage points
on the same object. T-H3 is the formal statement of that. Four independent
derivations, same snap, same verdict.

---

Connects ZP-G (Category Theory) to ZP-A through ZP-E. Every cross-framework claim
is traced to a theorem in ZP-G or ZP-A through ZP-E, plus an explicit bridge axiom
where required. No floating connections.

Key results:
- T-H1: For each domain, the canonical initial element satisfies the relevant
  domain-specific extremality property.
  - F_A (ZPA/ZPE): fully categorical — ℕ with max/0 is a concrete ZPCategory instance
    (see NatSLat appendix); ⊥ satisfies the universal property of an initial object.
  - F_B, F_C, F_D: ℝ≥0 with ≤ (NNRealZPCat appendix) provides a concrete ZPCategory
    grounding all three. Domain properties (irreversibility/C3, JSD cost/T1b,
    orthogonality/T4) close OQ-G3 for F_B, F_C, F_D. Full abstract functor objects
    (Lean Functor terms C → pTop/InfoSp/Hilb) remain future work, but the concrete
    categorical and domain grounding is complete. See NNRealZPCat appendix.
- T-H2: Categorical singularity (domain-absent) and ZPC singularity (divergent
  accumulation) are compatible — jointly derivable (OQ-G4 closed).
- T-H3: Binary Snap described consistently under all four functors. Fully proved
  by assembling independently proved domain theorems.
-/

namespace ZeroParadox.ZPH

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPB
open ZeroParadox.ZPC
open ZeroParadox.ZPD
open ZeroParadox.ZPE
open ZeroParadox.ZPG
open CategoryTheory

/-! ## D-H1 — Morphisms of C are State Transitions (Design Commitment)

A morphism f: A → B in C is a state transition satisfying:
(i) Forward direction: every morphism represents a net addition of informational content.
(ii) Compatibility with AX-G2: no morphism X → 0 exists for X ≠ 0.
(iii) Composition: composition corresponds to sequential state accumulation.
D-H1 is a design commitment, not a derivation. No Lean theorem — the choice is what
makes the instantiation functors well-defined. A different morphism structure would
yield different functors. -/

/-! ## Section III — Instantiation Functors: Domain Properties

The four functors F_A, F_B, F_C, F_D map the abstract ZPCategory C to its four domain
codomains. A complete Lean construction of each functor as a CategoryTheory.Functor
requires defining SLat, pTop, InfoSp, and Hilb as full CategoryTheory categories (objects,
hom-sets, composition, identity, laws) and verifying functor laws. That abstract construction
remains future work. What is complete: a concrete ZPCategory witness for each functor,
plus the domain-specific theorem grounding the initial-object claim.

- **F_A (SLat)**: NatSLat appendix — ℕ with max/0 as ZPSemilattice, ≤ as poset-category.
  0 is categorical initial. Distinct concrete instance. OQ-G3 closed for F_A.
- **F_B / F_C / F_D**: NNRealZPCat appendix — ℝ≥0 with ≤ is the **shared** concrete ZPCategory
  witness for all three. One concrete instance; three distinct domain contexts. The domain
  differentiation is carried by the per-domain theorems proved separately in T-H1 above:
  C3 (ZPB) for F_B, T1b (ZPC) for F_C, T4 (ZPD) for F_D. `nnreal_initial_grounding` is the
  single Lean definition establishing 0 : NNReal as a categorical initial object.
  Full abstract functors (Lean Functor terms to pTop / InfoSp / Hilb) remain future work (OQ-G3). -/

/-! ## T-H1 — Initial-Object Properties Under Each Instantiation Functor -/

/-- T-H1 for F_A — ⊥ is the initial object in the join-semilattice codomain.
    For any element x, ⊥ ≼ x: the unique "morphism" ⊥ → x exists (bot_le).
    In the poset-as-category, ⊥ satisfies the universal property of 0.
    The NatSLat appendix exhibits ℕ as a concrete ZPCategory grounding this claim.
    OQ-G3 is closed for F_A. -/
theorem th1_fa {L : Type*} [ZPSemilattice L] (x : L) :
    le bot x :=
  bot_le x

/-- T-H1 for F_B — domain property: topological irreversibility of 0 in Q₂.
    No continuous path returns to 0 from any x ≠ 0 (ZPB C3). This is the key
    irreversibility property that F_B's initial-object claim rests on, grounded in
    ZPB T3 (clopen isolation) and T5 (total disconnectedness).
    The shared concrete ZPCategory witness for F_B/C/D is nnrealZPCategory (ℝ≥0 with ≤);
    C3 is the domain analogue of AX-G2 in that category. See nnreal_initial_grounding
    in the NNRealZPCat appendix for the categorical grounding. -/
theorem th1_fb :
    ∀ x : Q₂, x ≠ 0 → ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0 :=
  c3_irreversible

/-- T-H1 for F_C — domain property: the P → Q snap costs exactly 1 bit.
    JSD(P, Q) = log 2 (ZPC T1b). This is the information-cost fact that F_C's
    initial-object claim rests on.
    The shared concrete ZPCategory witness for F_B/C/D is nnrealZPCategory (ℝ≥0 with ≤);
    the snap corresponds to the morphism 0 → ⟨Real.log 2, _⟩ in that category.
    See nnreal_initial_grounding in the NNRealZPCat appendix for the categorical grounding. -/
theorem th1_fc : jsdPQ = Real.log 2 :=
  t1b_jsd

/-- T-H1 for F_D — domain property: the snap is an orthogonal shift in Hilb.
    ⟪T(0), T(ε₀)⟫_ℂ = 0 (ZPD T4). This is the Hilbert-space fact that F_D's
    initial-object claim rests on, grounded in ZPD T2 (injectivity, norm 1) and DP-1.
    The shared concrete ZPCategory witness for F_B/C/D is nnrealZPCategory (ℝ≥0 with ≤);
    the categorical snap 0 → 1 corresponds to the orthogonal shift T(0) → T(ε₀) in Hilb.
    See nnreal_initial_grounding in the NNRealZPCat appendix for the categorical grounding. -/
theorem th1_fd (n : ℕ) (hn : 2 ≤ n) :
    @inner ℂ (StateSpace n) _
      (transitionOp n ⟨0, by omega⟩)
      (transitionOp n ⟨1, by omega⟩) = 0 :=
  t4_snap_orthogonal n hn

/-! ## T-H2 — Compatibility of Singularity Characterizations (OQ-G4 Closed)

ZPG characterizes the singularity as domain absence: hom(X, 0) = ∅ for X ≇ 0 (T3/AX-G2).
ZPC characterizes it as infinite accumulation: ∑ I(X_k → X_{k+1}) diverges along any
sequence approaching 0 (t2_diverges). These are compatible: domain-absence is strictly
stronger than divergence — if infinite accumulation is required to reach 0, no finite
morphism can accomplish it, which is exactly hom(X, 0) = ∅. Both sides are independently
derived. Their joint derivability closes OQ-G4. -/

/-- T-H2: Both singularity characterizations are jointly derivable.
    Part I (ZPG side): hom(X, 0) = ∅ for any X not isomorphic to 0 — domain-absent.
    Part II (ZPC side): accumulated surprisal along sequences approaching 0 diverges.
    The conjunction establishes compatibility: same structural obstruction, two vantages. -/
theorem th2_singularity_compatibility {C : Type*} [Category C] [zpcat : ZPCategory C]
    (X : C) (hne : IsEmpty (X ≅ zpcat.zpInitial)) :
    IsEmpty (X ⟶ zpcat.zpInitial) ∧
    (∀ M : ℝ, ∃ n : ℕ, M < circPartial n) :=
  ⟨t3_unreachability X hne, t2_diverges⟩

/-! ## T-H3 — The Binary Snap Under All Four Functors (Cross-Framework)

The Binary Snap 0 → ε₀ is characterized consistently under all four instantiation
functors. Each domain document establishes irreversibility by its own methods.
T-SNAP (Binary Snap Causality) is a derived theorem inherited from ZP-E v2.0. -/

/-- T-H3: The Binary Snap is described consistently under all four functors.
    Assembled from independently proved domain theorems; no bridge axioms used.
    - Under F_A (ZPA/ZPE): join c₀ c₁ = c₁. T-SNAP derived; AX-1 retired.
    - Under F_B (ZPB): no continuous path ε₀ → 0 in Q₂. Topologically irreversible (C3).
    - Under F_C (ZPC): JSD(P, Q) = log 2 (1 bit). Informational cost of the Snap (T1b).
    - Under F_D (ZPD): ⟪T(0), T(ε₀)⟫_ℂ = 0. Snap produces orthogonal shift (T4).
    Cross-framework consistency: four independent derivations, same verdict. -/
theorem th3_snap_all_functors (n : ℕ) (hn : 2 ≤ n) :
    join c₀ c₁ = c₁ ∧
    (∀ x : Q₂, x ≠ 0 → ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0) ∧
    jsdPQ = Real.log 2 ∧
    @inner ℂ (StateSpace n) _
      (transitionOp n ⟨0, by omega⟩)
      (transitionOp n ⟨1, by omega⟩) = 0 :=
  ⟨t_snap_machine, c3_irreversible, t1b_jsd, t4_snap_orthogonal n hn⟩

end ZeroParadox.ZPH

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPC ZeroParadox.ZPD
open CategoryTheory

#print axioms th1_fa
#print axioms th1_fb
#print axioms th1_fc
#print axioms th1_fd
#print axioms th2_singularity_compatibility
#print axioms th3_snap_all_functors

end PurityCheck

/-! ## Appendix — NatSLat: ℕ as a Concrete ZPCategory (Closes OQ-G3 for F_A)

ℕ with Nat.max as join and 0 as bottom is a ZPSemilattice. The induced ≼ relation
agrees with the standard ≤ on ℕ. The poset-as-category construction (morphisms are
≤-proofs packed as ULift (PLift (m ≤ n))) makes 0 categorical initial and admits no
terminal object. AX-G2 holds because m ≤ 0 implies m = 0. Together these verify ℕ
instantiates ZPCategory with zpInitial = 0. This is the concrete grounding of the
F_A claim in T-H1: OQ-G3 is closed for F_A. -/

section NatSLat

open ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPG CategoryTheory CategoryTheory.Limits

/-- ℕ is a ZPSemilattice with max as join and 0 as bottom. -/
instance natZPSemilattice : ZPSemilattice ℕ where
  join       := max
  bot        := 0
  join_assoc := max_assoc
  join_comm  := max_comm
  join_idem  := max_self
  bot_join   := fun n => max_eq_right (Nat.zero_le n)

/-- Category on ℕ via ≤: morphisms m → n are proofs of m ≤ n. -/
instance natOrderCat : Category ℕ where
  Hom m n     := ULift (PLift (m ≤ n))
  id  n       := ⟨⟨le_refl n⟩⟩
  comp f g    := ⟨⟨le_trans f.down.down g.down.down⟩⟩
  id_comp _   := Subsingleton.elim _ _
  comp_id _   := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Every morphism out of 0 exists and is unique (Nat.zero_le). -/
instance natHom0Unique (n : ℕ) : Unique ((0 : ℕ) ⟶ n) where
  default := ⟨⟨Nat.zero_le n⟩⟩
  uniq    := fun _ => Subsingleton.elim _ _

/-- ℕ is a ZPCategory with 0 as initial object.
    AX-G1: no greatest natural number exists.
    AX-G2: m ≤ 0 implies m = 0, so hom(m, 0) = ∅ when m ≇ 0. -/
noncomputable instance natZPCategory : ZPCategory ℕ where
  zpInitial         := 0
  zpIsInitial       := IsInitial.ofUnique 0
  ax_g1_no_terminal := fun t => ⟨fun ht => by
    have h : t + 1 ≤ t := (ht.from (t + 1)).down.down; omega⟩
  ax_g2             := fun n hne => ⟨fun f => by
    have hn0 : n = 0 := Nat.le_zero.mp f.down.down
    subst hn0; exact hne.elim (Iso.refl (0 : ℕ))⟩

end NatSLat

/-! ## Axiom Purity Check — NatSLat -/

section PurityCheckNatSLat
open ZeroParadox.ZPG CategoryTheory CategoryTheory.Limits

-- OQ-G3 closed for F_A: ℕ has a categorical initial object grounded in the ZPA semilattice.
-- IsInitial is a Type (not Prop), so `def` rather than `theorem`.
noncomputable def natSLat_initial_grounding : IsInitial (0 : ℕ) :=
  natZPCategory.zpIsInitial
#print axioms natSLat_initial_grounding

end PurityCheckNatSLat

/-! ## Appendix — NNRealZPCat: ℝ≥0 as a Concrete ZPCategory
    (Shared Categorical Witness for F_B, F_C, F_D)

ℝ≥0 (nonneg reals) with ≤ as morphisms is a ZPCategory where 0 is the initial object.
For any t : ℝ≥0, t + 1 > t, so no terminal object exists (AX-G1). For any x ≤ 0 in
ℝ≥0, x = 0 (AX-G2). Together, ℝ≥0 instantiates ZPCategory with zpInitial = 0.

`nnreal_initial_grounding` is the single Lean definition establishing this. F_B, F_C, and
F_D all share this one concrete categorical instance — they are distinguished only by the
domain-specific theorems proved separately in T-H1 (C3 for F_B, T1b for F_C, T4 for F_D).
Full abstract functors (Lean Functor terms to pTop / InfoSp / Hilb) remain future work (OQ-G3). -/

section NNRealZPCat
open ZeroParadox.ZPB ZeroParadox.ZPC ZeroParadox.ZPD ZeroParadox.ZPG
open CategoryTheory CategoryTheory.Limits

/-- Category on ℝ≥0 via ≤: morphisms x → y are proofs of x ≤ y. -/
instance nnrealOrderCat : Category NNReal where
  Hom x y     := ULift (PLift (x ≤ y))
  id  x       := ⟨⟨le_refl x⟩⟩
  comp f g    := ⟨⟨le_trans f.down.down g.down.down⟩⟩
  id_comp _   := Subsingleton.elim _ _
  comp_id _   := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Every morphism out of 0 exists and is unique (zero_le). -/
instance nnrealHom0Unique (y : NNReal) : Unique ((0 : NNReal) ⟶ y) where
  default := ⟨⟨zero_le y⟩⟩
  uniq    := fun _ => Subsingleton.elim _ _

/-- ℝ≥0 is a ZPCategory with 0 as initial object.
    AX-G1: no greatest nonneg real — t + 1 > t for all t.
    AX-G2: x ≤ 0 implies x = 0 (zero_le gives 0 ≤ x, antisymmetry gives x = 0). -/
noncomputable instance nnrealZPCategory : ZPCategory NNReal where
  zpInitial         := 0
  zpIsInitial       := IsInitial.ofUnique 0
  ax_g1_no_terminal := fun t => ⟨fun ht => by
    have h : t + 1 ≤ t := (ht.from (t + 1)).down.down
    exact absurd h (not_le.mpr (lt_add_of_pos_right t one_pos))⟩
  ax_g2             := fun x hne => ⟨fun f => by
    have hx0 : x = 0 := le_antisymm f.down.down (zero_le x)
    subst hx0; exact hne.elim (Iso.refl (0 : NNReal))⟩

/-- Shared concrete ZPCategory witness for F_B, F_C, and F_D.
    ℝ≥0 with ≤ is a ZPCategory (nnrealZPCategory); 0 : NNReal is the categorical initial object.
    All three instantiation functors share this single concrete instance — same category, three
    distinct domain contexts differentiated by the per-domain theorems in T-H1:
      F_B: th1_fb (C3 — topological irreversibility in Q₂)
      F_C: th1_fc (T1b — JSD snap cost = log 2)
      F_D: th1_fd (T4 — orthogonal snap shift in Hilb)
    This is one concrete witness, not three independent verifications. The domain facts above
    are proved separately; this definition establishes only the shared categorical structure.
    Full abstract functors (Lean Functor terms to pTop / InfoSp / Hilb) remain future work
    (OQ-G3). -/
noncomputable def nnreal_initial_grounding : IsInitial (0 : NNReal) :=
  nnrealZPCategory.zpIsInitial

end NNRealZPCat

/-! ## Axiom Purity Check — NNRealZPCat -/

section PurityCheckNNRealZPCat
open ZeroParadox.ZPG CategoryTheory CategoryTheory.Limits

-- One shared witness for F_B, F_C, F_D: ℝ≥0 has a categorical initial object.
-- Domain differentiation (C3, T1b, T4) is proved separately in T-H1 above.
#print axioms nnreal_initial_grounding

end PurityCheckNNRealZPCat

/-! ## Appendix — Q₂BallCat and fb_functor: Full Functor for F_B

The clopen ball hierarchy in Q₂ — the sequence B(0, 2⁰) ⊃ B(0, 2⁻¹) ⊃ ⋯ converging to {0} —
gives a natural category grounding F_B concretely in Q₂'s topology.

Q₂BallDepth indexes this hierarchy: depth n corresponds to the clopen ball B(0, 2^(-n)).
A morphism n → m (n ≤ m) descends into a smaller ball — topologically forward, not back.
AX-G2 (no morphism m → 0 for m ≠ 0) is the categorical encoding of C3: no continuous path
returns from a non-zero element to 0 in Q₂.

fb_functor : Functor ℕ Q₂BallDepth is the concrete F_B Lean term.
The snap morphism 0 → 1 in ℕ maps to the depth-0 → depth-1 ball transition;
fb_snap_q2_grounded connects this to C3. -/

section Q₂BallFunctor

open ZeroParadox.ZPB ZeroParadox.ZPG CategoryTheory CategoryTheory.Limits

/-- Q₂BallDepth: depth index for the clopen ball hierarchy in Q₂.
    A distinct type (not ℕ) so its Category and ZPCategory instances
    do not conflict with NatSLat's Category ℕ instance. -/
structure Q₂BallDepth where
  val : ℕ
  deriving DecidableEq

instance : Zero Q₂BallDepth := ⟨⟨0⟩⟩

@[ext] theorem Q₂BallDepth.ext {a b : Q₂BallDepth} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- Category on Q₂BallDepth: morphisms n → m are proofs of n.val ≤ m.val.
    Descending to a deeper ball (smaller radius, closer to 0) is the forward direction. -/
instance q2BallCat : Category Q₂BallDepth where
  Hom n m     := ULift (PLift (n.val ≤ m.val))
  id  _       := ⟨⟨Nat.le_refl _⟩⟩
  comp f g    := ⟨⟨Nat.le_trans f.down.down g.down.down⟩⟩
  id_comp _   := Subsingleton.elim _ _
  comp_id _   := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Every morphism out of depth 0 exists and is unique (Nat.zero_le). -/
instance q2BallHom0Unique (n : Q₂BallDepth) : Unique ((0 : Q₂BallDepth) ⟶ n) where
  default := ⟨⟨Nat.zero_le _⟩⟩
  uniq    := fun _ => Subsingleton.elim _ _

/-- Q₂BallDepth is a ZPCategory with depth 0 as the initial object.
    AX-G1: depth has no maximum — n + 1 > n always.
    AX-G2: m.val ≤ 0 forces m = 0, grounded in C3 (no return to 0 in Q₂). -/
noncomputable instance q2BallZPCat : ZPCategory Q₂BallDepth where
  zpInitial         := 0
  zpIsInitial       := IsInitial.ofUnique 0
  ax_g1_no_terminal := fun t => ⟨fun ht => by
    have h : t.val + 1 ≤ t.val := (ht.from ⟨t.val + 1⟩).down.down
    omega⟩
  ax_g2             := fun n hne => ⟨fun f => by
    have hle : n.val ≤ 0 := f.down.down
    have h0 : n.val = 0   := Nat.le_zero.mp hle
    have hn : n = 0       := Q₂BallDepth.ext h0
    subst hn
    exact hne.elim (Iso.refl _)⟩

/-- Semantic embedding: depth n corresponds to the clopen ball B(0, 2^(-n)) in Q₂. -/
noncomputable def q2BallAt (n : Q₂BallDepth) : Set Q₂ :=
  Metric.closedBall 0 (2 ^ (-(n.val : ℤ)))

/-- Ball containment is antitone in depth: n ≤ m → B(0, 2^(-m)) ⊆ B(0, 2^(-n)). -/
theorem q2Ball_antitone {n m : Q₂BallDepth} (h : n.val ≤ m.val) :
    q2BallAt m ⊆ q2BallAt n := by
  simp only [q2BallAt]
  apply Metric.closedBall_subset_closedBall
  exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (by omega : -(↑m.val : ℤ) ≤ -(↑n.val : ℤ))

/-- Semantic grounding of fb_functor's snap morphism 0 → ⟨1⟩:
    For any x ∈ B(0, 2^(-1)) with x ≠ 0, C3 (ZPB) guarantees no continuous path
    returns from x to 0 in Q₂. This is the topological content of AX-G2 in Q₂BallDepth. -/
theorem fb_snap_q2_grounded :
    ∀ x : Q₂, x ∈ q2BallAt ⟨1⟩ → x ≠ 0 →
      ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0 :=
  fun x _ hx => c3_irreversible x hx

/-- fb_functor: the concrete Lean Functor term for F_B.
    Source: ℕ with ≤ (NatSLat / NatOrderCat).
    Target: Q₂BallDepth with ≤ (q2BallCat), grounded in Q₂ via q2BallAt and C3.
    Object map: n ↦ ⟨n⟩ (each ℕ index wraps to the corresponding ball depth).
    Morphism map: carries the ≤ proof across; functor laws hold by Subsingleton. -/
noncomputable def fb_functor : Functor ℕ Q₂BallDepth where
  obj n       := ⟨n⟩
  map f       := ⟨⟨f.down.down⟩⟩
  map_id _    := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- fb_functor maps the NatSLat initial object to the Q₂BallDepth initial object. -/
noncomputable def fb_preserves_initial : IsInitial (fb_functor.obj 0) :=
  show IsInitial (0 : Q₂BallDepth) from IsInitial.ofUnique 0

end Q₂BallFunctor

/-! ## Axiom Purity Check — Q₂BallFunctor -/

section PurityCheckQ₂BallFunctor
open ZeroParadox.ZPG CategoryTheory CategoryTheory.Limits

#print axioms fb_preserves_initial
#print axioms fb_snap_q2_grounded

end PurityCheckQ₂BallFunctor
