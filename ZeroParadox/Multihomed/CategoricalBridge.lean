import ZeroParadox.Order.Lattice
import ZeroParadox.Valuation.Padic
import ZeroParadox.Information.Surprisal
import ZeroParadox.State.StateSpace
import ZeroParadox.Order.Snap
import ZeroParadox.Category.Category
import Mathlib.Tactic

/-!
# ZP-H: Categorical Bridge

## Engineer's Take

Now that the categorical structure is established, ZPH goes back through ZPA
to ZPD and takes one result from each of those frameworks. T-H3 joins the four
with an "and": the join in the machine phase, no continuous path back to zero
in Q₂, the one bit between P and Q, and two orthogonal basis vectors. No
functor shows up in it, and none of the four leans on another. Four independent
derivations. I read them as different vantage points on the same snap with the
same verdict. That is my reading, and T-H3 doesn't state it.

---

## Formal Overview (AI-assisted)

Connects ZP-G (Category Theory) to ZP-A through ZP-E. Key results T-H1 to T-H3, the functor witnesses
and the OQ-G3 status: `ZeroParadox/Multihomed/CategoricalBridge.md`.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox
open ZeroParadox
open ZeroParadox
open ZeroParadox
open ZeroParadox
open CategoryTheory

/-! ## D-H1 — Morphisms of C are State Transitions (Design Commitment)

A morphism f: A → B in C is a state transition satisfying:
(i) Forward direction: every non-identity morphism represents a net addition of informational content.
(ii) Compatibility with AX-G2: no morphism X → 0 exists for X not isomorphic to 0.
(iii) Composition: composition corresponds to sequential state accumulation.
D-H1 is a design commitment, not a derivation. No Lean theorem — the choice is what
makes the instantiation functors well-defined. A different morphism structure would
yield different functors. -/

/-! ## Section III — Instantiation Functors: Domain Properties

F_B, F_C, F_D are declared below as functors out of ℕ (`natOrderCat`), not out of an abstract
ZPCategory; F_A has no functor term in this file. A Lean construction of F_B, F_C, F_D as a CategoryTheory.Functor into a
real Mathlib category is now done in the sibling files (ZeroParadox/Valuation/TopFunctor.lean / ZeroParadox/State/HilbFunctor.lean /
ZeroParadox/Multihomed/InfoFunctor.lean, bundled in ZeroParadox/Multihomed/MC1Bridge.lean): fB into TopCat, fD into ModuleCat ℂ, fC into the Kleisli
category of PMF. (Mathlib has no bespoke SLat/pTop/InfoSp/Hilb categories, so those standard
categories are the genuine realizations.) The proxies below are the original concrete witnesses,
superseded by those real-category functors; each still provides a concrete ZPCategory witness
plus a domain-specific theorem stated beside it, which its initial-object proof does not use.

- **F_A (SLat)**: NatSLat appendix — ℕ with max/0 as ZPSemilattice, ≤ as poset-category.
  0 is categorical initial. Distinct concrete instance. OQ-G3 closed for F_A.
- **F_B**: Q₂BallDepth appendix — `fb_functor : Functor ℕ Q₂BallDepth`, beside C3.
- **F_C**: InfoDepth appendix — `fc_functor : Functor ℕ InfoDepth`, beside T1b.
- **F_D**: HilbDimDepth appendix — `fd_functor : Functor ℕ HilbDimDepth`, beside T4.
  Each has a distinct depth-index type, ZPCategory instance, concrete Functor term,
  preserves_initial definition, and a domain theorem stated beside it. These depth-index types are
  proxies isomorphic to ℕ — concrete witnesses, not the real domain categories. The full
  functors into the real Mathlib categories (TopCat / ModuleCat ℂ / KleisliCat PMF) are now
  built in ZeroParadox/Valuation/TopFunctor.lean / ZeroParadox/State/HilbFunctor.lean / ZeroParadox/Multihomed/InfoFunctor.lean and bundled in ZeroParadox/Multihomed/MC1Bridge.lean; they
  supersede these proxies.
  Their targets carry their own instances (`q2BallZPCat`, `infoDepthZPCat`, `hilbDimZPCat`), not NNReal's. -/

/-! ## T-H1 — Domain Facts Beside Each Instantiation (initiality: `f*_preserves_initial`) -/

/-- T-H1 for F_A — ⊥ of a ZPSemilattice L lies below every element (`bot_le`).
    `Statement:` `le bot x` for every x : L; no category on L is built here and no initiality
    or uniqueness is stated. Separately, the NatSLat appendix builds ℕ as a concrete ZPCategory
    with 0 initial (`natSLat_initial_grounding`). OQ-G3 is closed for F_A. -/
theorem th1_fa {L : Type*} [ZPSemilattice L] (x : L) :
    le bot x :=
  bot_le x

-- Statement: F_A's initiality leg on EVERY `ZPSemilattice`: in ZP-A's induced order (`zpSemilatticeSup`,
-- `zpOrderBot`), ⊥ of `L` is initial in the order category of `L` (Mathlib `Preorder.isInitialBot`);
-- `natSLat_initial_grounding` states initiality of ℕ's 0 in `natOrderCat`, a different category, built
-- from ℕ's ≤ and not from the join. The codomain is that order category of one `L`.
open CategoryTheory.Limits in
noncomputable example (L : Type*) [ZPSemilattice L] :
    letI := zpSemilatticeSup L; letI := zpOrderBot L; IsInitial (bot : L) := by
  letI := zpSemilatticeSup L; letI := zpOrderBot L
  exact Preorder.isInitialBot L

-- Statement: CONTROL, on the one-point semilattice `Unit` that ⊥ is also terminal, so this is AX-G1's
-- initial-object half only; the no-terminal half is the separate hypothesis `HasNoTop`.
noncomputable example :
    letI : ZPSemilattice Unit := ⟨fun _ _ => (), (), fun _ _ _ => rfl, fun _ _ => rfl,
      fun _ => rfl, fun _ => rfl⟩
    letI := zpSemilatticeSup Unit; CategoryTheory.Limits.IsTerminal (bot : Unit) :=
  CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun _ => CategoryTheory.homOfLE (le_of_eq (Subsingleton.elim _ _)))
    (fun _ _ => Subsingleton.elim _ _)

/-- T-H1 for F_B — domain property: no continuous path in Q₂ runs from any x ≠ 0 to 0 (ZPB C3).
    `Statement:` the type is one way, x to 0. INVARIANT, of the pair with `disconnectedness_forbids_path`
    (`ZeroParadox/Valuation/BranchingSnapChain.lean`), which excludes a path between any two distinct
    points of a totally disconnected space, from 0 to x as well. `fb_preserves_initial` does not use
    this theorem (it follows from `q2BallHom0Unique`); F_B's target instance is `q2BallZPCat`. -/
theorem th1_fb :
    ∀ x : Q₂, x ≠ 0 → ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0 :=
  c3_irreversible

/-- T-H1 for F_C — domain property: the P → Q snap costs exactly 1 bit.
    JSD(P, Q) = log 2 (ZPC T1b, `t1b_jsd`). `fc_preserves_initial` does not use this theorem
    (it follows from `infoDepthHom0Unique`); F_C's target instance is `infoDepthZPCat`, and no
    declaration here relates `jsdPQ` to a morphism (`fc_snap_info_grounded` only pairs them). -/
theorem th1_fc : jsdPQ = Real.log 2 :=
  t1b_jsd

/-- T-H1 for F_D — domain property (ZPD T4, `t4_snap_orthogonal`): in `StateSpace n`, n ≥ 2,
    the images of indices 0 and 1 under `transitionOp` (= `basisVec`) are orthogonal. The type
    states orthogonality of the pair, not a map between them; calling index 1 "ε₀" is a naming
    convention (`ZeroParadox/State/StateSpace.lean`, Note on Fin n Indexing). `fd_preserves_initial`
    does not use this theorem (it follows from `hilbDimHom0Unique`); F_D's target instance is `hilbDimZPCat`. -/
theorem th1_fd (n : ℕ) (hn : 2 ≤ n) :
    @inner ℂ (StateSpace n) _
      (transitionOp n ⟨0, by omega⟩)
      (transitionOp n ⟨1, by omega⟩) = 0 :=
  t4_snap_orthogonal n hn

/-! ## T-H2 — Compatibility of Singularity Characterizations (OQ-G4 Closed)

ZPG characterizes the singularity as domain absence: hom(X, 0) = ∅ for X ≇ 0 (T3/AX-G2).
ZPC characterizes it as infinite accumulation: the partial circulation
`circPartial n = I(n+1) − I(1)` is unbounded above (t2_diverges). These are compatible: both hold.
No comparison of strength between them is proved here: the theorem below pairs ZP-G Lemma T3
(`t3_unreachability`) with ZP-C Theorem T2 (`t2_diverges`) and uses neither to prove the other. `Reading:` if
infinite accumulation is required to reach 0, no finite morphism reaches it — an informal
link running from divergence toward absence, not a theorem. That both hold together (ZP-G Lemma T3
paired with ZP-C Theorem T2) closes OQ-G4. -/

/-- T-H2: Both singularity characterizations hold together.
    Part I (ZPG side): hom(X, 0) = ∅ for any X not isomorphic to 0 — domain-absent.
    Part II (ZPC side): the partial circulation `circPartial n` is unbounded above.
    `Statement:` a pair `⟨t3_unreachability X hne, t2_diverges⟩`: the two conjuncts are ZP-G Lemma T3
    and ZP-C Theorem T2, and this theorem only pairs them. -/
theorem th2_singularity_compatibility {C : Type*} [Category C] [zpcat : ZPCategory C]
    (X : C) (hne : IsEmpty (X ≅ zpcat.zpInitial)) :
    IsEmpty (X ⟶ zpcat.zpInitial) ∧
    (∀ M : ℝ, ∃ n : ℕ, M < circPartial n) :=
  ⟨t3_unreachability X hne, t2_diverges⟩

/-! ## T-H3 — The Binary Snap: Four Domain Facts, Conjoined (Cross-Framework)

`th3_snap_all_functors` conjoins four separately proved domain facts. Its type names no functor
and relates no conjunct to another, so a reading of one snap seen under four functors is not what
it states. T-SNAP (Binary Snap Causality) is a derived theorem inherited from ZP-E v2.0. -/

/-- T-H3: four separately proved domain facts, conjoined; no bridge axioms used.
    `Statement:` the tuple `⟨t_snap_machine, c3_irreversible, t1b_jsd, t4_snap_orthogonal n hn⟩`, one conjunct per line:
    - ZPA/ZPE: join c₀ c₁ = c₁. T-SNAP derived (the shape; AX-1 retired); the snap occurs given the occurrence commitment and DA-1.
    - ZPB: no continuous path in Q₂ from any x ≠ 0 to 0 (C3).
    - ZPC: JSD(P, Q) = log 2 (1 bit) (T1b).
    - ZPD: indices 0 and 1 of `transitionOp n`, n ≥ 2, are orthogonal in `StateSpace n` (T4).
    No functor occurs in the type, and no conjunct is used to prove another. -/
theorem th3_snap_all_functors (n : ℕ) (hn : 2 ≤ n) :
    join c₀ c₁ = c₁ ∧
    (∀ x : Q₂, x ≠ 0 → ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0) ∧
    jsdPQ = Real.log 2 ∧
    @inner ℂ (StateSpace n) _
      (transitionOp n ⟨0, by omega⟩)
      (transitionOp n ⟨1, by omega⟩) = 0 :=
  ⟨t_snap_machine, c3_irreversible, t1b_jsd, t4_snap_orthogonal n hn⟩

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox ZeroParadox ZPSemilattice ZeroParadox ZeroParadox
open CategoryTheory

#print axioms th1_fa
#print axioms th1_fb
#print axioms th1_fc
#print axioms th1_fd
#print axioms th2_singularity_compatibility
#print axioms th3_snap_all_functors

end PurityCheck

/-! ## Appendix — NatSLat: ℕ as a Concrete ZPCategory (Closes OQ-G3 for F_A)

ℕ with Nat.max as join and 0 as `bot` is a ZPSemilattice (`natZPSemilattice`). The poset-as-category
construction `natOrderCat` is built from ℕ's ≤ directly (morphisms are ≤-proofs packed as
ULift (PLift (m ≤ n))), not from the semilattice's join; no declaration in this file states that
the induced ≼ agrees with ≤. It makes 0 categorical initial and admits no terminal object; AX-G2
holds because m ≤ 0 implies m = 0, so ℕ instantiates ZPCategory with zpInitial = 0. This is a
concrete ZPCategory beside the F_A statement in T-H1: OQ-G3 is closed for F_A. -/

section NatSLat

open ZeroParadox ZPSemilattice ZeroParadox CategoryTheory CategoryTheory.Limits

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
open ZeroParadox CategoryTheory CategoryTheory.Limits

-- OQ-G3 closed for F_A: 0 is initial in `natOrderCat`, built from ≤, not from `natZPSemilattice`'s join.
-- IsInitial is a Type (not Prop), so `def` rather than `theorem`.
noncomputable def natSLat_initial_grounding : IsInitial (0 : ℕ) :=
  natZPCategory.zpIsInitial
#print axioms natSLat_initial_grounding

end PurityCheckNatSLat

/-! ## Appendix — NNRealZPCat: ℝ≥0 as a Concrete ZPCategory
    (A Standalone Categorical Witness)

ℝ≥0 (nonneg reals) with ≤ as morphisms is a ZPCategory where 0 is the initial object.
For any t : ℝ≥0, t + 1 > t, so no terminal object exists (AX-G1). For any x ≤ 0 in
ℝ≥0, x = 0 (AX-G2). Together, ℝ≥0 instantiates ZPCategory with zpInitial = 0.

`nnreal_initial_grounding` is the single Lean definition establishing this. No declaration relates
it to `fb_functor`, `fc_functor` or `fd_functor`, whose targets carry their own instances
(`q2BallZPCat`, `infoDepthZPCat`, `hilbDimZPCat`); NNReal occurs in none of their types. -/

section NNRealZPCat
open ZeroParadox ZeroParadox ZeroParadox ZeroParadox
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
  default := ⟨⟨zero_le (a := y)⟩⟩
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
    have hx0 : x = 0 := le_antisymm f.down.down (zero_le (a := x))
    subst hx0; exact hne.elim (Iso.refl (0 : NNReal))⟩

/-- A concrete ZPCategory witness on ℝ≥0.
    ℝ≥0 with ≤ is a ZPCategory (nnrealZPCategory); 0 : NNReal is the categorical initial object.
    `Statement:` `IsInitial (0 : NNReal)`; it is not related to any of the three instantiation
    functors, whose targets carry their own instances (`q2BallZPCat`, `infoDepthZPCat`, `hilbDimZPCat`).
    OQ-G3 is closed (CLAIMS.md); the real-category functors are in the sibling files. -/
noncomputable def nnreal_initial_grounding : IsInitial (0 : NNReal) :=
  nnrealZPCategory.zpIsInitial

end NNRealZPCat

/-! ## Axiom Purity Check — NNRealZPCat -/

section PurityCheckNNRealZPCat
open ZeroParadox CategoryTheory CategoryTheory.Limits

-- ℝ≥0 has a categorical initial object; not the target of fb/fc/fd_functor.
#print axioms nnreal_initial_grounding

end PurityCheckNNRealZPCat

/-! ## Appendix — Q₂BallCat and fb_functor: Full Functor for F_B

Q₂BallDepth indexes the clopen balls B(0, 2^(-n)) of Q₂ by depth n; a morphism n → m (n ≤ m)
descends into a smaller ball. AX-G2 (no morphism m → 0 for m ≠ 0) holds here by antisymmetry of ≤
on the depth index; C3 (no continuous path returns from a non-zero element to 0 in Q₂) is the
domain fact it mirrors. In `TopCat`, where `fB_functor` lands, the floor `{0}` is not initial
(`padic_bottom_not_initial`). fb_functor : Functor ℕ Q₂BallDepth is the concrete F_B Lean term;
fb_snap_q2_grounded restates C3 for points of the depth-1 ball; its type names no morphism. -/

section Q₂BallFunctor

open ZeroParadox ZeroParadox CategoryTheory CategoryTheory.Limits

/-! ### NO-GO gauge — `Q₂BallDepth`, `InfoDepth`, `HilbDimDepth` are NEWTYPES, not requirements
classes. Each wraps a single `val : ℕ` with no laws, existing only to give `ℕ` a distinct `Category`
instance without colliding with `NatSLat`'s. **The degeneracy question does not apply**: there is
nothing to fail, because there is nothing required. Membership is never cited as evidence for
anything here — the content is entirely in the `Category` / `ZPCategory` instances built on top.

Flagged by `check_classes.py` because it keys on the `structure` keyword and cannot tell a newtype
from a requirements class. That is the right conservative default; this note is the answer. -/

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
    AX-G2: m.val ≤ 0 forces m = 0 (antisymmetry); C3 (no return to 0 in Q₂) is the domain analogue. -/
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

/-- C3 (ZPB) stated for x in the depth-1 ball `q2BallAt ⟨1⟩`: no continuous path in Q₂ runs from
    x ≠ 0 to 0. The type names no morphism of `Q₂BallDepth`, the morphism 0 → ⟨1⟩ included.
    `Statement:` the ball hypothesis `x ∈ q2BallAt ⟨1⟩` is unused by the proof: the content is
    `c3_irreversible`'s, which carries no ball hypothesis. -/
theorem fb_snap_q2_grounded :
    ∀ x : Q₂, x ∈ q2BallAt ⟨1⟩ → x ≠ 0 →
      ¬∃ γ : C(Set.Icc (0 : ℝ) 1, Q₂),
        γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = 0 :=
  fun x _ hx => c3_irreversible x hx

/-- fb_functor: the concrete Lean Functor term for F_B.
    Source: ℕ with ≤ (NatSLat / NatOrderCat).
    Target: Q₂BallDepth with ≤ (q2BallCat); neither its type nor its definition uses q2BallAt or C3.
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
open ZeroParadox CategoryTheory CategoryTheory.Limits

#print axioms fb_preserves_initial
#print axioms fb_snap_q2_grounded

end PurityCheckQ₂BallFunctor

/-! ## Appendix — InfoDepthCat and fc_functor: Full Functor for F_C

InfoDepth is a newtype over ℕ named for surprisal levels; no declaration here maps a depth to a
surprisal value. A morphism n → m is a proof of n ≤ m. AX-G2 (no morphism m → 0 for m ≠ 0) holds
here by antisymmetry of ≤ on the depth index.
fc_functor : Functor ℕ InfoDepth is the concrete F_C Lean term; fc_snap_info_grounded
pairs the morphism 0 → ⟨1⟩ with T1b (JSD = log 2) and relates neither to the other. -/

section InfoDepthFunctor

open ZeroParadox ZeroParadox CategoryTheory CategoryTheory.Limits

/-- InfoDepth: surprisal-level index for the information hierarchy.
    A distinct type (not ℕ) so its Category and ZPCategory instances
    do not conflict with NatSLat's or Q₂BallDepth's instances. -/
structure InfoDepth where
  val : ℕ
  deriving DecidableEq

instance : Zero InfoDepth := ⟨⟨0⟩⟩

@[ext] theorem InfoDepth.ext {a b : InfoDepth} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- Category on InfoDepth: morphisms n → m are proofs of n.val ≤ m.val.
    Advancing to higher surprisal (more informational content) is the forward direction. -/
instance infoDepthCat : Category InfoDepth where
  Hom n m     := ULift (PLift (n.val ≤ m.val))
  id  _       := ⟨⟨Nat.le_refl _⟩⟩
  comp f g    := ⟨⟨Nat.le_trans f.down.down g.down.down⟩⟩
  id_comp _   := Subsingleton.elim _ _
  comp_id _   := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Every morphism out of depth 0 exists and is unique (Nat.zero_le). -/
instance infoDepthHom0Unique (n : InfoDepth) : Unique ((0 : InfoDepth) ⟶ n) where
  default := ⟨⟨Nat.zero_le _⟩⟩
  uniq    := fun _ => Subsingleton.elim _ _

/-- InfoDepth is a ZPCategory with depth 0 as the initial object.
    AX-G1: depth has no maximum — n + 1 > n always.
    AX-G2: m.val ≤ 0 forces m = 0; no morphism returns to depth 0 from a positive depth. -/
noncomputable instance infoDepthZPCat : ZPCategory InfoDepth where
  zpInitial         := 0
  zpIsInitial       := IsInitial.ofUnique 0
  ax_g1_no_terminal := fun t => ⟨fun ht => by
    have h : t.val + 1 ≤ t.val := (ht.from ⟨t.val + 1⟩).down.down
    omega⟩
  ax_g2             := fun n hne => ⟨fun f => by
    have h0 : n.val = 0 := Nat.le_zero.mp f.down.down
    have hn : n = 0     := InfoDepth.ext h0
    subst hn
    exact hne.elim (Iso.refl _)⟩

/-- The morphism 0 → ⟨1⟩ of InfoDepth beside T1b (ZPC): JSD(P, Q) = log 2 (1 bit). The type relates
    neither to the other, and maps no depth to a surprisal value.
    `Statement:` a pair: the first conjunct, `Nonempty (0 ⟶ ⟨1⟩)` in InfoDepth, is witnessed by
    `⟨⟨Nat.zero_le 1⟩⟩`, the second is proved by `t1b_jsd`, and the theorem only pairs them. -/
theorem fc_snap_info_grounded :
    Nonempty ((0 : InfoDepth) ⟶ ⟨1⟩) ∧ jsdPQ = Real.log 2 :=
  ⟨⟨⟨⟨Nat.zero_le 1⟩⟩⟩, t1b_jsd⟩

/-- fc_functor: the concrete Lean Functor term for F_C.
    Source: ℕ with ≤ (NatSLat / NatOrderCat).
    Target: InfoDepth with ≤ (infoDepthCat); neither its type nor its definition uses surprisal or T1b.
    Object map: n ↦ ⟨n⟩ (each ℕ index wraps to the corresponding surprisal depth).
    Morphism map: carries the ≤ proof across; functor laws hold by Subsingleton. -/
noncomputable def fc_functor : Functor ℕ InfoDepth where
  obj n        := ⟨n⟩
  map f        := ⟨⟨f.down.down⟩⟩
  map_id _     := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- fc_functor maps the NatSLat initial object to the InfoDepth initial object. -/
noncomputable def fc_preserves_initial : IsInitial (fc_functor.obj 0) :=
  show IsInitial (0 : InfoDepth) from IsInitial.ofUnique 0

end InfoDepthFunctor

/-! ## Axiom Purity Check — InfoDepthFunctor -/

section PurityCheckInfoDepthFunctor
open ZeroParadox CategoryTheory CategoryTheory.Limits

#print axioms fc_preserves_initial
#print axioms fc_snap_info_grounded

end PurityCheckInfoDepthFunctor

/-! ## Appendix — HilbDimCat and fd_functor: Full Functor for F_D

HilbDimDepth is a newtype over ℕ named for state-space dimensions; no declaration here maps a
depth to a `StateSpace`. A morphism n → m is a proof of n ≤ m. AX-G2 (no morphism m → 0 for
m ≠ 0) holds here by antisymmetry of ≤ on the depth index.
fd_functor : Functor ℕ HilbDimDepth is the concrete F_D Lean term; fd_snap_hilb_grounded
pairs the morphism 0 → ⟨1⟩ with T4 (`t4_snap_orthogonal`) and relates neither to the other. -/

section HilbDimFunctor

open ZeroParadox ZeroParadox CategoryTheory CategoryTheory.Limits

/-- HilbDimDepth: dimension index for the Hilbert state space hierarchy.
    A distinct type (not ℕ) so its Category and ZPCategory instances
    do not conflict with NatSLat's, Q₂BallDepth's, or InfoDepth's instances. -/
structure HilbDimDepth where
  val : ℕ
  deriving DecidableEq

instance : Zero HilbDimDepth := ⟨⟨0⟩⟩

@[ext] theorem HilbDimDepth.ext {a b : HilbDimDepth} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

/-- Category on HilbDimDepth: morphisms n → m are proofs of n.val ≤ m.val.
    Advancing to a higher-dimensional state space is the forward direction. -/
instance hilbDimCat : Category HilbDimDepth where
  Hom n m     := ULift (PLift (n.val ≤ m.val))
  id  _       := ⟨⟨Nat.le_refl _⟩⟩
  comp f g    := ⟨⟨Nat.le_trans f.down.down g.down.down⟩⟩
  id_comp _   := Subsingleton.elim _ _
  comp_id _   := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

/-- Every morphism out of depth 0 exists and is unique (Nat.zero_le). -/
instance hilbDimHom0Unique (n : HilbDimDepth) : Unique ((0 : HilbDimDepth) ⟶ n) where
  default := ⟨⟨Nat.zero_le _⟩⟩
  uniq    := fun _ => Subsingleton.elim _ _

/-- HilbDimDepth is a ZPCategory with depth 0 as the initial object.
    AX-G1: dimension has no maximum — n + 1 > n always.
    AX-G2: m.val ≤ 0 forces m = 0 (antisymmetry). In `ModuleCat ℂ` it fails: every stage maps into
    the zero module (`fD_has_return`) and stage 1 is not a zero object (`leaf_not_isZero`,
    `ZeroParadox/Category/SeamNotColimit.lean`). -/
noncomputable instance hilbDimZPCat : ZPCategory HilbDimDepth where
  zpInitial         := 0
  zpIsInitial       := IsInitial.ofUnique 0
  ax_g1_no_terminal := fun t => ⟨fun ht => by
    have h : t.val + 1 ≤ t.val := (ht.from ⟨t.val + 1⟩).down.down
    omega⟩
  ax_g2             := fun n hne => ⟨fun f => by
    have h0 : n.val = 0 := Nat.le_zero.mp f.down.down
    have hn : n = 0     := HilbDimDepth.ext h0
    subst hn
    exact hne.elim (Iso.refl _)⟩

/-- The morphism 0 → ⟨1⟩ of HilbDimDepth beside T4 (ZPD): indices 0 and 1 of `transitionOp n` are
    orthogonal in `StateSpace n`, n ≥ 2, where n is independent of the depth index.
    `Statement:` a pair: the first conjunct, `Nonempty (0 ⟶ ⟨1⟩)` in HilbDimDepth, is witnessed by
    `⟨⟨Nat.zero_le 1⟩⟩`, the second is proved by `t4_snap_orthogonal n hn`, and the theorem only pairs them. -/
theorem fd_snap_hilb_grounded (n : ℕ) (hn : 2 ≤ n) :
    Nonempty ((0 : HilbDimDepth) ⟶ ⟨1⟩) ∧
    @inner ℂ (StateSpace n) _
      (transitionOp n ⟨0, by omega⟩)
      (transitionOp n ⟨1, by omega⟩) = 0 :=
  ⟨⟨⟨⟨Nat.zero_le 1⟩⟩⟩, t4_snap_orthogonal n hn⟩

/-- fd_functor: the concrete Lean Functor term for F_D.
    Source: ℕ with ≤ (NatSLat / NatOrderCat).
    Target: HilbDimDepth with ≤ (hilbDimCat); neither its type nor its definition uses StateSpace or T4.
    Object map: n ↦ ⟨n⟩ (each ℕ index wraps to the corresponding dimension depth).
    Morphism map: carries the ≤ proof across; functor laws hold by Subsingleton. -/
noncomputable def fd_functor : Functor ℕ HilbDimDepth where
  obj n        := ⟨n⟩
  map f        := ⟨⟨f.down.down⟩⟩
  map_id _     := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- fd_functor maps the NatSLat initial object to the HilbDimDepth initial object. -/
noncomputable def fd_preserves_initial : IsInitial (fd_functor.obj 0) :=
  show IsInitial (0 : HilbDimDepth) from IsInitial.ofUnique 0

end HilbDimFunctor

/-! ## Axiom Purity Check — HilbDimFunctor -/

section PurityCheckHilbDimFunctor
open ZeroParadox CategoryTheory CategoryTheory.Limits

#print axioms fd_preserves_initial
#print axioms fd_snap_hilb_grounded

end PurityCheckHilbDimFunctor
