import ZeroParadox.Order.Lattice
import ZeroParadox.Order.Snap
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Computability.Kleene
import ZeroParadox.Information.BottomMeasure
import ZeroParadox.Valuation.PricedPadicInterface
import ZeroParadox.Ordinal.ProofFloorCanonical
import ZeroParadox.Algebra.Wheel
import ZeroParadox.Multihomed.MC1Bridge
import ZeroParadox.Multihomed.TopNumEdge
import ZeroParadox.Category.Category
import ZeroParadox.Category.LinFunctor
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP Claims Mirror — the machine-checked representation of the claim graph

## Engineer's Take

For a while it looked like this whole framework might be standing on what is technically a false
assumption, and that was scary and fascinating at the same time. The part worth keeping in mind is that
the theories came before the Lean. The PDFs and the ideas predate the formal files, and some of the early
material came out of conversations, a fair number of them across several other models. The conclusions
were reached first and the proofs were retrofitted under them afterward.

I thought the SSOT was already doing this kind of mapping. It was partway there, and what was missing was
the link from each claim to the declaration that discharges it. So the job of this file is to change
nothing in the prose and just write the Lean that is an exact representation of each claim. A lot of these
were already proved, some of them a long time ago, the MC-1 correspondence among them. The proof was never
the missing piece. The link between the claim and the proof was.

I want this file kept as a reference in the same way we did for the bottom, so we never lose track of this
again.

---

## Formal Overview (AI-assisted)

This file is the exact Lean representation of the framework's **claim graph** — the nodes in the SSOT
`claims` store. For each claim the store marks `proved`, a theorem here states the claim exactly and
discharges it from the existing machinery, so the claim graph's `proved` *label* becomes a
kernel-checked *link* to a green declaration. Conjectural claims are represented as their exact `Prop`
(stated, never asserted); the retired MC-1 identity is documented as ill-typed, which is itself the
faithful representation.

**This file changes no prose in any document.** It only mirrors what the claims already assert and lets
the kernel confirm which `proved` labels actually resolve to a real theorem — the check that a status is
backed, not merely labeled. A claim here that fails to elaborate, or cannot be discharged, is a finding:
a `proved` label with nothing under it.

Status legend (the SSOT `claims.status` vocab): proved · corr (corroboration) · conj (conjecture) ·
deep · commitment · retired.

## Structure
- § I  Logical core (order, set theory, computation, the snap).
- (further tranches to come: valuation, information, state, category, ordinal, algebra, MC-1
  correspondence, the floor-reaching E-series, and the Lawvere conjectures.)
-/

namespace ZeroParadox

open ZPSemilattice
open CategoryTheory

/-! ## § I. Logical core -/

/-- Claim `node-order` (proved). Statement: "In order theory, ⊥ is realized as the least element:
    ⊥ ≤ x for every state." Exact representation: the order bottom lies below every element.
    Backing: `bot_le`. -/
theorem claim_node_order {L : Type*} [ZPSemilattice L] (x : L) : le bot x :=
  bot_le x

/-- Claim `node-set-theory` (proved). Statement: "In set theory, ⊥ is realized as the Quine atom
    ⊥ = {⊥}, the self-membered singleton (ZF+AFA)." Exact representation: ⊥ is the unique self-membered
    element, i.e. a Quine atom. Backing: `bot_is_quine_atom`. -/
theorem claim_node_set_theory {L : Type*} [ZPSemilattice L] [AFAStructure L] :
    IsQuineAtom (bot : L) :=
  bot_is_quine_atom

/-- Claim `DA-1` (proved). Statement: "⊥ is the Quine atom realized in the computation layer (DA-1,
    closed concretely in ZP-K)." Exact representation: the machine-phase bottom is a Quine atom.
    Backing: `da1_closed_concrete`. -/
theorem claim_DA1 : IsQuineAtom (bot : MachinePhase) :=
  da1_closed_concrete

/-- Claim `T-SNAP` (proved). Statement: "The Binary Snap ⊥→ε₀ is a theorem (T-SNAP, derived in ZP-E)."
    Exact representation: the concrete snap is the join transition c₀ → c₁ between two distinct states.
    Backing: `t_snap_derived`. -/
theorem claim_T_SNAP : c₀ ≠ c₁ ∧ c₁ ≠ c₀ ∧ join c₀ c₁ = c₁ :=
  t_snap_derived

/-! ## § II. Floor domains (information, valuation) -/

/-- Claim `node-information` (proved). Statement: "In information theory, ⊥ is realized as the null
    state of maximal informational extremity (L-INF)." Exact representation: the surprisal is unbounded
    (no finite bound holds), the L-INF divergence at the null state. Backing: `info_bottom_diverges`. -/
theorem claim_node_information : ∀ M : ℝ, ∃ n : ℕ, M < surprisal n :=
  info_bottom_diverges

/-- Claim `node-valuation` (proved). Statement: "In the p-adic valuation domain, ⊥ is realized at the
    floor where the additive 2-adic valuation diverges, v₂(0) = ∞ (⊤)." Exact representation: the 2-adic
    valuation of 0 is ⊤. Backing: `v2_bot`. -/
theorem claim_node_valuation : v2 0 = ⊤ :=
  v2_bot

/-! ## § III. Remaining bottom-realization nodes (ordinal, algebra, state) -/

/-- Claim `node-ordinal` (proved). Statement: "In the ordinal/proof-theory domain, ⊥ is realized as
    the floor the ε₀-tower descends to (heval floor = ⊥)." Exact representation: the hereditary
    evaluation at the floor is the ordinal bottom. Backing: `heval_floor_eq_bot`. -/
theorem claim_node_ordinal (b : ℕ) : heval b 0 = (⊥ : Ordinal) :=
  heval_floor_eq_bot b

/-- Claim `node-algebra` (proved). Statement: "In algebra, ⊥ is realized as the bottom of the wheel of
    fractions (0·∞ = ⊥)." Exact representation: in the ZP wheel, 0 · ∞ is the wheel bottom.
    Backing: `zpw_zero_mul_inf_eq_bot`. -/
theorem claim_node_algebra : zpwMul (.fin 0) .inf = .bot :=
  zpw_zero_mul_inf_eq_bot

/-- Claim `node-state` (proved). Statement: "In the state/Hilbert domain, ⊥ is realized as the zero
    module (StateSpace 0), the initial object of the state category." Exact representation: an
    initial-object witness exists for the state floor. Backing: `fD_zero_isInitial`. -/
theorem claim_node_state : Nonempty (Limits.IsInitial (fD_functor.obj 0)) :=
  ⟨fD_zero_isInitial⟩

/-! ## § IV. MC-1 correspondence (each domain bottom is its category's categorical bottom) -/

/-- Claim `MC-1-correspondence` (corr). Statement: "Each domain bottom is the categorical bottom of its
    own real category (MC-1, correspondence half — formally realized)." Exact representation: the bundled
    three-realization witness exists. Backing: `mc1_correspondence`. -/
theorem claim_MC1_correspondence : Nonempty MC1Correspondence :=
  ⟨mc1_correspondence⟩

/-- Claim `MC1-cat-state` (corr). Statement: "the state/Hilbert bottom is the initial object of its real
    category (fD zero is initial)." Backing: `fD_zero_isInitial`. -/
theorem claim_MC1_cat_state : Nonempty (Limits.IsInitial (fD_functor.obj 0)) :=
  ⟨fD_zero_isInitial⟩

/-- Claim `MC1-cat-information` (corr). Statement: "the information bottom is the initial object of its
    real category (fC zero is initial)." Backing: `fC_zero_isInitial`. -/
theorem claim_MC1_cat_information : Nonempty (Limits.IsInitial (fC_functor.obj 0)) :=
  ⟨fC_zero_isInitial⟩

/-- Claim `MC1-cat-valuation` (corr). Statement: "the p-adic (valuation) bottom is the inverse limit of
    the ball system in the category realization (⋂ balls = {0})." Backing: `fB_bottom_is_limit`. -/
theorem claim_MC1_cat_valuation : (⋂ n, q2Ball n) = {(0 : Q₂)} :=
  fB_bottom_is_limit

/-! ## § V. Category bottom and the floor-reaching correspondence (E-series, Perron) -/

/-- Claim `node-category` (proved). Statement: "In category theory, ⊥ is realized as the initial object
    (the universal constituent of ZP-G)." Exact representation: in any ZPCategory, the ZP-G bottom is an
    initial object. Backing: `ZPCategory.zpIsInitial`. -/
theorem claim_node_category {C : Type*} [Category C] [ZPCategory C] :
    Nonempty (Limits.IsInitial (ZPCategory.zpInitial : C)) :=
  ⟨ZPCategory.zpIsInitial⟩

/-- Claim `E2-tower-floor` (proved). Statement: "Proof-theory reaches the p-adic floor: the ε₀-tower's
    2-adic encodings eventually enter every closed ball around 0." Backing: `tower_enters_every_ball`. -/
theorem claim_E2_tower_floor (n : ℕ) :
    ∀ᶠ k in Filter.atTop,
      cnf_encode (towerOrd k) ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ))) :=
  tower_enters_every_ball n

/-- Claim `E3-quines-floor` (proved). Statement: "Computation reaches the p-adic floor: the computational
    quine family enters every closed ball around 0 (unbounded family, existential form)." Backing:
    `quines_enter_every_ball`. -/
theorem claim_E3_quines_floor (n : ℕ) :
    ∃ c, IsComputationalQuine c ∧
      (2 : ℤ_[2]) ^ (Encodable.encode c) ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ))) :=
  quines_enter_every_ball n

/-- Claim `E4-info-floor` (proved). Statement: "Information reaches the p-adic floor: the surprisal-depth
    points 2^k eventually enter every closed ball around 0." Backing: `info_points_enter_every_ball`. -/
theorem claim_E4_info_floor (n : ℕ) :
    ∀ᶠ k in Filter.atTop, (2 : ℤ_[2]) ^ k ∈ Metric.closedBall (0 : ℤ_[2]) ((2 : ℝ) ^ (-(n : ℤ))) :=
  info_points_enter_every_ball n

/-- Claim `Perron-info-state` (deep). Statement: "Perron–Frobenius transport across the
    information→state boundary: the stochastic transfer operator has a unit eigenvector (the
    stationary/floor state)." Backing: `stationary_transports_to_unit_eigenvector`. -/
theorem claim_Perron_info_state {n : ℕ}
    (f : Fin n → PMF (Fin n)) (μ : PMF (Fin n)) (hμ : μ.bind f = μ) :
    linMap (a := ⟨n⟩) (b := ⟨n⟩) f (Finsupp.equivFunOnFinite.symm (fun i => ((μ i).toReal : ℂ)))
      = Finsupp.equivFunOnFinite.symm (fun i => ((μ i).toReal : ℂ)) :=
  stationary_transports_to_unit_eigenvector f μ hμ

/-- Claim `node-computability` (proved). Statement: "In computability, ⊥ is realized as the Kleene quine,
    the self-reproducing program and diagonal fixed point of the computation layer." Exact representation:
    in a KleeneStructure, the Kleene quine (any self-containing / Quine-atom element) equals ⊥.
    Backing: `kleene_quine_is_bot`. -/
theorem claim_node_computability {L : Type*} [ZPSemilattice L] [KleeneStructure L]
    (q : L) (hq : IsQuineAtom q) : q = bot :=
  kleene_quine_is_bot q hq

/-! ## § VI. Claims that are NOT theorems (the faithful non-representation)

Three claim-graph nodes are, by their own recorded status, not Lean theorems. Representing them faithfully
means writing no theorem for them — the absence is the representation, and each absence is itself a checked
fact about the claim's status.

- `Lawvere-unification` (conj): "The diagonal fixed point keystone is a manifestation of Lawvere's
  fixed-point theorem." A conjectural cross-domain *connection*, not a single provable proposition (the
  claim graph marks it `conj`). Stated, never asserted; no theorem here.

- `Lawvere-set-comp` (conj): "the set-theoretic and computational diagonal fixed points are two faces of
  one Lawvere fixed point." Conjecture only — and the Set face is provably *not* a Lawvere instance (the
  Cantor obstruction), so this edge stays unbuilt. A theorem asserting it would be false; hence none.

- `MC-1-identity` (retired): "the four domain bottoms are numerically one object." Retired 2026-07-15 as
  ill-typed — `x = y` across distinct categories is not a well-formed proposition, so it cannot be stated
  in Lean at all. The non-representability *is* the finding: the members are provably distinct (the
  walls); only the shared diagonal shape survives, apophatically. No theorem here, by type. -/

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms claim_node_order
#print axioms claim_node_set_theory
#print axioms claim_DA1
#print axioms claim_T_SNAP
#print axioms claim_node_information
#print axioms claim_node_valuation
#print axioms claim_node_ordinal
#print axioms claim_node_algebra
#print axioms claim_node_state
#print axioms claim_MC1_correspondence
#print axioms claim_MC1_cat_state
#print axioms claim_MC1_cat_information
#print axioms claim_MC1_cat_valuation
#print axioms claim_node_category
#print axioms claim_E2_tower_floor
#print axioms claim_E3_quines_floor
#print axioms claim_E4_info_floor
#print axioms claim_Perron_info_state
#print axioms claim_node_computability
end PurityCheck
