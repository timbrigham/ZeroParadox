import ZeroParadox.Valuation.Scale
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZPJ — Accessible Pointed Graphs and AFA Decoration Uniqueness

## Engineer's Take

The zero paradox approaches ε₀ from two distinct directions concurrently — from infinity and from
zero. That same squeeze operates here. The valuation chain is one way of representing it, not the
whole picture.

Getting to self-containing was easy. The harder question — and the reason this document exists — is
why ⊥ has to be the *only* case where this can occur.

For cyclic vertices, the infinitude-of-zeros forces every decoration to ⊥. Agreement between any
two decorations is then trivial, because neither has anywhere else to go. The "any two decorations
agree" statement is the universal quantification of that: each one must independently equal ⊥, so
they agree as a consequence, not as a coincidence.

Cyclic vertices have a finite period k — the path returns in k steps. Acyclic vertices have an
"infinite period" — the path never returns, so there is no cycle length k to close the equation.
This is the same zero-versus-infinity identification that runs throughout the framework: the finite
k of a cycle is the zero side; its absence is the infinity side.

The hardness of the acyclic proof is that "infinite period" gives you nothing to induct on. Reach
cardinality is a finite proxy that encodes it as a strictly decreasing natural number. Proving it
strictly decreases was where the formalization work lived.

## The theorem

For any finite APG, any two valid decorations into any DecorationUniverse are equal.
The proof uses the two typeclass axioms (collect_singleton, collect_val_ge)
together with ValuationStructure. This characterizes when decoration uniqueness holds;
it does not construct a specific AFA model or derive AFA's axioms from ZP's.

## Architecture note: why not ZFSet

Mathlib's ZFSet satisfies the Axiom of Foundation (ZFSet.regularity), forbidding
x ∈ x. For a self-loop v → v, the decoration rule d(v) = {d(v)} requires
d(v) ∈ d(v) — prohibited. The correct target is a DecorationUniverse: an abstract
type with ValuationStructure (which provides scale, val, val_scale) and a collect
operation that assembles a parent's value from its children's values.
See: .claude-local/notes/afa_apg_zfset_correction_2026-05-27.md

## Structure

- § I    APG definition (Quiver + root + accessibility)
- § II   Decoration universe typeclass (ValuationStructure + collect)
- § III  val_iterate: val(scale^k x) = val x + k for x ≠ ⊥ (PROVED)
- § IV   scale_iterate_unique_fp: scale^k(x) = x → x = ⊥ (k-cycle resolved)
- § V    Decoration predicate
- § VI   Self-loop uniqueness (PROVED)
- § VII  k-cycle node uniqueness (PROVED: corollary of § IV)
- § VII' Cyclic vertex uniqueness (PROVED: cyclic_decoration_eq_bot)
- § VIII Acyclic vertex uniqueness (superseded by § IX; local step proved, full route commented out)
- § IX   Global decoration uniqueness (PROVED: direct strong induction on reach cardinality)

## What remains

- Nothing load-bearing. The acyclic-specific route (§ VIII) — induct on depth, congrArg on
  collect, requiring [Fintype V] and a WellFounded instance on acyclic vertices — was not
  needed: § IX (decoration_unique) proves global uniqueness directly by strong induction on
  reach cardinality. The § VIII full theorem is commented out; its local step
  (acyclic_induction_step) is proved.

## Dependencies

- ZeroParadox/Valuation/Scale.lean: ValuationStructure, val_scale, scale_unique_fp, val_finite_of_ne_bot
- Mathlib.Combinatorics.Quiver.Path: directed graph paths
-/

namespace ZeroParadox

open ZeroParadox ZeroParadox ZeroParadox ZPSemilattice

/-! ## § I. APG Definition -/

/-! ### NO-GO gauge — a one-node self-loop is an `APG`, and the class still has teeth.
Measured 2026-08-09 by building it: on `Unit` with `Quiver := fun _ _ => Unit`, `accessible` is the
empty path, so membership is vacuous **on a subsingleton**. A non-member is now PROVED rather than
asserted — the `example` below the structure. ⚠ "A vertex unreachable from the root" presupposes a
root the type does not fix: `root` is a FIELD, so the honest statement is that **no choice of root
works**. Cite the accessibility, not the membership.

⚠ **Accessibility buys representation, not decorability.** Aczel (1988) decorates plain *graphs* —
Mostowski *"every well-founded graph …"* (p. 4), AFA *"every graph …"* (p. 6), neither asking for it.
Root and accessibility make the graph an **apg**, a picture of a unique set under AFA (p. 6). -/

/-- An Accessible Pointed Graph: a Quiver with a distinguished root vertex
    from which every vertex is reachable via directed paths. -/
-- [ZP-CUSTOM] extends: Mathlib.Combinatorics.Quiver.Basic | reason: Mathlib's Quiver is a bare directed graph (objects + edges) with no distinguished root or accessibility requirement. APG adds root : V and the accessibility proof (every vertex reachable from root), matching Aczel's definition of Accessible Pointed Graph (1988 p. 4). ⚠ These fields are NOT load-bearing for anything proved in this file, and no claim of necessity should be made for them in either direction: decoration_unique binds the structure as `_G` and never uses it, so what is actually proved holds for EVERY finite quiver, accessible or not — structurally Aczel's own AFA generality (p. 6). No APG value is constructed anywhere in the corpus as of 2026-08-09.
structure APG (V : Type*) [Quiver V] where
  /-- Distinguished vertex. ⚠ Aczel's term for it is the **point**; he introduces *root* only for the
      special case where every path from it is unique, i.e. a tree (1988 p. 4). The field name is
      this file's, not his. -/
  root : V
  /-- Every vertex is reachable from the root via directed paths. -/
  accessible : ∀ v : V, Nonempty (Quiver.Path root v)

-- Statement: the class has a genuine non-member. On `Bool` with NO edges, every path is `nil`, so no
-- choice of root reaches the other vertex and the structure is uninhabited. Anonymous, so it adds no
-- declaration; being about the CARRIER is the point, since `root` is a field and not fixed by `V`.
example : IsEmpty (@APG Bool ⟨fun _ _ => Empty⟩) := by
  constructor
  rintro ⟨r, acc⟩
  obtain ⟨p⟩ := acc (!r)
  have hnil : ∀ {a b : Bool} (_ : @Quiver.Path Bool ⟨fun _ _ => Empty⟩ a b), a = b := by
    intro a b p
    induction p with
    | nil => rfl
    | cons _ e _ => exact e.elim
  exact Bool.not_ne_self r (hnil p).symm

section APGBasics

variable {V : Type*} [Quiver V]

/-- Immediate successors of a vertex: all w with an edge v ⟶ w. -/
def apg_children (v : V) : Set V :=
  { w | Nonempty (v ⟶ w) }

/-- A vertex has a directed cycle through itself: some outgoing edge leads to a
    path that returns to v (positive length). -/
def HasSelfCycle (v : V) : Prop :=
  ∃ (w : V) (_ : Nonempty (v ⟶ w)), Nonempty (Quiver.Path w v)

/-- A vertex is acyclic if it has no directed cycle through itself. -/
def IsAcyclic (v : V) : Prop :=
  ¬ HasSelfCycle v

/-- A pure self-loop vertex: has a self-edge, and every outgoing edge goes to itself. -/
def IsPureSelfLoop (v : V) : Prop :=
  Nonempty (v ⟶ v) ∧ ∀ w : V, Nonempty (v ⟶ w) → w = v

/-- For a pure self-loop vertex, the apg_children set is the singleton {v}. -/
theorem pureSelfLoop_children_eq_singleton (v : V) (hv : IsPureSelfLoop v) :
    apg_children v = {v} := by
  ext w
  simp only [apg_children, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨e⟩; exact hv.2 w ⟨e⟩
  · intro hw; rw [hw]; exact hv.1

end APGBasics

/-! ## § II. Decoration Universe Typeclass -/

/-- A decoration universe: a type with ValuationStructure and a collect operation.

    ValuationStructure provides scale, val, and the key axiom val_scale — which
    is what closes both the k=1 and k>1 SCC cases. collect assembles a parent
    vertex's value from the set of its children's values.

    Key constraints:
    - collect_singleton: collect {x} = scale x (links collect to the valuation structure)

    ZFSet is NOT a valid instance: Foundation forbids x ∈ x, which any cyclic APG requires.
    OntologicalStates (ZeroParadox/Settheory/OntBridge.lean) has AbstractSelfApp but not ValuationStructure —
    decoration of cyclic APGs specifically requires val_scale for the k>1 argument. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's ZFSet (the only set-theory formalization) uses Foundation — x ∈ x is forbidden, making it invalid as a decoration target for any APG with a self-loop. DecorationUniverse is an abstract type with ValuationStructure + a collect operation and two axioms (collect_singleton, collect_val_ge), providing the structure the decoration-uniqueness proof consumes, without importing ZFSet or any axiomatic set theory. ⚠ NOT axiom-free: DecorationUniverse and decoration_unique each measure [propext, Classical.choice, Quot.sound], inherited from the required [ValuationStructure U] — the route is the ℕ∞ numeral in val_scale, pinned by the _VSlit/_VScast pair in ZeroParadox/Valuation/Scale.lean. ⚠ "Minimum" is unproved: the NO-GO gauge below shows this class is inhabited over EVERY ValuationStructure carrier.
class DecorationUniverse (U : Type*) [ZPSemilattice U] [ValuationStructure U] where
  /-- A map `Set U → U`. ⚠ The two axioms below pin only the SINGLETON case and a lower bound; they
      do not require it to assemble a parent's value from its children's. -/
  collect : Set U → U
  /-- On a singleton input, collect = scale (the one-step operation from ValuationStructure). -/
  collect_singleton : ∀ x : U, collect {x} = ValuationStructure.scale x
  /-- Valuation lower bound: collecting any non-empty set increases val by ≥ 1.
      Each set-membership level adds depth — collect strictly increases valuation.
      Independent axiom: not derivable from collect_singleton alone. -/
  collect_val_ge : ∀ (S : Set U) (x : U), x ∈ S →
      ValuationStructure.val (collect S) ≥ ValuationStructure.val x + 1

/-! ### NO-GO gauge — `DecorationUniverse` is inhabited over EVERY `ValuationStructure` carrier.

Witness built and elaborated 2026-08-08, **classically** (the `dite` needs `Decidable (∃ x, S = {x})`):
`collect S := if h : ∃ x, S = {x} then scale h.choose else bot`, so the class constrains nothing
beyond the `ValuationStructure` it already assumes.
**Only the non-singleton half is free**, where `val bot` is top and dominates the bound. The singleton
branch of `collect_val_ge` needs `val_scale` (plus `scale_bot` when `x = bot`), and
`collect_singleton` needs `Set.singleton_eq_singleton_iff`.
**Not a carrier-level defect** — every use site takes it as a hypothesis carrying data. It does mean
`[DecorationUniverse U]` alone licenses no conclusion. -/

/-! ## § III. val_iterate — The Key Lemma

    For any x ≠ ⊥ and k : ℕ, applying scale k times increases the valuation by k.
    This is the iterated version of val_scale and is what makes ALL k-cycle cases
    reduce to the same impossibility argument: a fixed-point equation would require
    val x = val x + k, which is impossible for finite val. -/

section ValIterate

variable {U : Type*} [ZPSemilattice U] [ValuationStructure U]

/-- Applying scale k times to x ≠ ⊥ strictly increases val by k.
    Proof: induction on k. Base: scale^0 x = x (trivial). Step: scale^(n+1) x = scale(scale^n x).
    Induction hypothesis gives val(scale^n x) = val x + n; then val_scale applies
    (scale^n x ≠ ⊥, since val(scale^n x) = val x + n is finite). -/
theorem val_iterate (x : U) (hx : x ≠ bot) :
    ∀ (k : ℕ), ValuationStructure.val (ValuationStructure.scale^[k] x) =
    ValuationStructure.val x + k := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp]
    -- Establish scale^[n] x ≠ ⊥ using the IH and finiteness of val x
    have hne : ValuationStructure.scale^[n] x ≠ bot := by
      intro heq
      -- IH gives val(scale^[n] x) = val x + n; but scale^[n] x = ⊥ gives val = ⊤
      have hval_inf : ValuationStructure.val (ValuationStructure.scale^[n] x) = ⊤ :=
        heq ▸ ValuationStructure.val_bot
      rw [ih] at hval_inf
      -- Now hval_inf : val x + n = ⊤, but val x is finite (x ≠ ⊥)
      have hfin := val_finite_of_ne_bot x hx
      rcases hv : ValuationStructure.val x with _ | m
      · exact hfin hv
      · rw [hv] at hval_inf
        norm_cast at hval_inf
    rw [ValuationStructure.val_scale _ hne, ih]
    push_cast
    ring

end ValIterate

/-! ## § IV. scale_iterate_unique_fp — k-Cycle Case Resolved -/

section ScaleIterate

variable {U : Type*} [ZPSemilattice U] [ValuationStructure U]

/-- For any k ≥ 1: if scale^k(x) = x then x = ⊥.
    Proof: if x ≠ ⊥, then val(scale^k x) = val x + k > val x (by val_iterate).
    But scale^k x = x implies val(scale^k x) = val x — contradiction.
    This resolves ALL k-cycle cases in APG decoration uniqueness:
    composing k decoration equations around a k-cycle gives d(v) = scale^k(d(v)),
    and this theorem immediately forces d(v) = ⊥. -/
theorem scale_iterate_unique_fp (k : ℕ) (hk : 0 < k) (x : U)
    (hfp : ValuationStructure.scale^[k] x = x) : x = bot := by
  by_contra hx
  -- val x is finite (x ≠ ⊥)
  have hfin := val_finite_of_ne_bot x hx
  -- val(scale^[k] x) = val x + k (by val_iterate)
  have hval := val_iterate x hx k
  -- But scale^[k] x = x, so val(scale^[k] x) = val x
  rw [hfp] at hval
  -- hval : val x = val x + k
  -- This is impossible for finite val and k ≥ 1
  rcases hv : ValuationStructure.val x with _ | m
  · exact hfin hv
  · rw [hv] at hval
    -- some m = some m + ↑k — impossible for k ≥ 1; normalize then cast down to ℕ
    change (↑m : ℕ∞) = (↑m : ℕ∞) + (↑k : ℕ∞) at hval
    norm_cast at hval
    omega

/-- Equivalent formulation: scale^k has ⊥ as its only periodic point. -/
theorem scale_no_nontrivial_period (k : ℕ) (hk : 0 < k) :
    ∀ x : U, ValuationStructure.scale^[k] x = x → x = bot :=
  fun x hfp => scale_iterate_unique_fp k hk x hfp

end ScaleIterate

/-! ## § V. Decoration Predicate -/

/-- A valid decoration of a graph: a vertex labeling d : V → U satisfying the
    AFA decoration equation at every vertex: d(v) = collect over d's image of v's apg_children. -/
def IsDecoration {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d : V → U) : Prop :=
  ∀ v : V, d v = DecorationUniverse.collect (d '' apg_children v)

/-! ## § VI. Self-Loop Uniqueness -/

/-- Any valid decoration assigns ⊥ to any pure self-loop vertex.
    Proof: apg_children v = {v}, so d(v) = collect{d(v)} = scale(d(v)).
    scale(d v) = d v makes d v a fixed point of scale, so scale_unique_fp gives d v = ⊥. -/
theorem pureSelfLoop_decoration_eq_bot
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d : V → U) (hd : IsDecoration d) (v : V) (hv : IsPureSelfLoop v) :
    d v = bot := by
  have hchildren : apg_children v = {v} := pureSelfLoop_children_eq_singleton v hv
  have himage : d '' apg_children v = {d v} := by rw [hchildren, Set.image_singleton]
  have hcollect : DecorationUniverse.collect (d '' apg_children v) =
      ValuationStructure.scale (d v) := by
    rw [himage]; exact DecorationUniverse.collect_singleton (d v)
  -- d v = scale(d v), so d v is a fixed point of scale
  have hfp : ValuationStructure.scale (d v) = d v := ((hd v).trans hcollect).symm
  exact scale_unique_fp (d v) hfp

/-- Any two valid decorations agree on pure self-loop vertices. -/
theorem pureSelfLoop_decoration_unique
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂)
    (v : V) (hv : IsPureSelfLoop v) :
    d₁ v = d₂ v := by
  rw [pureSelfLoop_decoration_eq_bot d₁ hd₁ v hv,
      pureSelfLoop_decoration_eq_bot d₂ hd₂ v hv]

/-! ## § VII. k-Cycle Node Uniqueness -/

/-- If a valid decoration satisfies d(v) = scale^k(d(v)) for some k ≥ 1, then d(v) = ⊥.
    This is the SCC case: composing decoration equations around a k-cycle in the APG
    gives exactly this hypothesis. The proof is an immediate corollary of
    scale_iterate_unique_fp — no additional structure needed.

    The valuation argument in full:
      d(v) = scale^k(d(v))                     [from composing k decoration equations]
      val(scale^k(d(v))) = val(d(v)) + k        [val_iterate, if d(v) ≠ ⊥]
      val(d(v)) + k = val(d(v))                 [from d(v) = scale^k(d(v))]
      impossible for finite val                  [k ≥ 1]
      therefore d(v) = ⊥ -/
theorem kCycle_node_eq_bot
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d : V → U) (_hd : IsDecoration d) (v : V) (k : ℕ) (hk : 0 < k)
    (hcycle : ValuationStructure.scale^[k] (d v) = d v) :
    d v = bot :=
  scale_iterate_unique_fp k hk (d v) hcycle

/-- Any two valid decorations agree on all k-cycle nodes. -/
theorem kCycle_node_unique
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂)
    (v : V) (k : ℕ) (hk : 0 < k)
    (hcycle₁ : ValuationStructure.scale^[k] (d₁ v) = d₁ v)
    (hcycle₂ : ValuationStructure.scale^[k] (d₂ v) = d₂ v) :
    d₁ v = d₂ v := by
  rw [kCycle_node_eq_bot d₁ hd₁ v k hk hcycle₁,
      kCycle_node_eq_bot d₂ hd₂ v k hk hcycle₂]

/-! ## § VII'. Cyclic Vertex Uniqueness

    Any vertex with a directed cycle through itself must receive ⊥ under any valid
    decoration. The argument generalizes § VII to arbitrary cycle lengths without
    needing the explicit scale^k formulation:

    - path_val_chain: for any path u ↝ v of length n, val(d u) ≥ val(d v) + n
      (chain collect_val_ge along each edge)
    - cyclic_decoration_eq_bot: if v ⟶ w ↝ v then val(d v) ≥ val(d v) + (cycle_len + 1),
      impossible for finite val, so d v = ⊥ -/

/-- Valuation chain along a path: for any path p : u ↝ v, decoration at u has valuation
    ≥ decoration at v plus the path length. Each edge step uses collect_val_ge:
    if b ⟶ c then d(b) = collect(d '' apg_children b) and d(c) ∈ d '' apg_children b. -/
private theorem path_val_chain
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d : V → U) (hd : IsDecoration d)
    {u v : V} (p : Quiver.Path u v) :
    ValuationStructure.val (d u) ≥ ValuationStructure.val (d v) + (p.length : ℕ∞) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    -- rename_i names inaccessibles in introduction order (first = intermediate, second = endpoint)
    rename_i b c
    -- p : Path u b, e : b ⟶ c, ih : val(d u) ≥ val(d b) + ↑p.length
    simp only [Quiver.Path.length_cons, Nat.cast_add, Nat.cast_one]
    -- goal : val(d u) ≥ val(d c) + (↑p.length + 1)
    have hc_child : c ∈ apg_children b := ⟨e⟩
    have hc_img : d c ∈ d '' apg_children b := Set.mem_image_of_mem d hc_child
    have hstep : ValuationStructure.val (d b) ≥ ValuationStructure.val (d c) + 1 := by
      rw [hd b]
      exact DecorationUniverse.collect_val_ge _ (d c) hc_img
    calc ValuationStructure.val (d u)
        ≥ ValuationStructure.val (d b) + (p.length : ℕ∞) := ih
      _ ≥ (ValuationStructure.val (d c) + 1) + (p.length : ℕ∞) :=
          add_le_add hstep (le_refl _)
      _ = ValuationStructure.val (d c) + ((p.length : ℕ∞) + 1) := by
          rw [add_assoc, add_comm (1 : ℕ∞) (p.length : ℕ∞)]

/-- Any valid decoration assigns ⊥ to any vertex with a directed cycle through itself.
    Proof: chain collect_val_ge along the cycle to derive val(d v) ≥ val(d v) + (cycle_len + 1),
    impossible for finite val. -/
theorem cyclic_decoration_eq_bot
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d : V → U) (hd : IsDecoration d) (v : V) (hcyc : HasSelfCycle v) :
    d v = bot := by
  obtain ⟨w, ⟨e⟩, ⟨p⟩⟩ := hcyc
  by_contra hdv
  have hfin := val_finite_of_ne_bot (d v) hdv
  -- val(d v) ≥ val(d w) + 1: w ∈ apg_children v, d v = collect, collect_val_ge
  have hw_child : w ∈ apg_children v := ⟨e⟩
  have hdw_mem : d w ∈ d '' apg_children v := Set.mem_image_of_mem d hw_child
  have hge1 : ValuationStructure.val (d v) ≥ ValuationStructure.val (d w) + 1 := by
    have hcoll := DecorationUniverse.collect_val_ge (d '' apg_children v) (d w) hdw_mem
    rwa [← hd v] at hcoll
  -- val(d w) ≥ val(d v) + p.length: path from w to v
  have hge2 : ValuationStructure.val (d w) ≥ ValuationStructure.val (d v) + p.length :=
    path_val_chain d hd p
  -- rcases on ℕ∞ = WithTop ℕ gives `some m` form; use `change` to normalize to coercion form
  rcases hval : ValuationStructure.val (d v) with _ | m
  · exact hfin hval
  · rcases hvalw : ValuationStructure.val (d w) with _ | k
    · -- val(d w) = none = ⊤; none + 1 = ⊤ definitionally, so change normalizes directly
      rw [hval, hvalw] at hge1
      change (m : ℕ∞) ≥ ⊤ at hge1
      exact absurd hge1 (not_le.mpr (WithTop.coe_lt_top m))
    · -- Both finite; some m = ↑m definitionally, so change normalizes to cast form
      rw [hval, hvalw] at hge1 hge2
      change (m : ℕ∞) ≥ (k : ℕ∞) + 1 at hge1
      change (k : ℕ∞) ≥ (m : ℕ∞) + p.length at hge2
      have h1 : m ≥ k + 1 := by exact_mod_cast hge1
      have h2 : k ≥ m + p.length := by exact_mod_cast hge2
      omega

/-! ## § VIII. Acyclic Vertex Uniqueness (superseded by § IX)

    For acyclic vertices, the induction step is clear:
      - IH: d₁ and d₂ agree on all apg_children of v
      - d₁ '' apg_children v = d₂ '' apg_children v    [image equality from IH]
      - collect(d₁ '' apg_children v) = collect(d₂ '' apg_children v)  [congrArg collect]
      - d₁ v = collect(d₁ '' apg_children v) = collect(d₂ '' apg_children v) = d₂ v

    The local step `acyclic_induction_step` below is proved. The full acyclic-vertex route
    would then need a well-founded induction principle (for [Fintype V], the apg_children
    relation on acyclic vertices has no infinite descending chains). That route was not needed:
    § IX (`decoration_unique`) proves global uniqueness directly by strong induction on
    reachable-set cardinality, handling acyclic and cyclic vertices in one argument. The
    commented-out `acyclic_decoration_unique` below records the abandoned approach. -/

/-- Local induction step: if d₁ and d₂ agree on all apg_children of v, they agree on v. -/
theorem acyclic_induction_step
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂)
    (v : V) (ih : ∀ w ∈ apg_children v, d₁ w = d₂ w) :
    d₁ v = d₂ v := by
  have himage_eq : d₁ '' apg_children v = d₂ '' apg_children v := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, (ih w hw).symm⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, ih w hw⟩
  rw [hd₁ v, hd₂ v, himage_eq]

-- /-- Two decorations agree on any acyclic vertex. -/
-- theorem acyclic_decoration_unique
--     {V : Type*} [Quiver V] [Fintype V]
--     {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
--     (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂)
--     (v : V) (hv : IsAcyclic v) :
--     d₁ v = d₂ v := by
--   -- Not load-bearing: decoration_unique proves global uniqueness directly via
--   -- strong induction on reach cardinality, handling acyclic vertices inline.
--   -- Proof when needed: same strong-induction argument, restricted to acyclic case.
--   sorry

/-! ## § IX. Global Decoration Uniqueness

    Proved directly by strong induction on |{w | Path u w}| (reachable set cardinality).
    No SCC decomposition needed — the valuation argument handles cyclic vertices directly:

    - Cyclic u: d₁ u = ⊥ = d₂ u by cyclic_decoration_eq_bot
    - Acyclic u: for each child w, reach w ⊊ reach u (since v ∉ reach w by acyclicity),
      so IH gives d₁ w = d₂ w for all apg_children, and acyclic_induction_step closes the goal.

    Requires [Fintype V] to bound the reachable set cardinality. -/

/-! ### PRIOR ART — the uniqueness clause of a RECURSIVE COALGEBRA, for ONE SHAPE of algebra.

A coalgebra is **recursive** when *every* algebra admits a unique coalgebra-to-algebra morphism
(Adámek-Milius-Moss 2020, arXiv:1910.09401v2, Def 3.2 p. 11, crediting Osius for the definition).
`decoration_unique` gives that clause for algebras of the `DecorationUniverse.collect` shape, not
for every algebra, and existence not at all. `ZeroParadox/Category/WellFoundedCoalgebra.lean` has
the well-foundedness side. **The delta:** the standard route to such uniqueness is well-foundedness
(Taylor's General Recursion Theorem, AMM Thm 7.2 p. 27), unavailable here since these quivers may
carry cycles. It closes on two branches instead — cyclic vertices to ⊥ (`cyclic_decoration_eq_bot`),
acyclic ones by strict-subset descent on the reachable set, which is what `[Fintype V]` is for. -/

-- `[Fintype V]` is not used in the *type* but is essential to the *proof*: it bounds the
-- reachable-set cardinality so the strict-subset descent (`Set.ncard_lt_ncard`) terminates.
set_option linter.unusedFintypeInType false in
/-- Global decoration uniqueness: any two valid decorations of a finite APG are equal. -/
theorem decoration_unique
    {V : Type*} [Quiver V] [Fintype V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (_G : APG V) (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) :
    d₁ = d₂ := by
  funext v
  suffices key : ∀ n : ℕ, ∀ u : V,
      ({x : V | Nonempty (Quiver.Path u x)}).ncard ≤ n → d₁ u = d₂ u from
    key _ v le_rfl
  intro n
  induction n with
  | zero =>
    intro u hcard
    -- u reaches itself via nil, so the reachable set is nonempty, ncard ≥ 1 > 0
    have hpos : 0 < ({x : V | Nonempty (Quiver.Path u x)}).ncard := by
      rw [Set.ncard_pos]; exact ⟨u, ⟨Quiver.Path.nil⟩⟩
    omega
  | succ n ih =>
    intro u hcard
    by_cases hcyc : HasSelfCycle u
    · rw [cyclic_decoration_eq_bot d₁ hd₁ u hcyc, cyclic_decoration_eq_bot d₂ hd₂ u hcyc]
    · -- u is acyclic: use acyclic_induction_step (no IsAcyclic param needed)
      apply acyclic_induction_step d₁ d₂ hd₁ hd₂ u
      intro w hw
      -- unfold apg_children membership to get hw : Nonempty (u ⟶ w)
      simp only [apg_children, Set.mem_setOf_eq] at hw
      apply ih w
      -- reach w ⊂ reach u because: ⊆ via edge u→w, and u ∈ reach u but u ∉ reach w (acyclicity)
      have hreach_mono : {x : V | Nonempty (Quiver.Path w x)} ⊆
          {x : V | Nonempty (Quiver.Path u x)} :=
        fun _ ⟨p⟩ => ⟨(Quiver.Path.nil.cons hw.some).comp p⟩
      have hv_in : u ∈ {x : V | Nonempty (Quiver.Path u x)} := ⟨Quiver.Path.nil⟩
      have hv_not : u ∉ {x : V | Nonempty (Quiver.Path w x)} :=
        fun ⟨p⟩ => hcyc ⟨w, hw, ⟨p⟩⟩
      have hstrict : {x : V | Nonempty (Quiver.Path w x)} ⊂
          {x : V | Nonempty (Quiver.Path u x)} := by
        constructor
        · exact hreach_mono
        · intro hsub; exact hv_not (hsub hv_in)
      have hlt := Set.ncard_lt_ncard hstrict
      omega

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#check @val_iterate
#check @scale_iterate_unique_fp
#check @scale_no_nontrivial_period
#check @pureSelfLoop_decoration_eq_bot
#check @kCycle_node_eq_bot
#check @acyclic_induction_step
#check @decoration_unique

#print axioms val_iterate
#print axioms scale_iterate_unique_fp
#print axioms pureSelfLoop_decoration_eq_bot
#print axioms kCycle_node_eq_bot
#print axioms acyclic_induction_step
#print axioms cyclic_decoration_eq_bot
#print axioms decoration_unique

end PurityCheck
