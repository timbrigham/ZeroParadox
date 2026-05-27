import ZeroParadox.ZPJ_SelfApp
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZPJ — Accessible Pointed Graphs and AFA Decoration Uniqueness (Exploratory)

## Engineer's Take

Every APG (accessible pointed graph) in AFA set theory has a unique decoration:
a labeling of vertices with sets such that each vertex's label is exactly the
collection of its children's labels. The Quine atom (self-loop vertex) gets
labeled with ⊥ because ⊥ is the only element that can equal the set containing
itself. For acyclic vertices, the label is determined bottom-up by structural
induction. For k-cycles (k > 1), the argument is harder: the composed operator
must also have ⊥ as its only fixed point, which requires additional structure
beyond what AbstractSelfApp currently provides.

## The conjecture

AFA universality: for any APG, there exists a unique decoration in any
DecorationUniverse (an abstract AbstractSelfApp type with a collect operation).
This would derive AFA's decoration uniqueness clause from ZP structure rather
than asserting it as an independent axiom.

## Architecture note: why not ZFSet

Mathlib's ZFSet satisfies the Axiom of Foundation (ZFSet.regularity), which
forbids x ∈ x for any x. For a self-loop vertex v → v, the AFA decoration rule
requires d(v) = {d(v)}, hence d(v) ∈ d(v) — prohibited by Foundation. ZFSet
cannot serve as the decoration target for cyclic APGs. See:
  .claude-local/notes/afa_apg_zfset_correction_2026-05-27.md

The correct target is an abstract DecorationUniverse — a type carrying
AbstractSelfApp structure plus a collect operation that assembles a parent's
value from its children's values.

## Structure

- § I   APG definition (Quiver + root + accessibility)
- § II  Decoration universe typeclass (abstract alternative to ZFSet)
- § III Decoration predicate
- § IV  Self-loop uniqueness (PROVED: AbstractSelfApp.unique_fp handles k=1)
- § V   Acyclic vertex uniqueness (sorry: structural induction pending)
- § VI  Global decoration uniqueness conjecture (sorry: k>1 SCC case open)

## What remains open

For a k-cycle (k > 1), d(v₁) = selfApp^k(d(v₁)). AbstractSelfApp guarantees
bot is the only fixed point of selfApp¹, but not of selfApp^k. A 2-cycle in
selfApp — selfApp(x) = y and selfApp(y) = x with x ≠ y — is not ruled out by
current axioms. Additional algebraic structure (monotonicity? injectivity?) is
needed to close the k > 1 case.

## Dependencies

- ZPJ_SelfApp.lean: AbstractSelfApp typeclass and unique_fp
- Mathlib.Combinatorics.Quiver.Path: directed graph paths
- Mathlib.Combinatorics.Quiver.ConnectedComponent: SCC infrastructure (Step 3)
-/

namespace ZeroParadox.APG

open ZeroParadox.SelfApp ZeroParadox.ZPA ZPSemilattice

/-! ## § I. APG Definition -/

/-- An Accessible Pointed Graph: a Quiver with a distinguished root vertex
    from which every vertex is reachable via directed paths. -/
structure APG (V : Type*) [Quiver V] where
  /-- Distinguished root vertex. -/
  root : V
  /-- Every vertex is reachable from the root via directed paths. -/
  accessible : ∀ v : V, Nonempty (Quiver.Path root v)

section APGBasics

variable {V : Type*} [Quiver V]

/-- Immediate successors of a vertex: all w with an edge v ⟶ w. -/
def children (v : V) : Set V :=
  { w | Nonempty (v ⟶ w) }

/-- A vertex has a directed cycle through itself: there is a length-≥-1 path
    from v back to v (i.e., some outgoing edge whose target has a return path). -/
def HasSelfCycle (v : V) : Prop :=
  ∃ (w : V) (_ : Nonempty (v ⟶ w)), Nonempty (Quiver.Path w v)

/-- A vertex is acyclic if it has no directed cycle through itself. -/
def IsAcyclic (v : V) : Prop :=
  ¬ HasSelfCycle v

/-- A pure self-loop vertex: it has a self-edge, and all outgoing edges go to itself. -/
def IsPureSelfLoop (v : V) : Prop :=
  Nonempty (v ⟶ v) ∧ ∀ w : V, Nonempty (v ⟶ w) → w = v

/-- For a pure self-loop vertex, the children set is the singleton {v}. -/
theorem pureSelfLoop_children_eq_singleton (v : V) (hv : IsPureSelfLoop v) :
    children v = {v} := by
  ext w
  simp only [children, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ⟨e⟩; exact hv.2 w ⟨e⟩
  · intro hw; rw [hw]; exact hv.1

end APGBasics

/-! ## § II. Decoration Universe Typeclass -/

/-- A decoration universe: an AbstractSelfApp type with a collect operation that
    assembles a parent vertex's value from the set of its children's values.

    The key constraint is collect_singleton: collect {x} = selfApp x. This ensures
    that a pure self-loop vertex v (with children v = {v}) satisfies the fixed-point
    equation d(v) = selfApp(d(v)), which AbstractSelfApp.unique_fp then resolves to bot.

    Note: This is intentionally abstract — ZFSet is NOT a valid instance due to
    ZFSet.mem_irrefl (Foundation). Any AbstractSelfApp instance (e.g. OntologicalStates
    via ZPJ_OntBridge) can in principle be extended to a DecorationUniverse. -/
class DecorationUniverse (U : Type*) [ZPSemilattice U] [AbstractSelfApp U] where
  /-- Assembles a parent's value from the set of its children's values. -/
  collect : Set U → U
  /-- On a singleton input, collect reduces to selfApp.
      This is the key condition linking decoration to the AbstractSelfApp structure. -/
  collect_singleton : ∀ x : U, collect {x} = AbstractSelfApp.selfApp x

/-! ## § III. Decoration Predicate -/

/-- A valid decoration of a graph: a vertex labeling d : V → U satisfying the
    AFA decoration equation at every vertex: d(v) = collect of d's image over
    v's children. -/
def IsDecoration {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [AbstractSelfApp U] [DecorationUniverse U]
    (d : V → U) : Prop :=
  ∀ v : V, d v = DecorationUniverse.collect (d '' children v)

/-! ## § IV. Self-Loop Uniqueness -/

/-- Any valid decoration assigns bot to any pure self-loop vertex.

    Proof sketch:
      d(v) = collect (d '' children v)   [decoration equation, hd v]
           = collect (d '' {v})           [children v = {v} by IsPureSelfLoop]
           = collect {d v}               [image of singleton = Set.image_singleton]
           = selfApp (d v)               [collect_singleton]
      So d(v) = selfApp(d v), i.e. d v is a fixed point of selfApp.
      AbstractSelfApp.unique_fp: selfApp x = x → x = bot.
      Therefore d v = bot.

    Note: the proof avoids rw on hd v to prevent replacement of d v inside selfApp(d v). -/
theorem pureSelfLoop_decoration_eq_bot
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [AbstractSelfApp U] [DecorationUniverse U]
    (d : V → U) (hd : IsDecoration d) (v : V) (hv : IsPureSelfLoop v) :
    d v = bot := by
  have hchildren : children v = {v} := pureSelfLoop_children_eq_singleton v hv
  have himage : d '' children v = {d v} := by
    rw [hchildren, Set.image_singleton]
  have hcollect : DecorationUniverse.collect (d '' children v) =
      AbstractSelfApp.selfApp (d v) := by
    rw [himage]; exact DecorationUniverse.collect_singleton (d v)
  -- Build hfp via transitivity, not rw, to avoid replacing d v inside selfApp (d v).
  have hfp : d v = AbstractSelfApp.selfApp (d v) := (hd v).trans hcollect
  exact AbstractSelfApp.unique_fp (d v) hfp.symm

/-- Any two valid decorations agree on pure self-loop vertices (both give bot). -/
theorem pureSelfLoop_decoration_unique
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [AbstractSelfApp U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂)
    (v : V) (hv : IsPureSelfLoop v) :
    d₁ v = d₂ v := by
  rw [pureSelfLoop_decoration_eq_bot d₁ hd₁ v hv,
      pureSelfLoop_decoration_eq_bot d₂ hd₂ v hv]

/-! ## § V. Acyclic Vertex Uniqueness (sorry)

    For acyclic vertices, any two decorations agree. The proof should be by
    well-founded induction on the graph structure: the children of an acyclic
    vertex have strictly smaller "depth" from a leaf, so the inductive hypothesis
    applies to each child, and the decoration equation pins d(v).

    Pending: formalize the well-founded order on acyclic vertices and verify that
    the induction step goes through. Requires that collect is injective (or at
    least that equal children sets give equal collect values), which is not yet
    in DecorationUniverse. -/

/-- Two decorations agree on any acyclic vertex (pending: structural induction). -/
theorem acyclic_decoration_unique
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [AbstractSelfApp U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂)
    (v : V) (hv : IsAcyclic v) :
    d₁ v = d₂ v := by
  sorry

/-! ## § VI. Global Decoration Uniqueness Conjecture (sorry)

    AFA universality: any APG has at most one decoration in any DecorationUniverse.
    Combining:
      - § IV: pure self-loop vertices → both decorations give bot
      - § V:  acyclic vertices → induction gives equality
      - SCC case (k > 1): requires selfApp^k has bot as unique fixed point — OPEN

    The SCC case is the key gap. For k = 1 (self-loop), § IV handles it directly.
    For k > 1 (cycle v₁ → v₂ → ... → vₖ → v₁), d(v₁) = selfApp^k(d(v₁)).
    AbstractSelfApp.unique_fp handles k=1 but not k>1 without additional axioms. -/

/-- Global decoration uniqueness: any two valid decorations of G are equal. -/
theorem decoration_unique
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [AbstractSelfApp U] [DecorationUniverse U]
    (G : APG V) (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) :
    d₁ = d₂ := by
  sorry

end ZeroParadox.APG

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.APG

#check @pureSelfLoop_decoration_eq_bot
#check @pureSelfLoop_decoration_unique
#check @acyclic_decoration_unique
#check @decoration_unique

end PurityCheck
