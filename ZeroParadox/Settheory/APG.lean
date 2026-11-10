import ZeroParadox.Valuation.Scale
import ZeroParadox.Settheory.Model
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.Combinatorics.Quiver.Arborescence
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

It's the absorption and the pole that allow us to convert that endless descent into a single point.

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

/-! ⚠ Corrections to the header above, which `check_prose` freezes by content hash (2026-09-13):
`decoration_unique` consumes `collect_val_ge` and never `collect_singleton`, and it gives a
SUFFICIENT condition for uniqueness, not a characterization (no converse is proved). § IV settles
periodic points of `scale`, not an APG cycle — the cyclic case is `cyclic_decoration_eq_bot` (§ VII').
For "x ∈ x is forbidden" the named theorem is `ZFSet.mem_irrefl`, not `ZFSet.regularity`. -/

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
-- [ZP-CUSTOM] extends: Mathlib.Combinatorics.Quiver.Basic | reason: Mathlib's Quiver is a bare directed graph (objects + edges) with no distinguished root. APG adds root : V and the accessibility proof (every vertex reachable from root), which is Mathlib's separate class Quiver.RootedConnected root (Mathlib/Combinatorics/Quiver/Arborescence.lean; the two Quiver.RootedConnected examples below the structure, after its non-member example), matching Aczel's definition of Accessible Pointed Graph (1988 p. 4). ⚠ These fields are NOT load-bearing for anything proved in this file, and no claim of necessity should be made for them in either direction: decoration_unique binds the structure as `_G` and never uses it, so what is actually proved holds for EVERY finite quiver, accessible or not — structurally Aczel's own AFA generality (p. 6). The second Quiver.RootedConnected example constructs an APG from any root carrying Quiver.RootedConnected.
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

-- Statement: an `APG` on `V` gives `Quiver.RootedConnected` at its root, and a root with
-- `Quiver.RootedConnected` gives an `APG`, so the `accessible` field is that Mathlib class.
example {V : Type*} [Quiver V] (G : APG V) : Quiver.RootedConnected G.root := ⟨G.accessible⟩
example {V : Type*} [Quiver V] (r : V) [h : Quiver.RootedConnected r] : APG V := ⟨r, h.nonempty_path⟩

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

    ValuationStructure provides scale and val with laws scale_bot, val_bot, val_unique, val_scale. ⚠ The cyclic case
    `decoration_unique` uses (`cyclic_decoration_eq_bot`) consumes `val_unique` and
    `collect_val_ge`, not `val_scale`; `val_scale` enters only through the scale^k lemmas
    of § III–§ VII. collect assembles a parent vertex's value from the set of its children's values.

    Key constraints:
    - collect_singleton: collect {x} = scale x (links collect to the valuation structure)

    ZFSet is NOT a valid instance: Foundation forbids x ∈ x, which any cyclic APG requires.
    OntologicalStates (ZeroParadox/Settheory/OntBridge.lean) has AbstractSelfApp but not ValuationStructure,
    which this class takes as a binder. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's ZFSet carries Foundation (ZFSet.mem_wf) — x ∈ x is forbidden, making it invalid as a decoration target for any APG with a self-loop. DecorationUniverse is an abstract type with ValuationStructure + a collect operation and two axioms (collect_singleton, collect_val_ge), providing the structure the decoration-uniqueness proof consumes, without importing ZFSet or any axiomatic set theory. ⚠ The class and its [ValuationStructure U] binder measure no axioms (this file's PurityCheck; ZeroParadox/Valuation/Scale.lean's). decoration_unique measures [propext, Classical.choice, Quot.sound], and under the instances the pinned Mathlib supplies its STATEMENT carries them through the [Fintype V] binder: Fintype measures the three (PurityCheck below), and in statement controls measured 2026-11-07 the full statement reports them, the same statement with [Finite V] in place of [Fintype V] reports none, and forall {U} [ZPSemilattice U] [ValuationStructure U], True reports none. So no proof of decoration_unique as stated can drop them, and the bin is relative to those instances (ZeroParadox/Category/ChoiceCannotBe.lean § III, STATEMENT-CARRIED IS INSTANCE-RELATIVE). Its proof term also names Nonempty.some, Classical.propDecidable (the by_cases on HasSelfCycle u), Set.ncard_pos, Set.ncard_lt_ncard and cyclic_decoration_eq_bot, each measuring Classical.choice (2026-11-07). The [Finite V] restatement has a choice-free proof, decoration_unique_finite, from decoration_unique_of_val, which binds no finiteness at all (§ IX; footprints in PurityCheck below). Provenance and necessity are independent axes (ZeroParadox/AxiomProfile.lean § 0). ⚠ "Minimum" is unproved: the NO-GO gauge below shows this class is inhabited over EVERY ValuationStructure carrier.
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

The `example` below emits it; a concrete one on ℕ∞, with a decoration, follows `IsDecoration` (§ V). So `[DecorationUniverse U]` alone licenses no conclusion about `U`
beyond the `ValuationStructure` it already assumes, classically; every use site takes it as a hypothesis carrying data. -/

-- Statement: every `ValuationStructure` carrier has a `DecorationUniverse`, classically:
-- `collect S := if h : ∃ x, S = {x} then scale h.choose else bot`.
example {U : Type*} [ZPSemilattice U] [ValuationStructure U] : Nonempty (DecorationUniverse U) := by
  classical
  refine ⟨{ collect := fun S => if h : ∃ x, S = {x} then ValuationStructure.scale h.choose else bot,
            collect_singleton := fun x => ?_, collect_val_ge := fun S x hx => ?_ }⟩
  · have h : ∃ y, ({x} : Set U) = {y} := ⟨x, rfl⟩
    have hx : h.choose = x := (Set.singleton_eq_singleton_iff.mp h.choose_spec).symm
    rw [dite_eq_left h, hx]
  · split_ifs with h
    · have hxe : x = h.choose := by rw [h.choose_spec] at hx; exact hx
      rw [← hxe]
      by_cases hb : x = bot
      · subst hb
        rw [ValuationStructure.scale_bot, ValuationStructure.val_bot]
        exact le_top
      · exact le_of_eq (ValuationStructure.val_scale x hb).symm
    · rw [ValuationStructure.val_bot]
      exact le_top

/-! ## § III. val_iterate — The Key Lemma

    For any x ≠ ⊥ and k : ℕ, applying scale k times increases the valuation by k.
    This is the iterated version of val_scale, consumed by `scale_iterate_unique_fp` (§ IV):
    a fixed point of scale^k would require val x = val x + k, impossible for finite val.
    ⚠ Not the APG cyclic case — `cyclic_decoration_eq_bot` (§ VII') never forms scale^[k]. -/

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

/-! ## § IV. scale_iterate_unique_fp — Periodic Points of scale -/

section ScaleIterate

variable {U : Type*} [ZPSemilattice U] [ValuationStructure U]

/-- For any k ≥ 1: if scale^k(x) = x then x = ⊥.
    Proof: if x ≠ ⊥, then val(scale^k x) = val x + k > val x (by val_iterate).
    But scale^k x = x implies val(scale^k x) = val x — contradiction.
    ⚠ It settles an APG cycle only where d(v) = scale^k(d(v)) is already in hand. The class laws
    relate `collect` to `scale` only through `collect_singleton`, so composing decoration equations
    yields that when each child image on the cycle is a singleton (e.g. one child per vertex). The
    general cyclic case is `cyclic_decoration_eq_bot` (§ VII'), which bounds with inequalities. -/
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

-- Statement: on ℕ∞ (join `min`, ⊥ of ℕ∞'s ZP structure is `⊤`, scale `+ 1`, val `id`;
-- `ZeroParadox/Settheory/Model.lean`) `collect S := sSup S + 1`, `sSup` in ℕ∞'s own order, is a
-- `DecorationUniverse`, and under it the quiver on `Bool` with the one edge `true ⟶ false` has the
-- decoration `true ↦ 2`, `false ↦ 1`.
-- Reading: here the decoration is the well-founded rank plus one (Mathlib's `Acc.rank_eq`,
-- `WellFounded.rank_eq`, `Mathlib/SetTheory/Ordinal/Rank.lean`).
example : ∃ D : DecorationUniverse ℕ∞, ∃ d : Bool → ℕ∞,
    @IsDecoration Bool ⟨fun a b => PLift (a = true ∧ b = false)⟩ ℕ∞ _ _ D d ∧
      d true = 2 ∧ d false = 1 := by
  let Q : Quiver Bool := ⟨fun a b => PLift (a = true ∧ b = false)⟩
  have hc : ∀ a b : Bool, b ∈ @apg_children Bool Q a ↔ (a = true ∧ b = false) :=
    fun a b => ⟨fun ⟨e⟩ => e.down, fun h => ⟨⟨h⟩⟩⟩
  refine ⟨⟨fun S => sSup S + 1, fun x => ?_, fun S x hx => ?_⟩, fun b => if b then 2 else 1, ?_, rfl, rfl⟩
  · show sSup {x} + 1 = x + 1
    rw [sSup_singleton]
  · show x + 1 ≤ sSup S + 1
    exact add_le_add (le_sSup hx) le_rfl
  · intro v
    cases v
    · have he : @apg_children Bool Q false = (∅ : Set Bool) := Set.ext fun b => by rw [hc]; simp
      show (1 : ℕ∞) = sSup ((fun b : Bool => if b then (2 : ℕ∞) else 1) '' @apg_children Bool Q false) + 1
      rw [he, Set.image_empty, sSup_empty]
      simp
    · have he : @apg_children Bool Q true = ({false} : Set Bool) := Set.ext fun b => by
        rw [hc, Set.mem_singleton_iff]; simp
      show (2 : ℕ∞) = sSup ((fun b : Bool => if b then (2 : ℕ∞) else 1) '' @apg_children Bool Q true) + 1
      rw [he, Set.image_singleton, sSup_singleton]
      exact one_add_one_eq_two.symm

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
    ⚠ `hcycle` is TAKEN, not derived, and `_hd` is unused. Through `collect_singleton`, composing
    decoration equations produces it when each child image on the cycle is a singleton (e.g. one
    child per vertex); for an arbitrary cycle use `cyclic_decoration_eq_bot` (§ VII'). The proof is an immediate
    corollary of scale_iterate_unique_fp.

    The valuation argument in full:
      d(v) = scale^k(d(v))                     [hypothesis hcycle]
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

-- Statement: a cyclic vertex receives the order bottom ⊥ AND its valuation is ⊤ — both charts of
-- one vertex (finite period, infinite depth). One-way: nothing here fixes an acyclic vertex's value.
example {V : Type*} [Quiver V] {U : Type*} [ZPSemilattice U] [ValuationStructure U]
    [DecorationUniverse U] (d : V → U) (hd : IsDecoration d) (v : V) (hcyc : HasSelfCycle v) :
    d v = bot ∧ ValuationStructure.val (d v) = ⊤ := by
  have h := cyclic_decoration_eq_bot d hd v hcyc
  exact ⟨h, by rw [h]; exact ValuationStructure.val_bot⟩

/-- `Statement:` along a path `v ⟶* w`, a decoration sending `w` to ⊥ of `U` (valuation ⊤ of ℕ∞)
    sends `v` there too: ⊥ spreads backward to every ancestor.
    `Reading:` rank ∞ propagates upward (Pakhomov–Walsh, JSL 86 (2021), arXiv 1805.02095,
    Remark 5.1, with `∞ + 1 = ∞`); at graph level, every ancestor of a vertex on a cycle starts an
    infinite path, so lies outside "A∗ = Aω", "the set of all nodes from which no infinite paths
    starts" (Adámek-Milius-Moss 2020, arXiv:1910.09401v2, Example 6.10 p. 26). -/
theorem path_decoration_eq_bot
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d : V → U) (hd : IsDecoration d) {v w : V} (p : Quiver.Path v w) (hw : d w = bot) :
    d v = bot := by
  have h := path_val_chain d hd p
  rw [hw, ValuationStructure.val_bot, top_add] at h
  exact ValuationStructure.val_unique _ (top_le_iff.mp h)

-- Statement: so every vertex that reaches a cyclic vertex is decorated ⊥ of `U`.
example {V : Type*} [Quiver V] {U : Type*} [ZPSemilattice U] [ValuationStructure U]
    [DecorationUniverse U] (d : V → U) (hd : IsDecoration d) {v w : V} (p : Quiver.Path v w)
    (hc : HasSelfCycle w) : d v = bot :=
  path_decoration_eq_bot d hd p (cyclic_decoration_eq_bot d hd w hc)

/-! ### Absorption at ⊥ of `U`, and when the join identity is the absorber

Here `v : U → ℕ∞` and `c : Set U → U` are bare data. -/

/-- `Statement:` under `hc` and `hu` (bare data, no class), `v b = ⊤` and `c S = b` whenever `b ∈ S`. -/
theorem absorb_of_unique_top {U : Type*} (v : U → ℕ∞) (c : Set U → U)
    (hc : ∀ S x, x ∈ S → v (c S) ≥ v x + 1) (b : U) (hu : ∀ x, v x = ⊤ → x = b) :
    v b = ⊤ ∧ ∀ S, b ∈ S → c S = b := by
  have htop : v (c Set.univ) = ⊤ := by
    have h := hc Set.univ (c Set.univ) trivial
    rcases hv : v (c Set.univ) with _ | m
    · rfl
    · rw [hv] at h
      have h' : WithTop.LE (some (m + 1) : WithTop ℕ) (some m) := h
      cases h' with
      | coe_le_coe hle => exact absurd hle (Nat.not_succ_le_self m)
  have hb : v b = ⊤ := hu _ htop ▸ htop
  refine ⟨hb, fun S hS => hu _ ?_⟩
  have h := hc S b hS
  rw [hb] at h
  rcases hv : v (c S) with _ | m
  · rfl
  · rw [hv] at h
    have h' : WithTop.LE (none : WithTop ℕ) (some m) := h
    cases h'

-- Statement: absorption needs no join and no `val_bot`: a lower bound `v (c S) ≥ v x + 1` on members
-- and a unique `v`-⊤ point `b` force `v b = ⊤` and `c S = b` whenever `b ∈ S`.
-- Reading: a rank into On ∪ {∞} with `∞ + 1 = ∞` (Pakhomov–Walsh, Remark 5.1); the uniqueness of
-- the ∞ point is the corpus's own hypothesis.
example {U : Type*} (v : U → ℕ∞) (c : Set U → U) (hc : ∀ S x, x ∈ S → v (c S) ≥ v x + 1)
    (b : U) (hu : ∀ x, v x = ⊤ → x = b) : v b = ⊤ ∧ ∀ S, b ∈ S → c S = b :=
  absorb_of_unique_top v c hc b hu

/-- `Statement:` ⊥ of `U` absorbs `collect`: `collect S = bot` whenever `bot ∈ S`. By cases on
    `WithTop.LE`, with no order lemma. -/
theorem collect_absorbs_bot {U : Type*} [ZPSemilattice U] [ValuationStructure U]
    [DecorationUniverse U] (S : Set U) (h : (bot : U) ∈ S) :
    DecorationUniverse.collect S = bot := by
  have hge := DecorationUniverse.collect_val_ge S bot h
  rw [ValuationStructure.val_bot] at hge
  apply ValuationStructure.val_unique
  rcases hv : ValuationStructure.val (DecorationUniverse.collect S) with _ | m
  · rfl
  · rw [hv] at hge
    have h' : WithTop.LE (none : WithTop ℕ) (some m) := hge
    cases h'

-- Statement: its instance: ⊥ of `U` absorbs `collect` in every `DecorationUniverse`.
example {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (S : Set U) (h : (bot : U) ∈ S) : DecorationUniverse.collect S = bot :=
  collect_absorbs_bot S h

-- Statement: `v` reverses the ZP order into ℕ∞'s iff `v (join x y) ≤ min (v x) (v y)`; Mathlib's
-- `Antitone.map_sup_le` and `Monotone.of_le_map_sup` (through `OrderDual`), restated because the ZP
-- order is not `≤` here. Reading: the equation form is a nonzero prime's valuation on the fractional
-- ideals of a Dedekind domain (values in ℤ), `v_p(I + J) = min (v_p I) (v_p J)` (Aitken,
-- arXiv 2102.11725, Prop. 86, p. 33).
example {L : Type*} [ZPSemilattice L] (v : L → ℕ∞) :
    (∀ x y, le x y → v y ≤ v x) ↔ ∀ x y, v (join x y) ≤ min (v x) (v y) := by
  have hl : ∀ x y : L, le x (join x y) := fun x y =>
    show join x (join x y) = join x y by rw [← join_assoc, join_idem]
  refine ⟨fun h x y => le_min (h _ _ (hl x y)) (h _ _ (join_comm y x ▸ hl y x)), fun h x y hxy => ?_⟩
  have := h x y
  rw [show join x y = y from hxy] at this
  exact le_trans this (min_le_left _ _)

-- Statement: one way only: under order-reversal, any identity `e` of a binary operation `j` is the
-- unique `v`-⊤ point `b`, the absorber above.
example {U : Type*} (j : U → U → U) (v : U → ℕ∞) (c : Set U → U)
    (hc : ∀ S x, x ∈ S → v (c S) ≥ v x + 1) (b : U) (hu : ∀ x, v x = ⊤ → x = b)
    (hanti : ∀ x y, j x y = y → v y ≤ v x) (e : U) (he : ∀ x, j e x = x) : e = b := by
  have htop : v (c Set.univ) = ⊤ := by
    have h := hc Set.univ (c Set.univ) trivial
    rcases hv : v (c Set.univ) with _ | m
    · rfl
    · rw [hv] at h
      change (m : ℕ∞) ≥ (m : ℕ∞) + 1 at h
      exact absurd (show m ≥ m + 1 by exact_mod_cast h) (by omega)
  exact hu e (top_le_iff.mp (htop ▸ hanti e (c Set.univ) (he _)))

-- Statement: the converse fails (counter-model M1, on `Option ℕ∞`): a semilattice operation with
-- order-reversal and a unique, absorbing `v`-⊤ point, and no identity at all.
example : ∃ (j : Option ℕ∞ → Option ℕ∞ → Option ℕ∞) (v : Option ℕ∞ → ℕ∞)
    (c : Set (Option ℕ∞) → Option ℕ∞) (b : Option ℕ∞),
    (∀ x y z, j (j x y) z = j x (j y z)) ∧ (∀ x y, j x y = j y x) ∧ (∀ x, j x x = x) ∧
    (∀ x y, j x y = y → v y ≤ v x) ∧ (∀ x, v x = ⊤ → x = b) ∧
    (∀ S x, x ∈ S → v (c S) ≥ v x + 1) ∧ (∀ S, b ∈ S → c S = b) ∧
    ¬ ∃ e, ∀ x, j e x = x := by
  let mj : Option ℕ∞ → Option ℕ∞ → Option ℕ∞ := fun x y => match x, y with
    | some a, some c => some (min a c)
    | none, none => none
    | _, _ => some 0
  let mv : Option ℕ∞ → ℕ∞ := fun x => x.elim 0 id
  have hu : ∀ x, mv x = ⊤ → x = some ⊤ := by
    intro x hx; rcases x with _ | x
    · simp [mv] at hx
    · simp [mv] at hx; simp [hx]
  have hc : ∀ (S : Set (Option ℕ∞)) x, x ∈ S → mv (some (sSup (mv '' S) + 1)) ≥ mv x + 1 :=
    fun S x hx => add_le_add (le_sSup (Set.mem_image_of_mem mv hx)) le_rfl
  refine ⟨mj, mv, fun S => some (sSup (mv '' S) + 1), some ⊤, ?_, ?_, ?_, ?_, hu, hc, ?_, ?_⟩
  · intro x y z
    rcases x with _ | x <;> rcases y with _ | y <;> rcases z with _ | z <;> simp [mj, min_assoc]
  · intro x y
    rcases x with _ | x <;> rcases y with _ | y <;> simp [mj, min_comm]
  · intro x; rcases x with _ | x <;> simp [mj]
  · intro x y h
    rcases x with _ | x <;> rcases y with _ | y
    · exact le_rfl
    · change some (0 : ℕ∞) = some y at h
      change y ≤ 0
      rw [← Option.some.inj h]
    · change some (0 : ℕ∞) = none at h
      exact absurd h (Option.some_ne_none _)
    · change some (min x y) = some y at h
      change y ≤ x
      rw [← Option.some.inj h]
      exact min_le_left x y
  · intro S hS
    refine hu _ (top_le_iff.mp ?_)
    exact le_trans (le_self_add (a := ⊤) (b := 1)) (hc S _ hS)
  · rintro ⟨e, he⟩
    rcases e with _ | e
    · have := he (some 5); simp [mj] at this
    · have := he none; simp [mj] at this

-- Statement: without order-reversal the identity and the absorber can be different elements
-- (counter-model M2, ℕ∞ with `max`): 0 is the identity, ⊤ absorbs `sSup · + 1`.
example : (∀ x : ℕ∞, max 0 x = x) ∧ (∀ S : Set ℕ∞, ⊤ ∈ S → sSup S + 1 = ⊤) ∧
    (∀ (S : Set ℕ∞) x, x ∈ S → sSup S + 1 ≥ x + 1) ∧ (0 : ℕ∞) ≠ ⊤ ∧
    ¬ ∀ x y : ℕ∞, max x y = y → y ≤ x := by
  refine ⟨fun x => by simp, fun S hS => ?_, fun S x hx => add_le_add (le_sSup hx) le_rfl,
    by simp, fun h => ?_⟩
  · rw [top_le_iff.mp (le_sSup hS)]; rfl
  · have := h 0 1 (by simp); simp at this

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

    Two proofs, one per chart (the `Reading:` on `decoration_unique_of_val`):

    - `decoration_unique`, graph side, `[Fintype V]`: strong induction on |{w | Path u w}|. A cyclic
      u goes to ⊥ of `U` (`cyclic_decoration_eq_bot`); for an acyclic u each child's reachable set
      is strictly smaller, which `[Fintype V]` bounds, and `acyclic_induction_step` closes the goal.
    - `decoration_unique_of_val`, value side, any quiver: strong induction on the finite valuation
      of the TARGET value; valuation ⊤ is forced to ⊥ of `U` by `val_unique`. -/

/-! ### PRIOR ART — the uniqueness clause of a RECURSIVE COALGEBRA, for ONE SHAPE of algebra.

A coalgebra is **recursive** when *every* algebra admits a unique coalgebra-to-algebra morphism
(Adámek-Milius-Moss 2020, arXiv:1910.09401v2, Def 3.2 p. 11, crediting Osius for the definition).
`decoration_unique` gives that clause for algebras of the `DecorationUniverse.collect` shape only,
and existence not at all. Well-foundedness of the GRAPH (Taylor's General Recursion Theorem, AMM
Thm 7.2 p. 27; `ZeroParadox/Category/WellFoundedCoalgebra.lean`) is unavailable, as these quivers
may carry cycles. `decoration_unique_of_val` inducts on the TARGET's rank instead: the AFA2 half of
"the foundation axiom implies AFA2 and the negation of AFA1" (Aczel, *Non-Well-Founded Sets*, CSLI
1988, Ex. 2.1 p. 20; AFA1/AFA2 p. 19), with one rank-⊤ point, ⊥ of `U`, admitted via `val_unique`. -/

-- Statement: `IsDecoration d` is the coalgebra-to-algebra equation `d = collect ∘ (d '' ·) ∘ apg_children`.
-- Reading: read from the TARGET, `decoration_unique` is then CRA-uniqueness for the algebra `collect`
-- (Capretta-Uustalu-Vene, *Corecursive Algebras*, SBMF 2009, LNCS 5902, Def. 1 p. 86), from the
-- coalgebras `apg_children` of finite APGs; the `example` after `decoration_unique` drops the `APG`
-- argument and gives the same uniqueness for every finite quiver, `decoration_unique_of_val` for
-- every quiver. Also near: Urabe, Hara and Hasuo,
-- *Categorical Liveness Checking by Corecursive Algebras* (arXiv:1704.04872), use a corecursive algebra
-- "as a classifier for (non-)well-foundedness" (abstract) in their ranking domains (Def. III.10,
-- p. 7), classically ranking functions into ℕ ∪ {∞} (p. 1); here a cyclic vertex gets valuation ⊤
-- (`cyclic_decoration_eq_bot` with `ValuationStructure.val_bot`; the `example` directly after `cyclic_decoration_eq_bot` states both).
example {V : Type*} [Quiver V] {U : Type*} [ZPSemilattice U] [ValuationStructure U]
    [DecorationUniverse U] (d : V → U) :
    IsDecoration d ↔ d = fun v => DecorationUniverse.collect (d '' apg_children v) :=
  ⟨fun h => funext h, fun h v => congrFun h v⟩

-- `[Fintype V]` is not used in the *type*; THIS proof spends it bounding the reachable-set
-- cardinality for `Set.ncard_lt_ncard`. Uniqueness needs no finiteness: `decoration_unique_of_val`.
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

-- Statement: the same uniqueness holds for EVERY finite quiver, with no `APG` argument: the proof of
-- `decoration_unique`, which never reads its `APG`, run without one.
-- Reading: the uniqueness half (not existence) of a "finitary corecursive" algebra, unique solutions
-- for coalgebras on finitely presentable objects (Adámek, Haddadi and Milius, LMCS 10(3:19), 2014,
-- arXiv:1407.4425, Def. 8.1(a), p. 40).
example {V : Type*} [Quiver V] [Fintype V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) : d₁ = d₂ := by
  funext v
  suffices key : ∀ n : ℕ, ∀ u : V,
      ({x : V | Nonempty (Quiver.Path u x)}).ncard ≤ n → d₁ u = d₂ u from key _ v le_rfl
  intro n
  induction n with
  | zero =>
    intro u hcard
    have hpos : 0 < ({x : V | Nonempty (Quiver.Path u x)}).ncard := by
      rw [Set.ncard_pos]; exact ⟨u, ⟨Quiver.Path.nil⟩⟩
    omega
  | succ n ih =>
    intro u hcard
    by_cases hcyc : HasSelfCycle u
    · rw [cyclic_decoration_eq_bot d₁ hd₁ u hcyc, cyclic_decoration_eq_bot d₂ hd₂ u hcyc]
    · apply acyclic_induction_step d₁ d₂ hd₁ hd₂ u
      intro w hw
      simp only [apg_children, Set.mem_setOf_eq] at hw
      apply ih w
      have hv_in : u ∈ {x : V | Nonempty (Quiver.Path u x)} := ⟨Quiver.Path.nil⟩
      have hv_not : u ∉ {x : V | Nonempty (Quiver.Path w x)} := fun ⟨p⟩ => hcyc ⟨w, hw, ⟨p⟩⟩
      have hstrict : {x : V | Nonempty (Quiver.Path w x)} ⊂ {x : V | Nonempty (Quiver.Path u x)} :=
        ⟨fun _ ⟨p⟩ => ⟨(Quiver.Path.nil.cons hw.some).comp p⟩, fun hsub => hv_not (hsub hv_in)⟩
      have hlt := Set.ncard_lt_ncard hstrict
      omega

/-- `Statement:` in ℕ∞, `m ≥ x + 1` for a natural `m` gives a natural `k < m` with `x = k`.
    By cases on Mathlib's inductive `WithTop.LE`, with no order lemma (`WithTop`'s order
    instances: `ZeroParadox/Category/ChoiceCannotBe.lean` § III). -/
theorem enat_lt_of_add_one_le {m : ℕ} {x : ℕ∞} (h : (m : ℕ∞) ≥ x + 1) :
    ∃ k : ℕ, x = (k : ℕ∞) ∧ k < m := by
  rcases x with _ | k
  · have h' : WithTop.LE (none : WithTop ℕ) (some m) := h
    cases h'
  · have h' : WithTop.LE (some (k + 1) : WithTop ℕ) (some m) := h
    cases h' with
    | coe_le_coe hab => exact ⟨k, rfl, hab⟩

/-- `Statement:` two decorations of any quiver agree at every vertex where the first one's value
    has a finite valuation `m`; strong induction on `m`, each child's valuation strictly smaller
    by `collect_val_ge`. -/
theorem decoration_agree_of_val_coe
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) :
    ∀ m : ℕ, ∀ u : V, ValuationStructure.val (d₁ u) = (m : ℕ∞) → d₁ u = d₂ u := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro u hu
    apply acyclic_induction_step d₁ d₂ hd₁ hd₂ u
    intro w hw
    have hmem : d₁ w ∈ d₁ '' apg_children u := ⟨w, hw, rfl⟩
    have hge := DecorationUniverse.collect_val_ge (d₁ '' apg_children u) (d₁ w) hmem
    rw [← hd₁ u, hu] at hge
    obtain ⟨k, hk, hlt⟩ := enat_lt_of_add_one_le hge
    exact ih k hlt w hk

/-- `Statement:` on EVERY quiver, finite or not, any two decorations into a `DecorationUniverse`
    are equal; no `APG` argument and no finiteness binder.
    `Reading:` CARRIER, one uniqueness in two charts, neither of them the structure. The graph side splits
    vertices acyclic/cyclic (`decoration_unique`); the value side, this proof, splits the valuation
    finite/⊤, and `val_unique` sends ⊤ to ⊥ of `U`. `collect_val_ge` and `val_unique` relate them,
    one way: a cyclic vertex's valuation is ⊤ (`cyclic_decoration_eq_bot`); no converse is claimed. -/
theorem decoration_unique_of_val
    {V : Type*} [Quiver V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) :
    d₁ = d₂ := by
  funext u
  rcases h₁ : ValuationStructure.val (d₁ u) with _ | m
  · rcases h₂ : ValuationStructure.val (d₂ u) with _ | n
    · rw [ValuationStructure.val_unique _ h₁, ValuationStructure.val_unique _ h₂]
    · exact (decoration_agree_of_val_coe d₂ d₁ hd₂ hd₁ n u h₂).symm
  · exact decoration_agree_of_val_coe d₁ d₂ hd₁ hd₂ m u h₁

-- Statement: it applies on an infinite quiver: ℕ with one edge n ⟶ n + 1.
example {U : Type} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (d₁ d₂ : ℕ → U) (hd₁ : @IsDecoration ℕ ⟨fun a b => PLift (b = a + 1)⟩ U _ _ _ d₁)
    (hd₂ : @IsDecoration ℕ ⟨fun a b => PLift (b = a + 1)⟩ U _ _ _ d₂) : d₁ = d₂ :=
  @decoration_unique_of_val ℕ ⟨fun a b => PLift (b = a + 1)⟩ U _ _ _ d₁ d₂ hd₁ hd₂

set_option linter.unusedFintypeInType false in
/-- `Statement:` `decoration_unique` with `[Finite V]` in place of `[Fintype V]`, the restatement
    `ZeroParadox/Category/ChoiceCannotBe.md` asks of a STATEMENT-CARRIED theorem. -/
theorem decoration_unique_finite
    {V : Type*} [Quiver V] [Finite V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (_G : APG V) (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) :
    d₁ = d₂ :=
  decoration_unique_of_val d₁ d₂ hd₁ hd₂

-- Statement: `decoration_unique`'s statement, `[Fintype V]` included, is a special case of
-- `decoration_unique_of_val`; its footprint stays the statement's (PurityCheck).
set_option linter.unusedFintypeInType false in
example {V : Type*} [Quiver V] [Fintype V]
    {U : Type*} [ZPSemilattice U] [ValuationStructure U] [DecorationUniverse U]
    (_G : APG V) (d₁ d₂ : V → U) (hd₁ : IsDecoration d₁) (hd₂ : IsDecoration d₂) : d₁ = d₂ :=
  decoration_unique_of_val d₁ d₂ hd₁ hd₂

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
#print axioms path_decoration_eq_bot
#print axioms absorb_of_unique_top
#print axioms collect_absorbs_bot
#print axioms decoration_unique
#print axioms enat_lt_of_add_one_le
#print axioms decoration_agree_of_val_coe
#print axioms decoration_unique_of_val
#print axioms decoration_unique_finite
-- The class, and the `[Fintype V]` binder of `decoration_unique` (the custom-registry line above the class).
#print axioms DecorationUniverse
#print axioms Fintype

end PurityCheck
