import ZeroParadox.Category.Lawvere
import Mathlib.Order.UpperLower.Basic

/-!
# The minimum requirements to be a diagonal fixed point — the relativized Lawvere witness

`DiagonalFixedPoint.lean` *collects* the faces of self-reference; this file asks what they **minimally
have in common**, one level beneath the μ/ν fork. The engine is the diagonal argument of **Lawvere
(1969)**, restated by **Yanofsky (2003)**; that whether the witness exists is *category-relative* is the
recognized effective-topos / Turing-category observation (**Hyland 1982; Cockett–Hofstra 2008; van
Oosten**). This file only *packages* those — `HasWitnessRel` is a formalization lever, not a new theorem,
and its level sets are the per-face verdicts already proven in `Category/Lawvere.lean` §V–VI. There the
bare `HasLawvereWitness β` (a point-surjection `α → (α → β)`) is FALSE for every nontrivial type in
**Set** (Cantor), so the lattice and 2-adic faces are *posited* fixed points, while the computability
(Kleene) face is *genuine* — in the **effective** category.

## The underlying level: the witness relative to an admissible endomap class

`HasWitnessRel β M` relativizes the diagonal hypothesis to a class `M` of admissible endomaps: a
self-application `e : α → (α → β)` whose range contains the diagonal `fun x => g (e x x)` for every
`g ∈ M`. This is the minimal requirement — the witness only has to dodge the diagonals of the maps `M`
that "count" in the ambient category. The face table becomes level sets of ONE predicate:
- **M coarse (all endomaps), β nontrivial** — a fixed-point-free swap is admissible ⇒ no witness. Set
  floor faces are *posited*, wall faces *refuted*.
- **M fine (computable endomaps)** — the fixed-point-free diagonal is **not** admissible, which
  **removes** the § III obstruction. It does not by itself supply the witness: the implication runs one
  way, and **no `HasWitnessRel` theorem for the computable class is proved in this file.** The genuine
  diagonal fixed point on this side is **Kleene's recursion theorem**, cited rather than derived here
  (`Nat.Partrec.Code.fixed_point`, aliased below as `computability_face_fixedPoint`).
  *(Corrected 2026-08-01: previously written "not admissible ⇒ the witness holds ⇒ a genuine diagonal
  fixed point", which does not follow — an absent obstruction is not a witness.)*

## The topology (why "underlying level" makes it obvious)

`HasWitnessRel β ·` is **antitone** in `M`: shrinking the admissible class can only help the witness. So
`{M | HasWitnessRel β M}` is downward-closed in `⊆` — a lower set on the lattice of admissible-map-classes,
i.e. a **closed set in the Alexandrov topology** on that lattice. The wall/floor/posited trichotomy is the
level structure of one monotone predicate over that space; the floor "switches on" exactly as `M` drops
below the fixed-point-free diagonal. That lattice-of-map-classes, with the witness as an Alexandrov-closed
set, is the topology the collection carries.

## Engineer's Take

Definition of a minimal set of criteria across the faces, including Cantor, Russell, Turing, Kleene,
Tarski, Curry, Löb, Gödel, and Rice. We focused our work around behavior at bottom, and have been able
to build a topological map.
-/

namespace ZeroParadox

open Function

universe u

/-- **The minimal requirement (relativized diagonal hypothesis).** `β` has a diagonal witness *relative
    to* an admissible endomap class `M` when some self-application `e : α → (α → β)` has, in its range,
    the diagonal `fun x => g (e x x)` for every admissible `g`. `HasLawvereWitness` relativized to the
    maps the diagonal must dodge — the underlying level beneath the μ/ν fork. (`α` shares `β`'s universe:
    the self-reference faces encode maps on the same object.) -/
def HasWitnessRel (β : Type u) (M : (β → β) → Prop) : Prop :=
  ∃ (α : Type u) (e : α → (α → β)), ∀ g : β → β, M g → ∃ a, (fun x => g (e x x)) = e a

/-- **The engine, relativized.** A relative witness forces every *admissible* endomap to have a fixed
    point (Lawvere's diagonal, restricted to `M`). -/
theorem fixedPoint_of_witnessRel {β : Type*} {M : (β → β) → Prop}
    (h : HasWitnessRel β M) {g : β → β} (hg : M g) : ∃ b, g b = b := by
  obtain ⟨α, e, he⟩ := h
  obtain ⟨a, ha⟩ := he g hg
  exact ⟨e a a, congrFun ha a⟩

/-- **The obstruction, relativized (the wall).** If an admissible endomap is fixed-point-free, there is
    no relative witness. Cantor, restricted to `M`. -/
theorem no_witnessRel_of_admissible_fpf {β : Type*} {M : (β → β) → Prop}
    {g : β → β} (hg : M g) (hgf : ∀ x, g x ≠ x) : ¬ HasWitnessRel β M := by
  intro h
  obtain ⟨b, hb⟩ := fixedPoint_of_witnessRel h hg
  exact hgf b hb

/-- **Antitone in the admissible class (the topology spine).** Shrinking the admissible endomap class
    can only help the witness. So `{M | HasWitnessRel β M}` is downward-closed in `⊆` — a lower set /
    Alexandrov-closed set on the lattice of admissible-map-classes. -/
theorem witnessRel_antitone {β : Type*} {M M' : (β → β) → Prop}
    (hsub : ∀ g, M g → M' g) (h : HasWitnessRel β M') : HasWitnessRel β M := by
  obtain ⟨α, e, he⟩ := h
  exact ⟨α, e, fun g hg => he g (hsub g hg)⟩

/-- A surjective self-application gives a relative witness for the *entire* endomap class — the top of
    the lattice, where the engine forces a fixed point for every map. This is the framework's absolute
    `HasLawvereWitness` content, stated directly in `β`'s universe (`Category/Lawvere.lean` phrases it
    with a universe-independent `α`). -/
theorem hasWitnessRel_top_of_surjective {β : Type u} {α : Type u} (f : α → (α → β))
    (hf : Surjective f) : HasWitnessRel β (fun _ => True) := by
  refine ⟨α, f, fun g _ => ?_⟩
  obtain ⟨a, ha⟩ := hf (fun x => g (f x x))
  exact ⟨a, ha.symm⟩

/-- **The coarse-M level set (Cantor recovered).** At the top of the lattice — every endomap admissible —
    any nontrivial carrier has NO witness: the fixed-point-free swap is admissible and kills it. This is
    the Set-level Cantor obstruction as a level set of `HasWitnessRel`, and it is exactly why the lattice
    and 2-adic faces are *posited* (a designated self-map has a fixed point without a witness), not
    genuine, at the coarse end. Mirrors `no_witness_of_nontrivial` (`Category/Lawvere.lean`). -/
theorem no_witnessRel_top_of_nontrivial {β : Type u} [DecidableEq β] [Nontrivial β] :
    ¬ HasWitnessRel β (fun _ => True) := by
  -- Choice-free: with `DecidableEq β` the swap needs no classical decision (constructive-footprint audit,
  -- 2026-07-18). This is the base-level, choice-free form; the `DecidableEq` restriction is what buys
  -- the purity. The construction inlined below is the one that
  -- `ZeroParadox/Category/Lawvere.lean`'s `fixedPointFree_of_nontrivial` produces, and THAT theorem is
  -- essentially classical — `ZeroParadox/Category/LawvereTaboo.lean`'s `wem_of_fixedPointFree` reduces
  -- weak excluded middle from it. **That is a fact about that theorem, not about this one:
  -- essentiality does not transfer, and there is no dependency here — the swap is inlined, and this
  -- statement measures `[propext]`, which is what proves the independence.**
  -- (Corrected 2026-08-01, found independently by all three round-4 gates: an earlier revision called
  -- this "the theorem this MIRRORS (`:96`)". Line 96 mirrors `no_witness_of_nontrivial`, a DIFFERENT
  -- declaration; the relation to `fixedPointFree_of_nontrivial` is inlining, not mirroring. That
  -- revision had itself corrected the word "SUPPLIER" while carrying the wrong theorem name along.)
  obtain ⟨b₀, b₁, hne⟩ := exists_pair_ne β
  refine no_witnessRel_of_admissible_fpf (g := fun x => if x = b₀ then b₁ else b₀) trivial (fun x => ?_)
  by_cases hx : x = b₀
  · subst hx; simpa using hne.symm
  · simp only [if_neg hx]; exact fun h => hx h.symm

/-- **The fine end is inhabited (non-degeneracy).** A one-element carrier has a witness for *every*
    admissible class — there is no fixed-point-free endomap to obstruct it, so the diagonal always
    closes. This is the trivial genuine floor; it keeps the witness set (hence the topology) from being
    empty. The nontrivial genuine floor is the computability face (see below). -/
theorem hasWitnessRel_of_subsingleton {β : Type u} [Nonempty β] [Subsingleton β]
    (M : (β → β) → Prop) : HasWitnessRel β M := by
  obtain ⟨b₀⟩ := ‹Nonempty β›
  refine ⟨β, fun b _ => b, fun g _ => ⟨b₀, ?_⟩⟩
  funext x
  exact Subsingleton.elim _ _

/-! ## § The topology — the witness set is Alexandrov-closed on the lattice of map-classes -/

/-- **The topology, made explicit.** On the lattice of admissible-map-classes `Set (β → β)` (ordered by
    inclusion), the set of classes carrying a diagonal witness is a **lower set** — downward closed. A
    lower set is exactly a closed set of the Alexandrov topology on the poset, so this is the topology
    the diagonal-fixed-point collection sits on: the fork (wall vs floor) is the boundary of one closed
    set, crossed as the admissible class shrinks past the fixed-point-free diagonal. Immediate from
    `witnessRel_antitone`. -/
theorem witnessSet_isLowerSet {β : Type u} :
    IsLowerSet {M : Set (β → β) | HasWitnessRel β M} := by
  intro a b hab hb
  exact witnessRel_antitone (fun g hg => hab hg) hb

/-! ## § Axis 2 — the genuine floor in the effective category (joining the effective-topos program)

The `HasWitnessRel` topology above is axis 1: the admissible map-class M *within* a fixed category
(raw functions, raw equality). The genuine NONTRIVIAL floor lives one axis out — in the **effective
category**, where "endomap" means computable and "equality" means eval-equality. There the Cantor
obstruction lifts, and the diagonal genuinely closes: Rogers' fixed-point / Kleene's recursion theorem. This is the
recognized **effective-topos / Turing-category** setting (Lawvere 1969; Hyland 1982, "The effective
topos"; Cockett–Hofstra 2008, "Introduction to Turing categories"; van Oosten). Located and cited here,
NOT claimed — the framework joins that program. -/

/-- **Axis-2 genuine floor.** Every *computable* self-map on codes has an eval-fixed point —
    **Rogers' fixed-point theorem** (`computability_face_fixedPoint` = Mathlib
    `Nat.Partrec.Code.fixed_point`). Mathlib reserves the name *Kleene's second recursion theorem*
    for `fixed_point₂`; the two are inter-derivable, and `ZeroParadox/Category/Lawvere.lean:116,121`
    words it the same way. The fine end of axis 2. -/
theorem effective_floor_fixedPoint {g : Nat.Partrec.Code → Nat.Partrec.Code} (hg : Computable g) :
    ∃ c, Nat.Partrec.Code.eval (g c) = Nat.Partrec.Code.eval c :=
  computability_face_fixedPoint hg

/-- **Why the wall lifts in the effective category (the axis-2 mechanism).** There is no *computable*
    self-map on codes that is eval-fixed-point-free: the recursion theorem forces a fixed point. So the
    diagonal swap that refutes the witness at the Set level (`no_witnessRel_of_admissible_fpf`) has NO
    computable representative — it is not admissible effectively, and the obstruction cannot fire. This
    is exactly why the floor switches on along axis 2. -/
theorem no_computable_evalFixedPointFree {g : Nat.Partrec.Code → Nat.Partrec.Code} (hg : Computable g) :
    ¬ (∀ c, Nat.Partrec.Code.eval (g c) ≠ Nat.Partrec.Code.eval c) := by
  intro hfpf
  obtain ⟨c, hc⟩ := effective_floor_fixedPoint hg
  exact hfpf c hc

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms HasWitnessRel
#print axioms fixedPoint_of_witnessRel
#print axioms no_witnessRel_of_admissible_fpf
#print axioms witnessRel_antitone
#print axioms hasWitnessRel_top_of_surjective
#print axioms no_witnessRel_top_of_nontrivial
#print axioms hasWitnessRel_of_subsingleton
#print axioms witnessSet_isLowerSet
#print axioms effective_floor_fixedPoint
#print axioms no_computable_evalFixedPointFree
end PurityCheck
