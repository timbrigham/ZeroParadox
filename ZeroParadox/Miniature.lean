import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option maxHeartbeats 400000

universe u

/-!
# The Zero Paradox in miniature — the minimal core

## Engineer's Take

If we know exactly what conditions always create the snap and those that always create the wall, that is the
beginnings of a map that would always fit. This is that map on the smallest concrete witness: the engine, the
boundaries and why they have to be where they are, and the snap and why it has to be there. It is the most
compact way of showing what the whole project is about, in a couple hundred lines of Lean.

---

## Formal Overview (AI-assisted)

The smallest self-contained artifact that exhibits the **shape** the whole framework is built on: the
**engine**, the **wall** and **floor** and *why each must be where it is*, and the **snap** and *why it must
be one-way* — all on the smallest possible concrete witness, the two-element pole, where every "why" is
**decidable** (computed, not asserted).

It reads top to bottom:

* **§ I — the engine.** Lawvere's diagonal (`lawvere`): a point-surjection forces every endomap to have a
  fixed point. Its dual seed (`negation_no_fp`): negation has no fixed point. This is the one mechanism the
  whole framework runs off.
* **§ II — the classifier (the map).** `HasWitnessRel` is the minimum requirement to be a diagonal fixed
  point; `floor_of_witness` is the **floor** (a witness forces a fixed point); `wall_of_fpf` is the **wall**
  (a fixed-point-free map kills the witness); `witness_antitone` is the topology spine (the witness set is a
  lower set). This is the classifier that sorts wall from floor everywhere.
* **§ III–IV — the smallest concrete witness.** The two-element pole `{0, ∞}` has exactly **four** self-maps
  (`card_four`, `four_exhaustive`), classified by fixed-point count: `swap` (0 — the **wall**), the two
  collapses (1 — the **floor** at each pole), the identity (2 — both fixed). The **bridge** `swap_is_the_wall`
  is the one genuinely-new line: `swap` is fixed-point-free, so by the classifier it kills the witness — the
  wall sits at the inversion corner, on the smallest domain there is.
* **§ V — the snap.** The floor is the *irreversible* corner: the collapse forgets which pole it came from
  (`snap_irreversible`), while the wall (`swap`) is *reversible* (`swap_involutive`). So the one-way direction
  — the snap — sits at the floor, not the wall, and this too is forced.
* **The capstone (`miniature`)** bundles the four forced facts: wall has no fixed point, floor closes at a
  fixed point, the wall is reversible, the floor/snap is not — the entire shape, decided, in one theorem.

**Honest status.** The *content* is re-derived, not new: the engine is **Lawvere (1969) / Yanofsky (2003)**
(canonical home `Settheory/Wall.lean` `lawvere_fixedpoint`); the classifier is `Category/DiagonalWitness.lean`;
the four corners are `Valuation/PoleCorners.lean`. The tiny proofs are **restated inline for
self-containment** (this file is meant to read in isolation), and the only new connective tissue is
`swap_is_the_wall` — the four corners as the *finite instance* of the classifier. The *value* is the
compression: the shape in ~150 lines you can check in one sitting.

**Honest fence (load-bearing).** This is the **shape**, the skeleton every domain hangs on — **not** the
entire project. The framework's flesh is its domain instances (set theory / AFA, the 2-adics, ε₀ and proof
theory, the categorical bridges, the whole MC-1 bottom family), which are *not* here and cannot be: the whole
point of the layers is that they are the shape *worn* by real mathematics. This file stands **alongside** them
as the most compact statement of what they are all instances *of*; it does not contain or replace them. And
the cross-domain identity of the instances stays a type boundary (retired as ill-typed), never a Lean `=`.
-/

namespace ZeroParadox.Miniature

/-! ### § I. The engine — Lawvere's diagonal and its no-fixed-point seed. -/

/-- **The engine.** A point-surjection `e : A → (A → B)` forces every endomap `f : B → B` to have a fixed
point (Lawvere 1969). The whole framework's self-reference runs off this one construction. -/
theorem lawvere {A B : Type*} (e : A → (A → B)) (surj : Function.Surjective e) (f : B → B) :
    ∃ b, f b = b := by
  obtain ⟨a, ha⟩ := surj (fun x => f (e x x))
  exact ⟨e a a, (congrFun ha a).symm⟩

/-- **The seed of the wall.** Negation has no fixed point: no proposition satisfies `p ↔ ¬p`. Everything on
the wall side is this, wearing a domain's clothes (Cantor, Russell, Turing, Tarski). -/
theorem negation_no_fp (p : Prop) : ¬ (p ↔ ¬ p) := by
  intro h
  have hnp : ¬ p := fun hp => h.mp hp hp
  exact hnp (h.mpr hnp)

/-! ### § II. The classifier — the minimum requirement, and the wall / floor conditions. -/

/-- **The minimum requirement.** `β` carries a diagonal witness relative to an admissible endomap class `M`
when some self-application `e : α → (α → β)` has, in its range, the diagonal of every admissible `g`. -/
def HasWitnessRel (β : Type u) (M : (β → β) → Prop) : Prop :=
  ∃ (α : Type u) (e : α → (α → β)), ∀ g : β → β, M g → ∃ a, (fun x => g (e x x)) = e a

/-- **The floor condition.** A witness forces every admissible endomap to have a fixed point — self-reference
closes. -/
theorem floor_of_witness {β : Type*} {M : (β → β) → Prop} (h : HasWitnessRel β M)
    {g : β → β} (hg : M g) : ∃ b, g b = b := by
  obtain ⟨α, e, he⟩ := h
  obtain ⟨a, ha⟩ := he g hg
  exact ⟨e a a, congrFun ha a⟩

/-- **The wall condition.** A fixed-point-free admissible endomap kills the witness — self-reference cannot
close. This is Cantor, relativized. -/
theorem wall_of_fpf {β : Type*} {M : (β → β) → Prop} {g : β → β} (hg : M g)
    (hgf : ∀ x, g x ≠ x) : ¬ HasWitnessRel β M := by
  intro h
  obtain ⟨b, hb⟩ := floor_of_witness h hg
  exact hgf b hb

/-- **The topology spine.** Shrinking the admissible class can only help the witness, so the witness set is a
lower set (Alexandrov-closed) on the lattice of map-classes — the space the wall/floor verdict lives on. -/
theorem witness_antitone {β : Type*} {M M' : (β → β) → Prop}
    (hsub : ∀ g, M g → M' g) (h : HasWitnessRel β M') : HasWitnessRel β M := by
  obtain ⟨α, e, he⟩ := h
  exact ⟨α, e, fun g hg => he g (hsub g hg)⟩

/-! ### § III. The smallest concrete witness — the two-element pole and its four self-maps. -/

/-- The pole: the two-element type `{0, ∞}`. -/
inductive Pole where
  | zero
  | infty
deriving DecidableEq, Fintype, Repr

namespace Pole

/-- Collapse to `0` — the floor at zero. -/
def cZero : Pole → Pole := fun _ => zero
/-- Collapse to `∞` — the floor at infinity. -/
def cInfty : Pole → Pole := fun _ => infty
/-- The identity — both poles fixed. -/
def cId : Pole → Pole := id
/-- The inversion `0 ↔ ∞` — the wall. -/
def swap : Pole → Pole
  | zero => infty
  | infty => zero

/-- **Exactly four self-maps.** `2² = 4`. -/
theorem card_four : Fintype.card (Pole → Pole) = 4 := by decide

/-- **The four are exhaustive.** Every self-map of the pole is one of the four corners. -/
theorem four_exhaustive (f : Pole → Pole) :
    f = cZero ∨ f = cInfty ∨ f = cId ∨ f = swap := by
  revert f; decide

/-! ### § IV. The fixed-point classification, and the bridge to the classifier. -/

/-- **The wall corner has no fixed point.** `swap` fixes neither pole: 0 fixed points. -/
theorem swap_no_fp : ∀ p, swap p ≠ p := by decide

/-- **The floor corner closes.** The collapse `cZero` fixes `0`: self-reference lands at the floor. -/
theorem cZero_has_fp : ∃ b, cZero b = b := ⟨zero, rfl⟩

/-- **The identity fixes both poles** — the double corner (2 fixed points). -/
theorem cId_all_fp : ∀ p, cId p = p := by decide

/-- **THE BRIDGE (the one new line).** `swap` is the fixed-point-free map, so by the classifier's wall
condition it kills the witness: the **wall sits at the inversion corner**, on the smallest domain there is.
The four corners are the finite instance of the wall/floor classifier. -/
theorem swap_is_the_wall (M : (Pole → Pole) → Prop) (hswap : M swap) :
    ¬ HasWitnessRel Pole M :=
  wall_of_fpf hswap swap_no_fp

/-! ### § V. The snap — the floor is the irreversible corner. -/

/-- **The wall is reversible.** `swap` is an involution; you can always turn back. -/
theorem swap_involutive : Function.Involutive swap := by
  intro p; cases p <;> rfl

/-- **The floor/snap is irreversible.** The collapse `cZero` forgets which pole it came from — not injective.
This is the one-way direction: you can fall to the floor, not un-fall. The snap sits here, not at the wall. -/
theorem snap_irreversible : ¬ Function.Injective cZero := by
  intro h
  exact absurd (@h zero infty rfl) (by decide)

/-! ### § VI. The capstone — the whole shape, forced, in one theorem. -/

/-- **The miniature.** On the smallest concrete witness, all four faces of the shape are forced by
computation: the **wall** (`swap`) has no fixed point; the **floor** (`cZero`) closes at a fixed point; the
wall is **reversible**; the floor/**snap** is **irreversible**. The engine (`lawvere`) and classifier
(`wall_of_fpf` / `floor_of_witness`) say *why* — a fixed-point-free map is a wall, a witness is a floor — and
here it is, decided, on two points. -/
theorem miniature :
    (∀ p, swap p ≠ p) ∧
    (∃ b, cZero b = b) ∧
    Function.Bijective swap ∧
    ¬ Function.Injective cZero :=
  ⟨swap_no_fp, cZero_has_fp, swap_involutive.bijective, snap_irreversible⟩

end Pole
end ZeroParadox.Miniature

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox.Miniature ZeroParadox.Miniature.Pole
#print axioms lawvere
#print axioms negation_no_fp
#print axioms wall_of_fpf
#print axioms floor_of_witness
#print axioms card_four
#print axioms swap_is_the_wall
#print axioms miniature
end PurityCheck
