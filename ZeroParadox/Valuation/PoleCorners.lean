import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# The four corners: 0 and ∞ have exactly four representations to each other

## Engineer's Take

All four of those conditions should be met by one shape, and I wanted to know whether anything holds them
all. These are the only four cases for representing these items to each other, so it is a complete set. You
can transition from any one of the points to any other, and that encodes both mu and nu. We also know
exactly which direction we cannot make that transition on, and why, and that forbidden direction is the very
shape we keep hitting, the very definition of the snap.

This came as I tried to pin down whether the four ways zero and infinity meet form a closed and complete set.
Sometimes it helps to work through this from the ground up. Much of what is here re-derives results the
framework already has, and that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

The pole is the two-element type `Pole = {zero, infty}` — the framework's self-dual point `0 = ∞`
(`rInv_swaps`). A *representation of the poles to each other* is an endofunction `Pole → Pole`: where each
pole is sent. There are **exactly four** (`card_representations : Fintype.card (Pole → Pole) = 4`), and the
four named corners **exhaust** them (`four_corners_exhaustive`):

* `cornerZero`  — both poles to `0`  : the **zero pole**;
* `cornerInfty` — both poles to `∞`  : the **infinity pole**;
* `cornerId`    — each pole to itself : `0` and `∞` **concurrently**, unchanged;
* `swap`        — `0 ↔ ∞`            : the **inversion**, one after the other.

So the four conditions — zero pole, infinity pole, concurrent, inversion — are a **complete set**: they
exhaust the endofunctions of the pole-pair, proved by finite exhaustion. The `swap` is the finite shadow of
the Riemann-sphere inversion `rInv` (`swap_involutive` = the ℤ/2 symmetry, i.e. `rInv_involutive`;
`swap_swaps` = `rInv_swaps`).

**Honest scope.** The completeness is *elementary once the model is fixed* — there are `2² = 4` endofunctions
of a two-element set. The content is the identification of those four endofunctions with the four
pole-representations; the counting itself is `decide`. This does not prove that "endofunctions of the pole"
is the *only* reasonable model of "representation" — it proves that, under that model, the set is exactly
these four.

## Structure
- § I   `Pole` and the four named corners.
- § II  Completeness: exactly four, and the four exhaust them.
- § III The inversion as the ℤ/2 symmetry (finite shadow of `rInv`).
-/

namespace ZeroParadox

/-! ### § I. The pole and its four representations -/

/-- The pole: the two-element type `{0, ∞}` — the framework's self-dual point `0 = ∞`. -/
inductive Pole where
  | zero
  | infty
deriving DecidableEq, Fintype, Repr

namespace Pole

/-- Representation 1 — the **zero pole**: both poles collapse to `0`. -/
def cornerZero : Pole → Pole := fun _ => zero

/-- Representation 2 — the **infinity pole**: both poles collapse to `∞`. -/
def cornerInfty : Pole → Pole := fun _ => infty

/-- Representation 3 — **concurrent**: each pole stays itself; `0` and `∞` coexist, unchanged. -/
def cornerId : Pole → Pole := id

/-- Representation 4 — the **inversion** (one after the other): `0 ↔ ∞`. -/
def swap : Pole → Pole
  | zero => infty
  | infty => zero

/-! ### § II. Completeness — exactly four, and they exhaust the representations -/

/-- **Exactly four representations.** The endofunctions of the pole-pair number exactly four (`2² = 4`). -/
theorem card_representations : Fintype.card (Pole → Pole) = 4 := by decide

/-- **Completeness — the four corners exhaust the representations.** Every endofunction of the pole-pair is
one of the four: the zero pole, the infinity pole, the concurrent identity, or the inversion. The four
conditions are a complete set. -/
theorem four_corners_exhaustive (f : Pole → Pole) :
    f = cornerZero ∨ f = cornerInfty ∨ f = cornerId ∨ f = swap := by
  revert f; decide

/-- The four corners are pairwise distinct — four genuinely different representations. -/
theorem four_corners_distinct :
    cornerZero ≠ cornerInfty ∧ cornerZero ≠ cornerId ∧ cornerZero ≠ swap ∧
      cornerInfty ≠ cornerId ∧ cornerInfty ≠ swap ∧ cornerId ≠ swap := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### § III. The inversion as the ℤ/2 symmetry (finite shadow of `rInv`) -/

/-- The inversion is an involution — the ℤ/2 symmetry; the finite shadow of `rInv_involutive`. -/
theorem swap_involutive : Function.Involutive swap := by
  intro x; cases x <;> rfl

/-- The inversion swaps the two poles — the finite shadow of `rInv_swaps` (`0 ↔ ∞`). -/
theorem swap_swaps : swap zero = infty ∧ swap infty = zero := ⟨rfl, rfl⟩

/-! ### § IV. The reversibility split — the symmetries reverse, the collapses do not (the snap direction)

The four corners are not on equal footing. The two **symmetries** (`cornerId`, `swap`) are bijections — you
can undo them; they are the ν-side, the reversible inversion. The two **collapses** (`cornerZero`,
`cornerInfty`) send both poles to one pole: they are **not injective**, the input is forgotten, there is no
inverse — the μ-side, the **one-way direction**. This is the finite shape of the snap's irreversibility:
you can fall to the floor, you cannot climb back out the way you came (`t_snap_irreversible` — no join from
ε₀ returns to ⊥; `PoleCornersBridge` co-witnesses the identification). The forbidden direction is not a gap
in the structure; it is the snap. -/

/-- The concurrent corner is **reversible**: `cornerId` is a bijection. -/
theorem cornerId_bijective : Function.Bijective cornerId := by
  unfold cornerId; exact Function.bijective_id

/-- The inversion corner is **reversible**: `swap` is a bijection (an involution). -/
theorem swap_bijective : Function.Bijective swap := swap_involutive.bijective

/-- The zero corner is **irreversible**: `cornerZero` collapses both poles to `0`, so it is not injective —
the origin is forgotten, no inverse exists. The one-way direction. -/
theorem cornerZero_not_injective : ¬ Function.Injective cornerZero := by
  intro h
  exact absurd (@h zero infty rfl) (by decide)

/-- The infinity corner is **irreversible**: `cornerInfty` collapses both poles to `∞`, not injective. -/
theorem cornerInfty_not_injective : ¬ Function.Injective cornerInfty := by
  intro h
  exact absurd (@h zero infty rfl) (by decide)

/-- **The reversibility split.** Of the four corners, the two symmetries (`cornerId`, `swap`) are bijections
— reversible (the ν-inversion); the two collapses (`cornerZero`, `cornerInfty`) are not injective —
irreversible (the μ-collapse to a pole, the one-way snap direction). -/
theorem reversibility_split :
    Function.Bijective cornerId ∧ Function.Bijective swap ∧
      ¬ Function.Injective cornerZero ∧ ¬ Function.Injective cornerInfty :=
  ⟨cornerId_bijective, swap_bijective, cornerZero_not_injective, cornerInfty_not_injective⟩

end Pole
end ZeroParadox

section PurityCheck
open ZeroParadox.Pole
#print axioms card_representations
#print axioms four_corners_exhaustive
#print axioms four_corners_distinct
#print axioms swap_involutive
#print axioms reversibility_split
end PurityCheck
