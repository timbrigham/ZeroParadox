-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Die
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
  cases hz : f zero <;> cases hi : f infty
  · exact Or.inl (funext fun x => by cases x <;> simp [cornerZero, hz, hi])
  · exact Or.inr (Or.inr (Or.inl (funext fun x => by cases x <;> simp [cornerId, hz, hi])))
  · exact Or.inr (Or.inr (Or.inr (funext fun x => by cases x <;> simp [swap, hz, hi])))
  · exact Or.inr (Or.inl (funext fun x => by cases x <;> simp [cornerInfty, hz, hi]))

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

/-! ### § V. The corners as die motions (`ZeroParadox/Die.lean`)

The two trap sets of a motion are written out: "no entry from elsewhere" is `∀ a, step a y → a = y`,
"no exit elsewhere" is `∀ b, step y b → b = y`. -/

open Motion

/-- `Statement:` in `ofFun cornerZero`: `zero` steps to itself only, `infty` steps elsewhere; a step
    into `zero` starts elsewhere, every step into `infty` starts at `infty`; every step out of `zero`
    ends at `zero`, a step out of `infty` ends elsewhere; `zero` has fan-in, `infty` does not; every
    point arrives at `zero`; a point arrives at `infty` iff it is `infty`; `cornerZero` is not
    one-to-one. -/
theorem cornerZero_cells :
    (ofFun cornerZero).SelfOnlyAt zero ∧ (ofFun cornerZero).LeavesAt infty ∧
    ¬ (∀ a, (ofFun cornerZero).step a zero → a = zero) ∧
    (∀ a, (ofFun cornerZero).step a infty → a = infty) ∧
    (∀ b, (ofFun cornerZero).step zero b → b = zero) ∧
    ¬ (∀ b, (ofFun cornerZero).step infty b → b = infty) ∧
    (ofFun cornerZero).FanIn zero ∧ ¬ (ofFun cornerZero).FanIn infty ∧
    (∀ x, (ofFun cornerZero).Arrives zero x) ∧
    (∀ x, (ofFun cornerZero).Arrives infty x ↔ x = infty) ∧
    ¬ Function.Injective cornerZero := by
  refine ⟨(selfOnlyAt_ofFun_iff _ _).2 rfl, (leavesAt_ofFun_iff _ _).2 (by intro h; cases h),
    fun h => absurd (h infty rfl) (by intro h; cases h),
    fun a (h : infty = zero) => (by cases h), fun b (h : b = zero) => h,
    fun h => absurd (h zero rfl) (by intro h; cases h),
    ⟨zero, infty, (by intro h; cases h), rfl, rfl⟩, ?_,
    fun x => (arrives_ofFun_iff _ _ _).2 ⟨1, rfl⟩, fun x => ?_, cornerZero_not_injective⟩
  · rintro ⟨a, b, hab, (ha : infty = zero), hb⟩
    cases ha
  · rw [arrives_ofFun_iff]
    refine ⟨fun ⟨n, hn⟩ => ?_, fun h => ⟨0, h⟩⟩
    cases n with
    | zero => exact hn
    | succ n =>
      rw [Function.iterate_succ_apply'] at hn
      cases (hn : zero = infty)

/-- `Statement:` the same cells for `ofFun cornerInfty`, with `zero` and `infty` exchanged. -/
theorem cornerInfty_cells :
    (ofFun cornerInfty).SelfOnlyAt infty ∧ (ofFun cornerInfty).LeavesAt zero ∧
    ¬ (∀ a, (ofFun cornerInfty).step a infty → a = infty) ∧
    (∀ a, (ofFun cornerInfty).step a zero → a = zero) ∧
    (∀ b, (ofFun cornerInfty).step infty b → b = infty) ∧
    ¬ (∀ b, (ofFun cornerInfty).step zero b → b = zero) ∧
    (ofFun cornerInfty).FanIn infty ∧ ¬ (ofFun cornerInfty).FanIn zero ∧
    (∀ x, (ofFun cornerInfty).Arrives infty x) ∧
    (∀ x, (ofFun cornerInfty).Arrives zero x ↔ x = zero) ∧
    ¬ Function.Injective cornerInfty := by
  refine ⟨(selfOnlyAt_ofFun_iff _ _).2 rfl, (leavesAt_ofFun_iff _ _).2 (by intro h; cases h),
    fun h => absurd (h zero rfl) (by intro h; cases h),
    fun a (h : zero = infty) => (by cases h), fun b (h : b = infty) => h,
    fun h => absurd (h infty rfl) (by intro h; cases h),
    ⟨zero, infty, (by intro h; cases h), rfl, rfl⟩, ?_,
    fun x => (arrives_ofFun_iff _ _ _).2 ⟨1, rfl⟩, fun x => ?_, cornerInfty_not_injective⟩
  · rintro ⟨a, b, hab, (ha : zero = infty), hb⟩
    cases ha
  · rw [arrives_ofFun_iff]
    refine ⟨fun ⟨n, hn⟩ => ?_, fun h => ⟨0, h⟩⟩
    cases n with
    | zero => exact hn
    | succ n =>
      rw [Function.iterate_succ_apply'] at hn
      cases (hn : infty = zero)

/-- `Statement:` in `ofFun cornerId` every point steps to itself only, is in both trap sets, and has
    no fan-in; `x` arrives at `y` iff `x = y`; `cornerId` is one-to-one. -/
theorem cornerId_cells :
    (∀ y, (ofFun cornerId).SelfOnlyAt y) ∧ (∀ y a, (ofFun cornerId).step a y → a = y) ∧
    (∀ y b, (ofFun cornerId).step y b → b = y) ∧ (∀ y, ¬ (ofFun cornerId).FanIn y) ∧
    (∀ x y, (ofFun cornerId).Arrives y x ↔ x = y) ∧ Function.Injective cornerId := by
  refine ⟨fun y => (selfOnlyAt_ofFun_iff _ _).2 rfl, fun y a (h : y = a) => h.symm,
    fun y b (h : b = y) => h,
    fun y => not_fanIn_of_injective cornerId cornerId_bijective.1 (fun _ _ => Iff.rfl) y,
    fun x y => ?_, cornerId_bijective.1⟩
  rw [arrives_ofFun_iff]
  refine ⟨fun ⟨n, hn⟩ => ?_, fun h => ⟨0, h⟩⟩
  rwa [show cornerId = id from rfl, Function.iterate_id] at hn

/-- `Statement:` in `ofFun swap` every point steps elsewhere, neither trap set has a member, no point
    has fan-in, and every point arrives at every point; `swap` is one-to-one. -/
theorem swap_cells :
    (∀ y, (ofFun swap).LeavesAt y) ∧ (∀ y, ¬ ∀ a, (ofFun swap).step a y → a = y) ∧
    (∀ y, ¬ ∀ b, (ofFun swap).step y b → b = y) ∧ (∀ y, ¬ (ofFun swap).FanIn y) ∧
    (∀ x y, (ofFun swap).Arrives y x) ∧ Function.Injective swap := by
  refine ⟨fun y => (leavesAt_ofFun_iff _ _).2 (by cases y <;> intro h <;> cases h),
    fun y h => ?_, fun y h => ?_,
    fun y => not_fanIn_of_injective swap swap_bijective.1 (fun _ _ => Iff.rfl) y,
    fun x y => (arrives_ofFun_iff _ _ _).2 ?_, swap_bijective.1⟩
  · cases y
    · exact absurd (h infty rfl) (by intro h; cases h)
    · exact absurd (h zero rfl) (by intro h; cases h)
  · cases y
    · exact absurd (h infty rfl) (by intro h; cases h)
    · exact absurd (h zero rfl) (by intro h; cases h)
  · cases x <;> cases y
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- `Statement:` for `f g : Pole → Pole`, if `ofFun f` and `ofFun g` have the same points stepping to
    themselves only, then `f = g`. -/
theorem eq_of_selfOnlyAt_iff (f g : Pole → Pole)
    (h : ∀ y, (ofFun f).SelfOnlyAt y ↔ (ofFun g).SelfOnlyAt y) : f = g := by
  simp only [selfOnlyAt_ofFun_iff] at h
  funext y
  have hy := h y
  cases y <;> cases hf : f _ <;> cases hg : g _ <;> simp_all

/-- `Statement:` the set of points stepping to themselves only names the corner: `{zero}` gives
    `cornerZero`, `{infty}` gives `cornerInfty`, every point gives `cornerId`, no point gives `swap`. -/
theorem corner_of_selfOnlyAt (f : Pole → Pole) :
    ((∀ y, (ofFun f).SelfOnlyAt y ↔ y = zero) → f = cornerZero) ∧
    ((∀ y, (ofFun f).SelfOnlyAt y ↔ y = infty) → f = cornerInfty) ∧
    ((∀ y, (ofFun f).SelfOnlyAt y) → f = cornerId) ∧
    ((∀ y, ¬ (ofFun f).SelfOnlyAt y) → f = swap) := by
  refine ⟨fun h => eq_of_selfOnlyAt_iff _ _ fun y => (h y).trans ?_,
    fun h => eq_of_selfOnlyAt_iff _ _ fun y => (h y).trans ?_,
    fun h => eq_of_selfOnlyAt_iff _ _ fun y => iff_of_true (h y) ((selfOnlyAt_ofFun_iff _ _).2 rfl),
    fun h => eq_of_selfOnlyAt_iff _ _ fun y => iff_of_false (h y) ?_⟩
  · rw [selfOnlyAt_ofFun_iff]; cases y <;> simp [cornerZero]
  · rw [selfOnlyAt_ofFun_iff]; cases y <;> simp [cornerInfty]
  · rw [selfOnlyAt_ofFun_iff]; cases y <;> simp [swap]

/-- `Statement:` conjugating by `swap` exchanges `cornerZero` and `cornerInfty` and keeps `cornerId`
    and `swap`. -/
theorem swap_conj :
    swap ∘ cornerZero ∘ swap = cornerInfty ∧ swap ∘ cornerInfty ∘ swap = cornerZero ∧
    swap ∘ cornerId ∘ swap = cornerId ∧ swap ∘ swap ∘ swap = swap :=
  ⟨funext fun x => by cases x <;> rfl, funext fun x => by cases x <;> rfl,
    funext fun x => by cases x <;> rfl, funext fun x => by cases x <;> rfl⟩

/-- `Statement:` `swap` is a relation isomorphism (Mathlib `RelIso`) from the steps of
    `ofFun cornerZero` to the steps of `ofFun cornerInfty`. `Reading:` an EXCHANGE witness: the two
    collapse targets `zero` and `infty` are distinct points carried onto each other, as `rInv_swaps`
    exchanges 0 and ∞ on the sphere; not the coincidence witness. -/
def zeroInftyIso : (ofFun cornerZero).step ≃r (ofFun cornerInfty).step where
  toEquiv := ⟨swap, swap, swap_involutive.leftInverse, swap_involutive.rightInverse⟩
  map_rel_iff' := by
    intro a b
    show swap b = cornerInfty (swap a) ↔ b = cornerZero a
    cases a <;> cases b <;> simp [swap, cornerInfty, cornerZero]

/-- `Statement:` no relation isomorphism from the steps of `ofFun cornerId` to those of `ofFun swap`. -/
theorem not_iso_id_swap : IsEmpty ((ofFun cornerId).step ≃r (ofFun swap).step) :=
  ⟨fun e => by
    have h := (fixed_iff_of_relIso e zero).1 rfl
    generalize e zero = q at h
    cases q <;> simp [swap] at h⟩

/-- `Statement:` no relation isomorphism from the steps of `ofFun swap` to those of
    `ofFun cornerZero`. -/
theorem not_iso_swap_zero : IsEmpty ((ofFun swap).step ≃r (ofFun cornerZero).step) :=
  ⟨fun e => by
    have h := (fixed_iff_of_relIso e.symm zero).1 rfl
    generalize e.symm zero = q at h
    cases q <;> simp [swap] at h⟩

/-- `Statement:` no relation isomorphism from the steps of `ofFun cornerId` to those of
    `ofFun cornerZero`. -/
theorem not_iso_id_zero : IsEmpty ((ofFun cornerId).step ≃r (ofFun cornerZero).step) :=
  ⟨fun e => by
    have h0 := (fixed_iff_of_relIso e zero).1 rfl
    have h1 := (fixed_iff_of_relIso e infty).1 rfl
    have : zero = infty := e.injective (h0.symm.trans h1)
    cases this⟩

/-- `Statement:` up to relation isomorphism of the steps, the motions `ofFun f` for `f : Pole → Pole`
    fall in three classes, represented by `cornerId`, `swap` and `cornerZero`; `cornerInfty` is in
    the class of `cornerZero`; the three representatives are pairwise not isomorphic. `Reading:`
    EXCHANGE, as `zeroInftyIso`: the two collapses differ only in which point is named the target. -/
theorem three_classes :
    Nonempty ((ofFun cornerInfty).step ≃r (ofFun cornerZero).step) ∧
    IsEmpty ((ofFun cornerId).step ≃r (ofFun swap).step) ∧
    IsEmpty ((ofFun swap).step ≃r (ofFun cornerZero).step) ∧
    IsEmpty ((ofFun cornerId).step ≃r (ofFun cornerZero).step) ∧
    ∀ f : Pole → Pole, Nonempty ((ofFun f).step ≃r (ofFun cornerId).step) ∨
      Nonempty ((ofFun f).step ≃r (ofFun swap).step) ∨
      Nonempty ((ofFun f).step ≃r (ofFun cornerZero).step) := by
  refine ⟨⟨zeroInftyIso.symm⟩, not_iso_id_swap, not_iso_swap_zero, not_iso_id_zero, fun f => ?_⟩
  rcases four_corners_exhaustive f with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr ⟨RelIso.refl _⟩)
  · exact Or.inr (Or.inr ⟨zeroInftyIso.symm⟩)
  · exact Or.inl ⟨RelIso.refl _⟩
  · exact Or.inr (Or.inl ⟨RelIso.refl _⟩)

/-- `Statement:` `zero ↦ 0`, `infty ↦ 1`. -/
def poleRank : Pole → ℕ
  | zero => 0
  | infty => 1

/-- `Statement:` the view `zero ≤ infty`: the preorder lifted along `poleRank`. -/
abbrev poleView : Preorder Pole := Preorder.lift poleRank

/-- `Statement:` the view lifted along `poleRank ∘ swap`. -/
abbrev poleViewSwap : Preorder Pole := Preorder.lift (poleRank ∘ swap)

/-- `Statement:` `poleViewSwap` is `poleView` reversed: `x ≤ y` in the first iff `y ≤ x` in the
    second. -/
theorem poleView_swap_dual (x y : Pole) : poleViewSwap.le x y ↔ poleView.le y x := by
  show poleRank (swap x) ≤ poleRank (swap y) ↔ poleRank y ≤ poleRank x
  cases x <;> cases y <;> decide

/-- `Statement:` under `poleView`, OVER of `ofFun cornerZero` lowers and does not raise, OVER of
    `ofFun cornerInfty` raises and does not lower, `ofFun cornerId` does both, `ofFun swap` neither. -/
theorem corner_polarity :
    @StepLowers Pole (ofFun cornerZero) poleView.toLE ∧
    ¬ @StepRaises Pole (ofFun cornerZero) poleView.toLE ∧
    @StepRaises Pole (ofFun cornerInfty) poleView.toLE ∧
    ¬ @StepLowers Pole (ofFun cornerInfty) poleView.toLE ∧
    (@StepRaises Pole (ofFun cornerId) poleView.toLE ∧
      @StepLowers Pole (ofFun cornerId) poleView.toLE) ∧
    (¬ @StepRaises Pole (ofFun swap) poleView.toLE ∧
      ¬ @StepLowers Pole (ofFun swap) poleView.toLE) := by
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro x y rfl; show poleRank zero ≤ poleRank x; cases x <;> decide
  · intro h; exact absurd (h infty zero rfl) (by decide)
  · rintro x y rfl; show poleRank x ≤ poleRank infty; cases x <;> decide
  · intro h; exact absurd (h zero infty rfl) (by decide)
  · intro x y h; show poleRank x ≤ poleRank y; rw [h]; exact Nat.le_refl _
  · intro x y h; show poleRank y ≤ poleRank x; rw [h]; exact Nat.le_refl _
  · intro h; exact absurd (h infty zero rfl) (by decide)
  · intro h; exact absurd (h zero infty rfl) (by decide)

/-- `Statement:` for every motion on `Pole`, OVER raises under `poleViewSwap` iff it lowers under
    `poleView` (`stepRaises_iff_of_dual`). -/
theorem pole_polarity_swap (M : Motion Pole) :
    @StepRaises Pole M poleViewSwap.toLE ↔ @StepLowers Pole M poleView.toLE :=
  stepRaises_iff_of_dual poleView.toLE poleViewSwap.toLE poleView_swap_dual M

/-- `Statement:` under `poleView`, `Pole` is in the both-ends cell of `PoleEnds`, with `zero` least,
    `infty` greatest, and `zero ≠ infty`. -/
theorem poleView_ends :
    @PoleEnds Pole poleView.toLE true true ∧ @IsBot Pole poleView.toLE zero ∧
    @IsTop Pole poleView.toLE infty ∧ zero ≠ infty := by
  have hb : @IsBot Pole poleView.toLE zero := fun y =>
    show poleRank zero ≤ poleRank y by cases y <;> decide
  have ht : @IsTop Pole poleView.toLE infty := fun y =>
    show poleRank y ≤ poleRank infty by cases y <;> decide
  exact ⟨⟨⟨fun _ => rfl, fun _ => ⟨_, hb⟩⟩, ⟨fun _ => rfl, fun _ => ⟨_, ht⟩⟩⟩, hb, ht,
    fun h => by cases h⟩

/-- `Statement:` under `poleViewSwap`, `Pole` is in the both-ends cell, with `infty` least and `zero`
    greatest. -/
theorem poleView_swap_ends :
    @PoleEnds Pole poleViewSwap.toLE true true ∧ @IsBot Pole poleViewSwap.toLE infty ∧
    @IsTop Pole poleViewSwap.toLE zero :=
  ⟨(poleEnds_of_dual poleView.toLE _ poleView_swap_dual true true).2 poleView_ends.1,
    fun y => (poleView_swap_dual _ y).2 (poleView_ends.2.2.1 y),
    fun y => (poleView_swap_dual y _).2 (poleView_ends.2.1 y)⟩

-- The `DecidableEq` binder is kept in the type on purpose: the map to `Pole` cases on `x = a`, and
-- the PurityCheck prints the footprint that binder buys.
set_option linter.unusedDecidableInType false in
/-- `Statement:` if a partial order with decidable equality has a least point `a`, a greatest point
    `b ≠ a`, and every point is `a` or `b`, an equivalence with `Pole` sends `a` to `zero`, `b` to
    `infty`, and preserves and reflects `≤` against `poleView`. -/
theorem two_point_both_ends_is_poleView {α : Type*} [PartialOrder α] [DecidableEq α] {a b : α}
    (ha : IsBot a) (hb : IsTop b) (hab : a ≠ b) (h2 : ∀ x, x = a ∨ x = b) :
    ∃ e : α ≃ Pole, e a = zero ∧ e b = infty ∧ ∀ x y, x ≤ y ↔ poleView.le (e x) (e y) := by
  let f : α → Pole := fun x => if x = a then zero else infty
  let g : Pole → α := fun p => match p with
    | zero => a
    | infty => b
  have hfa : f a = zero := if_pos rfl
  have hfb : f b = infty := if_neg (Ne.symm hab)
  refine ⟨⟨f, g, fun x => ?_, fun p => ?_⟩, hfa, hfb, fun x y => ?_⟩
  · rcases h2 x with rfl | rfl
    · rw [hfa]
    · rw [hfb]
  · cases p
    · exact hfa
    · exact hfb
  · show x ≤ y ↔ poleRank (f x) ≤ poleRank (f y)
    rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl
    · rw [hfa]; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
    · rw [hfa, hfb]; exact ⟨fun _ => by decide, fun _ => ha _⟩
    · rw [hfa, hfb]
      exact ⟨fun h => absurd (le_antisymm (hb _) h) hab, fun h => absurd h (by decide)⟩
    · rw [hfb]; exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩

end Pole
end ZeroParadox

section PurityCheck
open ZeroParadox.Pole
#print axioms card_representations
#print axioms four_corners_exhaustive
#print axioms four_corners_distinct
#print axioms swap_involutive
#print axioms reversibility_split
#print axioms cornerZero_cells
#print axioms cornerInfty_cells
#print axioms cornerId_cells
#print axioms swap_cells
#print axioms eq_of_selfOnlyAt_iff
#print axioms corner_of_selfOnlyAt
#print axioms swap_conj
#print axioms zeroInftyIso
#print axioms not_iso_id_swap
#print axioms not_iso_swap_zero
#print axioms not_iso_id_zero
#print axioms three_classes
#print axioms poleRank
#print axioms poleView
#print axioms poleViewSwap
#print axioms poleView_swap_dual
#print axioms corner_polarity
#print axioms pole_polarity_swap
#print axioms poleView_ends
#print axioms poleView_swap_ends
#print axioms two_point_both_ends_is_poleView
end PurityCheck
