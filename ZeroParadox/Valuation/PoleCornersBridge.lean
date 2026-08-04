-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCorners
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Order.Snap
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Bridge: the four corners are the corners of the tower to ω (shared-shape correspondence)

## Engineer's Take

Looking at it from the top down, this is the very same single point versus an infinite field that we started
out looking at. These four corners are the corners of the whole tower to omega, and the inversion corner is
the framework's own bridge map. The one direction we cannot reverse is the definition of the snap, and it is
the same wall we kept hitting from the start.

This landed when I looked at it from the top down and saw the same single point versus infinite field we
started with. Sometimes it helps to work through this from the ground up. Much of what is here re-derives
results the framework already has, and that is fine. The movement of the thought process itself was what I
needed.

---

## Formal Overview (AI-assisted)

Ties the abstract four corners (`PoleCorners`) to the framework's 2-adic inversion and, through it, to the
ω-tower to ε₀ (`Ordinal/CnfBridge.lean`).

**The genuine Lean content is `swap_is_rInv`:** under the pole embedding `poleToSphere : Pole → Sphere`
(`zero ↦ 0`, `infty ↦ ∞`), the abstract inversion corner `Pole.swap` commutes with the Riemann-sphere
inversion `rInv` — the four-corner inversion **is** the framework's `z ↦ 1/z`, swapping the floor `0` and
the point at infinity. So the corner that flips the two poles is not decoration: it is the framework's
actual inversion map, at the finite level.

**The tower correspondence is SHARED-SHAPE, not identity** (honoring the type fence
`cnf_bridge_type_boundary`). The tower ↔ tree link is already built in `CnfBridge`:
* the ω-tower `towerNONote` ascends (via `NONote.repr`) to **ε₀**, and its 2-adic images (via `cnfToZp2`)
  **descend in norm to `0 = ⊥`** — one construction, two carrier closures (`mu_construction_correspondence`);
* `cnfToZp2` is order-reflecting along the tower: ordinal height climbs = 2-adic norm falls. **That
  order-reversal is exactly the inversion corner** — `swap` / `rInv` at the abstract level.

So the four corners map onto the tower's corners: the **zero** corner is the tower's seed and the tree's
`botEnd` (`seed_maps_to_bot_both`: `cnfToZp2 (towerNONote 0) = 0`); the **infinity** corner is that seed's
image under the inversion; **concurrent** is the pole `0 = ∞ = ⊥` where ascent and descent meet; and the
**inversion** corner is `cnfToZp2`'s ordinal-ascent-↔-2-adic-descent reversal, i.e. the tower→tree map
itself. No cross-type `ε₀ = 0` is asserted anywhere — the corners and the tower are connected by MAPS
(`poleToSphere`, `rInv`, `cnfToZp2`), never by `=`.

**The INFINITY corner is measured elsewhere, and this file did not say so** (pointer added 2026-08-04;
`InfinitudeFloor` had **zero** mentions here despite both files working the same tower). The corner is
not prose — it is a class with theorems, in `ZeroParadox/Valuation/InfinitudeFloor.lean`:

* `InfinitudeFloor α` bundles a `floor : α` with a **complexity** `cx : α → ℕ∞` and a member sequence.
* `infinitude_forces_infinite_complexity : I.cx I.floor = ⊤` — **the top is ATTAINED, and it is
  attained AT THE FLOOR.** That is the `0 = ∞` pole identity as a measured statement rather than a
  slogan: the point of infinite complexity *is* the bottom.
* `infinite_complexity_is_infinitude_of_zeros : I.cx I.floor = ⨆ n, I.cx (I.member n)` — the floor's
  complexity is the supremum of its members'.
* `pole_inversion` — members descend to the floor **as elements** while their complexity ascends to
  `⊤`; the **DRIFT** kind (two measures running opposite along one sequence). ⚠ It needs the
  *extending* class `InfinitudeFloorInversion` plus a topology, and its "members descend" half is a
  **class field** (`member_tendsto_floor`), an assumption rather than a consequence. Instances exist
  on `ℕ∞` (the toy) and `Q₂` only — **there is none on `ℤ_[2]`**, so `pole_inversion` is *not*
  available on this file's own tower. It is a *shape* alongside § II's `swap_is_rInv` (an INVERSION),
  not the same claim: DRIFT and INVERSION are distinct POV kinds and no theorem identifies them.
* What IS available on this file's own tower, in `ZeroParadox/Valuation/TowerHeightFloor.lean`:
  `towerCx_zero : towerCx (0 : ℤ_[2]) = ⊤` and
  `towerCx_member (n) : towerCx (cnfToZp2 (towerNONote (n+1))) = ((n+1 : ℕ) : ℕ∞)`. So the zero corner
  (`seed_maps_to_bot_both`) and the infinity corner (`towerCx_zero`) are witnessed on the *same*
  `cnfToZp2 ∘ towerNONote` this file discusses throughout (in prose — `cnfToZp2` is not imported here).

`Reading:` with both corners measured, `cornerId` — the "concurrent" corner — stops being a phrase:
one index, an element-descent and a complexity-ascent, each reaching its own pole. **Co-witnessed
only.** The corners live in `Pole`/`Sphere` and the complexities in `ℕ∞`; nothing here asserts a
cross-type `=`, exactly as `cnf_bridge_type_boundary` fences the tower. Note the direction of
`infinitude_forces_infinite_complexity`: it says the floor HAS complexity `⊤`. It does **not** say
`⊤` is attained only at the floor — the abstract class gives no such uniqueness.

**⚠ SCOPE — what the class actually requires, stated from its fields rather than inferred.**
`InfinitudeFloor` asks for a `floor`, a complexity `cx : α → ℕ∞`, a `member : ℕ → α`, and the two
conditions `member_ne_floor` and **`cx_member_strictMono`**. That last one is a **CHAIN condition** —
the members' complexities climb strictly — and it is the whole requirement. **The class imposes no
valuation axioms whatsoever**, so "a carrier needs a valuation" is NOT a consequence of the class.

Realizations located 2026-08-04 (**five**, and the count is a measurement at a date, not a census):

| carrier | `cx` is | where |
|---|---|---|
| `Q₂` | the 2-adic valuation | `InfinitudeFloor.lean` `q2InfinitudeFloor` |
| `ℤ_[2]` | `towerCx`, the tower height | `TowerHeightFloor.lean` `towerInfinitudeFloor` (`@[reducible] def`, deliberately not a global instance) |
| `PowerSeries R` | `PowerSeries.order` | `InfinitudeFloor.lean` `powerSeriesInfinitudeFloor` |
| `End` | `localCx v`, per node | `LocalFloor.lean` `boundaryFloor` — a **`List (Fin 2)`-indexed family** (one witness per tree node, a `def` not a global instance) |
| `ℕ∞` | `id` | `InfinitudeFloor.lean` — the file's own docstring calls this a **"Toy witness … Degenerate"**, included only to show the requirements are inhabitable |

`Reading:` (framework interpretation, **conjectural**, not a theorem) — four of the five carry a
genuine valuation, and the degenerate fifth is labelled as such by its author, which *suggests* a
valuation is what supplies a climbing complexity chain in practice. **That is a pattern across five
witnesses, not a structural necessity**, and `cx = id` is the standing counterexample to stating it
as one.

**⚠ NO REALIZATION HAS BEEN GIVEN at the Kleisli initial object, the Hilbert zero object, the ordinal
floor, or the Markov attractor as of 2026-08-04** — a measurement, deliberately not the stronger
claim that none *can* be. Nothing in the class forbids one: any complexity map with a strictly
climbing member chain would do, and whether a categorical bottom admits one is **open and untried
here**. *(An earlier version of this block asserted four realizations, called them all
valuation-carrying, and stated the negative structurally — "none of which carries a complexity map".
All three were wrong: the fifth realization was missed, row 5 is `id`, and the class requires a chain
rather than a valuation. Corrected 2026-08-04.)*

## Structure
- § I   `poleToSphere` — the pole embedding into the 2-adic Riemann sphere.
- § II  `swap_is_rInv` — the inversion corner is `rInv` (the genuine bridge content).
- § III `point_and_field_at_the_poles` — the point/field inversion at the two poles.
- § IV  `irreversible_direction_is_the_snap` — the one-way direction, co-witnessed with `t_snap_irreversible`.

*(The overview above previously said "the genuine Lean content is `swap_is_rInv`" full stop; the file
carries one `def` and six theorems — the four listed above plus the two `@[simp]` `rfl`-lemmas
`poleToSphere_zero` / `poleToSphere_infty` — and § III / § IV were unlisted. Corrected 2026-08-04.)*
-/

namespace ZeroParadox

open OnePoint

/-! ### § I. The pole embedding into the 2-adic Riemann sphere -/

/-- Embed the abstract pole-pair into the 2-adic Riemann sphere: `zero ↦ 0`, `infty ↦ ∞`. The floor and
its antipode; the two poles the whole four-corner structure is about. -/
noncomputable def poleToSphere : Pole → Sphere
  | Pole.zero => OnePoint.some (0 : ℚ_[2])
  | Pole.infty => (∞ : Sphere)

@[simp] theorem poleToSphere_zero : poleToSphere Pole.zero = OnePoint.some (0 : ℚ_[2]) := rfl

@[simp] theorem poleToSphere_infty : poleToSphere Pole.infty = (∞ : Sphere) := rfl

/-! ### § II. The inversion corner IS the Riemann-sphere inversion -/

/-- **The inversion corner is `z ↦ 1/z`.** Under the pole embedding, the abstract `swap` corner commutes
with the Riemann-sphere inversion `rInv`: `poleToSphere (swap p) = rInv (poleToSphere p)`. The four-corner
inversion is the framework's own `rInv` — the map that, on the tower side (`cnfToZp2`), reverses ordinal
ascent into 2-adic descent. The corner that connects the two poles is the map that connects the tower to the
tree. -/
theorem swap_is_rInv (p : Pole) : poleToSphere (Pole.swap p) = rInv (poleToSphere p) := by
  cases p <;> simp [poleToSphere, Pole.swap, rInv_zero, rInv_infty]

/-- The floor corner and the infinity corner are genuinely the two swapped poles: `swap` moves the zero
corner to `∞` and the infinity corner to `0`, exactly as `rInv_swaps` does on the sphere. -/
theorem corners_are_the_swapped_poles :
    poleToSphere (Pole.swap Pole.zero) = (∞ : Sphere) ∧
      poleToSphere (Pole.swap Pole.infty) = OnePoint.some (0 : ℚ_[2]) := by
  constructor <;> rfl

/-! ### § III. The capstone — a single point versus an infinite field, at both poles at once -/

/-- **The capstone (co-witnessing, shared-shape).** The structure the whole pivot turned on: **two single,
distinct points — the poles — swapped by the inversion, sitting in an infinite field.** That is the "single
point versus infinite field" seen at BOTH ends at once. On the 2-adic sphere: `0` (the floor; the tower's
2-adic limit, `tower_converges_to_zero`) and `∞` (its inversion; the summit side) are the two single points;
`rInv` swaps them; and `ℚ_[2]` is the infinite field between. Via `cnfToZp2` (`CnfBridge`) the **top-down**
view — summit `ε₀` (a single point), tree boundary `ℤ₂` (a field) — is the **inverted image** of the
**bottom-up** view — floor `0` (a single point), its field. One construction, two ends, joined by the map,
never by `=`: `ε₀ = 0` stays a type boundary (`cnf_bridge_type_boundary`). The point and the field are the
same object read up or down; the inversion is what turns each into the other. -/
theorem point_and_field_at_the_poles :
    poleToSphere Pole.zero ≠ poleToSphere Pole.infty ∧
      rInv (poleToSphere Pole.zero) = poleToSphere Pole.infty ∧
      rInv (poleToSphere Pole.infty) = poleToSphere Pole.zero ∧
      Infinite ℚ_[2] := by
  refine ⟨?_, ?_, ?_, inferInstance⟩
  · simp [poleToSphere]
  · simp [poleToSphere, rInv_zero]
  · simp [poleToSphere, rInv_infty]

/-! ### § IV. The forbidden direction is the snap (co-witness, shared-shape) -/

/-- **The irreversible direction is the snap.** The two proved one-way facts, sharing one shape:
* **corner side** — `cornerZero` is not injective: falling to a pole forgets the origin, there is no inverse
  (the forbidden transition among the four corners is *un-collapsing*);
* **snap side** — `t_snap_irreversible`: once `x ≼ y` with `x ≠ y`, no join from `y` returns to `x` (the
  forbidden transition of the snap is *returning to the same ⊥*).

These are the same one-way shape on two structures. It is the wall the whole abstraction is bounded by:
everything reversible is free (the ν-symmetries `cornerId`, `swap`); the one thing you cannot reverse is the
fall to the floor. The forbidden direction is not a gap — it is the definition of the snap. Co-witnessed,
never a cross-type `=`. -/
theorem irreversible_direction_is_the_snap {L : Type*} [ZPSemilattice L] {x y : L}
    (hle : ZPSemilattice.join x y = y) (hne : x ≠ y) :
    ¬ Function.Injective Pole.cornerZero ∧ ¬ ∃ z : L, ZPSemilattice.join y z = x :=
  ⟨Pole.cornerZero_not_injective, t_snap_irreversible hle hne⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms poleToSphere
#print axioms swap_is_rInv
#print axioms corners_are_the_swapped_poles
#print axioms point_and_field_at_the_poles
#print axioms irreversible_direction_is_the_snap
end PurityCheck
