# The four corners and the tower to omega: how the shared shape was assembled

Ride-along documentation for [`ZeroParadox/Valuation/PoleCornersBridge.lean`](PoleCornersBridge.lean).
The Lean file holds the declarations and a statement per declaration; this document holds the
correspondence argument, its fences and its structure. Where the two would overlap, **the Lean is
authoritative**.

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

**The INFINITY corner is measured elsewhere, and the Lean file did not say so** (pointer added 2026-08-04;
`InfinitudeFloor` had **zero** mentions here despite both files working the same tower). The corner is
not prose — it is a class with theorems, in `ZeroParadox/Valuation/InfinitudeFloor.lean`:

* `InfinitudeFloor α` bundles a `floor : α` with a **complexity** `cx : α → ℕ∞` and a member sequence.
* `infinite_complexity_is_infinitude_of_zeros : I.cx I.floor = ⨆ n, I.cx (I.member n)` — the floor's
  complexity is the supremum of its members'. This is the field `cx_floor_eq_iSup` projected out, so
  it is a **requirement of the class**, not a consequence of the others.
* `Statement:` **COINCIDENCE.** `infinitude_forces_infinite_complexity : I.cx I.floor = ⊤` — the top
  is attained, and the floor is a point at which it is attained. ⚠ **Not a uniqueness claim**: the
  statement has no "only at the floor" conjunct and the class gives no such uniqueness, so read it as
  *the floor has complexity `⊤`*, never as *the point of infinite complexity is the bottom*. And note
  what it rests on — the proof is `rw [I.cx_floor_eq_iSup]` and only then the chain condition, so it
  needs the identity field first; a climbing chain alone constrains `cx floor` not at all.
* `Reading:` **COINCIDENCE**, conjectural — the framework reads that co-location of floor and `⊤` as a
  face of `⊥ = 0 = ∞`. `CLAUDE.md` fences the pole identity as a CHART claim, *stated, not proved*,
  whose actual witnesses are `pole_inversion` (coincidence/drift) and `rInv_swaps` (inversion). This
  theorem is not a proof of that identity and must not be cited as one.
* `Statement:` **DRIFT.** `pole_inversion` — members descend to the floor **as elements** while their
  complexity ascends to `⊤` (two measures running opposite along one sequence). ⚠ It needs the
  *extending* class `InfinitudeFloorInversion` plus a topology, and its "members descend" half is a
  **class field** (`member_tendsto_floor`), an assumption rather than a consequence. As of 2026-08-04
  the located instances are `ℕ∞` (the toy) and `Q₂` — **none on `ℤ_[2]`**, so `pole_inversion` itself
  is not available on the Lean file's own tower. It is a *shape* alongside § II's `swap_is_rInv` (an
  INVERSION), not the same claim: DRIFT and INVERSION are distinct POV kinds and no theorem located
  here identifies them.
* **But both halves of the drift ARE proved on the Lean file's own tower** — only the class packaging is
  missing. Complexity-ascent: `towerCx_zero : towerCx (0 : ℤ_[2]) = ⊤` and
  `towerCx_member (n) : towerCx (cnfToZp2 (towerNONote (n+1))) = ((n+1 : ℕ) : ℕ∞)`
  (`ZeroParadox/Valuation/TowerHeightFloor.lean`). Element-descent: `tower_converges_to_zero`
  (`tower_converges_to_zero`, `ZeroParadox/Ordinal/Gentzen.lean`), cited in § III below. ⚠ Cite the right witness for the
  infinity corner: `towerCx_zero` alone says only `towerCx (0 : ℤ_[2]) = ⊤`, with no `cnfToZp2` and no
  `towerNONote` in its statement. What ties the top to *this tower* is `towerInfinitudeFloor`'s
  `cx_floor_eq_iSup` field — which shows `towerCx 0 = ⨆ n, towerCx (cnfToZp2 (towerNONote (n+1)))` —
  and `tower_height_floor_reconciliation`, whose first conjunct is that floor complexity for that
  instance. So the zero corner (`seed_maps_to_bot_both`, whose conjunct is literally
  `cnfToZp2 (towerNONote 0) = 0`) and the infinity corner (`tower_height_floor_reconciliation`) are
  witnessed on the *same* `cnfToZp2 ∘ towerNONote` the Lean file works with throughout (in prose —
  `cnfToZp2` is not imported here).

`Reading:` with both corners measured, `cornerId` — the "concurrent" corner — stops being a phrase:
one index, an element-descent and a complexity-ascent, each reaching its own pole. **Co-witnessed
only.** The corners live in `Pole`/`Sphere` and the complexities in `ℕ∞`; nothing here asserts a
cross-type `=`, exactly as `cnf_bridge_type_boundary` fences the tower.

**⚠ SCOPE — what the class actually requires, stated from its fields rather than inferred.**
**Read `class InfinitudeFloor` in `ZeroParadox/Valuation/InfinitudeFloor.lean` for its fields — this
block deliberately does not re-list them** (see the correction note at the end of this section for
why). Two facts about it are load-bearing here and were measured:
* **It imposes no valuation axioms.** So "a carrier needs a valuation to have a second pole" is NOT a
  consequence of the class, and the table below is a survey of what happens to exist, not a derivation.
* **`cx_floor_eq_iSup : cx floor = ⨆ n, cx (member n)` is a required field, not a consequence of the
  others.** It is what the headline theorem rewrites with first, and it is the non-obvious thing a new
  realization must discharge — a climbing complexity chain alone constrains `cx floor` not at all.

Realizations located 2026-08-04 (**five**, and the count is a measurement at a date, not a census):

| carrier | `cx` is | where |
|---|---|---|
| `Q₂` | `cxQ2` = `if x = 0 then ⊤ else x.valuation.toNat` — the 2-adic valuation clamped by `.toNat` (negative valuations map to `0`) and extended by `⊤` at the floor | `InfinitudeFloor.lean` `q2InfinitudeFloor` |
| `ℤ_[2]` | `towerCx` = `if x = 0 then ⊤ else x.valuation` — the 2-adic valuation extended by `⊤` at the floor | `TowerHeightFloor.lean` `towerInfinitudeFloor` (`@[reducible] def`, deliberately not a global instance) |
| `PowerSeries R` | `PowerSeries.order`, the order of vanishing — a valuation when `R` is a domain, and the instance assumes only `[CommRing R] [Nontrivial R]` | `InfinitudeFloor.lean` `powerSeriesInfinitudeFloor` |
| `End` | `localCx v`, per node | `LocalFloor.lean` `boundaryFloor` — a **`List (Fin 2)`-indexed family** (one witness per tree node, a `def` not a global instance) |
| `ℕ∞` | `id` | `InfinitudeFloor.lean` — the file's own docstring calls this a **"Toy witness … Degenerate"**, included only to show the requirements are inhabitable |

`Reading:` (framework interpretation, **conjectural**, not a theorem) — four of the five `cx` maps are
valuations or order-of-vanishing maps, and the fifth is labelled degenerate by its own author, which
*suggests* a valuation is what supplies a climbing complexity chain in practice. The class's own field
docstring glosses `cx` as "a valuation / surprisal", so this reading is the author's too. **It is still
a pattern across five witnesses, not a structural necessity** — `cx = id` is the standing
counterexample to stating it as one.

**⚠ NO REALIZATION HAS BEEN GIVEN at the Kleisli initial object, the Hilbert zero object, the ordinal
floor, or the Markov attractor as of 2026-08-04** — a measurement, deliberately not the stronger
claim that none *can* be. Nothing in the class forbids one — a candidate needs a complexity map with a
strictly climbing member chain **and** must discharge `cx_floor_eq_iSup`; whether a categorical bottom
admits that is **open and untried here**.

*(**Correction note, and the reason this block no longer enumerates anything.** Two review rounds on
2026-08-04 found the same defect twice, one level apart. Round 1: the block said there were **four**
realizations — there are five. Round 2: the fix then said the class had **two** conditions and that
this "is the whole requirement" — it has three, and the dropped one, `cx_floor_eq_iSup`, is precisely
the load-bearing one. Both are the same error: **a completeness claim about a Lean object's contents,
asserted in prose that cannot check itself.** A docstring that re-lists a class's fields is a second
copy of the definition, and a second copy drifts — here, twice in two rounds, in a file whose entire
job is to POINT AT that definition. So the enumerations are gone and the pointer stands. The table
below is kept because a survey of *located realizations* is a measurement result, not a re-copy of a
definition — and it is dated for exactly that reason.)*

## Structure
- § I   `poleToSphere` — the pole embedding into the 2-adic Riemann sphere.
- § II  `swap_is_rInv` — the inversion corner is `rInv` (the genuine bridge content).
- § III `point_and_field_at_the_poles` — the point/field inversion at the two poles.
- § IV  `irreversible_direction_is_the_snap` — the one-way direction, co-witnessed with `t_snap_irreversible`.

*(The overview above previously said "the genuine Lean content is `swap_is_rInv`" full stop, and
§ III / § IV were unlisted. Corrected 2026-08-04. The § list names the headline declaration of each
section and is not a census — every declaration sits inside a section, but `corners_are_the_swapped_poles`
and the two `@[simp]` `rfl`-lemmas are not named above. Scroll the file for the full list; a count kept
in prose is the drift hazard described in the correction note above.)*
