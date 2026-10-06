# Height meets floor — the tower's 2-adic images as an InfinitudeFloor, norm order reversed from stage 1

Ride-along companion to `ZeroParadox/Valuation/TowerHeightFloor.lean`.

The tower ASCENDS (ordinal side) to its height ε₀; an `InfinitudeFloor` DESCENDS (its members climb in
complexity) to a floor of infinite complexity, here ℤ_[2]'s 0 (least under the 2-adic norm). These
orientations *fight*, and that fight is the content. The bridge `cnfToZp2`
(`ZeroParadox/Ordinal/CnfBridge.lean`) joins them **without ever asserting that ε₀ equals a floor**: with
ℤ_[2]'s 0 that is a cross-type identity, ill-typed per MC-1 / ZP-P; with ⊥ of `Ordinal` it is false
(`epsilon0_ne_bot`). Along the tower `cnfToZp2` keeps the order in the 2-adic valuation
(`tower_orders_agree`; at the seed by Mathlib's `valuation 0 = 0`) and reverses it in the norm only from
stage 1 (`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § V, DRIFT). On the floor's members, stages ≥ 1, the
ordinal ascent toward ε₀ is the norm descent toward ℤ_[2]'s 0.
Reading: the tie is worth building because it fights `ε₀ ≠ ⊥` of `Ordinal`; the map both joins the two
closures and holds them apart.

`towerInfinitudeFloor : InfinitudeFloor ℤ_[2]` is a **genuine instance** realizing this:
* `floor = 0`, ℤ_[2]'s 0;
* `member n = cnfToZp2 (towerNONote (n+1))` — the tower's 2-adic images (the shared construction of
  `mu_construction_correspondence`), each `≠ 0` (`snap_arc_z2_loop`);
* `cx x = ↑x.valuation` off 0 and `⊤` at 0, so `cx floor = ⊤` holds by the definition (`towerCx_zero`);
  `cx (member n) = n+1` (`cnfToZp2_tower_valuation`), so the members' complexities **climb**, and their
  supremum is that `⊤` (the field `cx_floor_eq_iSup`).

On the members the **order-reversal is visible in the numbers**: as `n` rises, the 2-adic *valuation* of
`member n` rises (`= n+1`) while its *norm* falls toward 0. Valuation-up ⟺ norm-down is a fact about
the 2-adic norm (`‖x‖ = 2^(-v(x))` for `x ≠ 0`), not a property of `cnfToZp2`; across the seed the norm
rises from 0 (`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § V). The SAME index sequence ascends on the
ordinal side to ε₀.

`tower_height_floor_reconciliation` bundles the reconciliation and **proves `ε₀ ≠ 0` in the same statement
that connects the two closures**: (1) the InfinitudeFloor's floor, ℤ_[2]'s 0, has infinite complexity
`cx = ⊤`; (2) the shared tower ascends to the height `ε₀ = ⨆ fundamentalSeq`; (3) `ε₀ ≠ 0` in `Ordinal` —
the height is NOT the ordinals' floor. One construction, two carrier-specific closures (ε₀ in `Ordinal`;
ℤ_[2]'s 0 as the images' limit), opposite orientations, joined by `cnfToZp2` and held apart by it. No
cross-type `=`: with ℤ_[2]'s 0, `ε₀ = 0` fails to elaborate; with the ordinal 0 it elaborates and is
false, (3).

**Honest fence.** The floor lives in `ℤ_[2]`, the height in `Ordinal`; they are co-witnessed through the
shared `towerNONote`, never identified. `towerInfinitudeFloor` is a `def` (an exhibited witness), not a
registered global instance on `ℤ_[2]`.
