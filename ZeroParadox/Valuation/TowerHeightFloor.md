# Height meets floor — the tower as an InfinitudeFloor, order-reversed

Ride-along companion to `ZeroParadox/Valuation/TowerHeightFloor.lean`.

The tower ASCENDS (ordinal side) to its height ε₀; an `InfinitudeFloor` DESCENDS (its members climb in
complexity) to a floor ⊥ of infinite complexity. These orientations *fight* — and that fight is exactly the
content, because the order-reversing bridge `cnfToZp2` (`ZeroParadox/Ordinal/CnfBridge.lean`) reconciles them
**without ever asserting `ε₀ = ⊥`**: with ⊥ of `ℤ_[2]` that is a cross-type identity, ill-typed per MC-1 / ZP-P;
with ⊥ of `Ordinal` it is false (`epsilon0_ne_bot`). Building the tie is required *precisely because* it fights
`ε₀ ≠ ⊥`: the map turning ascent-to-ε₀ into descent-to-⊥ is the wall that is the spine.

`towerInfinitudeFloor : InfinitudeFloor ℤ_[2]` is a **genuine instance** realizing this:
* `floor = 0` (= ⊥ in `ℤ_[2]`);
* `member n = cnfToZp2 (towerNONote (n+1))` — the tower's 2-adic images (the shared construction of
  `mu_construction_correspondence`), each `≠ 0` (`snap_arc_z2_loop`);
* `cx x = ↑x.valuation` off 0, `⊤` at 0 — and `cx (member n) = n+1` (`cnfToZp2_tower_valuation`), so the
  complexities **climb** and drive `cx floor = ⊤` (`infinitude_forces_infinite_complexity`).

The **order-reversal is visible in the numbers**: as `n` rises, the 2-adic *valuation* rises (`= n+1`) while
the *norm* falls to 0 — valuation-up ⟺ norm-down is `cnfToZp2` being antitone. The SAME index sequence
ascends on the ordinal side to ε₀.

`tower_height_floor_reconciliation` bundles the reconciliation and **proves `ε₀ ≠ 0` in the same statement
that connects the two closures**: (1) the InfinitudeFloor floor ⊥ has infinite complexity `cx = ⊤`; (2) the
shared tower ascends to the height `ε₀ = ⨆ fundamentalSeq`; (3) `ε₀ ≠ 0` in `Ordinal` — the height is NOT the
ordinals' floor. One construction, two carrier-specific closures (ε₀ ; ⊥), opposite orientations, joined by the
order-reversing map and held apart by it. No cross-type `=`: with ℤ_[2]'s 0, `ε₀ = 0` fails to elaborate; with
the ordinal 0 it elaborates and is false, (3).

**Honest fence.** The floor lives in `ℤ_[2]`, the height in `Ordinal`; they are co-witnessed through the
shared `towerNONote`, never identified. `towerInfinitudeFloor` is a `def` (an exhibited witness), not a
registered global instance on `ℤ_[2]`.
