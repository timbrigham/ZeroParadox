# SnapFrameChange — the tower limit's two chart-readings

Ride-along companion to `ZeroParadox/Multihomed/SnapFrameChange.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md`.

## Formal Overview (AI-assisted)

Two prior results meet here.

**P8** (`ZeroParadox/Ordinal/P8.lean`) built the tower-rank encoding `cnf_encode : {α < ε₀} → ℤ₂`
and proved that the ω-tower's encodings converge to `0` (`cnf_encode_tower_tendsto_zero`): the
tower climbing to `ε₀` has stage-encodings that land on the 2-adic floor `0 = ⊥`, so in this
**encoding chart** the ascent to `ε₀` resolves onto the bottom.

⚠ The encodings **converge to** ⊥; `ε₀` is not ⊥ (`ε₀ ≠ ⊥`). And reading that floor as a **NEW**
bottom ⊥ₙ₊₁ is **C-DA2, a commitment** — no theorem here carries it, and in this very chart
`snap_arc_z2_loop` has the arc returning to the **same** `0`. `t_iz_limit_is_new_null` proves the
ROLE half only and must never be cited as a novelty witness (`Order/SnapCannotBe.lean:43`).

**RiemannSphere** (`ZeroParadox/Valuation/RiemannSphere.lean`) built the inversion `rInv` on the
one-point compactification `OnePoint ℚ₂`, a homeomorphism swapping the floor `0` with the point at
infinity `∞` (`rInv_swaps`) — the change of frame, or chart-transition.

`Statement:` **INVERSION** — `rInv` exchanges the floor `0` with `∞`, and one tower of encodings
reads as converging to either pole depending which chart it is viewed through
(`snap_is_frameflip`).

`Reading:` **INVERSION** — the framework reads the snap as an instance of that exchange.
Conjectural: no snap transition appears in the statement.

`Statement:` **INVERSION** — the result is the **valuation-frame realization of the POLE EXCHANGE**
(the snap-as-instance reading is ZP-Q's conjecture, not established here — see the declaration
docstring): `snap_frameflip_tower_tendsto_infty` — the *same* tower encodings, pushed into `OnePoint ℚ₂` and
viewed through `rInv`, tend to `∞`. So one sequence, two charts: it falls to the floor `0` in the
encoding chart and rises to the antipode `∞` in the `rInv` chart, and `rInv` is the passage between
them.

`Statement:` **INVERSION** — `snap_is_frameflip` bundles both limits with the `0 ↔ ∞` swap: the
descent to ⊥ and the ascent to ∞ are the *same* tower-encodings under the frame-change.

## Fences

`Reading:` **INVERSION** — this is the **valuation point of view's** shape of the frame-change, not
the abstract cross-domain claim: the general statement "the snap `⊥ → ε₀` IS the change of point of
view" remains a **conjecture**.

It also inherits P8's honest scope — the tower-rank encoding is a **constructed** witness (the
valuation growth is built into the rank), **not** an independent CNF↔2-adic structural identity.

**No dynamical or physical claim. No claim of mathematical novelty** — this composes two proved
results.

## Structure

- **§ I** The tower under the frame-change: `rInv ∘ encode` tends to `∞`
- **§ II** The two charts, bundled: descent to `0` and ascent to `∞` are one tower, swapped by `rInv`
