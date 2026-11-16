# The pole: two points, and the chart claim

Ride-along documentation for [`ZeroParadox/Valuation/PoleCorners.lean`](PoleCorners.lean).
The Lean file holds the declarations and a statement per declaration; this document holds the reading of the
pole carrier. Where the two would overlap, **the Lean is authoritative**.

## The pole carrier

The pole is the two-element type `Pole = {zero, infty}`: the two points that inversion exchanges
(`rInv_swaps`); they are distinct here (`poleView_ends`). The framework's `0 = ∞` reading is a chart claim
with its own witness (`infinitude_forces_infinite_complexity`).
