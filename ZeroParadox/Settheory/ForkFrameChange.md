# The fork's two closures under order-duality, and the fences on the shared shape

Moved from `ZeroParadox/Settheory/ForkFrameChange.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise. The Fences sentence on cross-domain identity was updated on moving to the MC-1 retirement (it previously called the identity a modeling commitment).

## Formal Overview (AI-assisted)

`Statement:` COINCIDENCE (`fork_collapse_iff`) and INVERSION (`lfp_dual_eq_gfp`, `gfp_dual_eq_lfp`).
`fork_collapse_iff` (`Settheory/FixedPointFork.lean`) is the P1 spine: over a complete lattice a monotone
self-map's least fixed point `lfp` (μ, well-founded closure) and greatest fixed point `gfp` (ν,
non-well-founded closure) collapse to one point iff the map has a unique fixed point (the diagonal fixed
point). `ZeroParadox/Settheory/ForkFrameChange.lean` adds the P2 face — the **frame-change** — in its domain-independent form: the
**order-duality** (the abstract analog of `rInv` swapping `0 ↔ ∞` and `op` swapping initial ↔ terminal)
**swaps the two closures**: `lfp (dual f) = gfp f` and `gfp (dual f) = lfp f`. So the μ-closure and the
ν-closure are the two charts, order-duality is the frame-change between them, and the fork collapses at
the diagonal fixed point.

`Statement:` INVERSION and COINCIDENCE, bundled (`fork_is_frameflip`). `Reading:` INVERSION, conjectural: that
the valuation and category frame-flips share this shape.
`fork_is_frameflip` bundles both faces: the duality-swap (P2) with `fork_collapse_iff` (P1). This is the
order-theoretic universal `fork_is_frameflip` — the domain-independent shape that the valuation
(`snap_is_frameflip`) and category (`catseam_is_frameflip`) faces are read as sharing (conjectural; see the
Reading label). Not "instances": neither satisfies `fork_collapse_iff`'s hypotheses (complete lattice, monotone map) — see the `fork_is_frameflip`
docstring in `ZeroParadox/Settheory/ForkFrameChange.lean`, which states this in full.

**Fences.** This is the **order-theoretic** universal (Knaster–Tarski world), choice-free. It is NOT the
categorical Lawvere universal, which is a proven **wall**: `Category/Lawvere.lean` shows the Lawvere
fixed-point test is category-relative — in **Set** no nontrivial total type carries a Lawvere witness
(Cantor), so the lattice bottom is a *posited* fixed point sharing the diagonal shape, not a literal
Lawvere instance. The cross-domain identity of all these fixed points is retired as ill-typed (object equality
across categories does not typecheck and is not invariant under equivalence). No mathematical novelty:
the duality-swap is the standard `lfp`/`gfp` order-duality, bundled with the fork.

## Structure of `ZeroParadox/Settheory/ForkFrameChange.lean`
- § I  Order-duality swaps the fork's two closures (`lfp ↔ gfp`)
- § II The universal frame-flip: both faces bundled
