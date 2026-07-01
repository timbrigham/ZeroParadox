import ZeroParadox.ZPC

/-!
# P6: measure = +∞ at the bottom — per-domain bundle, and the type-boundary finding

The zero-infinity premise tabulates "+∞ at the floor" across domains: v₂(0)=∞ (p-adic), surprisal
unbounded (information), ε₀ = sup tower (ordinal). MC-1 now pins the three categorical bottoms, so the
parked goal was ONE uniform cross-functor "measure(bottom) = ⊤" invariant.

**Finding (the honest scope).** That uniform invariant is NOT a single theorem: the three measures are
heterogeneous — a `WithTop`-valued additive valuation (`v 0 = ⊤`), an ℝ-valued surprisal that is
*unbounded above* (no single ⊤ value — a divergence), and an ordinal supremum. They are functions of
different types into different codomains, so "measure(bottom) = ⊤" is not well-formed uniformly — the
SAME type boundary as MC-1's identity half, now at the MEASURE level. The honest form is a per-domain
bundle of the divergence facts, each in its own measure type:

* valuation domains (incl. every p-adic field): `ZeroParadox.FloorWitness.addVal_bot` (P7) — `v 0 = ⊤`,
  choice-free;
* information: `info_bottom_diverges` here (= ZP-C `l_inf`) — surprisal unbounded above;
* ordinal: ε₀ = sup of the ω-tower (ZP-N), the order-theoretic divergence.

So "+∞ at every bottom" is real per-domain but is a BUNDLE, not a uniform invariant. P6 thus EXTENDS the
MC-1 type-boundary finding from the bottoms (different objects) to their measures (different functions).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.BottomMeasure

/-- **Information-side floor divergence (P6).** The surprisal at ball-depth `n` is unbounded above: the
    information measure diverges to +∞ as depth → the bottom. The info-domain member of the bottom-measure
    bundle (= ZP-C `l_inf`). -/
theorem info_bottom_diverges : ∀ M : ℝ, ∃ n : ℕ, M < ZeroParadox.ZPC.surprisal n :=
  ZeroParadox.ZPC.l_inf

end ZeroParadox.BottomMeasure

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.BottomMeasure
#print axioms info_bottom_diverges
end PurityCheck
