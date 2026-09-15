# ScaleDepthWitness — ride-along documentation

Long-form analysis for `ZeroParadox/Valuation/ScaleDepthWitness.lean`. Written 2026-09-04 after two
review gates; every claim below was elaborated or measured, not recalled.

## What ZP-I's `IsDepthChain` actually buys

`ZeroParadox/Valuation/SemilatticeInstance.lean` (ZP-I) defines

```
IsDepthChain (S : ℕ → Q₂) (depths : ℕ → ℕ) : Prop := ∀ n, (S n).valuation = (depths n : ℤ)
```

and its own docstring calls this the framework's one *"undischarged modelling commitment"* — the
bridge asserting that 2-adic depth and lattice motion are the same. Its Engineer's Take is blunter:
*"nothing derives that these are the same motion. We assert it."*

This file exhibits a family for which it holds by proof. It is important to be exact about what that
is worth, because the first draft overstated it as *the seam, discharged*.

`depthchain_iff_nonneg` measures it:

```
(∃ depths, IsDepthChain S depths) ↔ ∀ n, 0 ≤ (S n).valuation
```

The forward direction is immediate; the reverse takes `depths := fun n => (S n).valuation.toNat`.
So **a chain admits some depth index exactly when its valuations are non-negative**, and the index can
always be read back off the chain itself. Existentially quantified, `IsDepthChain` excludes only the
chains that pass below the floor.

`scaleChain` is in that situation. Its depth index `fun n => n` *is* its valuation. The witness
supplies both sides of the bridge itself, so it **satisfies the interface rather than crossing it**.
ZP-I's actual commitment is that a depth index arriving *independently* — from the lattice, not read
off the valuation — is the one the valuation tracks. Nothing here touches that.

What the file does establish is that the two sides are simultaneously satisfiable by a non-degenerate
family: the depth index is a strict state sequence (`depthId_isStrictStateSequence`), so the pair
`IsDepthChain ∧ IsStrictStateSequence` is not vacuous, and ZP-I's own bridge then carries it to
convergence. The content is in the **conjunction**, never in the depth chain alone.

## The no-go gauge, and why it is owed

ZP-I retracted the claim *"because there is no top element, the chain cannot stop"* in commit
`62b5b61`, replacing it with a gauge: a constant sequence is a perfectly good state sequence in a
lattice with no top, and it never moves. A family that *does* move invites that reading straight back,
so the same fence is owed here. `constChain_isDepthChain_not_strict` is it: the constant chain `1` is a
depth chain, at depth `0` forever, and what it fails is strictness — which lives on the lattice side.

⚠ Its strictness conjunct restates an anonymous `example` at `SemilatticeInstance.lean`, in the file
this one imports. It is named here only because the `Q₂` conjunct has to be stated somewhere; the
lattice half is not new.

## What is NOT new here

- **The valuation fact.** `ZeroParadox/Valuation/InfinitudeFloor.lean` already proves
  `two_pow_valuation (k : ℕ) : ((2 : Q₂) ^ k).valuation = (k : ℤ)`. An earlier draft of this file
  restated it as `scaleChain_valuation`; that declaration has been deleted and
  `scaleChain_isDepthChain` now consumes `two_pow_valuation` directly. The same fact also appears
  inline at `ZeroParadox/Multihomed/TopNumEdge.lean`, with the inverted twin at
  `ZeroParadox/Valuation/PolarityFlip.lean`.
- **The limit.** `ZeroParadox/Valuation/PadicAttractor.lean`'s `doubling_orbit_tendsto_zero` gives
  convergence to `0` for *every* orbit, and closes `scaleChain_tendsto_zero` in one line. Routing
  through ZP-I's `t_iz_cauchy` instead is deliberate — it shows ZP-I's hypotheses suffice to reach a
  conclusion that is independently available — but the limit itself is not the contribution.
- **The choice-free shift.** `ZeroParadox/Valuation/PricedPadicInterface.lean` proves the
  corresponding scaling shift on ℕ (`v2_scale_nat`), choice-free.

What is new is `scaleChain_isDepthChain` — as far as the prior-art gate could find, the first concrete
`IsDepthChain` witness anywhere in the corpus — and `depthchain_iff_nonneg`, which prices it.

## The axiom footprint

`depthId_isStrictStateSequence` reports `[propext, Quot.sound]`: **the lattice side is choice-free**.
Everything over `Q₂` reports `Classical.choice`. That footprint is inherited and generic rather than
p-adic — `padicValNat p n` is `(Nat.maxPowDvdDiv p n).fst`, and that natural-number division helper
already carries choice at this pin, below the completion.

`#print axioms` reports what a proof used, never what it needed, so none of this settles whether the
`Q₂` footprint could be avoided by a different proof. See `RiemannSphere.md` for the same point about
the sphere, and `PricedPadicInterface.md` for the pin-relativity fence.

## Relation to the sphere

`scaleChain_eq_orbit` identifies the family as the orbit of `1` under
`ZeroParadox/Valuation/RiemannSphere.lean`'s `rScale`, so the depth index and the scaling parameter
are the same integer. The orbit stays inside the affine chart; the pole at `∞` is fixed by
`rScale_infty` and is never reached. In the loxodromic reading described in `RiemannSphere.md`, the
depth index is translation length along the axis.
