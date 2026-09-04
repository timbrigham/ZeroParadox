# ScaleRealization — ride-along documentation

Long-form argument and fences for `ZeroParadox/Valuation/ScaleRealization.lean`. Written 2026-09-04.
Everything below was elaborated or measured; nothing is recalled.

## What this file is for

`ZeroParadox/Valuation/SemilatticeInstance.lean` (ZP-I) carries

```lean
IsDepthChain (S : ℕ → Q₂) (depths : ℕ → ℕ) : Prop := ∀ n, (S n).valuation = (depths n : ℤ)
```

and its own Engineer's Take calls it the framework's *"one undischarged modelling commitment"* — the
assertion that lattice motion and 2-adic valuation are the same motion.

Two things were measured about it on 2026-09-04, both at the artifact.

**It is strictly stronger than what its consumers use.** There are exactly two, found by tracing
every occurrence, and they want different things.

`h_strict_from_r1_t3` rewrites with the equality twice and transports strictness, producing
`∀ n, (S n).valuation < (S (n+1)).valuation` — a pure *difference* condition. `t_iz_r1_t3_geometric_bound`
then keeps it that way: its helper is `v 0 + n ≤ v n` and its conclusion is `‖Sₙ‖ ≤ ‖S₀‖ · (½)ⁿ`, both
relative to the starting term.

`t_iz_h_bound_from_depth_chain` uses it a **second** time, at `h_depth 0`, and this one is not a
difference: because `depths 0` is a natural number, the equality gives `0 ≤ (S 0).valuation`, hence
`‖S₀‖ ≤ 1`, which absorbs the `‖S₀‖` factor and turns the relative bound into the absolute
`‖Sₙ‖ ≤ (½)ⁿ`.

⚠ **An earlier revision of this file said "nothing on the path consumes the absolute valuation." That
was false** — it was written after tracing one consumer and generalising to all of them, and the
second use is exactly an absolute fact. What is true is narrower and is the useful statement: **neither
use needs the EQUALITY.** Strictness needs order-correspondence; the base bound needs one inequality.
That is what `SemilatticeInstance.TracksDepth` asks for, and `tracksDepth_not_isDepthChain` shows the
weakening is real rather than a rename.

**And the existential form is nearly empty.** `ScaleDepthWitness.depthchain_iff_nonneg` proves a chain
admits *some* depth index exactly when its valuations are non-negative — the index can be read back
off the chain. So a witness can satisfy the interface by supplying both sides itself.

This file states the commitment differently: as an **equivariance hypothesis on the theorems that need
it**, per `R-COMMIT`, never as a class field.

## The commitment, and why this shape

`Function.Semiconj ρ scale (2 * ·)` is Mathlib's `∀ x, ρ (scale x) = 2 * ρ x`. Read as a contract: the
abstract one-step operator, pushed through the realization, *is* doubling on the metric side.

That is a genuine, falsifiable modelling claim about a map between two independently-given structures.
It cannot be manufactured from either side alone, which is exactly what `depths` could be.

From it, every valuation fact is **derived**:

- `realized_orbit` — the `n`-step image is `2 ^ n · ρ x`, so the realized orbit *is* the doubling orbit;
- `realized_valuation_step` — one step raises the valuation by exactly one;
- `realized_valuation_orbit` — `n` steps shift it by `n`, **from wherever the base point sat**;
- `realized_strict` — strict ascent, which is precisely ZP-I's `h_strict`, obtained without any
  depth chain;
- `realized_tendsto_zero` — convergence to the floor.

⚠ The limit is not the new part. `PadicAttractor.doubling_orbit_tendsto_zero` already gives it for
every orbit. What is new is the hypothesis that reaches it.

## The expansion joint, and why the welded form is not merely too strong

The offset in `realized_valuation_orbit` is never pinned: the theorem says the valuation moves by `n`
*relative to the base point*, and the base point's own valuation is carried along as a symbol. The
increment is rigid; the origin is free. That is the same shape as `RiemannSphere.rScale_valuation`
(the valuation of `2ⁿ · x` is `n` plus the valuation of `x`), and it is the same shape the p-adic
literature uses for **translation length** along a loxodromic axis, where the origin on the axis is
not defined at all.

⭐ **Across general value monoids the welded form is not even statable.** `ValuationStructure.val`
(`Valuation/Scale.lean`) lands in `ℕ∞`; `Padic.addValuation` lands in `WithTop ℤ`. These are different
types, and `withTopInt_has_negative` exhibits the obstruction to identifying them — `WithTop ℤ` has
elements strictly below `0` and `ℕ∞` does not, so no order isomorphism exists. Writing an equation
between the two valuations would need a coercion that is not one. ZP-I avoids this only by using the
ℤ-valued `Padic.valuation`, which in turn has no value at the floor — the same reason
`rScale_valuation` carries an `x ≠ 0` guard that `Padic.addValuation` does not need.

## Falsifiers — run, not asserted

`R-CONTROLS` asks for objects satisfying the same inputs for which the conclusion is false. Both
hypotheses were tested by **refutation**, which is stronger than "the proof stops working":

- **Drop `ρ x ≠ 0`** and the conclusion becomes provably FALSE. The constant map to `0` is
  semiconjugate to doubling (`trivial_realization_is_semiconj_and_static`) and its valuation never
  moves, so the universally-quantified strict-ascent statement is refuted outright.
- **Drop equivariance** and it is also provably FALSE. The constant map to `1` is nowhere zero, is
  demonstrably *not* semiconjugate to doubling, and has a flat valuation.

Both refutations are anonymous `example`s in § IV, so they declare nothing and owe no purity entry,
and they stop compiling if either fence ever fails.

**Non-vacuity is checked separately, and without it the file would say nothing.**
`succ_realized_by_doubling` exhibits a realization satisfying every hypothesis at once: `L := ℕ`, the
abstract step is the successor, and `ρ n = 2 ^ n`. That map is `ScaleDepthWitness.scaleChain`, so the
witness built the day before is the instance this file needed.

## Both banks — how the self-supply residue is closed

`ScaleDepthWitness.depthchain_iff_nonneg` showed the weakness of `IsDepthChain`: a depth index can be
read back off the chain, so a witness can satisfy the interface by supplying both sides itself.
`SemilatticeInstance.TracksDepth` does not fix that, and `tracksDepth_is_self_supplied` says so in the
file.

§ VI closes it, and the mechanism is worth stating precisely. **`ValBridge.val` is a class field.** It
is fixed when the instance is built, before anyone chooses a realization, so it cannot be manufactured
from the chain the way a free `depths` parameter can.

`realization_bridges_both_valuations` is then a conjunction of two facts with **two independent
citations**:

- the abstract valuation climbs by `n` from its own origin — `ScaleBridge.orbit_ne_bot_and_val_free`,
  which mentions no realization at all;
- the metric valuation climbs by `n` from *its* own origin — `realized_valuation_orbit`, from
  equivariance.

Neither conjunct is derived from the other, and that is visible in the proof term. The two origins are
never identified; they do not even share a value monoid.

`banks_are_independent` is the control that makes "independently supplied" mean something: it exhibits
a realization — the constant map to `1` — for which the **abstract** half still holds and the
**metric** half is false. One side needs no realization at all, so it demonstrably was not read off the
chain, and the coupling is exactly what equivariance buys.

## What this does NOT settle

**The scope is one distinguished endomap.** `scale` is a single function and the orbit is its
iteration; ZP-I quantifies over arbitrary state sequences in a lattice, and this file does not reach
that. The framework's motion here is iteration of one map rather than a group acting on the carrier.

§ VII narrows that gap. `realized_orbit_is_rScale_orbit` proves the abstract `ℕ`-indexed orbit is
exactly `RiemannSphere.rScale`'s orbit of the base point, so the abstract step and the sphere's
`ℤ`-action agree wherever both are defined. **The abstract side is a monoid and the sphere side is a
group; the realization is the embedding of the first in the second.**

⭐ **And the missing half is not missing — it is refused, which reframes this whole item.**
`ScaleBridge.scale_not_surjective` proves that given any point of valuation `0`, `scale` is not
surjective: that layer has no scale-predecessor, because `bot` maps to itself and carries `⊤`, and any
other predecessor would force `0 = val y + 1`, which `ℕ∞` refuses. So the abstract family **cannot** be
a group. A surjective `scale` would be invertible along its orbit, and invertible motion is exactly
what this framework denies.

⚠ **Which arrow, stated carefully, because `BOTTOMELEMENT.md` records this mis-sort as a correction
already made once.** `val bot = ⊤`, so climbing the valuation is motion TOWARD the floor. This is the
**inbound (ν)** face — the algebraic sibling of `c3_irreversible`, which says there is no continuous
path *to* `0` and that the arrival is a jump. It is **not** `t_snap_irreversible`, the **outbound (μ)**
face, which says no join returns to `⊥`. Both are one-way; they are different arrows, and conflating
them is the error that once put two irreversibility theorems in the wrong column.

**No lattice content is used.** None of the theorems mention a join, and none needs `[ZPSemilattice L]`
— `L` is a bare type. That is a finding rather than an omission: `ScaleBridge`'s `ValBridge` already
records that the join appears in none of the four valuation axioms, and ZP-I's own no-go gauge records
that `HasNoTop` appears in no binder of `h_strict_from_r1_t3`. The lattice structure is not load-bearing
anywhere on this path, and stating the realization over a bare type makes that visible instead of
implied.

**This does not retire `IsDepthChain`.** What it shows is that ZP-I's downstream conclusion is
reachable from a hypothesis that is not self-satisfiable. The companion rewiring — `TracksDepth` and
its two derived consumers, added to `SemilatticeInstance.lean` in the same change — is additive: every
existing declaration is untouched, and `isDepthChain_tracksDepth` carries the old form into the new one
so nothing citing `IsDepthChain` loses anything.

## Prior art

`Function.Semiconj` is Mathlib's (`Mathlib/Logic/Function/Conjugate.lean`) — the standard name for an
intertwiner of two self-maps, adopted rather than re-coined per `R-PRIORART`.
`BottomValuation` (`Valuation/ValuationAFA.lean`) is the corpus's abstract valuation-with-a-floor, with
Γ a parameter; `ValuationAFA_Padic.lean` proves its axioms hold of `Padic.addValuation` on ℚ₂.
`ValuationStructure` (`Valuation/Scale.lean`) adds the `+1` increment law on ℕ∞ — the closest existing
statement to `realized_valuation_step`, on the abstract side rather than through a realization.
The valuation arithmetic is Mathlib's (`Padic.valuation_mul`, `valuation_pow`, `valuation_p`).
