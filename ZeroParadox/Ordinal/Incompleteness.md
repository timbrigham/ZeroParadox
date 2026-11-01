# Incompleteness — ride-along documentation

Moved from `ZeroParadox/Ordinal/Incompleteness.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** It has since carried corrective edits, but its claims are unverified until a claim review says otherwise.

## § I. The snapEmbed Morphism

snapEmbed sends the snap state c₁ to 0 in ℤ_[2] (the limit of the tower stages' `cnfToZp2`
images, `tower_converges_to_zero`) and the pre-snap state c₀ to 1 (a nonzero 2-adic integer). The
tower itself, in `Ordinal`, has supremum ε₀ (`epsilonZero_eq_iSup`), a different carrier.

This formalizes the embedding: c₁ maps to 0 ∈ ℤ_[2], the limit in ℤ_[2] of the tower stages'
images. Within the ZP framework, 0 here plays the role of ⊥; in the Scale.lean chart (⊥ = 0)
0 fills ℤ_[2]'s bottom role (a ZPSemilattice on ℤ_[2] with ⊥ = 0 is built in
`ZeroParadox/Valuation/Scale.lean` § V), and in the multiplicative reading `snapEmbed c₀ = 1` is
the identity, and that reading is not a ZPSemilattice, since multiplication on ℤ_[2] is not idempotent (2 · 2 ≠ 2) — the identification is a modelling commitment, not a
ring-theoretic fact.

The morphism property: join on MachinePhase (c₁ is absorbing) corresponds to
multiplication on ℤ_[2] (0 is absorbing). Both structures have the same absorbing
element pattern: c₁ absorbs all joins, 0 absorbs all products.

## Remark R-M.1: DA-1 Path 2 and the Limits of the Diagonalization Frame

`both_fixed_points_exist` conjoins two existentials, one per domain: a code periodic with
period its own Gödel number, and ε₀ = ω^ε₀ as the least fixed point. The first conjunct is not
diagonal content on its own, since any code whose evaluation ignores its input meets it
(`Code.zero`, the `example` in `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § IV; the constant
codes in `infinite_quine_family`, `ZeroParadox/Computability/Kleene.lean`); the proof supplies it
from the recursion-theorem witness `computational_quine_exists`, which the statement does not
record. The ordinal conjunct is ε₀'s least-fixed-point face; its supremum face is
`epsilonZero_eq_iSup`. The statement establishes that both exist, not
that they are one structural pattern; reading them as the same pattern is the framework's
interpretation, and no equation between a `Code` and an `Ordinal` is well-formed.

`Statement:` **CARRIER** — two theorems, one per chart, both in Lean. In the depth chart, ZP-C Lemma L-INF (`l_inf`,
`ZeroParadox/Information/Surprisal.lean`) says the surprisal I(n) = n exceeds every bound at some
depth n, while every value I(n) is finite. In the point chart, the coincidence witness
`infinitude_forces_infinite_complexity` (`ZeroParadox/Valuation/InfinitudeFloor.lean`) says the floor
of any `InfinitudeFloor` has complexity ⊤ in ℕ∞, the supremum of its members' complexities, each
of which is finite (`member_cx_lt_top`). On ℤ_[2] a witness is `towerInfinitudeFloor` (a def, not a
global instance), floor 0, complexity `towerCx` (⊤ at 0, the 2-adic valuation elsewhere), applied in
`tower_height_floor_reconciliation` (`ZeroParadox/Valuation/TowerHeightFloor.lean`); on ℚ_[2] the
global instance is `q2InfinitudeFloor`, floor 0. `Statement:` **CARRIER** — the point-chart measure
`cxQ2` (`ZeroParadox/Valuation/InfinitudeFloor.lean`) is ⊤ at 0 and elsewhere the 2-adic valuation
truncated at 0; on the members it is the valuation (`cxQ2_two_pow`), and Mathlib's `Padic.valuation`
returns 0 at 0 (`Padic.valuation_zero`). It is not `surprisal`, and the two agree along the members: `info_valuation_eq_surprisal`
(`ZeroParadox/Multihomed/TopNumEdge.lean`) says the 2-adic valuation of 2ⁿ ∈ ℚ_[2] equals I(n), and
the members of `q2InfinitudeFloor` are the points 2ⁿ⁺¹. That equation is indexed by depth n and stops
at the floor 0, which sits at no finite depth: there the complexity `cxQ2` is ⊤ and `surprisal`, a
function of the depth, has no argument. `Reading:` ⊥ of
`MachinePhase`, c₀, corresponds to that point 0 under the `l_inf` docstring's reading, which names
0 ∈ ℚ_[2]; that is a different pairing from `snapEmbed` in § I, which sends c₀ to 1 and c₁ to 0. L-INF is structurally analogous to the two
fixed points above. The Kleene recursion theorem and ε₀'s fixed point are both textbook
instances of the diagonalization schema; whether
L-INF fits the same schema formally is the open question this remark is tracking.

The formally unconnected instance is L-INF. L-INF is a measure-theoretic statement
(surprisal under a probability measure on ZP-B's binary space), while the Kleene quine is
a computability-theoretic statement (partial recursive functions, Gödel encoding), and
neither this remark nor `both_fixed_points_exist` links them. ZP-C keeps the surprisal measure and
Kolmogorov complexity as independent routes (ZP-C Remark R-BRIDGE). Kolmogorov complexity
itself was not located as a definition in `ZeroParadox/**/*.lean` as of 2026-10-04 (searched
for declarations named for Kolmogorov, prefix or description-length complexity, and for
"incompressib"); `ZPSurprisal` in `ZeroParadox/Category/Category.lean` abstracts only its
skeleton.

DA-1 Path 2 is a different matter. In ZP-E (DA-1 insert § IV) it is the step from
unbounded surprisal to executing: a bridge principle of its own, a missing principle and not
a missing proof, which the framework does not adopt and which is not the occurrence
commitment.
