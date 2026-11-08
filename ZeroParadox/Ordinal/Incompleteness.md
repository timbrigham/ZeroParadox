# Incompleteness — ride-along documentation

Moved from `ZeroParadox/Ordinal/Incompleteness.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** It has since carried corrective edits, but its claims are unverified until a claim review says otherwise.

## § I. The snapEmbed Morphism

snapEmbed sends the snap state c₁ to 0 in ℤ_[2] (the limit of the tower stages' `cnfToZp2`
images, `tower_converges_to_zero`) and the pre-snap state c₀ to 1 (a nonzero 2-adic integer). The
tower itself, in `Ordinal`, has supremum ε₀ (`epsilonZero_eq_iSup`), a different carrier.

No equation between a `MachinePhase` state and a point of ℤ_[2] is stated. What the two carriers
share is a role, the die's Quine-atom role `Motion.SelfOnlyAt` (`ZeroParadox/Die.lean`, a point
that steps to itself and to nothing else), whose occupant in each carrier depends on the step
chosen there. On `MachinePhase` under join it is c₁ (c₀ steps to c₀ and to c₁), while under a
self-application map supplied by `AbstractSelfApp` it is c₀, ⊥ of `MachinePhase`, by that class's
fields (`selfApp_quine_role_iff`). § I-b of
the `.lean` file states two pairings, each through `snapEmbed`:

- **The absorbing pairing.** Under the join motion on `MachinePhase` (`a → join a z`) only c₁
  steps to itself only (`machineJoinMotion_selfOnlyAt_iff`); under the multiplication motion on
  ℤ_[2] (`x → x · w`) only 0 does (`z2MulMotion_selfOnlyAt_iff`). `snapEmbed` is a map of these
  motions (`snapEmbedHom`, from `snapEmbed_mul_morphism`) and sends c₁ to 0 (`snapEmbed_c1`). It
  has no back clause at c₀ (the `example` after `z2MulMotion_selfOnlyAt_iff`), so the general
  transport `Motion.LaxHom.selfOnlyAt` does not apply; at c₁ the role does carry over, since 0 has
  only itself as successor (`snapEmbed_selfOnlyAt_c1`, from `Motion.selfOnlyAt_relHom`).
- **The doubling pairing.** Under doubling on ℤ_[2], only 0 steps to itself only
  (`z2_double_selfOnlyAt_iff`), and 0 is divisible by every power of 2
  (`snapEmbed_c1_dvd`). `snapEmbed` carries no motion on `MachinePhase` with a step at c₀ into
  doubling steps (`snapEmbed_doubling_noStepAt`): the snap step c₀ → c₁ goes to 1 → 0, which is
  not a doubling step.

A third chart is a chosen one: a `ZPSemilattice` on ℤ_[2] with ⊥ = 0 is built in
`ZeroParadox/Valuation/Scale.lean` § V from a join picked through a well-ordering, and there 0
occupies the join-identity role by that choice.

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
