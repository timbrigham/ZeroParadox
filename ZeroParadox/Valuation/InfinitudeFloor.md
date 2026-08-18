# What the requirements class pins down, and why non-degeneracy must be an inequation

Argument, NO-GO gauge and prior art for `ZeroParadox/Valuation/InfinitudeFloor.lean`. The Lean file
holds the declarations, the Engineer's Take and the per-declaration glosses.

## The move

A well-typed form of the claim **"the bottom's infinite complexity IS its being an infinitude of
zeros."** Rather than equate two objects across a type boundary (the MC-1 wall), this uses the
framework's instance-meets-requirements move: a REQUIREMENTS typeclass `InfinitudeFloor` with a `floor`
carrying a complexity `cx : α → ℕ∞`, an infinitude of distinct `member`s below it whose complexities
climb strictly, and the identity field `cx_floor_eq_iSup : cx floor = ⨆ n, cx (member n)` — the floor's
complexity IS the supremum of the infinitude's.

Its consequence, `infinitude_forces_infinite_complexity` (`cx floor = ⊤`), says the infinitude of
(distinct, complexity-climbing) zeros is what MAKES the floor infinitely complex — recovering the
framework's `addVal_bot` (v₂(0) = ⊤, `ZeroParadox/Valuation/FloorWitness.lean`) as a fact ABOUT the
infinitude, not a separate assertion. "Same" is realized as "both are consequences of one
requirements-structure, met by one witness," not as a cross-type `=`.

Substance is in the WITNESS: the non-degenerate instance is ℚ₂ (floor = 0, cx = the 2-adic valuation,
member n = 2ⁿ⁺¹ so cx(member n) climbs to ⊤ = v₂(0)). All of it is present and proved: the abstract
requirements, the payoff theorem, a toy witness (ℕ∞), the power-series witness, and the full ℚ₂ witness
with the 0 = ∞ inversion.

## NO-GO — what the requirements class does and does not pin down

**The sharp form, and it is a CHARACTERISATION rather than a bare negative.** `[InfinitudeFloor α]` does
constrain `α`: `member_injective` supplies `ℕ ↪ α`, so **the class forces `α` to be INFINITE** and no
finite type can carry it. What it does **not** do is constrain `α` any further — the fields are
satisfiable on a carrier whose only relevant property is that infinitude, with every field discharged
from hand-written data. The honest statement is therefore:

> **`Nonempty (InfinitudeFloor α) ↔ Infinite α`** — the class pins down infinitude and nothing else.

That biconditional is `infinitudeFloor_nonempty_iff_infinite`, so "nothing else" is proved rather than
inferred from one witness.

⚠ **Do not say the class "says nothing about `α`" or that membership "carries no content".** Both are
refuted by `member_injective` in the same file. `ZeroParadox/Algebra/Wheel.lean` carries a dated
correction retiring exactly that sentence shape, on the ground that it tells a reader to discard
legitimate results.

⚠ **The no-go witness is the toy TRANSPORTED, not a new carrier.** `BookkeepingCarrier = ℕ ⊕ Unit` is
canonically equivalent to `ℕ∞` (`Equiv.optionEquivSumPUnit`, since `ℕ∞ = WithTop ℕ = Option ℕ`), and its
`cx` is that equivalence's inverse — the toy witness's `cx = id` in other clothing. **The delta is the
STATEMENT of the no-go, not the carrier.** What is new, as measured on 2026-08-07 across the eight other
files using the class: **no corpus file states the no-go for `InfinitudeFloor`, and the class has no
non-degeneracy predicate.**

## Precedent

`ZeroParadox/Algebra/Wheel.lean` found `WheelValuationStructure` degenerately inhabited — a constant-`⊤`
valuation satisfies every field on any **commutative ring** (that class extends `CommRing`; not "any
carrier") — and answered with an explicit `WVSNondegenerate` predicate plus the standing rule that
constructions over it carry that predicate as a hypothesis. `InfinitudeFloor` has no analogue. The older
sibling is `trivialSelfApp` (`ZeroParadox/Computability/SelfApp.lean`), which `Wheel.lean` names as what
its own gauge mirrors.

## Prior art — the shape is standard and the framework joins it

Degenerate models of an axiom set, and non-degeneracy stated as an **inequation**, are ordinary
universal algebra. Burris & Sankappanavar, *A Course in Universal Algebra* (all three passages read from
the filed copy): an algebra is *"trivial if |A| = 1"* (§ II.1, p. 26); *"as trivial algebras satisfy any
quasi-identity"* (p. 250); and — the load-bearing one — *"As a trivial algebra cannot satisfy a negated
atomic formula, exactly one of Ψ₁, …, Ψₖ is atomic"* (p. 251).

**That last is WHY a non-degeneracy condition has to be stated as an inequality**: a trivial model
satisfies every positive axiom, so only a negated atom excludes it. It is the shape `WVSNondegenerate`,
`0 ≠ 1` and Mathlib's **`Nontrivial`** all take; `Nontrivial` / `Valuation.IsNontrivial` (the latter
already named in `Wheel.lean`) are the idioms to reach for if a predicate is ever added here.

⚠ Those sentences wrap across lines, and a tight pattern with a result limit misses them while the
book's own index reads *"Quasi-identity 250"*. Grep loosely.

⚠ This is **not** an instance-of relation either way: `InfinitudeFloor` degenerates in its **chosen
data**, not in its **carrier**. Shared shape, nothing more.

⚠ **The degeneracy is not walled off by statability.** `TopologicalSpace (ℕ ⊕ Unit)` synthesizes, so the
members' convergence to the floor is perfectly statable on the bookkeeping carrier; a gate probe
reported a full `InfinitudeFloorInversion` witness there under the indiscrete topology, with
`pole_inversion` going through. **That extension is NOT built** — this is recorded so no reader infers a
protection that was never established.
