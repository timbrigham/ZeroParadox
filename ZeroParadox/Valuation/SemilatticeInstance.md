# SemilatticeInstance — ZP-I: Inside Zero

Ride-along companion to `ZeroParadox/Valuation/SemilatticeInstance.lean`.

## Theorem T-IZ, stated exactly

Every maximal ascending chain in the Zero Paradox framework is a Cauchy sequence that
**converges to 0 in Q₂**. That is the whole of what is proved about the chain.

⚠ **Two further readings, both commitments, neither part of the statement:**

1. **Occupancy** — reading that limit as an OCCUPANT of the ⊥ role. This is not merely
   unproved. `ZPSemilattice ℚ_[2]` does not synthesize, so the join-identity is **not statable**
   of the limit: a type error, not a missing lemma.
2. **Novelty** — reading that occupant as the chain's own *successor* null. This is C-DA2, and
   `Order/SnapCannotBe.lean:43` forbids citing `t_iz_limit_is_new_null` as its witness.

So there are three tiers, and `CLAIMS.md`'s T-IZ row is the ratified statement of them:
**convergence PROVED · role-recognition PROVED as an implication · occupancy a COMMITMENT ·
novelty a further COMMITMENT.**

## What `t_iz_complete` is, and what it is not

It carries all four formal steps in one theorem **as a CONJUNCTION, not a chain**. Its signature
takes `S : ℕ → Q₂` and, separately, a `terminal` in an arbitrary Kleene-structured semilattice
`L'` with the role property handed in as `h_role`. **Nothing relates the two objects.**

The anonymous `example` beside the theorem is the NO-GO gauge: it discharges the whole
conjunction with `S` the constant `0` in Q₂ and `terminal` at `MachinePhase` — a two-element type
with no map to or from the 2-adics. A theorem that said anything about the 2-adic limit could not
be satisfied that way.

⚠ Two measurements worth keeping, both from running rather than reading. The unlinkedness is
**not** an artifact of degenerate inputs: it still discharges at `S n = 2ⁿ` (nonzero at every
stage) with `ε₀' = MachinePhase.running`. And the `L'` interface is **not** vacuous — discharging
at `ℕ` fails on `KleeneStructure`/`AFAStructure`, so "arbitrary semilattice" understates it; it is
an arbitrary *Kleene-structured* one.

## What `HasNoTop` does, and what it does not

⚠ This is the ORDER property `HasNoTop` (`ZeroParadox/Order/Lattice.lean`), **not ZP-A's R1**.
ZP-A's R1 is the no-subtraction restriction, and `t_snap_irreversible` cites it in that sense.

`HasNoTop L := ∀ x : L, ∃ y : L, le x y ∧ x ≠ y` says a strictly greater element always exists, so
no chain halts for want of anywhere to go. That is AVAILABILITY, and it is all it is.

What makes a *particular* chain ascend is `IsStrictStateSequence`, and that is the hypothesis
`h_strict_from_r1_t3` actually binds. `HasNoTop` appears nowhere in its signature.

The NO-GO gauge in § Ib exhibits the gap twice. `ℕ` has no top (`nat_has_no_top`) and the constant
chain is a state sequence *in that same lattice* that never moves; and a second, generic example
proves the stalling half holds at **any** element of **any** `ZPSemilattice`. So availability fails
to force occurrence in every lattice where the question can even be posed — the same distinction
`tsnap_holds_but_nothing_moves` makes for T-SNAP.

Do not correct an overstatement here by deleting the property from the account; that is the
retraction overshooting (`DC-30`). It is load-bearing, for its own conclusion.

⚠ **No-top does NOT put the limit outside `L`.** Whether a chain's limit escapes its carrier is a
property of the particular lattice, never a consequence of no-top: the ordinals under `max` have no
top, and the chain `n ↦ (n : Ordinal)` has least upper bound ω, which is *inside* `Ordinal`. The
framework's own `InfinitudeFloor` declares `floor : α` and `member : ℕ → α` in the SAME type and
defines the floor's complexity as the supremum of the climbers'. `tower_height_floor_reconciliation`
(`ZeroParadox/Valuation/TowerHeightFloor.lean`) carries the account this folder uses: two
carrier-specific closures — ε₀ in `Ordinal`, 0 in `ℤ_[2]` — co-witnessed by one construction and
held apart by the antitone map `cnfToZp2`, never identified.

**The chain approaches the 2-adic depth of zero by its own forward motion, not by reversing
direction.** No inverse operation is used, and none is available in the lattice — the signature has
`join` and `bot` and nothing else. ⚠ **But that is not why the convergence holds.** `t_iz_cauchy`
binds `(S : ℕ → Q₂)` and `h_bound` and nothing else, with no lattice anywhere in its signature, and
`Q₂` is a field in which subtraction elaborates. What forces convergence is the norm bound, which
traces back to the assumed strict ascent. The lattice's lack of subtraction is a fact about where
the chain lives, not about why its image converges.

## The null-balance theorem carries less than its name suggests

`c_t_iz_null_balance` proves exactly one thing: `S ≠ ⊥ → ¬(∀ x, join S x = x)`. The join-identity
role is **exclusive to ⊥** — one direction, inside one semilattice.

It does **not** carry the additive balance `0 + x + (−x) = 0`, and that identity is not statable in a
`ZPSemilattice` at all: the signature has `join` and `bot` and no additive inverse.

Nor does it establish that the 2-adic limit *occupies* the role. `#synth ZPSemilattice ℚ_[2]` fails
(verified by running), so `∀ x, join S x = x` is not a well-formed proposition of that limit — a type
error, not a missing lemma. Occupancy is a commitment; reading the occupant as a successor ⊥′ is a
further one (C-DA2).

## The layer's components

- **§ I** Cauchy convergence — the topological core (inherits `Classical.choice` from Mathlib analysis)
- **§ Ib** `h_strict` from `IsDepthChain` + `IsStrictStateSequence` — closes R-IZ-A (proved)
- **§ II** Valuation-complexity bridge — SUPERSEDED by the AFA path (see § III-B)
- **§ III** The T-IZ theorem, the successor-null reading, and framework closure (proved)
- **§ III-B** `t_iz_complete` — the four steps via the AFA/Kleene path (proved)
- **§ III-C** `t_iz_complete_from_axioms` — the depth-chain bridge (proved). Its hypotheses are
  NOT all ZP-A conditions: only `IsStrictStateSequence` is, and it constrains the depth index.
  `hS` (nowhere zero) and `IsDepthChain` live in ℚ_[2], and `IsDepthChain` binds no semilattice.
  ⚠ It still carries `h_role` explicitly, which is the one hypothesis nothing here grounds.

## The Kolmogorov bridge is bypassed, not closed

Steps 2–6 are formalized without it: DA-1 fires at any element identified as ⊥′ by DA-2, and step 4
discharges from `AFAStructure` fields alone, so no Kolmogorov complexity is computed. **Step 2's K
bridge is bypassed, not shown closed** — a fact about this proof route, not a demonstration that the
two paths are one property.

## Dependencies

ZP-E (full synthesis: ZP-A, ZP-B, ZP-C, ZP-D), ZP-K (`KleeneStructure`), plus
`Mathlib.Analysis.SpecificLimits.Basic` for the geometric `tendsto` lemmas.

## § III-C, the depth-chain bridge, in full

`t_iz_complete` is formally complete without this section; it exists as a transparency layer for a
reviewer who wants to trace the chain from the ZP-A lattice axioms to convergence without meeting
an ungrounded hypothesis.

The gap it closes is one factor wide. `t_iz_complete` takes `h_bound : ∀ n, ‖Sₙ‖ ≤ (2⁻¹)ⁿ`. The §Ib
theorems derive strict valuation growth from IsDepthChain plus IsStrictStateSequence, but `t_iz_r1_t3_geometric_bound`
produces `‖Sₙ‖ ≤ ‖S₀‖ · (2⁻¹)ⁿ` — one `‖S₀‖` factor short of that.

The bridge absorbs the factor: `IsDepthChain` forces `(S 0).valuation = depths 0 ≥ 0`, which in `Q₂`
means `‖S 0‖₂ = 2^{-depths(0)} ≤ 1`. Multiplying through by `‖S 0‖ ≤ 1` recovers the exact `(2⁻¹)ⁿ`
bound.
