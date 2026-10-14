# SelfApp — ride-along documentation

Moved from `ZeroParadox/Computability/SelfApp.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## The question

ZPJ imports three fields from AFA (via AFAStructure):
  `selfMem`, `bot_self_mem`, `quine_unique`

These encode Aczel's AFA content but appear as axioms in the Lean encoding
because the abstract lattice lacks the graph-decoration semantics needed to
derive them. This file asks: can they be derived from something more primitive?

## The fixed-point identification

Two facts from different ZP layers:
  - Set theory (ZPJ / AFA): ⊥ is the unique fixed point of x ↦ {x}
  - 2-adic (ZPB): 0 is the unique fixed point of x ↦ 2x (characterised by v₂ = +∞)

These are the same abstract pattern: the domain's self-application operation has a
unique fixed point, and that fixed point is the "bottom" of the domain. Neither
requires DC — uniqueness collapses construction to identification (ZeroParadox/Settheory/AczelConn.lean).

## What this file does

Introduces `AbstractSelfApp`: a typeclass encoding the minimal fixed-point
structure. From it, `selfMem`, `bot_self_mem`, and `quine_unique` are derived
as theorems rather than class fields — reducing AFAStructure's axiom load to a
single structural commitment (selfApp + fixed_bot + unique_fp).

The 2-adic parallel is then proved standalone: `singleton_from_unique_witness`
(already proved in ZeroParadox/Settheory/AczelConn.lean) closes the Q₂ case with the same proof term.
Both domains are formally instances of the same abstract pattern.

## What the Scale files resolved

The abstract valuation typeclass described here as the remaining ZPB→ZPJ gap is
`ValuationStructure`, defined in `ZeroParadox/Valuation/Scale.lean`. That file derives the
unique-fixed-point chain without an AFA import:
  ValuationStructure → scale_ne_fixed → AbstractSelfApp (unique_fp as theorem)
`ZeroParadox/Valuation/ScaleBridge.lean` further extends this: ValBridge drops the ZPSemilattice
constraint entirely, and both ℤ_[2] and ZPSemilattice types become instances
of a common ancestor. The formal gap described here is closed.
