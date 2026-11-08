# SelfApp — ride-along documentation

Moved from `ZeroParadox/Computability/SelfApp.lean` on 2026-10-13. ⚠ **At the move this content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED, and moving it changed that by exactly nothing.** The text has been edited since the move; this banner records its state on 2026-10-13 and does not record whether any review has taken place since.

In the sections below, "this file" and "here" refer to `ZeroParadox/Computability/SelfApp.lean`.

## The question

ZPJ imports three fields from AFA (via AFAStructure):
  `selfMem`, `bot_self_mem`, `quine_unique`

These encode Aczel's AFA content but appear as class fields in the Lean encoding
because the abstract lattice lacks the graph-decoration semantics needed to
derive them. This file asks: can they be derived from something more primitive?

## The fixed-point identification

Two facts from different ZP layers:
  - Set theory (ZPJ / AFA): ⊥ is the unique fixed point of x ↦ {x}
  - 2-adic (ZPB): 0 is the unique fixed point of x ↦ 2x (characterised by v₂ = +∞)

These follow an analogous pattern: the domain's self-application operation has a
unique fixed point, and that fixed point is the "bottom" of the domain. Membership in
`AbstractSelfApp` does not discriminate: every `ZPSemilattice` carries one
(`abstractSelfApp_always_inhabited`). Prior art for treating AFA's unique solutions and final
coalgebras of locally contracting functors on complete metric spaces uniformly, as final-coalgebra uniqueness:
Rutten and Turi, "On the Foundations of Final Semantics: Non-Standard Sets, Metric Spaces, Partial
Orders", REX 1992, LNCS 666 (1993) (cited, not claimed). Uniqueness
collapses construction to identification (ZeroParadox/Settheory/AczelConn.lean). Footprints: the
`PurityCheck` section of `ZeroParadox/Computability/SelfApp.lean`.

## What this file does

Introduces `AbstractSelfApp`: a typeclass encoding the minimal fixed-point
structure. Which of `AFAStructure`'s three fields it derives as theorems, and which it
supplies as data: § III of `ZeroParadox/Computability/SelfApp.lean`.

The 2-adic parallel is then proved standalone: `singleton_from_unique_witness`
(already proved in ZeroParadox/Settheory/AczelConn.lean) closes the Q₂ case with the same proof structure.
Why it is standalone rather than an `AbstractSelfApp` instance: § IV of the same file.

## What the Scale files resolved

The 2-adic case above is proved standalone on ℚ_[2], not as an `AbstractSelfApp` instance.
`ZeroParadox/Valuation/Scale.lean` defines `ValuationStructure`, an abstract valuation typeclass over a
`ZPSemilattice`, and derives the unique-fixed-point chain from it without an AFA import:
  ValuationStructure → scale_ne_fixed → AbstractSelfApp (unique_fp as theorem; instance `toAbstractSelfApp`)
Its 2-adic carrier is ℤ_[2], not ℚ_[2]: the `example`s closing `Scale.lean` build a `ZPSemilattice ℤ_[2]`
whose least element is ℤ_[2]'s 0 and put a `ValuationStructure` on it (scale `×2`, val `q2Val`); neither
is registered as an instance. `ZeroParadox/Valuation/ScaleBridge.lean` adds `ValBridge`, which drops the
`ZPSemilattice` requirement: ℤ_[2] (`instZ2ValBridge`) and every `ZPSemilattice` carrying a
`ValuationStructure` (`toValBridge`) are instances, and `scale_unique_fp_free` gives the unique fixed
point on each. Being a `ValBridge` instance does not by itself separate these carriers from a trivial
one: `trivialValBridge` inhabits `ValBridge Unit`.
