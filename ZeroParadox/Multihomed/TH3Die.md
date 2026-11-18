# TH3Die — T-H3's four conjuncts as die motions

Ride-along companion to `ZeroParadox/Multihomed/TH3Die.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXII.

## Formal Overview (AI-assisted)

T-H3 (`th3_snap_all_functors`, `ZeroParadox/Multihomed/CategoricalBridge.lean`) conjoins four facts on
four carriers and relates none of them to another. This file reads each conjunct as a property of a
`Motion` (`ZeroParadox/Die.lean`) on its own carrier:

- (A) `MachinePhase`: UP is `join · c₁`; conjunct (A) is verbatim the membership `th3_A_iff`.
- (B) `Q₂`: OVER is Mathlib's `Joined`; every step into `0` starts at `0` (`th3_B_fit`). The role
  `SelfOnlyAt` is occupied at EVERY point of `Q₂` (`th3_B_every_point_selfOnly`), so (B) does not
  single out `0`.
- (C) the mixture as UP; `Th3JsdAlong` is a property defined in the file, not die vocabulary.
  The fit holds only as DATA (`th3_C_fit`).
- (D) `StateSpace n`: UP is projection onto `ℂ ∙ e₀`; with OVER `e₀ → e₁` the motion climbs
  (`th3_D_climb`).

Each fit has a failing control beside it and a reversed or dual chart. § V of the Lean file holds two
obstructions through maps of carriers (`th3_AB_collapse`, `th3_AD_no_upLax`), each with a control
showing the second conjunct is used. No equation across carriers is stated.

## Prior art

- Corpus: `machineJoinMotion`, `snapEmbedHom` (`ZeroParadox/Ordinal/Incompleteness.lean` § I-b);
  `disconnectedness_forbids_path` (`ZeroParadox/Valuation/BranchingSnapChain.lean`), from which
  `th3_joined_eq` is derived; `Motion.ofStarProjection` (`ZeroParadox/State/DieProjection.lean`, real
  scalars).
- Mathlib: `Joined` and `PathConnectedSpace.joined` (adopted for OVER in § II);
  `Submodule.starProjection_singleton`.
- Literature: ProofWiki, "Totally Disconnected Space is Totally Pathwise Disconnected".
  `Reading:` CARRIER — the textbook form of `th3_joined_eq`.
