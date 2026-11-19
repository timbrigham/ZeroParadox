# TH3Die — T-H3's four conjuncts as die motions

Ride-along companion to `ZeroParadox/Multihomed/TH3Die.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXII.

## Formal Overview (AI-assisted)

T-H3 (`th3_snap_all_functors`, `ZeroParadox/Multihomed/CategoricalBridge.lean`) conjoins four facts on
four carriers and relates none of them to another. This file reads each conjunct as a property of a
`Motion` (`ZeroParadox/Die.lean`) on its own carrier:

- (A) `MachinePhase`: UP is `join · c₁`; conjunct (A) is equivalent, in both directions, to the
  membership in `th3_A_iff`.
- (B) `Q₂`: OVER is Mathlib's `Joined`; every step into `0` starts at `0` (`th3_B_fit`). The role
  `SelfOnlyAt` is occupied at EVERY point of `Q₂` (`th3_B_every_point_selfOnly`), so (B) does not
  single out `0`.
- (C) `BinaryState → ℝ`: the mixture as UP; `Th3JsdAlong` is a property defined in the file, not die
  vocabulary. The fit holds only as DATA (`th3_C_fit`).
- (D) `StateSpace n`: write `th3E0`, `th3E1` for `transitionOp n` at indices `0` and `1`. UP is
  projection onto `ℂ ∙ th3E0`; with OVER `th3E0 → th3E1` the motion climbs (`th3_D_climb`).

Each fit has a failing control beside it and a second chart: a reversed motion for (A), (B) and (C)
(`th3_A_reverse`, `th3_B_reverse`, `th3_C_reverse_motion`), an order dual for (A) (`th3_A_dual`), a
swap of the two summands for (C) (`th3_C_reverse`), and a swap of the basis vectors for (D)
(`th3_D_swap`). § V of the Lean file holds two obstructions through maps of carriers
(`th3_AB_collapse`, `th3_AD_no_upLax`), each with a control. The first holds at every point, not only
at `0` (`th3_AB_collapse_any`); the second needs only that the projection of the image of `c₀` onto
`ℂ ∙ th3E0` is not `th3E0` (`th3_AD_no_upLax_of_proj_ne`). No equation across carriers is stated.

## Prior art

- Corpus: `machineJoinMotion`, `snapEmbedHom` (`ZeroParadox/Ordinal/Incompleteness.lean` § I-b);
  `disconnectedness_forbids_path` (`ZeroParadox/Valuation/BranchingSnapChain.lean`), from which
  `th3_joined_eq` is derived; `Motion.ofStarProjection` (`ZeroParadox/State/DieProjection.lean`, real
  scalars).
- Mathlib: `Joined` and `PathConnectedSpace.joined` (adopted for OVER in § II);
  `Submodule.starProjection_singleton`. `Statement:` CARRIER — `TotallyDisconnectedSpace.eq_of_continuous` (a continuous map
  from a preconnected space into a totally disconnected one is constant) gives `th3_joined_eq` when
  applied to a path. `Submodule.starProjection_apply_eq_zero_iff` with
  `Submodule.mem_orthogonal_singleton_iff_inner_right` gives `th3_D_up_zero_iff`.
- Literature: ProofWiki, "Totally Disconnected Space is Totally Pathwise Disconnected".
  `Reading:` CARRIER — the textbook form of `th3_joined_eq`.
