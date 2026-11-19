# CollapseDie — the collapse family as die motions

Ride-along companion to `ZeroParadox/Multihomed/CollapseDie.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXIV.

## Formal Overview (AI-assisted)

Six legacy results read as facts about maps between `Motion`s (`ZeroParadox/Die.lean`) share one
argument. § 0 of the Lean file states it once, in two forms, plus a loop obstruction:

- IN form, `cd_collapse_in`: every point has a path of steps to `y`, and every step of the target
  into the image of `y` starts there. A step-carrying map is then constant.
- OUT form, `cd_collapse_out` (locally `cd_fan_collapse`): `t` steps to every point, and the image of
  `t` has at most one successor. A step-carrying map is then constant.
- Loop obstruction, `cd_not_injective_of_loop`: a lax map out of a motion that loops, into one whose
  landings step only to themselves, is not one-to-one. Its first half, a self-step mapped into a step
  with no self-step, is `Motion.isEmpty_relHom_of_step_self`.

What each form consumes is a property of the target's step at one point: no other entry (IN), or at
most one successor (OUT). A fixed point at the image is forced by the conclusion; it is not a
hypothesis. Into a function motion the OUT form needs no hypothesis on the target at all, because a
function has one successor everywhere.

Each section below is an instance, with its controls beside it in the Lean file.

- § I, T-IZ (`t_iz_complete`, `ZeroParadox/Valuation/SemilatticeInstance.lean`). A map carrying the
  join step of a `ZPSemilattice` to doubling on `Q₂` is `0` (`cd_tiz_doubling_collapse`, the OUT form
  at the bottom of the semilattice). Reversing the join step gives the IN form at the same point
  (`cd_tiz_reverse_doubling_collapse`). Both use only A4 (`bot_join`). The convergence conjunct of
  T-IZ is left out: convergence to `0` is not invariant under isomorphism of motions, so it belongs to
  a separate metric probe.
- § II, floors (`floor_reach_separates_mu_nu`, `ZeroParadox/Order/WellFoundedObstruct.lean`). A
  semiconjugacy from `Nat.pred` to doubling on `Q₂` is `0` (`cd_pred_to_doubling_const`, through
  `cd_semiconj_const`). The other direction is not obstructed (`cd_doubling_to_pred`).
- § III, the valuation bridge (`realization_bridges_both_valuations`,
  `ZeroParadox/Valuation/ScaleRealization.lean`). A realization sends ⊥ of `L` to `0` of `Q₂`
  (`cd_realization_bot`), so the source's hypothesis `x ≠ ⊥` follows from `ρ x ≠ 0`, and
  `cd_realization_bridges` drops it. The offset between the two valuations is constant along the
  orbit (`cd_banks_offset`). The back clause holds forward (`cd_forward_stepBack`) and fails in the
  reversed chart at any point with no predecessor (`cd_reverse_no_stepBack`).
- § IV, T-H2 (`th2_singularity_compatibility`, `ZeroParadox/Multihomed/CategoricalBridge.lean`).
  `cd_run_into` uses only AX-G2's shape at one object. `cd_no_map_to_accumulation` is the loop
  obstruction's first half: an identity morphism is a self-step, and `succ` has none.
- § V, the miniature (`Miniature.shape`, `ZeroParadox/Miniature.lean`). Two-way branching fits on the
  two-point pole (`cd_pole_fans_two`), with the node one of its own two successors, and three-way
  does not (`cd_pole_no_three`). A map from the
  collapse `cZero` into `+ 1` on `ℕ∞` is constant `⊤` (`cd_floor_to_tower`, the IN form at `zero`).
- § VI, fixed points (`both_fixed_points_exist`, `ZeroParadox/Ordinal/Incompleteness.lean`). Every lax
  map from `shiftMotion c` to `ordinalTowerMotion` takes only fixed points of `α ↦ ω^α` and has
  period `⌜c⌝` (`cd_shift_tower_periodic`). For `⌜c⌝ ≠ 0` none is one-to-one, and none goes the other
  way (`cd_no_laxHom_tower_shift`). Neither consumes that `c` is a quine, nor that the fixed point is
  the least one.

Left out: anything a probe showed does not fit (T-IZ's convergence conjunct), the fits that restate
corpus content, and the hom-motion characterizations of `KleisliCat PMF` and `TopCat`, which are not
collapses.

## Prior art

- Corpus: `od_collapse`, `od_selfstep_image` (`ZeroParadox/Multihomed/OrbitDie.lean`);
  `Motion.isEmpty_relHom_of_step_self`, `Motion.selfOnlyAt_relHom`, `Motion.semiconj_iff_exists_relHom`,
  `Motion.arrives_ofFun_iff_reflTransGen`, `Motion.LaxHom.loop` (`ZeroParadox/Die.lean`);
  `machineJoinMotion` (`ZeroParadox/Ordinal/Incompleteness.lean`), of which `cdJoinStep` is the
  general form; `banks_are_independent` (`ZeroParadox/Valuation/ScaleRealization.lean`).
- Mathlib: `RelHom`, and `SimpleGraph.Walk.IsCycle.map` (an injective graph homomorphism carries a
  cycle to a cycle), the graph form of `Motion.LaxHom.loop`, which `cd_not_injective_of_loop` uses.
- Search, 2026-11-18: corpus grep for "single-valued", "at most one successor", "not_injective" and
  "collapse"; LeanExplore, "relation homomorphism into a functional relation identifies two
  successors of one point", returned only the `RelHom` API; theoremsearch, informal, "a homomorphism
  of transition systems from a system with a vertex adjacent to every vertex into a deterministic
  system is constant", returned determinization results, none stating the collapse; theoremsearch,
  formal, "injective map preserving a cycle into a graph where fixed points have no other
  successors", returned `SimpleGraph.Walk.IsCycle.map`. These nulls are uninformative.
