# CollapseDie — the collapse family as die motions

Ride-along companion to `ZeroParadox/Multihomed/CollapseDie.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXIV.

## Formal Overview (AI-assisted)

Six legacy results are read here as facts about maps between `Motion`s (`ZeroParadox/Die.lean`).
§ 0 of the Lean file states one collapse lemma, in two forms, plus a loop obstruction:

- IN form, `cd_collapse_in`: every point has a path of steps to `y`, and every step of the target
  into the image of `y` starts there. A step-carrying map is then constant.
- OUT form, `cd_collapse_out` (locally `cd_fan_collapse`): `t` steps to every point, and the image of
  `t` has at most one successor. A step-carrying map is then constant. The source half is two
  successors of `t`, not required distinct, while `execution_requires_branching`'s conclusion has
  them distinct; the target half is `deterministic_has_no_fanout`
  (`ZeroParadox/Computability/Occurrence.lean`).
- Loop obstruction, `cd_not_injective_of_loop`: a lax map out of a motion that loops, into one whose
  landings step only to themselves, is not one-to-one. A related obstruction excludes every
  step-carrying map, not only the one-to-one ones: `Motion.isEmpty_relHom_of_step_self`, a self-step
  has no image in a motion with no self-step.

Each form has one hypothesis on the source and one on the target. The source supplies paths to `y`
(IN) or a point stepping everywhere (OUT). The target is restricted at one point: no other entry
(IN), or at most one successor (OUT). For the OUT form the image of `t` is a fixed point by the
conclusion, since `t` steps to itself. For the IN form it is one when the source has a step (an
`example` beside `cd_collapse_in`); on one point with no steps, into a target with no steps, every
hypothesis holds and the image is not a fixed point (the control beside it). Into a function motion
the OUT form needs no hypothesis on the target at all, because a function has one successor
everywhere. For function motions the IN form's target hypothesis at `f y` says no other point maps
to `f y`; when `f y` is a fixed point, that is `{f y}` backward invariant, `B⁻¹{f y} = {f y}`
(Milnor, § 5, p. 5-2). `cd_semiconj_const` asks it at every fixed point of `B`, more than its proof
uses (the `example` after it states the one-point form).

The sections below take the six legacy results in turn, with controls beside them in the Lean file.
Several do not go through § 0; among them `cd_run_into`, `cd_shift_tower_periodic`,
`cd_realization_bot`, `cd_banks_offset`, the back-clause pair, `cd_pole_fans_two`,
`cd_pole_no_three` and `cd_doubling_to_pred` have their own proofs.

- § I, T-IZ (`t_iz_complete`, `ZeroParadox/Valuation/SemilatticeInstance.lean`). A map carrying the
  join step of a `ZPSemilattice` to doubling on `Q₂` is `0` (`cd_tiz_doubling_collapse`, the OUT form
  at the bottom of the semilattice). Reversing the join step gives the IN form at the same point
  (`cd_tiz_reverse_doubling_collapse`). Of the `ZPSemilattice` laws, the first uses only A4
  (`bot_join`); the reversed one also uses `two_ne_zero` and no zero divisors in `Q₂`. Neither
  statement needs these: every point steps to itself, forward and reversed, by `join_idem`, which
  forces `0` in any commutative ring (an `example` beside each). The convergence conjunct of T-IZ is
  left out here: convergence to `0` is not invariant under strict isomorphism of motions
  (`lm_q2_torn`).
- § II, floors (`floor_reach_separates_mu_nu`, `ZeroParadox/Order/WellFoundedObstruct.lean`). A
  semiconjugacy from `Nat.pred` to doubling on `Q₂` is `0` (`cd_pred_to_doubling_const`, through
  `cd_semiconj_const`). The other direction is not obstructed (`cd_doubling_to_pred`).
- § III, the valuation bridge (`realization_bridges_both_valuations`,
  `ZeroParadox/Valuation/ScaleRealization.lean`). A realization sends ⊥ of `L` to `0` of `Q₂`
  (`cd_realization_bot`), so the source's hypothesis `x ≠ ⊥` follows from `ρ x ≠ 0`, and
  `cd_realization_bridges` drops it. For a realization `ρ` and a point `x` with `ρ x ≠ 0`, the offset
  between the two valuations is constant along the orbit of `x` (`cd_banks_offset`). The back clause
  holds forward (`cd_forward_stepBack`). In the reversed chart it fails at any point with no
  predecessor (`cd_reverse_no_stepBack`); that proof uses that every point of `Q₂` has a half, the
  fact `cd_reverse_control` removes on `ℤ_[2]`.
- § IV, T-H2 (`th2_singularity_compatibility`, `ZeroParadox/Multihomed/CategoricalBridge.lean`).
  `cd_run_into` uses, of the `ZPCategory` fields, only AX-G2's shape at one object, plus composition
  of morphisms. Its control on the same hom motion is the run `0, 1, 1, …` in ℕ. For an inhabited
  category, `cd_no_map_to_accumulation` is an instance of `Motion.isEmpty_relHom_of_step_self`: an
  identity morphism is a self-step, and `succ` has none.
- § V, the miniature (`Miniature.shape`, `ZeroParadox/Miniature.lean`). Two-way branching fits on the
  two-point pole (`cd_pole_fans_two`), with the node one of its own two successors, and three-way
  does not (`cd_pole_no_three`). A step-carrying map from `ofFun cZero` into `+ 1` on `ℕ∞` is
  constant `⊤`
  (`cd_floor_to_tower`, the IN form at `zero`).
- § VI, fixed points (`both_fixed_points_exist`, `ZeroParadox/Ordinal/Incompleteness.lean`). Every lax
  map from `shiftMotion c` to `ordinalTowerMotion` takes only fixed points of `α ↦ ω^α` and has
  period `⌜c⌝` (`cd_shift_tower_periodic`). For `⌜c⌝ ≠ 0` none is one-to-one
  (`cd_shift_tower_not_injective`), and none goes the other way (`cd_no_laxHom_tower_shift`). Neither
  consumes that `c` is a quine, nor that the fixed point is the least one.

Left out: anything a probe showed does not fit (T-IZ's convergence conjunct), the fits that restate
corpus content, and the hom-motion characterizations of `KleisliCat PMF` and `TopCat`, which are not
collapses.

## Prior art

- Corpus: `od_collapse`, `od_selfstep_image` (`ZeroParadox/Multihomed/OrbitDie.lean`);
  `Motion.isEmpty_relHom_of_step_self`, `Motion.selfOnlyAt_relHom`, `Motion.semiconj_iff_exists_relHom`,
  `Motion.arrives_ofFun_iff_reflTransGen`, `Motion.LaxHom.loop` (`ZeroParadox/Die.lean`);
  `execution_requires_branching`, `deterministic_has_no_fanout`
  (`ZeroParadox/Computability/Occurrence.lean`); `machineJoinMotion`
  (`ZeroParadox/Ordinal/Incompleteness.lean`), of which `cdJoinStep` is the general form;
  `banks_are_independent` (`ZeroParadox/Valuation/ScaleRealization.lean`).
- Standard name: the step-carrying hypothesis is the transition clause of a functional simulation
  (Dubut and Wißmann, arXiv:2301.07004, Def. 2.1, pp. 2–3, after Joyal, Nielsen and Winskel). Their
  definition is for labelled transition systems with an initial state, and also asks `f(x0) = y0`;
  the hypothesis here is its unpointed, single-label case. The name is for the hypothesis; it does
  not name the collapse. Their Def. 2.3, an open map, reflects runs, the run-level
  form of `Motion.StepBack`.
- Mathlib: `RelHom`, and `SimpleGraph.Walk.IsCycle.map` (an injective graph homomorphism carries a
  cycle to a cycle), the graph form of `Motion.LaxHom.loop`, which `cd_not_injective_of_loop` uses.
- Search for the collapse, 2026-11-18: corpus grep for "single-valued", "at most one successor",
  "not_injective" and "collapse". theoremsearch, three phrasings (digraph homomorphism into
  out-degree at most one; relation-preserving map into a functional relation; formal, `RelHom`
  constant along `ReflTransGen` into a point with only a self-loop entry), returned definitions and
  the `RelHom` and `ReflTransGen` API only; a further formal phrasing about an injective map
  preserving a cycle returned `SimpleGraph.Walk.IsCycle.map`, cited above. LeanExplore, three
  phrasings, returned `RelHom`, `ReflTransGen` and `Function.Semiconj.mapsTo_fixedPoints`. GitHub
  `extension:lean`, one query, returned nothing related. The open web, two queries, returned work on
  retracts and pseudoforests and the functional-simulation background above. `exact?` at the pin
  closed the OUT form only by a direct term, so no library lemma owns it; for the IN form it timed
  out. No standard name for the collapse was located as of that date; those nulls are
  uninformative.
