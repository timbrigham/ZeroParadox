# OrbitDie — the orbit family as die motions

Ride-along companion to `ZeroParadox/Multihomed/OrbitDie.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXIII.

## Formal Overview (AI-assisted)

Three results each set doubling on `Q₂` beside another dynamics:
`padic_nat_no_orbit_correspondence` (`ZeroParadox/Valuation/RateTransport.lean`),
`doubling_place_dichotomy` (`ZeroParadox/Valuation/PlaceMetric.lean`) and
`padic_markov_no_orbit_correspondence` (`ZeroParadox/Valuation/NuRateMatch.lean`). This file reads
each as a fact about `Motion`s (`ZeroParadox/Die.lean`), each fit beside a failing control.

**The first unjustified step is reading the three as "never lands against lands".** Only the first
has that shape. Doubling on `Q₂` never arrives at `0` of `Q₂` from `x ≠ 0` (`od_RT_padic_fit`), and
every natural arrives at `0` of ℕ under halving (`od_halve_arrives`). Doubling on ℝ never lands from
a nonzero rational start either (`od_PM_same_shape`, `x : ℚ`, `x ≠ 0`), and neither does the Markov
step from an unbalanced start (`od_NM_markov_fit`). All of these "never lands" fits come from one
die lemma, `od_never_arrives`, which repackages `Motion.not_noEntry_of_arrives`.

- § I. The obstruction `od_RT_collapse` runs ONE WAY: a map from halving to doubling that carries
  steps is `0`. It is `od_RT_collapse_ring` at `Q₂`, which holds on any commutative ring. From the
  source it uses the self-step at `0` and the fork at `2n`, which steps to both `n` and `0`. From
  the target it uses only that doubling is a function and that `z = 2z` forces `z = 0`. It does not
  use the target's no-entry at `0`, which fails in `ZMod 4` while the collapse holds there. The
  fork is the shape of `execution_requires_branching`'s conclusion, the single-valued target is
  `deterministic_has_no_fanout` (`ZeroParadox/Computability/Occurrence.lean`), and the local OUT
  form is `cd_fan_collapse` (`ZeroParadox/Multihomed/CollapseDie.lean`). Controls on the target
  remove single-valuedness alone, `z = 2z ⇒ z = 0` alone, and both at once
  (`od_RT_collapse_control_target`); `od_RT_collapse_control_source` takes successor on ℕ as the
  source, which has no self-step and no fork. `od_RT_collapse_real` is the ring version at ℝ. `od_RT_collapse_fun` has a function source
  with no fork, and its proof uses no-entry at `0` of `Q₂`. Into `ofFun Nat.pred`, which has one
  fixed point and an entry into it, the fork-free source admits a nonconstant map. Whether no-entry
  is needed there inside a commutative ring is not measured. The reverse direction is not obstructed
  (`od_RT_reverse_map`); that map uses the 2-adic contraction.
- § II. On the die the two places have the same shape. The difference is DATA, an order lifted along
  the norm (`od_PM_fit`: `StepLowers` on `Q₂`, `StepRaises` on ℝ). The obstruction is INVARIANT under
  reversing the map: `od_PM_collapse` and `od_PM_collapse_rev`. Each uses the step square, the
  monotonicity, the contraction on `Q₂` and the expansion on ℝ: `od_PM_collapse` uses
  `StepLowers` on `Q₂` and `‖2‖ = 2` on ℝ, and `od_PM_collapse_rev` uses `StepRaises` on ℝ and the
  contraction on `Q₂`. The controls `od_PM_collapse_control_mono` and `od_PM_collapse_control` are
  for the forward direction only. The `Tendsto` halves of the source do not fit the function
  motions of this file, since `Motion.ofFun` carries no topology (`ZeroParadox/DieCannotBe.lean`,
  the remark beside `Motion.Arrives`). They do fit a limit motion, whose UP is the limit retraction:
  `lm_q2_doubling_closure_at_zero` and `lm_real_doubling_closure_at_infty`
  (`ZeroParadox/Multihomed/LimitMotion.lean`).
- § III. `odQ2toMarkovHom` is a strict map from doubling on `Q₂` into the Markov motion. It sends
  `0` to a balanced point and `x ≠ 0` to an unbalanced one (`od_NM_hom_balance`). The source's Markov
  conjunct starts ON the balanced line (`od_NM_source_markov`). So its "no correspondence" comes from
  the choice of start. In the direction from `Q₂` to the Markov motion the dynamics correspond
  through this strict map; no map in the other direction is built. A map from halving into the
  Markov motion is constant (`od_NM_halve_collapse`). Its proof uses only the fork and that the
  Markov step is a function, so the same holds into any function motion.

## Prior art

- Corpus: `Motion.not_noEntry_of_arrives`, `Motion.eq_of_reflTransGen_of_noEntry`,
  `Motion.arrives_ofFun_iff`, `Motion.run_const_of_selfOnlyAt`, `Motion.arrives_of_acc`,
  `Motion.StepLowers`, `Motion.StepRaises`, `Motion.Hom` (`ZeroParadox/Die.lean`). Step-carrying for
  function motions is `Motion.semiconj_iff_exists_relHom`; the neighbours of `od_selfstep_image` are
  `Motion.isEmpty_relHom_of_step_self` and `Motion.selfOnlyAt_relHom`. `od_double_noEntry` restates
  an anonymous `example` in `ZeroParadox/DieCannotBe.lean` (beside
  `Motion.eq_of_step_to_ofFun_iff_iterate`). The fork and single-valuedness halves are
  `execution_requires_branching` and `deterministic_has_no_fanout`
  (`ZeroParadox/Computability/Occurrence.lean`).
- Standard name: a map carrying every step to a step is a functional simulation (Dubut and Wißmann,
  arXiv:2301.07004, Def. 2.1, pp. 2–3, after Joyal, Nielsen and Winskel). The name is for the
  hypothesis; it does not name the collapse.
- Mathlib: `Function.Semiconj` and `Function.IsFixedPt.map`. Each is an `example` in § 0 of the Lean
  file. `Function.Semiconj.mapsTo_fixedPoints` and `Function.Semiconj.mapsTo_periodicPts` are
  neighbours.
- Search for the collapse, 2026-11-18: theoremsearch, three phrasings (digraph homomorphism into
  out-degree at most one; relation-preserving map into a functional relation; formal, `RelHom`
  constant along `ReflTransGen` into a point with only a self-loop entry), returned definitions and
  the `RelHom` and `ReflTransGen` API only. LeanExplore, three phrasings, returned `RelHom`,
  `ReflTransGen` and `Function.Semiconj.mapsTo_fixedPoints`. GitHub `extension:lean`, one query,
  returned nothing related. The open web, two queries, returned work on retracts and pseudoforests
  and the functional-simulation background above. `exact?` at the pin found no library lemma for the
  OUT form. No standard name for the collapse was located as of that date; the nulls are
  uninformative.
