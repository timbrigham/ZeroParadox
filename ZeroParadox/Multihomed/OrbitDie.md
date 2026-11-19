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
every natural arrives at `0` of ℕ under halving (`od_halve_arrives`). Doubling on ℝ never lands either
(`od_PM_same_shape`), and neither does the Markov step from an unbalanced start
(`od_NM_markov_fit`). All of these "never lands" fits come from one die lemma, `od_never_arrives`,
which repackages `Motion.not_noEntry_of_arrives`.

- § I. The obstruction `od_RT_collapse` runs ONE WAY: a map from halving to doubling that carries
  steps is `0`. Uses from the source: the self-step at `0` and the one-step path `n → 0`. Uses from
  the target: `0` is the only fixed point, and every step into `0` starts at `0`. It uses nothing
  2-adic (`od_RT_collapse_ring`, `od_RT_collapse_real`). Its controls sit on both ends:
  `od_RT_collapse_control_target`, `od_RT_collapse_control_source`. The reverse direction is not
  obstructed (`od_RT_reverse_map`); that map uses the 2-adic contraction.
- § II. On the die the two places have the same shape. The difference is DATA, an order lifted along
  the norm (`od_PM_fit`: `StepLowers` on `Q₂`, `StepRaises` on ℝ). The obstruction is INVARIANT under
  reversing the map: `od_PM_collapse` and `od_PM_collapse_rev`. Each uses the step square, the
  monotonicity (`od_PM_collapse_control_mono`) and the contraction on the `Q₂` side
  (`od_PM_collapse_control`). The `Tendsto` halves of the source do not fit, since a motion carries
  no topology (`ZeroParadox/DieCannotBe.lean`, the remark beside `Motion.Arrives`).
- § III. `odQ2toMarkovHom` is a strict map from doubling on `Q₂` into the Markov motion. It sends
  `0` to a balanced point and `x ≠ 0` to an unbalanced one (`od_NM_hom_balance`). The source's Markov
  conjunct starts ON the balanced line (`od_NM_source_markov`). So its "no correspondence" comes from
  the choice of start, and the dynamics do correspond. A map from halving into the Markov motion is
  constant (`od_NM_halve_collapse`).

## Prior art

- Corpus: `Motion.not_noEntry_of_arrives`, `Motion.eq_of_reflTransGen_of_noEntry`,
  `Motion.arrives_ofFun_iff`, `Motion.run_const_of_selfOnlyAt`, `Motion.arrives_of_acc`,
  `Motion.StepLowers`, `Motion.StepRaises`, `Motion.Hom` (`ZeroParadox/Die.lean`). Step-carrying for
  function motions is `Motion.semiconj_iff_exists_relHom`; the neighbours of `od_selfstep_image` are
  `Motion.isEmpty_relHom_of_step_self` and `Motion.selfOnlyAt_relHom`. `od_double_noEntry` restates
  an anonymous `example` in `ZeroParadox/DieCannotBe.lean` (beside
  `Motion.eq_of_step_to_ofFun_iff_iterate`).
- Mathlib: `Function.Semiconj` and `Function.IsFixedPt.map`. Each is an `example` in § 0 of the Lean
  file. LeanExplore, 2026-11-18, query "semiconjugacy maps fixed points to fixed points", also
  returned `Function.Semiconj.mapsTo_fixedPoints` and `Function.Semiconj.mapsTo_periodicPts`.
- Literature: theoremsearch, 2026-11-18, one informal phrasing ("a semiconjugacy ... into a system
  whose fixed point has no other preimage is constant"). It returned semiconjugacy definitions and
  results about fixed and periodic points under conjugacy, none stating the collapse. That null is
  uninformative.
