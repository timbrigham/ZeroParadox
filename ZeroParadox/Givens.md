# The givens at the die level: what each one is, and the theorem that carries it

Ride-along for `ZeroParadox/Givens.lean`. Each given is a `Prop`, never a field of a class, so each one
can be true of one chart and false of another. All but `GConnected` and `GJoined` take a die `Motion`
(`ZeroParadox/Die.lean`); those two take two points of a topological space. The file proves or
refutes each given chart by chart. The main charts are four limit motions: doubling and halving on the
2-adic sphere `OnePoint ℚ_[2]`, and doubling and halving on the real projective line `OnePoint ℝ`. Further
charts are `machineJoinMotion` on `MachinePhase`, `ordinalSuccMotion` and `ordinalTowerMotion` on
`Ordinal`, `slotMotion`, doubling on ℤ_[2] mapped into `+1` on `ℕ∞`, and every `UpAndOver`. The controls
include `Unit`, a `Fin 3` motion and a constant map; the file labels the rest as CONTROL at their sites.

## The givens

Tim named three. Each one splits into the predicates below.

**(a) Minimally and maximally complex at once.**
- `GMinMax M p q`: `p` steps only to itself, and `p` is the limit sink of every point other than `q`.
  The sink half is one pole of `lmDipole`, which `ZeroParadox/Multihomed/LimitMotion.md` reads as
  north–south dynamics and cites there. It holds at 0 of `ℚ_[2]` under doubling (`q2_GMinMax`). It holds
  at ∞ of `OnePoint ℝ` under real doubling (`real_GMinMax_infty`), and fails there at 0 of ℝ
  (`real_not_GMinMax_zero`). It fails at `c₀`, ⊥ of `MachinePhase`, and at every ordinal of
  universe 0 under `Order.succ` (`ordinal_no_selfOnly`). Controls: the identity on `Unit`, and the constant map at 0
  (`const_GMinMax`). Both meet it, so `GMinMax` alone says little. The constant map has no limit motion
  as its dipole partner (`const_no_limit_partner`).
- `GCoincidence`: a strict map of motions sends a point `y` that steps only to itself and is least in
  the source view to a point that steps only to itself and is greatest in the target view, and sends no
  other point there. It holds for `q2Val` from doubling on ℤ_[2] to `+1` on `ℕ∞`, at ℤ_[2]'s 0
  (`z2_GCoincidence`). With the target fixed as `+1` on `ℕ∞`, it fails at 0 of every field, ℝ and
  `ℚ_[2]` included (`field_no_GCoincidence_any`; the characteristic-0 form is `field_no_GCoincidence`):
  in a field 2 is 0 or a unit, so no `f` with `f (2x) = f x + 1` is finite off 0
  (`no_doubling_valuation_field_any`). On a commutative ring such an `f` exists exactly when 2 is a
  non-zero-divisor and the ring is 2-adically separated (`doubling_counter_iff`,
  `doubling_counter_iff_isHausdorff`).
- Reading: COINCIDENCE, in the valuation chart (`z2_GCoincidence`). The tape-chart reading of (a) is the
  fair-coin ensemble: `tape_totality_two_faces` and `maxEntropy_mlRandom_and_snap_ae`. It sits beside
  the die-level face, and it is not a hypothesis of the snap.

**(b) The run from 0 to infinity is discrete and continuous at once.**
- Discrete face: `GDiscrete M P`, where some step moves and every moving step is a cover, in either
  direction, in the view `P`; and `GCoverAtLanding`. The verdict belongs to the pair of motion and view.
  2-adic doubling meets `GDiscrete` in the norm view `lmSphN` (`q2_GDiscrete`). Real doubling fails it in
  the absolute-value view `lmRealN` (`real_not_GDiscrete`: `3/2` lies between 1 and 2), and meets it in
  the binary-exponent view (`real_dbl_GDiscrete_expView`). `MachinePhase`, `ordinalSuccMotion` on
  `Ordinal` (universe 0) and every `UpAndOver` meet both. `ordinalTowerMotion` on `Ordinal` (universe 0)
  fails both (`ordinal_tower_not_discrete`: 1 steps to ω, and 2 lies between). No motion on `Unit`
  meets `GDiscrete`.
- So the discrete/continuous contrast is stated at each carrier's own absolute value. In `ℚ_[2]` the
  nonzero norms are exactly the integer powers of 2 (`q2_norm_image`), so no norm lies strictly between
  `‖x‖` and `2‖x‖` (`q2_norm_gap`). In ℝ the nonzero absolute values are every positive real
  (`real_norm_image`), so another lies between any two (`real_norm_dense`).
- Continuous face: `GConnected` and `GJoined`. On `OnePoint ℝ`, ∞ is in 0's connected component
  (`real_GConnected`). On the 2-adic sphere it is not (`q2_not_GConnected`), and no path joins them
  (`q2_not_GJoined`). The path form on `OnePoint ℝ` is not proved here. The component form is.
- Both at once: `givens_two_charts`. Two dipoles, poles disconnected in one carrier and connected in the
  other, and one rational orbit `2ⁿ` that tends to 0 in `ℚ_[2]` and to infinity in ℝ
  (`doubling_place_dichotomy`). The two carriers are not homeomorphic (`no_homeo_sphere_real`), so the
  two doubling motions are never `HomeoIso` (`no_homeoIso_dblQ2_dblReal`). Any strict isomorphism
  between them would send 0 of `ℚ_[2]` to ∞ of `OnePoint ℝ` (`strictIso_zero_to_infty`). A strict `Hom`
  exists, the constant map at ∞ (`const_infty_hom`), so a `Hom` alone carries nothing.

**(c) Breaking away, and returning to zero the long way round.**
- Breaking away: `GLeavesByRun M y`. It holds at `c₀` of `MachinePhase`, at 0 of `Ordinal` (universe 0) and at `false`
  in the slot chart. It fails at 0 of `ℚ_[2]` under doubling (§ V, limit (a)).
- The climb: `GClimbNotLoop`. It holds for `ordinalSuccMotion` (universe 0) and every `UpAndOver`. The control is a
  `Fin 3` motion with always-true OVER, which loops.
- The return: `GReturnToStart M s`. The tail of `s` is a run whose closure contains `s 0`.
  Statement: CARRIER, two charts meet it from 0. The 2-adic arc meets it under 2-adic doubling
  (`q2_arc_returnToStart`), and the sequence `0, 1, 1/2, 1/4, …` meets it under real halving
  (`real_hlv_returnToStart`). So `GReturnToStart` alone does not separate the long way round from a
  plain contraction. Inside its own carrier the 2-adic return is a plain contraction too: 0 of `ℚ_[2]`
  is an attracting fixed point of doubling (`padic_two_poles`, `ZeroParadox/Multihomed/TwoAdicBend.lean`).
  The two return runs differ step by step at each carrier's own absolute value. Each 2-adic doubling
  step from a nonzero point is a cover in the norm order (`q2_double_covBy`). Real halving is not
  `GDiscrete` in the absolute-value view `lmRealN` (`real_hlv_not_GDiscrete`), because 3/4 lies
  between 1/2 and 1. The nonzero 2-adic norms are the integer powers of 2 (`q2_norm_image`: Mathlib's
  `Padic.padicNormE.image` gives one inclusion, `Padic.norm_p_zpow` the other), and the nonzero
  absolute values of ℝ fill (0, ∞)
  (`real_norm_image`), with another between any two (`real_norm_dense`). That is the
  discrete/continuous contrast of (b).
  Reading: INVERSION, the long way round is a two-chart reading: one rational orbit `2ⁿ` tends to 0 in
  `ℚ_[2]` and to infinity in ℝ (`doubling_place_dichotomy`). Under real doubling no sequence from 0 of
  ℝ meets `GReturnToStart` (`real_dbl_no_return_zero`). The ordinal tower from 0 of `Ordinal` (universe 0) does not
  meet `GReturnToStart` (`ordinal_tower_no_return`); the proof: its tail's closure is ε₀
  (`ordinalTowerMotion_stageClosure`), and ε₀ ≠ 0 of `Ordinal` (`epsilon0_ne_zero`).

## AX-B1 as a chart choice

Reading (the Engineer's Take in `ZeroParadox/Givens.lean`): AX-B1 is a chart choice, the discrete chart
being where we evaluate. Which carrier steps off its least element is a theorem, not a commitment. For
every carrier, the step-off mass is 1 when the least element has a first step and the dial is nonzero,
and 0 otherwise (`stepOff_mass`). The discrete chart is a choice of where to evaluate, not an
assumption about the world. Once the carrier is chosen the outcome is fixed: Bool (join or) gives the
switch, NNReal (join max) gives 0 at every dial (`two_charts_snap`). Whether the world steps off in the
discrete chart is a separate question, not settled here: it sits with the dial setting `p` and the
occurrence hypothesis `hocc` of `t_snap_given` (§ VI). Kept separate, on purpose: discreteness ALONG
the run (every doubling step that moves is a cover, one way or the other, in the view order,
`GDiscrete`) is a different notion from a first step AT the least element. The 2-adic chart has
discreteness along the run (`q2_GDiscrete`) and lacks a first step at 0 of `ℚ_[2]`
(`q2_zero_not_firstStep`). The continuous chart stands beside the discrete one and is not denied. The
connectivity of each chart is proved: 0 and ∞ lie in one connected component of `OnePoint ℝ`
(`real_GConnected`), and no path joins them in the 2-adic sphere (`q2_not_GJoined`).
`BotHasFirstStep L` (§ VI) stays a hypothesis of the theorems that use it; `stepOff_mass` says what
follows on each side of it.

## The field lines

In `ℚ_[2]` the field line through a nonzero `x` is `{2 ^ k * x | k : ℤ}`, and its label is
`fieldLineLabel x = x * 2 ^ (-v(x))`, with `v` the 2-adic valuation. A line is a coset of the subgroup
generated by 2 inside the standard decomposition of the multiplicative group, `ℚ_2^× ≅ 2^ℤ × ℤ_2^×`, the
case `p = 2` of `ℚ_p^× ≅ ⟨p⟩ × ℤ_p^×`: A. Jenkins and S. Spallone, arXiv:1011.2451v1, § 3.2, p. 7, "the
basic decomposition Q_p^× ≅ <p> × Z_p^×", also cited in `ZeroParadox/Multihomed/TwoAdicBend.md`. On
ℤ_[2] the label is Mathlib's unit part `PadicInt.unitCoeff` (`PadicInt.unitCoeff_spec`), checked by an
`example` in § III. Relative to Mathlib, which states the unit part on ℤ_[2], the file adds the `ℚ_[2]`
form and the reading of each line as a run between the shared ends 0 and ∞.

Two lines are equal or disjoint (`fieldLine_same_iff`). Each line has a label of norm 1
(`norm_fieldLineLabel`), and a point of norm 1 is its own label (`fieldLineLabel_of_norm_one`), so
distinct units give distinct lines. The lines through 1 and through 3 never meet
(`fieldLines_one_three_disjoint`). Every line has the same two ends: forward it tends to 0 of `ℚ_[2]`,
and backward its norm grows without bound (`fieldLine_two_ends`).

## Given these, then

`given_then_fixed_destination` is the general form. Take a motion whose UP is unchanged along steps, a
point `p` that is the limit sink off `q`, and a run from off `q` with no landing among its stages. Then
the run closes at UP of its start, `p` is in that closure, and the start `s 0` does not arrive at `p`
(`¬ M.Arrives p (s 0)`). It
runs one way. `fixed_destination_two_charts` applies it twice: the 2-adic line from 2 closes at 0 of
`ℚ_[2]`, the real one at ∞ of `OnePoint ℝ`. The destination is fixed, and there is no finite step
count to it: in each chart the start 2 does not arrive at its destination (`¬ Arrives`).

## The limits

- **(a)** 0 of `ℚ_[2]` meets `GMinMax` under doubling (a constant map meets it too, `const_GMinMax`), and
  no run of doubling from 0 of `ℚ_[2]` leaves it at the first step (`q2_not_leavesByRun_zero`). Departure comes from another chart: the
  machine (`machine_leavesByRun`) or the tape (`slot_occurrence_ae`).
- **(b)** Reading: complexity selects the coin. It does not make the step happen. Any `0 < p ≤ 1`
  together with a first step gives firing on almost every run (`snap_ae_of_firstStep`). At `p = 0`
  almost every tape fires nowhere (`never_fires_ae_zero`). Reading: CARRIER, the coin is a real,
  Archimedean, nonzero chance, as the signature of `snap_ae_of_firstStep` takes `p : NNReal` with
  `0 < p`. Repetition does its work in exactly those carriers: an ordered field is Archimedean exactly
  when every crossing probability strictly between 0 and 1 drives survival below every positive bound
  (`archimedean_iff_survival_eventually_lt`), and an infinitesimal crossing probability stays
  infinitesimal at every standard `n`, no standard multiple of it reaching 1
  (`crossing_stays_infinitesimal`; standard `n` only, see `ZeroParadox/Information/Surprisal.md`, the
  Archimedean fence).
- **(c)** The same 0, as a limit: the tower's image starts at 0 of ℤ_[2] and tends to that same 0
  (`snap_arc_z2_loop`); on the sphere the run closure of the arc's tail contains its start, 0 of
  `ℚ_[2]` (`q2_arc_returnToStart`), along a route unique to its line (`fieldLine_same_iff`), by cover
  steps in the norm order (`q2_double_covBy`).

## The magnet, as a Reading

Reading: the core of the magnet has two faces. One is the continuous chart, where 0 and infinity sit in
one connected piece and there is no first step. The other is the coincidence chart, where one point is
read as 0 and as infinity and nothing travels. The outer field lines are the discrete chart. There the
same journey breaks into covers, each doubling one step, and every line ends at the same two poles. None
of this picture is a theorem beyond the declarations named above.
