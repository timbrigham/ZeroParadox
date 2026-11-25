# The givens at the die level: what each one is, and the theorem that carries it

Ride-along for `ZeroParadox/Givens.lean`. Each given is a `Prop` on a die `Motion` (`ZeroParadox/Die.lean`),
never a field of a class, so each one can be true of one chart and false of another. The file proves or
refutes each given chart by chart. The charts are four limit motions: doubling and halving on the 2-adic
sphere `OnePoint ℚ_[2]`, and doubling and halving on the real projective line `OnePoint ℝ`. Two more
motions are used, `machineJoinMotion` on `MachinePhase` and `ordinalSuccMotion` on `Ordinal`.

## The givens

Tim named three. Each one splits into the predicates below.

**(a) Minimally and maximally complex at once.**
- `GMinMax M p q`: `p` steps only to itself, and `p` is the limit sink of every point other than `q`.
  It holds at 0 of `ℚ_[2]` under doubling (`q2_GMinMax`). It holds at ∞ of `OnePoint ℝ` under real
  doubling (`real_GMinMax_infty`), and fails there at 0 of ℝ (`real_not_GMinMax_zero`). It fails at
  `c₀`, ⊥ of `MachinePhase`, and at every ordinal under `Order.succ` (`ordinal_no_selfOnly`).
  Controls: the identity on `Unit`, and the constant map at 0 (`const_GMinMax`). Both meet it, so
  `GMinMax` alone says little. The constant map has no limit motion as its dipole partner
  (`const_no_limit_partner`).
- `GCoincidence`: a strict map of motions sends a point that is least at the source to a point that is
  greatest at the target, and sends nothing else there. It holds for `q2Val` from doubling on ℤ_[2] to
  `+1` on `ℕ∞`, at ℤ_[2]'s 0 (`z2_GCoincidence`). It fails on every field of characteristic 0, ℝ and
  `ℚ_[2]` included (`field_no_GCoincidence`), because halving is available there.
- Reading: COINCIDENCE, in the tape chart. The tape-chart reading of (a) is the fair-coin ensemble:
  `tape_totality_two_faces` and `maxEntropy_mlRandom_and_snap_ae`. It sits beside the die-level face,
  and it is not a hypothesis of the snap.

**(b) The run from 0 to infinity is discrete and continuous at once.**
- Discrete face: `GDiscrete M P`, where every moving step is a cover in the view `P`, and
  `GCoverAtLanding`. 2-adic doubling meets `GDiscrete` (`q2_GDiscrete`). Real doubling fails it
  (`real_not_GDiscrete`: `3/2` lies between 1 and 2). `MachinePhase`, the ordinals and every
  `UpAndOver` meet both. No motion on `Unit` meets `GDiscrete`.
- Continuous face: `GConnected` and `GJoined`. On `OnePoint ℝ`, ∞ is in 0's connected component
  (`real_GConnected`). On the 2-adic sphere it is not (`q2_not_GConnected`), and no path joins them
  (`q2_not_GJoined`). The path form on `OnePoint ℝ` is not proved here. The component form is.
- Both at once: `givens_two_charts`. Two dipoles, poles disconnected in one carrier and connected in the
  other, and one rational orbit `2ⁿ` that tends to 0 in `ℚ_[2]` and to infinity in ℝ
  (`doubling_place_dichotomy`). The two carriers are not homeomorphic (`no_homeoIso_dblQ2_dblReal`).
  Any strict isomorphism between the two doubling motions would send 0 of `ℚ_[2]` to ∞ of `OnePoint ℝ`
  (`strictIso_zero_to_infty`). A strict `Hom` exists, the constant map at ∞ (`const_infty_hom`), so a
  `Hom` alone carries nothing.

**(c) Breaking away, and returning to zero the long way round.**
- Breaking away: `GLeavesByRun M y`. It holds at `c₀` of `MachinePhase`, at 0 of `Ordinal` and at `false`
  in the slot chart. It fails at 0 of `ℚ_[2]` under doubling (§ V, limit (a)).
- The climb: `GClimbNotLoop`. It holds for `ordinalSuccMotion` and every `UpAndOver`. The control is a
  `Fin 3` motion with always-true OVER, which loops.
- The return: `GReturnToStart M s`. The tail of `s` is a run whose closure contains `s 0`. The 2-adic arc
  meets it (`q2_arc_returnToStart`). The real chart has no such return to 0 of ℝ
  (`real_dbl_no_return_zero`). The ordinal tower from 0 closes at ε₀, never back at 0 of `Ordinal`
  (`ordinal_tower_no_return`).

## AX-B1 has two faces

AX-B1 is a chart choice: the discrete chart is where we evaluate. It is also the framework's one
substantive commitment: the discrete chart is where the step happens. The continuous chart stands
beside it and is not denied. In Lean, both charts are theorems (`real_GConnected`, `q2_not_GJoined`).
The commitment is the hypothesis `BotHasFirstStep L` (§ VI).

## The field lines

In `ℚ_[2]` the field line through a nonzero `x` is `{2 ^ k * x | k : ℤ}`. Two lines are equal or
disjoint (`fieldLine_same_iff`). Each line has a label of norm 1 (`norm_fieldLineLabel`), and a point of
norm 1 is its own label (`fieldLineLabel_of_norm_one`), so distinct units give distinct lines. The lines
through 1 and through 3 never meet (`fieldLines_one_three_disjoint`). Every line has the same two ends:
forward it tends to 0, and backward its norm grows without bound (`fieldLine_two_ends`).

## Given these, then

`given_then_fixed_destination` is the general form. Take a motion whose UP is unchanged along steps, a
point `p` that is the limit sink off `q`, and a run from off `q` with no landing among its stages. Then
the run closes at UP of its start, `p` is in that closure, and the run never arrives at `p` by steps. It
runs one way. `fixed_destination_two_charts` applies it twice: the 2-adic line from 2 closes at 0, the
real one at ∞. The destination is fixed. The step count is not, because the climb never arrives.

## The limits

- **(a)** 0 of `ℚ_[2]` is minimal and maximal at once under doubling, and it never leaves under that
  motion (`q2_not_leavesByRun_zero`). Departure comes from another chart: the machine
  (`machine_leavesByRun`) or the tape (`slot_occurrence_ae`).
- **(b)** Complexity selects the coin. It does not make the step happen. Any `0 < p ≤ 1` together with a
  first step gives firing on almost every run (`snap_ae_of_firstStep`). At `p = 0` nothing fires
  (`never_fires_ae_zero`). The coin is a real, Archimedean, nonzero chance: an ordered field is
  Archimedean exactly when every crossing probability strictly between 0 and 1 drives survival below
  every positive bound (`archimedean_iff_survival_eventually_lt`), and an infinitesimal crossing
  probability accumulates to nothing at any standard `n` (`crossing_stays_infinitesimal`; standard `n`
  only, see `ZeroParadox/Information/Surprisal.md`, the Archimedean fence).
- **(c)** The return is to the same 0 (`snap_arc_z2_loop`, `q2_arc_returnToStart`), along a route unique
  to its line (`fieldLine_same_iff`).

## The magnet, as a Reading

Reading: the core of the magnet has two faces. One is the continuous chart, where 0 and infinity sit in
one connected piece and there is no first step. The other is the coincidence chart, where one point is
read as 0 and as infinity and nothing travels. The outer field lines are the discrete chart. There the
same journey breaks into covers, each doubling one step, and every line ends at the same two poles. None
of this picture is a theorem beyond the declarations named above.
