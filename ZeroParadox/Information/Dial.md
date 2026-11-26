# The dial: prior art, pointers and fences

Ride-along for `ZeroParadox/Information/Dial.lean`. The Lean file holds the declarations and the glosses;
this file holds what was already in the corpus, the prior art, and the fences.

## Already in the corpus (pointed to, not restated)

- The vacuum's own jump: `trials_zero_eq_dirac`, `trials_bot_mass_jump`, `botMass_not_continuousAt_zero`,
  `cylMass_eq`, `cylMass_continuous`, `botMass_eq_iInf` (`ZeroParadox/Information/PoleWithinEnsemble.lean` § VI).
  `fireWithin` is one minus `cylMass` (`dial_fire_within`).
- A tape fires iff it is not ⊥ of `ℕ → Bool`: `exists_startBit_iff` (`ZeroParadox/Information/StartBit.lean`);
  `tape_never_fires_iff` is its negated form.
- Stage-varying chances: `fadingTrials`, `fadingTrials_fires`, `returning_two_charts` (StartBit § III).
- The image run on `firedRun`: `snap_ae_fixed_phi`, `never_fires_ae_zero`, `ae_firesOnce`
  (`ZeroParadox/Information/PoleWithinEnsemble.lean`); `t_snap_of_fires_once`, `slotRun_crosses_iff`
  (`ZeroParadox/Information/CrossingTrials.lean`).
- The law's minimal face: `tape_totality_two_faces` (`ZeroParadox/Information/BottomTotality.lean`).

## Prior art (searched 2026-11-25)

- Second Borel-Cantelli lemma, Mathlib `ProbabilityTheory.measure_limsup_eq_one` (independent events, divergent
  sum, limsup has measure one); used by `schedule_fires_of_tsum_top`. First lemma, Mathlib
  `MeasureTheory.measure_limsup_atTop_eq_zero` (not `measure_limsup_eq_zero`), used by StartBit's
  `fadingTrials_eventuallyFalse`. Both lemmas in prose: Koukoulopoulos, arXiv:2109.11003, Theorem 2.4
  (a theoremsearch hit, statement only; the paper was not retrieved).
- `schedule_never_pos` is the convergent half of the standard fact that, for independent events with
  probabilities below one, none occurs with positive probability iff the sum converges. Its proof here is a
  tail bound (a block of `N` silent stages, then a union bound on the rest), not an infinite product. Mathlib
  has infinite products (`Real.multipliable_of_summable_log`); a statement in this form was not located as of
  2026-11-25 (lean-explore, one phrasing; theoremsearch, one phrasing).
- The volume tending to the switch: a uniform limit of continuous functions is continuous (Mathlib
  `TendstoUniformly.continuous`), so the jump of `fireMass` forces non-uniform convergence on `[0, 1]`. Each
  `fireWithin n` is monotone in `p`; a monotone sequence converging pointwise to a CONTINUOUS limit converges
  uniformly (Bogoya, Böttcher, Maximenko, arXiv:1509.01836, Proposition 3.2; a theoremsearch hit, statement
  only, not retrieved), so here the non-uniformity and
  the discontinuity are the same fact read from two sides. `dial_not_uniform` proves it on `(0, 1]`, where the
  limit is continuous, by an explicit witness (`dial_not_uniform_witness`).

## Fences

- "The bottom is the set of all tapes" is the tape-chart `Reading:` (ruling 94). Nothing identifies ⊥ of a
  `ZPSemilattice` with `ℕ → Bool`; `dial_jump_into_L` runs tape → `slotRun` → image under `φ`, forward only.
- "Certain" means probability one. ⊥ of `ℕ → Bool` is a member at every `p`, of mass 0 for `0 < p`.
- Analog and digital are a `Reading:`; the theorems say continuous (`fireWithin_continuous`) and jump
  (`fireMass_not_continuousAt_zero`).
- The schedule's dichotomy assumes independent stages; `schedule_never_pos` also needs every chance below one.
