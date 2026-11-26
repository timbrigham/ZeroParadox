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
  `fadingTrials_eventuallyFalse`. Both lemmas in prose, a secondary source: Koukoulopoulos, arXiv:2109.11003,
  Theorem 2.4 (a survey on metric Diophantine approximation; (b) assumes the events mutually independent).
- `schedule_never_pos` is the convergent half of the standard fact that, for independent events with
  probabilities below one, none occurs with positive probability iff the sum converges. Its proof here is a
  tail bound (a block of `N` silent stages, then a union bound on the rest), not an infinite product. The
  analytic core of that half in product form is Mathlib `tprod_one_add_ne_zero_of_summable` (with `f = -q`,
  `∏ (1 - q n) ≠ 0` in a complete normed ring when every `1 - q n ≠ 0` and `∑ ‖q n‖` converges); see also
  `multipliable_one_sub_of_summable` and `Real.multipliable_of_summable_log`. The measure-theoretic statement
  was not located as of 2026-11-25 (lean-explore, two phrasings; theoremsearch, one phrasing).
- The volume tending to the switch: a uniform limit of continuous functions is continuous (Mathlib
  `TendstoUniformly.continuous`), so the jump of `fireMass` forces non-uniform convergence on `[0, 1]`.
  Conversely, Pólya's theorem (Dini's second theorem), in the form of Bogoya, Böttcher, Maximenko,
  arXiv:1509.01836, Proposition 3.2: if `g` is continuous on `[0, 1]` and functions `f n : [0, 1] → ℝ`, each
  increasing (non-strict), converge to `g` at every point of `[0, 1]`, the convergence is uniform on `[0, 1]`.
  Each `fireWithin n` is monotone in `p` (`fireWithin_mono`), so on the segment `[0, 1]` uniform convergence
  and a continuous limit go together, and the jump at 0 is what blocks it. `dial_not_uniform` proves more, on
  `(0, 1]`, by an explicit witness (`dial_not_uniform_witness`): there the limit is constantly 1 and
  continuous and the convergence is still not uniform, which the proposition does not forbid, since `(0, 1]`
  is not compact; non-uniformity on `(0, 1]` gives it on `[0, 1]`.

## Fences

- "The bottom is the set of all tapes" is the tape-chart `Reading:` (ruling 94). Nothing identifies ⊥ of a
  `ZPSemilattice` with `ℕ → Bool`; `dial_jump_into_L` runs tape → `slotRun` → image under `φ`, forward only.
- "Certain" means probability one. ⊥ of `ℕ → Bool` is a member at every `p`, of mass 0 for `0 < p`.
- Analog and digital are a `Reading:`; the theorems say continuous (`fireWithin_continuous`) and jump
  (`fireMass_not_continuousAt_zero`).
- The schedule's dichotomy assumes independent stages; `schedule_never_pos` also needs every chance below one.
- `Dial.lean` imports two EXPERIMENTAL modules, `ZeroParadox/Information/PoleWithinEnsemble.lean` and
  `ZeroParadox/Information/StartBit.lean`; `tape_never_fires_iff` and `dial_jump_into_L` rest on them.
