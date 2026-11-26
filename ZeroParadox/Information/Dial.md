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
- § VII: the cylinder mass `trials_cyl`, the wait `waitENat ∘ det` and `natCast_le_waitENat_iff`
  (`ZeroParadox/Valuation/DepthIsWait.lean`), `wait_bot`, `never_fires_ae_zero`
  (`ZeroParadox/Information/PoleWithinEnsemble.lean`); `trials_zeroBlock` (`ZeroParadox/Information/CrossingTrials.lean`)
  states the same block mass for a window starting at any `N`.
- § VIII: `natDirsOrderIso`, the same `Nat.pair` columns on `End` with its order (`ZeroParadox/Valuation/Interleave.lean`),
  and `natDirs_bot_iff` (`ZeroParadox/Valuation/TowerTape.lean`); the `example` after `unpack_apply` relates the two
  through `tapeIso`.
- § IX: `bot_mem_support_iff`, `trials_bot_null` (`ZeroParadox/Information/PoleWithinEnsemble.lean`).

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
  `∏ (1 - q n) ≠ 0` in a ring `R` with `[NormedCommRing R] [NormOneClass R] [CompleteSpace R]
  [NormMulClass R]`, when every `1 - q n ≠ 0` and `∑ ‖q n‖` converges); see also
  `multipliable_one_sub_of_summable` and `Real.multipliable_of_summable_log`. The measure-theoretic statement
  was not located as of 2026-11-25 (lean-explore, two phrasings; theoremsearch, one phrasing).
- The volume tending to the switch: a uniform limit of continuous functions is continuous (Mathlib
  `TendstoUniformly.continuous`), so the jump of `fireMass` forces non-uniform convergence on `[0, 1]`.
  Conversely, two results give uniform convergence when the limit is continuous. Dini's theorem, Mathlib
  `Monotone.tendstoUniformlyOn_of_forall_tendsto` (`Mathlib/Topology/UniformSpace/Dini.lean`): functions
  continuous on a compact set, increasing in the index, converging pointwise there to a function continuous
  there, converge uniformly there. `fireWithin n p` increases with `n`, since the event "some stage below `n`
  fires" grows with `n` (the monotonicity `dial_digital_limit`'s proof uses). Bogoya, Böttcher, Maximenko,
  arXiv:1509.01836, Proposition 3.2, with monotonicity in the variable instead: if `g` is continuous on
  `[0, 1]` and functions `f n : [0, 1] → ℝ`, each increasing (non-strict), converge to `g` at every point of
  `[0, 1]`, the convergence is uniform on `[0, 1]`. Each `fireWithin n` is monotone in `p`
  (`fireWithin_mono`). So on the segment `[0, 1]` uniform convergence and a continuous limit go together, and
  the jump at 0 is what blocks it. `dial_not_uniform` proves more, on
  `(0, 1]`, by an explicit witness (`dial_not_uniform_witness`): there the limit is constantly 1 and
  continuous and the convergence is still not uniform, which the proposition does not forbid, since `(0, 1]`
  is not compact; non-uniformity on `(0, 1]` gives it on `[0, 1]`.

## Prior art for § VII-IX (searched 2026-11-26)

- § VII. The number of stages up to and including the first success of independent Bernoulli(`p`) trials is
  the shifted geometric distribution, mean `1/p`; `lintegral_wait_succ` proves it by the tail-sum formula,
  `E[N + 1] = Σ_k P(N ≥ k)`. Mathlib's `ProbabilityTheory.geometricMeasure` is the unshifted (failures) form
  and sets `geometricMeasure 0` to the Dirac mass at 0; a Mathlib lemma evaluating its mean was not located as
  of 2026-11-26, searched: the declaration list of `Mathlib/Probability/Distributions/Geometric.lean`,
  LeanExplore (one phrasing), theoremsearch (one formal phrasing). The `p = 0` endpoint, wait ⊤ almost surely
  and mean ⊤ (`wait_chart_top`), is an improper (defective) waiting-time distribution; in survival analysis
  the mass never failing is the cure fraction (Louzada, de Oliveira, Moreira, arXiv:1509.05244, p. 3: "S is an
  improper survival function"), here equal to 1. The chart `x = p⁻¹` is Mathlib's `OrderIso.invENNReal`.
- § VIII. `unpack_measurePreserving` reindexes an infinite product measure, from Mathlib's
  `Measure.infinitePi_map_piCongrLeft` and `Measure.infinitePi_map_curry`. At the level of individual random
  sequences the neighbours are van Lambalgen's theorem (Franklin, Porter, arXiv:2004.02851, Theorem 3.6:
  `A ⊕ B` is n-random iff `A` is n-random and `B` is n-random relative to `A`; Shen, Uspensky, Vereshchagin,
  *Kolmogorov Complexity and Algorithmic Randomness*, AMS 2017, Theorem 125, for a product `P × Q`) and the
  countable column decomposition along a pairing function (Porter, arXiv:1503.06332, Theorem 2.10, crediting
  Kautz 1991: each column of a Martin-Löf random `A` is random relative to the others). Those are about the
  uniform or a computable measure and about which sequences are random; § VIII is measure-level only, for
  every `p ≤ 1`, in both directions (`pack_measurePreserving`), and says nothing about individual tapes.
- § IX. The two faces as a reading of random strings: effective complexity, which Ay, Müller, Szkoła,
  arXiv:0810.5663, p. 1, describe as Gell-Mann and Lloyd's attempt "to split the algorithmic information
  content of some string x into two parts, its random features and its regularities" (Gell-Mann, Lloyd,
  *Complexity* 2(1), 1996, cited for existence only, not retrieved). The same paper's Theorem 10
  ("Incompressible Strings are Simple"): incompressible strings of length `n` have effective complexity at most
  `log n + O(log log n)`. That is finite strings and computable ensembles; § IX measures no description length.

## Fences

- "The bottom is the set of all tapes" is the tape-chart `Reading:` (ruling 94). Nothing identifies ⊥ of a
  `ZPSemilattice` with `ℕ → Bool`; `dial_jump_into_L` runs tape → `slotRun` → image under `φ`, forward only.
- "Certain" means probability one. ⊥ of `ℕ → Bool` is a member at every `p`, of mass 0 for `0 < p`.
- Analog and digital are a `Reading:`; the theorems say continuous (`fireWithin_continuous`) and jump
  (`fireMass_not_continuousAt_zero`).
- The schedule's dichotomy assumes independent stages; `schedule_never_pos` also needs every chance below one.
- The mean in § VII is a value in `ℝ≥0∞`; at `p = 0` it is ⊤ of `ℝ≥0∞`, not a real number. `x = p⁻¹` is a
  chart on `[1, ⊤]`, not an identity of 0 with ∞.
- § VIII proves equality of measures, not randomness of any column; the `End` relation is pointwise, through
  `tapeIso`, and no measure on `End` is stated.
- § IX: "minimally and maximally complex" is a `Reading:`; the theorems say support membership, positive
  binary entropy, mass 1 and mass 0. The `p = 0` and `p = 1` controls each meet one face and not the other.
- EXPERIMENTAL dependence. `Dial.lean` imports `ZeroParadox/Information/StartBit.lean` (EXPERIMENTAL) and
  reaches `ZeroParadox/Information/PoleWithinEnsemble.lean` (EXPERIMENTAL) through
  `ZeroParadox/Information/BottomTotality.lean`, which also imports `ZeroParadox/Information/MaxEntropy.lean`
  (EXPERIMENTAL). Theorems using a declaration of those modules: `tape_never_fires_iff`
  (`exists_startBit_iff`); `dial_fire_within`, `fireWithin_continuous`, `fireWithin_mono`,
  `dial_not_uniform_witness`, `dial_not_uniform` (`cylMass_eq`, `cylMass_continuous`); `dial_jump_into_L`
  (`never_fires_ae_zero`, `ae_firesOnce`, `tape_never_fires_iff`); all of § V (`fadingTrials`); `law_two_faces`
  (`tape_totality_two_faces`, in `BottomTotality.lean`). `dial_fire_jump`, `fireMass`, `fireMass_eq`,
  `fireMass_not_continuousAt_zero`, `fireWithin` and `dial_digital_limit` use no declaration of those three
  modules (theirs come from `ZeroParadox/Information/CrossingTrials.lean` and Mathlib), though their module
  imports them. § VII uses `trials_cyl`, `wait_bot`, `never_fires_ae_zero` (`PoleWithinEnsemble.lean`) and
  `natCast_le_waitENat_iff` (`ZeroParadox/Valuation/DepthIsWait.lean`, EXPERIMENTAL); § IX uses
  `bot_mem_support_iff` and `trials_bot_null` (`PoleWithinEnsemble.lean`). `unpack`, `unpack_apply`,
  `unpack_measurePreserving` and `pack_measurePreserving` use none of those modules' declarations.
