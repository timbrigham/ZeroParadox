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
- § VII: the cylinder mass `trials_cyl`, the wait `waitENat ∘ det` (`waitENat` and `natCast_le_waitENat_iff` in
  `ZeroParadox/Valuation/DepthIsWait.lean`, `det` in `ZeroParadox/Die.lean`), `wait_bot`, `never_fires_ae_zero`
  (`ZeroParadox/Information/PoleWithinEnsemble.lean`); `trials_zeroBlock` (`ZeroParadox/Information/CrossingTrials.lean`)
  states the same block mass for a window starting at any `N`.
- § VIII: `natDirsOrderIso`, the same `Nat.pair` columns on `End` with its order (`ZeroParadox/Valuation/Interleave.lean`),
  and `natDirs_bot_iff` (`ZeroParadox/Valuation/TowerTape.lean`); the `example` after `unpack_apply` relates the two
  through `tapeIso`.
- § IX: `bot_mem_support_iff`, `trials_support_univ`, `trials_cyl`, `trials_zero_eq_dirac`
  (`ZeroParadox/Information/PoleWithinEnsemble.lean`); `fairTape_singleton_null`
  (`ZeroParadox/Information/BottomTotality.lean`) is the `p = 1/2` case of `trials_support_null`'s second half.
  The complexity rate of `trials p` tapes, which the "maximally complex" `Reading:` gestures at, is
  `brudno_ae_trials` (`ZeroParadox/Information/BrudnoBridge.lean`).
- § X: `xorWith`, `xorHomeo`, `xorWith_involutive` and `homog_cantor` (`ZeroParadox/Valuation/UltrametricView.lean`:
  some involutive homeomorphism of `ℕ → Bool` sends any tape to any other); `xorOffset` is `xorHomeo t` as a
  measurable equivalence. `det_eq_ofNat_iff` (`ZeroParadox/Information/TapeHalting.lean`); `fairTape`
  (`ZeroParadox/Information/Disjunctive.lean`); `trials_fires`, `fires_measurable`
  (`ZeroParadox/Information/CrossingTrials.lean`).

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

- § VII. The number of stages up to and including the first success of independent Bernoulli(`p`) trials has
  the shifted geometric distribution, mean `1/p`; `lintegral_wait_succ` proves that mean (not the
  distribution) by the tail-sum formula, `E[T + 1] = Σ_k P(T ≥ k)` with `T` the wait. Mathlib's
  `ProbabilityTheory.geometricMeasure` is the unshifted (failures) form and sets `geometricMeasure 0` to the
  Dirac mass at 0; a Mathlib lemma evaluating its mean was not located as of 2026-11-26, searched: the
  declaration list of `Mathlib/Probability/Distributions/Geometric.lean` and a regex for geometric
  mean/expectation over the pinned Mathlib, LeanExplore (two phrasings), theoremsearch (three formal
  phrasings: geometric mean, geometric expectation, tail-sum lintegral), GitHub code search with
  `extension:lean` (two phrasings). Neighbours: Mathlib's series identity
  `tsum_coe_mul_geometric_of_norm_lt_one`; outside Mathlib, GitHub code search returned fragments of
  `weighted_geometric_tsum_eq_inv` (facebookresearch/atlas-lean) and `tsum_geometric_trials`
  (paulklemstine/Lean), both stating `Σ (n + 1) p (1 - p)ⁿ = 1/p` in `ℝ` for `0 < p`, existence only, source not
  read. The `p = 0` endpoint, where almost every tape never fires and the mean is ⊤ (`wait_chart_top`), is an
  improper (defective) waiting-time distribution; in survival analysis the mass never failing is the cure
  fraction (Louzada, de Oliveira, Moreira, arXiv:1509.05244, p. 3: "S is an improper survival function"), here
  equal to 1. They credit the cure-rate model to Berkson and Gage (*JASA*, 1952), cited for existence only, not
  retrieved. The chart `x = p⁻¹` is Mathlib's `OrderIso.invENNReal`.
- § VIII. `unpack_measurePreserving` reindexes an infinite product measure, from Mathlib's
  `Measure.infinitePi_map_piCongrLeft` and `Measure.infinitePi_map_curry`. A published measure-level pairing
  statement: Brattka, Gherardi, Hölzl, "Probabilistic computability and choice", *Information and
  Computation* 242 (2015), arXiv:1312.7305, Lemma 4.4(1), pp. 16-17: the pairing `2^ℕ × 2^ℕ → 2^ℕ`,
  `(p, q) ↦ ⟨p, q⟩`, is a computable isomorphism and measure preserving, where measure preserving means
  `μ_X(f⁻¹(A)) = μ_Y(A)` for all closed `A`, with the spaces' canonical measures. Theirs is two columns, the
  canonical measure on `2^ℕ`, and computable; § VIII is countably many columns along `Nat.pair`, Bernoulli(`p`)
  for every `p ≤ 1`, and equality of Borel measures in both directions. At the level of individual random
  sequences the neighbours are van Lambalgen's theorem (Franklin, Porter, arXiv:2004.02851, Theorem 3.6:
  `A ⊕ B` is n-random iff `A` is n-random and `B` is n-random relative to `A`; Shen, Uspensky, Vereshchagin,
  *Kolmogorov Complexity and Algorithmic Randomness*, AMS 2017, Theorem 125, for a product `P × Q`) and the
  countable column decomposition along a pairing function (Porter, arXiv:1503.06332, Theorem 2.10, crediting
  Kautz 1991: each column of a Martin-Löf random `A` is random relative to the others). Those are about the
  uniform or a computable measure and about which sequences are random; § VIII is measure-level only, for
  every `p ≤ 1`, in both directions (`pack_measurePreserving`), and says nothing about individual tapes.
- § IX. `dial_entropy_pos_iff` (binary entropy positive exactly on the open interval) was not located in
  Mathlib as of 2026-11-26, searched: the lemma list of `Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean`
  (`Real.binEntropy_pos` is the backward direction, `Real.binEntropy_eq_zero` the zero set), `exact?` on the
  `NNReal` form and on the `ℝ` form with `0 ≤ p ≤ 1`, LeanExplore (one phrasing). `trials_support_null` is the
  standard fact that for `0 < p < 1` the Bernoulli(`p`) product measure on `{0, 1}^ℕ` has full support and no
  atoms. The reading of the faces against random strings: effective complexity, which Ay, Müller, Szkoła,
  arXiv:0810.5663, p. 1, call "an attempt by M. Gell-Mann and S. Lloyd" to define a complexity measure, whose
  main idea, they write, "is to split the algorithmic information content of some string x into two parts, its
  random features and its regularities" (Gell-Mann, Lloyd, *Complexity*, Vol. 2, 44-52 (1996), as that
  paper's reference list gives it; cited for existence only, not retrieved). The same paper's Theorem 10
  ("Incompressible Strings are Simple"): for some global constant `c`, effective complexity `E_{δ,Δ}(x)` is at
  most `log n + O(log log n)` for every `r`-incompressible string `x` of length `n` (`K(x) ≥ n + K(n) − r`),
  every `δ ≥ 0` and every tolerance `Δ ≥ r + c`. That is finite strings and computable ensembles; § IX
  measures no description length (the rate is `brudno_ae_trials`, above).

## Prior art for § X (searched 2026-11-26)

- Standard names: `ℕ → Bool` under pointwise `xor` is the Cantor group `(ℤ/2ℤ)^ℕ`, a compact abelian group;
  `xorOffset t` is translation by `t`; the fair-coin product measure is its normalized Haar measure, and
  `xorOffset_measurePreserving_fair` is the translation invariance of that measure, proved here coordinatewise
  from Mathlib's `Measure.infinitePi_map_pi` (the image of an infinite product measure under a coordinatewise
  map is the product of the images). Uniqueness of a Haar probability measure on a locally compact group is
  Mathlib's `MeasureTheory.Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure`. It applies here: Mathlib makes
  `Bool` a Boolean ring (`Mathlib/Algebra/Ring/BooleanRing.lean`), whose addition is `xor`, so `ℕ → Bool` is a
  locally compact topological additive group (`Pi.addCommGroup`, `Pi.isTopologicalAddGroup`) and `xorOffset t`
  is addition of `t`. § X does not use it, since that instance lies outside `Dial.lean`'s imports, and states
  the converse within the Bernoulli family, for a single `t`:
  `xorOffset_measurePreserving_iff`, one coordinate where `t` is `true` sends Bernoulli(`p`) to Bernoulli(`1 - p`).
  Mathlib has Haar measure on finite products (`MeasureTheory.Measure.pi.isAddHaarMeasure`) and binary products
  (`MeasureTheory.Measure.prod.instIsAddHaarMeasure`); a statement that the infinite product of uniform measures
  on `ZMod 2` is Haar was not located as of 2026-11-26, searched: LeanExplore (one phrasing), theoremsearch
  (one formal phrasing, which returned `Measure.IsInvInvariant` and finite-product invariance instances). Two
  informal theoremsearch phrasings returned the compact-group Haar theorem (not retrieved, existence only) and
  Sussman, arXiv:2210.02495, Remark at the end of p. 3: the Haar measure on the Cantor group `{−1, +1}^ℕ` makes
  the coordinates independent fair ±1 signs.

## Fences

- "The bottom is the set of all tapes" is the tape-chart `Reading:` (ruling 94). Nothing identifies ⊥ of a
  `ZPSemilattice` with `ℕ → Bool`; `dial_jump_into_L` runs tape → `slotRun` → image under `φ`, forward only.
- "Certain" means probability one. ⊥ of `ℕ → Bool` is in the support of `trials p hp` exactly for `p < 1`
  (`bot_mem_support_iff`) and its singleton has mass 0 exactly for `0 < p`: mass 0 for `0 < p`
  (`trials_bot_null`) and mass 1 at `p = 0` (`trials_zero_eq_dirac`); for `0 < p < 1` every tape has both properties (`trials_support_null`).
- Analog and digital are a `Reading:`; the theorems say continuous (`fireWithin_continuous`) and jump
  (`fireMass_not_continuousAt_zero`).
- The schedule's dichotomy assumes independent stages; `schedule_never_pos` also needs every chance below one.
- The mean in § VII is a value in `ℝ≥0∞`; at `p = 0` it is ⊤ of `ℝ≥0∞`, not a real number. `x = p⁻¹` is a
  chart on `[1, ⊤]`, not an identity of 0 with ∞.
- § VIII proves equality of measures, not randomness of any column; the `End` relation is pointwise, through
  `tapeIso`, and no measure on `End` is stated.
- § IX: "minimally and maximally complex" is a `Reading:`; the theorems say support membership, positive
  binary entropy, mass 1 and mass 0. Positive entropy alone pins `0 < p < 1` and implies ⊥ of `ℕ → Bool` in the
  support, one way: the `p = 0` control meets the support condition and not the entropy one, and no `p` meets
  the entropy condition without the support one. The `p = 1` control meets neither, and shows firing of mass 1
  without positive entropy. Under positive entropy (`0 < p < 1`) no measure-level statement singles out ⊥ of
  `ℕ → Bool` (`dial_pinned_faces`, `trials_support_null`); at `p = 0` the law is the Dirac mass at ⊥ of `ℕ → Bool`
  (`trials_zero_eq_dirac`, the § IX `p = 0` CONTROL); at every `p` the order (`bot_le`), never firing
  (`tape_never_fires_iff`) and wait ⊤ (`wait_bot`) single it out (the § IX `example`).
- § X: "every tape is a local bottom" is a `Reading:` (Tim, 2026-11-26: "that's exactly a baseline and a local
  reference change to it"). Proved: `xorOffset t` exchanges ⊥ of `ℕ → Bool` and `t`, and under the fair coin the
  wait to first disagreement with `t` has the law of the wait from ⊥ (`fair_wait_offset`). The order bottom is
  unique: ⊥ of `ℕ → Bool` is the least tape (`bot_le`), and `xorOffset t` for `t` not ⊥ of `ℕ → Bool` is not an
  order automorphism; it is not even monotone (the `example` after `xorOffset_bot`). For a tape `t` other than
  ⊥ of `ℕ → Bool`, only `p = 1/2` makes `xorOffset t` measure preserving (`xorOffset_measurePreserving_iff`).
  "Needed to exist" in Tim's "The local existance of the zero tape is needed as a hypothetical in order for the
  other options to exist" (Tim, 2026-11-26) is stronger than what is proved, which is that ⊥ of `ℕ → Bool` is the reference the
  wait is computed from: the cylinders of ⊥ of `ℕ → Bool` a tape lies in number wait + 1
  (`tsum_cylinder_bot_indicator`), and their masses `(1 - p)^k` (`trials_cyl` at ⊥) give the mean of wait + 1
  (`lintegral_wait_succ`); § X moves that reference to any `t`.
- EXPERIMENTAL dependence. `Dial.lean` imports modules marked EXPERIMENTAL; the theorems that use a declaration
  of one are listed below. Uses, by section: `tape_never_fires_iff` (`exists_startBit_iff`, StartBit);
  `dial_fire_within`, `fireWithin_continuous`, `fireWithin_mono`, `dial_not_uniform_witness`, `dial_not_uniform`
  (`cylMass_eq`, `cylMass_continuous`, PoleWithinEnsemble); `dial_jump_into_L` (`never_fires_ae_zero`,
  `ae_firesOnce`, PoleWithinEnsemble, and `tape_never_fires_iff`); all of § V (`fadingTrials`, StartBit);
  `law_two_faces` (`tape_totality_two_faces`, in `BottomTotality.lean`, which uses `ZeroParadox/Information/MaxEntropy.lean`). § VII:
  `trials_cyl`, `wait_bot`, `never_fires_ae_zero` (PoleWithinEnsemble), `waitENat` and
  `natCast_le_waitENat_iff` (DepthIsWait). § VIII: the `example` after `unpack_apply` uses `tapeIso`
  (DepthIsWait) and `natDirsOrderIso` (Interleave); `natDirs_bot_iff` (TowerTape) is a pointer only. § IX:
  `bot_mem_support_iff`, `trials_support_univ`, `trials_cyl`, `trials_zero_eq_dirac` (PoleWithinEnsemble),
  `wait_bot` and `waitENat` in the `example` naming what singles out ⊥ of `ℕ → Bool`, and `tape_never_fires_iff`
  in the same `example`. § X: `xorHomeo`,
  `xorWith_involutive` (UltrametricView), `det_eq_ofNat_iff` (TapeHalting), `waitENat` (DepthIsWait),
  `tape_never_fires_iff`. `dial_fire_jump`, `fireMass`, `fireMass_eq`, `fireMass_not_continuousAt_zero`,
  `fireWithin`, `dial_digital_limit`, `unpack`, `unpack_apply`, `unpack_measurePreserving`,
  `pack_measurePreserving` and `dial_entropy_pos_iff` use no declaration of an EXPERIMENTAL module (theirs come from
  `ZeroParadox/Information/CrossingTrials.lean` and Mathlib), though their module imports them.
