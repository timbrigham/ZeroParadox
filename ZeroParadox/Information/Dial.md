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
- § XI: `slotMotion` (`ZeroParadox/Information/CrossingTrials.lean`) is reused as the die `slotKernel` is
  subordinate to; `Motion`, `NoStepAt`, `SelfOnlyAt`, `LeavesAt`, `ofFun` (`ZeroParadox/Die.lean`).
  `trials_det_eq_geometric` (`ZeroParadox/Information/PoleWithinEnsemble.lean`) is the first-hit law of
  `trials p hp` as Mathlib's `geometricMeasure`, for `p ≠ 0`; `runLaw_stay` is the same geometric holding read
  off the chain. `InvariantMarkovKernel` (`ZeroParadox/Valuation/BottomInvariant.lean`) bundles a Markov kernel
  with an invariant law; § XI uses no invariant law. The other chart of `ofFun_kernel_dirac`: `odMarkov`
  (`ZeroParadox/Multihomed/OrbitDie.lean` § III) runs the Markov step at `a = 1/4` as a deterministic
  `Motion.ofFun` die on vectors `Fin 2 → ℝ` (distributions among them), and `odometerIMK`, `attractorIMK` (`ZeroParadox/Valuation/BottomInvariant.lean`)
  are `Kernel.deterministic` instances of `InvariantMarkovKernel`. The two observers of the `Reading:` at § XI's header:
  value side `loop_is_a_trap`, `stutter_obs_const`, `carry_steps_onward_forever_yet_shows_nothing`
  (`ZeroParadox/Computability/Occurrence.lean`), `da1_minimal_path` (`ZeroParadox/Order/Snap.lean`),
  `Motion.quot_leavesAt_iff`, `Motion.selectedTotal_of_option` (`ZeroParadox/Die.lean`); move side
  `not_halted_is_stepping_head` (`ZeroParadox/Computability/GroundZero.lean`), `dead_yields_live_withholds`
  (`ZeroParadox/Computability/Occurrence.lean`), `Motion.LaxHom.noStepAt_iff` (`ZeroParadox/Die.lean`).
- § XII: the unweighted counterparts are `Motion.StepCompat`, `Motion.quot`, `Motion.quot_step_mk_iff`,
  `Motion.quot_leavesAt_iff`, `Motion.UpStepInvariant` (`ZeroParadox/Die.lean`); `subordinate_quot_of_lumps`
  and `quot_leavesAt_of_ae` connect `Lumps` to them. The relational reversal shape
  `step a b ↔ step (σ b) (σ a)` for an involution `σ`, used by `absorb4_not_sigma_reversible`, is
  `Motion.bijOn_sources_sinks` and `Motion.not_exists_involution_reverses_lt` (`ZeroParadox/Die.lean` § X).
  A real-valued detailed-balance predicate on `Fin n → PMF (Fin n)` is `Reversible`
  (`ZeroParadox/State/ReversibleSpectrum.lean`); § XII uses Mathlib's `Kernel.IsReversible` on a general
  measurable carrier, and `DetailedBalance` only for the finite-matrix statements.

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
- § VII, the unshifted mean (searched 2026-11-27). `lintegral_wait` proves the mean of the wait (failures
  before the first success) is `p⁻¹ - 1`, which is `(1 - p)/p` for `0 < p`: the textbook mean of the
  failures form of the geometric distribution (Wikipedia, "Geometric distribution", retrieved 2026-11-27:
  `E(Y) = (1 - p)/p` for `Y = X - 1`, `0 < p ≤ 1`; ProofWiki, "Expectation of Geometric
  Distribution/Formulation 2", retrieved 2026-11-27: pmf `p(1 - p)^k`, `E X = (1 - p)/p`). Outside Mathlib the mean
  is stated in ℝ by TauCetiProject/TauCeti at commit b12bdfa, `integral_id_map_cast_geometricMeasure`
  (`∫ x, x ∂((geometricMeasure p).map Nat.cast) = (1 - p) / p` for every `p : unitInterval`), which gives 0
  at `p = 0` (`integral_id_map_cast_geometricMeasure_zero`, Mathlib's `geometricMeasure 0 = dirac 0`), and
  by danlyng/Econlib at commit d7bd947, `CountDist.geometric_expect`, for `0 < p ≤ 1`; both read at those
  commits, types not elaborated. Our `lintegral_wait` gives ⊤ of `ℝ≥0∞` at `p = 0`, and that is the mean
  itself: at `p = 0` almost every tape never fires (`never_fires_ae_zero`), so almost every tape is ⊥ of `ℕ → Bool`
  (`tape_never_fires_iff`; the `p = 0` facts together: `wait_chart_top`), whose wait is ⊤ of `ℕ∞` (`wait_bot`), and the wait is infinite almost surely. The convention `0⁻¹ = ⊤`
  in `ℝ≥0∞` makes the closed form `p⁻¹ - 1` agree. TauCeti gives 0 there and Econlib excludes `p = 0`.
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

## Prior art for § XI (searched 2026-11-26)

- Standard names. A Markov kernel `K` with `Subordinate M K` is a Markov chain whose directed graph lies in
  the step relation: Levin, Peres, Wilmer, *Markov Chains and Mixing Times*, 2nd ed., Remark 1.24, p. 15,
  "the directed graph with vertex set equal to the state space of the chain, that includes the directed edge
  (x, y) in its edge set iff P(x, y) > 0". Under a subordinate kernel, a point stepping to itself only is an absorbing state
  (`leave_zero_of_selfOnlyAt`; p. 15:
  "the chain never leaves x once it first visits x; such states are called absorbing"); a chain that may stay
  put has positive holding probability, of which LPW's lazy version `Q = (I + P)/2` is one instance (p. 8, "We
  call Q a lazy version of P"). `slotKernel` is their Example 1.1 (p. 3, the frog,
  east coin `p`) with the west pad made absorbing.
- The chain law. `runLaw` is Mathlib's `Kernel.trajMeasure` (the Ionescu-Tulcea theorem,
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`) of `dirac x₀` and the time-homogeneous `homK K`; a
  time-homogeneous wrapper in the pinned Mathlib was not located as of 2026-11-26, searched: case-insensitive
  grep of `Mathlib/Probability` for `markovChain`, `Markov chain`, `homogeneous` and `trajMeasure` (hits only
  `trajMeasure` in `Kernel/IonescuTulcea/Traj.lean` and docstrings of `Kernel/Irreducible.lean`). The same
  construction is `markovChainLaw` in TauCeti (repository TauCetiProject/TauCeti, commit 656ded17,
  `TauCeti/Probability/Process/MarkovChain.lean`), and `absorbingChain p : Kernel Bool Bool` there
  (`TauCeti/Probability/MarkovChain/Examples/Absorbing.lean`, `p : unitInterval` the stay weight at `false`) is
  `slotKernel (1 - p)`, whose `p` is the leave weight (`slotKernel_leave`).
  PARTLY VERIFIED: statements fetched, not elaborated, outside this repository's dependency closure. § XI's
  own part is the die side: `Subordinate`, its controls, and the identity of the stay record with `trials p`.
- Exact weights. `ae_leaves_iff` depends only on whether the leave-weight is positive; the law itself
  depends on the exact weight. For product measures that is Kakutani's dichotomy: van Erven, Harremoës,
  arXiv:1206.2459, Theorem 29, p. 16 (equivalence or mutual singularity of infinite products; with
  `α = 1/2` equivalent to Kakutani, *Ann. of Math.* 49 (1948)); Dutkay, Jorgensen, arXiv:math/0501077,
  Corollary 5.17, p. 21: on `{1, ..., N}^ℕ` the product measures `μ_p`, `μ_p'` are mutually singular for
  `p ≠ p'`, credited to Kakutani 1948 (not retrieved). Cited, not formalized here.
- Maximum entropy (`leave_half_of_maxEntropy`): Jaynes, *Phys. Rev.* 106 (1957) 620; abstract only
  retrieved, cited for existence.

## Prior art for § XII (searched 2026-11-27)

- Lumping. The lumped chain is Levin, Peres, Wilmer, *Markov Chains and Mixing Times*, 2nd ed., Lemma 2.5,
  p. 25, under the per-class condition (2.10), which is `FiberConst`; Wolfer and Watanabe, arXiv:2203.04575,
  Theorem 3.1, p. 12, attribute that characterisation to Kemeny and Snell (not retrieved, not cited as read
  here). `Lumps.fiberConst` is its one-way relation to `Lumps`. That intertwining gives the observed
  process the lumped chain's law from every initial probability law (`chainLaw_map_of_lumps`; from every
  point start, the forward direction of `lumps_iff_runLaw_map`) is Dynkin's criterion as Rogers and Pitman
  (1981), Remark (iii), p. 575, state it; Burke and Rosenblatt (1958), Corollary 1, p. 1113, give the
  per-class condition as sufficient for every initial distribution with all weights positive (`w_i > 0`,
  foot of p. 1112) and "not generally necessary". The converse half of `lumps_iff_runLaw_map` (the
  `L`-chain's law from every point start forces the intertwining) is, for irreducible finite chains, Wolfer
  and Watanabe, Theorem 3.1, p. 12 (their `W(Y, E)` is the irreducible stochastic matrices, p. 9, and
  lumpability there is strong lumpability, "independent of the starting distribution", footnote 8, p. 12),
  which they attribute to Kemeny and Snell, Theorem 6.3.2 (not retrieved). The version here (a supplied `L`, point starts, a general measurable
  carrier) follows UEOT's `pathLaw_implies_strongLumpability` (below) and reads off the time-1 marginal
  (`runLaw_time_one`).
- Reversibility. Detailed balance and reversibility of a stationary process: Kelly, *Reversibility and
  Stochastic Networks* (1979), § 1.2, Lemma 1.1 and Theorem 1.2. That lumping preserves reversibility
  (`isReversible_map_of_lumps`) is Wolfer and Watanabe, Proposition 4.2, p. 26, for irreducible finite
  chains; they attribute it to Kemeny and Snell. § XII states it with Mathlib's `Kernel.IsReversible` on a
  general measurable carrier. For every partition, not only a lumping one, the `π`-weighted coarse-grained
  chain of an irreducible reversible chain is reversible: Eldar, Ozols, Thompson, "The Need for Structure
  in Quantum LDPC Codes", *IEEE Trans. Inf. Theory* 66(3) (2020), arXiv:1610.07478, Definition 23, p. 11,
  and Fact 27, p. 12; `aggregatedChain_detailedBalance` is that statement for matrices over ℚ with nonzero
  class weights. That a non-reversible chain can lump to a reversible one (`a4_direction_erased`, w.r.t. the
  counting measure on `Bool`; w.r.t. a probability measure, `boolSwap_reversible_half`) is noted
  by Wolfer and Watanabe, § 4.4.3, p. 26: embedding a reversible chain, "even by a Markov embedding", can
  yield a non-reversible one, and a Markov embedding serves "as a right inverse of the lumping operation"
  (§ 2.1, p. 5), so that chain lumps back to the reversible one. paulklemstine/Lean `cycleLumpable` (below) lumps the `n`-cycle onto the
  `m`-cycle for `m ∣ n`, which at `n = 4`, `m = 2` is the lumping half of `a4_direction_erased`.
- Lumping without a Markov observer. For a stationary reversible chain with positive weights, the observed
  process is Markov iff the per-class condition holds: Burke and Rosenblatt, Theorem 1, p. 1112.
  `lazyPairs` with `unifFin4` is such a chain and fails the condition (`lazyPairs_not_lumpable`), so
  `lazyPairs_coarse_not_markov` is an instance of their Theorem 1, refuted explicitly at three times.
  Coarse-graining and entropy production: Esposito, arXiv:1112.5410, cited for the topic only.
- Lean neighbours, PARTLY VERIFIED (source read, type not elaborated, outside this dependency closure).
  Erotemic/shufflemath `Shufflemath.ReversibleQuotient.reversible_quotient`: the same intertwining
  hypothesis plus matrix detailed balance, on finite carriers with rational masses; the delta here is
  `Kernel.IsReversible` on a general measurable carrier. MurphyHoops UEOT `StrongLumpability` and
  `strongLumpability_iff_pathLaw` (all probability initial laws), the path-law characterisation closest to
  `lumps_iff_runLaw_map`. paulklemstine/Lean `Catalog/Probability/MarkovLumpability.lean` (`Lumpable`, a
  bounded morphism of support frames, `cycleLumpable`; no reversibility result). TauCeti `markovChainLaw`,
  the construction behind `chainLaw` (already cited under § XI). or4nge19/MCMC (commit a7a5ccab):
  `isReversible_iff_kernel_reversible` (`MCMC/Finite/toKernel.lean`), matrix detailed balance iff Mathlib
  `Kernel.IsReversible` on a finite carrier; `eq_trajMeasure_iff`, `trajMeasure_map_eval` and
  `trajMeasure_map_eval_eval_add` (`MCMC/ToMathlib/Probability/Kernel/IonescuTulcea/Traj.lean`), the
  characterisation of `Kernel.trajMeasure` by its initial law and one-step joint laws, and the one- and
  two-time laws of the chain of a single kernel.
- Credit, adapted Lean. § XII's path-law block is UEOT's
  `formalization/ueot-core/UEOT/V3/DynamicsKernel.lean` (namespace `UEOT.V3.DynamicsKernel`, Copyright
  2025-2026 Degui Qian), adapted to `homK`: `Lumps.fiberConst` from `strongLumpability_fiber_constant`,
  `mapHist` and `measurable_mapHist` from `mapHistory` and `measurable_mapHistory`, `appendHist` and `measurable_appendHist` from `appendHistory` and
  `measurable_appendHistory`, `mapHist_comp_appendHist` from `mapHistory_comp_appendHistory` and `mapHistory_appendHistory`,
  `appendHist_prefix` from `appendHistory_prefix_next`, `chainLaw_prefix_zero` and `chainLaw_prefix_succ`
  from `homTrajMeasure_prefix_zero` and `homTrajMeasure_prefix_succ`, `chainLaw_step` from the first step
  of `homTrajMeasure_prefix_succ`, `homK_compProd_naturality` from `homHistory_compProd_naturality` and
  `compProd_comap_map` from its last step, `pathMeasure_eq_of_prefix_eq` from the declaration of the same
  name, `runLaw_map_of_lumps` from `homTrajMeasure_path_naturality` at a Dirac start, `runLaw_time_one`
  from `homTrajMeasure_dirac_time_one`, `lumps_of_runLaw_map` from `pathLaw_implies_strongLumpability`, `lumps_iff_runLaw_map` from `strongLumpability_iff_pathLaw`, and
  `chainLaw_prefix_naturality` and `chainLaw_map_of_lumps` from `homTrajMeasure_prefix_naturality` and
  `homTrajMeasure_path_naturality`. That file is in UEOT's Apache-2.0 export, the archive that
  `publications/artifacts/lean4-core-export/export_lean4_archive.py` builds from
  `formalization/ueot-core/UEOT/` (v1.0.0, base commit 83ecdb12, DOI 10.5281/zenodo.24433585), licensed
  Apache License, Version 2.0, with its `NOTICE` in the same directory.

## Prior art for § XII, every window (searched 2026-11-27)

- Kelly, *Reversibility and Stochastic Networks* (1979), § 1.2, p. 5: a process is reversible if
  `(X(t1), ..., X(tn))` has the law of `(X(τ − t1), ..., X(τ − tn))` for all `t1, ..., tn, τ`; Lemma 1.1,
  p. 5: a reversible process is stationary. Theorem 1.2, pp. 5-6: a stationary Markov chain is reversible iff
  some positive `π(j)` summing to one satisfy detailed balance; its proof writes the probability of
  `m + 1` consecutive states as `π` times a product of transitions and reverses it, the argument of
  `pathWeight_rev`.
- Levin, Peres, Wilmer, *Markov Chains and Mixing Times*, 2nd ed., § 1.6, (1.29)-(1.31), pp. 13-14: for a
  probability distribution `π` satisfying detailed balance (1.29), the weight of a path equals that of its
  reversal (1.30), so from `π` the law of `(X0, ..., Xn)` is the law of `(Xn, ..., X0)` (1.31). (1.30) is
  `pathWeight_rev`; (1.31) is `chainLaw_finPath_map_rev`. LPW take `π` a probability distribution, not
  positive; Kelly's Theorem 1.2 takes it positive.
- Kelly 1979, Exercise 1.2.9, p. 10: "If X(t) is a reversible stochastic process show that so is
  Y(t) = f[X(t)] for any function f." `chainLaw_coarseN_map_reverse` composes that step with (1.31), and
  `chainLaw_window_map_reverse` adds stationarity (Mathlib `Kernel.IsReversible.invariant`,
  `chainLaw_window_eq_finPath`).
- What is ours is the formalization only: the reversal on Mathlib's `Kernel.trajMeasure` with
  `Kernel.IsReversible`, composed with a measurable observer, for every window of consecutive times, and
  the two-sided `coarse_graining_trade`.
- Lean neighbours, PARTLY VERIFIED (source read, type not elaborated, outside this dependency closure).
  gszep/times-arrow (commit 0f8e977) `TimesArrow.Markov.pathPMF_reversePath`: under pointwise detailed
  balance the path `PMF` of every length `T` is invariant under path reversal; no observer step.
  itakura-hidetoshi/4d-mass-gap (commit 615babf), `MGAP4D/MathlibAnalytic/LinearMarkovFinitePathReversal.lean`:
  `linearMarkovFinitePathPMF_map_reverse_of_detailedBalance`, the same as a `PMF.map` equality on a finite
  carrier, and `linearMarkovFinitePathPMF_expectation_reverse_of_detailedBalance`, the expectation of every
  real path function invariant under reversal; `MGAP4D/MathlibAnalytic/LinearMarkovTwoSidedIntegerPathReflectionInvariance.lean`:
  `linearMarkovTwoSidedIntegerPathMeasure_map_reflection`, a two-sided ℤ-indexed path measure invariant
  under `t ↦ -t`, and `linearMarkovIntegerFiniteMarginalMeasure_map_reflectionReindex`, every finite time
  set. TauCeti (repository TauCetiProject/TauCeti, commit 9f9b83d)
  `TauCeti.Probability.markovChainLaw_map_prefix_apply_singleton` (`Process/MarkovChain.lean`): the
  product formula `ν {w 0} * ∏ i, κ (w i) {w (i + 1)}` for the finite path masses of `markovChainLaw`,
  which `chainLaw_finPath_singleton` states for `chainLaw`; and, in the same repository and commit,
  `MeasureTheory.Measure.markovChainLaw_setOf_forall_apply_eq` (`MarkovChain/Cylinder.lean`), the
  cylinder formula at monotone times.
- The erasing half of `coarse_graining_trade` from the lift side: Wolfer and Watanabe, § 4.4.3, p. 26
  (under § XII above).

## Prior art for § IV, the 2-adic norm form (searched 2026-11-27)

- The norm image of ℤ_[2] as a set, `N2` (`q2_nnnorm_mem`, `normN2_surjective`): not located as a single
  Mathlib lemma as of 2026-11-27, searched as follows: grep of `Mathlib/NumberTheory/Padics`, `exact?` on
  three phrasings, LeanExplore on two. It follows from `PadicInt.norm_eq_zpow_neg_valuation` and
  `norm_zero`; `n2Run_eq_norm` uses `PadicInt.norm_p_pow`.
- Mathlib's `IsDiscreteValuationRing.idealOrderIsoENat : Ideal R ≃o ℕ∞ᵒᵈ` ends where `e2 : ℕ∞ᵒᵈ ≃o N2`
  starts; composed they give `Ideal ℤ_[2] ≃o N2` (ideals of a discrete valuation ring; ideal `(2 ^ n)` for
  norm `2⁻¹ ^ n`). There is also a value-group form,
  `Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt`. The order content of `e2` on ℤ_[2] is
  `q2Val_le_iff_norm_le` (`ZeroParadox/Valuation/Scale.lean`).
- Sutherland, MIT 18.782 Lecture 4 (Fall 2013), Def. 4.10, p. 3 (`v_p(0) = ∞`) and Thm. 4.16, p. 4 (every
  nonzero ideal of ℤ_p is `(p^m)`); Stacks Project tags 00IE (discrete valuation ring) and 00IH (ideals of a
  valuation ring correspond to ideals of its value group). These give the valuation and ideal side; no
  retrieved text states the norm image itself.
- `boolN2_bot_cover_and_limit` takes its order conjuncts from `boolNInfL_bot_cover_and_limit` along
  `boolN2Iso`; its limit conjunct is proved directly, in the subspace topology of `N2` in `ℝ≥0`.

## Prior art for § XIII, the gap count (searched 2026-11-27)

- Fractal strings: Dettmers, Giza, Knox, Morales, Rock, "A survey of complex dimensions, measurability, and
  the lattice/nonlattice dichotomy", arXiv:1510.06467. Def. 3.1, p. 10: "An ordinary fractal string Ω is a
  bounded open subset of the real line. A fractal string L = (ℓj)_{j=1}^∞ is a nonincreasing sequence of
  positive real numbers such that lim_{j→∞} ℓj = 0." Def. 3.8, p. 12: the geometric counting function, defined for
  `x > 0` by `N_L(x) := #{j ∈ ℕ : ℓj⁻¹ ≤ x}`. Def. 3.3, p. 11: the dimension `D_L` is the abscissa of
  convergence of `Σ ℓj^s`. Thm. 3.4, p. 11, a restatement of Lapidus-van Frankenhuijsen Thm. 1.10: for an
  ordinary fractal string with infinitely many components and `vol1(Ω) = sup Ω - inf Ω`,
  `D_L = dim_M(∂Ω)`.
- Read through these, the gaps `n2GapInt n` of `n2Real` form an ordinary fractal string with lengths
  `(1/2)^(n+1)` (`volume_n2GapInt`) summing to the span (`tsum_volume_n2GapInt`, `spanGap_n2Real`), which is
  Thm. 3.4's hypothesis; `Σ ((1/2)^(n+1))^s` converges exactly for `s > 0`, so `D_L = 0`. The corpus
  proves the Hausdorff dimension (`dimH_n2Real`), not the Minkowski one. For a fractal string `ℓ` and
  `r > 0`, `gapCount ℓ r` is `N_L(1/r)`.
- The 2-adic side: Lapidus, Lũ' Hùng, van Frankenhuijsen, "Minkowski dimension and explicit tube formulas
  for p-adic fractal strings", arXiv:1603.09409 (v4, 2018). § 2.3, pp. 7-8: the p-adic Euler string
  `E_p = ⋃_{n≥0} (a_n + p^n ℤ_p)`, with geometric zeta function `Σ p^(-ns) = 1/(1 - p^(-s))` and `D = 0`.
  Remark 2.7, p. 8 (the punctured unit ball): "The unit ball minus the origin is not a ball itself, but
  instead the infinite union" `ℤ_p \ {0} = ⋃_{n≥0} ⋃_{k=1}^{p-1} (k p^n + p^(n+1) ℤ_p)`, and "This union is
  isomorphic to the Euler string". At `p = 2` the pieces are `2^n + 2^(n+1) ℤ_2`, each of Haar measure
  `2^(-(n+1))` (our arithmetic, not stated there): the lengths of `n2GapInt`.
- What is ours: the exact identity `cxQ2_eq_gap_count` (`cxQ2_eq_gapCount`): for `x ≠ 0` in `ℚ_[2]`,
  `cxQ2 x = N_L(1/‖x‖)` for the string of lengths `(1/2)^(n+1)`, and at 0 of `ℚ_[2]` both sides are ⊤ of
  `ℕ∞` (the count at threshold 0, outside Def. 3.8's `x > 0`); the log law on the scaled ladder
  (`ladder_count_eq_log`), its converse for positive summable gaps (`log_law_iff_ladder`, with controls for
  each hypothesis), the control `harm_no_log_law`; and the Lean. The fractal-string framework is not ours.

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
  without positive entropy. Under positive entropy (`0 < p < 1`) support membership and null singletons do not
  single out ⊥ of `ℕ → Bool`, since every tape has both (`dial_pinned_faces`, `trials_support_null`); for
  `0 < p < 1` with `p ≠ 1/2` the law does single it out, as the only tape whose translation `xorOffset t`
  preserves `trials p hp` (`xorOffset_measurePreserving_iff`, § X); at `p = 0` the law is the Dirac mass at ⊥ of `ℕ → Bool`
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
- § XI: the observer is named (Tim, 2026-11-26). To an observer of values, a halted state padded with
  "stay" and a self-loop give the same constant run, and the question asked is heads versus non-heads
  (`ae_leaves_iff`); to an observer of available moves they differ (the move-side pointers above). The kernel
  `K` is a supplied argument: nothing derives it from the die or from a `ZPSemilattice`, and in the
  `ZPSemilattice` `example` the law from ⊥ of `L` exists because `K` is given. `glauber_slot_leaves`
  relocates the hypothesis `0 < p` into `glauberExciteNN_pos`; it does not remove it.
- § XII, motivation only. Tim, 2026-07-11: "There's also the fact that the.bridge.runs one direction and
  to get it to run the other way you look at it from when zero and Infinity reverse roles (the snap
  itself)". This is a `Reading:`; § XII proves nothing about the snap or about zero and infinity. The
  statement it motivates is `coarse_graining_trade`, read as two arrows trading places (`Reading:`).
- § XII, lumping. A step-compatible die does not force lumpable weights on a kernel subordinate to it
  (CONTROL B, whose kernel's own support die is not step-compatible), and a subordinate kernel that lumps
  does not make the die's relation step-compatible (CONTROL A), since the die may hold steps of weight 0.
  `stepCompat_supp_of_fiberConst` and `quot_leavesAt_of_ae` are one way: a step-compatible support die
  does not give the per-class form (`suppControlKernel_stepCompat_not_fiberConst`), and the `Bool` CONTROL
  refutes the converse of the second. `lumps_id_of_upStepInvariant` needs `UpStepInvariant` as a
  hypothesis, on a carrier with measurable singletons; it is not derived.
- § XII, reversibility, both directions. A kernel reversible w.r.t. no probability measure can lump to a
  reversible one: `rot4` and its lumping along parity (`a4_direction_erased`), where the swap of `Bool` is
  reversible w.r.t. the counting measure `dirac true + dirac false`, of mass 2 and not a probability
  measure; w.r.t. the probability measure `(1/2) • (dirac true + dirac false)` it is
  `boolSwap_reversible_half`. From a reversible start,
  lumping gives a reversible kernel for a measurable lumping map on a general measurable carrier
  (`isReversible_map_of_lumps`; along the map to `Unit` its conclusion holds for every kernel, the CONTROL
  after `a4_direction_erased`), and, on a finite carrier with measurable singletons, from a probability
  initial law w.r.t. which the Markov kernel is reversible, every measurable observer, lumpable or not, sees
  each window of consecutive times with the law of its reversal (`chainLaw_window_map_reverse`; from time
  0: `chainLaw_coarseN_map_reverse`; singleton masses: `chainLaw_coarseN_reverse`, three times
  `chainLaw_coarse3_reverse`). `coarse_graining_trade` states both directions. `Reading:`
  coarse-graining can erase an arrow, and from a reversible start it creates none in any window of
  consecutive times; "two arrows trade places" is this reading. Without detailed balance the reversal can
  fail: at the matrix level, `rotMat` from `unifFin4` (`rot4_coarse_not_reversal_symmetric`, with
  `rotMat_not_detailedBalance`); at the chain level, `rot4` from every probability law giving `0` positive
  mass (`rot4_chainLaw_not_reversal_symmetric`). The observer need not see a
  Markov chain: `lazyPairs` under `lazyPairsProj` is not lumpable and its observed three-time statistic fits
  no Markov chain over ℚ (`lazyPairs_coarse_not_markov`), and its observed statistic is reversal-symmetric
  at every `n` (the `example` after `coarseLawN_reverse`'s section). At the matrix level every `n` is proved
  over any commutative semiring (`coarseLawN_reverse`; `coarseLaw2_reverse`, `coarseLaw3_reverse`). The
  `lazyPairs` statements are at the matrix level over ℚ and are not instantiated at the measure level.
  Detailed balance and a reversing involution of the
  steps are different conditions: `absorb4` admits no reversing involution of its steps
  (`absorb4_not_sigma_reversible`) and its kernel is reversible w.r.t. every measure on its fixed points
  (`absorb4_reversible`).
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
  `tape_never_fires_iff`. § XI: `runLaw_stay_eq_trials`, `runLaw_leaves`, `ae_leaves_iff`,
  `slot_stay_eq_trials`, `glauber_slot_leaves`, the `slotKernel 0` CONTROL `example` and the `ZPSemilattice`
  `example` use `trials_cyl` (PoleWithinEnsemble); the converse CONTROL `example` (after the `slotKernel 0`
  control) uses no EXPERIMENTAL declaration;
  `glauber_slot_leaves` also `glauberExciteNN` (PoleWithinEnsemble); `leave_half_of_maxEntropy` uses
  `eq_half_of_maxEntropy` (MaxEntropy); the rest of § XI uses none. § XII: `ae_obs_leaves_iff`,
  `quot_leavesAt_of_ae`, `ae_landing_const` and the `Bool` converse CONTROL `example` use `trials_cyl`
  (PoleWithinEnsemble), through `ae_leaves_iff` or `runLaw_leaves`; the rest of § XII uses none. `dial_fire_jump`, `fireMass`, `fireMass_eq`, `fireMass_not_continuousAt_zero`,
  `fireWithin`, `dial_digital_limit`, `unpack`, `unpack_apply`, `unpack_measurePreserving`,
  `pack_measurePreserving` and `dial_entropy_pos_iff` use no declaration of an EXPERIMENTAL module (theirs come from
  `ZeroParadox/Information/CrossingTrials.lean` and Mathlib), though their module imports them.
