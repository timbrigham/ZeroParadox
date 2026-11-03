# Crossing trials, § IV–VIII: from almost surely to one run, and from one firing to a state sequence

Ride-along for `ZeroParadox/Information/CrossingTrials.lean`. The Lean file holds the declarations, the
Engineer's Take and the per-declaration glosses; this file holds the prior art, the open items and the
two-chart reading for § IV–VII, and § VIII's conditional below.

## What the sections establish, as conditionals

- § IV. If `0 < p ≤ 1`, some tape fires infinitely often (`exists_fires_io`). Not every tape fires even
  once (the `example` after it, the all-`false` tape). Measure one buys an existential, never a universal.
- § V. If `0 < p ≤ 1`, the tapes silent from stage `N` on (`silentFrom N`) are the intersection of zero
  blocks whose measures are at most `2⁻ᵐ` (`trials_zeroBlock_le`, `silentFrom_eq_iInter`); a tape fails
  to fire infinitely often iff it is silent from some `N` (`not_mem_limsup_fires_iff`).
- § VI. If `0 < p ≤ 1`, a class `𝒯` of tests contains every zero-block test for `trials p hp`, and the
  tape `w` avoids `𝒯`, then `w` fires infinitely often (`fires_io_of_avoids`). The avoidance is the
  hypothesis `htyp` on one tape. For `𝒯` the zero-block tests it is weak: the all-`true` tape, a
  constant tape, meets it at every `p ≤ 1` (the third `example`); it is not Martin-Löf randomness
  (open item 1 concerns that). One way: the squares tape
  fires infinitely often (the first `example`), and for every `0 < p ≤ 1` and every such `𝒯` it does
  not avoid `𝒯` (`squaresTape_not_avoids`; the first `example` is the case `p = 1/2`); at `p = 1/2`
  the all-`true` tape fires infinitely often and lies in every one block, each of measure at most
  `2⁻ᵐ` (the second `example`), so it does not avoid a class that also holds those one-block tests.
- § VII. In `slotMotion`, `false` steps elsewhere and to itself (`slotMotion_leavesAt_false`); `true`
  steps to itself only (`slotMotion_selfOnlyAt_true`). Every tape drives a run (`slotRun_isRun`). Along
  a one-to-one lax map, stepping elsewhere carries to the image (`Motion.LaxHom.leavesAt`, in
  `ZeroParadox/Die.lean`), with no tape and no measure. `slotRun_image_departs_of_avoids` gives an image
  run that leaves its start for a tape meeting § VI's hypotheses. Those hypotheses are sufficient, not
  necessary: any tape that fires once gives such a run (`slotRun_crosses_iff`; the `example` after the
  theorem), and the squares tape gives one while failing them at every `0 < p ≤ 1` (the second
  `example`, from `squaresTape_not_avoids`). `Reading:` what § VI adds is a guarantee stated through
  test sets, naming no stage at which the tape fires. The all-`false` tape drives a run that never leaves `false` (the
  closing `example`).
- § VIII. If a tape fires at some stage (`hw`) and `φ : Bool → L`, `L` a `ZPSemilattice`, sends
  `false` to ⊥ of `L` and `true` to a point other than ⊥ of `L`, then `φ` applied to the run with the
  stages before the first firing dropped is a state sequence meeting `t_snap_given`'s `hcc1` and
  `hocc` (`t_snap_of_fires_once`). It steps once, at index 1, and stays, so it is not an
  `IsStrictStateSequence` (the file's last `example`). If `0 < p ≤ 1`, the fired-once tapes have
  `trials p hp` measure one (`trials_fires_once`), and § VI's hypotheses give `hw`
  (`t_snap_of_avoids`). `Reading:` `hw` is the occurrence commitment in its slot chart, as one
  hypothesis on the realized tape (`ZeroParadox/Order/Snap.lean` states both charts).

## Prior art

- **Effective second Borel–Cantelli lemma.** G. Davie, "The Borel-Cantelli lemmas, probability laws and
  Kolmogorov complexity", Ann. Probab. 29(4) (2001) 1426–1434. Davie's text was not retrieved; it is cited
  as restated in P. Potgieter, arXiv:1612.09492v1, p. 2, Lemma 1.1, attributed there to [2] = Davie
  (reference list, p. 13): for "a uniform sequence of Σ⁰₁ sets" {A_k}, "(ii) If the events {A_k} are
  pairwise independent and ∑_k λ(A_k) = ∞, then A_k must occur infinitely often for each α ∈ KC", with λ
  the Lebesgue (fair-coin) measure and KC the Kolmogorov–Chaitin complex sequences (p. 1: prefixes
  incompressible up to a constant, `∃k ∀n K(α(n)) ≥ n − k`). With `K` prefix-free complexity, these are
  exactly the Martin-Löf random sequences (Levin–Schnorr: Franklin and Porter, arXiv:2004.02851, p. 16,
  Theorem 2.5); Potgieter's p. 1 does not say whether its `K` is prefix-free. § VI has the shape of
  (ii) for the events `fires n`, with two differences: the measure is Bernoulli(`p`) for any
  `0 < p ≤ 1`, computable or not, and the hypothesis is avoidance of a parameter class `𝒯` holding the
  zero-block tests. At `p = 1/2` the weakest such hypothesis (`𝒯` the zero-block tests) is implied
  by Martin-Löf randomness granted open item 1, which includes that `trials (1/2)` is the fair-coin
  measure; a larger `𝒯` can make the hypothesis stronger (no tape avoids the class of all families).
  The credit runs from Davie to here.
- **Computable non-atoms are not random.** J. Reimann and T. Slaman, "Measures and their random reals",
  arXiv:0802.2705, p. 9, Theorem 4.4, (i) ⇒ (ii): a computable sequence that is not an atom of a
  probability measure `µ` is not `µ`-random (Martin-Löf randomness relative to a representation of `µ`).
  `squaresTape_not_avoids` has that shape at Bernoulli(`p`), where the squares tape is not an atom for
  any `0 < p ≤ 1`; its test is a zero-block test needing only the integer `K`, and that zero-block tests
  are tests in their sense is not proved here (open item 1, stated at `p = 1/2`). The credit runs from
  Reimann and Slaman to here.
- **Kurtz null tests.** J. Franklin and C. Porter, "Key developments in algorithmic randomness",
  arXiv:2004.02851, p. 32, Definition 4.24 (citing Wang): "A Kurtz null test is a Martin-Löf test ⟨V_i⟩
  such that for some computable function f : ω → (2^{<ω})^{<ω}, V_n = [f(n)] for all n"; p. 33, Theorem
  4.26 (credited there to Wang and to Downey, Griffiths and Reid): a sequence is Kurtz random iff it
  passes all Kurtz null tests. Each level of a `ZeroBlockTest` is a finite union of cylinders, chosen
  by a primitive recursive index, so at `p = 1/2` a zero-block test has the shape of a Kurtz null test
  (open item 1).
- **Kurtz randomness in Lean.** C. Freer, `algorithmic-randomness`
  (github.com/cameronfreer/algorithmic-randomness, commit `863da3d`,
  `AlgorithmicRandomness/Randomness/Kurtz.lean`, retrieved 2026-11-01): `IsKurtzRandom x := ∀ T :
  ComputableTree, fairCoin T.paths = 0 → x ∉ T.paths`, with `IsMartinLofRandom.isKurtzRandom` and
  `ComputableCantorPoint.not_isKurtzRandom`. Fair-coin measure only.
- **Martin-Löf randomness in Lean.** A. Milovanov, `kolmogorov-complexity-lean`
  (github.com/AlexeyMilovanov/kolmogorov-complexity-lean, commit `28da513`,
  `KolmogorovMathlib/AlgorithmicRandomness/MartinLof.lean`, retrieved 2026-11-01):
  `IsMartinLofTest μ U := IsUniformlyEffectiveOpen U ∧ ∀ n, μ (U n) ≤ dyadicValue 1 n`, "a uniformly
  effective open sequence of sets whose measures decrease as `2⁻ⁿ`"; `IsMartinLofRandom μ w := ∀ U,
  IsMartinLofTest μ U → w ∉ ⋂ n, U n`. `AvoidsTests` has the shape of `IsMartinLofRandom` with the test
  class left as a parameter. The same library's `EffectiveSLLNBernoulli.lean` states
  `tendsto_freqOne_of_isMartinLofRandom_bernoulli'` ("SUV Theorem 34"): for `p ≤ 1` with
  `IsComputableReal (p : ℝ)` and `x` Martin-Löf random for its `bernoulliMeasure p hp`, the frequency of
  ones in `x` tends to `p`; for `p > 0` that gives infinitely many ones. Its hypothesis needs a
  computable `p`, which § VI does not; that Martin-Löf randomness meets § VI's `htyp` for `𝒯` = the
  zero-block tests is open item 1 at `p = 1/2` and is not stated here for other `p`, and its
  `bernoulliMeasure` was not compared with `trials`. For the uniform measure the same library has
  `exists_isMartinLofRandom_uniform` (a Martin-Löf random sequence exists, `EffectiveLaws.lean`) and
  `isEffectivelyNull_singleton_of_computable` (no computable sequence is, `EffectiveNull.lean`); given
  open item 1, the first gives a Martin-Löf random tape meeting `htyp` at `p = 1/2` for `𝒯` = the
  zero-block tests. A tape meeting that `htyp` needs no open item: the all-`true` tape meets it at every
  `p ≤ 1` (§ VI's third `example`), so that hypothesis is weak, and Martin-Löf randomness is the
  stronger property open item 1 is about. None of these libraries is a dependency here.
- **Mathlib.** The pin was searched 2026-11-01 for `Martin-L`, `MartinLof`, `algorithmic(ally)? random`,
  `Kurtz` (case-insensitive, `.lake/packages/mathlib/Mathlib`): zero matches. Not located as of
  2026-11-01, searched as stated. theoremsearch, four phrasings (Kurtz null test; Martin-Löf random for
  Bernoulli `p > 0` has infinitely many ones; a formal-only phrasing; effective Borel–Cantelli), found the
  Franklin–Porter and Potgieter passages above; LeanExplore, two phrasings, returned no randomness
  declaration (an uninformative null).

## What remains open (2026-11-01)

1. **Zero-block tests and the standard test classes.** That every `ZeroBlockTest` at `p = 1/2` is a Kurtz
   null test, hence a Martin-Löf test, is read off the definitions above and is not proved in Lean here;
   nor is it proved that `trials (1/2)` is the fair-coin measure those definitions use. No
   effective-open-set notion was located in `ZeroParadox/**` as of 2026-11-01 (searched for
   `effective(ly) open`, `EffectiveOpen`, `Σ⁰₁`, `Sigma01`, `computably enumerable`, `IsKurtz`,
   `MartinLof`: hits only in prose), and neither library is imported.
2. **Uniformity in `p`.** `exists_halving_block` gives the block length `K` by an existence proof; it is
   not computed from `p`. For one fixed `p` the test needs only the number `K`, so the primitive-recursive
   index holds for every `0 < p` (`zeroBlockTest_silentFrom`). Computability of `p` would matter for a
   test uniform in `p`, and for Milovanov's universal test, which assumes a computable measure.
3. **The bridge to the framework.** No map from ⊥ of a `ZPSemilattice` to a tape is claimed
   (`ZeroParadox/Information/Disjunctive.md` fence 3; fence 1 of the Lean header: nothing here says the
   structureless referent ⊥ is the trial space). `htyp` is a hypothesis on a tape.

## Two charts

`Reading:` CARRIER — Tim's sentence "the bottom is infinitely complex, and somewhere in that complexity
movement is possible" reads here as: if the tape driving a run is typical (it avoids the tests), and the
per-stage chance is positive, the run it drives crosses. Possibility (`LeavesAt` at `false`) is a property
of the motion; crossing is a property of one run; typicality is a property of a tape, a point of
`ℕ → Bool`, never of a state of `slotMotion`, a point of `Bool`.

`Reading:` CARRIER — the tension. In the valuation chart, `infinitude_forces_infinite_complexity`
(`ZeroParadox/Valuation/InfinitudeFloor.lean`) gives complexity ⊤ (the top of `ℕ∞`) at the floor of any
`InfinitudeFloor`; at the 2-adic instance `q2InfinitudeFloor`, on `ℚ_[2]`, the floor is 0 and its
complexity is `cxQ2 0 = ⊤` (`cxQ2_zero`, from the explicit `if x = 0` in the definition of `cxQ2`),
matching the additive-valuation convention that the valuation of 0 is ⊤. Read as a digit tape (a
reading; no map from `ℚ_[2]` to tapes is built here), 0 is the all-`false` tape, the sole member of
`silentFrom 0`, and § VI's hypothesis excludes it at `N = 0` for every `0 < p ≤ 1`
(`zeroBlockTest_silentFrom`). In the tape chart, under the pointwise order, the least element of
`ℕ → Bool` is the same all-`false` tape (the `example` at `ZeroParadox/BottomCannotBe.lean`,
`(⊥ : ℕ → Bool) = fun _ => false`), which is not disjunctive (`allFalse_not_disjunctive`,
`ZeroParadox/Information/Disjunctive.lean`). Tim's maximally complex reading
(`ZeroParadox/Information/Disjunctive.md` fence 3) places the occupant of ⊥ of a `ZPSemilattice`, read as
a tape, among the maximally complex tapes, which by standard theory (Levin–Schnorr; not proved here,
Disjunctive.md fence 2) are Martin-Löf random for the fair coin; that such tapes meet § VI's hypothesis at
`p = 1/2` for `𝒯` = the zero-block tests is open item 1. That hypothesis is weak and does not single
them out: the all-`true` tape meets it too (§ VI's third `example`). The two readings put different tapes in the
role, and nothing in Lean identifies them.

Not claimed: that the realized tape is typical or has fired, or that ⊥ of any carrier is a tape. The
theorem moves "almost surely" (`crossing_almost_surely`, which already assumes `0 < p`) to "this run
crosses" by adding two premises: a class `𝒯` holding the zero-block tests for `trials p hp`, and `htyp`.
§ VIII's `t_snap_of_avoids` derives `hw` from `htyp`; neither is supplied for the realized tape.
