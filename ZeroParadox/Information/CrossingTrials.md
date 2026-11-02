# Crossing trials, § IV–VII: from almost surely to one run

Ride-along for `ZeroParadox/Information/CrossingTrials.lean`. The Lean file holds the declarations, the
Engineer's Take and the per-declaration glosses; this file holds the prior art, the open items and the
two-chart reading for § IV–VII.

## What the sections establish, as conditionals

- § IV. If `0 < p ≤ 1`, some tape fires infinitely often (`exists_fires_io`). Not every tape fires even
  once (the `example` after it, the all-`false` tape). Measure one buys an existential, never a universal.
- § V. If `0 < p ≤ 1`, the tapes silent from stage `N` on (`silentFrom N`) are the intersection of zero
  blocks whose measures are at most `2⁻ᵐ` (`trials_zeroBlock_le`, `silentFrom_eq_iInter`); a tape fails
  to fire infinitely often iff it is silent from some `N` (`not_mem_limsup_fires_iff`).
- § VI. If `0 < p ≤ 1`, a class `𝒯` of tests contains every zero-block test, and the tape `w` avoids
  `𝒯`, then `w` fires infinitely often (`fires_io_of_avoids`). The avoidance is the hypothesis `htyp`
  on one tape; nothing in the file says any tape meets it. One way: the squares tape fires infinitely
  often and is caught by a zero-block test; the all-`true` tape fires infinitely often and is caught by
  one-block tests (the two `example`s).
- § VII. In `slotMotion`, `false` steps elsewhere and to itself (`slotMotion_leavesAt_false`); `true`
  steps to itself only (`slotMotion_selfOnlyAt_true`). Every tape drives a run (`slotRun_isRun`). Along
  a one-to-one lax map, stepping elsewhere carries to the image (`Motion.LaxHom.leavesAt`, in
  `ZeroParadox/Die.lean`), with no tape and no measure. A run of the image motion that leaves its start
  is obtained only for a tape meeting § VI's hypotheses (`slotRun_image_departs_of_avoids`); the
  all-`false` tape drives a run that never leaves `false` (the closing `example`).

## Prior art

- **Martin-Löf randomness in Lean.** A. Milovanov, `kolmogorov-complexity-lean`
  (github.com/AlexeyMilovanov/kolmogorov-complexity-lean, commit `28da513`, file
  `KolmogorovMathlib/AlgorithmicRandomness/MartinLof.lean`, retrieved 2026-11-01). Its definitions, read
  from the retrieved file: `IsMartinLofTest μ U := IsUniformlyEffectiveOpen U ∧ ∀ n, μ (U n) ≤
  dyadicValue 1 n`, "a uniformly effective open sequence of sets whose measures decrease as `2⁻ⁿ`";
  `IsMartinLofRandom μ w := ∀ U, IsMartinLofTest μ U → w ∉ ⋂ n, U n`. `AvoidsTests` has the shape of
  `IsMartinLofRandom` with the test class left as a parameter.
- **The stronger result is there.** The same library's
  `KolmogorovMathlib/AlgorithmicRandomness/EffectiveSLLNBernoulli.lean` (signature retrieved through
  GitHub code search, 2026-11-01) states `tendsto_freqOne_of_isMartinLofRandom_bernoulli'`, labelled
  "SUV Theorem 34": for `p ≤ 1` with `IsComputableReal (p : ℝ)` and `x` Martin-Löf random for its
  `bernoulliMeasure p hp`, the frequency of ones in `x` tends to `p`. For `p > 0` that gives infinitely
  many ones, which is § VI's conclusion under a stronger hypothesis. The library is not a dependency of
  this corpus; its `bernoulliMeasure` was not compared with `trials`; nothing here imports or restates it.
- **Mathlib.** The pin was searched 2026-11-01 for `Martin-L`, `MartinLof`, `algorithmic(ally)? random`
  (case-insensitive, `.lake/packages/mathlib/Mathlib`): zero matches. Not located as of 2026-11-01,
  searched as stated. LeanExplore (`Martin-Löf random sequence`) and theoremsearch with `formality:
  "formal"` (one phrasing) returned no randomness definition; both nulls are uninformative.
- Martin-Löf's 1966 paper and the effective Borel–Cantelli literature were not retrieved; nothing here
  describes them.

## What remains open (2026-11-01)

1. **Zero-block tests are Martin-Löf tests.** Each level is a cylinder over a finite window and the window
   is a primitive recursive function of the level, so in the standard theory every `ZeroBlockTest` is a
   Martin-Löf test for its measure. That implication is not proved in Lean here: the corpus has no
   effective-open-set notion and does not import the library above.
2. **Uniformity in `p`.** `exists_halving_block` gives the block length `K` by an existence proof; it is
   not computed from `p`. For one fixed `p` the test needs only the number `K`, so the primitive-recursive
   index holds for every `0 < p` (`zeroBlockTest_silentFrom`). Computability of `p` would matter for a
   test uniform in `p`, and for the library's universal test, which assumes a computable measure.
3. **The bridge to the framework.** No map from ⊥ of a `ZPSemilattice` to a tape is claimed (fence 1 of
   the Lean header; `ZeroParadox/Information/Disjunctive.md` fence 3). `htyp` is a hypothesis on a tape.

## Two charts

`Reading:` CARRIER — Tim's sentence "the bottom is infinitely complex, and somewhere in that complexity movement is
possible" reads here as: if a run is typical (it avoids the tests), and the per-stage chance is positive,
that run crosses. Possibility (`LeavesAt` at `false`) is a property of the motion; crossing is a property
of one run; typicality is a property of a run, a sequence, never of a point.

`Reading:` CARRIER — the tension, each step a cited declaration: in the valuation chart the proved infinite-complexity point is 0 of the
2-adics: `infinitude_forces_infinite_complexity` (`ZeroParadox/Valuation/InfinitudeFloor.lean`) gives
complexity ⊤ (the top of `ℕ∞`) at the floor of any `InfinitudeFloor`, and at its 2-adic instance that is
v₂(0) = ⊤. Read as a digit tape, 0 is the all-`false` tape: that is
`silentFrom 0`, which lies in a zero-block test for every `0 < p ≤ 1` (`zeroBlockTest_silentFrom` at
`N = 0`), so it is the tape § VI's hypothesis excludes first. In the tape chart under the pointwise order
the least element is the same all-`false` tape (`allFalse_not_disjunctive`,
`ZeroParadox/Information/Disjunctive.lean`). Tim's maximally complex reading
(`ZeroParadox/Information/Disjunctive.md` fence 3) places ⊥'s occupant among the typical tapes. The two
readings put different tapes in the role, and nothing in Lean identifies them.

Not claimed: that any tape is typical, that ⊥ of any carrier is a tape, or that typicality supplies the
occurrence commitment. The theorem moves "almost surely" to "this run crosses" only by adding `htyp`.
