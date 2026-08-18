# The Archimedean fence, what repetition buys, and the concurrent readings

Argument, prior art and fences for `ZeroParadox/Information/Surprisal.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses — including `l_inf`'s docstring, which
is canonical for where the argument stops and stays there.

## What the file formalizes

The Zero Paradox information-theoretic framework over binary ontological states: T1 (unique state
distributions), T1b (JSD = log 2), D5 (DF antisymmetry), T2 (non-conservative circulation), L-RUN
(execution is a non-null state change), and TQ-IH (no execution avoids a non-null config).

Self-contained within information theory and real analysis. Imports ZP-B conceptually (total
disconnectedness, clopen balls) but not as a Lean dependency — ZP-C's theorems do not require the p-adic
structure.

## The converse — the collision is NECESSARY, not decorative

The question these two theorems answer, which no wording gate could: does a non-injective representation
actually **buy** anything, or would the distribution exist anyway? They are stated over an arbitrary `f`
because the fact has nothing to do with ordinals.

`Statement:` under an **injective** map, a distribution confined to one fiber has at most one point in
its support — so it cannot be spread. Therefore a spread confined distribution **refutes** injectivity
outright.

⚠ **Scope the conclusion precisely.** A collision is **not** the only source of a spread distribution —
`exists_spread_pmf` builds one from *any* two points, no collision required. What a collision is the only
source of is a spread distribution **confined to a single denotation**. The confinement hypothesis is
doing all the work and must not be dropped when the sentence is quoted.

**Prior art — both are elementary and neither is new.**
`injective_forces_confined_support_subsingleton` is Mathlib's `Set.Subsingleton.preimage`
(`Mathlib/Data/Set/Image.lean`) composed with a singleton; the proof body is the same argument (composed
with `Set.Subsingleton.anti`). It is not swapped in because the statement mentions `PMF`, and
`#print axioms` follows the STATEMENT — both routes measure `[propext, Classical.choice, Quot.sound]`, so
there is no purity gain, and the hand proof reads locally. Same verdict as the `CovBy` precedent: keep the
hand proof, cite the standard name.

**And the object itself has a standard name the corpus had never used:** `Setoid.ker f` is the "same
image" equivalence — what the docstrings call *the fiber* — and
`Setoid.injective_iff_ker_bot : Injective f ↔ Setoid.ker f = ⊥` (`Mathlib/Data/Setoid/Basic.lean`) is a
**biconditional** of which `confined_non_pure_refutes_injective` is one direction under an added
distinctness hypothesis. Grep of the corpus for `Setoid.ker` as of `f28c8d1`: **0 hits**. Recorded as the
stronger library form, in the shape of the `denselyOrdered_iff_forall_not_covBy` miss.

## The two readings run CONCURRENTLY — spread in the source, certain in the target

**Origin (Tim, 2026-08-06).** On being shown that a fiber-confined distribution is the *reverse* arrow of
the representation map, his reaction was that the zero/infinity boundary *"likely is going to run multiple
directions concurrently, frankly I think it has to."* That is this project's own Two-Pole rule, and on
this object it is checkable rather than a framing.

⚠ **The necessity half — *"it has to"* — is NOT proved and is not claimed.** What is proved is that on
this object both readings do hold at once. Whether a boundary of this kind *cannot* run one direction only
is an open no-go, recorded in `.claude-local/notes/future-research/concurrent_poles_2026-08-06.md`.

**Prior art.** Mathlib's `PMF.map_const : p.map (Function.const α b) = pure b`
(`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`) is the **globally constant** case. One
level up, the measure-theoretic form already has the almost-everywhere framing:
`MeasureTheory.Measure.map_congr` and `MeasureTheory.Measure.map_const`. **The honest delta for keeping a
PMF-level proof:** the statement needs no `MeasurableSpace` and no measurability of `f`, where routing
through `PMF.toMeasure_map` would require `Measurable f`. The in-field name for the conclusion is a
**degenerate distribution / Dirac point mass**. The generalization is to constant **on the support**,
which is the case that arises: a representation map is nowhere near globally constant, it is constant
exactly along one fiber. The conclusion shape (`= pure`, not merely a support equality) is taken from
Mathlib's version rather than settled for at support level.

## The repeated crossing — what repetition does and does not buy

**Origin (Tim, 2026-08-06):** *"one pull. one chance to cross the snap. one action taken which may or may
not work. and a fixed cost every time it fires."* The slot-machine reading: if the crossing is a trial
with positive probability, unboundedly many trials make it eventually certain.

**That reading is correct, and the standard account is in the pinned Mathlib.**
`ProbabilityTheory.measure_limsup_eq_one` (`Mathlib/Probability/BorelCantelli.lean`) — the second
Borel–Cantelli lemma — gives, for independent events whose probabilities sum to infinity (true for any
fixed `p > 0`), that `limsup` has measure **one**. So almost every realization crosses at a **finite**
trial. The slot machine pays.

**What the theorems add is strictly weaker, and worth stating in its own right: no FIXED DEADLINE is
certain.** For each `n`, the probability of not yet having crossed is positive, so no stage can be named
in advance by which the crossing is guaranteed. *"There is almost surely some finite crossing time"* and
*"there is a finite time by which crossing is certain"* are different claims; the first is true and is
Borel–Cantelli's, the second is false and is what `survival_pos` denies. **Do not restate the second as
the first.**

**⚠ THE FENCE THAT CARRIES THE SECTION IS THE OTHER ONE: nothing here says the crossing HAS a
probability.** That a `p` exists at all is untouched, and possibility is not a measure. So this does not
discharge the gap `l_inf`'s docstring names — the step from unbounded surprisal to *forced execution*
being a design principle rather than a consequence — but the reason is the missing `p`, not any failure
of repetition.

**⚠ THE INDEPENDENCE IS A COMMITMENT AND IT IS VISIBLE IN THE HYPOTHESES.** `hstep` says each trial
multiplies the survival probability by the same `1 - p`; that is what independence-with-fixed-`p` buys,
and it is **assumed, never derived**. No product measure and no trial sequence is constructed — `q` is any
real sequence satisfying the recurrence. ⚠ **That is a statement about this file only.**
`ZeroParadox/Information/CrossingTrials.lean` does build the product measure and the trial sequence, and
proves `crossing_almost_surely`: given a constant positive per-stage probability with independent trials,
the crossing fires with probability one. It is a **consistency** result — it does not supply the
probability, which is the open question. Per the standing rule a commitment goes in a hypothesis so the
signature cannot be misread.

**Prior art, and the corpus under-searched itself twice before this was written.**

* Mathlib already has the object: `ProbabilityTheory.geometricPMFReal p n = (1 - p) ^ n * p`
  (`Mathlib/Probability/Distributions/Geometric.lean`), of which `q n = (1 - p) ^ n` is the standard
  **survival function** — the in-field name. ⚠ `geometricPMFReal_pos` does **not** carry the same
  hypotheses as `survival_pos`: Mathlib's takes `0 < p` **and** `p < 1`, ours takes only `p < 1`, because
  `(1-p)^n` needs no positivity where `(1-p)^n * p` does. Ours is the weaker-hypothesis one.
* The limit is Mathlib's `tendsto_pow_atTop_nhds_zero_of_lt_one`, cited not re-proved. ⚠ The nearest
  corpus work is `ZeroParadox/Valuation/ContractionRate.lean`, which uses the **biconditional**
  `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` — stronger than the implication used here, and the same
  Trigger-0 pattern as the `CovBy` case. `ZeroParadox/Order/MarkovContractionDual.lean` is a *different*
  statement (geometric convergence of a Markov law to stationary), not a survival function.

**On the two-sided form (Tim, 2026-08-06):** *"asymptotic from one side and a fixed value from the other,
forced together into a single point by a squeezing."*

`Statement:` **COINCIDENCE kind** — `epsilon0_min_eq_max` (`ZeroParadox/Ordinal/Epsilon0MinMax.lean`)
proves ε₀ is the tower supremum **and** the least fixed point: one object, two extremal
characterisations, both at once. Approached from below, pinned exactly from the other side.

`Reading:` **COINCIDENCE kind** (conjectural) — the framework reads this result as sharing that shape: the
limit value exact, no stage attaining it, both true of one object. **Shared shape only; these live on
different carriers and no instance-of relation is claimed.** ⚠ Report **both** halves: min≡max is
direction-specific, and flattening it to one face is a bedrock error — the asymptotic half alone supports
a conclusion the exact half refutes.

## The Archimedean fence — repetition works in exactly the Archimedean carriers

**Origin (Tim, 2026-08-06):** asked what an *"infinitely slim but non-zero"* crossing probability would
do. In ℝ there is no such number — for any `p > 0` there is `p/2` — so the question is really about which
carrier the argument lives in.

`Statement:` **CARRIER kind** — `archimedean_iff_survival_eventually_lt` proves the carrier-dependence
outright: the repeated-trials argument holds in an ordered field **if and only if that field is
Archimedean**. Not a reading about ℝ; a biconditional on the typeclass.

**What that buys.** An infinitesimal crossing probability never accumulates
(`crossing_stays_infinitesimal`): at every standard `n` the accumulated crossing probability is still
infinitesimal, so no number of pulls makes headway. The slot machine does not merely become unlikely —
its engine is gone.

⚠ **FENCE 1 — `n` ranges over STANDARD `ℕ`.** The result says nothing about infinite hypernatural indices;
this is an **external** statement and the internal one is different and unproved. This is the likeliest
way to misquote the theorem.

⚠ **FENCE 2 — the Archimedean property is NOT the only obstruction, and stating it alone would mislead.**
`PMF` and `MeasureTheory.Measure` are `ℝ≥0∞`-valued, so `ProbabilityTheory.measure_limsup_eq_one` does not
even typecheck over a non-Archimedean `F`. Two independent blockers, not one.

⚠ **FENCE 3 — THIS DOES NOT CONTRADICT `ZeroParadox/Reals/OrderedField.lean`; the two claims are about
different objects.** That file states in bold that the **snap**'s impossibility in an ordered field is due
to **density, NOT** the Archimedean property (ℝ(t) is a non-Archimedean ordered field where the snap still
fails, and `f_snap_impossible` carries no Archimedean hypothesis). Both are true: the *snap* is blocked in
**every** ordered field; the *repeated-trials argument* works in **exactly** the Archimedean ones.

⚠ **FENCE 4 — infinitesimality does not imply non-zero.** `ArchimedeanClass.mk 0 = ⊤ > 0`, and
`∀ k, k • p < 1` holds at `p = 0`, so `0 < p` remains a separate necessary hypothesis wherever it is
wanted.

⚠ **FENCE 5 — the p-adic route is a DIFFERENT non-Archimedean-ness and is not this one.** Khrennikov's
ℚ_p-valued probability (survey: `.claude-local/papers/dragovich_padic_physics_2009_0904.4205.pdf` § 10,
"Q_p-valued Probability") replaces the **topology** of frequency stabilisation, not the **order**. `ℚ_[p]`
is not an ordered field and its absolute value is real-valued with an Archimedean value group, so
"infinitely slim but non-zero" is not expressible there at all. The corpus's home for the Ostrowski sense
of "Archimedean" is `ZeroParadox/Valuation/SnapDichotomy.lean`. Entry points if this route is ever
pursued: `MeasureTheory.AddContent` (arbitrary `AddCommMonoid`) and `MeasureTheory.VectorMeasure`; `PMF` /
`Measure` / `Kernel` are hard-wired to `ℝ≥0∞`.

### Prior art — the biconditional is PUBLISHED and this is a formalization

Kantrowitz & Neumann, *"Another face of the Archimedean property"*, The College Mathematics Journal **46**
(2015), no. 2, 139–141, establish the equivalence of the **geometric series test** and the Archimedean
property for ordered fields — `archimedean_iff_survival_eventually_lt` in different dress.

⚠ **The capsule is paywalled and its body was not read. Its CONTENT is nonetheless sourced — from the
open-access 2016 sibling, read in full**, which both states the result and *uses it as a cited fact inside
a proof*:

* *"An elementary example from the Classroom Capsule [6] exposes the equivalence of the geometric series
  test and the Archimedean property."*
* *"Because F is Archimedean, we know from [6] that the geometric series ∑(1/2)ⁿ converges in F."*
* and the scope: *"While the geometric series test is certainly not, on its own, strong enough to
  guarantee completeness …"*

So the capsule's content is **the geometric series test holds in an ordered field iff that field is
Archimedean.** Bibliographic data is confirmed twice over — the reference lists of *Completeness of
Ordered Fields and a Trio of Classical Series Tests* (Abstr. Appl. Anal. 2016, art. 6023273) and *Normed
Algebras and the Geometric Series Test* (Surveys in Math. and its Appl. **12** (2017), 203-217, ref.
[10]), both in `.claude-local/papers/`, agree on volume 46, 2015, pp. 139-141, MR3361762.

**The delta, stated exactly.** Theirs is the **series** form (∑ rⁿ converges for `0 < r < 1`); this file's
is the **sequence** form (`rⁿ → 0`, with `r = 1 - p`). In an ordered field the two are linked by the
geometric partial-sum identity — the partial sums are exactly `(1 - rⁿ)/(1 - r)` — which is field algebra
rather than analysis. ⚠ **That link is NOT formalized and is not claimed as proved**; what is claimed is
that the two are the series and sequence versions of one characterization, and that the characterization
is theirs.

**The converse direction also appears in Propp, *Real Analysis in Reverse*, Amer. Math. Monthly **120**
(2013), p. 13 — read at source:** *"Note that the Ratio Test implies that 1/2 + 1/4 + 1/8 + … converges,
implying that R is Archimedean (the sequence of partial sums 1/2, 3/4, 7/8, … isn't even a Cauchy sequence
if there exists an ε > 0 that is less than 1/n for all n)."* That is convergence-implies-Archimedean at
`r = 1/2`, with its proof — the Ratio Test supplying only the convergence *premise*, the implication
itself proved by the ratio-free parenthetical. ⚠ It is **not** stated as an equivalence (Propp's
equivalences run Ratio Test ⟺ *completeness*), so the biconditional remains Kantrowitz–Neumann's. Note the
single ratio is the **stronger** form, not a weaker one: Propp reaches Archimedean from `r = 1/2` alone,
where the converse consumes its hypothesis at arbitrary `p`.

⚠ **Propp writes the series in symbols and never names it, so `"geometric series"` occurs ZERO times in
that paper.** Do not read that zero as his having no geometric series test. Grep the CLAIM, not the name.

**Honest delta: a Lean 4 formalization of a known 2015 characterization, whose forward half is discharged
by Mathlib** (`exists_pow_lt_of_lt_one`); the converse is not in the pin (Mathlib's `archimedean_iff_*`
family is nat/int/rat unboundedness only).

Bernoulli's inequality is Mathlib's `one_add_mul_le_pow` (`Mathlib/Algebra/Order/Ring/Pow.lean`), cited
not re-proved; `1 - (1-p)^n ≤ n·p` is the **union bound** (Boole). The ordered-infinitesimal reading of
probability is Benci–Horsten–Wenmackers, *Non-Archimedean Probability*, Milan J. Math. 81 (2013) — where
only `∅` gets probability zero — read at source: Prop. 2(ii), p. 9, from axioms (NAP0)–(NAP3) alone.

⚠ **Nelson, *Radically Elementary Probability Theory* (1987), is a DIFFERENT shape and does not belong
under that heading.** Nelson's probabilities are **real-valued on finite spaces**; the infinitesimals are
external IST ones **on ℝ**, and negligibility means *infinitesimal* probability rather than zero. It is not
an ordered-non-Archimedean-valued probability.

Non-vacuity of the infinitesimal hypothesis is by **citation, not import**: `Hyperreal.epsilon_pos` and
`Hyperreal.archimedeanClassMk_epsilon_pos`. ⚠ `Hyperreal`'s classical NSA layer (`Infinitesimal`, `IsSt`,
`st`) is deprecated since 2026-01-05 in favour of `ArchimedeanClass`; design against the latter.
