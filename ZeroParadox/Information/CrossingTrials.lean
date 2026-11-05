import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Tactic
import ZeroParadox.Die
import ZeroParadox.Order.Snap

set_option maxHeartbeats 400000

/-!
# Crossing trials: what a probability on the crossing would buy

## Engineer's Take

I was working through a theory with my robotic assistant, and these were my thoughts as things
evolved.

Given infinite chances you are going to eventually receive the deterministic outcome. If you pull a
slot machine an infinite number of times you have to eventually get the jackpot. One pull. One chance
to cross the snap. One action taken which may or may not work. This does feel like a slot machine.

The line that was missing is a theorem that gives us a probability for Borel-Cantelli. Worth building
just to formalize the pieces.

---

## Formal Overview (AI-assisted)

**This file is a CONSISTENCY result, not a necessity one, and the distinction is the whole point.**

`ZeroParadox/Information/Surprisal.lean` prices the repeated-crossing argument and stops at an
honest gap: *nothing says the crossing HAS a probability*. This file does not close that gap. It
builds the object that would exist **if** it did, and shows the object is coherent — the
requirements-and-witness form the corpus uses elsewhere (`QuineHost`), never an instance-of claim.

Concretely: an infinite sequence of independent Bernoulli(`p`) trials is constructed as a genuine
probability space (`trials`), the per-stage events are shown independent (`fires_iIndepSet`) with
measure exactly `p` (`trials_fires`), and the second Borel-Cantelli lemma then gives
`crossing_almost_surely` — with a **constant positive** `p`, the crossing fires infinitely often
with probability one, hence at some finite stage.

**⚠ WHAT THIS DOES NOT ESTABLISH — four fences, all load-bearing.**

1. **Nothing here says the structureless referent ⊥ IS this space.** Exhibiting a model that meets
   the hypotheses is not showing that **⊥** is such a model; that step is precisely the commitment
   `l_inf`'s docstring names as a design principle rather than a consequence, and a realizability
   result cannot discharge it without circularity. This is the requirements/instance distinction,
   not a technicality.
2. **Measure one is not necessity.** Borel-Cantelli concludes *almost surely* — outside a null set.
   The framework commits that the snap fires, full stop. So this upgrades that commitment from
   *possible* to *measure-one on its own premise*, which is strictly stronger than the former and
   strictly weaker than the latter.
3. **What the argument consumes is DIVERGENCE of `∑ pₙ`, not constancy.** A per-stage probability
   that shrinks fast enough — `pₙ = 2⁻ⁿ` — has a convergent sum, and the **first** Borel-Cantelli
   lemma then gives almost surely only finitely many firings; so a positive chance at every stage is
   genuinely not sufficient. ⚠ **But constancy is this file's ROUTE to divergence, never a
   requirement of the mathematics**, and an earlier draft of this fence said otherwise.
   `measure_limsup_eq_one` consumes measurability, `iIndepSet` and `∑' n, μ (s n) = ∞` — constancy
   appears nowhere — and `Measure.infinitePi` takes an arbitrary family, so `pₙ = 1/(n+1)` is
   non-constant, positive at every stage, divergent, and yields `crossing_almost_surely` verbatim.
   That matters here: a *shrinking* `p` is the natural reading of unbounded surprisal, and under the
   honest boundary a shrinking `p` can still work.
4. **The carrier here is `ℝ≥0∞`, not any framework carrier.** `Measure` and `PMF` are hard-wired to
   it (`PMF α := { f : α → ℝ≥0∞ // HasSum f 1 }`). That is not an obstruction — probability on
   framework objects already exists in the corpus, in **this same carrier**
   (`fC_functor : ℕ ⥤ KleisliCat PMF`, `ZeroParadox/Multihomed/InfoFunctor.lean`), so there is no
   mismatch to explain away. ⚠ An earlier draft called that functor "real-valued", contradicting the
   preceding sentence three lines up. Nothing here crosses a type boundary, and no framework object
   appears in any statement below.

**Prior art. ⚠ THE ASSEMBLY ITSELF IS ALREADY PACKAGED IN MATHLIB, and an earlier draft of this
paragraph claimed it as the contribution.** `ProbabilityTheory.exists_iid` /
`exists_hasLaw_indepFun` (`Mathlib/Probability/HasLawExists.lean`) is proved by exactly this
construction — `use Π i, (𝓧 i), .pi, infinitePi μ, fun i ↦ Function.eval i` — and its
module is one import step away. At `ι = ℕ`, `𝓧 = Bool`, `μ = bernoulli p`, its three
conjuncts **are** § I and § II. `ProbabilityTheory.setBernoulli`
(`Mathlib/Probability/Distributions/SetBernoulli.lean`) is the same `infinitePi`-of-Bernoullis object
on `Set ι`, though it supplies neither coordinate independence nor a marginal.

**What survives as this file's own content is two things, and only two:** `fires_iIndepSet`, the
`iIndepFun`-to-`iIndepSet` bridge — **searched, not located in the pin**, which carries only the
opposite direction `iIndepSet.iIndepFun_indicator` — and § III, the Borel-Cantelli application, which
Mathlib applies to no Bernoulli or i.i.d. product. `trials` is built rather than taken from
`exists_iid` because that result is existential while `crossing_almost_surely` needs a named measure;
that is packaging, not novelty.

Every ingredient is Mathlib's and is cited rather than rebuilt:
`Measure.infinitePi` (`Mathlib/Probability/ProductMeasure.lean`), `iIndepFun_infinitePi`
(`Mathlib/Probability/Independence/InfinitePi.lean`), `PMF.bernoulli`, and
`ProbabilityTheory.measure_limsup_eq_one` — the second Borel-Cantelli lemma
(`Mathlib/Probability/BorelCantelli.lean`). ⚠ The assembly is **not** the contribution — see above. The
companion fact that the argument works in exactly the Archimedean ordered fields is
`archimedean_iff_survival_eventually_lt` (`ZeroParadox/Information/Surprisal.lean`), itself a
formalization of a published characterization.

## Structure

- § I   The trial space, and that it is a probability space
- § II  The per-stage events: measurable, independent, marginal exactly `p`
- § III The payoff; § IV–VIII to one run and `t_snap_given`'s hypotheses; § IX topology (`.md`)
-/

namespace ZeroParadox

open MeasureTheory ProbabilityTheory Filter

/-! ## § I. The trial space -/

/-- **The trial space:** independent Bernoulli(`p`) flips, one per stage. `p` and its bound are
explicit **hypotheses**, not fields of a structure — the framework could be wrong about either, so
they belong on the signature. -/
noncomputable def trials (p : NNReal) (hp : p ≤ 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ => (PMF.bernoulli p hp).toMeasure)

instance (p : NNReal) (hp : p ≤ 1) : IsProbabilityMeasure (trials p hp) := by
  unfold trials; infer_instance

/-! ## § II. The per-stage events -/

/-- **The event:** the crossing fires at stage `n`. -/
def fires (n : ℕ) : Set (ℕ → Bool) := {w | w n = true}

/-- **`Statement:` each event is measurable.** -/
theorem fires_measurable (n : ℕ) : MeasurableSet (fires n) :=
  measurableSet_eq_fun (measurable_pi_apply n) measurable_const

/-- **`Statement:` the coordinates are independent under the product measure.** Mathlib's
`iIndepFun_infinitePi`, instantiated; nothing is proved here that the library does not give. -/
theorem coords_iIndep (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (fun (i : ℕ) (w : ℕ → Bool) => w i) (trials p hp) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- **`Statement:` each event lies in the sigma-algebra of its own coordinate.** -/
theorem fires_comap (n : ℕ) :
    MeasurableSet[(inferInstance : MeasurableSpace Bool).comap (fun w : ℕ → Bool => w n)]
      (fires n) :=
  ⟨{true}, measurableSet_singleton true, rfl⟩

/-- **`Statement:` so the events themselves are independent.** This is the step the assembly
actually owes: coordinate independence is Mathlib's, event independence is derived from it. -/
theorem fires_iIndepSet (p : NNReal) (hp : p ≤ 1) : iIndepSet fires (trials p hp) := by
  rw [iIndepSet_iff_iIndepSets_singleton fires_measurable, iIndepSets_iff]
  intro S f hf
  have hrw : ∀ i ∈ S, f i = fires i := fun i hi => by simpa using hf i hi
  have h1 : (⋂ i ∈ S, f i) = ⋂ i ∈ S, fires i := by
    apply Set.iInter₂_congr; intro i hi; rw [hrw i hi]
  rw [h1, Finset.prod_congr rfl (fun i hi => by rw [hrw i hi])]
  exact (coords_iIndep p hp).meas_biInter (fun i _ => fires_comap i)

/-- **`Statement:` each stage fires with probability exactly `p`.** -/
theorem trials_fires (p : NNReal) (hp : p ≤ 1) (n : ℕ) :
    trials p hp (fires n) = (p : ENNReal) := by
  have hpi : fires n = Set.pi ({n} : Finset ℕ) (fun _ => ({true} : Set Bool)) := by
    ext w; simp [fires]
  rw [hpi, trials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton true)]
  simp [PMF.bernoulli]

/-! ## § III. The payoff -/

/-- **`Statement:` with a CONSTANT positive probability the sum diverges.** ⚠ Constancy is where
this is consumed — see fence 3 in the header. -/
theorem trials_tsum_top (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ∑' n : ℕ, trials p hp (fires n) = ⊤ := by
  simp only [trials_fires]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by exact_mod_cast hp0.ne')

/-- **`Statement:` THE PAYOFF — the crossing fires infinitely often with probability one.** Given a
constant positive per-stage probability, `limsup` of the firing events has measure `1` — the
`limsup` being the set of realizations that fire infinitely often.

⚠ **The further step "hence at some finite stage" is NOT part of this declaration.** Trivially true,
but no finite stage appears in the statement, and an earlier draft carried that clause inside this
`Statement:` gloss.

`Reading:` (conjectural) the framework reads this as the precise content of the commitment that the
snap fires: *if* the crossing carries a constant positive probability and the trials are
independent, occurrence is not merely possible but almost certain. ⚠ **The antecedent is the whole
open question** and nothing here supplies it — see fences 1 and 2. -/
theorem crossing_almost_surely (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp (Filter.limsup fires Filter.atTop) = 1 :=
  measure_limsup_eq_one fires_measurable (fires_iIndepSet p hp) (trials_tsum_top p hp hp0)

/-! ## § IV. Almost surely gives some run, never every run

§ IV–VII: prior art, open items and the two-chart reading are in
`ZeroParadox/Information/CrossingTrials.md`. -/

/-- **`Statement:` if `p ≤ 1` and `0 < p`, then some tape fires infinitely often.** A set of measure
one under a probability measure is nonempty (`nonempty_of_measure_ne_zero`); the antecedent is
`crossing_almost_surely`'s. The conclusion is an existential: it names no tape. -/
theorem exists_fires_io (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    ∃ w : ℕ → Bool, w ∈ Filter.limsup fires Filter.atTop :=
  nonempty_of_measure_ne_zero (by rw [crossing_almost_surely p hp hp0]; exact one_ne_zero)

-- Statement: CONTROL: not every tape fires even once; the all-`false` tape never fires.
example : ¬ ∀ w : ℕ → Bool, ∃ n, w ∈ fires n := fun h => by
  obtain ⟨n, hn⟩ := h (fun _ => false)
  simp [fires] at hn

/-! ## § V. Zero blocks -/

/-- **`Statement:` the tapes that do not fire at any stage in `[N, N + n)`.** -/
def zeroBlock (N n : ℕ) : Set (ℕ → Bool) := {w | ∀ k ∈ Finset.Ico N (N + n), w k = false}

/-- **`Statement:` a zero block is the cylinder over the finite window `[N, N + n)`.** -/
theorem zeroBlock_eq_pi (N n : ℕ) :
    zeroBlock N n = (↑(Finset.Ico N (N + n)) : Set ℕ).pi (fun _ => ({false} : Set Bool)) := by
  ext w; simp [zeroBlock]

/-- **`Statement:` if `p ≤ 1`, a zero block of length `n` has measure `(1 - p) ^ n`.** -/
theorem trials_zeroBlock (p : NNReal) (hp : p ≤ 1) (N n : ℕ) :
    trials p hp (zeroBlock N n) = ((1 - p : NNReal) : ENNReal) ^ n := by
  rw [zeroBlock_eq_pi, trials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton false)]
  simp [PMF.bernoulli]

/-- **`Statement:` if `0 < p`, some `K > 0` has `(1 - p) ^ K ≤ 1/2`.** Existential: `K` is not
computed from `p` here. -/
theorem exists_halving_block (p : NNReal) (hp0 : 0 < p) :
    ∃ K : ℕ, 0 < K ∧ ((1 - p : NNReal) : ENNReal) ^ K ≤ 2⁻¹ := by
  have hlt : ((1 - p : NNReal) : ENNReal) < 1 := by
    have : (1 - p : NNReal) < 1 := tsub_lt_self one_pos hp0
    exact_mod_cast this
  have ht := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ENNReal) < 2⁻¹ by simp))).and
    (eventually_gt_atTop 0)
  obtain ⟨K, hK, hK0⟩ := hev.exists
  exact ⟨K, hK0, hK.le⟩

/-- **`Statement:` if `(1 - p) ^ K ≤ 1/2`, the zero block of length `K * m` has measure at most
`2⁻ᵐ`.** -/
theorem trials_zeroBlock_le (p : NNReal) (hp : p ≤ 1) {K : ℕ}
    (hK : ((1 - p : NNReal) : ENNReal) ^ K ≤ 2⁻¹) (N m : ℕ) :
    trials p hp (zeroBlock N (K * m)) ≤ 2⁻¹ ^ m := by
  rw [trials_zeroBlock, pow_mul]
  exact pow_le_pow_left₀ (zero_le _) hK m

/-- **`Statement:` the tapes that fire at no stage from `N` on.** `silentFrom 0` never fires. -/
def silentFrom (N : ℕ) : Set (ℕ → Bool) := {w | ∀ k, N ≤ k → w k = false}

/-- **`Statement:` if `0 < K`, `silentFrom N` is the intersection over `m` of the zero blocks of
length `K * m` from `N`.** -/
theorem silentFrom_eq_iInter (N : ℕ) {K : ℕ} (hK : 0 < K) :
    silentFrom N = ⋂ m, zeroBlock N (K * m) := by
  ext w
  simp only [silentFrom, zeroBlock, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_Ico]
  constructor
  · intro h m k hk; exact h k hk.1
  · intro h k hk
    exact h (k + 1) k ⟨hk, by nlinarith⟩

/-- **`Statement:` a tape fails to fire infinitely often iff it is silent from some `N`; both
directions.** -/
theorem not_mem_limsup_fires_iff (w : ℕ → Bool) :
    w ∉ Filter.limsup fires Filter.atTop ↔ ∃ N, w ∈ silentFrom N := by
  rw [mem_limsup_iff_frequently_mem, Filter.not_frequently, Filter.eventually_atTop]
  simp [fires, silentFrom]

/-! ## § VI. Typicality as an explicit hypothesis -/

/-- **`Statement:` `U` is a zero-block test for `μ`: level `m` has `μ`-measure at most `2⁻ᵐ`, and
level `m` is the zero block `zeroBlock (w m).1 (w m).2` for a primitive recursive `w`.** -/
def ZeroBlockTest (μ : Measure (ℕ → Bool)) (U : ℕ → Set (ℕ → Bool)) : Prop :=
  (∀ m, μ (U m) ≤ 2⁻¹ ^ m) ∧
    ∃ w : ℕ → ℕ × ℕ, Primrec w ∧ ∀ m, U m = zeroBlock (w m).1 (w m).2

/-- **`Statement:` `w` lies outside `⋂ m, U m` for every `U` in the class `𝒯`.** A predicate on a
tape, used only as a hypothesis. -/
def AvoidsTests (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (w : ℕ → Bool) : Prop :=
  ∀ U, 𝒯 U → w ∉ ⋂ m, U m

/-- **`Statement:` if `p ≤ 1` and `0 < p`, then for every `N` some zero-block test for
`trials p hp` has intersection `silentFrom N`.** -/
theorem zeroBlockTest_silentFrom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (N : ℕ) :
    ∃ U, ZeroBlockTest (trials p hp) U ∧ ⋂ m, U m = silentFrom N := by
  obtain ⟨K, hK0, hK⟩ := exists_halving_block p hp0
  refine ⟨fun m => zeroBlock N (K * m), ⟨fun m => trials_zeroBlock_le p hp hK N m,
    fun m => (N, K * m), ?_, fun m => rfl⟩, (silentFrom_eq_iInter N hK0).symm⟩
  exact Primrec.pair (Primrec.const N) (Primrec.nat_mul.comp (Primrec.const K) Primrec.id)

/-- **`Statement:` if `p ≤ 1`, `0 < p`, the class `𝒯` contains every zero-block test for
`trials p hp`, and `w` avoids `𝒯`, then `w` fires infinitely often.** One way: the squares tape
below fires infinitely often, and at every `0 < p ≤ 1` is caught by a zero-block test
(`squaresTape_not_avoids`). `Reading:` `htyp` is the typicality commitment written as a hypothesis
on one tape. -/
theorem fires_io_of_avoids (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p)
    (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (h𝒯 : ∀ U, ZeroBlockTest (trials p hp) U → 𝒯 U)
    (w : ℕ → Bool) (htyp : AvoidsTests 𝒯 w) :
    w ∈ Filter.limsup fires Filter.atTop := by
  by_contra h
  obtain ⟨N, hN⟩ := (not_mem_limsup_fires_iff w).1 h
  obtain ⟨U, hU, hUeq⟩ := zeroBlockTest_silentFrom p hp hp0 N
  exact htyp U (h𝒯 U hU) (hUeq ▸ hN)

/-- **`Statement:` the tape that is `true` exactly at the perfect squares.** -/
def squaresTape (k : ℕ) : Bool := decide (Nat.sqrt k * Nat.sqrt k = k)

/-- **`Statement:` if `p ≤ 1`, `0 < p`, and the class `𝒯` contains every zero-block test for
`trials p hp`, then the squares tape does not avoid `𝒯`.** Level `m` is the first `K * m`
non-squares after `(K * m)²`, with `K` from `exists_halving_block`; `p = 1` is included. -/
theorem squaresTape_not_avoids (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p)
    (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (h𝒯 : ∀ U, ZeroBlockTest (trials p hp) U → 𝒯 U) :
    ¬ AvoidsTests 𝒯 squaresTape := by
  obtain ⟨K, -, hK⟩ := exists_halving_block p hp0
  intro h
  refine h (fun m => zeroBlock (K * m * (K * m) + 1) (K * m))
    (h𝒯 _ ⟨fun m => trials_zeroBlock_le p hp hK _ m, fun m => (K * m * (K * m) + 1, K * m), ?_,
      fun m => rfl⟩) ?_
  · have hKm : Primrec (fun m : ℕ => K * m) := Primrec.nat_mul.comp (Primrec.const K) Primrec.id
    exact Primrec.pair (Primrec.succ.comp (Primrec.nat_mul.comp hKm hKm)) hKm
  · simp only [Set.mem_iInter, zeroBlock, Set.mem_setOf_eq, Finset.mem_Ico]
    intro m k hk
    have hs : Nat.sqrt k = K * m := by
      obtain ⟨j, rfl⟩ : ∃ j, k = K * m * (K * m) + j := ⟨k - K * m * (K * m), by omega⟩
      exact Nat.sqrt_add_eq (K * m) (by omega)
    simp only [squaresTape, hs, decide_eq_false_iff_not]
    omega

/-- **`Statement:` the tapes that fire at every stage in `[0, n)`.** -/
def oneBlock (n : ℕ) : Set (ℕ → Bool) := {w | ∀ k ∈ Finset.range n, w k = true}

/-- **`Statement:` if `p ≤ 1`, a one block of length `n` has measure `p ^ n`.** -/
theorem trials_oneBlock (p : NNReal) (hp : p ≤ 1) (n : ℕ) :
    trials p hp (oneBlock n) = (p : ENNReal) ^ n := by
  have : oneBlock n = (↑(Finset.range n) : Set ℕ).pi (fun _ => ({true} : Set Bool)) := by
    ext w; simp [oneBlock]
  rw [this, trials, Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton true)]
  simp [PMF.bernoulli]

-- Statement: CONTROL, the converse of `fires_io_of_avoids` fails inside the zero-block class: at
-- `p = 1/2` the squares tape fires infinitely often and lies in a zero-block test's intersection
-- (level `m` the first `m` non-squares after `m * m`; every `0 < p ≤ 1`: `squaresTape_not_avoids`).
example : squaresTape ∈ Filter.limsup fires Filter.atTop ∧
    ¬ AvoidsTests (ZeroBlockTest (trials (1/2) (by norm_num))) squaresTape := by
  have half : (1 - (1/2 : NNReal) : NNReal) = 2⁻¹ := by
    rw [one_div]; exact tsub_eq_of_eq_add (by rw [← two_mul, mul_inv_cancel₀ two_ne_zero])
  refine ⟨?_, fun h => ?_⟩
  · rw [mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
    intro a
    exact ⟨a * a, Nat.le_mul_self a, by simp [fires, squaresTape]⟩
  · refine h (fun m => zeroBlock (m * m + 1) m)
      ⟨fun m => ?_, fun m => (m * m + 1, m), ?_, fun m => rfl⟩ ?_
    · have := trials_zeroBlock_le (1/2) (by norm_num) (K := 1) (by rw [half]; simp) (m * m + 1) m
      simpa using this
    · exact Primrec.pair (Primrec.succ.comp (Primrec.nat_mul.comp Primrec.id Primrec.id)) Primrec.id
    · simp only [Set.mem_iInter, zeroBlock, Set.mem_setOf_eq, Finset.mem_Ico]
      intro m k hk
      have hs : Nat.sqrt k = m := by
        obtain ⟨j, rfl⟩ : ∃ j, k = m * m + j := ⟨k - m * m, by omega⟩
        exact Nat.sqrt_add_eq m (by omega)
      simp only [squaresTape, hs, decide_eq_false_iff_not]
      omega

-- Statement: CONTROL, firing infinitely often is not typicality against a class holding one-block
-- tests: the all-`true` tape fires infinitely often and lies in every one block, whose measures at
-- `p = 1/2` are at most `2⁻ᵐ`.
example : (fun _ => true : ℕ → Bool) ∈ Filter.limsup fires Filter.atTop ∧
    (fun _ => true : ℕ → Bool) ∈ ⋂ m, oneBlock m ∧
    ∀ m, trials (1/2) (by norm_num) (oneBlock m) ≤ 2⁻¹ ^ m := by
  refine ⟨?_, ?_, fun m => ?_⟩
  · rw [mem_limsup_iff_frequently_mem]; exact Filter.Frequently.of_forall (fun n => rfl)
  · simp [oneBlock]
  · rw [trials_oneBlock]; simp

-- Statement: the zero-block hypothesis is weak: for every `p ≤ 1` the all-`true` tape, a constant
-- tape, avoids the class of zero-block tests for `trials p hp` (level 1 of a test has measure at
-- most `1/2`, so its window has positive length, and the all-`true` tape lies in no zero block over a
-- window of positive length).
-- Reading (cited, not claimed): so meeting this hypothesis does not give Kurtz randomness at
-- `p = 1/2`: the all-`true` tape is computable, and no computable sequence is Kurtz random for the
-- fair coin (Freer, `algorithmic-randomness`, `ComputableCantorPoint.not_isKurtzRandom`). Reading
-- it as "not Martin-Löf random" needs `p < 1`, since the cited result (Reimann and Slaman, Thm 4.4)
-- concerns non-atoms. Both sources: `ZeroParadox/Information/CrossingTrials.md`.
example (p : NNReal) (hp : p ≤ 1) :
    AvoidsTests (ZeroBlockTest (trials p hp)) (fun _ => true) := by
  rintro U ⟨hμ, f, -, hf⟩ hmem
  have h1 := hμ 1
  rw [hf 1] at h1
  have hm : (fun _ => true : ℕ → Bool) ∈ zeroBlock (f 1).1 (f 1).2 := by
    rw [← hf 1]; exact Set.mem_iInter.1 hmem 1
  rcases Nat.eq_zero_or_pos (f 1).2 with h0 | hpos
  · have : zeroBlock (f 1).1 (f 1).2 = Set.univ := by
      ext w; simp [zeroBlock, h0]
    rw [this, measure_univ] at h1
    norm_num at h1
  · have := hm (f 1).1 (by simp [Finset.mem_Ico]; omega)
    simp at this

/-! ## § VII. The slot machine as a die motion -/

/-- **`Statement:` the motion on `Bool` with UP the identity and OVER: every point steps to itself,
and `false` steps to `true`.** `Reading:` `false` is not yet crossed, `true` crossed. -/
def slotMotion : Motion Bool :=
  Motion.ofTotal id (fun _ => rfl) (fun a b => a = b ∨ (a = false ∧ b = true))

/-- **`Statement:` the stage-`n` state driven by `w`: `true` iff `w` fires below stage `n`.** -/
def slotRun (w : ℕ → Bool) (n : ℕ) : Bool := decide (∃ k < n, w k = true)

/-- **`Statement:` for every tape `w`, `slotRun w` is a run of `slotMotion`.** -/
theorem slotRun_isRun (w : ℕ → Bool) : slotMotion.IsRun (slotRun w) := by
  intro n
  show slotRun w n = slotRun w (n + 1) ∨ (slotRun w n = false ∧ slotRun w (n + 1) = true)
  by_cases h : ∃ k < n, w k = true
  · left
    have h' : ∃ k < n + 1, w k = true := let ⟨k, hk, e⟩ := h; ⟨k, by omega, e⟩
    simp only [slotRun, h, h', decide_true]
  · by_cases hn : w n = true
    · right
      have h' : ∃ k < n + 1, w k = true := ⟨n, by omega, hn⟩
      simp only [slotRun, h, h', decide_true, decide_false, and_self]
    · left
      have h' : ¬ ∃ k < n + 1, w k = true := by
        rintro ⟨k, hk, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact h ⟨k, hk, e⟩
        · exact hn e
      simp only [slotRun, h, h']

/-- **`Statement:` in `slotMotion`, `false` steps elsewhere (`LeavesAt`) and steps to itself.**
`Reading:` the possibility of crossing, with no measure and no tape. -/
theorem slotMotion_leavesAt_false : slotMotion.LeavesAt false ∧ slotMotion.step false false :=
  ⟨⟨true, Or.inr ⟨rfl, rfl⟩, by decide⟩, Or.inl rfl⟩

/-- **`Statement:` in `slotMotion`, `true` steps to itself and to nothing else (`SelfOnlyAt`).** -/
theorem slotMotion_selfOnlyAt_true : slotMotion.SelfOnlyAt true :=
  ⟨Or.inl rfl, fun _ h => h.elim Eq.symm (fun h => absurd h.1 (by decide))⟩

/-- **`Statement:` `slotRun w` starts at `false`, and reaches `true` iff `w` fires at some stage;
both directions.** -/
theorem slotRun_crosses_iff (w : ℕ → Bool) :
    slotRun w 0 = false ∧ ((∃ n, slotRun w n = true) ↔ ∃ k, w k = true) := by
  refine ⟨by simp [slotRun], ⟨fun ⟨n, hn⟩ => ?_, fun ⟨k, e⟩ => ⟨k + 1, ?_⟩⟩⟩
  · simp only [slotRun, decide_eq_true_eq] at hn
    obtain ⟨k, -, e⟩ := hn; exact ⟨k, e⟩
  · simp only [slotRun, decide_eq_true_eq]; exact ⟨k, by omega, e⟩

/-- **`Statement:` if `p ≤ 1`, `0 < p`, `𝒯` contains every zero-block test for `trials p hp`, `w`
avoids `𝒯`, and `φ` is a one-to-one lax map from `slotMotion` to `N`, then `φ ∘ slotRun w` is a
run of `N` that reaches a state other than its start.** One way: the `example` after it gives the
departure for any tape that fires once (the run half needs no hypothesis on the tape). Without
`htyp` the all-`false` tape's run never leaves `false`. -/
theorem slotRun_image_departs_of_avoids {β : Type*} {N : Motion β}
    (φ : Motion.LaxHom slotMotion N) (hi : Function.Injective φ.toFun)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p)
    (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (h𝒯 : ∀ U, ZeroBlockTest (trials p hp) U → 𝒯 U)
    (w : ℕ → Bool) (htyp : AvoidsTests 𝒯 w) :
    N.IsRun (φ.toFun ∘ slotRun w) ∧ ∃ n, (φ.toFun ∘ slotRun w) n ≠ (φ.toFun ∘ slotRun w) 0 := by
  refine ⟨fun n => φ.map_step (slotRun_isRun w n), ?_⟩
  have h := fires_io_of_avoids p hp hp0 𝒯 h𝒯 w htyp
  rw [mem_limsup_iff_frequently_mem] at h
  obtain ⟨k, -, hk⟩ := h.forall_exists_of_atTop 0
  obtain ⟨n, hn⟩ := (slotRun_crosses_iff w).2.2 ⟨k, hk⟩
  exact ⟨n, fun e => by
    have := hi e; rw [hn, (slotRun_crosses_iff w).1] at this; cases this⟩

-- Statement: if `φ` is a one-to-one lax map and `w` fires at some stage, the image run leaves its
-- start, with no measure and no typicality hypothesis.
example {β : Type*} {N : Motion β} (φ : Motion.LaxHom slotMotion N)
    (hi : Function.Injective φ.toFun) (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    ∃ n, (φ.toFun ∘ slotRun w) n ≠ (φ.toFun ∘ slotRun w) 0 := by
  obtain ⟨n, hn⟩ := (slotRun_crosses_iff w).2.2 hw
  exact ⟨n, fun e => by have := hi e; rw [hn, (slotRun_crosses_iff w).1] at this; cases this⟩

-- Statement: CONTROL, the converse of `slotRun_image_departs_of_avoids` fails: for every one-to-one
-- lax map `φ`, every `0 < p ≤ 1` and every class `𝒯` holding the zero-block tests for
-- `trials p hp`, the squares tape's image run leaves its start, yet the squares tape does not avoid
-- `𝒯` (`squaresTape_not_avoids`).
example {β : Type*} {N : Motion β} (φ : Motion.LaxHom slotMotion N)
    (hi : Function.Injective φ.toFun) (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p)
    (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (h𝒯 : ∀ U, ZeroBlockTest (trials p hp) U → 𝒯 U) :
    (∃ n, (φ.toFun ∘ slotRun squaresTape) n ≠ (φ.toFun ∘ slotRun squaresTape) 0) ∧
    ¬ AvoidsTests 𝒯 squaresTape := by
  refine ⟨?_, squaresTape_not_avoids p hp hp0 𝒯 h𝒯⟩
  obtain ⟨n, hn⟩ := (slotRun_crosses_iff squaresTape).2.2 ⟨0, by simp [squaresTape]⟩
  exact ⟨n, fun e => by
    have := hi e; rw [hn, (slotRun_crosses_iff squaresTape).1] at this; cases this⟩

-- Statement: CONTROL: without the typicality hypothesis, the all-`false` tape drives a run that
-- stays at `false` at every stage.
example : ∀ n, slotRun (fun _ => false) n = false := fun n => by simp [slotRun]

/-! ## § VIII. Fired at least once gives `t_snap_given`'s hypotheses

Direction: a tape that has fired at least once gives a state sequence meeting `t_snap_given`'s
`hcc1` and `hocc`; the cover `hcov` of `t_snap_given_cover` is not supplied. "Fired at least once"
holds on a set of `trials p hp` measure one when `0 < p ≤ 1` (`trials_fires_once`) and for every
tape meeting § VI's hypotheses (`t_snap_of_avoids`); neither statement names a tape. -/

/-- **`Statement:` `slotRun w` with the stages before the first firing dropped.** `Nat.find hw` is
the least `k` with `w k = true`, a first hitting time (Mathlib: `MeasureTheory.hittingAfter`). -/
def firedRun (w : ℕ → Bool) (hw : ∃ k, w k = true) (n : ℕ) : Bool :=
  slotRun w (Nat.find hw + n)

-- Statement: if `w` fires at some stage, `Nat.find hw` is Mathlib's `hittingAfter` of the coordinate
-- process at `{true}` from time 0.
example (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    MeasureTheory.hittingAfter (fun (j : ℕ) (x : ℕ → Bool) => x j) {true} 0 w =
      (Nat.find hw : WithTop ℕ) := by
  rw [MeasureTheory.hittingAfter_def]
  have : ∃ j, 0 ≤ j ∧ w j ∈ ({true} : Set Bool) := by
    obtain ⟨k, hk⟩ := hw; exact ⟨k, Nat.zero_le _, hk⟩
  simp only [this, if_true]
  congr 1
  apply le_antisymm
  · exact Nat.sInf_le ⟨Nat.zero_le _, Nat.find_spec hw⟩
  · apply le_csInf
    · obtain ⟨k, hk⟩ := hw; exact ⟨k, Nat.zero_le _, hk⟩
    · rintro b ⟨-, hb⟩; exact Nat.find_min' hw hb

/-- **`Statement:` if `w` fires at some stage, `firedRun w hw` is `false` at stage 0 and `true` at
every later stage.** -/
theorem firedRun_spec (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    firedRun w hw 0 = false ∧ ∀ n, firedRun w hw (n + 1) = true := by
  refine ⟨?_, fun n => ?_⟩
  · simp only [firedRun, slotRun, Nat.add_zero, decide_eq_false_iff_not]
    rintro ⟨k, hk, e⟩
    exact Nat.find_min hw hk e
  · simp only [firedRun, slotRun, decide_eq_true_eq]
    exact ⟨Nat.find hw, by omega, Nat.find_spec hw⟩

/-- **`Statement:` if `w` fires at some stage, `firedRun w hw` is a run of `slotMotion`.** A shift of
the run `slotRun w` (`slotRun_isRun`). -/
theorem firedRun_isRun (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    slotMotion.IsRun (firedRun w hw) := fun n =>
  slotRun_isRun w (Nat.find hw + n)

/-- **`Statement:` if `φ : Bool → L` sends `false` to ⊥ of `L` and `true` to a point other than ⊥ of
`L`, and the tape `w` fires at some stage (`hw`), then `S := φ ∘ firedRun w hw` has `S 0 = ⊥` (CC-1,
`t_snap_given`'s `hcc1`), `S 1 ≠ S 0` (`t_snap_given`'s `hocc`), is a state sequence (ZP-A's D3), and
carries `t_snap_given`'s triple.** One way: having fired at least once gives the hypotheses; the
converse is not claimed. Every firing tape gives the same `firedRun w hw`, `false` at stage 0 and `true` after
(`firedRun_spec`): the tape contributes one bit, that it fired. `S` steps once, at index 1, and
stays, so it is not an `IsStrictStateSequence` (the last `example` of the file). Without `hw` the
all-`false` tape's run `φ ∘ slotRun` stays at ⊥ of `L` at every stage (the first `example` below).
`Reading:` `hw` is the occurrence commitment in its slot chart, written as one hypothesis on the
realized tape; it is a hypothesis here, never a field of a structure. -/
theorem t_snap_of_fires_once {L : Type*} [ZPSemilattice L] (φ : Bool → L)
    (hφ0 : φ false = ZPSemilattice.bot) (hφ1 : φ true ≠ ZPSemilattice.bot)
    (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    let S := φ ∘ firedRun w hw
    S 0 = ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧ ZPSemilattice.IsStateSequence S ∧
      (S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ ZPSemilattice.join (S 0) (S 1) = S 1) := by
  intro S
  obtain ⟨h0, hs⟩ := firedRun_spec w hw
  have hS0 : S 0 = ZPSemilattice.bot := by simp [S, h0, hφ0]
  have hS1 : S 1 ≠ S 0 := by
    simp only [S, Function.comp, hs 0, h0, hφ0]; exact hφ1
  refine ⟨hS0, hS1, ⟨fun _ => φ true, fun n => ?_⟩, t_snap_given S hS0 hS1⟩
  cases n with
  | zero => simp only [S, Function.comp, hs 0, h0, hφ0]; exact (ZPSemilattice.bot_join _).symm
  | succ n => simp only [S, Function.comp, hs]; exact (ZPSemilattice.join_idem _).symm

/-- **`Statement:` if `p ≤ 1` and `0 < p`, the tapes that fire at some stage have `trials p hp`
measure one.** They contain the tapes that fire infinitely often, a set of measure one
(`crossing_almost_surely`). The conclusion is about a set of tapes and names no tape. -/
theorem trials_fires_once (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp {w | ∃ k, w k = true} = 1 := by
  refine le_antisymm prob_le_one ?_
  rw [← crossing_almost_surely p hp hp0]
  refine measure_mono fun w hw => ?_
  rw [mem_limsup_iff_frequently_mem] at hw
  obtain ⟨k, -, hk⟩ := hw.forall_exists_of_atTop 0
  exact ⟨k, hk⟩

/-- **`Statement:` if `p ≤ 1`, `0 < p`, `𝒯` contains every zero-block test for `trials p hp`, `w`
avoids `𝒯`, and `φ` is as in `t_snap_of_fires_once`, then `w` fires at some stage and
`t_snap_of_fires_once`'s conclusion holds for it.** From `fires_io_of_avoids`. One way: the squares
tape fires at stage 0 and does not avoid `𝒯` (the fourth CONTROL `example` below), so § VI's
hypotheses are sufficient for `hw`, not necessary. `Reading:` `htyp`, like `hw`, is a hypothesis on
one tape. -/
theorem t_snap_of_avoids {L : Type*} [ZPSemilattice L] (φ : Bool → L)
    (hφ0 : φ false = ZPSemilattice.bot) (hφ1 : φ true ≠ ZPSemilattice.bot)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p)
    (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (h𝒯 : ∀ U, ZeroBlockTest (trials p hp) U → 𝒯 U)
    (w : ℕ → Bool) (htyp : AvoidsTests 𝒯 w) :
    ∃ hw : ∃ k, w k = true,
      let S := φ ∘ firedRun w hw
      S 0 = ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧ ZPSemilattice.IsStateSequence S ∧
        (S 0 ≠ S 1 ∧ S 1 ≠ S 0 ∧ ZPSemilattice.join (S 0) (S 1) = S 1) := by
  have h := fires_io_of_avoids p hp hp0 𝒯 h𝒯 w htyp
  rw [mem_limsup_iff_frequently_mem] at h
  obtain ⟨k, -, hk⟩ := h.forall_exists_of_atTop 0
  exact ⟨⟨k, hk⟩, t_snap_of_fires_once φ hφ0 hφ1 w ⟨k, hk⟩⟩

-- Statement: CONTROL, the tape-driven run needs `hw`: the all-`false` tape fires at no stage, and for any `φ`
-- with `φ false = ⊥` the sequence `φ ∘ slotRun` it drives starts at ⊥ of `L` and never steps.
example {L : Type*} [ZPSemilattice L] (φ : Bool → L) (hφ0 : φ false = ZPSemilattice.bot) :
    (¬ ∃ k, (fun _ => false : ℕ → Bool) k = true) ∧
    (φ ∘ slotRun (fun _ => false)) 0 = ZPSemilattice.bot ∧
    ∀ n, (φ ∘ slotRun (fun _ => false)) n = (φ ∘ slotRun (fun _ => false)) 0 :=
  ⟨fun ⟨_, h⟩ => Bool.false_ne_true h, by simp [slotRun, hφ0], fun n => by simp [slotRun]⟩

-- Statement: CONTROL, the shift is needed for `hocc` at index 1: the tape firing only at stage 1
-- drives `φ ∘ slotRun` with `S 1 = S 0`.
example {L : Type*} [ZPSemilattice L] (φ : Bool → L) :
    (φ ∘ slotRun (fun k => decide (k = 1))) 1 = (φ ∘ slotRun (fun k => decide (k = 1))) 0 := by
  simp [slotRun]

-- Statement: CONTROL, `Unit`: it carries a `ZPSemilattice` (as `trivialZPSemilattice`,
-- `ZeroParadox/Valuation/Scale.lean`), and under any such instance no `φ : Bool → Unit` has
-- `φ true ≠ ⊥`, so `hφ1` has no member.
example : Nonempty (ZPSemilattice Unit) :=
  ⟨⟨fun _ _ => (), (), fun _ _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩⟩
example [ZPSemilattice Unit] (φ : Bool → Unit) : ¬ φ true ≠ ZPSemilattice.bot := fun h => h rfl

-- Statement: CONTROL, fired at least once does not imply typical: for every `0 < p ≤ 1` and every
-- class `𝒯` holding the zero-block tests for `trials p hp`, the squares tape fires at stage 0 and
-- does not avoid `𝒯`.
example (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p)
    (𝒯 : (ℕ → Set (ℕ → Bool)) → Prop) (h𝒯 : ∀ U, ZeroBlockTest (trials p hp) U → 𝒯 U) :
    (∃ k, squaresTape k = true) ∧ ¬ AvoidsTests 𝒯 squaresTape :=
  ⟨⟨0, by simp [squaresTape]⟩, squaresTape_not_avoids p hp hp0 𝒯 h𝒯⟩

-- Statement: CONTROL, measure one is not every tape: if `0 < p ≤ 1`, the set of tapes that fired at
-- least once has measure one and the all-`false` tape is not in it.
example (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) :
    trials p hp {w | ∃ k, w k = true} = 1 ∧ ¬ ∀ w : ℕ → Bool, ∃ k, w k = true :=
  ⟨trials_fires_once p hp hp0, fun h => by obtain ⟨k, hk⟩ := h (fun _ => false); simp at hk⟩

-- Statement: occurrence once: under `t_snap_of_fires_once`'s hypotheses, `S := φ ∘ firedRun w hw`
-- has `S 2 = S 1`, so `S` is not an `IsStrictStateSequence` (ZP-A's proper ascent at every step).
example {L : Type*} [ZPSemilattice L] (φ : Bool → L) (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    ¬ ZPSemilattice.IsStrictStateSequence (φ ∘ firedRun w hw) := fun h => by
  have a : firedRun w hw 1 = true := (firedRun_spec w hw).2 0
  have b : firedRun w hw 2 = true := (firedRun_spec w hw).2 1
  exact h.2 1 (show φ (firedRun w hw 1) = φ (firedRun w hw 2) by rw [a, b])

/-! ## § IX. Fired at least once is open, and no continuous test decides it

Topology: the product (Cantor) topology on `ℕ → Bool`, with `Bool` discrete. Direction: a test
`f : (ℕ → Bool) → Bool` is continuous iff one prefix length `N` fixes its value on every tape
(both directions below); "fired at least once" is open and not closed, and no continuous test
decides it. That computable implies continuous is cited, not proved here: Weihrauch, *Computable
Analysis* (Springer 2000), Thm 2.2.3, p. 30. Mathlib's `Computable` takes `Primcodable` types, and
`ℕ → Bool` carries none (the first `example` below). Prior art, the search and the footprints:
`ZeroParadox/Information/CrossingTrials.md`. -/

-- Statement: `ℕ → Bool` has no `Primcodable` instance (diagonal argument), so Mathlib's `Computable`
-- does not apply to tests on tapes.
example : IsEmpty (Primcodable (ℕ → Bool)) :=
  ⟨fun h => by
    haveI := h.toEncodable
    obtain ⟨f, hf⟩ := exists_surjective_nat (ℕ → Bool)
    obtain ⟨m, hm⟩ := hf fun n => !(f n n)
    have := congrFun hm m
    cases h' : f m m <;> simp [h'] at this⟩

/-- **`Statement:` if `f : (ℕ → Bool) → Bool` is continuous, one `N` has: tapes agreeing below `N`
get the same value.** By compactness of `ℕ → Bool`; the Baire-space `example` below shows
continuity alone does not give the uniform `N`. -/
theorem prefixDetermined_of_continuous (f : (ℕ → Bool) → Bool) (hf : Continuous f) :
    ∃ N, ∀ w w' : ℕ → Bool, (∀ i < N, w i = w' i) → f w = f w' := by
  have hn : ∀ w : ℕ → Bool, ∃ n, PiNat.cylinder w n ⊆ f ⁻¹' {f w} := by
    intro w
    obtain ⟨_, ⟨x, n, rfl⟩, hw, hsub⟩ :=
      (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open
        (show w ∈ f ⁻¹' {f w} from rfl) ((isOpen_discrete _).preimage hf)
    exact ⟨n, (PiNat.mem_cylinder_iff_eq.1 hw) ▸ hsub⟩
  choose n hn using hn
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun w => PiNat.cylinder w (n w))
    (fun w _ => (PiNat.isOpen_cylinder (fun _ : ℕ => Bool) w (n w)).mem_nhds
      (PiNat.self_mem_cylinder _ _))
  refine ⟨t.sup n, fun w w' hww' => ?_⟩
  obtain ⟨x, hx, hwx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ w))
  have hle : n x ≤ t.sup n := Finset.le_sup hx
  have hw'x : w' ∈ PiNat.cylinder x (n x) := fun i hi =>
    (hww' i (hi.trans_le hle)).symm.trans (hwx i hi)
  have e1 : f w = f x := hn x hwx
  have e2 : f w' = f x := hn x hw'x
  rw [e1, e2]

/-- **`Statement:` the converse: if one `N` fixes `f`'s value on tapes agreeing below `N`, `f` is
continuous.** -/
theorem continuous_of_prefixDetermined (f : (ℕ → Bool) → Bool)
    (h : ∃ N, ∀ w w' : ℕ → Bool, (∀ i < N, w i = w' i) → f w = f w') : Continuous f := by
  obtain ⟨N, hN⟩ := h
  let ext : (Fin N → Bool) → ℕ → Bool := fun v i => if hi : i < N then v ⟨i, hi⟩ else false
  let r : (ℕ → Bool) → Fin N → Bool := fun w i => w i
  have hr : Continuous r := continuous_pi fun i => continuous_apply _
  have hf : f = (f ∘ ext) ∘ r := by
    funext w
    exact hN w _ (fun i hi => by simp [ext, r, hi])
  rw [hf]
  exact continuous_of_discreteTopology.comp hr

/-- **`Statement:` the tapes that fired at least once form an open set.** The set is
`trials_fires_once`'s; it is not closed (the never-fired CONTROL `example`). -/
theorem isOpen_fires_once : IsOpen {w : ℕ → Bool | ∃ k, w k = true} := by
  have : {w : ℕ → Bool | ∃ k, w k = true} = ⋃ k, (fun w : ℕ → Bool => w k) ⁻¹' {true} := by
    ext w; simp
  rw [this]
  exact isOpen_iUnion fun k => (isOpen_discrete _).preimage (continuous_apply k)

/-- **`Statement:` if `f w = true ↔ ∃ k, w k = true` for every tape `w`, then `f` is not continuous
at ⊥ of `ℕ → Bool` (pointwise order), the all-`false` tape.** Every prefix of ⊥ is also a prefix of
a tape that fires one stage later. -/
theorem not_continuousAt_bot_of_decides_fires_once (f : (ℕ → Bool) → Bool)
    (hf : ∀ w, f w = true ↔ ∃ k, w k = true) : ¬ ContinuousAt f ⊥ := by
  intro hc
  have hbot : f ⊥ = false := by
    cases h : f ⊥
    · rfl
    · obtain ⟨k, hk⟩ := (hf _).1 h; cases hk
  have hmem : f ⁻¹' {f ⊥} ∈ nhds (⊥ : ℕ → Bool) := hc ((isOpen_discrete _).mem_nhds rfl)
  obtain ⟨_, ⟨x, n, rfl⟩, hb, hsub⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).mem_nhds_iff.1 hmem
  have hw : (fun k => decide (k = n)) ∈ PiNat.cylinder x n := by
    rw [← PiNat.mem_cylinder_iff_eq.1 hb]
    intro i hi; simp [Nat.ne_of_lt hi]
  have h1 : f (fun k => decide (k = n)) = f ⊥ := hsub hw
  rw [hbot] at h1
  have h2 : f (fun k => decide (k = n)) = true := (hf _).2 ⟨n, by simp⟩
  rw [h1] at h2; cases h2

/-- **`Statement:` no continuous `f : (ℕ → Bool) → Bool` has `f w = true ↔ ∃ k, w k = true` for
every tape `w`.** `Reading:` `hw` in `t_snap_of_fires_once` is one tape's instance of the
predicate decided here by no continuous test (`CrossingTrials.md` § IX). -/
theorem no_continuous_test_fires_once :
    ¬ ∃ f : (ℕ → Bool) → Bool, Continuous f ∧ ∀ w, f w = true ↔ ∃ k, w k = true :=
  fun ⟨f, hc, hf⟩ => not_continuousAt_bot_of_decides_fires_once f hf hc.continuousAt

/-- **`Statement:` "some test on `ℕ → Bool` is continuous", bare: the statement control for § IX,
whose statements all mention `Continuous` or `IsOpen` on this space.** -/
def ContinuousTestStatement : Prop := ∃ f : (ℕ → Bool) → Bool, Continuous f

-- Statement: CONTROL, fired at stage 0 is decided by a one-bit prefix: `w ↦ w 0` is continuous.
example : Continuous fun w : ℕ → Bool => w 0 := continuous_apply 0

-- Statement: CONTROL, the complement, never fired, is closed and not open.
example : IsClosed {w : ℕ → Bool | ∀ k, w k = false} ∧
    ¬ IsOpen {w : ℕ → Bool | ∀ k, w k = false} := by
  have hc : {w : ℕ → Bool | ∀ k, w k = false} = {w | ∃ k, w k = true}ᶜ := by
    ext w; simp
  refine ⟨hc ▸ isOpen_fires_once.isClosed_compl, fun ho => ?_⟩
  obtain ⟨_, ⟨x, n, rfl⟩, hb, hsub⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).mem_nhds_iff.1
      (ho.mem_nhds (show (⊥ : ℕ → Bool) ∈ {w : ℕ → Bool | ∀ k, w k = false} from fun _ => rfl))
  have hw : (fun k => decide (k = n)) ∈ PiNat.cylinder x n := by
    rw [← PiNat.mem_cylinder_iff_eq.1 hb]
    intro i hi; simp [Nat.ne_of_lt hi]
  have := hsub hw n
  simp at this

-- Statement: CONTROL, the theorem is about continuity, not definability: classically, a Boolean
-- function on `ℕ → Bool` that is not continuous exists.
example : ∃ f : (ℕ → Bool) → Bool, ¬ Continuous f := by
  classical
  exact ⟨fun w => decide (∃ k, w k = true), fun hc =>
    no_continuous_test_fires_once ⟨_, hc, fun w => by simp⟩⟩

-- Statement: CONTROL, continuity alone does not give the uniform `N`: on `ℕ → ℕ`, `w ↦ (w (w 0) = 0)` is
-- continuous and no single prefix length fixes its value.
example : ∃ f : (ℕ → ℕ) → Bool, Continuous f ∧
    ¬ ∃ N, ∀ w w' : ℕ → ℕ, (∀ i < N, w i = w' i) → f w = f w' := by
  refine ⟨fun w => decide (w (w 0) = 0), ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    have hmem : PiNat.cylinder w (w 0 + 1) ∈ nhds w :=
      (PiNat.isOpen_cylinder (fun _ : ℕ => ℕ) w _).mem_nhds (PiNat.self_mem_cylinder _ _)
    rw [ContinuousAt, nhds_discrete Bool, Filter.tendsto_pure]
    refine Filter.mem_of_superset hmem fun y hy => ?_
    have h0 : y 0 = w 0 := hy 0 (Nat.succ_pos _)
    have h1 : y (w 0) = w (w 0) := hy (w 0) (Nat.lt_succ_self _)
    show decide (y (y 0) = 0) = decide (w (w 0) = 0)
    rw [h0, h1]
  · rintro ⟨N, hN⟩
    have := hN (fun i => if i = 0 then N + 1 else 0)
      (fun i => if i = 0 then N + 1 else if i = N + 1 then 1 else 0)
      (fun i hi => by by_cases h : i = 0 <;> simp [h]; omega)
    simp at this

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms trials
#print axioms fires
#print axioms fires_measurable
#print axioms coords_iIndep
#print axioms fires_comap
#print axioms fires_iIndepSet
#print axioms trials_fires
#print axioms trials_tsum_top
#print axioms crossing_almost_surely
#print axioms exists_fires_io
#print axioms zeroBlock
#print axioms zeroBlock_eq_pi
#print axioms trials_zeroBlock
#print axioms exists_halving_block
#print axioms trials_zeroBlock_le
#print axioms silentFrom
#print axioms silentFrom_eq_iInter
#print axioms not_mem_limsup_fires_iff
#print axioms ZeroBlockTest
#print axioms AvoidsTests
#print axioms zeroBlockTest_silentFrom
#print axioms fires_io_of_avoids
#print axioms squaresTape
#print axioms squaresTape_not_avoids
#print axioms oneBlock
#print axioms trials_oneBlock
#print axioms slotMotion
#print axioms slotRun
#print axioms slotRun_isRun
#print axioms slotMotion_leavesAt_false
#print axioms slotMotion_selfOnlyAt_true
#print axioms slotRun_crosses_iff
#print axioms slotRun_image_departs_of_avoids
#print axioms firedRun
#print axioms firedRun_spec
#print axioms firedRun_isRun
#print axioms t_snap_of_fires_once
#print axioms trials_fires_once
#print axioms t_snap_of_avoids
#print axioms prefixDetermined_of_continuous
#print axioms continuous_of_prefixDetermined
#print axioms isOpen_fires_once
#print axioms not_continuousAt_bot_of_decides_fires_once
#print axioms no_continuous_test_fires_once
#print axioms ContinuousTestStatement

end PurityCheck
