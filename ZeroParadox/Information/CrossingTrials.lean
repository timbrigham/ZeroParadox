import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import ZeroParadox.Die

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
- § III The payoff; § IV–VII from almost surely to one run (ride-along `CrossingTrials.md`)
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
`trials p hp`, and `w` avoids `𝒯`, then `w` fires infinitely often.** One way: at `p = 1/2` the
squares control below fires infinitely often and is caught by a zero-block test. `Reading:` `htyp`
is the typicality commitment written as a hypothesis on one tape. -/
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
-- (level `m` the `m` non-squares after `m * m`).
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
same for any tape that fires once. Without `htyp` the all-`false` tape's run never leaves `false`. -/
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

-- Statement: the converse fails: if `φ` is a one-to-one lax map and `w` fires at some stage, the image
-- run leaves its start, with no measure and no typicality hypothesis (the squares tape is one such `w`).
example {β : Type*} {N : Motion β} (φ : Motion.LaxHom slotMotion N)
    (hi : Function.Injective φ.toFun) (w : ℕ → Bool) (hw : ∃ k, w k = true) :
    ∃ n, (φ.toFun ∘ slotRun w) n ≠ (φ.toFun ∘ slotRun w) 0 := by
  obtain ⟨n, hn⟩ := (slotRun_crosses_iff w).2.2 hw
  exact ⟨n, fun e => by have := hi e; rw [hn, (slotRun_crosses_iff w).1] at this; cases this⟩

-- Statement: CONTROL: without the typicality hypothesis, the all-`false` tape drives a run that
-- stays at `false` at every stage.
example : ∀ n, slotRun (fun _ => false) n = false := fun n => by simp [slotRun]

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
#print axioms oneBlock
#print axioms trials_oneBlock
#print axioms slotMotion
#print axioms slotRun
#print axioms slotRun_isRun
#print axioms slotMotion_leavesAt_false
#print axioms slotMotion_selfOnlyAt_true
#print axioms slotRun_crosses_iff
#print axioms slotRun_image_departs_of_avoids

end PurityCheck
