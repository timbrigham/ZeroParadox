import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Crossing trials: what a probability on the crossing would buy

## Engineer's Take

TODO (Tim): <Your take, in your own voice. Claude never writes this section; the release gate
keys on this placeholder, so a release is blocked until you fill it.>

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
- § III The payoff — constant positive `p` gives firing with probability one
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

end PurityCheck
