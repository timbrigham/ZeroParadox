-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import ZeroParadox.ZPH_TopFunctor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC05 — the p-adic floor #3 as a dynamical attractor

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file tests **TC05**, a candidate recharacterization of the p-adic bottom (#3, the snap floor
`{0} = ⋂ q2Ball n ⊆ Q₂`). In `ZPH_TopFunctor` #3 appears as a **ν-style limit**: the intersection of
a shrinking inverse system of clopen balls. The claim under test here is that the *same* floor `0` is
**also** a global dynamical attractor — the orbit of the **doubling map** `x ↦ 2·x` converges to `0`
from *every* starting point in `Q₂`. If true, this is a candidate bridge toward #2 (the
Markov-dynamical attractor, a fixed point of a stochastic map), recasting the p-adic ν as an attractor.

**Pre-registered GO conjecture:** `2ⁿ · x → 0` for all `x : Q₂`.

**Pre-registered NO-GO obstruction:** the doubling map is *not* a contraction / its orbit does not
converge.

**Verdict: GO.** The load-bearing reason is that in `Q₂` the doubling map *is* a strict contraction:
`‖2‖₂ = 1/2 < 1` (Archimedes fails — multiplying by 2 makes things *smaller* 2-adically). This is the
exact opposite of the real picture, where `x ↦ 2x` is expansive and `0` is a *repeller*. So the
pre-registered NO-GO ("not a contraction") is **false** in `Q₂`, and the orbit converges globally.

What the Lean proves (load-bearing, in the statements):

- `doubling_norm_lt_one` — `‖(2 : Q₂)‖ < 1`: the doubling map is a strict 2-adic contraction. This is
  the obstruction-killer; it is *false* over ℝ and is the whole reason the orbit collapses.
- `doubling_orbit_tendsto_zero` — `Tendsto (fun n => (2 : Q₂)^n * x) atTop (nhds 0)` for **every**
  `x : Q₂`: the GO claim, `0` is a global attractor of the doubling map. The quantifier "for every `x`"
  is what makes `0` *global*, and it lives in the statement, not the prose.
- `doubling_zero_isFixed` — `2 · 0 = 0`: the limit point `0` is a fixed point of the doubling map.
  (This is `mul_zero` — it holds for any multiplier; it confirms `0` is genuinely fixed, but is not
  itself dynamical content.)
- `orbit_tendsto_into_topfloor` — the **load-bearing bridge**: for every `x`, the orbit `2ⁿ · x`
  converges to the unique point `p` cut out by the ν-limit floor `⋂ q2Ball n = {p}`. The orbit and the
  inverse-limit floor appear together in one statement, so "#3-as-attractor = #3-as-ν-limit" is
  witnessed, not narrated. (`topfloor_singleton` is the bare floor equation `⋂ q2Ball n = {0}`, with no
  dynamics — re-exported only as a lemma for the bridge.)

**Honest scope (interpretation, NOT proved here).** The "candidate bridge toward #2" is interpretation:
this file shows #3 is an attractor of a *deterministic ℚ₂-linear* map, whereas #2 is the attractor of a
*stochastic* map on a simplex. No functor or measure-preserving comparison between the two dynamical
systems is built — that edge remains OPEN. TC05 establishes only that #3 *carries an attractor
structure*, putting it in the same descriptive vocabulary as #2; it does not connect the two systems.
-/

namespace ZeroParadox.ZPH_MC1_TC05

open ZeroParadox.ZPB
open Filter Topology

/-- **The contraction fact (obstruction-killer).** The 2-adic norm of the doubling multiplier is
    `< 1`: `x ↦ 2·x` is a strict contraction in `Q₂`. False over ℝ, where it is expansive and `0` is a
    repeller — this single inequality is why the p-adic orbit collapses to `0`. -/
theorem doubling_norm_lt_one : ‖(2 : Q₂)‖ < 1 := by
  have : ‖((2 : ℕ) : Q₂)‖ < 1 := Padic.norm_p_lt_one
  simpa using this

/-- `‖(2 : Q₂)‖ = (2 : ℝ)⁻¹`: the exact 2-adic norm of the contraction multiplier. -/
theorem doubling_norm_eq : ‖(2 : Q₂)‖ = (2 : ℝ)⁻¹ := by
  have : ‖((2 : ℕ) : Q₂)‖ = ((2 : ℕ) : ℝ)⁻¹ := Padic.norm_p
  simpa using this

/-- **GO — the global attractor.** The orbit of the doubling map converges to `0` from *every*
    starting point: `2ⁿ · x → 0` for all `x : Q₂`. The universal quantifier over `x` is the
    load-bearing "global attractor" content. Proof: `‖2ⁿ · x‖ = ‖2‖ⁿ · ‖x‖ → 0` because `‖2‖ < 1`. -/
theorem doubling_orbit_tendsto_zero (x : Q₂) :
    Tendsto (fun n : ℕ => (2 : Q₂) ^ n * x) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hnorm : (fun n : ℕ => ‖(2 : Q₂) ^ n * x‖)
      = fun n : ℕ => ‖(2 : Q₂)‖ ^ n * ‖x‖ := by
    funext n
    rw [norm_mul, norm_pow]
  rw [hnorm]
  have hbase : Tendsto (fun n : ℕ => ‖(2 : Q₂)‖ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) doubling_norm_lt_one
  simpa using hbase.mul_const ‖x‖

/-- The attractor is genuinely a fixed point of the doubling map: `2 · 0 = 0`. -/
theorem doubling_zero_isFixed : (2 : Q₂) * 0 = 0 := mul_zero 2

/-- The `ZPH_TopFunctor` ν-limit floor as a bare set equation, re-exported for convenience:
    `⋂ n, q2Ball n = {0}`. This is purely about the inverse-limit floor — it carries **no**
    dynamical content (it is just `fB_bottom_is_limit`). The dynamics/ν-limit *bridge* is the next
    theorem, `orbit_tendsto_into_topfloor`, where the orbit and the floor appear in one statement. -/
theorem topfloor_singleton :
    ⋂ n, ZPH_TopFunctor.q2Ball n = {(0 : Q₂)} :=
  ZPH_TopFunctor.fB_bottom_is_limit

/-- **The bridge — dynamics meet the ν-limit floor (witnessed in-statement).** For every starting
    point `x`, the doubling orbit `2ⁿ · x` converges to the *unique point* `p` of the
    `ZPH_TopFunctor` inverse-limit floor `⋂ n, q2Ball n`. Both the orbit (left) and the ν-limit floor
    (the hypothesis pinning `p`) appear in the statement, so the identification "#3-as-attractor =
    #3-as-ν-limit" is proved, not narrated: the dynamical limit of every orbit is exactly the point
    cut out by the shrinking-ball inverse system. -/
theorem orbit_tendsto_into_topfloor
    (x p : Q₂) (hp : ⋂ n, ZPH_TopFunctor.q2Ball n = {p}) :
    Tendsto (fun n : ℕ => (2 : Q₂) ^ n * x) atTop (nhds p) := by
  -- the floor is a singleton, and topfloor_singleton pins its point to `0`
  have hp0 : p = 0 := by
    have : ({p} : Set Q₂) = {(0 : Q₂)} := by rw [← hp, topfloor_singleton]
    exact (Set.singleton_eq_singleton_iff).1 this
  subst hp0
  exact doubling_orbit_tendsto_zero x

end ZeroParadox.ZPH_MC1_TC05

/-! ## Axiom Purity Check

`Classical.choice` enters through the Mathlib normed-field / p-adic and topology libraries
(`Padic.norm_p`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_zero_iff_norm_tendsto_zero`,
`q2Ball`/`closedBall`). It is a library dependency carried by the ZP-B topology layer, not a new
commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC05

#print axioms doubling_norm_lt_one
#print axioms doubling_norm_eq
#print axioms doubling_orbit_tendsto_zero
#print axioms doubling_zero_isFixed
#print axioms topfloor_singleton
#print axioms orbit_tendsto_into_topfloor

end PurityCheck
