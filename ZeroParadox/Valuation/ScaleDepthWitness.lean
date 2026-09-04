-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a concrete family for which ZP-I's `IsDepthChain` is a THEOREM rather than an assertion. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.RiemannSphere
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# A witness for the depth-chain seam: the powers of two

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---
## Formal Overview (AI-assisted)

ZP-I names `IsDepthChain` its one *"undischarged modelling commitment"*: that 2-adic depth and
lattice motion are the same. Here it is a THEOREM for `scaleChain n = 2 ^ n`, of valuation `n`.
⚠ It buys NO motion (§ IV) and nothing about the ⊥ role. Choosing this family IS the occurrence.
-/

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. The family -/

/-- The powers of two, as a `Q₂` sequence. -/
noncomputable def scaleChain : ℕ → Q₂ := fun n => (2 : Q₂) ^ n

theorem scaleChain_ne_zero (n : ℕ) : scaleChain n ≠ 0 :=
  pow_ne_zero n (by norm_num)

/-- The valuation of the `n`-th term is exactly `n`. Mathlib's arithmetic; stated here because it
    is what the next theorem consumes. -/
theorem scaleChain_valuation (n : ℕ) : (scaleChain n).valuation = (n : ℤ) := by
  simp [scaleChain, Padic.valuation_pow]

/-! ## § II. The seam, discharged

`IsDepthChain` is the assertion that the 2-adic valuation tracks the depth index. For this family
it is a consequence of `scaleChain_valuation`, so the interface contract holds by proof. -/

/-- **The undischarged commitment, discharged for one family.** -/
theorem scaleChain_isDepthChain : IsDepthChain scaleChain (fun n => n) :=
  fun n => scaleChain_valuation n

/-! ## § III. The lattice side, and the bound ZP-I asks for -/

/-- The identity depth index is a strict state sequence in `(ℕ, max, 0)`: the successor is the
    join, and no term equals its successor. -/
theorem depthId_isStrictStateSequence : IsStrictStateSequence (fun n : ℕ => n) :=
  ⟨⟨fun n => n + 1, fun n => by change n + 1 = max n (n + 1); omega⟩,
   fun n => by show n ≠ n + 1; omega⟩

/-- With both sides in hand, ZP-I's own bridge yields its geometric bound — so `t_iz_cauchy`
    applies to this family and it converges to `0`. Every hypothesis is now discharged. -/
theorem scaleChain_tendsto_zero :
    Filter.Tendsto scaleChain Filter.atTop (nhds 0) :=
  t_iz_cauchy scaleChain
    (t_iz_h_bound_from_depth_chain scaleChain (fun n => n)
      scaleChain_ne_zero scaleChain_isDepthChain depthId_isStrictStateSequence)

/-! ## § IV. NO-GO gauge — being a depth chain buys NOTHING about motion

⚠ The file this witnesses retracted *"because there is no top element, the chain cannot stop"* and
replaced it with a gauge showing a constant sequence that never moves. The same fence is owed here,
because a family that DOES move invites exactly that reading again.

The constant sequence `1` is a perfectly good depth chain, at depth `0` forever. What it fails is
strictness — which lives on the LATTICE side and is the occurrence. So `IsDepthChain` is the
interface, never the engine, and selecting `scaleChain` over the constant one is a choice. -/

/-- **The gauge.** A depth chain that never moves, and the strictness it fails. -/
theorem constChain_isDepthChain_not_strict :
    IsDepthChain (fun _ : ℕ => (1 : Q₂)) (fun _ => 0) ∧
    ¬ IsStrictStateSequence (fun _ : ℕ => (0 : ℕ)) :=
  ⟨fun _ => by simp, fun h => h.2 0 rfl⟩

/-! ## § V. The family is an orbit

`ZeroParadox/Valuation/RiemannSphere.lean` builds the scalings of the 2-adic sphere. This family is
the orbit of `1` under them, so the depth index and the scaling parameter are the same integer. -/

/-- The chain is the orbit of `1` under the sphere's scalings. -/
theorem scaleChain_eq_orbit (n : ℕ) :
    rScale (n : ℤ) (OnePoint.some (1 : Q₂)) = OnePoint.some (scaleChain n) := by
  simp [rScale, scaleChain, zpow_natCast]

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms scaleChain
#print axioms scaleChain_ne_zero
#print axioms scaleChain_valuation
#print axioms scaleChain_isDepthChain
#print axioms depthId_isStrictStateSequence
#print axioms scaleChain_tendsto_zero
#print axioms constChain_isDepthChain_not_strict
#print axioms scaleChain_eq_orbit
end PurityCheck
