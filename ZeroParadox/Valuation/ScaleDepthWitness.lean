-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): a concrete family satisfying ZP-I's `IsDepthChain`, and a gauge for what that does NOT buy. Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.InfinitudeFloor
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

ZP-I names `IsDepthChain` its one *"undischarged modelling commitment"*. Here it holds of
`scaleChain n = 2 ^ n` by proof — but `depthchain_iff_nonneg` measures what that is worth, and the
answer is: exactly non-negativity of the valuation. The content is in the CONJUNCTION with strictness.
-/

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. The family

⚠ **The valuation fact is NOT new here.** `ZeroParadox/Valuation/InfinitudeFloor.lean` proves
`two_pow_valuation` — the same statement, on the same carrier — and this file consumes it rather than
reproving it. What is and is not new, and the axiom-footprint fence, are in
`ZeroParadox/Valuation/ScaleDepthWitness.md`, beside this file. -/

/-- The powers of two, as a `Q₂` sequence. -/
noncomputable def scaleChain : ℕ → Q₂ := fun n => (2 : Q₂) ^ n

theorem scaleChain_ne_zero (n : ℕ) : scaleChain n ≠ 0 :=
  pow_ne_zero n (by norm_num)

/-! ## § II. The seam, and what satisfying it is worth

`IsDepthChain` asserts that the 2-adic valuation tracks the depth index. It holds here — and
`depthchain_iff_nonneg` is why that is a weaker fact than it reads: a chain admits SOME depth index
exactly when its valuations are non-negative, because the index can be read back off the chain. This
witness supplies both sides itself, so it satisfies the interface rather than crossing it. ZP-I's
commitment is that a depth index arriving INDEPENDENTLY from the lattice is the one the valuation
tracks, and that is untouched here. -/

/-- **The commitment, satisfied for one family** — via `InfinitudeFloor.two_pow_valuation`. -/
theorem scaleChain_isDepthChain : IsDepthChain scaleChain (fun n => n) :=
  fun n => two_pow_valuation n

/-- **The gauge for § II.** Being a depth chain is EXACTLY having non-negative valuations. The
    REVERSE direction is the one that reads the index off the chain — its witness is
    `fun n => (S n).valuation.toNat`. So `IsDepthChain` alone excludes only the chains that pass
    below the floor. -/
theorem depthchain_iff_nonneg (S : ℕ → Q₂) :
    (∃ depths : ℕ → ℕ, IsDepthChain S depths) ↔ ∀ n, 0 ≤ (S n).valuation := by
  constructor
  · rintro ⟨depths, h⟩ n
    rw [h n]; exact Int.natCast_nonneg _
  · intro h
    exact ⟨fun n => (S n).valuation.toNat, fun n => by
      simp [Int.toNat_of_nonneg (h n)]⟩

/-! ## § III. The lattice side, and the bound ZP-I asks for -/

/-- The identity depth index is a strict state sequence in `(ℕ, max, 0)`: the successor is the
    join, and no term equals its successor. Choice-free, unlike everything over `Q₂`. -/
theorem depthId_isStrictStateSequence : IsStrictStateSequence (fun n : ℕ => n) :=
  ⟨⟨fun n => n + 1, fun n => by change n + 1 = max n (n + 1); omega⟩,
   fun n => by show n ≠ n + 1; omega⟩

/-- With both sides in hand, ZP-I's own bridge yields its geometric bound, so `t_iz_cauchy` applies.
    ⚠ The LIMIT is not the new part — `PadicAttractor.doubling_orbit_tendsto_zero` already gives it
    for every orbit. What this routing shows is that ZP-I's hypotheses suffice to reach it. -/
theorem scaleChain_tendsto_zero :
    Filter.Tendsto scaleChain Filter.atTop (nhds 0) :=
  t_iz_cauchy scaleChain
    (t_iz_h_bound_from_depth_chain scaleChain (fun n => n)
      scaleChain_ne_zero scaleChain_isDepthChain depthId_isStrictStateSequence)

/-! ## § IV. NO-GO gauge — being a depth chain buys NOTHING about motion

The file this witnesses retracted *"because there is no top element, the chain cannot stop"* and
replaced it with a gauge showing a constant sequence that never moves. The same fence is owed here,
because a family that DOES move invites that reading again. The constant sequence `1` is a perfectly
good depth chain, at depth `0` forever; what it fails is strictness, which lives on the LATTICE side.
⚠ The strictness half restates an anonymous `example` in `SemilatticeInstance.lean`; it is named here
only because the `Q₂` conjunct has to be stated somewhere. -/

/-- **The gauge.** A depth chain that never moves, and the strictness it fails. -/
theorem constChain_isDepthChain_not_strict :
    IsDepthChain (fun _ : ℕ => (1 : Q₂)) (fun _ => 0) ∧
    ¬ IsStrictStateSequence (fun _ : ℕ => (0 : ℕ)) :=
  ⟨fun _ => by simp, fun h => h.2 0 rfl⟩

/-! ## § V. The family is an orbit

`ZeroParadox/Valuation/RiemannSphere.lean` builds the scalings of the 2-adic sphere. This family is
the orbit of `1` under them, so the depth index and the scaling parameter are the same integer. The
orbit stays in the affine chart; the pole at `∞` is fixed by `rScale_infty` and is not reached. -/

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
#print axioms scaleChain_isDepthChain
#print axioms depthchain_iff_nonneg
#print axioms depthId_isStrictStateSequence
#print axioms scaleChain_tendsto_zero
#print axioms constChain_isDepthChain_not_strict
#print axioms scaleChain_eq_orbit
end PurityCheck
