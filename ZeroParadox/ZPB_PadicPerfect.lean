import ZeroParadox.ZPN_P8
import Mathlib.Topology.Perfect

/-!
# M11 (re-attempt): the 2-adic ball is perfect — Cantor–Bendixson rank 0

Genuine re-attempt of M11 (was self-deferred with 0 attempts). The tractable half: ℤ₂ is a **perfect**
set — closed with no isolated points — so its Cantor–Bendixson rank is 0 (the derived set is the whole
space; nothing is ever removed). Proof: every 2-adic integer `x` is the limit of the *distinct* points
`x + 2ⁿ → x` (reusing P8's `two_pow_tendsto_zero`), so no point is isolated.

The Hausdorff-dimension half (`dim_H ℤ₂ = 1`) is the genuinely harder piece — Mathlib has `Set.dimH`
but no ready computation for self-similar p-adic sets; that needs the mass-distribution / self-similar
machinery and is the honest remaining open part of M11.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.P8

open Filter Topology

/-- **ℤ₂ is perfect (M11, CB-rank half).** The 2-adic integers form a perfect set: closed, with no
    isolated points. Hence Cantor–Bendixson rank 0. Every `x` is a limit of distinct points
    `x + 2ⁿ → x`. -/
theorem padicInt_univ_perfect : Perfect (Set.univ : Set ℤ_[2]) := by
  refine ⟨isClosed_univ, preperfect_iff_nhds.mpr fun x _ U hU => ?_⟩
  have htend : Tendsto (fun n : ℕ => x + (2 : ℤ_[2]) ^ n) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add two_pow_tendsto_zero
  obtain ⟨n, hn⟩ := (htend.eventually_mem hU).exists
  refine ⟨x + 2 ^ n, ⟨hn, Set.mem_univ _⟩, ?_⟩
  intro h
  exact pow_ne_zero n (show (2 : ℤ_[2]) ≠ 0 by norm_num)
    (add_left_cancel (h.trans (add_zero x).symm))

end ZeroParadox.P8

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.P8
#print axioms padicInt_univ_perfect
end PurityCheck
