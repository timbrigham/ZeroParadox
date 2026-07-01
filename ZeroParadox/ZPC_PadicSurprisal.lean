import ZeroParadox.ZPC
import ZeroParadox.ZPN_P8

/-!
# B3 (pipeline): information surprisal ≡ 2-adic depth at the floor

Experiment B3 (T3/T6): is ZP-C's surprisal the SAME invariant as the 2-adic valuation/depth, not just an
analogy? `surprisal n = n` (information at ball-hierarchy depth n), and the 2-adic point `2 ^ n` has size
`‖2 ^ n‖ = (1/2)^n = 2^(-n)` (valuation `n`). So both count the same depth `n`.

**Result: CONFIRMED, but NEAR-TAUTOLOGICAL — exactly the demotion I flagged.** The "identity" is
`surprisal n = n = (2-adic depth of 2^n)`: both sides are *definitionally* `n`, so this is two layers
sharing one counter, not a deep independent structural identity. Could-fail was thin (it could only fail on
a normalization mismatch, and there is none). Logged as confirmation, not a strong independent result —
validating the pipeline's volume-vs-independence filter (the generation agent over-ranked this; the filter
corrected it).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPC

/-- Information surprisal at ball-depth `n` is `n`. -/
theorem surprisal_eq_self (n : ℕ) : surprisal n = n := rfl

/-- The 2-adic size of the depth-`n` point `2 ^ n` is `(1/2)^n = 2^(-n)` — i.e. 2-adic valuation `n`.
    Together with `surprisal_eq_self`, surprisal `n` = 2-adic depth `n`: the same counter. -/
theorem padic_size_at_depth (n : ℕ) : ‖(2 : ℤ_[2]) ^ n‖ = (1 / 2 : ℝ) ^ n := by
  rw [norm_pow]
  congr 1
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_cast, PadicInt.norm_p]
  norm_num

end ZeroParadox.ZPC

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPC
#print axioms surprisal_eq_self
#print axioms padic_size_at_depth
end PurityCheck
