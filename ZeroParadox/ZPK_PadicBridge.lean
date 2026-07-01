import ZeroParadox.ZPK
import ZeroParadox.ZPN_P8

/-!
# B2 (pipeline): the computational bottom maps to the 2-adic floor

Experiment B2 (T3 bridge-the-domains): computation ↔ 2-adic, a domain pair not previously bridged.
The DA-2 instantiation succession has computational quines with UNBOUNDED Gödel numbers
(`infinite_quine_family`). Mapping a quine's Gödel number `encode c` to `2 ^ (encode c) : ℤ₂`, the quine
encodings get arbitrarily 2-adically close to the bottom `0` — computation's bottoms cluster at the
2-adic floor, exactly as the ordinal tower did in P8.

Falsifiable prediction: the quine 2-adic encodings approach 0. Would FAIL if the quine Gödel numbers were
bounded (then the encodings stay 2-adically away from 0) — but `infinite_quine_family` makes them
unbounded, so the prediction holds.

**Honest independence note:** new DOMAIN PAIR (computation ↔ 2-adic), but the BRIDGE MECHANISM (an
unbounded ℕ-valued quantity ↦ `2^·` → 0) is the same one used in P8 (there: ordinal tower-rank). So this
is independent on the domain, a repeat on the mechanism — lighter independence than a fresh mechanism.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPK

open Nat.Partrec Nat.Partrec.Code

/-- **The computational bottom clusters at the 2-adic floor (B2).** For any `ε > 0` there is a
    computational quine `c` whose 2-adic encoding `2 ^ (encode c)` is within `ε` of `0`: the quine
    Gödel numbers are unbounded (`infinite_quine_family`), so `‖2 ^ (encode c)‖ = (1/2)^(encode c)` can be
    made arbitrarily small. The computation→2-adic analog of P8's ordinal→2-adic bridge. -/
theorem quine_encodings_approach_bot (ε : ℝ) (hε : 0 < ε) :
    ∃ c : Code, IsComputationalQuine c ∧ ‖(2 : ℤ_[2]) ^ (Encodable.encode c)‖ < ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨c, hc, hcN⟩ := infinite_quine_family N
  refine ⟨c, hc, ?_⟩
  have hnorm : ‖(2 : ℤ_[2]) ^ (Encodable.encode c)‖ = (1 / 2 : ℝ) ^ (Encodable.encode c) := by
    rw [norm_pow]
    congr 1
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_cast, PadicInt.norm_p]
    norm_num
  rw [hnorm]
  calc (1 / 2 : ℝ) ^ (Encodable.encode c) ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hcN.le
    _ < ε := hN

end ZeroParadox.ZPK

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPK
#print axioms quine_encodings_approach_bot
end PurityCheck
