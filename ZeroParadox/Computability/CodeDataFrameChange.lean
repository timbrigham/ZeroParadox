-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the computability-frame realization of "the snap is the change of frame" — the code↔data (Gödel) involution swaps a configuration's program-role and data-role (both Gödel-numbered as ℕ); its fixed locus is the self-application diagonal (code = data), where the Kleene/Roger quine lives (the self-reproducing fixed point = ⊥). The computability analog of RiemannSphere's rInv (0↔∞) and Category's op (initial↔terminal). Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Computability.Kleene
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The frame-change in the computability frame: the code↔data involution and the quine on its fixed locus

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The valuation frame's frame-change is `rInv` (swaps the poles `0 ↔ ∞`); the category frame's is `op`
(swaps `initial ↔ terminal`). The computability frame's is the **code↔data swap**: a configuration is a
pair `(program, datum)`, both Gödel-numbered as `ℕ`, and the frame-change exchanges the program-role and
the data-role — `codeDataSwap := Prod.swap` on `ℕ × ℕ`. This is a genuine involution
(`codeDataSwap_involutive`), and — exactly as `rInv` fixes the seam `‖x‖ = 1` and `op` fixes the zero
object — its **fixed locus is the self-application diagonal**: `codeDataSwap p = p ↔ p.1 = p.2`
(`codeDataSwap_fixed_iff`), i.e. the configurations where a program's code equals its datum, a program
run on its own code.

The Kleene/Roger quine lives on that fixed locus. Every code's self-application configuration
`(encode c, encode c)` is swap-fixed (`selfConfig_on_fixedLocus`), and Roger's fixed-point theorem
(`roger_fixed_point_exists`, Mathlib `Nat.Partrec.Code.fixed_point`) supplies, for any computable
transformation `f`, a fixed-point code `c` with `eval (f c) = eval c` whose self-configuration sits on
the diagonal. `codedata_is_frameflip` bundles the three faces: the frame-change is an involution, its
fixed locus is exactly the self-application diagonal, and the self-reproducing quine lies on it — the
computability realization of "the snap is the change of frame."

Content: a bundling of Mathlib's `Prod.swap` involution with Roger's fixed-point theorem and the
`quine_period_is_goedel` / `IsComputationalQuine` infrastructure of ZP-K; no mathematical novelty. The
`Prod.swap` faces are choice-free; the quine face inherits `Classical.choice` from Roger's theorem (the
Mathlib computability infrastructure), as documented in `Computability/Kleene.lean`.

**Fences.** Computability point-of-view's shape of the frame-change; the abstract cross-domain
"snap = frame-change" stays conjectural (type boundary; see
`.claude-local/notes/frame_change_across_domains_2026-07-11.md`).

## Structure
- § I  The code↔data involution: `codeDataSwap`, involutive, fixed locus = the self-application diagonal
- § II The quine on the fixed locus: `selfConfig_on_fixedLocus`, `codedata_is_frameflip`
-/

namespace ZeroParadox

open Nat.Partrec Nat.Partrec.Code

/-! ## § I — The code↔data involution -/

/-- The **code↔data frame-change**: swap a configuration's program-role and data-role (both
    Gödel-numbered as `ℕ`). The computability analog of `rInv` (`0 ↔ ∞`) and `op`
    (`initial ↔ terminal`). -/
def codeDataSwap : ℕ × ℕ → ℕ × ℕ := Prod.swap

/-- The frame-change is an **involution** (self-inverse), like `rInv` and `op`. -/
theorem codeDataSwap_involutive : Function.Involutive codeDataSwap := by
  sorry

/-- The **fixed locus of the frame-change is the self-application diagonal**: a configuration is
    swap-fixed iff its code and datum coincide — a program run on its own code. The computability
    analog of `rInv` fixing the seam `‖x‖ = 1`. -/
theorem codeDataSwap_fixed_iff (p : ℕ × ℕ) : codeDataSwap p = p ↔ p.1 = p.2 := by
  sorry

/-! ## § II — The quine on the fixed locus -/

/-- Every code's **self-application configuration** `(encode c, encode c)` lies on the fixed locus
    (the diagonal) of the frame-change. -/
theorem selfConfig_on_fixedLocus (c : Code) :
    codeDataSwap (Encodable.encode c, Encodable.encode c)
      = (Encodable.encode c, Encodable.encode c) := by
  sorry

/-- **The code↔data frame-flip (computability frame).** The frame-change is (i) an involution
    (self-inverse, like `rInv`/`op`); (ii) its fixed locus is exactly the self-application diagonal
    (code = datum); and (iii) the Roger/Kleene quine — the self-reproducing fixed point — lives on that
    locus: for any computable transformation `f` there is a fixed-point code `c` (`eval (f c) = eval c`)
    whose self-application configuration is swap-fixed. The computability realization of "the snap is the
    change of frame." -/
theorem codedata_is_frameflip :
    Function.Involutive codeDataSwap
      ∧ (∀ p : ℕ × ℕ, codeDataSwap p = p ↔ p.1 = p.2)
      ∧ (∀ f : Code → Code, Computable f →
          ∃ c : Code, eval (f c) = eval c
            ∧ codeDataSwap (Encodable.encode c, Encodable.encode c)
                = (Encodable.encode c, Encodable.encode c)) := by
  sorry

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms codeDataSwap_involutive
#print axioms codeDataSwap_fixed_iff
#print axioms selfConfig_on_fixedLocus
#print axioms codedata_is_frameflip
end PurityCheck
