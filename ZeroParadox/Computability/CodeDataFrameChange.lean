-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the computability-frame realization of the POLE EXCHANGE (the snap-as-instance reading is ZP-Q's conjecture, not established here) — the code↔data (Gödel) involution swaps a configuration's program-role and data-role (both Gödel-numbered as ℕ); its fixed locus is the self-application diagonal (code = data), on which every code's self-configuration lies, the Kleene/Rogers quine's included. The computability analog of RiemannSphere's rInv (0↔∞) and Category's op (initial↔terminal). Curated results indexed in ZeroParadox/MANIFEST.md.

import ZeroParadox.Computability.Kleene
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The frame-change in the computability frame: the code↔data involution, whose fixed locus holds every code's self-application

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

`Statement:` INVERSION — the code/data involution exchanges the two roles, and its fixed locus is the
self-application diagonal (`codedata_is_frameflip`). Every code's self-configuration lies on it
(`selfConfig_on_fixedLocus`, for every `c : Code`), so face (iii) adds the existence of a Rogers
fixed-point code (`roger_fixed_point_exists`), not its position.
`Reading:` INVERSION — the framework reads the snap as an instance of this exchange. Conjectural: no snap
transition appears in these statements. See `Multihomed/SnapFrameChange.lean`'s declaration docstring.

Content: a bundling of Mathlib's `Prod.swap` involution with Rogers' fixed-point theorem; no
mathematical novelty.
Footprints: `codeDataSwap_involutive` axiom-free, `codeDataSwap_fixed_iff` `propext`-only; the two
results whose statements mention `Encodable.encode` on `Code` carry `Classical.choice`, which enters
through `Nat.Partrec.Code.instDenumerable` (`ZeroParadox/Category/ChoiceCannotBe.lean` § III; printed in
`ZeroParadox/Computability/Kleene.lean`'s `PurityCheck`). The bundle's proof also calls Rogers' theorem,
not separated here.

**Fences.** Computability point-of-view's shape of the frame-change; the abstract cross-domain
"snap = frame-change" stays conjectural (type boundary).

## Structure
- § I  The code↔data involution: `codeDataSwap`, involutive, fixed locus = the self-application diagonal
- § II Self-application configurations, and the bundled three-face result
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
  intro p
  exact Prod.swap_swap p

/-- The **fixed locus of the frame-change is the self-application diagonal**: a configuration is
    swap-fixed iff its code and datum coincide — a program run on its own code. The computability
    analog of `rInv` fixing the seam `‖x‖ = 1`. -/
theorem codeDataSwap_fixed_iff (p : ℕ × ℕ) : codeDataSwap p = p ↔ p.1 = p.2 := by
  unfold codeDataSwap
  rw [Prod.ext_iff]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact ⟨fun h => h.2, fun h => ⟨h.symm, h⟩⟩

/-! ## § II — Every code's self-configuration on the fixed locus -/

/-- Every code's **self-application configuration** `(encode c, encode c)` lies on the fixed locus
    (the diagonal) of the frame-change. -/
theorem selfConfig_on_fixedLocus (c : Code) :
    codeDataSwap (Encodable.encode c, Encodable.encode c)
      = (Encodable.encode c, Encodable.encode c) :=
  (codeDataSwap_fixed_iff (Encodable.encode c, Encodable.encode c)).mpr rfl

/-- `Statement:` INVERSION — the code↔data frame-change is (i) an involution; (ii) its fixed locus is
    exactly the self-application diagonal; (iii) for any computable `f` some code `c` has
    `eval (f c) = eval c` and a swap-fixed self-configuration, as every code's is
    (`selfConfig_on_fixedLocus`): (iii)'s content is the existence of `c`, not its position.
    `Reading:` INVERSION — the computability realization of the POLE EXCHANGE; the snap-as-instance
    reading is ZP-Q's conjecture, not established here (no snap transition appears in this statement). -/
theorem codedata_is_frameflip :
    Function.Involutive codeDataSwap
      ∧ (∀ p : ℕ × ℕ, codeDataSwap p = p ↔ p.1 = p.2)
      ∧ (∀ f : Code → Code, Computable f →
          ∃ c : Code, eval (f c) = eval c
            ∧ codeDataSwap (Encodable.encode c, Encodable.encode c)
                = (Encodable.encode c, Encodable.encode c)) :=
  ⟨codeDataSwap_involutive, codeDataSwap_fixed_iff, fun f hf =>
    let ⟨c, hc⟩ := roger_fixed_point_exists f hf
    ⟨c, hc, selfConfig_on_fixedLocus c⟩⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms codeDataSwap_involutive
#print axioms codeDataSwap_fixed_iff
#print axioms selfConfig_on_fixedLocus
#print axioms codedata_is_frameflip
end PurityCheck
