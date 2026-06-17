import Mathlib.NumberTheory.Ostrowski
import ZeroParadox.ZPP

/-!
# ZP-P instance: the number-system fork (ℝ vs ℚ_p), via Ostrowski

The number systems instance of the fixed-point fork (ZP-P). The completions of ℚ split into two
mutually-exclusive kinds — the Archimedean (real) absolute value and the non-Archimedean (p-adic)
ones — and Ostrowski's theorem classifies them exhaustively. The contact point of this fork is 0: in
the Archimedean completion ℝ it is approached but never reached (density), while in the 2-adic
completion ℚ₂ it is the unique fixed point of `x ↦ 2x` (`ZeroParadox.ZPJ.q2_unique_fp`) and its
valuation diverges (`v₂(0) = ∞`, ZP-B). See ZP-B / ZP-F for the snap behaviour at 0.

This file pins the exact Mathlib lemmas the prose document cites, so the citations cannot silently
drift:

- **Exhaustiveness leg:** `Rat.AbsoluteValue.equiv_real_or_padic` — every nontrivial absolute value on
  ℚ is equivalent to `real` or to `padic p` for a unique prime `p`.
- **Orthogonality leg:** `Rat.AbsoluteValue.not_real_isEquiv_padic` — `real` is inequivalent to every
  `padic p`.

**FENCE (per ZP-P soft fence).** This fork is theorem-backed *on its own terms* (Ostrowski is a genuine
classification theorem — stronger backing than the metatheoretic Foundation/AFA orthogonality). It is
**NOT** claimed to be an instance of the μ/ν (least-vs-greatest fixed point) schema: Ostrowski concerns
absolute values, not fixed points of a functor. The thread to ZP's diagonal fixed point runs through
the contact point 0 (`q2_unique_fp`), not through `fork_collapse_iff`.
-/

namespace ZeroParadox.ZPP

open Rat.AbsoluteValue

/-- **Exhaustiveness leg of the number-system fork.** Every nontrivial absolute value on ℚ is
equivalent to the real (Archimedean) absolute value, or to a p-adic one for a unique prime. The two
kinds of completion are the complete list. (Ostrowski's theorem, `equiv_real_or_padic`.) -/
theorem completions_exhaustive (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ padic p :=
  equiv_real_or_padic f hf

/-- **Orthogonality leg of the number-system fork.** The real absolute value is inequivalent to every
p-adic absolute value: the two kinds of completion are genuinely distinct, never the same metric.
(`not_real_isEquiv_padic`.) -/
theorem real_not_equiv_padic (p : ℕ) [Fact p.Prime] : ¬ real.IsEquiv (padic p) :=
  not_real_isEquiv_padic p

/-! ## Engineer's Take

These files sit at the boundary of where choice lives within the framework. There is a distinct boundary
between the theorems that define the Zero Paradox framework itself and the individual implementations of
the tooling, and that boundary is the same for set theory, coalgebra, and p-adics. This is a synthesis
layer: a validation tool, a unit test to represent that concept quickly.

Here the dataset is the completions of ℚ: ℝ (Archimedean) versus ℚ₂ (non-Archimedean), classified by
Ostrowski, a realization whose choice is inherited from Mathlib's classical analysis.
-/

section PurityCheck
-- These inherit `Classical.choice` from Mathlib's classical analysis / number theory (Ostrowski).
-- That is expected and honest: the number-system fork is an *analytic realization*, which carries
-- choice — in contrast to the choice-free fork spine (`ZeroParadox.ZPP.fork_collapse_iff`,
-- `[propext, Quot.sound]` only). Core choice-free; realizations choice-carrying. See AxiomProfile.lean.
#print axioms completions_exhaustive
#print axioms real_not_equiv_padic
end PurityCheck

end ZeroParadox.ZPP
