import ZeroParadox.Valuation.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Connected.PathConnected

/-!
# ZPF — the snap-occurrence dichotomy over ℚ

## Engineer's Take

This layer shows the exact edge between ℝ and ℚ_p using Ostrowski's theorem, and shows that the two
diverge into different branches specifically due to how they treat their respective bottom element. It is an
example of how incompatible structures can be built by flipping a single bit of logic — notably, the
treatment of zero.

## Overview

Completes ZP-F's "Classification Note": the Binary Snap's domain of validity is exactly the
non-Archimedean completions of ℚ. Unifies three previously separate facts under ONE statement,
with "snap occurs" formalized topologically as **total disconnectedness** (predicate (a)):

- ℝ (the Archimedean completion): connected, NOT totally disconnected → no snap.
  (Order-language companion: ZP-F `ZeroParadox.f_snap_impossible`.)
- ℚ_p (the non-Archimedean completions): totally disconnected → snap.
  (ZP-B anchor: `ZeroParadox.t5_totallyDisconnected`, itself `inferInstance` from Mathlib.)
- Ostrowski (ZP-P, `ZPP_Ostrowski`): these are the ONLY completions, and they are mutually exclusive.

## Why topological (predicate (a), Tim 2026-06-24)
The only NON-CIRCULAR choice: "snap := non-Archimedean" just renames Ostrowski. Total disconnectedness
is a genuinely different property whose coincidence with the Ostrowski class is real content. Both
witnesses are Mathlib-solid; the dichotomy reuses ZP-P's Ostrowski backbone + ZP-B's topology anchor.

## Symbol map (concept → Lean/Mathlib)
- "snap occurs"             → `TotallyDisconnectedSpace K`  (K a completion of ℚ)
- ℝ completion              → `ℝ`; connected via `Real.instPathConnectedSpace`
- ℚ_p completion            → `ℚ_[p]` = `Padic p` `[Fact p.Prime]`; totally disconnected = inferInstance
- "no order-atom" (ℝ side)  → `ZeroParadox.f_snap_impossible` (order companion)
- Ostrowski exhaustiveness  → `ZeroParadox.completions_exhaustive` (`equiv_real_or_padic`)
- Ostrowski orthogonality   → `ZeroParadox.real_not_equiv_padic` (`not_real_isEquiv_padic`)
- "ℝ not totally disc."     → ℝ connected + nontrivial → ¬ `TotallyDisconnectedSpace ℝ`   [NEW lemma]

## Scope / honest seam
v1 states the dichotomy as a faithful BUNDLE over the concrete completions (ℝ, ℚ_p) + the Ostrowski
classification of abstract absolute values. The implicit seam — "f ≈ real ⇒ completion is ℝ", "f ≈ padic p
⇒ completion is ℚ_p" — is left to the reader (it is standard); a single biconditional quantifying over the
abstract completion `UniformSpace.Completion` is the v2 polish (carries the completion-transport plumbing).

STATUS: PROVED (v1 bundle), sorry-free. Reuses ZP-P's Ostrowski backbone + Mathlib's
ultrametric/connected instances; the only new lemma is `real_no_snap`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Rat.AbsoluteValue

/-- The snap (total disconnectedness) holds for every non-Archimedean completion `ℚ_p`. -/
theorem padic_snaps (p : ℕ) [Fact p.Prime] : TotallyDisconnectedSpace ℚ_[p] := inferInstance

/-- The snap fails for the Archimedean completion `ℝ`: it is connected and nontrivial,
    hence not totally disconnected. -/
theorem real_no_snap : ¬ TotallyDisconnectedSpace ℝ := by
  intro h
  haveI := h
  have hsub : (Set.univ : Set ℝ).Subsingleton :=
    isTotallyDisconnected_of_totallyDisconnectedSpace Set.univ Set.univ
      (Set.Subset.refl _) isPreconnected_univ
  exact zero_ne_one (hsub (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)))

/-- **Snap-occurrence dichotomy over ℚ.** Among the completions of ℚ, the snap (total
disconnectedness) holds exactly for the non-Archimedean ones (the `ℚ_p`) and fails for the unique
Archimedean one (`ℝ`); by Ostrowski these are the only, mutually-exclusive cases. -/
theorem snap_dichotomy :
    (∀ (p : ℕ) [Fact p.Prime], TotallyDisconnectedSpace ℚ_[p]) ∧
    (¬ TotallyDisconnectedSpace ℝ) ∧
    (∀ f : AbsoluteValue ℚ ℝ, f.IsNontrivial →
        f ≈ real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ padic p) ∧
    (∀ (p : ℕ) [Fact p.Prime], ¬ real.IsEquiv (padic p)) :=
  ⟨fun p => padic_snaps p,
   real_no_snap,
   fun f hf => ZeroParadox.completions_exhaustive f hf,
   fun p => ZeroParadox.real_not_equiv_padic p⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms padic_snaps
#print axioms real_no_snap
#print axioms snap_dichotomy
end PurityCheck
