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

## Formal Overview
Completes ZP-F's "Classification Note": **where the Binary Snap is RULED OUT** among the completions of ℚ.
`Reading:` CARRIER — "snap occurs" is STIPULATED as total disconnectedness (predicate (a)), the only
non-circular choice, since "snap := non-Archimedean" would merely rename Ostrowski (Tim 2026-06-24). So nothing
here runs from a carrier property TO the snap, and each declaration below carries its own fence. ⚠ The first
step is AX-B1, a commitment — canonical in `ZeroParadox/Valuation/Padic.lean`'s classification note.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Rat.AbsoluteValue

/-- `Statement:` CARRIER — every non-Archimedean completion `ℚ_p` is totally disconnected, so the topological obstruction is ABSENT there. It is not thereby supplied: see `snap_dichotomy` below. -/
theorem padic_snaps (p : ℕ) [Fact p.Prime] : TotallyDisconnectedSpace ℚ_[p] := inferInstance

/-- `Statement:` CARRIER — `ℝ` is connected and nontrivial, hence NOT totally disconnected. Mathlib
    states the obstruction as a CARDINALITY floor (`subsingleton_of_preconnected_totallyDisconnected`
    forces `Subsingleton`; `Nontrivial ℝ` forbids it), so the standard form is used, not re-proved.
    ⚠ TOPOLOGICAL half only — the order half is `ZeroParadox.f_snap_impossible`, obstruction DENSITY. -/
theorem real_no_snap : ¬ TotallyDisconnectedSpace ℝ := by
  intro h
  haveI := h
  exact not_subsingleton ℝ subsingleton_of_preconnected_totallyDisconnected

/-- **Snap-occurrence dichotomy over ℚ.** `Statement:` CARRIER — a four-way conjunction: every `ℚ_p`
is totally disconnected, `ℝ` is not, and by Ostrowski (`ZeroParadox.completions_exhaustive`,
`ZeroParadox.real_not_equiv_padic`) these are the only completions of ℚ and are mutually exclusive.
⚠ No arrow runs from a carrier property TO the snap, and the word "snap" does not occur in the
statement at all. (Its third conjunct IS an implication — Ostrowski's `IsNontrivial → …` — so the
claim is about which arrows are absent, not that the statement is arrow-free.)
Scope (v1): a faithful BUNDLE over the concrete completions plus Ostrowski's classification of
abstract absolute values. The seam — "f ≈ real ⇒ the completion is ℝ" — is left to the reader as
standard; quantifying over the abstract `UniformSpace.Completion` is the v2 polish. -/
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
