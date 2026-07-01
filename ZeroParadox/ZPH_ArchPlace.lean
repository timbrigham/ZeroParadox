import ZeroParadox.ZPB
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Direction A, Cycle A1 — #2 (Markov) is the archimedean place; #3 (p-adic) is the 2-adic place

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Direction A of the pivot (`pivot_plan_2026-06-30.md`): locate the bottom-diagram's anomalous node #2 in
ℚ's genuine **place structure**, anchored to Mathlib's Ostrowski theorem. The campaign found #2 (the
Markov stationary attractor, living in a *connected* simplex over ℝ) anomalous on every axis; the
local-global picture predicts exactly one special place — the **archimedean** (infinite) one. This file
tests whether #2 occupies that slot.

**Anchored framing (honest).** These are Mathlib-native place-theory facts, tied to the framework nodes
through GENUINE connections: #2's ambient sits over the real (archimedean) completion of ℚ; #3's ambient
`Q₂ = ℚ_[2]` literally *is* the 2-adic completion. So this is a Mathlib-anchored result with a framework
interpretation — it *grounds* "#2 is the archimedean place" in Ostrowski, rather than asserting it. The
place structure runs over ALL places of ℚ (∞ + every prime); the framework lights up #2 (∞) and #3 (p=2)
as two of them.

**Results (load-bearing, in-statement).**
- `node2_place_archimedean` — the real absolute value (#2's place) is **archimedean**: unbounded on ℕ.
- `node3_place_nonarchimedean` — the 2-adic absolute value (#3's place) is **non-archimedean**:
  bounded by 1 on ℕ (the ultrametric / finite-place signature).
- `archimedean_place_unique` — any unbounded absolute value on ℚ is equivalent to `real`: the
  archimedean place is **unique** (Ostrowski's archimedean case). So #2's slot is the only archimedean one.
- `place_dichotomy` — Ostrowski: every nontrivial place is `real` or some `padic p` — the two classes are
  **exhaustive**; #2 (real) and #3 (`padic 2`) instantiate them.
- `node2_place_eq_real_norm` / `node3_place_eq_q2_norm` — the genuine ambient ties: the real place is the
  ℝ-absolute-value (#2's base field) and the 2-adic place is the `Q₂`-norm (#3's ambient).
-/

namespace ZeroParadox.ZPH_ArchPlace

open Rat.AbsoluteValue

/-- #2's place is **archimedean**: the real absolute value on ℚ is unbounded on ℕ (witness `n = 2`). -/
theorem node2_place_archimedean : ¬ (∀ n : ℕ, real n ≤ 1) := by
  intro h
  have h2 := h 2
  norm_num [real_eq_abs] at h2

/-- #3's place is **non-archimedean**: the 2-adic absolute value is bounded by 1 on every natural
    number (the ultrametric / finite-place signature). -/
theorem node3_place_nonarchimedean : ∀ n : ℕ, padic 2 n ≤ 1 := by
  intro n
  exact_mod_cast padic_le_one 2 (n : ℤ)

/-- The archimedean place is **unique**: any unbounded absolute value on ℚ is equivalent to `real`
    (Ostrowski's archimedean case). #2's slot is the only archimedean one. -/
theorem archimedean_place_unique (f : AbsoluteValue ℚ ℝ) (hub : ¬ (∀ n : ℕ, f n ≤ 1)) :
    f ≈ real :=
  equiv_real_of_unbounded hub

/-- Ostrowski exhaustiveness: every nontrivial absolute value on ℚ is `real` or some `padic p`.
    #2 (`real`) and #3 (`padic 2`) instantiate the two exhaustive classes. -/
theorem place_dichotomy (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ padic p :=
  equiv_real_or_padic f hf

/-- Genuine ambient tie for #2: the real place is the ℝ-absolute-value — #2's simplex lives over ℝ. -/
theorem node2_place_eq_real_norm (q : ℚ) : real q = |(q : ℝ)| := by
  simp [real_eq_abs]

/-- Genuine ambient tie for #3: the 2-adic place is the norm in `Q₂ = ℚ_[2]` — #3's ambient. -/
theorem node3_place_eq_q2_norm (q : ℚ) : padic 2 q = ‖(q : ℚ_[2])‖ := by
  rw [padic_eq_padicNorm, Padic.eq_padicNorm]

/-- The topological signature linking the place classification to the campaign's #2-vs-#3 wall: the
    archimedean place completes to a **connected** field (ℝ, the base of #2's simplex), the 2-adic place
    to a **totally disconnected** one (`Q₂ = ℚ_[2]`, #3's ambient). This is the genuine in-kernel tie
    between place-type and the topological character that distinguishes the two nodes (the T2 wall),
    using the framework's own `ZPB.t5_totallyDisconnected`. -/
theorem place_topological_signature :
    ConnectedSpace ℝ ∧ TotallyDisconnectedSpace ℚ_[2] :=
  ⟨inferInstance, ZeroParadox.ZPB.t5_totallyDisconnected⟩

/-- **A1 capstone.** `real` is ℚ's unique archimedean place; `padic 2` is non-archimedean; the two
    classes are exhaustive (Ostrowski). **INTERPRETATION (not a kernel theorem about the simplex):** the
    framework's #2 lives over the archimedean completion ℝ and #3's ambient is the non-archimedean
    `ℚ_[2]` — the "over-ℝ / over-ℚ₂" identification is via the ambients' base fields (witnessed
    topologically by `place_topological_signature` and by the norm ties `node{2,3}_place_eq_*`), NOT by
    any statement quantifying the Markov simplex. So A1 *anchors* #2 to ℚ's archimedean slot; it does not
    prove "#2 = the real place" as an object-level identity. -/
theorem arch_place_characterization :
    (¬ ∀ n : ℕ, real n ≤ 1) ∧
    (∀ n : ℕ, padic 2 n ≤ 1) ∧
    (∀ f : AbsoluteValue ℚ ℝ, (¬ ∀ n : ℕ, f n ≤ 1) → f ≈ real) :=
  ⟨node2_place_archimedean, node3_place_nonarchimedean, fun f h => archimedean_place_unique f h⟩

end ZeroParadox.ZPH_ArchPlace

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_ArchPlace

#print axioms node2_place_archimedean
#print axioms node3_place_nonarchimedean
#print axioms archimedean_place_unique
#print axioms place_dichotomy
#print axioms node2_place_eq_real_norm
#print axioms node3_place_eq_q2_norm
#print axioms place_topological_signature
#print axioms arch_place_characterization

end PurityCheck
