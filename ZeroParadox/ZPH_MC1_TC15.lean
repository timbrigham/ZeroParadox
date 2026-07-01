-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPJ_SelfApp
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — TC15: the selfApp bottom sits at the μ=ν seam, not on either branch

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The bottom-diagram tree (`thread_obstruction_table_2026-06-29.md`) has a μ root (least fixed point /
initial / colimit, well-founded descent) and a ν root (greatest fixed point / terminal / limit). One
node on the queue is the ZP-J `AbstractSelfApp` fixed point — the structural Quine atom (ZP-J / AFA),
to be placed: μ, ν, or seam?

This module **pre-commits and witnesses** the answer. `AbstractSelfApp.unique_fp` says ⊥ is the
*unique* fixed point of `selfApp`. A unique fixed point is trivially both extremal in the fixed-point
poset: it is the least fixed point AND the greatest fixed point. On the μ/ν fork, the coincidence
"least fixed point = greatest fixed point" is exactly the seam condition (μ = ν). So the selfApp /
Quine-atom node lands at the **seam**, with the #5 Hilbert zero object — not on the μ or ν branch.

**Load-bearing content, in the theorem statements (not just here):**

- `selfApp_bot_is_least_fp` — ⊥ is ≼ every fixed point of `selfApp` (μ-extremal: least fixed point).
- `selfApp_bot_is_greatest_fp` — every fixed point of `selfApp` is ≼ ⊥ (ν-extremal: greatest fixed
  point). This conjunct is what forces the seam: a μ-only node fails it.
- `selfApp_bot_is_both_extremal` — the conjunction: ⊥ is simultaneously least and greatest fixed
  point. μ-characterization and ν-characterization coincide AT this node ⇒ it is the seam.
- `selfApp_fp_set_eq_singleton_bot` — the fixed-point set is exactly `{⊥}` (reusing
  `selfMem_eq_singleton_bot`). This is the NO-GO fence made positive: the seam is **non-degenerate**
  because the fixed-point set is a *nonempty* singleton (⊥ really is a fixed point, `fixed_bot`), not
  the empty set. "Least = greatest" here is the genuine μ=ν collapse, not the vacuous emptiness case.
- `selfApp_seam_nondegenerate` — bundles non-emptiness (⊥ ∈ f.p. set) with both-extremal, ruling out
  the degenerate reading where "greatest fixed point" is empty.

**Honest fence.** Lean proves: ⊥ is both the least and the greatest fixed point of `selfApp`, and the
fixed-point set is the nonempty singleton `{⊥}`. The reading "least = greatest IS the μ=ν seam, hence
this node is the seam with #5 / the diagonal-fixed-point keystone" is the framework's interpretation
of that pattern — the seam *placement* is meaning attached to the Lean fact, not a separate Lean
theorem. The pre-registered GO conjecture is proved; the NO-GO (degenerate/vacuous placement) is
refuted by `selfApp_fp_set_eq_singleton_bot` showing the f.p. set is inhabited.
-/

namespace ZeroParadox.ZPH_MC1_TC15

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ_SelfApp

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-- μ-extremal: ⊥ is ≼ every fixed point of `selfApp` (it is the LEAST fixed point).
    Immediate from `bot_le` — ⊥ is the global minimum, a fortiori the minimum among fixed points. -/
theorem selfApp_bot_is_least_fp :
    ∀ x : L, AbstractSelfApp.selfApp x = x → le (bot : L) x :=
  fun x _ => bot_le x

/-- ν-extremal: every fixed point of `selfApp` is ≼ ⊥ (⊥ is the GREATEST fixed point).
    This is the seam-forcing conjunct: by `unique_fp` every fixed point equals ⊥, so it is ≼ ⊥ by
    reflexivity. A μ-only node would fail this. -/
theorem selfApp_bot_is_greatest_fp :
    ∀ x : L, AbstractSelfApp.selfApp x = x → le x (bot : L) := by
  intro x hx
  have : x = bot := AbstractSelfApp.unique_fp x hx
  rw [this]
  exact le_refl bot

/-- **The seam, in one statement (pre-registered GO).** ⊥ is simultaneously the least AND the greatest
    fixed point of `selfApp`. The μ-characterization (least f.p.) and the ν-characterization
    (greatest f.p.) coincide at this node — exactly the μ=ν seam condition. So the selfApp /
    Quine-atom bottom sits at the seam, not on either branch. -/
theorem selfApp_bot_is_both_extremal :
    (∀ x : L, AbstractSelfApp.selfApp x = x → le (bot : L) x)
    ∧ (∀ x : L, AbstractSelfApp.selfApp x = x → le x (bot : L)) :=
  ⟨selfApp_bot_is_least_fp, selfApp_bot_is_greatest_fp⟩

/-- The fixed-point set of `selfApp` is exactly the singleton `{⊥}`.
    Reuses `selfMem_eq_singleton_bot` (the fixed-point predicate `selfMemDerived x` is
    `selfApp x = x`). This is the positive NO-GO fence: the set is a *nonempty* singleton, so the
    "least = greatest" collapse is the genuine μ=ν coincidence, not the vacuous empty-set case. -/
theorem selfApp_fp_set_eq_singleton_bot :
    {x : L | AbstractSelfApp.selfApp x = x} = ({bot} : Set L) :=
  selfMem_eq_singleton_bot

/-- ⊥ is genuinely IN the fixed-point set — the seam is non-degenerate.
    Rules out the NO-GO reading where "greatest fixed point" would be vacuous because the
    fixed-point set is empty. Here the set is inhabited by ⊥ (`fixed_bot`). -/
theorem selfApp_bot_mem_fp_set :
    (bot : L) ∈ {x : L | AbstractSelfApp.selfApp x = x} :=
  AbstractSelfApp.fixed_bot

/-- **Non-degenerate seam (refutes the pre-registered NO-GO).** The fixed-point set is inhabited
    (⊥ ∈ it) AND ⊥ is both extremal. So "least = greatest" is the true μ=ν collapse of a nonempty
    fixed-point poset, not the degenerate emptiness that would route the node to tier-1. -/
theorem selfApp_seam_nondegenerate :
    (bot : L) ∈ {x : L | AbstractSelfApp.selfApp x = x}
    ∧ (∀ x : L, AbstractSelfApp.selfApp x = x → le (bot : L) x)
    ∧ (∀ x : L, AbstractSelfApp.selfApp x = x → le x (bot : L)) :=
  ⟨selfApp_bot_mem_fp_set, selfApp_bot_is_least_fp, selfApp_bot_is_greatest_fp⟩

end ZeroParadox.ZPH_MC1_TC15

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC15

#print axioms selfApp_bot_is_least_fp
#print axioms selfApp_bot_is_greatest_fp
#print axioms selfApp_bot_is_both_extremal
#print axioms selfApp_fp_set_eq_singleton_bot
#print axioms selfApp_bot_mem_fp_set
#print axioms selfApp_seam_nondegenerate

end PurityCheck
