-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.State.HilbFunctor
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.Multihomed.TreeObstructions
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Cross-root completeness: the #1↔#3 and #5↔#3 edges

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file tests the two **cross-root** (μ↔ν) edges of the bottom-diagram tree
(`thread_obstruction_table_2026-06-29.md` §7) that the earlier obstruction core left untested:

- **(a) #1 proof-theory floor (μ, well-founded order) ↔ #3 p-adic floor (ν, inverse limit).**
- **(b) #5 Hilbert seam (zero object) ↔ #3 p-adic floor (ν, inverse limit).**

The tree predicts cross-root pairs are **obstructed** (NO-GO), unlike the within-root siblings.
Edge (b) has an in-statement separator (initiality). Edge (a) does not: its theorem records two facts
that hold together, and no Lean statement here separates the two floors.

### Edge (a) — #1 vs #3: two descent facts that hold together (Axis I, no separator)

`ordinal_wf_padic_descent_clash` pairs `Ordinal.lt_wf` with `padic_descent_radii_strictAnti`, a fact
about the real sequence `2⁻ⁿ` that never mentions `Q₂`. The conjuncts share no variable, so it
separates nothing. `Ordinal` itself hosts a never-stabilizing strictly descending chain of sets (the
`example` after the theorem), so a never-stabilizing descent does not tell the floors apart. Compare
`ZeroParadox/Multihomed/FloorFactsCooccur.lean` (co-occurrence, no duality) and
`ZeroParadox/Multihomed/Fork.lean` (the μ/ν identification is conjecture).

### Edge (b) — #5 vs #3: zero object (initial) vs non-initial limit floor (Axis II)

The Hilbert seam `#5 = StateSpace 0` is a **zero object** of `ModuleCat ℂ` — in particular it is
**initial**. The p-adic floor `{0} ⊆ Q₂` is a **limit / terminal-flavoured** object and is provably
**not initial** in `TopCat` (`padic_bottom_not_initial`). The separator is the
categorical-polarity clash:

- `seam_initial_padic_not_initial` — `#5` is initial in `ModuleCat ℂ` **and** `#3`'s one-point space is *not*
  initial in `TopCat`. One bottom carries the initial universal property, the other provably does not.
  They differ on the initial (μ) half only: both are terminal (`fD_zero_isTerminal`,
  `padic_bottom_isTerminal`, `ZeroParadox/Multihomed/TreeObstructions.lean`), so the ν half is
  shared and #5 straddles the μ/ν root rather than sitting opposite #3.

**Cardinality does NOT separate (b).** Both `#5 = StateSpace 0` and `#3 = {0} ⊆ Q₂` are *subsingletons*,
at most one point (`bots_both_subsingleton`), and each is inhabited (the two `example`s after the
header of `ZeroParadox/Multihomed/TwoFacesBot.lean`), so each has exactly one point and the Axis-III
invariant that split #4 from #5 is silent here: the genuine separator for the #5↔#3 edge is polarity (initial vs not), not cardinality. Recorded by `bots_both_subsingleton` (at most one point
each) with the two one-point `example`s in `ZeroParadox/Multihomed/TwoFacesBot.lean`, so the finding is
honest about *which* wall does the work.

Edge (b) is an **obstruction (no-go) result** on the initial half: it proves a *separation*, not a
cross-domain identity. Edge (a) is not: no separating statement is proved for it, so of the two
cross-root pairs named here only (b) is machine-checked obstructed.
-/

namespace ZeroParadox

open CategoryTheory
open ZeroParadox ZeroParadox
open ZeroParadox ZeroParadox

/-! ## Edge (a) — #1 vs #3: two descent facts that hold together (no separator) -/

/-- The radii `2⁻ⁿ` of the p-adic descent (`q2Ball n = closedBall 0 (2⁻ⁿ)`) are strictly decreasing
    for all `n`. `Statement:` a fact about a real sequence; it does not mention `Q₂`, its balls or
    its floor. -/
theorem padic_descent_radii_strictAnti :
    StrictAnti (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) := by
  intro a b hab
  simp only
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
  omega

/-- **Edge (a), Axis I: two facts that hold together.** `Statement:` `<` on `Ordinal` is well-founded,
    and the real sequence `2⁻ⁿ` is strictly decreasing. The conjuncts share no variable and neither
    mentions `Q₂`, so this separates nothing; no Lean statement here separates the #1 and #3 floors. -/
theorem ordinal_wf_padic_descent_clash :
    WellFounded ((· < ·) : Ordinal → Ordinal → Prop) ∧
    StrictAnti (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) :=
  ⟨Ordinal.lt_wf, padic_descent_radii_strictAnti⟩

-- Statement: the well-founded carrier `Ordinal` also hosts a never-stabilizing strictly descending
-- chain of sets, so a non-terminating descent does not separate it from the p-adic floor.
example : WellFounded ((· < ·) : Ordinal → Ordinal → Prop) ∧
    StrictAnti (fun n : ℕ => Set.Ici (n : Ordinal)) := by
  refine ⟨Ordinal.lt_wf, fun a b hab => ?_⟩
  exact Set.Ici_ssubset_Ici.2 (by exact_mod_cast hab)

/-! ## Edge (b) — #5 (seam, initial) vs #3 (ν, non-initial limit floor) -/

/-- **Edge (b), cross-root obstruction (Axis II).** The #5 Hilbert seam `StateSpace 0` is **initial**
    in `ModuleCat ℂ` (the μ half of its zero-object straddle), while the #3 p-adic floor `{0} ⊆ Q₂` is
    **not initial** in `TopCat`. Both are terminal (`fD_zero_isTerminal`, `padic_bottom_isTerminal`),
    so they differ on the initial half only. -/
theorem seam_initial_padic_not_initial :
    Nonempty (Limits.IsInitial (fD_functor.obj 0)) ∧
    IsEmpty (Limits.IsInitial (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))) :=
  ⟨⟨fD_zero_isInitial⟩, ZeroParadox.padic_bottom_not_initial⟩

/-- Cardinality does NOT separate edge (b). `Statement:` `#5 = StateSpace 0` and `#3 = {0} ⊆ Q₂` are
    both subsingletons, at most one point each; that each is inhabited is not part of this statement
    (one-point witnesses: the two `example`s in `ZeroParadox/Multihomed/TwoFacesBot.lean`). So the
    Axis-III (cardinality) invariant is silent here — the genuine separator for #5↔#3 is polarity (`seam_initial_padic_not_initial`), not cardinality. -/
theorem bots_both_subsingleton :
    Subsingleton (StateSpace 0) ∧ Subsingleton (↥({(0 : Q₂)} : Set Q₂)) := by
  refine ⟨⟨fun a b => ?_⟩, ?_⟩
  · apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i
  · rw [Set.subsingleton_coe]
    exact Set.subsingleton_singleton

end ZeroParadox

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / `TopCat` / `ModuleCat` / p-adic libraries —
a library dependency, not a new commitment of these results. -/

section PurityCheck
open ZeroParadox

#print axioms padic_descent_radii_strictAnti
#print axioms ordinal_wf_padic_descent_clash
#print axioms seam_initial_padic_not_initial
#print axioms bots_both_subsingleton

end PurityCheck
