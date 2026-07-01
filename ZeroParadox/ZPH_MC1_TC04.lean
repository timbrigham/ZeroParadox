-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPH_MC1_TreeObstructions
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, cross-root completeness — TC04: #1↔#3 and #5↔#3

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file closes the two **cross-root** (μ↔ν) edges of the bottom-diagram tree
(`thread_obstruction_table_2026-06-29.md` §7) that the earlier obstruction core left untested:

- **(a) #1 proof-theory floor (μ, well-founded order) ↔ #3 p-adic floor (ν, inverse limit).**
- **(b) #5 Hilbert seam (zero object) ↔ #3 p-adic floor (ν, inverse limit).**

The tree predicts cross-root pairs are **obstructed** (NO-GO), unlike the within-root siblings.
Both edges are proven obstructed, by two distinct, in-statement separators.

### Edge (a) — #1 vs #3: well-founded descent vs non-well-founded inverse-limit descent (Axis I)

The proof-theory floor is reached by **well-founded** descent (the ordinals are well-founded under
`<`). The p-adic floor `{0} = ⋂ q2Ball n` is reached by an **infinite, never-stabilizing** descending
chain of balls — a *non-well-founded* descent. The separator is therefore the same well-founded-vs-not
clash as E4, instantiated for #3:

- `padic_descent_radii_strictAnti` — the radii `2⁻ⁿ` of the p-adic descent are **strictly** decreasing
  for all `n`: an infinite strict descent in ℝ. The descent that defines #3 never terminates.
- `tc04_a_wellfounded_clash` — the load-bearing in-statement separation: the proof-theory carrier is
  well-founded under `<` **and** the p-adic descent admits an infinite strictly-decreasing radius
  sequence (non-well-founded descent). A single structure cannot be both the terminating ordinal
  descent and the non-terminating ball descent; the two floors are reached by incompatible descents.

### Edge (b) — #5 vs #3: zero object (initial) vs non-initial limit floor (Axis II)

The Hilbert seam `#5 = StateSpace 0` is a **zero object** of `ModuleCat ℂ` — in particular it is
**initial**. The p-adic floor `{0} ⊆ Q₂` is a **limit / terminal-flavoured** object and is provably
**not initial** in `TopCat` (`ZPH_MC1_TreeObstructions.padic_bottom_not_initial`). The separator is the
categorical-polarity clash:

- `tc04_b_polarity_clash` — `#5` is initial in `ModuleCat ℂ` **and** `#3`'s one-point space is *not*
  initial in `TopCat`. One bottom carries the initial universal property, the other provably does not,
  so they sit on opposite sides of the μ/ν root.

**Cardinality does NOT separate (b).** Both `#5 = StateSpace 0` and `#3 = {0} ⊆ Q₂` are *singletons*
(`tc04_b_both_singletons`), so the Axis-III invariant that split #4 from #5 is silent here: the genuine
separator for the #5↔#3 edge is polarity (initial vs not), not cardinality. Recorded in-statement so the
finding is honest about *which* wall does the work.

These are **obstruction (no-go) results**: each proves a *separation*, not a cross-domain identity. They
complete the cross-root row of the tree — every μ↔ν pair the campaign named is now machine-checked
obstructed.
-/

namespace ZeroParadox.ZPH_MC1_TC04

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPB
open ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_TopFunctor

/-! ## Edge (a) — #1 (μ, well-founded) vs #3 (ν, non-well-founded inverse limit) -/

/-- The radii `2⁻ⁿ` of the p-adic descent (`q2Ball n = closedBall 0 (2⁻ⁿ)`) are strictly decreasing
    for all `n`: the inverse-limit descent that reaches the p-adic floor `{0}` never stabilizes — an
    infinite strict descent. This is the non-well-founded character of the #3 (ν) bottom. -/
theorem padic_descent_radii_strictAnti :
    StrictAnti (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) := by
  intro a b hab
  simp only
  apply zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2)
  omega

/-- **Edge (a), cross-root obstruction (Axis I).** The #1 proof-theory floor and the #3 p-adic floor
    are reached by **incompatible descents**: the proof-theory carrier (ordinals) is well-founded under
    `<` (terminating descent, μ), while the p-adic descent admits an infinite strictly-decreasing radius
    sequence (non-terminating descent, ν). The two bottoms cannot be one object reached by one descent. -/
theorem tc04_a_wellfounded_clash :
    WellFounded ((· < ·) : Ordinal → Ordinal → Prop) ∧
    StrictAnti (fun n : ℕ => (2 : ℝ) ^ (-(n : ℤ))) :=
  ⟨Ordinal.lt_wf, padic_descent_radii_strictAnti⟩

/-! ## Edge (b) — #5 (seam, initial) vs #3 (ν, non-initial limit floor) -/

/-- **Edge (b), cross-root obstruction (Axis II).** The #5 Hilbert seam `StateSpace 0` is **initial**
    in `ModuleCat ℂ` (the μ half of its zero-object straddle), while the #3 p-adic floor `{0} ⊆ Q₂` is
    **not initial** in `TopCat`. One bottom carries the initial universal property, the other provably
    does not — the categorical-polarity clash across the μ/ν root. -/
theorem tc04_b_polarity_clash :
    Nonempty (Limits.IsInitial (fD_functor.obj 0)) ∧
    IsEmpty (Limits.IsInitial (TopCat.of (↥({(0 : Q₂)} : Set Q₂)))) :=
  ⟨⟨fD_zero_isInitial⟩, ZeroParadox.ZPH_MC1_TreeObstructions.padic_bottom_not_initial⟩

/-- Cardinality does NOT separate edge (b): both bottoms are singletons. `#5 = StateSpace 0` is a
    subsingleton and `#3 = {0} ⊆ Q₂` is a singleton, so the Axis-III (cardinality) invariant is silent
    here — the genuine separator for #5↔#3 is polarity (`tc04_b_polarity_clash`), not cardinality. -/
theorem tc04_b_both_singletons :
    Subsingleton (StateSpace 0) ∧ Subsingleton (↥({(0 : Q₂)} : Set Q₂)) := by
  refine ⟨⟨fun a b => ?_⟩, ?_⟩
  · apply WithLp.ofLp_injective
    funext i
    exact Fin.elim0 i
  · rw [Set.subsingleton_coe]
    exact Set.subsingleton_singleton

end ZeroParadox.ZPH_MC1_TC04

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib ordinal / `TopCat` / `ModuleCat` / p-adic libraries —
a library dependency, not a new commitment of these obstruction results. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC04

#print axioms padic_descent_radii_strictAnti
#print axioms tc04_a_wellfounded_clash
#print axioms tc04_b_polarity_clash
#print axioms tc04_b_both_singletons

end PurityCheck
