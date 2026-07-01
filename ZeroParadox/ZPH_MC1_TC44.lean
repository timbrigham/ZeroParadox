-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_TC10
import ZeroParadox.ZPH_MC1_TC35
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC44 — co-occurrence of four ambient bottom-facts (thin: new fact is generic)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file bundles four facts about bottom-diagram nodes #1 (the well-founded proof-theory order
floor `0 : ℕ`) and #3 (the p-adic ν-limit floor `{0} ⊆ Q₂`). **The only NEW Lean content over
TC10+TC35 is a generic poset triviality** — see the honest-scope note below. The file is retained as
a thin, accurately-labeled co-occurrence record, not as a new structural result.

**Re-exported from TC35.** `ZPH_MC1_TC35` witnessed an *order-least* split: node #1 carries
`IsLeast (Set.univ : Set ℕ) 0` (a least element of its ambient order), while node #3 carries a least
element *only on the image of its norm* (`IsLeast (Set.range (‖·‖ : Q₂ → ℝ)) 0`) — not as an
order-bottom of `Q₂`.

**Re-exported from TC10.** `ZPH_MC1_TC10.floorConeIsLimit` proves the snap floor `{0} ⊆ Q₂` is a
genuine categorical `IsLimit` of the inverse system `fB_functor : ℕᵒᵖ ⥤ TopCat`. We re-expose it
here as `tc44_padic_floor_isLimit` (`Nonempty (IsLimit floorCone)`).

**The new (generic) fact.** In the `ℕ` preorder category the order floor `0` is the *initial* object
but is **not terminal**: there is no morphism `1 ⟶ 0`, because `¬ ((1 : ℕ) ≤ 0)`. This is in the
statement `tc44_no_hom_into_nat_floor : IsEmpty ((1 : ℕ) ⟶ (0 : ℕ))`, and from it
`tc44_nat_floor_not_isTerminal : IsEmpty (Limits.IsTerminal (0 : ℕ))`.

### What the file actually witnesses (load-bearing, in the theorem statements)

The bundle `tc44_floor_facts_cooccur` is a pure conjunction of four pre-existing-or-generic facts:
1. `Nonempty (IsLimit ZPH_MC1_TC10.floorCone)` — #3 sits at a real limit (TC10).
2. `IsEmpty (Limits.IsTerminal (0 : ℕ))` — `0` is not terminal in the `ℕ` preorder (new, generic).
3. `IsLeast (Set.univ : Set ℕ) 0` ∧ `IsLeast (Set.range ‖·‖) 0` (TC35).

The conjunction proves **co-occurrence** of these four facts. It does **not** prove any relation
connecting them: there is no "duality" predicate in any statement, and the bundling establishes none.

### Honest scope — the new fact is a generic triviality (THIN)

The single new Lean fact — `0 : ℕ` is not terminal in the `ℕ` preorder — is a **generic poset
triviality**: the bottom of any nontrivial poset is initial, never terminal (it is just a
category-theory restatement of `¬ ((1 : ℕ) ≤ 0)`, i.e. "0 is not the top of ℕ"). It is correctly
stated but is **not a framework-specific finding about node #1**. The analogous "not terminal" fact
for a different object (`fC_functor.obj 0`) was already proved in TC18.

Earlier drafts of this file framed the bundle as a "dual cross-root asymmetry," calling the
poset-bottom obstruction a "dual partner" of the p-adic `IsLimit`. **That framing is retracted.** The
four facts live in *incommensurable ambients* (an `ℕ` preorder category, `TopCat`, and the orders on
`ℕ`/`ℝ`); there is no single category in which an order-least property and a limit property are
directly comparable, so the bundle witnesses no duality. The honest reading is **four ambient facts
that happen to co-occur**, with one of them generic.
-/

namespace ZeroParadox.ZPH_MC1_TC44

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPB

/-! ## Re-expose TC10's genuine `IsLimit` cone for the p-adic floor. -/

/-- Node #3 (the p-adic floor `{0} ⊆ Q₂`) sits at a **genuine categorical limit** of the inverse
system `fB_functor : ℕᵒᵖ ⥤ TopCat` (TC10's cone). This is the native limit (ν) universal property of
#3. Re-exported verbatim from TC10. -/
theorem tc44_padic_floor_isLimit :
    Nonempty (IsLimit ZeroParadox.ZPH_MC1_TC10.floorCone) :=
  ⟨ZeroParadox.ZPH_MC1_TC10.floorConeIsLimit⟩

/-! ## The new (generic) fact: the order floor `0 : ℕ` is initial but NOT terminal. -/

/-- The morphism-level obstruction: there is **no morphism `1 ⟶ 0`** in the `ℕ` preorder category,
because `¬ ((1 : ℕ) ≤ 0)`. A terminal object must receive a morphism from every object; `0` does not
receive one from `1`. -/
theorem tc44_no_hom_into_nat_floor : IsEmpty ((1 : ℕ) ⟶ (0 : ℕ)) :=
  ⟨fun f => absurd (leOfHom f) (by decide)⟩

/-- **The new Lean content over TC10+TC35 — a generic poset triviality.** The order floor `0 : ℕ` is
**not terminal** in the `ℕ` preorder category: a terminal `0` would manufacture a morphism `1 ⟶ 0`,
i.e. `1 ≤ 0`, which is false. This is true of the bottom of any nontrivial poset (the bottom is
initial, never terminal); it is not a framework-specific fact about node #1. -/
theorem tc44_nat_floor_not_isTerminal : IsEmpty (IsTerminal (0 : ℕ)) :=
  ⟨fun t => tc44_no_hom_into_nat_floor.false (t.from (1 : ℕ))⟩

/-! ## The four ambient facts, bundled (co-occurrence only — proves no relation between them). -/

/-- **TC44 bundle — co-occurrence of four ambient bottom-facts.** This is a pure conjunction; it
proves the four facts *hold together*, not that any structural relation connects them.

- #3 sits at a real limit: `Nonempty (IsLimit floorCone)` (TC10).
- `0 : ℕ` is not terminal in the `ℕ` preorder: `IsEmpty (IsTerminal (0 : ℕ))` (new; generic poset
  triviality — see honest scope).
- order-least split: `IsLeast univ 0` ∧ `IsLeast (range ‖·‖) 0` (TC35).

**Honest scope:** the four facts live in incommensurable ambients (`ℕ` preorder, `TopCat`, orders on
`ℕ`/`ℝ`); there is no single category in which they are directly comparable, and no "duality"
predicate appears in the statement. This bundle witnesses co-occurrence, nothing more. -/
theorem tc44_floor_facts_cooccur :
    Nonempty (IsLimit ZeroParadox.ZPH_MC1_TC10.floorCone)
      ∧ IsEmpty (IsTerminal (0 : ℕ))
      ∧ IsLeast (Set.univ : Set ℕ) 0
      ∧ IsLeast (Set.range (fun x : Q₂ => ‖x‖)) 0 :=
  ⟨tc44_padic_floor_isLimit,
   tc44_nat_floor_not_isTerminal,
   ZeroParadox.ZPH_MC1_TC35.tc35_nat_floor_isLeast,
   ZeroParadox.ZPH_MC1_TC35.tc35_q2_floor_isLeast_norm⟩

end ZeroParadox.ZPH_MC1_TC44

/-! ## Axiom Purity Check

`Classical.choice` is expected via Mathlib's `TopCat` / limits / metric machinery (inherited from
TC10 and the ZP-B topology layer); it is a library dependency, not a new commitment. The
`IsTerminal`-obstruction results carry only the standard footprint. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC44

#print axioms tc44_padic_floor_isLimit
#print axioms tc44_no_hom_into_nat_floor
#print axioms tc44_nat_floor_not_isTerminal
#print axioms tc44_floor_facts_cooccur

end PurityCheck
