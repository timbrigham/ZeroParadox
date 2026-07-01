-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, edge TC35 — root-asymmetry test: #1 (μ order-floor) vs #3 (ν p-adic limit)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This file runs one go/no-go cycle on the **μ/ν root asymmetry** between two bottom-diagram nodes:

- **Node #1** — the well-founded proof-theory floor, taken as `0 : ℕ`. Its *native* universal
  property is **order-initiality**: `0` is the least element, `∀ n, (0 : ℕ) ≤ n`. This is the μ
  witness (`IsLeast`, `OrderBot.bot_le`): a least element / colimit-style floor.

- **Node #3** — the p-adic floor `{0} ⊆ Q₂` (`= ℚ_[2]`). Its native universal property is a
  **topological limit** (`fB_bottom_is_limit`: `⋂ₙ B(0, 2⁻ⁿ) = {0}`), the ν witness. `0 : Q₂` is the
  unique point of **minimal norm**, not a minimal *order* element: `Q₂` carries **no** `LinearOrder`
  instance making `0` order-least compatible with its valuation.

### What the file actually witnesses (load-bearing, in the theorem statements)

**GO side — the asymmetry holds in the precise registered form:**

1. `tc35_nat_floor_isLeast` — `IsLeast (Set.univ : Set ℕ) 0`: node #1's order-bottom μ-witness, a real
   least element of the whole order.
2. `tc35_q2_floor_isLeast_norm` — `IsLeast (Set.range (‖·‖ : Q₂ → ℝ)) 0`: node #3 carries a least
   element **only on the image of its norm**, i.e. in the *valuation/topological* register, not in an
   order on `Q₂` itself. This is the honest minimal-norm fact (`norm_zero` + `norm_nonneg`).
3. `tc35_q2_norm_floor_unique` — `‖x‖ = 0 ↔ x = 0`: the minimal-norm point of `Q₂` is exactly the
   topological floor `0`, so the only "least" structure #3 supports lives on the metric, mapping the
   floor through `‖·‖`, not as an order-bottom of `Q₂`.

The asymmetry is therefore witnessed concretely: #1's least element is a least element **of its
ambient order** (`Set.univ`), whereas #3's least element is a least element **of the norm image in ℝ**
— two different registers (order vs valuation). #1 supplies an order-initial (μ) bottom natively; #3
supplies it only after pushing through the non-archimedean norm into ℝ (the ν/limit register).

### Honest scope (what is interpretation, not Lean content)

The Lean does **not** prove "`Q₂` has no `LinearOrder` with `0` least" as a theorem (a negative
existential over all order instances). What it proves is the *positive* asymmetry: #1's bottom is
order-native (`IsLeast univ 0`), #3's bottom is norm-native (`IsLeast (range ‖·‖) 0`, with the
floor recovered by `‖x‖ = 0 ↔ x = 0`). The claim "the two roots are separated by which universal
property is native" is the *interpretation* of this concrete register split; it is not a single
no-such-order Lean theorem. The NO-GO obstruction (that #3 *also* carries an order-bottom collapsing
the asymmetry) does **not** prove: there is no `LinearOrder` on `Q₂` from the standard library
matching `0`-least, and the only least-element structure available is the norm register — which is the
GO outcome, not a collapse.
-/

namespace ZeroParadox.ZPH_MC1_TC35

open ZeroParadox.ZPB

/-! ## GO side: node #1's order-bottom μ-witness -/

/-- Node #1 (`0 : ℕ`), the well-founded proof-theory floor, is the **order-least** element of its
ambient order — its native μ (initial/colimit) universal property as a least element. -/
theorem tc35_nat_floor_isLeast : IsLeast (Set.univ : Set ℕ) 0 :=
  ⟨Set.mem_univ 0, fun n _ => Nat.zero_le n⟩

/-! ## GO side: node #3's bottom is least only in the norm/valuation register -/

/-- The minimal-norm point of `Q₂` is exactly the topological floor `0`: `‖x‖ = 0 ↔ x = 0`.
So the only "least" structure node #3 supports recovers the floor through the **norm**, not through an
order on `Q₂`. -/
theorem tc35_q2_norm_floor_unique (x : Q₂) : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

/-- Node #3 (`{0} ⊆ Q₂`) carries a least element **only on the image of its norm** in `ℝ`: `0` is the
least value of `‖·‖ : Q₂ → ℝ`. This is the valuation/topological register (`norm_nonneg`,
`norm_zero`), distinct from an order-bottom of `Q₂` itself. -/
theorem tc35_q2_floor_isLeast_norm :
    IsLeast (Set.range (fun x : Q₂ => ‖x‖)) 0 := by
  constructor
  · exact ⟨0, norm_zero⟩
  · rintro r ⟨x, rfl⟩
    exact norm_nonneg x

/-! ## The asymmetry, bundled.

#1 supplies an order-initial bottom in its **ambient order** (`Set.univ : Set ℕ`).
#3 supplies a least element only in the **norm image** (`Set.range (‖·‖ : Q₂ → ℝ)`), with the floor
recovered by `‖x‖ = 0 ↔ x = 0`. Two different registers: order (μ-native, #1) vs valuation (ν-limit,
#3). -/
theorem tc35_root_asymmetry :
    IsLeast (Set.univ : Set ℕ) 0
      ∧ IsLeast (Set.range (fun x : Q₂ => ‖x‖)) 0
      ∧ (∀ x : Q₂, ‖x‖ = 0 ↔ x = 0) :=
  ⟨tc35_nat_floor_isLeast, tc35_q2_floor_isLeast_norm, tc35_q2_norm_floor_unique⟩

section PurityCheck
#print axioms tc35_nat_floor_isLeast
#print axioms tc35_q2_norm_floor_unique
#print axioms tc35_q2_floor_isLeast_norm
#print axioms tc35_root_asymmetry
end PurityCheck

end ZeroParadox.ZPH_MC1_TC35
