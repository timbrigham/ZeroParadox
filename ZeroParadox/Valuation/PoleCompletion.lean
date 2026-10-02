-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicTree
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Valuation.LocalFloor
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The pole completion: the floor is a genuine self-application fixed point (the Quine atom on the tree)

## Engineer's Take

I asked what if the root's third edge were both of the other two at once. If the way back up is just the two
branches folded together, then the floor points back at itself, and on the tree's boundary that fold is a
real self-application whose only fixed point is the floor.

This was the what-if, the root's third edge being both of the other two at once. Sometimes it helps to work
through this from the ground up. Much of what is here re-derives results the framework already has, and that is
fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

Tim's question: "what if the third degree at the root were both the other two at once?" The rooted 2-adic
tree's root has degree 2 (`BoundaryGap.root_adj_iff`); its missing third edge points ∞-ward (toward the ball
*containing* ℤ₂). Reading that ∞-ward edge as the two 0-ward branches **folded** is exactly `rInv`
(`PoleCornersBridge.swap_is_rInv`, `z ↦ 1/z`), the pole `0 = ∞` — so this completion closes the tree into
the **sphere**, not into the Bruhat-Tits **tree** (an external parent) of `BoundaryGap`.

The self-referential content of that fold is here, and it is **a genuine typeclass instance**:

* `End = ℕ → Fin 2` (the boundary) is a `ZPSemilattice` pointwise — `Fin 2` is one (join = max, ⊥ = 0), and
  the axioms lift pointwise (`instZPSemilatticeEnd`), with ⊥ = `botEnd`, the floor.
* `boundaryDouble` is ×2 in digit expansion (shift right, insert 0 at position 0) — the exact combinatorial
  mirror of `SelfApp.q2SelfApp` (×2 on ℚ₂).
* Its **unique** fixed point is the floor (`boundaryDouble_unique_fp`), so `instAbstractSelfAppEnd :
  AbstractSelfApp End` holds: a self-map whose only fixed point is ⊥. Via `SelfApp.toAFAStructure`, `End`
  thereby also carries the AFA / Quine-atom structure.

**The delta from ℚ₂ (the point of the exercise).** `ZeroParadox/Computability/SelfApp.lean` records (the note beginning "ℚ_[2] is a field, not a ZPSemilattice") that ℚ₂ — *a field, not a
ZPSemilattice* — could NOT be an `AbstractSelfApp` instance; its ×2/0 fixed point is proved only as a
standalone parallel. The tree boundary clears exactly that bar: it *is* a semilattice, so the same
fixed-point fact is a **genuine instance**. Self-reference closing at the floor is not merely analogous to
the Quine atom's **structural** fixed point here — it is one, by the framework's own definition. (The literal
set-membership `⊥ = {⊥}` stays a metatheoretic commitment, as everywhere; this is the structural
self-application face, the axiom-free `t_exec` half.)

**Honest fence.** The tree↔ℚ₂ digit isomorphism is not formalized in this file, so the mirror to `q2SelfApp`
is a proved PARALLEL (same map, same unique fixed point), never a Lean `=`; and the "both children at once
= rInv = pole" reading is the interpretation, anchored by the proved `swap_is_rInv`, not a new graph theorem.
No cross-type identity anywhere.
-/

namespace ZeroParadox

open ZPSemilattice

/-- The boundary self-application: ×2 in 2-adic digit expansion = shift right, inserting `0` at position 0.
The exact combinatorial mirror of `SelfApp.q2SelfApp` (×2 on ℚ₂). -/
def boundaryDouble (x : End) : End := fun n => match n with | 0 => 0 | k + 1 => x k

/-- The floor `botEnd` is a fixed point of ×2 (doubling fixes 0). -/
theorem boundaryDouble_botEnd : boundaryDouble botEnd = botEnd := by
  funext n; cases n <;> rfl

/-- **The floor is the UNIQUE fixed point of the boundary self-application.** The only end fixed by ×2 is
`botEnd`: self-reference closes exactly at the floor. Mirrors `SelfApp.q2_unique_fp` (0 unique fixed point
of ×2 in ℚ₂). -/
theorem boundaryDouble_unique_fp (x : End) (h : boundaryDouble x = x) : x = botEnd := by
  funext n
  simp only [botEnd]
  induction n with
  | zero => exact (congrFun h 0).symm
  | succ k ih => exact (congrFun h (k + 1)).symm.trans ih

/-- The boundary `End = ℕ → Fin 2` is a `ZPSemilattice` pointwise (join = max, ⊥ = `botEnd`). Unlike ℚ₂
(a field), the tree boundary IS a semilattice, so it can host a genuine `AbstractSelfApp` instance. -/
instance instZPSemilatticeEnd : ZPSemilattice End where
  join x y := fun n => max (x n) (y n)
  bot := botEnd
  join_assoc := by intro x y z; funext n; exact max_assoc _ _ _
  join_comm := by intro x y; funext n; exact max_comm _ _
  join_idem := by intro x; funext n; exact max_self _
  bot_join := by
    intro x; funext n
    show max (botEnd n) (x n) = x n
    simp only [botEnd]
    exact max_eq_right (Fin.zero_le _)

/-- **The genuine instance.** The tree boundary is an `AbstractSelfApp`: the self-application ×2
(`boundaryDouble`) has the floor `botEnd` as its unique fixed point. Where ℚ₂ could only be a standalone
parallel (not a semilattice), `End` IS an instance — self-reference closing at the floor as an honest
typeclass instance, the Quine-atom shape realized on the tree's own boundary. -/
instance instAbstractSelfAppEnd : AbstractSelfApp End where
  selfApp := boundaryDouble
  fixed_bot := boundaryDouble_botEnd
  unique_fp := boundaryDouble_unique_fp

/-! ### Iterating the boundary self-application: depth-`k` cells around `botEnd`

Classical: the digit form of `2ᵏℤ₂`, the closed ball of radius `2⁻ᵏ` around `0`. The ball-chart relative
of `iInter_range_iterate_boundaryDouble` is `fB_bottom_is_limit` (`ZeroParadox/Valuation/TopFunctor.lean`).
`Reading:` `k` applications of the self-application are the depth-`k` cell around the all-zeros end —
one map for tower step and cell depth. -/

/-- The depth-`k` cell around the all-zeros end: the ends whose first `k` digits are `0`. -/
def boundaryCell (k : ℕ) : Set End := {x | ∀ i < k, x i = 0}

/-- `Statement:` `k` applications of `boundaryDouble` put `k` zeros in front. -/
theorem iterate_boundaryDouble (k : ℕ) (x : End) (n : ℕ) :
    (boundaryDouble^[k] x) n = if n < k then 0 else x (n - k) := by
  induction k generalizing n with
  | zero => rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero]; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    cases n with
    | zero => rw [if_pos (Nat.succ_pos k)]; rfl
    | succ m =>
      show (boundaryDouble^[k] x) m = _
      rw [ih m]
      by_cases h : m < k
      · rw [if_pos h, if_pos (by omega : m + 1 < k + 1)]
      · rw [if_neg h, if_neg (by omega : ¬ (m + 1 < k + 1)), show m + 1 - (k + 1) = m - k by omega]

-- `Statement:` dropping the first `k` digits (`shiftEnd`) undoes `k` applications.
example (k : ℕ) (x : End) : shiftEnd k (boundaryDouble^[k] x) = x := by
  funext j
  simp only [shiftEnd, iterate_boundaryDouble]
  rw [if_neg (by omega)]; congr 1; omega

/-- `Statement:` the image of `k` applications of `boundaryDouble` is exactly `boundaryCell k`. -/
theorem range_iterate_boundaryDouble (k : ℕ) : Set.range (boundaryDouble^[k]) = boundaryCell k := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ i hi
    rw [iterate_boundaryDouble, if_pos hi]
  · intro hy
    refine ⟨shiftEnd k y, funext fun n => ?_⟩
    rw [iterate_boundaryDouble]
    by_cases h : n < k
    · rw [if_pos h]; exact (hy n h).symm
    · rw [if_neg h]; simp only [shiftEnd]; congr 1; omega

/-- `Statement:` the intersection over `k` of those images is `{botEnd}`. -/
theorem iInter_range_iterate_boundaryDouble :
    (⋂ k, Set.range (boundaryDouble^[k])) = {botEnd} := by
  ext y
  simp only [Set.mem_iInter, range_iterate_boundaryDouble, boundaryCell, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro h; funext n; exact h (n + 1) n (Nat.lt_succ_self n)
  · rintro rfl k i _; rfl

-- `Statement:` `boundaryDouble` is not constant: it moves the single-`1`-at-`0` end.
example : boundaryDouble (fun k => if k = 0 then 1 else 0) ≠ fun k => if k = 0 then 1 else 0 := by
  intro h
  have := congrFun h 1
  simp [boundaryDouble] at this

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms boundaryDouble_botEnd
#print axioms boundaryDouble_unique_fp
#print axioms instAbstractSelfAppEnd
#print axioms boundaryCell
#print axioms iterate_boundaryDouble
#print axioms range_iterate_boundaryDouble
#print axioms iInter_range_iterate_boundaryDouble
end PurityCheck
