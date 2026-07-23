import ZeroParadox.Valuation.PadicTree
import ZeroParadox.Valuation.InfinitudeFloor
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Every node is a floor, literally: a genuine InfinitudeFloor at each node of the generic tree

## Engineer's Take

This is supposed to be the generic object, so I wanted every node to actually be a floor, not one we only
infer from self-similarity. No inferences is the solid plan. The floors behave the same way at every level
because each one is literally the same floor structure, built.

---

## Formal Overview (AI-assisted)

`PadicTree.adj_prefix_iff` proves the tree is self-similar (every vertex roots an exact copy), so *by
inference* every node has a local floor that behaves like the global one. Tim's directive: the tree is the
**generic object**, so make it **literal — no inferences**. This file constructs, for **every** node
`v : List (Fin 2)`, a genuine `InfinitudeFloor End`:

* `boundaryFloor v : InfinitudeFloor End` — floor `= localBotEnd v` (v's digits, then all zeros: the local
  bottom of the subtree below `v`), members `= localMember v n` (v's digits, then a single `1` at relative
  depth `n`: the climbing local nulls), complexity `= localCx v` (the boundary valuation measured **below**
  `v`, i.e. `endVal` of the tail after `v`).

Every field is discharged by construction: `member_ne_floor` (a member differs from the floor at position
`|v|+n`), `cx_member_strictMono` (`localCx v (localMember v n) = n`, climbing), and `cx_floor_eq_iSup` (the
local floor has infinite complexity `⊤`, driven by the members climbing — `localCx v (localBotEnd v) = ⊤`).

`every_node_is_a_floor` is the capstone: for **all** `v`, the constructed floor's complexity is `⊤` — every
node literally roots a floor of infinite complexity, the same structure at every level. The global boundary
floor is the special case `v = []` (`boundaryFloor_nil_floor`). This is the self-similarity made a
construction rather than a corollary of `adj_prefix_iff`.

**Honest scope.** These are genuine per-node `InfinitudeFloor` **defs** (witnesses), parametrized by `v`, not
competing global `instance`s on `End`. The local floors are all of one *kind* and behave identically; that
they are pairwise distinct where the prefixes differ is not asserted here (role-sameness is the claim, not a
single identity — the family/instance reading).
-/

namespace ZeroParadox

/-! ### § I. Prepend and shift on boundary ends. -/

/-- Prepend a finite prefix `v` to a boundary end `y`: `v`'s digits, then `y`. -/
def prependEnd (v : List (Fin 2)) (y : End) : End :=
  fun n => if n < v.length then v.getD n 0 else y (n - v.length)

/-- Shift a boundary end down by `m` positions (drop the first `m` digits). -/
def shiftEnd (m : ℕ) (x : End) : End := fun k => x (m + k)

/-- Shifting past a prepended prefix recovers the tail: `shiftEnd |v| (prependEnd v y) = y`. -/
theorem shiftEnd_prependEnd (v : List (Fin 2)) (y : End) :
    shiftEnd v.length (prependEnd v y) = y := by
  funext k
  simp only [shiftEnd, prependEnd]
  rw [if_neg (by omega : ¬ v.length + k < v.length)]
  congr 1
  omega

/-! ### § II. The local floor, members, and complexity at a node `v`. -/

/-- The local bottom at node `v`: `v`'s digits, then all zeros (the floor of the subtree below `v`). -/
def localBotEnd (v : List (Fin 2)) : End := prependEnd v botEnd

/-- The local nulls at node `v`: `v`'s digits, then a single `1` at relative depth `n`. -/
def localMember (v : List (Fin 2)) (n : ℕ) : End :=
  prependEnd v (fun k => if k = n then 1 else 0)

/-- The local complexity at node `v`: the boundary valuation of the tail after `v`. -/
noncomputable def localCx (v : List (Fin 2)) (x : End) : ℕ∞ := endVal (shiftEnd v.length x)

/-! ### § III. Support lemmas. -/

/-- `⨆ n, ↑n = ⊤` in `ℕ∞` — the climbing complexities are unbounded. -/
private theorem iSup_natCast_top : ⨆ n : ℕ, (n : ℕ∞) = ⊤ := by
  rw [iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  exact ⟨b + 1, by exact_mod_cast Nat.lt_succ_self b⟩

/-- The boundary valuation of a single-`1`-at-`n` indicator is `n`. -/
theorem endVal_indicator (n : ℕ) :
    endVal (fun k => if k = n then (1 : Fin 2) else 0) = (n : ℕ∞) := by
  have hset : {k | (if k = n then (1 : Fin 2) else 0) ≠ 0} = {n} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    by_cases hk : k = n
    · simp [hk]
    · simp [hk]
  unfold endVal
  rw [hset, Set.image_singleton, sInf_singleton]

/-- The local floor has infinite complexity: `localCx v (localBotEnd v) = ⊤`. -/
theorem localCx_bot (v : List (Fin 2)) : localCx v (localBotEnd v) = ⊤ := by
  unfold localCx localBotEnd
  rw [shiftEnd_prependEnd]
  exact botEnd_val_top

/-- The local complexity of member `n` is exactly `n` (climbing). -/
theorem localCx_member (v : List (Fin 2)) (n : ℕ) :
    localCx v (localMember v n) = (n : ℕ∞) := by
  unfold localCx localMember
  rw [shiftEnd_prependEnd]
  exact endVal_indicator n

/-! ### § IV. The genuine per-node InfinitudeFloor. -/

/-- **Every node is a floor, constructed.** For every node `v`, the subtree below `v` carries a genuine
`InfinitudeFloor End`: floor `= localBotEnd v`, members the climbing local nulls, floor complexity `⊤`. A
def (a witness) per node, not a global instance. -/
@[reducible] noncomputable def boundaryFloor (v : List (Fin 2)) : InfinitudeFloor End where
  floor := localBotEnd v
  cx := localCx v
  member := localMember v
  member_ne_floor := by
    intro n hcontra
    have hc := congrFun hcontra (v.length + n)
    have h1 : localMember v n (v.length + n) = 1 := by
      simp only [localMember, prependEnd]
      rw [if_neg (by omega : ¬ v.length + n < v.length), Nat.add_sub_cancel_left]
      simp
    have h0 : localBotEnd v (v.length + n) = 0 := by
      simp only [localBotEnd, prependEnd]
      rw [if_neg (by omega : ¬ v.length + n < v.length)]
      simp [botEnd]
    rw [h1, h0] at hc
    exact absurd hc (by decide)
  cx_member_strictMono := by
    intro a b hab
    show localCx v (localMember v a) < localCx v (localMember v b)
    rw [localCx_member, localCx_member]
    exact_mod_cast hab
  cx_floor_eq_iSup := by
    rw [localCx_bot]
    have hcong : (⨆ n, localCx v (localMember v n)) = ⨆ n : ℕ, (n : ℕ∞) :=
      iSup_congr (fun n => localCx_member v n)
    rw [hcong]
    exact iSup_natCast_top.symm

/-! ### § V. The capstone: every node roots a floor of infinite complexity. -/

/-- **Every node is a floor of infinite complexity.** For all `v`, the constructed floor's complexity is
`⊤`: the same floor structure recurs literally at every node of the generic tree. -/
theorem every_node_is_a_floor (v : List (Fin 2)) :
    (boundaryFloor v).cx (boundaryFloor v).floor = ⊤ :=
  infinitude_forces_infinite_complexity End (I := boundaryFloor v)

/-- The global boundary floor is the special case `v = []`: `localBotEnd [] = botEnd`. -/
theorem boundaryFloor_nil_floor : (boundaryFloor []).floor = botEnd := by
  funext n
  show localBotEnd [] n = botEnd n
  simp only [localBotEnd, prependEnd, List.length_nil]
  rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero]

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms shiftEnd_prependEnd
#print axioms endVal_indicator
#print axioms boundaryFloor
#print axioms every_node_is_a_floor
#print axioms boundaryFloor_nil_floor
end PurityCheck
