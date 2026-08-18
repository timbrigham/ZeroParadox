-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicTree
import ZeroParadox.Valuation.InfinitudeFloor
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Every node is a floor, literally: a genuine InfinitudeFloor at each node of the generic tree

## Engineer's Take

This is supposed to be the generic object, so I wanted every node to actually be a floor, not one we only
infer from self-similarity. No inferences is the solid plan. The floors behave the same way at every level
because each one is literally the same floor structure, built.

This was me wanting the generic object made literal, every node a floor, no inferences. Sometimes it helps to
work through this from the ground up. Much of what is here re-derives results the framework already has, and
that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

Constructs `boundaryFloor v : InfinitudeFloor End` for **every** node `v`, making the tree's
self-similarity a construction rather than a corollary of `PadicTree.adj_prefix_iff`. Capstone:
`every_node_is_a_floor`; the global floor is the case `v = []` (`boundaryFloor_nil_floor`).
**Honest scope:** per-node **defs**, not global `instance`s, and pairwise distinctness is **not**
asserted — role-sameness is the claim, never one identity. -/

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
`⊤`: the same floor structure recurs literally at every node of the generic tree.

`Reading:` **INVARIANT** (conjectural) — the framework reads this as the ratified **"iterative
bottoms"** picture made concrete: each node roots a floor *relative to its own subtree*, and
`boundaryFloor_nil_floor` below says the global floor `botEnd` is merely the empty-prefix case, so
**under the per-node measures `localCx v`, no node floor is distinguished** — each has complexity `⊤`
in its own subtree. ⚠ **The scoping is load-bearing.** Under the GLOBAL valuation `endVal`, `botEnd`
**is** distinguished: `botEnd_val_top : endVal botEnd = ⊤`
(`ZeroParadox/Valuation/PadicTree.lean`), while a floor below a prefix **containing a nonzero digit**
has finite `endVal`. ⚠ **A nonempty prefix is not enough** — an all-zero prefix gives
`localBotEnd v = botEnd`, so `endVal` is `⊤` there too. The discriminator is a **nonzero digit**,
and `zero_branch_same` / `one_branch_new` below prove it.
The non-distinction is a statement about the local measures, never about the carrier.

**A comparable shape holds in the ordinal carrier by a different mechanism** —
`nfp_seed_independent_below_epsilon0` (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) proves every seed at
or below ε₀ reaches ε₀, so no seed is distinguished within that range either.
⚠ **SHAPE, never instance-of:** this theorem runs on **self-similarity** (`shiftEnd` / `prependEnd`
shift-invariance), that one on **there being no fixed point of `ω^·` strictly below ε₀** — and the two
conclude **different propositions**, not one shared conclusion. `ℕ → Fin 2` is not `Ordinal`; a common
theorem across them would be a type boundary. Only the moral is shared. -/
theorem every_node_is_a_floor (v : List (Fin 2)) :
    (boundaryFloor v).cx (boundaryFloor v).floor = ⊤ :=
  infinitude_forces_infinite_complexity End (I := boundaryFloor v)

/-- The global boundary floor is the special case `v = []`: `localBotEnd [] = botEnd`. -/
theorem boundaryFloor_nil_floor : (boundaryFloor []).floor = botEnd := by
  funext n
  show localBotEnd [] n = botEnd n
  simp only [localBotEnd, prependEnd, List.length_nil]
  rw [if_neg (Nat.not_lt_zero n), Nat.sub_zero]

/-! ## § The discriminator is a nonzero digit — descending 0-ward is standing still

The two theorems below make the prose claim above checkable: a child's local floor is NEW only when
the step branches away. ⚠ The distinctness is **earned, not stipulated** — `localBotEnd` is
deliberately NOT injective. ⚠ Scope is the **0-spine**, not branching in general. Prior art
(`Nat.ofDigits_append`, `Turing.ListBlank`, Cobos & Navas) and what it settles:
`ZeroParadox/Valuation/LocalFloor.md`. -/

/-- `Statement:` the 0-branch gives back the SAME local floor: `localBotEnd (v ++ [0]) = localBotEnd v`.
    Descending 0-ward does not produce a new bottom. -/
theorem zero_branch_same (v : List (Fin 2)) :
    localBotEnd (v ++ [0]) = localBotEnd v := by
  funext n
  simp only [localBotEnd, prependEnd, List.length_append, List.length_cons,
             List.length_nil, botEnd]
  by_cases hn : n < v.length
  · rw [if_pos (by omega), if_pos hn, List.getD_append _ _ _ _ hn]
  · rw [if_neg hn]
    by_cases hn' : n < v.length + 1
    · have hv : n = v.length := by omega
      subst hv
      rw [if_pos (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp
    · rw [if_neg (by omega)]

/-- `Statement:` the 1-branch gives a DIFFERENT local floor: `localBotEnd (v ++ [1]) ≠ localBotEnd v`.
    They differ at position `|v|`, where the child carries digit 1 and the parent's tail is 0.

    `Reading:` taken with `zero_branch_same`, this QUALIFIES the framework's commitment that the
    snap-arc returns to a new bottom — it neither confirms nor refutes it. A new bottom is obtained
    exactly when the step branches away; 0-ward is standing still. -/
theorem one_branch_new (v : List (Fin 2)) :
    localBotEnd (v ++ [1]) ≠ localBotEnd v := by
  intro h
  have hv := congrFun h v.length
  simp only [localBotEnd, prependEnd, List.length_append, List.length_cons,
             List.length_nil, botEnd] at hv
  rw [if_pos (by omega), if_neg (by omega),
      List.getD_append_right _ _ _ _ (by omega)] at hv
  simp at hv

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms shiftEnd_prependEnd
#print axioms endVal_indicator
#print axioms boundaryFloor
#print axioms every_node_is_a_floor
#print axioms boundaryFloor_nil_floor
#print axioms zero_branch_same
#print axioms one_branch_new
end PurityCheck
