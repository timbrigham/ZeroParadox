-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): each local tower of `LocalFloor` is the orbit of one local push, whose only fixed point is the local floor. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Interleave
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Local towers: the local push at every node, and which nodes give distinct towers

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

"what you're talking about is literally the state transition from being a noun to a verb."

---

## Formal Overview (AI-assisted)
`localPush v` keeps the prefix `v` and doubles the tail: its orbit is the tower at `v`, its only fixed
point is `localBotEnd v` (`localPush_unique_fp`), and below `v` it is conjugate to `boundaryDouble`
(`subtreeOrderIso_conj`). Canonical towers are disjoint (`canonTower_unique`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ### § I. Formulas for the `LocalFloor` objects. -/

/-- `Statement:` `localBotEnd v m = v.getD m 0`. -/
theorem localBotEnd_eq_getD (v : List (Fin 2)) : localBotEnd v = fun m => v.getD m 0 := by
  funext m
  show (if m < v.length then v.getD m 0 else botEnd (m - v.length)) = v.getD m 0
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega)]; rfl

theorem localBotEnd_apply (v : List (Fin 2)) (m : ℕ) : localBotEnd v m = v.getD m 0 := by
  rw [localBotEnd_eq_getD]

/-- `Statement:` the digits of `localMember v n`. -/
theorem localMember_apply (v : List (Fin 2)) (n m : ℕ) :
    localMember v n m = if m < v.length then v.getD m 0 else if m = v.length + n then 1 else 0 := by
  show (if m < v.length then v.getD m 0 else (if m - v.length = n then (1 : Fin 2) else 0)) = _
  by_cases h : m < v.length
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases h2 : m = v.length + n
    · rw [ite_eq_left (by omega), ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2]

theorem localMember_at (v : List (Fin 2)) (n : ℕ) : localMember v n (v.length + n) = 1 := by
  rw [localMember_apply, ite_eq_right (by omega), ite_eq_left rfl]

theorem localMember_off (v : List (Fin 2)) (n m : ℕ) (h1 : v.length ≤ m) (h2 : m ≠ v.length + n) :
    localMember v n m = 0 := by
  rw [localMember_apply, ite_eq_right (by omega), ite_eq_right h2]

theorem localMember_pre (v : List (Fin 2)) (n m : ℕ) (h : m < v.length) :
    localMember v n m = v.getD m 0 := by
  rw [localMember_apply, ite_eq_left h]

/-- `Statement:` `localMember v` is one-to-one. -/
theorem localMember_injective (v : List (Fin 2)) : Function.Injective (localMember v) := by
  intro a b h
  have := congrFun h (v.length + a)
  rw [localMember_at] at this
  by_contra hab
  rw [localMember_off v b _ (by omega) (by omega)] at this
  exact absurd this (by decide)

/-- `Statement:` `localMember [] k = unitEnd k`. -/
theorem localMember_nil_eq_unitEnd (k : ℕ) : localMember [] k = unitEnd k := by
  funext m; rw [localMember_apply]; simp [unitEnd]

/-! ### § II. Each local tower is the orbit of a local push. -/

/-- The local push at node `v`: keep the prefix `v`, apply `boundaryDouble` to the tail. -/
def localPush (v : List (Fin 2)) (x : End) : End :=
  prependEnd v (boundaryDouble (shiftEnd v.length x))

/-- `Statement:` `localPush v (prependEnd v y) = prependEnd v (boundaryDouble y)`. -/
theorem localPush_prependEnd (v : List (Fin 2)) (y : End) :
    localPush v (prependEnd v y) = prependEnd v (boundaryDouble y) := by
  unfold localPush; rw [shiftEnd_prependEnd]

/-- `Statement:` `localPush v (localMember v n) = localMember v (n + 1)`. -/
theorem localPush_member (v : List (Fin 2)) (n : ℕ) :
    localPush v (localMember v n) = localMember v (n + 1) := by
  unfold localMember
  rw [localPush_prependEnd]
  exact congrArg (prependEnd v) (boundaryDouble_unitEnd n)

/-- `Statement:` `(localPush v)^[n] (localMember v 0) = localMember v n`. -/
theorem localPush_iterate (v : List (Fin 2)) (n : ℕ) :
    (localPush v)^[n] (localMember v 0) = localMember v n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, localPush_member]

/-- `Statement:` `localPush v (localBotEnd v) = localBotEnd v`. -/
theorem localPush_floor (v : List (Fin 2)) : localPush v (localBotEnd v) = localBotEnd v := by
  unfold localBotEnd; rw [localPush_prependEnd, boundaryDouble_botEnd]

/-- `Statement:` every fixed point of `localPush v` in `End` is `localBotEnd v`. -/
theorem localPush_unique_fp (v : List (Fin 2)) (x : End) (h : localPush v x = x) :
    x = localBotEnd v := by
  have hs := congrArg (shiftEnd v.length) h
  unfold localPush at hs
  rw [shiftEnd_prependEnd] at hs
  have h0 := boundaryDouble_unique_fp _ hs
  rw [← h]; unfold localPush localBotEnd; rw [h0, boundaryDouble_botEnd]

theorem prependEnd_nil (y : End) : prependEnd [] y = y := by funext n; simp [prependEnd]
theorem shiftEnd_zero (x : End) : shiftEnd 0 x = x := by funext k; simp [shiftEnd]

/-- `Statement:` `localPush [] = boundaryDouble`. -/
theorem localPush_nil : localPush [] = boundaryDouble := by
  funext x; simp only [localPush, List.length_nil, shiftEnd_zero, prependEnd_nil]

/-- `Statement:` `localMember v n` covers `localBotEnd v` in Mathlib's `Pi` order on `End`. -/
theorem localMember_covers (v : List (Fin 2)) (n : ℕ) : localBotEnd v ⋖ localMember v n := by
  rw [Pi.covBy_iff]
  refine ⟨v.length + n, ?_, fun j hj => ?_⟩
  · rw [localBotEnd_apply, localMember_at, List.getD_eq_default _ _ (by omega)]
    exact (finPlusTwo_zero_covBy_iff (q := 0) 1).2 rfl
  · rw [localBotEnd_apply, localMember_apply]
    by_cases h : j < v.length
    · rw [ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right hj, List.getD_eq_default _ _ (by omega)]

theorem localMember_ne_floor (v : List (Fin 2)) (n : ℕ) : localMember v n ≠ localBotEnd v :=
  (localMember_covers v n).1.ne'

-- Statement: control, the constant push `_ ↦ localBotEnd v` fixes the local floor and its orbit from
-- `localMember v 0` never reaches `localMember v 1`.
example (v : List (Fin 2)) (n : ℕ) :
    (fun _ : End => localBotEnd v)^[n] (localMember v 0) ≠ localMember v 1 := by
  cases n with
  | zero => exact fun h => absurd (localMember_injective v h) (by omega)
  | succ n => rw [Function.iterate_succ_apply']; exact (localMember_ne_floor v 1).symm

/-! ### § III. The subtree below `v` is an order copy of `End`; the push is `boundaryDouble` there. -/

/-- The ends with prefix `v`. -/
abbrev SubtreeEnd (v : List (Fin 2)) := {x : End // prependEnd v (shiftEnd v.length x) = x}

/-- Dropping the prefix: the subtree below `v` is order-isomorphic to `End`. -/
def subtreeOrderIso (v : List (Fin 2)) : SubtreeEnd v ≃o End where
  toFun x := shiftEnd v.length x.1
  invFun y := ⟨prependEnd v y, by rw [shiftEnd_prependEnd]⟩
  left_inv x := Subtype.ext x.2
  right_inv y := shiftEnd_prependEnd v y
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      show ∀ n, a.1 n ≤ b.1 n
      intro n
      rw [← a.2, ← b.2]
      show (if n < v.length then v.getD n 0 else shiftEnd v.length a.1 (n - v.length)) ≤
           (if n < v.length then v.getD n 0 else shiftEnd v.length b.1 (n - v.length))
      split_ifs
      · exact le_rfl
      · exact h _
    · intro h k
      exact h (v.length + k)

/-- `localPush v` restricted to the subtree. -/
def localPushSub (v : List (Fin 2)) (x : SubtreeEnd v) : SubtreeEnd v :=
  ⟨localPush v x.1, by unfold localPush; rw [shiftEnd_prependEnd]⟩
/-- The local floor as a point of the subtree. -/
def floorSub (v : List (Fin 2)) : SubtreeEnd v :=
  ⟨localBotEnd v, by unfold localBotEnd; rw [shiftEnd_prependEnd]⟩
/-- Member `n` as a point of the subtree. -/
def memberSub (v : List (Fin 2)) (n : ℕ) : SubtreeEnd v :=
  ⟨localMember v n, by unfold localMember; rw [shiftEnd_prependEnd]⟩

/-- `Statement:` `subtreeOrderIso v` conjugates `localPushSub v` to `boundaryDouble`. -/
theorem subtreeOrderIso_conj (v : List (Fin 2)) :
    Function.Semiconj (subtreeOrderIso v) (localPushSub v) boundaryDouble := by
  intro x
  show shiftEnd v.length (localPush v x.1) = boundaryDouble (shiftEnd v.length x.1)
  unfold localPush; rw [shiftEnd_prependEnd]

theorem subtreeOrderIso_floor (v : List (Fin 2)) : subtreeOrderIso v (floorSub v) = botEnd :=
  shiftEnd_prependEnd v botEnd

theorem subtreeOrderIso_member (v : List (Fin 2)) (n : ℕ) :
    subtreeOrderIso v (memberSub v n) = unitEnd n := by
  show shiftEnd v.length (localMember v n) = unitEnd n
  unfold localMember; rw [shiftEnd_prependEnd]; rfl

/-- `Statement:` inside the subtree, the covers of the local floor are exactly the tower members. -/
theorem subtree_covers_iff (v : List (Fin 2)) (s : SubtreeEnd v) :
    floorSub v ⋖ s ↔ ∃ n, s = memberSub v n := by
  rw [← apply_covBy_apply_iff (subtreeOrderIso v), subtreeOrderIso_floor, covBy_botEnd_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, (subtreeOrderIso v).injective ?_⟩
    rw [hk, subtreeOrderIso_member]
  · rintro ⟨n, rfl⟩; exact ⟨n, subtreeOrderIso_member v n⟩

/-- `Statement:` pull a seed computation back along a conjugating order isomorphism. -/
theorem coverSeeds_pullback {α β : Type*} [Preorder α] [Preorder β] (φ : α ≃o β) (P : α → α)
    (Q : β → β) (b : α) (hconj : ∀ x, φ (P x) = Q (φ x)) (S : Set α)
    (h : coverSeeds Q (φ b) = φ '' S) : coverSeeds P b = S := by
  have := coverSeeds_transport φ P Q b hconj
  rw [h] at this
  exact (Set.image_injective.2 φ.injective) this

/-- `Statement:` in the subtree, the seeds of `(localPushSub v)^[m]` are members `0, …, m-1`. -/
theorem subtree_coverSeeds_iterate (v : List (Fin 2)) (m : ℕ) :
    coverSeeds ((localPushSub v)^[m]) (floorSub v) = {s | ∃ i < m, s = memberSub v i} := by
  refine coverSeeds_pullback (subtreeOrderIso v) _ (boundaryDouble^[m]) _
    (fun x => Function.Semiconj.iterate_right (subtreeOrderIso_conj v) m x) _ ?_
  rw [subtreeOrderIso_floor, coverSeeds_iterate_boundaryDouble]
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨memberSub v i, ⟨i, hi, rfl⟩, subtreeOrderIso_member v i⟩
  · rintro ⟨s, ⟨i, hi, rfl⟩, rfl⟩; exact ⟨i, hi, subtreeOrderIso_member v i⟩

/-- `Statement:` in the subtree, `localPushSub v` has the one seed `memberSub v 0`. -/
theorem subtree_coverSeeds (v : List (Fin 2)) :
    coverSeeds (localPushSub v) (floorSub v) = {memberSub v 0} := by
  have h := subtree_coverSeeds_iterate v 1
  rw [Function.iterate_one] at h
  rw [h]; ext s
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩; rw [show i = 0 by omega]
  · rintro rfl; exact ⟨0, by omega, rfl⟩

-- Statement: control, in the ambient order of `End` the push at `[0, 1]` has a second seed `1 1 0 …`,
-- outside the subtree; one seed per tower needs the subtree order.
example : (fun n => if n ≤ 1 then (1 : Fin 2) else 0) ∈ coverSeeds (localPush [0, 1]) (localBotEnd [0, 1]) ∧
    (fun n => if n ≤ 1 then (1 : Fin 2) else 0) ≠ localMember [0, 1] 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Pi.covBy_iff]
    refine ⟨0, ?_, fun j hj => ?_⟩
    · rw [localBotEnd_apply]
      exact (finPlusTwo_zero_covBy_iff (q := 0) 1).2 rfl
    · rw [localBotEnd_apply]
      rcases j with _ | _ | j
      · exact absurd rfl hj
      · rfl
      · simp
  · rintro ⟨y, hy⟩
    have := congrFun hy 0
    simp [localPush, prependEnd] at this
  · intro h
    have := congrFun h 0
    rw [localMember_pre _ _ _ (by simp)] at this
    simp at this

/-! ### § IV. Which nodes give distinct towers. -/

/-- `Statement:` `localBotEnd v = localBotEnd w ↔ ∀ m, v.getD m 0 = w.getD m 0`. -/
theorem localBotEnd_eq_iff (v w : List (Fin 2)) :
    localBotEnd v = localBotEnd w ↔ ∀ m, v.getD m 0 = w.getD m 0 := by
  rw [localBotEnd_eq_getD, localBotEnd_eq_getD, funext_iff]

/-- `Statement:` trailing zeros do not change the local floor. -/
theorem localBotEnd_append_zeros (v : List (Fin 2)) (k : ℕ) :
    localBotEnd (v ++ List.replicate k 0) = localBotEnd v := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ', ← List.append_assoc, zero_branch_same, ih]

/-- `Statement:` `localMember (v ++ [0]) n = localMember v (n + 1)`. -/
theorem localMember_append_zero (v : List (Fin 2)) (n : ℕ) :
    localMember (v ++ [0]) n = localMember v (n + 1) := by
  funext m
  rw [localMember_apply, localMember_apply, List.length_append, List.length_singleton]
  by_cases h1 : m < v.length
  · rw [ite_eq_left (by omega), ite_eq_left h1, List.getD_append _ _ _ _ h1]
  · rw [ite_eq_right h1]
    by_cases h2 : m = v.length
    · subst h2
      rw [ite_eq_left (by omega), List.getD_append_right _ _ _ _ (le_refl _), ite_eq_right (by omega)]
      simp
    · rw [ite_eq_right (by omega)]
      by_cases h3 : m = v.length + 1 + n
      · rw [ite_eq_left h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h3, ite_eq_right (by omega)]

/-- `Statement:` `localMember (v ++ 0ᵏ) n = localMember v (n + k)`. -/
theorem localMember_append_zeros (v : List (Fin 2)) (k n : ℕ) :
    localMember (v ++ List.replicate k 0) n = localMember v (n + k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', ← List.append_assoc, localMember_append_zero, ih,
      show n + 1 + k = n + (k + 1) by omega]

/-- `Statement:` as sets, the tower at `v ++ [0]` is the tower at `v` from index 1. -/
theorem tower_append_zero (v : List (Fin 2)) :
    Set.range (localMember (v ++ [0])) = localMember v '' {n | 1 ≤ n} := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨n + 1, by simp, (localMember_append_zero v n).symm⟩
  · rintro ⟨n, hn, rfl⟩
    have hn' : 1 ≤ n := hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ⟨k, localMember_append_zero v k⟩

/-- `Statement:` `localMember v 0` is not in the tower at `v ++ [0]`. -/
theorem tower_append_zero_drops (v : List (Fin 2)) :
    localMember v 0 ∉ Set.range (localMember (v ++ [0])) := by
  rintro ⟨n, h⟩
  rw [localMember_append_zero] at h
  exact absurd (localMember_injective v h) (by omega)

/-- `Statement:` two nodes have the same tower set iff they are the same node. -/
theorem tower_eq_iff (v w : List (Fin 2)) :
    Set.range (localMember v) = Set.range (localMember w) ↔ v = w := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ : localMember v 0 ∈ Set.range (localMember w) := h ▸ ⟨0, rfl⟩
    obtain ⟨n, hn⟩ : localMember w 0 ∈ Set.range (localMember v) := h ▸ ⟨0, rfl⟩
    have h1 : w.length + m ≤ v.length := by
      by_contra hc
      have := congrFun hm (w.length + m)
      rw [localMember_at, localMember_off v 0 _ (by omega) (by omega)] at this
      exact absurd this (by decide)
    have h2 : v.length + n ≤ w.length := by
      by_contra hc
      have := congrFun hn (v.length + n)
      rw [localMember_at, localMember_off w 0 _ (by omega) (by omega)] at this
      exact absurd this (by decide)
    have hm0 : m = 0 := by omega
    have hlen : v.length = w.length := by omega
    subst hm0
    refine List.ext_getElem hlen fun p hp1 hp2 => ?_
    have := congrFun hm p
    rw [localMember_pre w 0 p hp2, localMember_pre v 0 p hp1, List.getD_eq_getElem _ _ hp2,
      List.getD_eq_getElem _ _ hp1] at this
    exact this.symm
  · rintro rfl; rfl

/-- Canonical nodes: the root, or a node ending in `1`. -/
def CanonNode (v : List (Fin 2)) : Prop := v = [] ∨ ∃ u, v = u ++ [1]

theorem canonNode_last (u : List (Fin 2)) : (u ++ [1]).getD u.length 0 = 1 := by
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl

/-- `Statement:` every node is a canonical node followed by zeros. -/
theorem exists_canonNode_append_zeros (v : List (Fin 2)) :
    ∃ w k, CanonNode w ∧ v = w ++ List.replicate k 0 := by
  induction v using List.reverseRecOn with
  | nil => exact ⟨[], 0, Or.inl rfl, rfl⟩
  | append_singleton u a ih =>
    obtain ⟨w, k, hw, rfl⟩ := ih
    rcases fin2_eq_zero_or_one a with rfl | rfl
    · exact ⟨w, k + 1, hw, by rw [List.replicate_succ', List.append_assoc]⟩
    · exact ⟨w ++ List.replicate k 0 ++ [1], 0, Or.inr ⟨_, rfl⟩, by simp⟩

/-- `Statement:` on canonical nodes, `localMember v n = localMember w m` forces `v = w` and `n = m`. -/
theorem canonTower_unique (v w : List (Fin 2)) (n m : ℕ) (hv : CanonNode v) (hw : CanonNode w)
    (h : localMember v n = localMember w m) : v = w ∧ n = m := by
  have hp : v.length + n = w.length + m := by
    have h1 : w.length + m ≤ v.length + n := by
      by_contra hc
      have := congrFun h (w.length + m)
      rw [localMember_at, localMember_off v n _ (by omega) (by omega)] at this
      exact absurd this (by decide)
    have h2 : v.length + n ≤ w.length + m := by
      by_contra hc
      have := congrFun h (v.length + n)
      rw [localMember_at, localMember_off w m _ (by omega) (by omega)] at this
      exact absurd this (by decide)
    omega
  have hl : v.length = w.length := by
    rcases lt_trichotomy v.length w.length with hlt | heq | hgt
    · exfalso
      rcases hw with rfl | ⟨u, rfl⟩
      · simp at hlt
      · have hlen : (u ++ [1]).length = u.length + 1 := by simp
        have := congrFun h u.length
        rw [localMember_pre (u ++ [1]) m u.length (by omega), canonNode_last,
          localMember_off v n _ (by omega) (by omega)] at this
        exact absurd this (by decide)
    · exact heq
    · exfalso
      rcases hv with rfl | ⟨u, rfl⟩
      · simp at hgt
      · have hlen : (u ++ [1]).length = u.length + 1 := by simp
        have := congrFun h u.length
        rw [localMember_pre (u ++ [1]) n u.length (by omega), canonNode_last,
          localMember_off w m _ (by omega) (by omega)] at this
        exact absurd this (by decide)
  refine ⟨?_, by omega⟩
  refine List.ext_getElem hl fun p hp1 hp2 => ?_
  have := congrFun h p
  rw [localMember_pre v n p hp1, localMember_pre w m p hp2, List.getD_eq_getElem _ _ hp1,
    List.getD_eq_getElem _ _ hp2] at this
  exact this

/-- `Statement:` on canonical towers, being a push-successor of some member holds iff `n ≠ 0`. -/
theorem canonTower_seed_iff (v : List (Fin 2)) (n : ℕ) (hv : CanonNode v) :
    (∃ w m, CanonNode w ∧ localMember v n = localMember w (m + 1)) ↔ n ≠ 0 := by
  constructor
  · rintro ⟨w, m, hw, h⟩; have := (canonTower_unique v w n (m + 1) hv hw h).2; omega
  · intro hn; exact ⟨v, n - 1, hv, by rw [show n - 1 + 1 = n by omega]⟩

/-- `Statement:` distinct canonical nodes have distinct local floors. -/
theorem canonNode_floor_injective (v w : List (Fin 2)) (hv : CanonNode v) (hw : CanonNode w)
    (h : localBotEnd v = localBotEnd w) : v = w := by
  rw [localBotEnd_eq_iff] at h
  have hl : v.length = w.length := by
    rcases lt_trichotomy v.length w.length with hlt | heq | hgt
    · exfalso
      rcases hw with rfl | ⟨u, rfl⟩
      · simp at hlt
      · have hlen : (u ++ [1]).length = u.length + 1 := by simp
        have := h u.length
        rw [canonNode_last, List.getD_eq_default _ _ (by omega)] at this
        exact absurd this (by decide)
    · exact heq
    · exfalso
      rcases hv with rfl | ⟨u, rfl⟩
      · simp at hgt
      · have hlen : (u ++ [1]).length = u.length + 1 := by simp
        have := h u.length
        rw [canonNode_last, List.getD_eq_default _ _ (by omega)] at this
        exact absurd this (by decide)
  refine List.ext_getElem hl fun p hp1 hp2 => ?_
  have := h p
  rwa [List.getD_eq_getElem _ _ hp1, List.getD_eq_getElem _ _ hp2] at this

/-- `Statement:` there are infinitely many distinct local floors. -/
theorem localFloors_infinite : (Set.range localBotEnd).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k => localBotEnd (List.replicate k 0 ++ [1]))
    (fun a b h => ?_) (fun _ => ⟨_, rfl⟩)
  have := congrArg List.length
    (canonNode_floor_injective _ _ (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) h)
  simpa using this

/-- `Statement:` `localMember u 0 = localBotEnd (u ++ [1])`. -/
theorem localMember_zero_eq_floor (u : List (Fin 2)) : localMember u 0 = localBotEnd (u ++ [1]) := by
  funext m
  rw [localMember_apply, localBotEnd_apply]
  by_cases h1 : m < u.length
  · rw [ite_eq_left h1, List.getD_append _ _ _ _ h1]
  · rw [ite_eq_right h1]
    by_cases h2 : m = u.length
    · subst h2; rw [ite_eq_left (by omega), canonNode_last]
    · rw [ite_eq_right (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-- `Statement:` every tower member is a local floor: `localMember v n = localBotEnd (v ++ 0ⁿ ++ [1])`. -/
theorem localMember_is_floor (v : List (Fin 2)) (n : ℕ) :
    localMember v n = localBotEnd (v ++ List.replicate n 0 ++ [1]) := by
  rw [← localMember_zero_eq_floor, localMember_append_zeros, zero_add]

/-- `Statement:` the root tower is the set of covers of `botEnd` in the `Pi` order. -/
theorem root_tower_eq_covers : Set.range (localMember []) = {x | botEnd ⋖ x} := by
  ext x
  simp only [Set.mem_range, Set.mem_ofPred_eq, covBy_botEnd_iff, localMember_nil_eq_unitEnd]
  constructor
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, rfl⟩

/-- `Statement:` for a non-root canonical node, the tower's first member does not cover `botEnd`. -/
theorem nonroot_seed_not_cover (u : List (Fin 2)) : ¬ botEnd ⋖ localMember (u ++ [1]) 0 := by
  intro h
  rw [covBy_botEnd_iff] at h
  obtain ⟨k, hk⟩ := h
  have hlen : (u ++ [1]).length = u.length + 1 := by simp
  have h1 := congrFun hk u.length
  have h2 := congrFun hk ((u ++ [1]).length + 0)
  rw [localMember_pre _ 0 _ (by omega), canonNode_last] at h1
  rw [localMember_at] at h2
  by_cases hk' : u.length = k
  · rw [unitEnd_ne (by omega)] at h2; exact absurd h2 (by decide)
  · rw [unitEnd_ne hk'] at h1; exact absurd h1 (by decide)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms localBotEnd_eq_getD
#print axioms localBotEnd_apply
#print axioms localMember_apply
#print axioms localMember_at
#print axioms localMember_off
#print axioms localMember_pre
#print axioms localMember_injective
#print axioms localMember_nil_eq_unitEnd
#print axioms localPush
#print axioms localPush_prependEnd
#print axioms localPush_member
#print axioms localPush_iterate
#print axioms localPush_floor
#print axioms localPush_unique_fp
#print axioms prependEnd_nil
#print axioms shiftEnd_zero
#print axioms localPush_nil
#print axioms localMember_covers
#print axioms localMember_ne_floor
#print axioms SubtreeEnd
#print axioms subtreeOrderIso
#print axioms localPushSub
#print axioms floorSub
#print axioms memberSub
#print axioms subtreeOrderIso_conj
#print axioms subtreeOrderIso_floor
#print axioms subtreeOrderIso_member
#print axioms subtree_covers_iff
#print axioms coverSeeds_pullback
#print axioms subtree_coverSeeds_iterate
#print axioms subtree_coverSeeds
#print axioms localBotEnd_eq_iff
#print axioms localBotEnd_append_zeros
#print axioms localMember_append_zero
#print axioms localMember_append_zeros
#print axioms tower_append_zero
#print axioms tower_append_zero_drops
#print axioms tower_eq_iff
#print axioms CanonNode
#print axioms canonNode_last
#print axioms exists_canonNode_append_zeros
#print axioms canonTower_unique
#print axioms canonTower_seed_iff
#print axioms canonNode_floor_injective
#print axioms localFloors_infinite
#print axioms localMember_zero_eq_floor
#print axioms localMember_is_floor
#print axioms root_tower_eq_covers
#print axioms nonroot_seed_not_cover
end PurityCheck
