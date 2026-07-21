import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
# A rooted 2-adic tree as a `SimpleGraph`

## Engineer's Take

A ZP-B construction. See the Engineer's Take in `ZeroParadox/Valuation/Padic.lean`.

---

A small, self-contained Lean 4 formalization of the rooted tree whose vertices are finite binary
strings (the clopen balls of ℤ₂), with an edge between a string and that same string with one extra
digit appended. Fully proved, `sorry`-free.

The aim is to make this tree an explicit graph object so it can be compared with the Lean
formalization of the Bruhat-Tits tree by J. Ludwig and C. Merten (arXiv:2505.12933, repo
`github.com/chrisflav/bruhat-tits`).

Contents:
1. The tree. Vertices = finite binary strings = clopen balls of ℤ₂ (`[]` = root = all of ℤ₂);
   edges = one-digit refinement. Built on `List (Fin 2)`, decoupled from the `Padic` machinery.
2. The boundary. Ends = infinite binary paths `ℕ → Fin 2` ≅ ℤ₂. The all-zeros end `botEnd`
   corresponds to `0 ∈ ℤ₂`, where the 2-adic valuation is ∞ (= ⊤); `endVal` is the combinatorial
   2-adic valuation under ℤ₂ ≅ (ℕ → Fin 2).
3. An open question. `EmbedsAsRootedSubtree`: this tree embeds as the rooted subtree, at a chosen
   end, of a 3-regular tree, the (p+1 = 3)-regular Bruhat-Tits tree of ℚ₂. Stated abstractly
   because the BT-tree type is not a dependency here.

This file is self-contained.
-/

namespace ZeroParadox

set_option maxHeartbeats 400000

/-! ## § I. The rooted 2-adic tree -/

/-- A vertex: a finite binary string = a clopen ball of ℤ₂.
    `[]` is the root (all of ℤ₂); the length is the ball depth (radius `2⁻ˡᵉⁿᵍᵗʰ`). -/
abbrev Vtx := List (Fin 2)

/-- The root: the whole space ℤ₂. -/
def root : Vtx := []

/-- Ball depth = string length = the `n` in `B(·, 2⁻ⁿ)`. -/
def depth (v : Vtx) : ℕ := v.length

/-- The two children of a ball: append a `0` or a `1` digit. -/
def children (v : Vtx) : Set Vtx := {v ++ [0], v ++ [1]}

/-- The rooted 2-adic tree. Two balls are adjacent iff one refines the other by exactly
    one digit. -/
def tree : SimpleGraph Vtx where
  Adj v w := (∃ d : Fin 2, w = v ++ [d]) ∨ (∃ d : Fin 2, v = w ++ [d])
  symm := by
    intro v w h
    rcases h with ⟨d, hd⟩ | ⟨d, hd⟩
    · exact Or.inr ⟨d, hd⟩
    · exact Or.inl ⟨d, hd⟩
  -- The length argument is written out explicitly rather than closed by `simp`, deliberately.
  -- `simp` discharged this goal but pulled `Classical.choice` into the graph OBJECT, and every
  -- lemma mentioning `tree` then inherited it — including `adj_prefix_iff`, which is pure list
  -- algebra. This file imports no `Padic`; the classical footprint was entirely self-inflicted here.
  -- Measured effect of writing it out: `tree` and `adj_prefix_iff` drop to `[propext, Quot.sound]`.
  -- The instance hazard in a structure field, and the third worked instance of the pattern
  -- (cf. `dneg_inf_distrib`, `ZeroParadox/Category/DoubleNegationNucleus.lean`).
  loopless := by
    refine ⟨?_⟩
    intro x hx
    rcases hx with ⟨d, hd⟩ | ⟨d, hd⟩ <;>
      · have hlen := congrArg List.length hd
        rw [List.length_append, List.length_singleton] at hlen
        omega

/-! ## § II. `tree_isTree`

**Acyclicity is proved directly from the definition (`IsAcyclic` = no cyclic walk), choice-free** — it
does not touch Mathlib's bridge / `deleteEdges` API, which is where `Classical.choice` enters. A
hypothetical cycle is rotated to start at its minimal-depth vertex `u`; both of `u`'s cycle-neighbours
are then children `u ++ [d₁]`, `u ++ [d₂]` (a shallower neighbour is impossible at the minimum), and
they are distinct (`a ≠ b`, from edge-nodup). The interior of the cycle is a walk from `u ++ [d₁]` to
`u ++ [d₂]` that avoids `u`; along it, membership in the prefix-closed subtree
`below(u ++ [d₁]) = {x | u ++ [d₁] <+: x}` is preserved (`walk_pres` — the only boundary edge,
`u — u ++ [d₁]`, is incident to `u`), yet the walk starts inside that subtree and ends outside it. That
is the contradiction. `tree_acyclic` and its infrastructure below measure `[propext, Quot.sound]`.
Connectedness is immediate: every vertex reaches the root by repeatedly dropping its last digit. -/

/-- A prefix of `p ++ [e]` is either all of it, or already a prefix of `p`: the "either you are the
    boundary element, or you lie strictly inside the parent" dichotomy used in `edge_pres`. -/
private theorem prefix_concat_split {α : Type*} {c p : List α} {e : α}
    (h : c <+: p ++ [e]) : c = p ++ [e] ∨ c <+: p := by
  obtain ⟨t, ht⟩ := h
  rcases t.eq_nil_or_concat with rfl | ⟨t', a, rfl⟩
  · exact Or.inl (by simpa using ht)
  · refine Or.inr ⟨t', ?_⟩
    rw [List.concat_eq_append, ← List.append_assoc] at ht
    exact List.append_inj_left' ht rfl

/-! ### Choice-free acyclicity infrastructure

Four small combinatorial facts, all choice-free. `walk_pres` is the heart: the subtree-membership
invariant transported along a vertex-avoiding walk. -/

section ChoiceFreeAcyclic
open SimpleGraph
set_option maxHeartbeats 1000000

/-- A neighbour of `u` that is not shallower than `u` is one of its two children. -/
private theorem neighbor_ge_is_child {u w : Vtx} (h : tree.Adj u w) (hge : u.length ≤ w.length) :
    ∃ d : Fin 2, w = u ++ [d] := by
  rcases h with ⟨d, rfl⟩ | ⟨d, hd⟩
  · exact ⟨d, rfl⟩
  · exfalso; subst hd; rw [List.length_append, List.length_singleton] at hge; omega

/-- Membership in `below(u ++ [d])` is preserved across any edge not incident to `u` — the only
boundary edge of that subtree is `u — u ++ [d]`. -/
private theorem prefix_pres {u : Vtx} {d : Fin 2} {a b : Vtx}
    (h : tree.Adj a b) (ha : a ≠ u) (hb : b ≠ u) :
    ((u ++ [d]) <+: a ↔ (u ++ [d]) <+: b) := by
  rcases h with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · constructor
    · intro hx; exact hx.trans (List.prefix_append a [e])
    · intro hy
      rcases prefix_concat_split hy with heq | hpref
      · exact absurd (by have := congrArg List.dropLast heq; simpa using this.symm) ha
      · exact hpref
  · constructor
    · intro hx
      rcases prefix_concat_split hx with heq | hpref
      · exact absurd (by have := congrArg List.dropLast heq; simpa using this.symm) hb
      · exact hpref
    · intro hy; exact hy.trans (List.prefix_append b [e])

/-- `below(u ++ [d])`-membership is preserved along any walk that avoids `u`. -/
private theorem walk_pres {u : Vtx} {d : Fin 2} : ∀ {p q : Vtx} (w : tree.Walk p q),
    u ∉ w.support → ((u ++ [d]) <+: p ↔ (u ++ [d]) <+: q) := by
  intro p q w
  induction w with
  | nil => intro _; exact Iff.rfl
  | @cons p p' q hadj w' ih =>
      intro hu
      rw [Walk.support_cons, List.mem_cons, not_or] at hu
      obtain ⟨hup, hurest⟩ := hu
      have hp' : u ≠ p' := fun h => hurest (h ▸ w'.start_mem_support)
      exact (prefix_pres hadj (Ne.symm hup) (Ne.symm hp')).trans (ih hurest)

/-- Every nonempty list of vertices has a minimum-length element. -/
private theorem exists_min_len : ∀ (l : List Vtx), l ≠ [] →
    ∃ u ∈ l, ∀ x ∈ l, u.length ≤ x.length := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a t ih =>
      intro _
      cases t with
      | nil => exact ⟨a, by simp, by simp⟩
      | cons b t' =>
          rcases ih (by simp) with ⟨u, hu, hmin⟩
          by_cases hle : a.length ≤ u.length
          · refine ⟨a, by simp, ?_⟩
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx'
            · exact le_refl _
            · exact hle.trans (hmin x hx')
          · refine ⟨u, List.mem_cons_of_mem _ hu, ?_⟩
            intro x hx
            rcases List.mem_cons.1 hx with rfl | hx'
            · omega
            · exact hmin x hx'

/-- **The tree is acyclic — proved directly from `IsAcyclic`, choice-free** (no bridge / `deleteEdges`
API). See the § II header for the argument. -/
theorem tree_acyclic : tree.IsAcyclic := by
  intro r c hc
  obtain ⟨u, hu_mem, hu_min⟩ := exists_min_len c.support c.support_ne_nil
  have hcyc' : (c.rotate u hu_mem).IsCycle := hc.rotate hu_mem
  have hrotnil : ¬ (c.rotate u hu_mem).Nil := hcyc'.not_nil
  have hmin' : ∀ x ∈ (c.rotate u hu_mem).support, u.length ≤ x.length := by
    intro x hx
    by_cases hxu : x = u
    · exact hu_min x (hxu ▸ hu_mem)
    · have hs : (c.rotate u hu_mem).support = u :: (c.rotate u hu_mem).tail.support := by
        conv_lhs => rw [← (c.rotate u hu_mem).cons_tail_eq hrotnil]
        rw [Walk.support_cons]
      rw [hs, List.mem_cons] at hx
      have hxt := hx.resolve_left hxu
      rw [(c.rotate u hu_mem).support_tail_of_not_nil hrotnil] at hxt
      exact hu_min x (List.mem_of_mem_tail (((c.support_rotate u hu_mem).mem_iff).1 hxt))
  set c' := c.rotate u hu_mem with hc'def
  clear_value c'
  cases c' with
  | nil => exact hcyc'.not_nil .nil
  | @cons _ a _ h1 w1 =>
      -- h1 : tree.Adj u a ; w1 : tree.Walk a u
      have hnd : w1.support.Nodup := by
        have := hcyc'.support_nodup
        rwa [Walk.support_cons, List.tail_cons] at this
      -- `a`, the second vertex, is a child of `u` (min depth)
      obtain ⟨d1, hd1⟩ := neighbor_ge_is_child h1 (hmin' a (by
        rw [Walk.support_cons]; exact List.mem_cons_of_mem _ w1.start_mem_support))
      -- not-nil from loopless (`Adj.ne`); no need for `three_le_length` (which carries choice)
      have hau : a ≠ u := (h1.ne).symm
      have hw1nil : ¬ w1.Nil := Walk.not_nil_of_ne hau
      have hqnil : ¬ w1.reverse.Nil := Walk.not_nil_of_ne h1.ne
      -- `b`, the second-to-last vertex, is the other child of `u`
      set b := w1.reverse.snd with hbdef
      have hub : tree.Adj u b := w1.reverse.adj_snd hqnil
      have hb_mem : b ∈ w1.support := by
        have hmem : b ∈ w1.reverse.support := w1.reverse.getVert_mem_support 1
        rw [Walk.support_reverse, List.mem_reverse] at hmem
        exact hmem
      obtain ⟨d2, hd2⟩ := neighbor_ge_is_child hub (hmin' b (by
        rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hb_mem))
      -- the interior walk `w1.reverse.tail : Walk b a` avoids `u`
      have hqsupp_nd : w1.reverse.support.Nodup := by
        rw [Walk.support_reverse]; exact List.nodup_reverse.mpr hnd
      have hcons : w1.reverse.support = u :: w1.reverse.tail.support := by
        conv_lhs => rw [← w1.reverse.cons_tail_eq hqnil]
        rw [Walk.support_cons]
      have hu_not_mid : u ∉ w1.reverse.tail.support := by
        rw [hcons] at hqsupp_nd; exact (List.nodup_cons.1 hqsupp_nd).1
      -- `a ≠ b`, choice-free via edge-nodup: `s(u,b)` is the last edge of `w1`, and
      -- `c'.edges = s(u,a) :: w1.edges` is nodup, so `a = b` would list `s(u,a) = s(u,b)` twice.
      have hedge_rev : s(u, b) ∈ w1.reverse.edges := by
        have h2 : w1.reverse.edges = s(u, b) :: w1.reverse.tail.edges := by
          conv_lhs => rw [← w1.reverse.cons_tail_eq hqnil]
          rw [Walk.edges_cons]
        rw [h2]; exact List.mem_cons_self ..
      have hmem_w1 : s(u, b) ∈ w1.edges := by
        rw [Walk.edges_reverse, List.mem_reverse] at hedge_rev; exact hedge_rev
      have hab : a ≠ b := by
        intro heq
        have hnd_e := hcyc'.edges_nodup
        rw [Walk.edges_cons] at hnd_e
        have hsym : s(u, a) = s(u, b) := by rw [heq]
        exact (List.nodup_cons.1 hnd_e).1 (by rw [hsym]; exact hmem_w1)
      -- transport the subtree invariant along the interior walk → contradiction
      have key := walk_pres (u := u) (d := d1) w1.reverse.tail hu_not_mid
      have hbend : u ++ [d1] <+: a := hd1 ▸ List.prefix_refl _
      have hbstart : u ++ [d1] <+: b := key.mpr hbend
      rw [hd2] at hbstart
      have hlen : (u ++ [d1]).length = (u ++ [d2]).length := by simp
      have hd12 : u ++ [d1] = u ++ [d2] := hbstart.eq_of_length hlen
      exact hab (by rw [hd1, hd2, hd12])

end ChoiceFreeAcyclic

/-- It is a tree (connected and acyclic). Acyclicity is `tree_acyclic`, proved choice-free. -/
theorem tree_isTree : tree.IsTree := by
  -- Connected: every vertex reaches the root `[]` by walking up via `dropLast`.
  have reach_root : ∀ x : Vtx, tree.Reachable [] x := by
    intro x
    induction x using List.reverseRecOn with
    | nil => exact SimpleGraph.Reachable.refl _
    | append_singleton l a ih =>
        exact ih.trans (SimpleGraph.Adj.reachable (Or.inl ⟨a, rfl⟩))
  have hconn : tree.Connected := by
    rw [SimpleGraph.connected_iff]
    exact ⟨fun x y => (reach_root x).symm.trans (reach_root y), ⟨[]⟩⟩
  exact ⟨hconn, tree_acyclic⟩

/-- Interior regularity: a non-root vertex's neighbors are exactly its two children and its
    parent (three of them), the analogue of (p+1 = 3)-regularity. Stated as a neighbor-set
    equality to avoid `Fintype`. -/
theorem neighborSet_interior (v : Vtx) (hv : v ≠ root) :
    tree.neighborSet v = {v ++ [0], v ++ [1], v.dropLast} := by
  have hv' : v ≠ [] := by simpa only [root] using hv
  ext w
  simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨d, rfl⟩ | ⟨d, hd⟩)
    · fin_cases d
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · right; right
      rw [hd]; simp
  · rintro (rfl | rfl | rfl)
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨v.getLast hv', (List.dropLast_append_getLast hv').symm⟩

/-- Root regularity: the root has exactly its two children as neighbors (degree 2, no parent). -/
theorem neighborSet_root : tree.neighborSet root = {root ++ [0], root ++ [1]} := by
  ext w
  simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨d, rfl⟩ | ⟨d, hd⟩)
    · fin_cases d
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact absurd (congrArg List.length hd) (by simp [root])
  · rintro (rfl | rfl)
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩

/-! ## § III. Boundary -/

/-- A boundary point / end: an infinite binary path. Identified with ℤ₂ via digit expansion. -/
abbrev End := ℕ → Fin 2

/-- The all-zeros end: the path that is `0` everywhere, corresponding to `0 ∈ ℤ₂`
    (2-adic valuation ∞). -/
def botEnd : End := fun _ => 0

/-- 2-adic valuation of an end: the least index carrying a nonzero digit, `⊤` if none.
    The combinatorial 2-adic valuation under ℤ₂ ≅ (ℕ → Fin 2). -/
noncomputable def endVal (x : End) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | x n ≠ 0})

/-- The all-zeros end has infinite valuation: `endVal botEnd = ⊤`. -/
theorem botEnd_val_top : endVal botEnd = ⊤ := by
  have h : {n | botEnd n ≠ 0} = (∅ : Set ℕ) := by
    ext n; simp [botEnd]
  unfold endVal
  rw [h, Set.image_empty, sInf_empty]

/-! ## § IV. The embedding question (open) -/

/-- **Open question (stated, not proved).** This `tree` embeds as the rooted subtree, at a chosen
    end, of a 3-regular tree. The intended witness is the Bruhat-Tits tree of ℚ₂ (which is
    `(p+1) = 3`-regular for `p = 2`), with `root` mapping to a vertex adjacent to the chosen
    boundary end. Stated abstractly because the BT-tree type (arXiv:2505.12933 /
    `chrisflav/bruhat-tits`) is not a dependency here. -/
def EmbedsAsRootedSubtree : Prop :=
  ∃ (W : Type) (T : SimpleGraph W), T.IsTree ∧ Nonempty (tree ↪g T)

/-! ## § V. Self-similarity

The acyclicity proof used the self-similar structure; here it is as a theorem. The prefix map
`x ↦ v ++ x` carries the whole tree faithfully onto the subtree `below(v)`: it preserves *and*
reflects adjacency. So beneath every vertex sits an exact copy of the whole tree. This is the
in-house analogue of the open question above (does this tree sit as a rooted subtree inside the
Bruhat-Tits tree?), answered here for the tree inside *itself*. -/

/-- **Self-similarity.** Prefixing by `v` reflects and preserves adjacency, so the subtree below
    any vertex `v` is a faithful copy of the whole tree. -/
theorem adj_prefix_iff (v x y : Vtx) : tree.Adj (v ++ x) (v ++ y) ↔ tree.Adj x y := by
  constructor
  · rintro (⟨d, hd⟩ | ⟨d, hd⟩)
    · refine Or.inl ⟨d, ?_⟩
      have h : v ++ y = v ++ (x ++ [d]) := by rw [hd, List.append_assoc]
      exact List.append_cancel_left h
    · refine Or.inr ⟨d, ?_⟩
      have h : v ++ x = v ++ (y ++ [d]) := by rw [hd, List.append_assoc]
      exact List.append_cancel_left h
  · rintro (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · exact Or.inl ⟨d, by rw [List.append_assoc]⟩
    · exact Or.inr ⟨d, by rw [List.append_assoc]⟩

/-! ## § VI. Purity check -/

section PurityCheck
#print axioms tree_acyclic
#print axioms tree_isTree
#print axioms adj_prefix_iff
#print axioms botEnd_val_top
end PurityCheck

end ZeroParadox
