import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
# A rooted 2-adic tree as a `SimpleGraph`

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

namespace ZeroParadox.PadicTree

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
  loopless := by
    refine ⟨?_⟩
    intro x hx
    rcases hx with ⟨d, hd⟩ | ⟨d, hd⟩ <;>
      exact absurd (congrArg List.length hd) (by simp)

/-! ## § II. `tree_isTree`

Acyclicity uses the bridge characterization (`isAcyclic_iff_forall_adj_isBridge`): every
parent-child edge `(v, v ++ [d])` is a bridge, because deleting it strands the prefix-closed
subtree `below(v ++ [d]) = {x | v ++ [d] <+: x}`, which the parent `v` is not in. The one
load-bearing lemma is `edge_pres`: membership in `below(v ++ [d])` is preserved across every
*remaining* edge, since the deleted edge is the only one crossing the boundary. (Equivalently, a
hypothetical cycle's minimal-length vertex would have to leave through both of its children, whose
subtrees are prefix-disjoint and reconnect only through that vertex.) Connectedness is immediate:
every vertex reaches the root by repeatedly dropping its last digit. -/

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

/-- It is a tree (connected and acyclic). -/
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
  -- Acyclic: every parent-child edge is a bridge.
  have hacyc : tree.IsAcyclic := by
    rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
    have bridge_lemma : ∀ (v : Vtx) (d : Fin 2), tree.IsBridge s(v, v ++ [d]) := by
      intro v d
      rw [SimpleGraph.isBridge_iff]
      refine ⟨Or.inl ⟨d, rfl⟩, ?_⟩
      -- `below(v ++ [d])`-membership is preserved across every *remaining* edge.
      have edge_pres : ∀ x y : Vtx,
          (tree.deleteEdges {s(v, v ++ [d])}).Adj x y →
          ((v ++ [d]) <+: x ↔ (v ++ [d]) <+: y) := by
        intro x y hxy
        simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff] at hxy
        obtain ⟨hadj, hne⟩ := hxy
        rcases hadj with ⟨e, rfl⟩ | ⟨e, rfl⟩
        · constructor
          · intro hx; exact hx.trans (List.prefix_append x [e])
          · intro hy
            rcases prefix_concat_split hy with heq | hpref
            · exfalso; apply hne
              have hxv : x = v := by simpa using (congrArg List.dropLast heq).symm
              subst hxv
              rw [← heq]
            · exact hpref
        · constructor
          · intro hx
            rcases prefix_concat_split hx with heq | hpref
            · exfalso; apply hne
              have hyv : y = v := by simpa using (congrArg List.dropLast heq).symm
              subst hyv
              rw [Sym2.eq_swap, ← heq]
            · exact hpref
          · intro hy; exact hy.trans (List.prefix_append y [e])
      -- The invariant is preserved along every walk in the edge-deleted graph.
      have key : ∀ {p q : Vtx},
          (tree.deleteEdges {s(v, v ++ [d])}).Walk p q →
          ((v ++ [d]) <+: p ↔ (v ++ [d]) <+: q) := by
        intro p q w
        induction w with
        | nil => exact Iff.rfl
        | cons hadj _ ih => exact (edge_pres _ _ hadj).trans ih
      -- So `v` (not in the subtree) is unreachable from `v ++ [d]` (in it): contradiction.
      intro hreach
      obtain ⟨w⟩ := hreach
      have hbad : (v ++ [d]) <+: v := (key w).mpr (List.prefix_refl _)
      have hlen := hbad.length_le
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    rintro a b (⟨d, rfl⟩ | ⟨d, rfl⟩)
    · exact bridge_lemma a d
    · rw [Sym2.eq_swap]; exact bridge_lemma b d
  exact ⟨hconn, hacyc⟩

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
#print axioms tree_isTree
#print axioms adj_prefix_iff
#print axioms botEnd_val_top
end PurityCheck

end ZeroParadox.PadicTree
