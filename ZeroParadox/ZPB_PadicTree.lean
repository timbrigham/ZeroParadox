import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
# ZP-B Padic Tree: ZP's rooted 2-adic tree as a graph (LOCAL / EXPLORATORY STUB)

## Engineer's Take

TODO (Tim): your own words go here.

---

## Formal Overview (AI-assisted)

**Status: complete — fully proved, `sorry`-free** (only the Engineer's Take above is left as a
TODO for Tim). Verified: the `SimpleGraph` on finite binary strings is connected and acyclic
(`tree_isTree`), with the (p+1 = 3)-regularity as neighbor-set equalities and the forced floor
`botEnd_val_top`. Acyclicity is proved on the local-bottom model (see §IV). This file makes ZP's
2-adic tree
an *explicit graph object* so it can be lined up against the Lean formalization of the
Bruhat–Tits tree by Ludwig & Merten (arXiv:2505.12933, repo `github.com/chrisflav/bruhat-tits`).

ZP's tree is currently only *implicit* in the project: `ZPB.lean` gives the 2-adic metric
(the nested clopen-ball hierarchy `B(0,2⁻ⁿ) ↘ {0}`, over Mathlib's `ℚ_[2]`), and
`ZPJ_Scale.lean` gives the valuation `q2Val` on ℤ₂. Neither is a graph. This file builds the
graph and states the question.

Three parts:
1. **The tree.** Vertices = finite binary strings = clopen balls of ℤ₂ (`[]` = the root = all
   of ℤ₂); edges = one-digit refinement. Kept on `List (Fin 2)` — decoupled from the heavy
   `Padic` machinery on purpose.
2. **The forced floor.** The boundary (ends) = infinite binary paths `ℕ → Fin 2` ≅ ℤ₂. The
   all-zeros end `botEnd` is the distinguished basepoint = `0 ∈ ℤ₂`, where the 2-adic valuation
   is ∞ (= ⊤). `endVal` is the combinatorial stand-in for `q2Val` under ℤ₂ ≅ (ℕ → Fin 2).
3. **The question (conjecture, not a result).** `EmbedsAsRootedSubtree`: ZP's `tree` embeds as
   the rooted subtree, at a chosen end, of a 3-regular tree — the (p+1 = 3)-regular Bruhat–Tits
   tree for p = 2. Stated abstractly here because their BT-tree type is not a dependency of this
   project; the question to put to Ludwig & Merten is whether *their* BT tree is the witness,
   with `botEnd`/`root` the chosen basepoint.
-/

namespace ZeroParadox.PadicTree

set_option maxHeartbeats 400000

/-! ## § I. ZP's rooted 2-adic tree -/

/-- A vertex: a finite binary string = a clopen ball of ℤ₂.
    `[]` is the root (all of ℤ₂); the length is the ball depth (radius `2⁻ˡᵉⁿᵍᵗʰ`). -/
abbrev Vtx := List (Fin 2)

/-- The root: the whole space ℤ₂. -/
def root : Vtx := []

/-- Ball depth = string length = the `n` in `B(·, 2⁻ⁿ)`. -/
def depth (v : Vtx) : ℕ := v.length

/-- The two children of a ball: append a `0` or a `1` digit. -/
def children (v : Vtx) : Set Vtx := {v ++ [0], v ++ [1]}

/-- ZP's rooted 2-adic tree. Two balls are adjacent iff one refines the other by exactly
    one digit. Mirrors the lattice-adjacency of the Bruhat–Tits tree (`Graph/Graph.lean`). -/
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

/-! ## § IV. `tree_isTree` — and a note on its proof structure (ZP-I in the metatheory)

The proof that this graph is a tree recurses on **local bottoms**: every vertex `v` is the root
of a self-similar subtree `below(v) = {x | v <+: x}`, an exact copy of the whole tree. Acyclicity
is the statement that a cycle's *minimal-length* vertex — its own local bottom — would have to
leave through both of its children, whose subtrees `below (v ++ [0])`, `below (v ++ [1])` are
prefix-disjoint and can only reconnect back through `v`. The disjointness of the local copies *is*
the acyclicity. This is exactly ZP-I's "a bottom at every level": the snap structure recurs at
every node, and that recursion is what forbids cycles — the framework describing itself inside its
own metatheory.

Formally: `isAcyclic_iff_forall_adj_isBridge`. Every parent–child edge `(v, v ++ [d])` is a bridge
because deleting it strands the child's prefix-closed subtree `below(v ++ [d])`, which `v` is not
in. The one load-bearing lemma is `edge_pres`: membership in `below(v ++ [d])` is preserved across
every *remaining* edge (the deleted edge is the only one that crosses the boundary). -/

/-- A prefix of `p ++ [e]` is either all of it, or already a prefix of `p`: the "either you are the
    child boundary, or you live strictly inside the parent" dichotomy that powers the local-bottom
    argument. -/
private theorem prefix_concat_split {α : Type*} {c p : List α} {e : α}
    (h : c <+: p ++ [e]) : c = p ++ [e] ∨ c <+: p := by
  obtain ⟨t, ht⟩ := h
  rcases t.eq_nil_or_concat with rfl | ⟨t', a, rfl⟩
  · exact Or.inl (by simpa using ht)
  · refine Or.inr ⟨t', ?_⟩
    rw [List.concat_eq_append, ← List.append_assoc] at ht
    exact List.append_inj_left' ht rfl

/-- It is a tree (connected + acyclic). Mirrors Ludwig–Merten `Graph/Tree.lean`.
    See the section note above: acyclicity recurses on local bottoms (ZP-I). -/
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
  -- Acyclic: every parent–child edge is a bridge (the local-bottom argument).
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
    parent (three of them) — the (p+1 = 3)-regularity of the BT tree for p = 2. Mirrors
    Ludwig–Merten `Graph/Regular.lean`, stated as a neighbor-set equality to avoid `Fintype`. -/
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

/-! ## § II. Boundary and the forced floor ⊥ -/

/-- A boundary point / end: an infinite binary path. Identified with ℤ₂ via digit expansion. -/
abbrev End := ℕ → Fin 2

/-- The distinguished basepoint/end: the all-zeros path = `0 ∈ ℤ₂` = ⊥ (where `v₂ = ∞`). -/
def botEnd : End := fun _ => 0

/-- 2-adic valuation of an end: the least index carrying a nonzero digit, `⊤` if none.
    The combinatorial stand-in for `q2Val` (ZPJ_Scale) under ℤ₂ ≅ (ℕ → Fin 2). -/
noncomputable def endVal (x : End) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | x n ≠ 0})

/-- ⊥ is the unique end with infinite valuation: `endVal botEnd = ⊤`.
    Mirrors `q2Val_zero` / `val_bot` (`val ⊥ = ⊤`). -/
theorem botEnd_val_top : endVal botEnd = ⊤ := by
  have h : {n | botEnd n ≠ 0} = (∅ : Set ℕ) := by
    ext n; simp [botEnd]
  unfold endVal
  rw [h, Set.image_empty, sInf_empty]

/-! ## § III. The embedding question (conjecture — the ask for Ludwig & Merten) -/

/-- **CONJECTURE (stated, not proved).** ZP's `tree` embeds as the rooted subtree, at a chosen
    end, of a 3-regular tree. The intended witness is the Bruhat–Tits tree of ℚ₂ (which is
    `(p+1) = 3`-regular for `p = 2`), with `root` mapping to a vertex adjacent to the chosen
    boundary end fixed by `botEnd`. Stated abstractly because the BT-tree type
    (arXiv:2505.12933 / `chrisflav/bruhat-tits`) is not a dependency here — the question to put
    to the authors is whether their tree is the witness `T`. -/
def EmbedsAsRootedSubtree : Prop :=
  ∃ (W : Type) (T : SimpleGraph W), T.IsTree ∧
    ∃ f : Vtx → W, Function.Injective f ∧ ∀ v w : Vtx, tree.Adj v w → T.Adj (f v) (f w)

/-! ## § V. Self-similarity — every vertex is a local bottom (ZP-I, positively)

The acyclicity proof *used* the self-similar structure; here it is as a theorem. The prefix map
`x ↦ v ++ x` carries the whole tree faithfully onto the subtree `below(v)`: it preserves *and*
reflects adjacency. So beneath every vertex sits an exact copy of the whole tree — each vertex is
the local bottom of a replica. This is ZP-I stated positively, and it is the in-house form of the
open question put to Ludwig & Merten (does ZP's tree sit as a rooted subtree inside the
Bruhat–Tits tree?) — here answered for ZP's tree inside *itself*. -/

/-- **Self-similarity.** Prefixing by `v` reflects and preserves adjacency, so the subtree below
    any vertex `v` is a faithful copy of the whole tree: each vertex is a local bottom. -/
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
