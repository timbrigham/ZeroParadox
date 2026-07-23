-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicTree
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The boundary embedding: the exact gap to the Bruhat-Tits tree

## Engineer's Take

I wanted to know exactly what the boundary is, where it sits, why it walls, and how it behaves. The goal was
always to define the boundary exactly, so the open question had to be stated tightly rather than left loose.
What stays open is the one honest gap between this tree and the standard one.

This was me wanting the boundary pinned down exactly, with its open question stated tightly. Sometimes it helps
to work through this from the ground up. Much of what is here re-derives results the framework already has, and
that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

`PadicTree.EmbedsAsRootedSubtree` — `∃ (W) (T : SimpleGraph W), T.IsTree ∧ Nonempty (tree ↪g T)` — is, as
stated, **trivially true**: take `T = tree` and the identity embedding (`embedsAsRootedSubtree_of_self`). So
the abstract statement does not capture the intended content. The real open question is embedding into a
**3-regular** tree — the Bruhat-Tits tree of ℚ₂ (which is `(p+1) = 3`-regular for `p = 2`).

This file pins the exact gap. `root_adj_iff`: the root `[]` is adjacent to **exactly** its two children
`[0]` and `[1]` — it has **no parent / upward edge**, so the root has degree 2, while every non-root vertex
has degree 3 (parent + two children, `nonroot_has_parent`). That single missing edge at the root is the
whole gap to 3-regularity, and it is precisely the direction toward the chosen boundary end: the
Bruhat-Tits embedding *is* the attachment of the root's third edge toward an end. `EmbedsInThreeRegularTree`
states the sharp (non-vacuous) question; it is **left open** — a genuine 3-regular witness cannot be `tree`
itself (the root's degree 2 forbids it), and building one needs either the Ludwig-Merten BT formalization
(arXiv:2505.12933, `chrisflav/bruhat-tits`, not a dependency here) or a substantial in-house 3-regular
construction. This file proves the gap, not the embedding.
-/

namespace ZeroParadox

open SimpleGraph

/-- The stated `EmbedsAsRootedSubtree` is trivially satisfiable — the tree embeds into itself by the
identity. This exposes that the abstract statement is **vacuous**; the intended content is the 3-regular
version below, which this does NOT establish. -/
theorem embedsAsRootedSubtree_of_self : EmbedsAsRootedSubtree :=
  ⟨Vtx, tree, tree_isTree, ⟨Embedding.refl⟩⟩

/-- **The root's exact neighborhood.** The root `[]` is adjacent to exactly its two children `[0]` and `[1]`;
it has no parent / upward edge. So the root has degree 2 — the exact gap to 3-regularity. -/
theorem root_adj_iff (w : Vtx) : tree.Adj [] w ↔ w = [0] ∨ w = [1] := by
  constructor
  · rintro (⟨d, hd⟩ | ⟨d, hd⟩)
    · rw [List.nil_append] at hd
      fin_cases d
      · exact Or.inl hd
      · exact Or.inr hd
    · simp at hd
  · rintro (rfl | rfl)
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩

/-- **Every non-root vertex has a parent.** For `v ≠ []`, `v` is adjacent to `v.dropLast` (its parent), so
together with its two children `v ++ [0]`, `v ++ [1]` it has degree 3. The root is the sole exception. -/
theorem nonroot_has_parent (v : Vtx) (hv : v ≠ []) : tree.Adj v v.dropLast := by
  refine Or.inr ⟨v.getLast hv, ?_⟩
  rw [List.dropLast_append_getLast hv]

/-- **The sharp (non-vacuous) open question.** The real content: `tree` embeds into a tree in which every
vertex has exactly three neighbours — the Bruhat-Tits tree of ℚ₂. Unlike `EmbedsAsRootedSubtree` this is
NOT trivially true: `tree` itself is not a witness, because its root has degree 2 (`root_adj_iff`). Stated;
open. -/
def EmbedsInThreeRegularTree : Prop :=
  ∃ (W : Type) (T : SimpleGraph W),
    (∀ v : W, ∃ s : Finset W, s.card = 3 ∧ ∀ w, T.Adj v w ↔ w ∈ s) ∧
      T.IsTree ∧ Nonempty (tree ↪g T)

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms embedsAsRootedSubtree_of_self
#print axioms root_adj_iff
#print axioms nonroot_has_parent
end PurityCheck
