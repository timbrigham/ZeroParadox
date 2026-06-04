import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENat.Basic
import Mathlib.Tactic

/-!
# ZP-B Padic Tree: ZP's rooted 2-adic tree as a graph (LOCAL / EXPLORATORY STUB)

## Engineer's Take

TODO (Tim): your own words go here.

---

## Formal Overview (AI-assisted)

**Status: STUB.** All nontrivial proofs are `sorry`. This file makes ZP's 2-adic tree
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
  symm := by sorry
  loopless := by sorry

/-- It is a tree (connected + acyclic). Mirrors Ludwig–Merten `Graph/Tree.lean`. -/
theorem tree_isTree : tree.IsTree := by sorry

/-- Interior regularity: a non-root vertex's neighbors are exactly its two children and its
    parent (three of them) — the (p+1 = 3)-regularity of the BT tree for p = 2. Mirrors
    Ludwig–Merten `Graph/Regular.lean`, stated as a neighbor-set equality to avoid `Fintype`. -/
theorem neighborSet_interior (v : Vtx) (hv : v ≠ root) :
    tree.neighborSet v = {v ++ [0], v ++ [1], v.dropLast} := by sorry

/-- Root regularity: the root has exactly its two children as neighbors (degree 2, no parent). -/
theorem neighborSet_root : tree.neighborSet root = {root ++ [0], root ++ [1]} := by sorry

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
theorem botEnd_val_top : endVal botEnd = ⊤ := by sorry

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

end ZeroParadox.PadicTree
