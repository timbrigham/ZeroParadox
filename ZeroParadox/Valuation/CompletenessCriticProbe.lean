-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicTree
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Completeness-critic probe: what property of the generic object do the four axes NOT capture?

## Engineer's Take

I went hunting for what the four axes miss, and it is the arity. Branching says it forks, and not into how
many, so a p-ary tree meets all four for any p. That free choice is exactly the binary commitment we already
flagged as the one real modeling assumption, and the hunt found it on its own.

This was the hunt for what the four axes miss, which turned out to be the arity. Sometimes it helps to work
through this from the ground up. Much of what is here re-derives results the framework already has, and that is
fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

The mutual-independence sweep (`ZeroParadox/Valuation/AxisSweepProbe.lean`) found the four axes (pole, fork,
chain, branching) distinct in pairs; no axis is a predicate there, so independence is not a theorem. The **completeness-critic** asks the opposite question: is there a property of the generic
object (the 2-adic tree boundary — a compact, totally disconnected, perfect Cantor set, in the sense of
Brouwer's 1910 topological characterization) that the four axes do
**not** pin down? If yes, that is a candidate fifth requirement.

**The finding: the branching axis does not fix the arity.** The branching axis says "there is a node with
`≤`-incomparable successors" — it does **not** say *how many*. Two witnesses:

* `binary_branch`: in `Bool × Bool`, the node `(false, false)` has **two** incomparable successors
  `(true, false)`, `(false, true)`.
* `ternary_branch`: in `Bool × Bool × Bool`, the node `(false, false, false)` has **three** pairwise
  incomparable successors `(true,false,false)`, `(false,true,false)`, `(false,false,true)`.

These are finite lattices, not trees, with no infinite chain, so they fail the chain axis: `arity_is_uncaptured`
shows only that branching leaves the arity **free**. `Reading:` conjecture: a `p`-ary tree meets all four, `p ≥ 2`.

**What the un-captured freedom IS.** The framework already names it: **AX-B1**, "binary / discrete existence,"
the framework's *one substantive modeling commitment* (a discrete alphabet, and specifically the binary
alphabet, over a continuum). The completeness-critic hunt independently re-surfaces exactly this: arity is a
degree of freedom the branching axis does not force, so fixing it (to two) is a **commitment, not a theorem** —
which is precisely AX-B1's status. The `IrreversibilityProbe` cardinality result complements this: two is the
*value-pole* threshold (a unique fixed point already costs injectivity there - irreversibility, not
occurrence); binary *arity* is the separate branching choice.

`Reading:` the completeness picture, a conjecture: no forced fifth *structural* axis, the four are mutually independent, and the one
thing left open is the arity — recovered here as AX-B1, a modeling commitment rather than a derived axis. This
is evidence the four structural axes plus the single AX-B1 commitment are the whole story.

**§ V — Perfectness (no isolated points) is DERIVED, not a new axis.** A second Cantor-set property:
*perfect* = every point is a limit of distinct points (no isolated point). `boundary_perfect`: in the tree
boundary `End`, for every end `x` and every depth `n`, there is a **different** end `y` agreeing with `x` on
the first `n` digits (flip the digit at position `n`). So every point is a limit of distinct points — the
boundary is perfect — and this falls straight out of the **branching** axis (at each depth there is an
alternative digit). Perfectness is therefore *derived*, not an independent fifth axis.

**Honest scope.** Two Cantor-set properties probed: **arity** is un-captured (= AX-B1, a commitment);
**perfectness** is derived from branching (no new axis). This does not claim AX-B1 is the *unique* remaining
freedom (compactness in particular tracks *finite* arity, a facet of this same commitment), but the pattern
holds: the structural properties are derived, and the one genuine open degree of freedom is the arity.
-/

namespace ZeroParadox

/-! ### § I. A binary branch (arity 2). -/

/-- **Binary branch.** In `Bool × Bool`, `(false, false)` has two incomparable successors. -/
theorem binary_branch :
    (((false, false) : Bool × Bool) ≤ (true, false)) ∧
    (((false, false) : Bool × Bool) ≤ (false, true)) ∧
    ¬ (((true, false) : Bool × Bool) ≤ (false, true)) ∧
    ¬ (((false, true) : Bool × Bool) ≤ (true, false)) := by decide

/-! ### § II. A ternary branch (arity 3). -/

/-- **Ternary branch.** In `Bool × Bool × Bool`, `(false, false, false)` has three pairwise-incomparable
successors — the same branching axis, one higher arity. -/
theorem ternary_branch :
    (((false, false, false) : Bool × Bool × Bool) ≤ (true, false, false)) ∧
    (((false, false, false) : Bool × Bool × Bool) ≤ (false, true, false)) ∧
    (((false, false, false) : Bool × Bool × Bool) ≤ (false, false, true)) ∧
    ¬ (((true, false, false) : Bool × Bool × Bool) ≤ (false, true, false)) ∧
    ¬ (((false, true, false) : Bool × Bool × Bool) ≤ (false, false, true)) ∧
    ¬ (((false, false, true) : Bool × Bool × Bool) ≤ (true, false, false)) := by decide

/-! ### § III. The branching axis does not fix the arity. -/

/-- `Statement:` the conjunction of `binary_branch` and `ternary_branch`: a node with two incomparable
successors in `Bool × Bool`, and one with three in `Bool × Bool × Bool`. `Reading:` the branching axis does not
fix the arity. Both are finite lattices with no infinite chain, so the other three axes are not tested. -/
theorem arity_is_uncaptured :
    ((((false, false) : Bool × Bool) ≤ (true, false)) ∧
      (((false, false) : Bool × Bool) ≤ (false, true)) ∧
      ¬ (((true, false) : Bool × Bool) ≤ (false, true)) ∧
      ¬ (((false, true) : Bool × Bool) ≤ (true, false))) ∧
    ((((false, false, false) : Bool × Bool × Bool) ≤ (true, false, false)) ∧
      (((false, false, false) : Bool × Bool × Bool) ≤ (false, true, false)) ∧
      (((false, false, false) : Bool × Bool × Bool) ≤ (false, false, true)) ∧
      ¬ (((true, false, false) : Bool × Bool × Bool) ≤ (false, true, false)) ∧
      ¬ (((false, true, false) : Bool × Bool × Bool) ≤ (false, false, true)) ∧
      ¬ (((false, false, true) : Bool × Bool × Bool) ≤ (true, false, false))) :=
  ⟨binary_branch, ternary_branch⟩

/-! ### § IV. Branching does not even force FINITE arity — so compactness is part of the commitment too. -/

/-- **Infinite branching.** In `Set ℕ`, the bottom `∅` has infinitely many pairwise-incomparable successors —
the singletons `{i}` (`{i} ⊆ {j}` iff `i = j`). So the branching axis does not force *finite* arity, let
alone binary. Hence "finite arity" — which is what makes the boundary *compact* — is itself part of the AX-B1
commitment, at a deeper level than binary-vs-ternary: the arity is structurally free all the way up. -/
theorem infinite_branch :
    (∀ i : ℕ, (∅ : Set ℕ) ⊆ {i}) ∧ (∀ i j : ℕ, i ≠ j → ¬ ({i} ⊆ ({j} : Set ℕ))) := by
  refine ⟨fun i => Set.empty_subset _, fun i j hij hsub => ?_⟩
  exact hij (hsub rfl)

/-! ### § V. Perfectness (no isolated points) is derived from branching. -/

/-- **The boundary is perfect.** For every end `x` and every depth `n`, there is a different end `y` agreeing
with `x` on the first `n` digits (flip digit `n`). So no point is isolated — every point is a limit of
distinct points. This follows from branching (an alternative digit at each depth), so perfectness is derived,
not an independent axis. -/
theorem boundary_perfect (x : End) (n : ℕ) :
    ∃ y : End, y ≠ x ∧ ∀ k, k < n → y k = x k := by
  refine ⟨fun k => if k = n then x n + 1 else x k, ?_, ?_⟩
  · intro h
    have hn : (if n = n then x n + 1 else x n) = x n := congrFun h n
    rw [if_pos rfl] at hn
    exact absurd hn ((by decide : ∀ a : Fin 2, a + 1 ≠ a) (x n))
  · intro k hk
    show (if k = n then x n + 1 else x k) = x k
    rw [if_neg (Nat.ne_of_lt hk)]

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms binary_branch
#print axioms ternary_branch
#print axioms arity_is_uncaptured
#print axioms infinite_branch
#print axioms boundary_perfect
end PurityCheck
