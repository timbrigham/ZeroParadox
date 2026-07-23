-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The complexity ladder: the arity is the variable-count, and it climbs without bound

## Engineer's Take

The arity being open is quite literally the ability to reference this with more and more complex sets of
variables, and that was one of our original conditions. This makes the loop close in Lean: the ladder shows
there is no ceiling on how many variables a node can carry, so the width is free and unbounded.

This closed the loop, the arity being open as the ability to reference ever more complex variables, one of our
original conditions. Sometimes it helps to work through this from the ground up. Much of what is here
re-derives results the framework already has, and that is fine. The movement of the thought process itself was
what I needed.

---

## Formal Overview (AI-assisted)

The completeness-critic found the arity is the one un-captured degree of freedom (= AX-B1). Tim's reading: the
arity being open **is** the original condition — "reference this with more and more complex sets of variables."
This file makes that a theorem: the arity is the **variable-count** (independent distinctions at a node), and
it is an **unbounded ladder**.

`complexity_ladder n`: for every `n`, the bottom `∅` admits `n` **independent** successors — an injective
family `Fin n → Set ℕ` (the singletons `{0}, …, {n-1}`), each `⊇ ∅`, pairwise `⊆`-incomparable. So a node can
carry exactly `n` independent variables, for any `n`. `complexity_unbounded` is the ∀-form: there is **no
ceiling** — arity `n+1` strictly exceeds arity `n`, forever.

**What this says.** The branching *width* (the arity) is the number of independent variables the object
references at each step, and it is free and unbounded. This is the pivot's opening condition ("cover any
complexity of variables using the self-reference shape") realized as a checkable ladder: the chain gives
arbitrary *length* (axis 3), the arity gives arbitrary *width* (the free parameter). **AX-B1 is the knob** —
fixing the arity at two is choosing the minimal rung; the generic object supports every rung.

**Honest fence.** This is arbitrary variable *width* — not universal framework-encoding. "Cover any complexity
of variables" ✓ (the ladder has no ceiling); "encode any framework" ✗ (the μ/ν walls, self-reference not
closing, are untouched here). The ladder realizes the width condition without crossing the walls.
-/

namespace ZeroParadox

/-- **The complexity ladder.** For every `n`, the bottom `∅` admits `n` independent successors: an injective
family `Fin n → Set ℕ` (the singletons), each above `∅`, pairwise incomparable. A node carries exactly `n`
independent variables, for any `n`. -/
theorem complexity_ladder (n : ℕ) :
    ∃ f : Fin n → Set ℕ,
      Function.Injective f ∧
      (∀ i, (∅ : Set ℕ) ⊆ f i) ∧
      (∀ i j, i ≠ j → ¬ f i ⊆ f j) := by
  refine ⟨fun i => {(i : ℕ)}, ?_, ?_, ?_⟩
  · intro a b hab
    exact Fin.ext (Set.singleton_injective hab)
  · intro i
    exact Set.empty_subset _
  · intro i j hij hsub
    have hii : (i : ℕ) ∈ ({(i : ℕ)} : Set ℕ) := Set.mem_singleton_iff.mpr rfl
    have hmem : (i : ℕ) ∈ ({(j : ℕ)} : Set ℕ) := hsub hii
    exact hij (Fin.ext (Set.mem_singleton_iff.mp hmem))

/-- **No ceiling on variable-complexity.** For every `n` the bottom admits `n` independent successors — the
arity/width is unbounded, so the object references arbitrarily complex sets of variables. This is the pivot's
opening condition, checked; AX-B1 (binary) is the choice of the minimal rung. -/
theorem complexity_unbounded :
    ∀ n : ℕ, ∃ f : Fin n → Set ℕ,
      Function.Injective f ∧
      (∀ i, (∅ : Set ℕ) ⊆ f i) ∧
      (∀ i j, i ≠ j → ¬ f i ⊆ f j) :=
  complexity_ladder

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms complexity_ladder
#print axioms complexity_unbounded
end PurityCheck
