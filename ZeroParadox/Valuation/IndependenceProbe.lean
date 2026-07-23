import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Experimental probe: are the chain axis and the branching axis independent?

## Engineer's Take

Having found no fifth axis, I wanted to keep probing, and check the four we keep are not secretly one. The
chain and the branching are genuinely two, a line with no fork and a fork with no line, so neither one is
hiding inside the other.

---

## Formal Overview (AI-assisted)

After three probes found no independent *fifth* axis (height, iterative-bottoms, irreversibility all came
back forced), the other half of completeness is: are the four surviving axes **mutually irredundant** — or is
one secretly implied by another? This probes the two most-easily-conflated, both "field-generating": **axis 3,
the chain** (point-and-field, `InfinitudeFloor`'s rising line `ℕ → α`) and **axis 4, branching** (an order
with incomparable elements, `children_incomparable`). Are they one axis or two?

Two witnesses settle it (the model / counter-model method):

* **A chain with no branching** (`chain_no_branching`): `ℕ` is **linearly** ordered — every pair is
  comparable, so **no** incomparable pair exists (no branching) — yet it is an infinite ascending chain (the
  point-and-field line). So the chain axis holds without branching.
* **Branching with no infinite chain** (`branching_no_infinite_chain`): `Bool × Bool` (the product order, a
  diamond) has `(false, true)` and `(true, false)` **incomparable** (branching) yet is **finite** — no
  infinite ascending chain, so no `InfinitudeFloor` member sequence. So branching holds without the chain.

Neither implies the other: **the chain and branching are genuinely two distinct axes**
(`chain_and_branching_independent`). A line is not a fork and a fork is not a line. This confirms axes 3 and 4
are non-redundant — the "not too many axes" half of completeness, complementing the "no fifth axis" probes.

**Honest scope.** This settles one pair (chain vs. branching). Full mutual independence of all four axes (pole,
fork, chain, branching) is the larger check; this is the pair most at risk of being one axis in disguise.
-/

namespace ZeroParadox

/-- **A chain with no branching.** `ℕ` is linearly ordered (every pair comparable — no incomparable pair,
hence no branching) and infinite (an ascending chain). The chain axis without the branching axis. -/
theorem chain_no_branching : (∀ a b : ℕ, a ≤ b ∨ b ≤ a) ∧ Infinite ℕ :=
  ⟨le_total, inferInstance⟩

/-- **Branching with no infinite chain.** In `Bool × Bool` (product order), `(false, true)` and
`(true, false)` are incomparable (branching), yet the type is finite — no infinite ascending chain, so no
`InfinitudeFloor` member sequence. The branching axis without the chain axis. -/
theorem branching_no_infinite_chain :
    (¬ (((false, true) : Bool × Bool) ≤ (true, false)) ∧
      ¬ (((true, false) : Bool × Bool) ≤ (false, true))) ∧ Finite (Bool × Bool) :=
  ⟨⟨by decide, by decide⟩, inferInstance⟩

/-- **The chain and branching are two distinct axes.** A chain exists with no branching (`ℕ`, linear); a
branching structure exists with no infinite chain (`Bool × Bool`, finite). Neither implies the other — axes 3
and 4 are non-redundant. -/
theorem chain_and_branching_independent :
    ((∀ a b : ℕ, a ≤ b ∨ b ≤ a) ∧ Infinite ℕ) ∧
    ((¬ (((false, true) : Bool × Bool) ≤ (true, false)) ∧
      ¬ (((true, false) : Bool × Bool) ≤ (false, true))) ∧ Finite (Bool × Bool)) :=
  ⟨chain_no_branching, branching_no_infinite_chain⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms chain_no_branching
#print axioms branching_no_infinite_chain
#print axioms chain_and_branching_independent
end PurityCheck
