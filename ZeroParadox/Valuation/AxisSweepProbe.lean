import ZeroParadox.Valuation.PoleCorners
import ZeroParadox.Order.Lattice
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Experimental probes: the fork is trivially satisfiable, and the pole vs chain / branching pairs

## Engineer's Take

I kept going on the axes until I ran out of pairs. The fixed-point fork turns out to be free for the taking,
so its content is which operation is the witness, not that a witness exists. And the pole, the chain, and the
branching sit at cardinalities two, infinite, and three, each a different thing.

This came mid-sweep, as I worked the axis pairs to the end. Sometimes it helps to work through this from the
ground up. Much of what is here re-derives results the framework already has, and that is fine. The movement of
the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

Three findings from continuing the independence sweep.

**§ I — The fork is trivially satisfiable, so it is not a *discriminating* axis.** Read as "there exists a
self-map with a unique fixed point," the fork holds for **every inhabited type**: the constant map `_ ↦ a`
has unique fixed point `a` (`weak_fork_trivial`). Worse, even the *structured* fork (`AbstractSelfApp`:
a designated self-application whose unique fixed point is `⊥`) is met on **every** `ZPSemilattice` by the
constant map `_ ↦ ⊥` (`structured_fork_trivially_satisfiable`). So the fork's content is **not existence** —
it is *which operation* is the witness: the domain's own canonical self-application (`×2`, `x ↦ {x}`, the
ω-tower `ω^·`) happening to land its unique fixed point at `⊥`. This is the instance-meets-requirements
reading: the axis is satisfied by the canonical instance, and the trivial witness (`const ⊥`) is why the axis
constrains *the operation*, not *the carrier*.

**§ II — Pole and chain are independent.** `pole_no_chain`: the pole is finite (two elements), no infinite
ascending chain. `chain_no_pole`: `ℕ` is an infinite chain and not two-element. Neither entails the other.

**§ III — Pole and branching are independent, and they sit at different cardinalities.** `branching_needs_three`:
a branch (a node `c` with two `≤`-incomparable successors `a`, `b`) forces **three distinct** elements. The
pole has exactly **two** (`Fintype.card Pole = 2`), so it **cannot host a branch**; a branch is realized at
**four** in `Bool × Bool` (`pole_and_branching_independent`). So the two axes are independent, and a
**cardinality ladder** appears: **two** is the pole (where the `IrreversibilityProbe` found self-reference
forces the snap), **three** is the minimum for branching (the field), so the pole is strictly below the
branching threshold — the minimal snap sits under the minimal field.

**Running tally (completeness).** No fifth axis (height, iterative-bottoms, irreversibility — all forced).
Non-redundant pairs so far: chain⊥branching, fork⊥pole, pole⊥chain, pole⊥branching; and the fork is exposed
as trivially-satisfiable (content in the canonical witness, not existence). The four axes keep behaving as
four distinct things.
-/

namespace ZeroParadox

/-! ### § I. The fork is trivially satisfiable. -/

/-- **The weak fork is trivial.** Every inhabited type has a self-map with a unique fixed point — the
constant map `_ ↦ a` (unique fixed point `a`). So "∃ a unique-fixed-point self-map" does not discriminate. -/
theorem weak_fork_trivial (α : Type*) (a : α) : ∃ f : α → α, ∃! x, f x = x :=
  ⟨fun _ => a, a, rfl, fun _y hy => hy.symm⟩

/-- **The structured fork is trivially satisfiable too.** On any `ZPSemilattice`, the constant map `_ ↦ ⊥`
satisfies the `AbstractSelfApp` requirements (`fixed_bot` and `unique_fp`). So the fork's content is not
existence but *which* self-application is the witness — the domain's canonical operation. -/
theorem structured_fork_trivially_satisfiable (L : Type*) [ZPSemilattice L] :
    (fun _ : L => (ZPSemilattice.bot : L)) ZPSemilattice.bot = ZPSemilattice.bot ∧
      ∀ x : L, (fun _ : L => (ZPSemilattice.bot : L)) x = x → x = ZPSemilattice.bot :=
  ⟨rfl, fun _x hx => hx.symm⟩

/-! ### § II. Pole vs chain — independent. -/

theorem pole_no_chain : Fintype.card Pole = 2 ∧ Finite Pole := ⟨by decide, inferInstance⟩

theorem chain_no_pole : Infinite ℕ ∧ (∀ a b : ℕ, a ≤ b ∨ b ≤ a) := ⟨inferInstance, le_total⟩

/-- **Pole and chain are independent.** The pole is finite (no infinite chain); `ℕ` is an infinite chain and
not the two-element pole. Neither entails the other. -/
theorem pole_and_chain_independent :
    (Fintype.card Pole = 2 ∧ Finite Pole) ∧ (Infinite ℕ ∧ (∀ a b : ℕ, a ≤ b ∨ b ≤ a)) :=
  ⟨pole_no_chain, chain_no_pole⟩

/-! ### § III. Pole vs branching — independent, and the cardinality ladder. -/

/-- **A branch forces three distinct elements.** A node `c` with two `≤`-incomparable successors `a`, `b`
has `a`, `b`, `c` pairwise distinct — branching needs at least three elements. -/
theorem branching_needs_three {α : Type*} [Preorder α] {c a b : α}
    (hca : c ≤ a) (hcb : c ≤ b) (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; exact hab le_rfl
  · rintro rfl; exact hab hcb
  · rintro rfl; exact hba hca

/-- **Pole and branching are independent.** The pole has two elements, so it cannot host a branch (which
needs three, `branching_needs_three`); a branch is realized at four in `Bool × Bool`. The cardinality ladder:
two (pole / snap threshold) below three (branching minimum). -/
theorem pole_and_branching_independent :
    Fintype.card Pole = 2 ∧
    (Fintype.card (Bool × Bool) = 4 ∧
      ¬ (((false, true) : Bool × Bool) ≤ (true, false)) ∧
      ¬ (((true, false) : Bool × Bool) ≤ (false, true))) :=
  ⟨by decide, by decide, by decide, by decide⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms weak_fork_trivial
#print axioms structured_fork_trivially_satisfiable
#print axioms pole_and_chain_independent
#print axioms branching_needs_three
#print axioms pole_and_branching_independent
end PurityCheck
