import Mathlib.Order.FixedPoints

/-!
# ZP-P: The Fixed-Point Fork

**Synthesis layer (not foundational).** This file is the abstract spine of the fixed-point fork:
over a complete lattice, a monotone self-map has a **least fixed point** and a **greatest fixed
point** (Knaster–Tarski; Mathlib's `OrderHom.lfp` / `OrderHom.gfp`), and these two ends collapse to a
single point exactly when the map has a unique fixed point. The intended reading is that a
self-referential operator's least fixed point is its inductive / well-founded closure and its greatest
fixed point its coinductive / non-well-founded closure; that reading is the initial-algebra /
final-coalgebra picture (a categorical setting), offered here as analogy — what is *proved* below is
purely the order-theoretic lfp/gfp statement. In the Zero Paradox the single collapse point is the
diagonal fixed point ⊥ (the self-containing bottom).

Naming note: this layer's informal nickname is "the fork." The word *porthole* is used elsewhere in
this repo (ZP-J Wheel) for a different, narrower thing — the `∞ ≠ ⊥` separation (`inf_ne_bot`). To
avoid overloading it, this file uses **fork** for the structure and theorem names.

This generalizes the ZFC+Foundation / ZFC+AFA "orthogonal at one contact point" claim: that pairing is
the *set-theory instance* of this fork. In the standard category-theoretic characterization
(Aczel; Lambek) Foundation corresponds to the initial algebra (μ) and AFA to the final coalgebra (ν)
of the (small/bounded) powerset functor; in that concrete set instance the Quine atom ⊥={⊥} is exactly
an element of νF that is not in μF. (The "final coalgebra of powerset" needs the bounded-powerset
qualification to live in **Set**; stated unqualified it is loose.)

## The complete concept is three tiers — only TIER 1 lives here

1. **Schema (this file, Lean theorems):** the lfp/gfp fork collapses to one point iff the self-map
   has a unique fixed point. Pure order theory over a complete lattice (Knaster–Tarski), built on
   Mathlib's `OrderHom.lfp` / `OrderHom.gfp`.
2. **Instance catalog (other layers — referenced, not re-proved here):** set theory (ZP-J/K,
   AbstractSelfApp / Quine atom), number systems (ZP-B/F, ℝ vs ℚ₂ via Ostrowski), the categorical
   parent (W-types vs M-types, `QPF.Fix` vs `QPF.Cofix`).
3. **Unification (prose conjecture, FENCED — never a Lean claim):** that the contact points of all
   instances are faces of *one* object (the diagonal fixed point). This is a type boundary, not a
   missing proof: `x = y` across distinct categories is not a well-formed proposition.

## Fences

- **Hard fence (permanent):** cross-instance identity ("the contact points are one object") is not a
  theorem and cannot be — it is a definitional/modeling commitment. Each framework forks at *its own*
  contact point; that is all that is claimed formally.
- **Soft fence (conjecture):** that *every* domain fork is an instance of this μ/ν schema. The
  schema is a theorem here and for canonical functors; "every fork is μ/ν" is the open
  generalization. (The Ostrowski / ℝ-vs-ℚ₂ instance, in particular, is theorem-backed on its own
  terms and is NOT claimed to be a μ/ν instance.)

Per-instance forks are theorems and are not hedged.

## Status

PROVED. Four theorems, no `sorry`; choice-free (`[propext, Quot.sound]` only — see PurityCheck).
-/

namespace ZeroParadox.ZPP

set_option maxHeartbeats 400000

variable {α : Type*} [CompleteLattice α] (f : α →o α)

/-- **The fork.** The least fixed point never exceeds the greatest: the inductive closure sits below
the coinductive closure. (Re-states Mathlib's `OrderHom.lfp_le_gfp` as the named width of the fork.) -/
theorem fork_le : f.lfp ≤ f.gfp :=
  f.lfp_le_gfp

/-- **Collapse, direction 1.** If `f` has a fixed point `x` that is its *only* fixed point, then both
ends of the fork land on `x`: the inductive and coinductive closures coincide at the contact point. -/
theorem collapse_of_unique (x : α) (_hx : f x = x) (huniq : ∀ y, f y = y → y = x) :
    f.lfp = x ∧ f.gfp = x :=
  ⟨huniq f.lfp f.map_lfp, huniq f.gfp f.map_gfp⟩

/-- **Collapse, direction 2.** If the two ends of the fork coincide, the common value is the unique
fixed point: every fixed point lies between `lfp` and `gfp`, so collapse forces uniqueness. -/
theorem unique_of_collapse (h : f.lfp = f.gfp) :
    ∀ y, f y = y → y = f.lfp := by
  intro y hy
  have h1 : f.lfp ≤ y := f.lfp_le_fixed hy
  have h2 : y ≤ f.gfp := f.le_gfp (le_of_eq hy.symm)
  rw [← h] at h2
  exact le_antisymm h2 h1

/-- **Fork theorem (the schema's spine).** The fork collapses to a single contact point *iff* the
self-referential operator has a unique fixed point. This is the abstract form of "the framework forks,
and the diagonal fixed point is where the two closures meet." -/
theorem fork_collapse_iff :
    f.lfp = f.gfp ↔ ∃! x, f x = x := by
  constructor
  · intro h
    exact ⟨f.lfp, f.map_lfp, fun y hy => unique_of_collapse f h y hy⟩
  · rintro ⟨x, hx, huniq⟩
    obtain ⟨hlfp, hgfp⟩ := collapse_of_unique f x hx huniq
    rw [hlfp, hgfp]

/-! ## Engineer's Take

TODO (Tim): Engineer's Take — write in your own voice.
-/

section PurityCheck
-- All four report `[propext, Quot.sound]` only — NO `Classical.choice`. The fork schema spine is
-- choice-free. (propext = propositional extensionality, Quot.sound = quotient soundness; both are
-- benign Mathlib-wide kernel axioms, not the Axiom of Choice.) Consistent with the choice-free core:
-- see ZeroParadox/AxiomProfile.lean.
#print axioms fork_le
#print axioms collapse_of_unique
#print axioms unique_of_collapse
#print axioms fork_collapse_iff
end PurityCheck

end ZeroParadox.ZPP
