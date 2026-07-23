import ZeroParadox.Valuation.PoleCorners
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Experimental probe: is the μ/ν fork independent of the pole?

## Engineer's Take

I kept going on the axes, and this one is the interesting pair. The fork and the pole are separate
requirements, and yet on the pole the fork forces the snap. The two are independent as axes, and it is their
meeting that makes the collapse.

---

## Formal Overview (AI-assisted)

Continuing the mutual-independence sweep of the four axes. This probes **axis 2, the μ/ν fork** (a self-map
with a unique fixed point — the fixed-point structure) against **axis 1, the pole** (the two-element carrier
`{0, ∞}`). The `IrreversibilityProbe` already found these two *interact* (on the pole, a self-map with a
unique fixed point is forced to be the collapse — the snap). So the sharp question: are they nonetheless
**independent as requirements**, or does one entail the other?

Two witnesses (model / counter-model):

* **A fork with no pole** (`fork_without_pole`): the constant map `n ↦ 0` on `ℕ` has a **unique fixed
  point** (`0`) — the fork — on an **infinite** carrier, which is not the two-element pole. So the fork lives
  on non-poles.
* **A pole with no fork** (`pole_without_fork`): the two-element pole (`Fintype.card Pole = 2`) admits the
  identity self-map, which has **two** fixed points — **no unique** fixed point, so **no** fork. So the pole
  carrier does not entail the fork.

Neither entails the other: **the fork and the pole are independent axes** (`fork_and_pole_independent`).

**The nuance this probe sharpens (and it is the interesting part).** Independence *as requirements* coexists
with a genuine *interaction*: they are separable, yet where they **meet** — the fork placed on the pole —
`IrreversibilityProbe.pole_selfref_forces_irreversible` shows the fork is forced to the collapse, i.e. the
snap appears. So axes 1 and 2 are non-redundant, and it is precisely their **conjunction** that generates the
one-way direction. Independent axes, an emergent snap at their intersection.

**Honest scope.** This settles the pole-vs-fork pair. Combined with `IndependenceProbe` (chain vs. branching),
two of the six axis-pairs are now checked non-redundant; the remaining pairs are the larger completeness
check.
-/

namespace ZeroParadox

/-- **A fork with no pole.** The constant map `n ↦ 0` on `ℕ` has a unique fixed point `0` (the fork), on an
infinite carrier that is not the two-element pole. -/
theorem fork_without_pole : (∃ f : ℕ → ℕ, ∃! n, f n = n) ∧ Infinite ℕ :=
  ⟨⟨fun _ => 0, 0, rfl, fun _y hy => hy.symm⟩, inferInstance⟩

/-- **A pole with no fork.** The two-element pole admits the identity self-map, which has two fixed points
(`0` and `∞`) — no unique fixed point, hence no fork. The pole carrier does not entail the fork. -/
theorem pole_without_fork :
    Fintype.card Pole = 2 ∧ ∃ f : Pole → Pole, ¬ (∃! p, f p = p) := by
  refine ⟨by decide, Pole.cornerId, ?_⟩
  rintro ⟨p, -, huniq⟩
  have h0 : Pole.zero = p := huniq Pole.zero rfl
  have hi : Pole.infty = p := huniq Pole.infty rfl
  exact absurd (h0.trans hi.symm) (by decide)

/-- **The fork and the pole are independent axes.** A fork exists off the pole (`ℕ`, `n ↦ 0`); the pole
exists without a fork (identity, two fixed points). Neither entails the other — axes 1 and 2 are
non-redundant. Their *interaction* (fork on the pole ⇒ the snap) is `IrreversibilityProbe`, not an
entailment between the axes themselves. -/
theorem fork_and_pole_independent :
    ((∃ f : ℕ → ℕ, ∃! n, f n = n) ∧ Infinite ℕ) ∧
    (Fintype.card Pole = 2 ∧ ∃ f : Pole → Pole, ¬ (∃! p, f p = p)) :=
  ⟨fork_without_pole, pole_without_fork⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms fork_without_pole
#print axioms pole_without_fork
#print axioms fork_and_pole_independent
end PurityCheck
