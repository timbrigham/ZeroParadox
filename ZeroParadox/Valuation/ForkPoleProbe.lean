-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCorners
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Experimental probe: is the μ/ν fork independent of the pole?

## Engineer's Take

I kept going on the axes, and this one is the interesting pair. The fork and the pole are separate
requirements, and yet on the pole the fork forces a collapse, and I read that collapse as the snap. There is a
fork with no pole. On the pole it depends on the map: the identity has no fork, a constant map does. And it is
their meeting that makes the collapse.

This was the interesting pair, the fork and the pole, separate and yet meeting to make the snap. Sometimes it
helps to work through this from the ground up. Much of what is here re-derives results the framework already
has, and that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

Continuing the mutual-independence sweep of the four axes. This probes **axis 2, the μ/ν fork** (a self-map
with a unique fixed point — the fixed-point structure) against **axis 1, the pole** (the two-element carrier
`{0, ∞}`). The `IrreversibilityProbe` already found these two *interact* (on the pole, a self-map with a
unique fixed point is necessarily non-injective — the one-way collapse).

`Statement:` non-injectivity on the pole. `Reading:` the framework reads that collapse as the snap;
conjectural, since no transition appears in the statement.

So the sharp question: does either entail the other?

* **A fork off the pole** (`fork_without_pole`): the constant map `n ↦ 0` on `ℕ` has a **unique fixed
  point** (`0`) on an **infinite** carrier, which is not the two-element pole. The fork does not need the pole.
* **On the pole, not every map carries the fork** (`pole_without_fork`): the two-element pole
  (`Fintype.card Pole = 2`) admits the identity self-map, which has **two** fixed points, so that one map has
  **no unique** fixed point.
* **On the pole, a constant map does carry it**: `Pole.cornerZero` has the unique fixed point `Pole.zero` (the
  `example` after `pole_without_fork`). Every inhabited carrier has such a map (`weak_fork_trivial`,
  `ZeroParadox/Valuation/AxisSweepProbe.lean`), so read as "some self-map has a unique fixed point" the pole
  entails the fork.

`fork_and_pole_independent` is the conjunction of the first two witnesses, and states nothing more.

**The interaction.** Where they meet, a self-map of the pole with a unique fixed point,
`IrreversibilityProbe.pole_selfref_forces_irreversible` shows that map is non-injective: the collapse.

**Honest scope.** This settles which maps on the pole carry the fork; it does not make the pair independent.
`IndependenceProbe` sweeps chain vs. branching; the remaining pairs are the larger completeness check.
-/

namespace ZeroParadox

/-- **A fork with no pole.** The constant map `n ↦ 0` on `ℕ` has a unique fixed point `0` (the fork), on an
infinite carrier that is not the two-element pole. -/
theorem fork_without_pole : (∃ f : ℕ → ℕ, ∃! n, f n = n) ∧ Infinite ℕ :=
  ⟨⟨fun _ => 0, 0, rfl, fun _y hy => hy.symm⟩, inferInstance⟩

/-- **On the pole, not every map carries the fork.** The two-element pole admits the identity self-map, which
has two fixed points (`0` and `∞`), so that map has no unique fixed point. One map, not the carrier: a
constant map on the pole has one (the `example` below). -/
theorem pole_without_fork :
    Fintype.card Pole = 2 ∧ ∃ f : Pole → Pole, ¬ (∃! p, f p = p) := by
  refine ⟨by decide, Pole.cornerId, ?_⟩
  rintro ⟨p, -, huniq⟩
  have h0 : Pole.zero = p := huniq Pole.zero rfl
  have hi : Pole.infty = p := huniq Pole.infty rfl
  exact absurd (h0.trans hi.symm) (by decide)

-- Statement: on the pole the constant map `Pole.cornerZero` has the unique fixed point `Pole.zero`.
example : ∃ f : Pole → Pole, ∃! p, f p = p :=
  ⟨Pole.cornerZero, Pole.zero, rfl, fun _y hy => hy.symm⟩

/-- **The two witnesses, conjoined.** A fork exists off the pole (`ℕ`, `n ↦ 0`), and on the pole the identity
has no unique fixed point. It does not say the pole lacks a fork: a constant map on the pole has one (the
`example` after `pole_without_fork`). The interaction (a unique fixed point on the pole forces
non-injectivity) is `IrreversibilityProbe`. -/
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
