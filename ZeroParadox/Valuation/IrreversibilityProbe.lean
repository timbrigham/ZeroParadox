-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCorners
import ZeroParadox.Order.Snap
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Experimental probe: is irreversibility (the snap direction) a fifth independent requirement?

## Engineer's Take

I wanted to probe whether the one direction we cannot reverse is its own requirement or whether it falls out
of the rest. We know exactly which direction we cannot make the transition on, and the probe says that
direction is not free, it is forced. The pole is two elements because two is where self-reference forces the
collapse.

This was the first real probe, testing whether the snap is its own requirement or falls out of the rest.
Sometimes it helps to work through this from the ground up. Much of what is here re-derives results the
framework already has, and that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

**The experiment.** The requirement axes so far: (1) the pole / four corners, (2) the μ/ν fixed-point fork,
(3) point-and-field via a chain, (4) branching / field. Candidate **fifth** axis: *irreversibility* — the
one-way snap direction (the collapse that forgets its origin). Independence test (the model / counter-model
method): does a structure exist that satisfies the other axes but is fully **reversible**? If yes,
irreversibility is a genuine independent axis; if the other axes force it, it is determined.

**Result: irreversibility is NOT a free fifth axis — it is over-determined, forced three ways.**

* **Order face — forced in every model.** `t_snap_irreversible` (`Order/Snap.lean`) is parametric in the
  carrier `L`: in *any* `ZPSemilattice`, `x ≤ y ∧ x ≠ y` forbids a `z` with `join y z = x`. This is just
  antisymmetry — it holds in every model, so it is forced by the order axioms, not independent.
* **Topological face — forced by branching.** `branching_is_the_snap_wall` (`BranchingSnapChain.lean`): total
  disconnectedness (axis 4, the branching) forces `c3_irreversible` (no continuous return). Forced by axis 4.
* **Pole face — forced at cardinality 2, and only there.** `pole_selfref_forces_irreversible`: at the
  two-element pole, a self-map with a **unique fixed point** (self-reference) *cannot be injective* — it must
  be a collapse (`decide`). So self-reference forces irreversibility *on the pole*. But
  `probe3_reversible_with_unique_fp` exhibits a **counter-model at three elements**: `![0,2,1]` on `Fin 3` is
  a **bijection** (fully reversible) with a **unique fixed point** — self-reference *without* irreversibility.

**The finding the probe surfaces.** Irreversibility is not independent — it is forced by the order
(antisymmetry), by branching (disconnectedness), and, at the pole, by self-reference. And the pole face
pins down *why the pole is two-element*: **two is exactly the cardinality at which self-reference forces the
one-way collapse** (`irreversibility_forced_at_pole_not_beyond` — forced at card 2, with the identity a
reversible unique-fixed-point map at card 1 and a reversible counter-model at card 3). So axis 1 (the two-element pole / four corners) and the snap (irreversibility) are
**linked by cardinality**: the pole's size is what makes the snap unavoidable. This is the third probe to
return "already forced" (after height and iterative-bottoms), further evidence the requirement set is closing.

**Honest scope.** Probes B/C test the *self-map* notion of irreversibility (injective vs. collapse); the
framework's snap is the *order* / *topological* one, forced by antisymmetry / branching respectively. The
three faces align; no single grand theorem is claimed to unify them here.
-/

namespace ZeroParadox

open ZeroParadox.Pole

/-! ### § I. Probe B — at the two-element pole, self-reference forces the collapse. -/

/-- Witness form (decidable): at the pole, a self-map with a unique fixed point (unfolded) has a collision. -/
theorem pole_selfref_not_inj_witness :
    ∀ f : Pole → Pole, (∃ p, f p = p ∧ ∀ q, f q = q → q = p) → ∃ a b, f a = f b ∧ a ≠ b := by decide

/-- **At the pole, a unique fixed point forces non-injectivity.** Every self-map of the two-element pole with
a *unique* fixed point (the self-reference requirement) is **not injective** — it must be a collapse
(`cornerZero` / `cornerInfty`), the one-way snap direction. Finite exhaustion. -/
theorem pole_selfref_forces_irreversible (f : Pole → Pole) (h : ∃! p, f p = p) :
    ¬ Function.Injective f := by
  obtain ⟨p, hp, huniq⟩ := h
  exact Function.not_injective_iff.mpr (pole_selfref_not_inj_witness f ⟨p, hp, huniq⟩)

/-! ### § II. Probe C — at three elements, self-reference does NOT force irreversibility. -/

/-- A counter-model at three elements: fix `0`, swap `1 ↔ 2`. -/
def probe3 : Fin 3 → Fin 3 := ![0, 2, 1]

theorem probe3_unique_fp_witness : probe3 0 = 0 ∧ ∀ x, probe3 x = x → x = 0 := by decide
theorem probe3_inj_witness : ∀ a b, probe3 a = probe3 b → a = b := by decide
theorem probe3_surj_witness : ∀ y, ∃ x, probe3 x = y := by decide

theorem probe3_unique_fp : ∃! x, probe3 x = x :=
  ⟨0, probe3_unique_fp_witness.1, probe3_unique_fp_witness.2⟩

/-- **The counter-model.** `probe3` has a **unique fixed point** (self-reference) *and* is a **bijection**
(fully reversible). So at three elements, self-reference does **not** force irreversibility — the forcing at
the pole is special to cardinality two. -/
theorem probe3_reversible_with_unique_fp :
    (∃! x, probe3 x = x) ∧ Function.Bijective probe3 :=
  ⟨probe3_unique_fp, (fun a b h => probe3_inj_witness a b h), probe3_surj_witness⟩

/-! ### § III. The threshold — irreversibility is forced by self-reference at the pole, not beyond. -/

/-- **Irreversibility is forced at the pole (card 2), not at card 3.** Two is the threshold at which
self-reference forces the one-way collapse: at the two-element pole every self-map with a unique fixed point
is non-injective, while at three elements a reversible witness with a unique fixed point exists. This links
the pole's cardinality (axis 1) to **irreversibility**: the pole is two-element *because* two is where a
unique fixed point already costs injectivity. **Not** "where self-reference forces the snap" — that was
this line until 2026-07-31, and non-injectivity is not occurrence; nothing here says anything moves. -/
theorem irreversibility_forced_at_pole_not_beyond :
    (∀ f : Pole → Pole, (∃! p, f p = p) → ¬ Function.Injective f) ∧
    (∃ g : Fin 3 → Fin 3, (∃! x, g x = x) ∧ Function.Bijective g) :=
  ⟨fun f h => pole_selfref_forces_irreversible f h, probe3, probe3_reversible_with_unique_fp⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms pole_selfref_forces_irreversible
#print axioms probe3_reversible_with_unique_fp
#print axioms irreversibility_forced_at_pole_not_beyond
end PurityCheck
