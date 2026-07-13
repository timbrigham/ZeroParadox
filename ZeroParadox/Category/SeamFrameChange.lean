-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the category-frame realization of "the snap is the change of frame" — the zero-object seam is the μ-bottom (initial) in one chart and the ν-top (terminal) in the other, and the op-duality frame-change swaps the two charts (initial ↔ terminal), fixing the seam as an op-self-dual zero object. The categorical analog of RiemannSphere's rInv swapping 0↔∞. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.State.HilbFunctor
import ZeroParadox.Category.TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The frame-change in the category frame: `op`-duality swaps initial ↔ terminal at the seam

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The categorical analog of `RiemannSphere.rInv` (which swaps the poles `0 ↔ ∞`) is the **`op`-duality**,
which swaps the poles **initial ↔ terminal**. The zero-object seam `Z = fD_functor.obj 0`
(`hilbert_bottom_isZero`) is the μ-bottom (initial) in one chart and the ν-top (terminal) in the other;
this file bundles that P1 coincidence with the P2 frame-change: `op` carries the seam's initial-ness to
its op's terminal-ness and its terminal-ness to its op's initial-ness. The seam is the fixed point of
the frame-change — an `op`-self-dual zero object — the category-frame realization of "the snap is the
change of frame."

`catseam_is_frameflip`: the seam is (i) initial and (ii) terminal in `ModuleCat ℂ` (the two charts), and
under the `op` frame-change it is (iii) terminal and (iv) initial in `(ModuleCat ℂ)ᵒᵖ` (the swap). Off
the zero object the coincidence fails (`generic_object_empty_lim_ne_colim`, `SeamLimColim`), so — as with
`0` on the sphere — the frame-change fixes only the bottom.

**Fences.** Category point-of-view's shape of the frame-change; the abstract cross-domain "snap = frame
change" stays conjectural (type boundary; see `.claude-local/notes/frame_change_across_domains_2026-07-11.md`).
The content is a bundling of `hilbert_bottom_isZero` with Mathlib's `op`-duality; no mathematical novelty.
-/

namespace ZeroParadox

open CategoryTheory CategoryTheory.Limits

/-- The zero-object seam `Z = fD_functor.obj 0` (the Hilbert bottom). -/
noncomputable abbrev Z_seamFC : ModuleCat ℂ := fD_functor.obj 0

/-- **The frame-change in the category frame.** The seam is the μ-bottom (initial, chart A) and the ν-top
    (terminal, chart B); the `op`-duality frame-change swaps the two charts — carrying the seam's
    initial-ness to a terminal-ness of `op Z` and its terminal-ness to an initial-ness of `op Z`. So the
    seam is `op`-self-dual: the fixed point of the frame-change that swaps initial ↔ terminal, exactly as
    `rInv` swaps `0 ↔ ∞`. -/
theorem catseam_is_frameflip :
    Nonempty (IsInitial Z_seamFC)
      ∧ Nonempty (IsTerminal Z_seamFC)
      ∧ Nonempty (IsTerminal (Opposite.op Z_seamFC))
      ∧ Nonempty (IsInitial (Opposite.op Z_seamFC)) := by
  have hZ : IsZero Z_seamFC := hilbert_bottom_isZero
  exact ⟨⟨hZ.isInitial⟩, ⟨hZ.isTerminal⟩,
    ⟨terminalOpOfInitial hZ.isInitial⟩, ⟨initialOpOfTerminal hZ.isTerminal⟩⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms catseam_is_frameflip
end PurityCheck
