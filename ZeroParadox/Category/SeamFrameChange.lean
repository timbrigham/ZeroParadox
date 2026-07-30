-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the category-frame realization of the POLE EXCHANGE (NOT of the snap - see the declaration docstring) — the zero-object seam is the μ-bottom (initial) in one chart and the ν-top (terminal) in the other, and the op-duality frame-change swaps the two charts (initial ↔ terminal), fixing the seam as an op-self-dual zero object. The categorical analog of RiemannSphere's rInv swapping 0↔∞. Curated results indexed in ZeroParadox/MANIFEST.md.
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
the frame-change — an `op`-self-dual zero object — the category-frame realization of the POLE EXCHANGE.
(NOT of the snap: no snap appears in `catseam_is_frameflip`; see its docstring.)

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

/-- **The seam is a FIXED POINT of the frame-change (category frame).**

    ⚠ **NAME CORRECTION (Tim, 2026-07-30). The handle `catseam_is_frameflip` is retained per the CC-2 /
    MC-1 convention — do not rename — but it OVERCLAIMS: the seam is not a frame flip, it is what the
    frame flip FIXES.** The docstring already said so ("the fixed point of the frame-change"); the name
    did not. No snap appears in this statement either.

    `Statement:` the seam is **initial AND terminal** (a zero object), and so is its opposite — four
    `Nonempty` witnesses. That is `op`-self-duality.

    `Reading:` this is "the bottom is **concurrently both poles**" in categorical dress — μ-bottom in one
    chart, ν-top in the other, **simultaneously**, with `op`-duality exchanging the charts and fixing the
    seam. Exactly as `rInv` exchanges `0 ↔ ∞` while ⊥ carries both readings. **The frame change is the
    exchange of the two poles; the seam is where they coincide.** The snap — one step off the zero face —
    is a separate object and is not established here.

    **⚠ CORRECTED 2026-07-30 (adversary gate, bedrock).** An earlier revision of this cross-link called `epsilon0_min_eq_max` an instance of `fork_collapse_iff`. **It is not.** `fork_collapse_iff` needs a UNIQUE fixed point, and `α ↦ ω^α` has a proper class of them — `ε₁, ε₂, …` all satisfy `ω ^ ε_ o = ε_ o` (Mathlib `omega0_opow_epsilon`) — so `lfp ≠ gfp` there and nothing collapses. There are TWO related coincidences, not one phenomenon with four witnesses:
    * **lfp = gfp** (a genuine `fork_collapse_iff` instance, needing uniqueness): `selfApp_bot_is_both_extremal`, whose fixed-point set is exactly `{⊥}` (`selfMem_eq_singleton_bot`), and the categorical zero object (`catseam_is_frameflip`, initial ∧ terminal).
    * **lfp = ⨆ of the approximating tower** (the Kleene shape, no uniqueness required): `epsilon0_min_eq_max`, which is literally what it states — ε₀ is the least fixed point AND the supremum of the ω-tower.

    **This IS a genuine lfp = gfp instance, in categorical form.** Initial = least, terminal =
    greatest, so "initial AND terminal" is one object carrying both extremal characterizations at once —
    the same shape as `epsilon0_min_eq_max` (at ε₀), `selfApp_bot_is_both_extremal` (at ⊥), and
    `fork_collapse_iff` (the abstract condition: `lfp = gfp` exactly when the fixed point is unique).
    Four witnesses, one phenomenon. In the four-corner classification
    (`Valuation/PoleCorners.lean`) this is **`cornerId`** — both poles concurrently, unchanged — as
    distinct from `swap` (the inversion) and `cornerZero` (the collapse that forgets which pole). -/
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
