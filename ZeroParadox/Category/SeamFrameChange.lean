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

    **⚠ CORRECTED TWICE, 2026-07-30 (adversary gate, bedrock). Read the whole of this before citing
    any "min≡max family".** An earlier revision called `epsilon0_min_eq_max` an instance of
    `fork_collapse_iff`; a second revision fixed that but then called `selfApp_bot_is_both_extremal` and the
    categorical zero object instances instead. **BOTH claims are false, for the same reason: nothing here
    satisfies `fork_collapse_iff`'s hypotheses.** It requires `[CompleteLattice α]` and a *monotone*
    `f : α →o α` (`Settheory/FixedPointFork.lean`). Measured against that:
    * `epsilon0_min_eq_max` — `α ↦ ω^α` on `Ordinal` has a **proper class** of fixed points (`ε₁, ε₂, …`
      all satisfy `ω ^ ε_ o = ε_ o`, Mathlib `omega0_opow_epsilon`), so `lfp ≠ gfp` and nothing collapses.
    * `selfApp_bot_is_both_extremal` — `ZPSemilattice` is a **bare join-semilattice**, not a complete
      lattice, and `AbstractSelfApp.selfApp : L → L` is **not an `OrderHom`**.
    * `catseam_is_frameflip` — lives in `ModuleCat ℂ`, a **category**, not a lattice at all.

    **So there is no common instance and no "four witnesses of one phenomenon".** What these share is a
    SHAPE — one object carrying both extremal characterizations at once — and per this project's standing
    rule a shared shape across distinct structures is a **type boundary**, never a common theorem. State
    the shape; do not state an instance-of relation. Each fact stands on its own carrier:
    ε₀ is least-fixed-point **and** tower-supremum (the Kleene shape); ⊥ is least **and** greatest fixed
    point of `selfApp`; the seam is initial **and** terminal. `fork_collapse_iff` is a *fourth*, separate
    fact about complete lattices — the general condition under which a fork collapses — and is **not** the
    genus of the other three. -/
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
