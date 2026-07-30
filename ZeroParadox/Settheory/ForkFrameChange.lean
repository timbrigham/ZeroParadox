-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the ORDER-THEORETIC universal form of "the snap is the change of frame" — over any complete lattice, the frame-change (order-duality) swaps the fork's two closures (lfp ↔ gfp), and the fork collapses to the diagonal fixed point exactly when the two coincide (fork_collapse_iff). The domain-independent snap_is_frameflip; choice-free. The CATEGORICAL universal is a proven wall (category-relative, Cantor — see Category/Lawvere.lean); this is the order-level universal that does hold. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Settheory.FixedPointFork
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The order-theoretic universal frame-change: duality swaps the fork's ends

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`fork_collapse_iff` (`Settheory/FixedPointFork.lean`) is the P1 spine: over a complete lattice a monotone
self-map's least fixed point `lfp` (μ, well-founded closure) and greatest fixed point `gfp` (ν,
non-well-founded closure) collapse to one point iff the map has a unique fixed point (the diagonal fixed
point). This file adds the P2 face — the **frame-change** — in its domain-independent form: the
**order-duality** (the abstract analog of `rInv` swapping `0 ↔ ∞` and `op` swapping initial ↔ terminal)
**swaps the two closures**: `lfp (dual f) = gfp f` and `gfp (dual f) = lfp f`. So the μ-closure and the
ν-closure are the two charts, order-duality is the frame-change between them, and the fork collapses at
the diagonal fixed point.

`fork_is_frameflip` bundles both faces: the duality-swap (P2) with `fork_collapse_iff` (P1). This is the
order-theoretic universal `snap_is_frameflip` — the domain-independent shape that the valuation
(`snap_is_frameflip`) and category (`catseam_is_frameflip`) instances realize concretely.

**Fences.** This is the **order-theoretic** universal (Knaster–Tarski world), choice-free. It is NOT the
categorical Lawvere universal, which is a proven **wall**: `Category/Lawvere.lean` shows the Lawvere
fixed-point test is category-relative — in **Set** no nontrivial total type carries a Lawvere witness
(Cantor), so the lattice bottom is a *posited* fixed point sharing the diagonal shape, not a literal
Lawvere instance. The cross-domain identity of all these fixed points remains a modeling commitment (type
boundary; `.claude-local/notes/frame_change_across_domains_2026-07-11.md`). No mathematical novelty:
the duality-swap is the standard `lfp`/`gfp` order-duality, bundled with the fork.

## Structure
- § I  Order-duality swaps the fork's two closures (`lfp ↔ gfp`)
- § II The universal frame-flip: both faces bundled
-/

namespace ZeroParadox

variable {α : Type*} [CompleteLattice α] (f : α →o α)

/-! ## § I — Order-duality swaps the two closures -/

/-- **Frame-change swaps the closures (μ → ν).** The least fixed point of the order-dual map is the
    greatest fixed point of the original: `lfp (dual f) = gfp f`. Order-duality — the abstract
    frame-change — carries the μ (well-founded) closure to the ν (non-well-founded) closure. -/
theorem lfp_dual_eq_gfp : (OrderHom.dual f).lfp = f.gfp := rfl

/-- **Frame-change swaps the closures (ν → μ).** Dually, `gfp (dual f) = lfp f`. -/
theorem gfp_dual_eq_lfp : (OrderHom.dual f).gfp = f.lfp := rfl

/-! ## § II — The universal frame-flip -/

/-- **The order-theoretic universal frame-flip.** Over any complete lattice: (i)-(ii) the order-duality
    frame-change swaps the fork's two closures `lfp ↔ gfp`, and (iii) the fork collapses to a single
    contact point iff the self-map has a unique fixed point (the diagonal fixed point) — `fork_collapse_iff`.
    The domain-independent shape realized concretely by the valuation (`snap_is_frameflip`) and category
    (`catseam_is_frameflip`) frame-flips. Choice-free.

    **Scope note (2026-07-30).** Of the three `*_is_frameflip` handles this is the only one whose name
    matches its statement: duality genuinely does exchange the fork's two ends. The other two overclaim and
    carry corrections in their own docstrings — `snap_is_frameflip` proves the tower limit's two
    chart-readings (**no snap appears in it**), and `catseam_is_frameflip` proves the seam is a **fixed
    point** of the flip, not a flip. **What all three establish is the exchange of the two poles and the
    point where they coincide — NOT that the snap is a change of frame.** The snap is one covering step
    off the zero face (`bot ⋖ a`, AX-B1), a separate object and a commitment. The cross-domain claim that
    the snap *is* the frame change remains this layer's open conjecture, as its file header states.

    **⚠ CORRECTED 2026-07-30 (adversary gate, bedrock).** An earlier revision of this cross-link called `epsilon0_min_eq_max` an instance of `fork_collapse_iff`. **It is not.** `fork_collapse_iff` needs a UNIQUE fixed point, and `α ↦ ω^α` has a proper class of them — `ε₁, ε₂, …` all satisfy `ω ^ ε_ o = ε_ o` (Mathlib `omega0_opow_epsilon`) — so `lfp ≠ gfp` there and nothing collapses. There are TWO related coincidences, not one phenomenon with four witnesses:
    * **lfp = gfp** (a genuine `fork_collapse_iff` instance, needing uniqueness): `selfApp_bot_is_both_extremal`, whose fixed-point set is exactly `{⊥}` (`selfMem_eq_singleton_bot`), and the categorical zero object (`catseam_is_frameflip`, initial ∧ terminal).
    * **lfp = ⨆ of the approximating tower** (the Kleene shape, no uniqueness required): `epsilon0_min_eq_max`, which is literally what it states — ε₀ is the least fixed point AND the supremum of the ω-tower.

    **Conjunct (iii), abstractly.** `f.lfp = f.gfp ↔ ∃! x, f x = x`
    says **least equals greatest exactly when the fixed point is unique** — the general condition of which
    `epsilon0_min_eq_max` (at ε₀), `selfApp_bot_is_both_extremal` (at ⊥) and `catseam_is_frameflip`
    (initial ∧ terminal) are instances. So this file carries both halves of the pole behaviour: (i)-(ii) the
    **inversion** (duality exchanging the ends) and (iii) the **coincidence** (when the ends are one). In
    the four-corner classification (`Valuation/PoleCorners.lean`) those are `swap` and `cornerId`
    respectively; the remaining two corners are the collapses, of which `cornerZero` is the irreversible one
    that forgets which pole it came from (`cornerZero_not_injective` there; `Miniature.lean`'s
    `collapse_irreversible` is the same fact on that file's own two-element pole, a different carrier). -/
theorem fork_is_frameflip :
    (OrderHom.dual f).lfp = f.gfp
      ∧ (OrderHom.dual f).gfp = f.lfp
      ∧ (f.lfp = f.gfp ↔ ∃! x, f x = x) :=
  ⟨lfp_dual_eq_gfp f, gfp_dual_eq_lfp f, fork_collapse_iff f⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms lfp_dual_eq_gfp
#print axioms gfp_dual_eq_lfp
#print axioms fork_is_frameflip
end PurityCheck
