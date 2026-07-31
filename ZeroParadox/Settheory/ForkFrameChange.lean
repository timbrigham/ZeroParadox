-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the ORDER-THEORETIC universal form of the POLE EXCHANGE (the snap-as-instance reading is ZP-Q's conjecture, not established here) — over any complete lattice, the frame-change (order-duality) swaps the fork's two closures (lfp ↔ gfp), and the fork collapses to the diagonal fixed point exactly when the two coincide (fork_collapse_iff). The domain-independent snap_is_frameflip; choice-free. The CATEGORICAL universal is a proven wall (category-relative, Cantor — see Category/Lawvere.lean); this is the order-level universal that does hold. Curated results indexed in ZeroParadox/MANIFEST.md.
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
(`snap_is_frameflip`) and category (`catseam_is_frameflip`) faces SHARE. Not "instances": neither
satisfies `fork_collapse_iff`'s hypotheses (complete lattice, monotone map) — see the declaration
docstring below, which states this in full.

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
    point where they coincide. That the snap IS an instance of that exchange is ZP-Q's conjecture, not
    established by these theorems.** The snap is one covering step
    off the zero face (`bot ⋖ a`, AX-B1), a separate object and a commitment. The cross-domain claim that
    the snap *is* the frame change remains this layer's open conjecture, as its file header states.

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
