-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the category-frame realization of the POLE EXCHANGE (the snap-as-instance reading is ZP-Q's conjecture, not established here - see the declaration docstring) — the zero-object seam is the μ-bottom (initial) in one chart and the ν-top (terminal) in the other, and the op-duality frame-change exchanges the two characterisations (initial ↔ terminal) the zero object carries at once; its opposite is again a zero object, as every zero object's is (IsZero.op). On the sphere, RiemannSphere's rInv instead exchanges two distinct points 0 ↔ ∞. Curated results indexed in ZeroParadox/MANIFEST.md.
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
its op's terminal-ness and its terminal-ness to its op's initial-ness: an `op`-self-dual zero object,
as every zero object is (`IsZero.op`), the category-frame realization of the POLE EXCHANGE.
`Statement:` COINCIDENCE — the seam is initial AND terminal in `ModuleCat ℂ`, both at once
(`catseam_is_frameflip` (i) and (ii)). This is the KIND `CLAUDE.md`'s table lists it under.
`Statement:` INVERSION — and `op`-duality exchanges those two characterisations: the seam's opposite
is terminal and initial in `(ModuleCat ℂ)ᵒᵖ` (`catseam_is_frameflip` (iii) and (iv)). The theorem
bundles both KINDs; that is what makes it a *self-dual* zero object rather than either fact alone.
`Reading:` INVERSION — the framework reads the snap as an instance of that exchange. Conjectural: no snap
appears in `catseam_is_frameflip`, and ZP-Q holds the identification open.

`catseam_is_frameflip`: the seam is (i) initial and (ii) terminal in `ModuleCat ℂ` (the two charts), and
under the `op` frame-change it is (iii) terminal and (iv) initial in `(ModuleCat ℂ)ᵒᵖ` (the swap). On
the sphere `rInv` exchanges two distinct points `0`, `∞` (`rInv_swaps`); `op` exchanges two characterisations
a zero object carries at once. Off it the coincidence fails at `ModuleCat.of ℂ ℂ` (`generic_object_empty_lim_ne_colim`).

**Fences.** Category point-of-view's shape of the frame-change; the abstract cross-domain "snap = frame
change" stays conjectural (type boundary).
The content is a bundling of `hilbert_bottom_isZero` with Mathlib's `op`-duality; no mathematical novelty.

Prior art (cited, not reproved): that a zero object stays zero under `op` is Mathlib's
`CategoryTheory.Limits.IsZero.op` (`Mathlib/CategoryTheory/Limits/Shapes/ZeroObjects.lean:126`,
`(h : IsZero X) : IsZero (Opposite.op X)`), with `IsZero.unop` at `:130`.
-/

namespace ZeroParadox

open CategoryTheory CategoryTheory.Limits

/-- The zero-object seam `Z = fD_functor.obj 0` (the Hilbert bottom). -/
noncomputable abbrev Z_seamFC : ModuleCat ℂ := fD_functor.obj 0

/-- **The seam and its opposite are both zero objects (category frame, `op`-self-duality).**

    ⚠ **NAME CORRECTION (Tim, 2026-07-30). The handle `catseam_is_frameflip` is retained per the CC-2 /
    MC-1 convention — do not rename — but it OVERCLAIMS: the seam is not a frame flip.** No snap appears in this statement either.

    `Statement:` COINCIDENCE — the seam is **initial AND terminal** at once, a zero object (conjuncts
    (i) and (ii)).
    `Statement:` INVERSION — `op` exchanges the two characterisations, initial and terminal, that the
    seam already carries: its opposite is terminal and initial (conjuncts (iii) and (iv)). Its opposite
    is again a zero object, as every zero object's is (`IsZero.op`), so `op` singles out no object here.
    `Reading:` INVERSION — by contrast, on the sphere (a different carrier, a different theorem) the
    exchange is of two distinct points: `rInv` swaps `0` and `∞` (`rInv_swaps`).

    `Reading:` COINCIDENCE and INVERSION — this is "the bottom is **concurrently both poles**" in categorical dress — μ-bottom in one
    chart, ν-top in the other, **simultaneously**. **The frame change is the exchange of the two
    characterisations; the seam is the object that carries both.** No snap transition appears in the
    statement, so the snap-as-instance reading stays ZP-Q's conjecture.

    **⚠ CORRECTED TWICE, 2026-07-30 (adversary gate, bedrock). Read the whole of this before citing
    any "min≡max family".** An earlier revision called `epsilon0_min_eq_max` an instance of
    `fork_collapse_iff`; a second revision fixed that but then called `selfApp_bot_is_both_extremal` and the
    categorical zero object instances instead. **BOTH claims are false, for the same reason: nothing here
    satisfies `fork_collapse_iff`'s hypotheses.** It requires `[CompleteLattice α]` and a *monotone*
    `f : α →o α` (`Settheory/FixedPointFork.lean`). Measured against that:
    * `epsilon0_min_eq_max` — `α ↦ ω^α` on `Ordinal` has a **proper class** of fixed points (`ε₁, ε₂, …`
      all satisfy `ω ^ ε_ o = ε_ o`, Mathlib `omega0_opow_epsilon`), so the uniqueness side of (iii)
      fails. The case is in fact stronger than that and the earlier wording under-stated it: `Ordinal`
      carries no `CompleteLattice` instance in the pin, so `lfp` and `gfp` are not defined there at all
      and `lfp ≠ gfp` is not even a well-formed proposition. The hypotheses fail before the conclusion
      can be stated.
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
    genus of the other three.

    **Standard name for this kind of comparison.** The sentences true throughout a class of
    structures are its theory `Th(K)`, defined for a class of L-structures - i.e. relative to ONE
    language L, which may itself be many-sorted; `M ≡ N`
    (*elementarily equivalent*) means `Th(M) = Th(N)` — Pillay, *Model Theory* lecture notes,
    Def 1.1(vi) and (viii).
    ⚠ Naming the vocabulary imports nothing: forming a common language for these carriers is a
    separate step, and nobody has taken it here. -/
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
