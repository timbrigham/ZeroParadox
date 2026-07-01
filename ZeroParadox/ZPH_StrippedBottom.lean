-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_PlaceAllPrimes
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ⊥ by inversion of attribute-classes — the "typecast" stand-in (Tim, 2026-06-30)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

You cannot write a Lean term that *is* ⊥ — any term has a type (structure) and is a finite description,
which ⊥ lacks (`reaching_bottom_vs_interpreting_it_2026-06-30.md`: ⊥ is timeless / spaceless /
descriptionless / measurementless / structureless / infinite). **But you can represent ⊥ by INVERTING
the attribute-classes** — naming the Lean classes that carry each attribute and asserting the point is
the degenerate/inverted value of each. Tim's "typecast by what it is NOT." This file builds that.

**HONEST STATUS (cold audit 2026-06-30: this was first OVERCLAIMED — corrected here).** Built eagerly,
then deflated. What the Lean actually contains is *thin*, and the distinctive idea is *conceptual*, not
formal. Stated plainly:

- **`StrippedBottom` is `ZPJ_SelfApp.AbstractSelfApp` re-skinned + one field.** Its `selfMap` /
  `unique_fixed` / `selfMap_fixes` ARE that class's `selfApp` / `unique_fp` / `fixed_bot` triple (the
  diagonal-fixed-point class), with `[Mul X]` in place of `[ZPSemilattice L]`; the only genuinely new
  field is `absorbing`. It is a vocabulary re-framing of an existing class, not a new structure.
- **Three of the four "attribute-inversions" are universal or borrowed, not content about ⊥:**
  `measure_degenerate := norm_zero` (holds of `0` in ANY normed group — decorative), `structure_absorbing
  := zero_mul` (ANY `MulZeroClass` — decorative), `extent_single_point` (genuine ℚ_[2] topology, but an
  unmodified re-export of `qp_floor_is_limit`, proved elsewhere). Only `dynamics_inverted` (`2x=x↔x=0`)
  has local content, and it is a two-line triviality.
- **The descriptionlessness "residue" is a PHILOSOPHICAL observation with ZERO formal content.** The
  claim "it can't be a field because stating the structure is a description" is true as a meta-remark,
  but the Lean establishes nothing about it. It is not a theorem; do not read it as one.

**So what this file actually is:** a conceptual *lens* — "represent ⊥ by inverting the attribute-classes
it lacks (`typecast by what it is NOT`)" — with the formal content amounting to (the existing fixed-point
class) + (one trivial local lemma) + (one borrowed topology theorem) + (two universal ring facts). The
*idea* is sound and is the value here; the *formalization* adds little beyond `AbstractSelfApp` and the
already-built limit theorems. Honest scope: still an **interpretation** (`0 ∈ ℚ_[2]`, a structured
term), one domain, an open list, and NOT ⊥. The genuine formal content that supports the inversion lens
lives elsewhere (the per-domain limit/uniqueness theorems); this file is the framing, honestly thin.
-/

namespace ZeroParadox.ZPH_StrippedBottom

open ZeroParadox.ZPH_PlaceAllPrimes

/-- **⊥ by inversion ("typecast by what it is NOT").** A point `b : X` that is the degenerate/inverted
    value of each listed attribute-class: STRUCTURE inverted (`absorbing`) and DYNAMICS inverted (the
    unique fixed point of an iteration self-map).
    **NOTE (honest): the dynamics fields (`selfMap`/`unique_fixed`/`selfMap_fixes`) ARE
    `ZPJ_SelfApp.AbstractSelfApp`'s triple re-skinned; the only new field is `absorbing`. This is a
    vocabulary re-framing of the existing diagonal-fixed-point class, not a new structure.** The list is
    OPEN. Descriptionlessness is deliberately NOT a field — but that is a philosophical remark (stating
    this structure is itself a description of `b`), with no formal content. -/
class StrippedBottom (X : Type*) [Mul X] where
  /-- the bottom point. -/
  b : X
  /-- STRUCTURE inverted: `b` absorbs under the operation — nothing escapes it. -/
  absorbing : ∀ x : X, b * x = b
  /-- the iteration self-map (the domain's "progression"). -/
  selfMap : X → X
  /-- DYNAMICS inverted: `b` is the unique fixed point of the self-map (no nontrivial progression). -/
  unique_fixed : ∀ x : X, selfMap x = x → x = b
  /-- `b` is a fixed point of the self-map. -/
  selfMap_fixes : selfMap b = b

/-! ## Concrete attribute-inversions at `0 ∈ ℚ_[2]` (the 2-adic interpretation) -/

/-- MEASUREMENT inverted: the norm degenerates at the bottom. (UNIVERSAL/decorative — `‖0‖ = 0` holds of
    `0` in any normed group; carries no ℚ_[2]-specific content. The contentful "infinite measure" version
    is `v₂(0) = +∞`, the ZP-B valuation framing, not this.) -/
theorem measure_degenerate : ‖(0 : ℚ_[2])‖ = 0 := norm_zero

/-- DYNAMICS inverted: `0` is the unique fixed point of doubling (`2x = x ↔ x = 0`). -/
theorem dynamics_inverted (x : ℚ_[2]) : 2 * x = x ↔ x = 0 := by
  constructor
  · intro h; linear_combination h
  · rintro rfl; ring

/-- STRUCTURE inverted: `0` absorbs under multiplication. (UNIVERSAL/decorative — `0 * x = 0` holds in any
    `MulZeroClass`; carries no ℚ_[2]-specific content.) -/
theorem structure_absorbing (x : ℚ_[2]) : 0 * x = 0 := zero_mul x

/-- SPACE / extent inverted: the intersection of the shrinking 2-adic balls is the single point `{0}`
    (reuses `qp_floor_is_limit`). -/
theorem extent_single_point : (⋂ n, qpBall 2 n) = {(0 : ℚ_[2])} := qp_floor_is_limit 2

/-- The inversion PINS the bottom: the only doubling-fixed-point is `0`. -/
theorem stripped_bottom_unique (x : ℚ_[2]) (h : 2 * x = x) : x = 0 := (dynamics_inverted x).mp h

/-- `ℚ_[2]` is a `StrippedBottom` with bottom `0`: structure-inverted (absorbing) and dynamics-inverted
    (doubling's unique fixed point). The typeclass instance — the inversion realized. -/
noncomputable instance : StrippedBottom ℚ_[2] where
  b := 0
  absorbing := structure_absorbing
  selfMap := fun x => 2 * x
  unique_fixed := stripped_bottom_unique
  selfMap_fixes := by ring

/-- `0 ∈ ℚ_[2]` satisfies the four listed attribute-inversions at once. (Honest: this is a
    *conjunction-bundle* of four already-proved facts — two universal, one borrowed, one trivial-local —
    not a new theorem. It records the simultaneity, nothing more.) -/
theorem stripped_bottom_padic :
    ‖(0 : ℚ_[2])‖ = 0 ∧
    (∀ x : ℚ_[2], 2 * x = x ↔ x = 0) ∧
    (∀ x : ℚ_[2], 0 * x = 0) ∧
    (⋂ n, qpBall 2 n) = {(0 : ℚ_[2])} :=
  ⟨measure_degenerate, dynamics_inverted, structure_absorbing, extent_single_point⟩

end ZeroParadox.ZPH_StrippedBottom

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_StrippedBottom

#print axioms measure_degenerate
#print axioms dynamics_inverted
#print axioms structure_absorbing
#print axioms extent_single_point
#print axioms stripped_bottom_unique
#print axioms stripped_bottom_padic

end PurityCheck
