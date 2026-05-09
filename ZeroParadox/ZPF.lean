import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# ZP-F: The Real Numbers as Counterexample

## Engineer's Take

Any numerical system — notably the reals or the rationals — is structurally
incapable of modeling the snap. They represent continuity to infinite regression.
While amazing tools at macro scales, they assume continuity that simply does not
exist at the scale that we are evaluating. It's almost like the break between
quantum physics and Newtonian.

---

## Formal Overview (AI-assisted)

The Binary Snap requires a metric where no halving is possible. ℝ fails that
test by construction — so does any field with a compatible linear order
([Field F] [LinearOrder F] [IsStrictOrderedRing F]). ℚ₂ passes it because
zero's valuation is +∞: the gap between zero and any nonzero element is not a
limit but a structural fact.

**General case (any [Field F] [LinearOrder F] [IsStrictOrderedRing F]):**

F-DENSITY        : ∀ ε : F, 0 < ε → 0 < ε/2 ∧ ε/2 < ε
F-NO-MIN         : F has no minimal positive element
F-SNAP-BLOCKED   : Any candidate first step from 0 in F can be halved
F-SNAP-IMPOSSIBLE: The Binary Snap cannot occur in any LinearOrderedField

**Real numbers (ℝ, the canonical instance):**

R-DENSITY, R-NO-MIN, R-SNAP-BLOCKED, R-SNAP-IMPOSSIBLE follow as corollaries
by instantiating F = ℝ.

All results follow from the LinearOrderedField axioms — no topology, no
measure theory.
-/

namespace ZeroParadox.ZPF

/-! ### General case: any LinearOrderedField -/

section General

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- F-DENSITY: For any positive element ε in a LinearOrderedField, ε/2 is also
    positive and strictly smaller. The halving argument works in any ordered field. -/
theorem f_density (ε : F) (hε : 0 < ε) : 0 < ε / 2 ∧ ε / 2 < ε :=
  ⟨half_pos hε, half_lt_self hε⟩

/-- F-NO-MIN: No LinearOrderedField has a minimal positive element.
    Any candidate minimum is undercut by its own half. -/
theorem f_no_minimal_positive : ¬∃ ε : F, 0 < ε ∧ ∀ δ : F, 0 < δ → ε ≤ δ := by
  intro ⟨ε, hpos, hmin⟩
  exact absurd (hmin (ε / 2) (half_pos hpos)) (not_le.mpr (half_lt_self hpos))

/-- F-SNAP-BLOCKED: Any candidate first step ε₀ > 0 from 0 in a LinearOrderedField
    is blocked — ε₀/2 is a smaller positive element, so ε₀ is not a first step. -/
theorem f_snap_blocked (ε₀ : F) (hε : 0 < ε₀) : ∃ δ : F, 0 < δ ∧ δ < ε₀ :=
  ⟨ε₀ / 2, half_pos hε, half_lt_self hε⟩

/-- F-SNAP-IMPOSSIBLE: The Binary Snap cannot occur in any LinearOrderedField.
    A snap requires a minimal first step with nothing below it — impossible when
    halving is always available. -/
theorem f_snap_impossible : ¬∃ ε₀ : F, 0 < ε₀ ∧ ¬∃ δ : F, 0 < δ ∧ δ < ε₀ := by
  intro ⟨ε₀, hpos, hno_smaller⟩
  exact hno_smaller (f_snap_blocked ε₀ hpos)

end General

/-! ### Real numbers: canonical instance -/

section Reals

/-- R-DENSITY: Density at zero for ℝ — the canonical LinearOrderedField instance. -/
theorem r_density (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 ∧ ε / 2 < ε :=
  f_density ε hε

/-- R-NO-MIN: ℝ has no minimal positive element. -/
theorem r_no_minimal_positive : ¬∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → ε ≤ δ :=
  f_no_minimal_positive

/-- R-SNAP-BLOCKED: Any candidate first step in ℝ can be halved. -/
theorem r_snap_blocked (ε₀ : ℝ) (hε : 0 < ε₀) : ∃ δ : ℝ, 0 < δ ∧ δ < ε₀ :=
  f_snap_blocked ε₀ hε

/-- R-SNAP-IMPOSSIBLE: The Binary Snap cannot occur in ℝ. -/
theorem r_snap_impossible : ¬∃ ε₀ : ℝ, 0 < ε₀ ∧ ¬∃ δ : ℝ, 0 < δ ∧ δ < ε₀ :=
  f_snap_impossible

end Reals

section PurityCheck
#print axioms f_density
#print axioms f_no_minimal_positive
#print axioms f_snap_blocked
#print axioms f_snap_impossible
#print axioms r_density
#print axioms r_no_minimal_positive
#print axioms r_snap_blocked
#print axioms r_snap_impossible
end PurityCheck

end ZeroParadox.ZPF
