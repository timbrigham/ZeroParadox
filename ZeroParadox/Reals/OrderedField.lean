import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Cover
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

The Binary Snap requires a setting where halving does not undercut every candidate
first step. ℝ fails that test by construction — so does any field with a compatible
linear order ([Field F] [LinearOrder F] [IsStrictOrderedRing F]). In ℚ₂ the halving
argument does not apply (dividing by 2 moves AWAY from zero, lowering the valuation),
and v₂(0) = +∞ while every non-zero element has finite valuation. **That removes the
obstruction; it does not supply a first step** — the 2-adic norms still accumulate at
zero (‖2ⁿ‖₂ = 2⁻ⁿ), so zero is a limit of the non-zero elements there, not isolated
from them. The first step is AX-B1 (§ 0), a commitment.

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

namespace ZeroParadox

/-! ### General case: any LinearOrderedField -/

/-! ## § 0. AX-B1 AS AN EXPLICIT COMMITMENT

**The framework's one substantive modelling commitment is DISCRETENESS**, and until now it was in
the least visible of the three encodings (CLAUDE.md, "Commitments Go In HYPOTHESES"): baked into a
carrier. `ax_b1_distinct : nullState ≠ firstAtomicState := by decide` only checks that the two
constructors of a two-element type differ — **it does not check the choice of a discrete alphabet
over a continuum**, which is the actual commitment.

Stated as a predicate, the commitment becomes visible at every use site, and something else falls
out for free: **it is exactly what the reals lack.** `f_snap_impossible` in this same file proves
no ordered field has it. The commitment and its counterexample are now the same proposition, in
opposite directions.

The ZP-C forcing lemmas (`pmf_subsingleton_isPure`, `binaryState_exhaustive`) discharge the
"no half-state" worry — leaving ⊥ needs a second outcome — but they force only the ≥ 2 lower bound.
**The residual commitment is that the outcome space is DISCRETE, and that is `HasFirstStep`.** -/

section AxB1

/-- **AX-B1, in standard order-theoretic vocabulary: the bottom is COVERED by something.**

    Mathlib's `CovBy` (notation `a ⋖ b`) says `b` is directly above `a` with nothing strictly
    between. The framework's discreteness commitment is exactly `∃ a, bot ⋖ a`, so AX-B1 is
    kept as the name and `CovBy` supplies the content and the lemmas.

    **Honest transition note (2026-07-27).** This was first written (2026-07-26) as a bespoke
    predicate carrying a custom-registry tag that asserted Mathlib had no analog. **That was
    wrong.** `CovBy` already existed, is stated over the weaker `[LT α]` rather than
    `[Preorder α]`, and carries `CovBy.unique_right`, `not_covBy`, and the biconditional below.
    The framework had simply never identified its own one substantive modelling commitment with
    the standard notion. Recorded here rather than quietly corrected, so that the same
    unidentified-notion failure is easier to spot if it appears elsewhere. -/
def HasFirstStep {α : Type*} [LT α] (bot : α) : Prop := ∃ a, bot ⋖ a

/-- **The first step is unique.** This is Mathlib's `CovBy.unique_right`, and it is cited as
    such — proved here by hand only to keep the footprint at `[propext]`. Mathlib's version
    routes through `LinearOrder` machinery that pulls in `Classical.choice`, and the framework
    prefers the pure route where one is available. Same statement, cheaper proof. -/
theorem firstStep_unique {α : Type*} [LinearOrder α] {bot a b : α}
    (ha : bot ⋖ a) (hb : bot ⋖ b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd h (hb.2 ha.1)
  · exact h
  · exact absurd h (ha.2 hb.1)

/-- **What the commitment buys.** Assume AX-B1 and the snap's target exists and is UNIQUE, so
    the transition has a well-defined destination. The hypothesis is visible on the face of the
    statement, so no reader can mistake the conclusion for something derived without it. -/
theorem axb1_gives_unique_target {α : Type*} [LinearOrder α] (bot : α)
    (h : HasFirstStep bot) : ∃! a : α, bot ⋖ a := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, fun b hb => firstStep_unique hb ha⟩

/-- **AX-B1 fails exactly where the order is dense — a BICONDITIONAL, and it is Mathlib's.**

    `denselyOrdered_iff_forall_not_covBy`. This is stronger than the framework's own statement:
    ZP-F shows the snap fails in the reals, and this shows that failing *is* density. The two
    are the same condition, not two facts that happen to coincide. -/
theorem axb1_fails_everywhere_iff_dense {α : Type*} [Preorder α] :
    DenselyOrdered α ↔ ∀ bot : α, ¬ HasFirstStep bot := by
  rw [denselyOrdered_iff_forall_not_covBy]
  exact ⟨fun h bot ⟨a, hcov⟩ => h bot a hcov, fun h a b hcov => h a ⟨b, hcov⟩⟩

end AxB1

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

/-- **AX-B1 FAILS in every ordered field.** Ordered fields are densely ordered in Mathlib
    (`LinearOrderedSemiField.toDenselyOrdered`), and in a dense order nothing covers anything
    (`not_covBy`). So the commitment is refuted pointwise against its own counterexample: what
    the framework commits to is exactly what the reals do not have.

    Proved through Mathlib rather than through `f_snap_impossible` — the halving argument above
    is the same fact reached by hand, and is kept because it is the elementary route a reader
    can check without the order-theory library. -/
theorem axb1_fails_in_ordered_field : ¬ HasFirstStep (0 : F) := by
  rintro ⟨a, hcov⟩
  exact not_covBy hcov

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

/-! ## Classification Note: Ordered Fields and the Snap

The results above establish that the Binary Snap cannot occur in any
LinearOrderedField. **The underlying reason is DENSITY, not the Archimedean property:**
in any ordered field halving is available, so between 0 and any positive x there is
something smaller — there is no "first step" from zero. Neither theorem below has an
Archimedean hypothesis, and none is needed.

*(Corrected 2026-08-01. This section was headed "Archimedean Fields and the Snap" and said
"the underlying reason is the Archimedean property". That is false: a non-Archimedean ordered
field such as ℝ(t) is still **dense**, so the snap is blocked there too. Being Archimedean is
not what does the work; being an ordered field is. The struck claim survived here for months
after the same wording was corrected in `ZeroParadox/Valuation/Padic.lean` — an adversary gate
found it by grepping the CLAIM rather than the file.)*

**ZP-F / ZP-B classification.** *(Ostrowski's theorem classifies the absolute values on ℚ up to
equivalence, so it governs the ℝ-versus-ℚ_p split only. It does **not** classify ℝ(t), which is not a
completion of ℚ — the first bullet is therefore wider than Ostrowski and rests on
`f_snap_impossible`, not on the classification. Heading corrected 2026-08-02; it previously read
"Classification (Ostrowski's theorem)" while governing a bullet containing ℝ(t).)*

- **Ordered fields** (ℝ, ℚ, and equally the non-Archimedean ones like ℝ(t)): the snap is
  **impossible** — proved in this file by two distinct theorems, `f_snap_impossible` (by halving)
  and `axb1_fails_in_ordered_field` (via density and `CovBy`): the same fact reached two ways,
  with distinct statements. They are **not** the same declaration and no equation between them is
  asserted.
- Non-Archimedean **and not an ordered field** (ℚ₂): the snap is **not blocked**, which is a strictly
  weaker statement than being forced. *(The p-adics admit no compatible linear order — standard, by
  Artin–Schreier: an orderable field must be formally real, i.e. −1 is not a sum of squares, and in
  ℚ_p it is. Cited 2026-08-02; the claim stood uncited.)*

**ZP-B does NOT force the snap, and cannot.** What it proves is topological: the gap at 0 is
clopen (`t3_isolation`) and the return across it admits no continuous path (`c3_irreversible`,
via `t5_totallyDisconnected`). Neither yields a first step, and no metric result could: the
2-adic norm values accumulate at 0 (‖2ⁿ‖₂ = 2⁻ⁿ), so ℚ₂ has no closest non-zero element either
— ZP-B's own `eps0 k = 2 ^ k` is parameterized by a chosen maximum accessible valuation and its
definition records the value as contingent. **The first step is AX-B1**, the commitment stated
in § 0 above, not a consequence of the 2-adic structure.

So the classification is a statement about where the snap is RULED OUT. Ostrowski's theorem
(see `ZeroParadox/Valuation/Ostrowski.lean` for the framework's own statement of it) separates
the Archimedean completions of ℚ from the non-Archimedean ones; **ZP-F rules the snap out in every
ordered field** — which is what this file actually proves, and is wider than the Archimedean
completion — and ZP-B removes the topological obstruction in ℚ₂. *(Corrected 2026-08-01: this read
"ZP-F rules the snap out on the Archimedean side", which understates a theorem needing no Archimedean
hypothesis. The identical phrasing in `ZeroParadox/Valuation/Padic.lean` was struck in the same arc, **as
of `a565649`** — and only on the second attempt: the first pass corrected this file while asserting the
sibling had already been fixed, when it had not. **Do not restate another file's state as fact in a
correction note — including this one, which is why it is dated: grep the claim there instead.** An
adversary gate caught it.)* That the snap
actually occurs there is carried by AX-B1 together with the framework's commitments, never by
C3 or T5 alone.

See `ZeroParadox/Valuation/Padic.lean` (`c3_irreversible`, `t5_totallyDisconnected`,
`t3_isolation`) for the non-Archimedean side. -/

section PurityCheck
#print axioms firstStep_unique
#print axioms axb1_gives_unique_target
#print axioms axb1_fails_in_ordered_field
#print axioms axb1_fails_everywhere_iff_dense
#print axioms f_density
#print axioms f_no_minimal_positive
#print axioms f_snap_blocked
#print axioms f_snap_impossible
#print axioms r_density
#print axioms r_no_minimal_positive
#print axioms r_snap_blocked
#print axioms r_snap_impossible
end PurityCheck

end ZeroParadox
