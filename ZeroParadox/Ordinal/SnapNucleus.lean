import ZeroParadox.Ordinal.Epsilon0MinMax
import Mathlib.Order.Nucleus

set_option maxHeartbeats 400000

/-!
# The snap is a nucleus: ε₀ is the modality generated from the bottom ⊥

## Engineer's Take

Is there always a system created out of the predicated object's difference itself? That was where this
started, and the next question was what of it we actually needed to realize in Lean.

From there it ran through the succession. When one instance ends, another has to begin, by definition, on
an orthogonal tangent, and the move away from zero is just one representation of that.

The object itself came from the last question. That unbounded upward system that marches toward infinity,
that very unboundedness is what creates the new instance of a new system. Is that not its own type of
boundary? It is, and that is the point where bottom stops being the floor, a thing, a noun, and becomes a
verb, an action.

---

## Formal Overview
`snapNucleus : Nucleus Ordinal` is a genuine **nucleus** — the point-free form of a Lawvere–Tierney
modality — and it sends ⊥ to ε₀. ⚠ ⊥ is the *least* seed, not a distinguished one; the modality carries
the content. Recognized structure, the frame-vs-semilattice scope, and credit outward: `ZeroParadox/Ordinal/SnapNucleus.md`.
-/

namespace ZeroParadox

open Order Ordinal

/-- **The snap as a nucleus.** The next-fixed-point of the snap-step `α ↦ ω^α` is an inflationary,
    idempotent, meet-preserving endomap of the ordinals — a genuine `Nucleus` (a point-free
    Lawvere–Tierney modality). The snap-step is normal (`isNormal_opow` at `1 < ω`); meet-preservation is
    free on a chain (a monotone map sends `min` to `min`); inflationary is `Ordinal.le_nfp`; idempotent is
    `Ordinal.nfp_fp` at the normal snap-step. -/
noncomputable def snapNucleus : Nucleus Ordinal where
  toFun := Ordinal.nfp (fun α => Ordinal.omega0 ^ α)
  map_inf' a b := by
    have hmono : Monotone (Ordinal.nfp (fun α => Ordinal.omega0 ^ α)) :=
      Ordinal.nfp_monotone (isNormal_opow one_lt_omega0).strictMono.monotone
    rcases le_total a b with h | h
    · rw [inf_eq_left.mpr h, inf_eq_left.mpr (hmono h)]
    · rw [inf_eq_right.mpr h, inf_eq_right.mpr (hmono h)]
  idempotent' x := (Ordinal.nfp_eq_self (Ordinal.nfp_fp (isNormal_opow one_lt_omega0) x)).le
  le_apply' x := Ordinal.le_nfp _ x

/-- Unfolding lemma: the nucleus acts as the next-fixed-point of the snap-step. -/
@[simp] theorem snapNucleus_apply (a : Ordinal) :
    snapNucleus a = Ordinal.nfp (fun α => Ordinal.omega0 ^ α) a := rfl

/-- **The difference generates ε₀ from the bottom.** The snap-nucleus sends the ordinal bottom ⊥ to ε₀
    (`epsilon0_eq_nfp_bot`): ⊥ the seed, ε₀ the fixed point the modality generates. ⊥ is the least
    seed rather than a distinguished one (`isLeastFixedPointFrom_nfp`). -/
theorem snapNucleus_bot : snapNucleus (⊥ : Ordinal) = epsilonZero :=
  epsilon0_eq_nfp_bot.symm

/-- **ε₀ is the generated system's closed point.** ε₀ is fixed by the snap-nucleus (a closed point /
    sublocale point): the modality has already run to completion there. -/
theorem snapNucleus_epsilon0 : snapNucleus epsilonZero = epsilonZero :=
  Ordinal.nfp_eq_self epsilonZero_fixedPoint

/-- **The difference is nontrivial at the bottom.** The snap-nucleus moves ⊥ strictly — it does not fix
    the floor, it generates ε₀ from it (`epsilon0_ne_bot`). The modality genuinely acts. -/
theorem snapNucleus_bot_ne_bot : snapNucleus (⊥ : Ordinal) ≠ (⊥ : Ordinal) := by
  rw [snapNucleus_bot]; exact epsilon0_ne_bot

end ZeroParadox

/-! ## Axiom Purity Check

The results inherit `Classical.choice` from Mathlib's `Ordinal` fixed-point theory (`nfp`, `epsilon`),
which is classically built.

**Status of that footprint: UNCLASSIFIED.** An earlier version of this note called it "representational,
not intrinsic to the snap." That is retracted — it is an eliminability claim with no re-proof behind it.
What ZP-N actually re-proved choice-free is the ordinal *ascent* on `ONote` (`exp_lt_term`,
`omegaPow_no_fixedpoint`, `tower_strictMono`), which is suggestive for the nucleus and is not the nucleus.
`snapNucleus` itself has not been re-proved choice-free as of 2026-08-02.

**Where the choice actually is (measured 2026-07-19; an earlier version of this note asserted the wrong
mechanism).** It is **NOT** in the `Ordinal` type — `#print axioms Ordinal` reports `[propext,
Quot.sound]`, no choice. It enters through the *order instance and the operations*: `Ordinal.instLinearOrder`,
`Ordinal.nfp`, `Ordinal.omega0` and `Ordinal.epsilon` each measure `[propext, Classical.choice,
Quot.sound]`, and `snapNucleus` is built from `nfp` over `omega0 ^ ·` on that order. The earlier claim
that "choice is in the type, so no rewrite can remove it" was reasoning from a quotient construction
rather than measuring, and it was false — so the "irremovable" conclusion drawn from it does not stand
either.
`ZeroParadox/Ordinal/SnapNucleusConstructive.lean` shows the natural counterpart route is **blocked** —
no idempotent endomap of the notation carrier can have the ε-numbers as closed points — but note that
obstruction is about **expressive reach, not choice** (its own proofs are `[propext]`), so it does not
settle whether this footprint is eliminable by some other route. Recorded honestly, at the honest tier. -/

section PurityCheck
open ZeroParadox
#print axioms snapNucleus
#print axioms snapNucleus_bot
#print axioms snapNucleus_epsilon0
#print axioms snapNucleus_bot_ne_bot
end PurityCheck
