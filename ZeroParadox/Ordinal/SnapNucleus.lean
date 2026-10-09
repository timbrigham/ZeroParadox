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

The results inherit `Classical.choice` from Mathlib's `Ordinal` fixed-point theory (`nfp`, `epsilon`).
**Status: STATEMENT-CARRIED** (`ZeroParadox/Category/ChoiceCannotBe.md`): each statement below, only
assumed, already reports the choice (statement control, measured 2026-10-08), so no proof of these
statements as written can drop it. The open question is a restatement on a notation carrier whose
statements are choice-free; where the choice enters, and that question's current state, are in
`ZeroParadox/Ordinal/SnapNucleus.md` § "Axiom footprint". -/

section PurityCheck
open ZeroParadox
#print axioms snapNucleus
#print axioms snapNucleus_bot
#print axioms snapNucleus_epsilon0
#print axioms snapNucleus_bot_ne_bot
end PurityCheck
