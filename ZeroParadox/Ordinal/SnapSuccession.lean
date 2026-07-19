import ZeroParadox.Ordinal.SnapNucleus
import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 400000

/-!
# The succession as a chain: the new bottoms are the ε-numbers, strictly climbing

`SnapNucleus.lean` builds the snap as a modality `snapNucleus : Nucleus Ordinal` sending ⊥ to ε₀. The snap
does not stop there: it returns to a NEW bottom and runs again. This file makes that succession precise.

The key fact is that a nucleus is a **closure** — idempotent — so iterating `snapNucleus` alone does
nothing (it has already run to completion). The succession comes instead from **re-seeding one step above
the current bottom**: the next new bottom is the snap applied just above the last. That operation is
exactly Mathlib's fixed-point enumerator: `ε_ = Ordinal.epsilon = deriv (α ↦ ω^α)`, whose successor step
is `ε_ (succ o) = nfp (ω^·) (succ (ε_ o))` (`epsilon_succ_eq_nfp`) — "snap from just past the current
bottom."

So the succession of new bottoms is the **ε-hierarchy** `ε₀ < ε₁ < ε₂ < …`, and:
- its rungs are exactly the **closed points** of `snapNucleus` (the fixed points of the snap-step) —
  `snapNucleus_isClosed_iff`;
- it climbs **strictly** — each new bottom is genuinely above the last (`succession_lt_succ`), never the
  same one;
- it starts at the framework's ε₀ (`succession_zero`).

This is Tim's "when one instance ends, another begins" as a strictly increasing chain of closed points.

**Scope (what is here vs deferred).** This file formalizes the succession as a strict chain of closed
points. The stronger claim that successive instances are *orthogonal* (the "orthogonal tangent" — that the
new bottom is transverse to the old, not merely above it) needs a transversality/complementation statement
in the coframe of sublocales that is not attempted here; it is the open next step
(`orthogonal_succession_conjecture_2026-07-18` note). Everything below is a strict-chain fact, cited to
Mathlib's `deriv`/`epsilon` theory (the ε-numbers are Cantor/Veblen, recognized), with the framework
contribution being the reading of the chain as the snap's succession of new bottoms.

## Engineer's Take

TODO (Tim): your take on the succession — the new bottoms as a strictly climbing chain, each one the snap
run from just past the last, and where the orthogonal-tangent idea still has to be pinned down.
-/

namespace ZeroParadox

open Order Ordinal

/-! ### § I. The rungs are the closed points of the snap-nucleus -/

/-- **The closed points of the snap-nucleus are exactly the fixed points of the snap-step** (the
    ε-numbers). A point is settled under `snapNucleus` iff `ω^x = x` — iff it is an ε-number. The generated
    system's points ARE the ε-hierarchy. -/
theorem snapNucleus_isClosed_iff (x : Ordinal) :
    snapNucleus x = x ↔ Ordinal.omega0 ^ x = x := by
  rw [snapNucleus_apply]
  constructor
  · intro h
    have hfp := Ordinal.nfp_fp (isNormal_opow one_lt_omega0) x
    rw [h] at hfp
    exact hfp
  · intro h
    exact Ordinal.nfp_eq_self h

/-! ### § II. The succession is the ε-hierarchy, strictly climbing -/

/-- The first bottom of the succession is the framework's ε₀: `ε_ 0 = ε₀`. -/
theorem succession_zero : Ordinal.epsilon 0 = epsilonZero := by
  rw [epsilon_eq_deriv, deriv_zero_right, ← Ordinal.bot_eq_zero]
  exact epsilon0_eq_nfp_bot.symm

/-- **The succession climbs strictly.** `ε_ = deriv (ω^·)` is a normal function, so the new bottoms are a
    strictly increasing chain — each ε-number is genuinely above the previous, never the same one. -/
theorem succession_strictMono : StrictMono Ordinal.epsilon := by
  rw [show Ordinal.epsilon = deriv (fun a => Ordinal.omega0 ^ a) from funext epsilon_eq_deriv]
  exact deriv_strictMono _

/-- **Each rung is a closed point of the snap-nucleus.** Every ε-number is fixed by `snapNucleus` — the
    snap has run to completion there. -/
theorem snapNucleus_fixes_epsilon (o : Ordinal) :
    snapNucleus (Ordinal.epsilon o) = Ordinal.epsilon o := by
  refine (snapNucleus_isClosed_iff _).mpr ?_
  rw [epsilon_eq_deriv]
  exact deriv_fp (isNormal_opow one_lt_omega0) o

/-- **The successor null — the next bottom is the snap from just past the current one.** `ε_ (succ o)` is
    the snap-closure seeded at `succ (ε_ o)`: when one instance ends at `ε_ o`, the next begins by snapping
    from one step above it. (Mathlib `epsilon_succ_eq_nfp`.) -/
theorem succession_succ (o : Ordinal) :
    Ordinal.epsilon (Order.succ o)
      = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) (Order.succ (Ordinal.epsilon o)) :=
  epsilon_succ_eq_nfp o

/-- **Each new bottom is genuinely new** — strictly above the last. The succession never returns to the
    same bottom. -/
theorem succession_lt_succ (o : Ordinal) :
    Ordinal.epsilon o < Ordinal.epsilon (Order.succ o) :=
  succession_strictMono (Order.lt_succ o)

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms snapNucleus_isClosed_iff
#print axioms succession_zero
#print axioms succession_strictMono
#print axioms snapNucleus_fixes_epsilon
#print axioms succession_succ
#print axioms succession_lt_succ
end PurityCheck
