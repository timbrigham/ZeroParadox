import ZeroParadox.Ordinal.SnapNucleus
import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 400000

/-!
# The succession as a chain: the ε-numbers are the snap's successive targets, strictly climbing

`ZeroParadox/Ordinal/SnapNucleus.lean` builds the snap as a modality `snapNucleus : Nucleus Ordinal` sending ⊥ to ε₀. The snap
does not stop there: it re-seeds above where it landed and runs again. This file makes that succession
precise.

**Read the following distinction before anything else in this file; an earlier draft of this header got
it wrong.** The ε-numbers are the ordinals the snap runs **to** — its successive closed points, the
targets. They are **not** ⊥. `ε₀ ≠ ⊥` is a bedrock invariant (`epsilon0_ne_bot`): ⊥ is the base fed in,
ε₀ the closure that comes out, and the base is never its own closure.

**The standard term for a rung is an ITERATIVE BOTTOM** (ratified 2026-07-19). Each rung serves as the
base the *next* iteration re-seeds
above — a bottom relative to its iteration, never ⊥ itself. The qualifier is load-bearing: "iterative
bottom" names the role, the bare noun would assert the identity. Do **not** call these "local bottoms" —
that phrase is already in use for the *per-domain* MC-1 family (`Category/GlobalZero.lean`), and would
collapse family-versus-succession; it also collides with the locale vocabulary this file's neighbours use.

This is the role/identity distinction, the same shape as the family-versus-instance reading: the rungs are
all *of the same kind*, and they are *provably distinct* members (`succession_lt_succ`), so no two of
them, and none of them and ⊥, may be identified.

The genuinely new bottom the snap-arc returns to is `t_iz_limit_is_new_null`'s successor null, a fact
about a `ZPSemilattice` and not about an ordinal ε-number. Do not merge the two readings.

The key fact is that a nucleus is a **closure** — idempotent — so iterating `snapNucleus` alone does
nothing (it has already run to completion). The succession comes instead from **re-seeding one step above
the current target**: the next target is the snap applied just above the last. That operation is
exactly Mathlib's fixed-point enumerator: `ε_ = Ordinal.epsilon = deriv (α ↦ ω^α)`, whose successor step
is `ε_ (succ o) = nfp (ω^·) (succ (ε_ o))` (`epsilon_succ_eq_nfp`) — "snap from just past the current
rung."

So the succession of snap targets is the **ε-hierarchy** `ε₀ < ε₁ < ε₂ < …`, and:
- its rungs are exactly the **closed points** of `snapNucleus` (the fixed points of the snap-step) —
  `snapNucleus_isClosed_iff`;
- it climbs **strictly** — each target is genuinely above the last (`succession_lt_succ`), never the
  same one;
- its first rung is ε₀ (`succession_zero`) — the target of the snap seeded at ⊥, not a bottom itself.

This is Tim's "when one instance ends, another begins" as a strictly increasing chain of closed points.

**Scope (what is here vs deferred).** This file formalizes the succession as a strict chain of closed
points. The stronger claim that successive instances are *orthogonal* (the "orthogonal tangent" — that the
next rung is transverse to the old, not merely above it) needs a transversality/complementation statement
in the coframe of sublocales that is not attempted here; it is the open next step
(`orthogonal_succession_conjecture_2026-07-18` note). Everything below is a strict-chain fact, cited to
Mathlib's `deriv`/`epsilon` theory (the ε-numbers are Cantor/Veblen, recognized), with the framework
contribution being the reading of the chain as the snap's succession of targets, each re-seeding the next.

## Engineer's Take

While it does return to bottom, it is a brand new instance of bottom at that point in time, just by virtue
of leaving and coming back.

Bottom is not ever epsilon zero. Always next to, but never the same as.
-/

namespace ZeroParadox

open Order Ordinal

/-! ### § I. The rungs are the closed points of the snap-nucleus -/

/-- **The closed points of the snap-nucleus are exactly the fixed points of the snap-step** (the
    ε-numbers). A point is settled under `snapNucleus` iff `ω^x = x`. That the enumeration `ε_` *reaches*
    every such point — range membership, not a restatement of the property — is the `example` below. -/
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

-- `Statement:` the hierarchy enumerates **exactly** the fixed points of the snap-step — sound and
-- complete, no rung missed and none spurious (Mathlib `mem_range_deriv`, a biconditional).
example (a : Ordinal) : a ∈ Set.range Ordinal.epsilon ↔ Ordinal.omega0 ^ a = a := by
  rw [show Ordinal.epsilon = deriv (fun b => Ordinal.omega0 ^ b) from funext epsilon_eq_deriv]
  exact mem_range_deriv (isNormal_opow one_lt_omega0)

/-! ### § II. The succession is the ε-hierarchy, strictly climbing -/

/-- The first rung of the succession is the framework's ε₀: `ε_ 0 = ε₀`. It is the snap's first
    **target**, seeded at ⊥ — not a bottom (`ε₀ ≠ ⊥`, `epsilon0_ne_bot`). -/
theorem succession_zero : Ordinal.epsilon 0 = epsilonZero := by
  rw [epsilon_eq_deriv, deriv_zero_right, ← Ordinal.bot_eq_zero]
  exact epsilon0_eq_nfp_bot.symm

/-- **The succession climbs strictly.** `ε_ = deriv (ω^·)` is a normal function, so the snap's targets
    are a strictly increasing chain — each ε-number is genuinely above the previous, never the same one. -/
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

/-- **Re-seeding — the next rung is the snap from just past the current one.** `ε_ (succ o)` is the
    snap-closure seeded at `succ (ε_ o)`: when one instance ends at `ε_ o`, the next begins by snapping
    from one step above it. (Mathlib `epsilon_succ_eq_nfp`.)

    NOT to be read as "the successor null": `ε_ o` *plays the bottom role* for this next step without
    *being* ⊥, and the framework's successor null (`t_iz_limit_is_new_null`) is a `ZPSemilattice` fact
    about a different object. The header's role/identity distinction applies here. -/
theorem succession_succ (o : Ordinal) :
    Ordinal.epsilon (Order.succ o)
      = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) (Order.succ (Ordinal.epsilon o)) :=
  epsilon_succ_eq_nfp o

/-- **Each rung is genuinely new** — strictly above the last. The succession never returns to a rung it
    has already occupied. -/
theorem succession_lt_succ (o : Ordinal) :
    Ordinal.epsilon o < Ordinal.epsilon (Order.succ o) :=
  succession_strictMono (Order.lt_succ o)

-- `Statement:` at a LIMIT the next rung is the supremum of every rung below it, not a function of one
-- predecessor (Mathlib `deriv_limit`). `succession_succ` covers successors only. The chain is already
-- infinite without this step (`succession_strictMono`); what it adds are the limit-indexed rungs.
example (o : Ordinal) (ho : Order.IsSuccLimit o) :
    Ordinal.epsilon o = ⨆ a : {a // a < o}, Ordinal.epsilon ↑a := by
  rw [show Ordinal.epsilon = deriv (fun b => Ordinal.omega0 ^ b) from funext epsilon_eq_deriv]
  exact deriv_limit _ ho

/-! ### § III. The levels — level 0 is the snap-step, and § II's whole chain is level 1 -/

-- `Statement:` level 0 of the Veblen hierarchy IS the snap-step, as functions.
example : Ordinal.veblen 0 = fun a => Ordinal.omega0 ^ a := veblen_zero

-- `Statement:` § II's whole chain IS level 1 — Mathlib defines `epsilon` as `veblen 1`, so this is `rfl`.
example : Ordinal.epsilon = Ordinal.veblen 1 := rfl

-- `Statement:` level `o+1` enumerates level `o`'s fixed points — the operation applied to its own output.
example (o : Ordinal) : Ordinal.veblen (o + 1) = deriv (Ordinal.veblen o) := veblen_add_one o

-- `Statement:` at a LIMIT level there is no "last one" to enumerate — level `o` collects the points
-- fixed by EVERY lower level. `o ≠ 0` is load-bearing, not decorative: at level 0 the right side is
-- vacuously true while the left is false (`2` is not a power of ω).
example (o a : Ordinal) (ho : o ≠ 0) :
    a ∈ Set.range (Ordinal.veblen o) ↔ ∀ b < o, Ordinal.veblen b a = a :=
  mem_range_veblen ho

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
