import Mathlib.SetTheory.Ordinal.Notation

/-!
# ZP-N: the ε₀ snap, constructively, on ordinal notations (choice-free)

## Engineer's Take

ZP-N is the choice-free constructive companion to the ZP-L/M ordinal snap. See the Engineer's Take in `ZeroParadox/Ordinal/Gentzen.lean`.

---

The ε₀ snap from below on Mathlib's ordinal notations (`ONote`), never touching `repr`/`Ordinal`:
`exp_lt_term`, `omegaPow_no_fixedpoint` and `tower_strictMono` report `[propext]` only; `tower_NF`
carries `Classical.choice` through Mathlib's `NF`. The probe, the result, its fences and the scope are
in `ZeroParadox/Ordinal/ConstructiveOrdinals.md`, beside this file.
-/

namespace ZeroParadox

open ONote

set_option maxHeartbeats 400000

/-- ω^x at the notation level: `oadd x 1 0` represents ω^(repr x). Purely syntactic, computable. -/
def omegaPow (x : ONote) : ONote := oadd x 1 0

/-- The ω-tower (ω^·)^[n] 0: `tower 0 = 0`, `tower (n+1) = ω^(tower n)`. Constructive. -/
def tower : ℕ → ONote
  | 0 => 0
  | (n + 1) => omegaPow (tower n)

/-- Each tower stage is in normal form. -/
theorem tower_NF : ∀ n, NF (tower n)
  | 0 => NF.zero
  | (n + 1) => by
      haveI := tower_NF n
      show NF (omegaPow (tower n))
      unfold omegaPow
      infer_instance

/-- An exponent is strictly below its own term: `cmp e (oadd e n a) = lt`, by structural induction on
the exponent. Pure syntax — no `repr`, no `Ordinal`, hence choice-free. -/
theorem exp_lt_term : ∀ (e : ONote) (n : ℕ+) (a : ONote),
    ONote.cmp e (oadd e n a) = Ordering.lt
  | 0, _, _ => rfl
  | (oadd e' n' a'), n, a => by
      simp only [ONote.cmp, exp_lt_term e' n' a', Ordering.then]

/-- **No ordinal notation is a fixed point of ω^·.** Every notation is strictly below ω^x in the
choice-free syntactic comparison `cmp` (holds for all notations, NF or not). This is the constructive
shadow of "ε₀ is the least fixed point of ω^·, lying beyond every notation." -/
theorem omegaPow_no_fixedpoint (x : ONote) :
    ONote.cmp x (omegaPow x) = Ordering.lt :=
  exp_lt_term x 1 0

/-- **The ω-tower is strictly increasing** (choice-free), via `cmp`. The snap stages climb without
bound below ε₀. -/
theorem tower_strictMono (n : ℕ) :
    ONote.cmp (tower n) (tower (n + 1)) = Ordering.lt := by
  show ONote.cmp (tower n) (omegaPow (tower n)) = Ordering.lt
  exact omegaPow_no_fixedpoint (tower n)

section PurityCheck
-- The payoff: these must be CHOICE-FREE (no Classical.choice) — the snap-from-below proved
-- syntactically on ONote, never touching repr/Ordinal. Contrast ZP-L's ε₀ results, all of which
-- carry Classical.choice (inherited from Mathlib's Ordinal).
#print axioms exp_lt_term
#print axioms omegaPow_no_fixedpoint
#print axioms tower_strictMono
#print axioms tower_NF
end PurityCheck

end ZeroParadox
