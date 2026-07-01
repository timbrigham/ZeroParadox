import Mathlib.SetTheory.Ordinal.Notation

/-!
# ZP-N: the ε₀ snap, constructively, on ordinal notations (choice-free)

The probe (`.claude-local/notes/choice_probe_ordinal_2026-06-15.md`) showed that ZP-L's
`Classical.choice` at ε₀ is *inherited* from Mathlib's choice-saturated `Ordinal` type — but the
syntactic notation substrate (`ONote.cmp`) is choice-free (`propext`-only). ZP-N rebuilds the
snap-from-below **syntactically**, never touching `repr`/`Ordinal`, so the results are choice-free.

Key move: ω^x at the notation level is just `oadd x 1 0` (the CNF term with leading exponent x,
coefficient 1, remainder 0) — no general `opow` needed. ε₀ itself is NOT an `ONote` element (the
notations name exactly the ordinals < ε₀); ε₀ is their limit. So the snap threshold is characterised
*from below*: the ω-tower climbs without bound, and **no notation is a fixed point of ω^·** — the fixed
point (ε₀) is precisely what the notation system cannot reach.

## Result (proved, this build)
The snap-from-below is **choice-free**: `exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono` all
report `[propext]` only — no `Classical.choice` — in contrast to every ε₀ result in ZP-L (all carry
`Classical.choice`, inherited from Mathlib's `Ordinal`). So ZP-L's choice at ε₀ is **representational,
not intrinsic**: the snap's downward structure (the ω-tower climbs without bound; no notation is a fixed
point of ω^·) is genuinely constructive.

Side finding: `tower_NF` (well-formedness) *does* carry `Classical.choice` — because Mathlib's `NF`
predicate is defined through `repr` into `Ordinal`. The snap facts do not depend on `NF`, so they stay
choice-free; but even "this notation is well-formed" inherits choice in Mathlib — corroborating that
choice lives precisely at the syntax→semantics bridge.

Scope: this is the snap *from below* (ε₀ is the unreachable fixed point). The matching *minimality*
("ε₀ is the LEAST fixed point") is the natural next target and is harder — it quantifies over the limit,
which no notation names.
-/

namespace ZeroParadox.ZPN

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
-- carry Classical.choice (inherited from Mathlib's Ordinal). See
-- .claude-local/notes/choice_probe_ordinal_2026-06-15.md.
#print axioms exp_lt_term
#print axioms omegaPow_no_fixedpoint
#print axioms tower_strictMono
#print axioms tower_NF
end PurityCheck

end ZeroParadox.ZPN
