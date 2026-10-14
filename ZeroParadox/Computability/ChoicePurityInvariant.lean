-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.W.Basic
import ZeroParadox.Settheory.Coalgebra

/-!
# Is choice-purity an IN-STATEMENT μ/ν separating invariant?

This module probes Axis V (choice-purity) at the root of the QPF fork. Every prior purity footnote
(`ZeroParadox/Settheory/Coalgebra.lean`) records, as a `#print axioms` **comment**, that the μ side
(`fix_isEmpty`, the initial algebra / well-founded closure) is choice-free `[propext, Quot.sound]`
while the ν side (`cofix_nonempty`, the final coalgebra / non-well-founded closure) carries
`Classical.choice`. The question here: can that split be lifted into a **theorem-level, in-statement
invariant** — a witnessed result — rather than a measured comment? Long form, beside this file:
`ZeroParadox/Computability/ChoicePurityInvariant.md`.
## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox

open QPF

set_option maxHeartbeats 400000

/-! ### μ side: a choice-free AND propext-free emptiness witness via the bare inductive eliminator -/

/-- **`idPF_Coalgebra.W` is empty, by the `WType` recursor alone.** `idPF_Coalgebra.W = WType idPF_Coalgebra.B` with
`idPF_Coalgebra.B = fun _ => PUnit`. There is no leaf node (no head whose child type is empty), so structural
recursion never bottoms out: the motive `fun _ => False` is discharged at every node by feeding
`PUnit.unit` to the (already-refuted) child function. This term uses NO axioms — not `Classical.choice`,
not `propext`, not `Quot.sound`. It is strictly more constructive than `QPF.Fix.ind`. -/
theorem w_isEmpty : IsEmpty ZeroParadox.idPF_Coalgebra.W :=
  ⟨fun w => WType.recOn w (fun _ _ ih => ih PUnit.unit)⟩

/-- **μ is empty — the choice-free, in-statement witness.** `Fix idPF_Coalgebra.Obj` is by definition
`Quotient (Wsetoid : Setoid idPF_Coalgebra.W)`. Any element has a representative (`Quot.exists_rep`), which is
impossible by `w_isEmpty`. Measured **fully axiom-free**, strictly tighter than the existing
`ZeroParadox.fix_isEmpty` (`[propext, Quot.sound]`). This is the load-bearing new content: the
μ-witness re-derived without `Liftp` / `Fix.ind`. -/
theorem fix_isEmpty_constructive : IsEmpty (Fix ZeroParadox.idPF_Coalgebra.Obj) :=
  ⟨fun x => by
    obtain ⟨w, _⟩ := Quot.exists_rep x
    exact w_isEmpty.false w⟩

/-! ### ν side: the strongest honest in-statement claim is inhabitation (choice is a comment) -/

/-- **ν is inhabited**, re-exported from `ZeroParadox.cofix_nonempty`. The witness is the concrete
corecursion term (the self-unfolding node). Its footprint carries `Classical.choice` from Mathlib's
M-type machinery — recorded in PurityCheck, NOT asserted as a necessity. Measured 2026-08-03:
`QPF.Cofix` carries the choice in the TYPE, so no proof of this statement is clean. `PFunctor.M`'s
FORMER and constructors are axiom-free while its DESTRUCTOR (`M.children`/`M.dest`) is NOT — that is
where the axiom originates, and `Cofix` inherits it through the congruence it quotients by. What makes
the footprint a *quotient-layer* artifact is that `strict_cofix_nonempty` witnesses the same
inhabitation with no axioms, by only BUILDING and never destructing (see the header for why Veltri is
background, not support). -/
theorem cofix_nonempty' : Nonempty (Cofix ZeroParadox.idPF_Coalgebra.Obj) :=
  ZeroParadox.cofix_nonempty

/-! ### The split, in one statement -/

/-- **The root purity split, as far as it can honestly be stated.** One theorem carrying both halves:
the μ side is empty via a witness derivable from the bare inductive eliminator (no quotient-collapse,
no choice — `fix_isEmpty_constructive`, ultimately resting on the axiom-free `w_isEmpty`), AND the ν
side is inhabited by a concrete corecursion term. The in-statement *constructive* content lives on the
μ side; the ν side's choice-carrying status is a measured comment (PurityCheck), not part of this type.
-/
theorem root_purity_split :
    IsEmpty (Fix ZeroParadox.idPF_Coalgebra.Obj) ∧ Nonempty (Cofix ZeroParadox.idPF_Coalgebra.Obj) :=
  ⟨fix_isEmpty_constructive, cofix_nonempty'⟩

section PurityCheck
-- Measured footprint (lake build, v4.30.0-rc2):
--   w_isEmpty                 : (no axioms)                                   — bare WType eliminator
--   fix_isEmpty_constructive  : (no axioms)                                   — FULLY AXIOM-FREE
--   cofix_nonempty'           : [propext, Classical.choice, Quot.sound]       — choice-carrying (ν)
--   root_purity_split         : [propext, Classical.choice, Quot.sound]       — inherits ν's choice
-- (Measured stronger than pre-registered: fix_isEmpty_constructive is axiom-free, strictly tighter than
--  the existing fix_isEmpty's [propext, Quot.sound] — the Quot.exists_rep path reduces without Quot.sound.)
--
-- VERDICT on Axis V as an in-statement invariant:
--   The μ side CAN be upgraded to genuine in-statement constructive content: `w_isEmpty` is axiom-free
--   (strictly tighter than the existing `fix_isEmpty`'s [propext, Quot.sound]) and witnesses Fix-emptiness
--   through the bare inductive `WType.recOn`, not through Fix.ind/Liftp/quotient machinery. That is a real
--   new term, not a re-export.
--   The ν side CANNOT be upgraded: Lean has no object-level proposition asserting "this term uses
--   Classical.choice", and the strongest honest statement (`cofix_nonempty'`) is exactly Mathlib's
--   corecursion inhabitant. That choice is a quotient-layer artifact, MEASURED: `QPF.Cofix` carries
--   it in the type (so no proof of a Cofix-mentioning statement is clean), inheriting it from
--   `PFunctor.M`'s DESTRUCTOR (`M.children`/`M.dest`) — the former and constructors are axiom-free —
--   while `strict_cofix_nonempty` proves the same inhabitation over the M-type with no axioms,
--   by only building.
--   So the SPLIT itself is not a single theorem-level invariant: half of it (μ choice-freeness) is now
--   witnessed constructively in-statement, but the other half (ν "needs" choice) remains a measured
--   #print-axioms comment. The fork's purity asymmetry is therefore HALF-WITNESSED, HALF-COMMENT —
--   the pre-registered NO-GO/DECORATIVE finding is the accurate one for "the split is ONE theorem",
--   while the pre-registered GO partially holds for the μ half alone.
#print axioms w_isEmpty
#print axioms fix_isEmpty_constructive
#print axioms cofix_nonempty'
#print axioms root_purity_split
end PurityCheck

end ZeroParadox
