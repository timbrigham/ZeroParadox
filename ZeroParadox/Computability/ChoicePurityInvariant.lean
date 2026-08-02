-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import Mathlib.Data.QPF.Univariate.Basic
import Mathlib.Data.W.Basic
import ZeroParadox.Settheory.Coalgebra

/-!
# ZP-H MC-1 tree test TC48: is choice-purity an IN-STATEMENT μ/ν separating invariant?

This module probes Axis V (choice-purity) at the root of the QPF fork. Every prior purity footnote
(`ZPP_Coalgebra`, TC26) records, as a `#print axioms` **comment**, that the μ side
(`fix_isEmpty`, the initial algebra / well-founded closure) is choice-free `[propext, Quot.sound]`
while the ν side (`cofix_nonempty`, the final coalgebra / non-well-founded closure) carries
`Classical.choice`. The question here: can that split be lifted into a **theorem-level, in-statement
invariant** — a witnessed result — rather than a measured comment?

## The honest answer, and what the Lean witnesses

Lean cannot quantify over its own axiom footprint inside a `Prop`: no object-level proposition can say
"this proof term omits `Classical.choice`." So "μ is choice-free" cannot be made *directly* load-bearing
in a statement. The only way to put constructive content IN the statement is to exhibit the μ-witness
through a genuinely constructive proxy. That is what this file does, and it is the load-bearing new
content over `fix_isEmpty`:

* **μ side — a strictly more constructive witness than the existing one.** `QPF.Fix idPF_Coalgebra.Obj` is by
  definition `Quotient (Wsetoid : Setoid idPF_Coalgebra.W)` with `idPF_Coalgebra.W = WType idPF_Coalgebra.B`. We prove
  `IsEmpty idPF_Coalgebra.W` **by the bare inductive `WType` eliminator** (`w_isEmpty`) — no `QPF.Fix.ind`, no
  `Liftp`, no quotient machinery. That term has footprint `[]` (NO axioms — not even `Quot.sound`),
  strictly tighter than `fix_isEmpty`'s `[propext, Quot.sound]`. `IsEmpty (Fix idPF_Coalgebra.Obj)`
  (`fix_isEmpty_constructive`) then follows using `Quot.exists_rep`, and is measured **fully
  axiom-free** — strictly tighter than the existing `fix_isEmpty`. The μ-emptiness of the root is thus
  witnessed by structural recursion on a plain inductive type, with no kernel axioms at all.

* **ν side — choice cannot be made load-bearing.** The strongest honest in-statement claim is
  `Nonempty (Cofix idPF_Coalgebra.Obj)` with the corecursion term as witness (re-exported as `cofix_nonempty'`),
  whose footprint carries `Classical.choice` from Mathlib's M-type / `Cofix.corec`. We do **not**
  claim ν *requires* choice: for a polynomial functor the final coalgebra is constructible choice-free
  in principle — **Ahrens–Capriotti–Spadotti** is the load-bearing citation here. The `Classical.choice`
  is a Mathlib artifact, recorded in the PurityCheck comment, not asserted as a theorem.

  *(Citation scoped 2026-08-02. Veltri, FSCD 2021 was cited alongside ACS for this claim; that
  overstates what he shows. His subject is the **finite powerset** functor — which is **not**
  polynomial — and his headline results run the other way, that certain constructions *require* choice.
  He is still apt as background: he treats the polynomial case explicitly as contrast, and his `Tree`
  is the final `List`-coalgebra. Cite him for the contrast, not for the principle.)*

The bundle `root_purity_split` packages both honest halves: the μ-witness is propositionally derivable
from a purely structural eliminator AND the ν-inhabitant is a concrete corecursion term, in one
statement. The *content* that is genuinely new is `w_isEmpty` / `fix_isEmpty_constructive`: a μ-witness
inhabiting the constructive (choice-and-propext-free, then choice-free) namespace, derived without any
choice-dependent or quotient-quotient-collapse lemma.

## Formal Overview

`PFunctor.W P = WType P.B`, an ordinary inductive type. For `idPF_Coalgebra` (`A = PUnit`, `B = fun _ => PUnit`)
there is no leaf (no head `a` with `B a` empty), so `WType.recOn` with motive `fun _ => False`
discharges emptiness: each node needs its `PUnit`-indexed child already refuted, and `PUnit.unit`
supplies that contradiction. `QPF.Fix idPF_Coalgebra.Obj = Quotient (Wsetoid)` is then empty because every class
has a representative (`Quot.exists_rep`) and the representative is impossible. The ν inhabitant is the
self-unfolding corecursion node (`ZeroParadox.cofix_nonempty`).

What is PROVED is exactly: `IsEmpty idPF_Coalgebra.W` by the inductive eliminator (no axioms), `IsEmpty (Fix
idPF_Coalgebra.Obj)` from it (`[Quot.sound]`), and `Nonempty (Cofix idPF_Coalgebra.Obj)`. The VERDICT on the pre-registered
fork — whether this constitutes a *new theorem-level invariant* or only a *measured comment* — is the
finding, recorded in the Engineer's Take placeholder and the report. The in-statement constructive
upgrade on the μ side is real; the "ν needs choice" half remains a fenced comment, not a theorem.

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
M-type machinery — recorded in PurityCheck, NOT asserted as a necessity (polynomial final coalgebras
are choice-free in principle: Ahrens–Capriotti–Spadotti; see the header for why Veltri is background, not support). -/
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
--   corecursion inhabitant, whose choice is a library artifact, not a necessity (Ahrens-Capriotti-Spadotti).
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
