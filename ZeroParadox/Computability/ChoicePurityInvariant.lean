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
  claim ν *requires* choice — but be precise about what is measured (2026-08-03). `QPF.Cofix` carries
  `Classical.choice` **in the type**, so this footprint is **not removable by rewriting the proof**;
  an earlier version of this line said "constructible choice-free in principle", which was an
  unmeasured inference. What makes it an *artifact* is the pair: `PFunctor.M` is **axiom-free**, and
  `strict_cofix_nonempty` (`ZeroParadox/Computability/RootCutTrichotomy.lean`) proves the same
  ν-inhabitation over that M-type with **no axioms at all**. So the choice belongs to the QPF
  *quotient layer*, and escaping it means changing the carrier rather than cleaning the argument.
  Recorded in the PurityCheck comment, not asserted as a theorem.

  **Prior art, and READ THE SETTING — each of these three lives in a different type theory, and the
  differences are the whole point of the block.**
  * **Altenkirch, Ghani, Hancock, McBride, Morris, *Indexed Containers*** (JFP 25, 2015) — **the
    Axiom-K citation, and the closest setting to this file.** It says so in its own words: it relies
    on axiom K, and notes that K together with function extensionality *"corresponds to extensional
    Type Theory"*. That is the setting the claim here is about, since Lean is an Axiom-K / UIP theory
    (the corpus says so itself in `ZeroParadox/Category/BottomUndecidable.lean`: "In Lean 4 UIP holds
    for every type").
  * **Abbott, Altenkirch, Ghani, "Containers: constructing strictly positive types"**, TCS
    342(1):3-27, 2005 — the **precursor, in EXTENSIONAL MLTT**, not Axiom-K. Its own text: *"We use
    here the language of extensional Martin-Löf Type Theory."* Cite it as the origin of the container
    treatment; do **not** cite it for the Axiom-K setting. *(That attribution was wrong here on
    2026-08-02 and is corrected — the error the block's own "READ THE SETTING" premise exists to
    catch, made one reference below the heading.)*
  * **Ahrens, Capriotti, Spadotti, "Non-wellfounded trees in Homotopy Type Theory"** (TLCA 2015,
    LIPIcs 38:17-30, arXiv:1504.02949) constructs the final coalgebra of a polynomial functor as an
    ω-limit in intensional MLTT, and says it *generalizes* the Altenkirch et al. construction *"to the
    whole of HoTT"*. **Its univalence dependency is narrower than stated here previously**: ACS says
    *"we make minimal use of univalence itself: Lemma 5 is the only result that uses it directly"* —
    and Lemma 5 is the **uniqueness** result, not the construction, which needs only function
    extensionality. Lean has function extensionality. So ACS is **not** simply "one setting removed";
    its construction is closer to applicable here than a univalence label suggests, and only its
    uniqueness half genuinely needs the stronger axiom.
  * **Veltri, FSCD 2021** — cite for **contrast only**. His subject is the **finite powerset** functor,
    which is *not* polynomial, and his headline results run the other way — certain constructions
    there are obtained ASSUMING choice principles rather than shown to need them, and his own
    preferred coinductive construction needs neither choice nor LLPO. The one genuine necessity
    he proves is of LLPO, a logic taboo, not of choice. He is apt as background — he treats the
    polynomial case explicitly as contrast, his
    `Tree` is the final `List`-coalgebra, and he himself hands the polynomial fact to Ahrens et al.

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
M-type machinery — recorded in PurityCheck, NOT asserted as a necessity. Measured 2026-08-03:
`QPF.Cofix` carries the choice in the TYPE, so no proof of this statement is clean. `PFunctor.M`'s
FORMER and constructors are axiom-free while its DESTRUCTOR (`M.children`/`M.dest`) is NOT — that is
where the axiom originates, and `Cofix` inherits it through the congruence it quotients by. What makes
the footprint a *quotient-layer* artifact is that `strict_cofix_nonempty` witnesses the same
inhabitation with no axioms, by only BUILDING and never destructing (see the header for why Veltri is
background, not support).-/
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
--   while `strict_cofix_nonempty` proves the same inhabitation with no axioms, by only building.
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
