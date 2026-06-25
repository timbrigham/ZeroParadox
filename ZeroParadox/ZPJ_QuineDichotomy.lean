import ZeroParadox.ZPP_Coalgebra
import ZeroParadox.ZPJ_SelfApp
import ZeroParadox.ZPJ_Lawvere

/-!
# ZPJ_QuineDichotomy — the Quine-atom dichotomy

## Engineer's Take

We can't directly represent the Quine atom — the underlying machine can't build a full representation of
a set that contains itself. What we can do is reuse the abstractive mock-up we built earlier: it stands in
for the components we actually need without requiring the part that can't exist. So this layer is largely an
additional cross-reference back to ZPJ — it assembles the pieces we already proved rather than building a
self-membering set the kernel won't allow.

## Overview

The set-theory FACE of the same μ/ν bottom-fork that `ZPF_SnapDichotomy` is the number-system face of.
Assembled from pieces already proved across the ZPJ family + ZP-P's coalgebra:

- **Existence fork (ν admits / μ forbids):** the self-referential object exists on the non-well-founded
  (greatest-fixed-point) side and not on the well-founded (least-fixed-point) side.
  (`ZeroParadox.ZPP.categorical_fork_strict`: `Fix idPF.Obj` empty, `Cofix idPF.Obj` inhabited.)
- **Uniqueness + identity:** wherever the self-referential fixed point lives, it is unique and IS the
  bottom. (`ZeroParadox.ZPJ_SelfApp.selfMem_eq_singleton_bot`: the self-members are exactly `{⊥}`.)
- **Cantor obstruction (no literal):** a nontrivial lattice face admits no Lawvere witness, so the literal
  self-singleton (which would need `T ≃ Set T`) cannot be built. (`ZPJ_Lawvere.nontrivial_lattice_no_witness`.)

## FENCE (crucial — unlike the snap dichotomy)
The snap's classifier (Ostrowski) is a theorem INSIDE one foundation, so "snap ⟺ non-Archimedean" is fully
machine-checkable. The Quine atom's classifier (Foundation vs AFA) is a choice of METATHEORY, which Lean's
well-founded kernel cannot adjudicate from inside (it cannot host `x = {x}`; that is the Cantor wall above).
So what is PROVED here is the STRUCTURAL dichotomy (the self-referential fixed point exists on the ν side,
not the μ side, and where it exists it is the unique bottom). The SET-THEORETIC reading — "the Quine atom
exists ⟺ AFA" — stays a metatheoretic commitment (the FMC / CC-2, fenced in ZP-E R-AFA). This file makes NO
claim that AFA is machine-checked.

## Symbol map (component → existing lemma)
- existence fork        → `ZeroParadox.ZPP.categorical_fork_strict`  (`idPF`, `Fix`, `Cofix` from ZP-P)
- self-members = {⊥}    → `ZeroParadox.ZPJ_SelfApp.selfMem_eq_singleton_bot`  (`selfMemDerived`, `bot`)
- no literal (Cantor)   → `ZeroParadox.ZPJ_Lawvere.nontrivial_lattice_no_witness`  (`HasLawvereWitness`)

STATUS: PROVED, sorry-free. Pure assembly of ZP-P coalgebra (`categorical_fork_strict`) +
ZPJ_SelfApp (`selfMem_eq_singleton_bot`) + ZPJ_Lawvere (`nontrivial_lattice_no_witness`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox.ZPJ_QuineDichotomy

open ZeroParadox.ZPP ZeroParadox.ZPJ_SelfApp ZeroParadox.ZPJ_Lawvere ZeroParadox.ZPA ZPSemilattice QPF

/-- **The Quine-atom dichotomy (existence fork).** The self-referential object exists on the
    non-well-founded (final-coalgebra) side and not on the well-founded (initial-algebra) side:
    `Fix idPF.Obj` is empty, `Cofix idPF.Obj` is inhabited. (= `ZeroParadox.ZPP.categorical_fork_strict`.)
    The set-theoretic reading "Quine atom ⟺ AFA" is the metatheoretic commitment (see FENCE), NOT part of
    this theorem. -/
theorem quine_dichotomy :
    IsEmpty (Fix idPF.Obj) ∧ Nonempty (Cofix idPF.Obj) := categorical_fork_strict

/-- **Uniqueness + identity.** In any `AbstractSelfApp` carrier the self-referential fixed points are
    exactly `{⊥}` — unique, and equal to the bottom. (= `ZeroParadox.ZPJ_SelfApp.selfMem_eq_singleton_bot`.) -/
theorem quine_self_members_eq_bot {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] :
    {x : L | selfMemDerived x} = ({bot} : Set L) := selfMem_eq_singleton_bot

/-- **Cantor obstruction (no literal Quine atom).** A nontrivial lattice face admits no Lawvere witness:
    the literal self-singleton, which would require `T ≃ Set T`, cannot be built (Cantor). -/
theorem quine_no_literal {L : Type*} [ZPSemilattice L] (a : L) (ha : a ≠ bot) :
    ¬ HasLawvereWitness L := nontrivial_lattice_no_witness a ha

end ZeroParadox.ZPJ_QuineDichotomy

section PurityCheck
open ZeroParadox.ZPJ_QuineDichotomy
#print axioms quine_dichotomy
#print axioms quine_self_members_eq_bot
#print axioms quine_no_literal
end PurityCheck
