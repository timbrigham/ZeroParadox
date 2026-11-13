import ZeroParadox.Settheory.Coalgebra
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Category.Lawvere
import ZeroParadox.Settheory.QuineHost

/-!
# ZPJ — the Quine-atom dichotomy

## Engineer's Take

We can't directly represent the Quine atom — the underlying machine can't build a full representation of
a set that contains itself. What we can do is reuse the abstractive mock-up we built earlier: it stands in
for the components we actually need without requiring the part that can't exist. So this layer is largely an
additional cross-reference back to ZPJ — it assembles the pieces we already proved rather than building a
self-membering set the kernel won't allow.

## Overview

The set-theory FACE of the same μ/ν bottom-fork that `ZeroParadox/Valuation/SnapDichotomy.lean` is the number-system face of.
Assembled from pieces already proved across the ZPJ family + ZP-P's coalgebra:

- **Existence fork (ν admits / μ forbids):** the self-referential object exists on the non-well-founded
  (greatest-fixed-point) side and not on the well-founded (least-fixed-point) side.
  (`ZeroParadox.categorical_fork_strict`: `Fix idPF_Coalgebra.Obj` empty, `Cofix idPF_Coalgebra.Obj` inhabited.)
- **Uniqueness + identity:** wherever the self-referential fixed point lives, it is unique and IS the
  bottom. (`ZeroParadox.selfMem_eq_singleton_bot`: the self-members are exactly `{⊥}`.)
- **Cantor obstruction (no literal):** a nontrivial lattice face admits no Lawvere witness
  (`nontrivial_lattice_no_witness`); a literal self-singleton needs `T ≃ Set T`, and no `T → Set T` is surjective (`cantor_via_engine`, `ZeroParadox/Settheory/Wall.lean`), so no such `≃` exists.

## FENCE (crucial — unlike the snap dichotomy)
The snap's classifier (Ostrowski) is a theorem INSIDE one foundation, so "snap ⟺ non-Archimedean" is fully
machine-checkable. The Quine atom's classifier (Foundation vs AFA) is a choice of METATHEORY, which Lean cannot
adjudicate from inside. `Statement:` **CARRIER** — no `ZFSet` is its own member (`no_quine_atom`) and no `T ≃ Set T` exists (Cantor, above), while the coalgebra chart hosts a self-unfolding element (`Cofix`, the existence fork above).
So what is PROVED here is the STRUCTURAL dichotomy (the self-referential fixed point exists on the ν side,
not the μ side, and where it exists it is the unique bottom). The Quine atom (CC-2) is the die role `Motion.SelfOnlyAt`, whose occupancy
is settled chart by chart (`selfApp_quine_role_iff`, `quineAtomHost_quine_role_iff`, `zfset_quine_role_unoccupied`), no cross-chart equation.
"Quine atom ⟺ AFA" concerns the set chart's host: Foundation-freeness is forced (`quineAtomHost_not_wellFounded`), adopting AFA stays the FMC / CC-2 (ZP-E R-AFA); AFA is not machine-checked here.

## Symbol map (component → existing lemma)
- existence fork        → `ZeroParadox.categorical_fork_strict`  (`idPF_Coalgebra`, `Fix`, `Cofix` from ZP-P)
- self-members = {⊥}    → `ZeroParadox.selfMem_eq_singleton_bot`  (`selfMemDerived`, `bot`)
- no literal (Cantor)   → `ZeroParadox.nontrivial_lattice_no_witness` (lattice face, `HasLawvereWitness`); `ZeroParadox.cantor_via_engine` (no surjection `A → (A → Prop)`, which excludes `T ≃ Set T`; `ZeroParadox/Settheory/Wall.lean`, not imported)

STATUS: PROVED, sorry-free. Pure assembly of ZP-P coalgebra (`categorical_fork_strict`) +
ZeroParadox/Computability/SelfApp.lean (`selfMem_eq_singleton_bot`) + ZeroParadox/Category/Lawvere.lean (`nontrivial_lattice_no_witness`); Cantor is cited from ZeroParadox/Settheory/Wall.lean (`cantor_via_engine`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open ZeroParadox ZeroParadox ZeroParadox ZeroParadox ZPSemilattice QPF

/-- **The Quine-atom dichotomy (existence fork).** The self-referential object exists on the
    non-well-founded (final-coalgebra) side and not on the well-founded (initial-algebra) side:
    `Fix idPF_Coalgebra.Obj` is empty, `Cofix idPF_Coalgebra.Obj` is inhabited. (= `ZeroParadox.categorical_fork_strict`.)
    The set-theoretic reading "Quine atom ⟺ AFA" is the metatheoretic commitment (see FENCE), NOT part of
    this theorem. -/
theorem quine_dichotomy :
    IsEmpty (Fix idPF_Coalgebra.Obj) ∧ Nonempty (Cofix idPF_Coalgebra.Obj) := categorical_fork_strict

/-- **Uniqueness + identity.** In any `AbstractSelfApp` carrier the self-referential fixed points are
    exactly `{⊥}` — unique, and equal to the bottom. (= `ZeroParadox.selfMem_eq_singleton_bot`.) -/
theorem quine_self_members_eq_bot {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] :
    {x : L | selfMemDerived x} = ({bot} : Set L) := selfMem_eq_singleton_bot

/-- **Cantor obstruction (no literal Quine atom).** A nontrivial lattice face has no Lawvere witness; a literal
    self-singleton needs `T ≃ Set T`, excluded by Cantor (`cantor_via_engine`: no `T → Set T` is surjective). -/
theorem quine_no_literal {L : Type*} [ZPSemilattice L] (a : L) (ha : a ≠ bot) :
    ¬ HasLawvereWitness L := nontrivial_lattice_no_witness a ha

/-- `Statement:` in a `ZPSemilattice` with `AbstractSelfApp`, with OVER the self-application map
    (`Motion.ofFun selfApp`), `y` steps to itself and to nothing else iff `y` is ⊥ of `L`; both
    directions, from the class fields `fixed_bot` and `unique_fp`. -/
theorem selfApp_quine_role_iff {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] (y : L) :
    (Motion.ofFun (AbstractSelfApp.selfApp (L := L))).SelfOnlyAt y ↔ y = bot :=
  (Motion.selfOnlyAt_ofFun_iff _ y).trans
    ⟨AbstractSelfApp.unique_fp y, fun h => h ▸ AbstractSelfApp.fixed_bot⟩

/-- `Statement:` in a `QuineAtomHost`, with OVER `a ⟶ b` when `b` is a member of `a`, `y` steps to
    itself and to nothing else iff `y` is the host's `bot`; both directions, from (Y') `bot_mem_iff`
    and (Z') `reflexive_unique`. -/
theorem quineAtomHost_quine_role_iff {L : Type*} [QuineAtomHost L] (y : L) :
    (Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => QuineAtomHost.mem b a)).SelfOnlyAt y ↔ y = QuineAtomHost.bot := by
  constructor
  · rintro ⟨hy, hu⟩
    exact QuineAtomHost.reflexive_unique y fun z => ⟨hu z, fun h => h ▸ hy⟩
  · rintro rfl
    exact ⟨(QuineAtomHost.bot_mem_iff _).2 rfl, fun b hb => (QuineAtomHost.bot_mem_iff b).1 hb⟩

-- Statement: the converse: for any `mem` and `bot`, (Y') and (Z') together hold iff, with OVER
-- `a ⟶ b` when `mem b a`, every `y` occupies the role iff `y = bot`; both directions.
example {L : Type} (mem : L → L → Prop) (bot : L) :
    ((∀ y, mem y bot ↔ y = bot) ∧ (∀ x, (∀ y, mem y x ↔ y = x) → x = bot)) ↔
    (∀ y, (Motion.ofTotal (id : L → L) (fun _ => rfl) (fun a b => mem b a)).SelfOnlyAt y ↔
      y = bot) := by
  constructor
  · rintro ⟨hY, hZ⟩ y
    let _ : QuineAtomHost L := ⟨mem, bot, hY, hZ⟩
    exact quineAtomHost_quine_role_iff y
  · intro h
    have hb := (h bot).2 rfl
    refine ⟨fun y => ⟨fun hy => hb.2 y hy, fun hy => hy ▸ hb.1⟩, fun x hx => ?_⟩
    exact (h x).1 ⟨(hx x).2 rfl, fun b hb => (hx b).1 hb⟩

-- Statement: CONTROL: on `Bool` with membership `=`, both points occupy the role, so (Y') at a point
-- does not make it the only occupant; no `QuineAtomHost` has this membership (`boffa_fails_reflexive_unique`).
example : (Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a b => b = a)).SelfOnlyAt true ∧
    (Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a b => b = a)).SelfOnlyAt false :=
  ⟨⟨rfl, fun _ h => h⟩, ⟨rfl, fun _ h => h⟩⟩

-- Statement: for any `QuineAtomHost` on a `ZPSemilattice` `L`, ⊥ of `L` occupies the membership
-- chart iff the host's `bot` is ⊥ of `L`; both directions, from `quineAtomHost_quine_role_iff`.
example (L : Type) [ZPSemilattice L] (S : QuineAtomHost L) :
    (Motion.ofTotal (id : L → L) (fun _ => rfl) (fun a b => S.mem b a)).SelfOnlyAt bot ↔
      S.bot = bot :=
  (@quineAtomHost_quine_role_iff L S bot).trans eq_comm

-- Statement: the host built from an `AFAStructure` on `L` has ⊥ of `L` as its `bot`, and for a point
-- `a ≠ ⊥` of `L` the host `trivialQuineAtomHost a` does not.
example (L : Type) [ZPSemilattice L] [AFAStructure L] :
    (afaStructure_isQuineAtomHost L).bot = bot := rfl
example (L : Type) [ZPSemilattice L] (a : L) (ha : a ≠ bot) :
    (trivialQuineAtomHost a).bot ≠ bot := ha

-- Statement: with the AFA-built host's membership as the step, occupying the role is being a Quine atom
-- in the `IsQuineAtom` sense, so by `t_exec_iff` its only occupant is ⊥ of `L`; both directions.
-- Reading: that host's membership relates no element to any other (the example after
-- `afaStructure_isQuineAtomHost` in `ZeroParadox/Settheory/QuineHost.lean`), so "and to nothing else"
-- is automatic here; uniqueness comes from `quine_unique`.
example (L : Type) [ZPSemilattice L] [AFAStructure L] (y : L) :
    (Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => (afaStructure_isQuineAtomHost L).mem b a)).SelfOnlyAt y ↔ IsQuineAtom y :=
  (@quineAtomHost_quine_role_iff L (afaStructure_isQuineAtomHost L) y).trans (t_exec_iff y).symm

-- Statement: under any well-founded membership relation no point occupies the membership chart, since
-- an occupant steps to itself (`wf_no_selfloop`); `zfset_quine_role_unoccupied` is the `ZFSet` case. The
-- example after `Antitone (fun q : Prop => q → P)` in `ZeroParadox/DieCannotBe.lean` assumes the STEP
-- relation well-founded instead; here it is membership, the step's converse, and neither implies the other.
example {C : Type*} (mem : C → C → Prop) (h : WellFounded mem) (y : C) :
    ¬ (Motion.ofTotal (id : C → C) (fun _ => rfl) (fun a b => mem b a)).SelfOnlyAt y :=
  fun hy => wf_no_selfloop h y hy.1

-- Statement: `ZFSet` has no Lawvere witness, since ∅ ≠ {∅} (`no_witness_of_nontrivial`).
example : ¬ HasLawvereWitness ZFSet :=
  no_witness_of_nontrivial (b₀ := (∅ : ZFSet)) (b₁ := ({∅} : ZFSet)) fun h => by
    have : (∅ : ZFSet) ∈ ({∅} : ZFSet) := ZFSet.mem_singleton.2 rfl
    rw [← h] at this
    exact ZFSet.notMem_empty _ this

-- Statement: CONTROL: under `trivialSelfApp`, the constant map to ⊥, the same occupancy holds; the
-- class fields alone give it, whatever the map is.
example {L : Type*} [ZPSemilattice L] (y : L) :
    (Motion.ofFun (@AbstractSelfApp.selfApp L _ (trivialSelfApp L))).SelfOnlyAt y ↔ y = bot :=
  @selfApp_quine_role_iff L _ (trivialSelfApp L) y

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms quine_dichotomy
#print axioms quine_self_members_eq_bot
#print axioms quine_no_literal
#print axioms selfApp_quine_role_iff
#print axioms quineAtomHost_quine_role_iff
end PurityCheck
