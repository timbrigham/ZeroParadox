import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.SetTheoryAFA
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The Quine-Host Requirements — the AFA fragment the framework actually needs

## Engineer's Take

So this one is an interesting one. In order to connect AFA and ZFC directly, it's
impossible to do due to type mismatches. What it is possible to do is make a list of
requirements that AFA satisfies, or that in theory another framework could fill, and
match based on those attributes. That's my computer programmer logic from my day job
slipping in.

---

## Formal Overview (AI-assisted)

The framework's set-theoretic commitment used to read "we adopt ZF + AFA." That
over-states it: the development's set-theoretic *assumption* is only the fragment
that supplies a *unique self-containing bottom* ⊥ = {⊥}, not the full Anti-Foundation
Axiom (AFA's "every graph has a unique decoration"). Naming "AFA specifically" is a
judgment call about which axiom system to adopt; naming the *requirements*, with AFA
as one witness, is the honest statement. (This is an assumption-side claim, not a
sufficiency claim: where AFA-specific content is used elsewhere — e.g. decoration
uniqueness in `ZeroParadox/Settheory/APG.lean` — it is proved on its own terms, not
assumed from full AFA.)

This file makes that reframe a citable object. `QuineHost` is a typeclass encoding
the two requirements a host theory must supply:

- **(Y)** `bot` is a Quine atom — `mem bot bot`, i.e. ⊥ = {⊥};
- **(Z)** that atom is unique — the only self-membered element is `bot`.

A third requirement, **(X) Foundation-free**, is NOT assumed: it is *forced* by (Y)
and proved here (`quineHost_not_wellFounded`). The three standard theories then sort
out — two as machine-checked theorems, Boffa by a mechanism-witness:

- **ZFC + Foundation fails (Y)** in-kernel about Mathlib's real `ZFSet`:
  `zfSet_no_quine_bottom` (via `no_quine_atom`, `ZeroParadox/Settheory/Wall.lean`).
- **Boffa fails (Z)**: its axiom admits a proper class of Quine atoms rather than one
  (Boffa 1968); the mechanism — self-membership without the uniqueness clause admits
  many atoms — is witnessed by a toy model (`boffa_fails_unique`), not an in-kernel
  result about Boffa's axiom itself.
- **AFA satisfies (X), (Y), (Z)**: it is the canonical example, exhibited as
  `afaStructure_isQuineHost` off the framework's own `AFAStructure`
  (`ZeroParadox/Settheory/SetTheoryAFA.lean`), with a concrete satisfiable model
  (`OneAtom`) witnessing the requirements are non-vacuous.

**Honest status.** What is *proved*: (X) is forced by (Y); Foundation excludes (Y);
Boffa fails (Z); the requirements are realizable; AFA meets them. What remains a
*modeling commitment* (a design principle, not a theorem): that (Y) and (Z) are the
right requirements to demand. AFA is the witness that a theory meeting them exists —
not itself the commitment. This shrinks the old "AFA is forced" Forced Metatheoretic
Commitment to "these requirements are the right ones," with the requirements
themselves grounded/proved.

## Structure

- § I   The `QuineHost` requirements typeclass — (Y) and (Z)
- § II  (X) is forced — any host is Foundation-free (not well-founded)
- § III Foundation (ZFSet) fails (Y) — no Quine atom in-kernel
- § IV  Boffa fails (Z) — permissiveness admits many atoms
- § V   The requirements are realizable — a concrete one-atom model
- § VI  AFA is the canonical example — from the framework's `AFAStructure`
-/

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. The requirements a host theory must supply -/

/-- **The Quine-Host requirements.** A type `L` with a membership relation `mem` and a
    distinguished `bot` *hosts the framework's bottom* when:
    - **(Y)** `bot` is a Quine atom: `mem bot bot`, i.e. ⊥ = {⊥} (self-containing);
    - **(Z)** that atom is unique: the only self-membered element is `bot`.

    Requirement **(X)** — that the host is Foundation-free (its membership is not
    well-founded) — is deliberately NOT a field: it is *forced* by (Y), and proved
    below as `quineHost_not_wellFounded`.

    This is the AFA *fragment* the framework actually uses, not the full Anti-Foundation
    Axiom. AFA (Aczel, Non-Well-Founded Sets, CSLI 1988) is the canonical set theory
    meeting these requirements (§ VI); Boffa's axiom (Boffa 1968; and the AFA/Boffa
    comparison in Barwise & Moss, Vicious Circles, CSLI 1996) meets (Y) but admits a
    proper class of Quine atoms, so fails (Z) (§ IV); ZFC + Foundation fails (Y)
    in-kernel (§ III). Naming the requirements, rather than committing to "AFA
    specifically," is the honest form of the framework's set-theoretic commitment: a
    design choice of *these requirements*, witnessed by AFA, not an adoption of AFA. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's ZFSet carries Foundation (ZFSet.mem_wf), which forbids x ∈ x, so it cannot host a Quine atom; and no Mathlib typeclass abstracts "a membership relation with a unique self-membered bottom." QuineHost is the minimal set-theory-native encoding of the framework's requirements on a host theory (fields bot_selfMem/selfMem_unique), distinct from the lattice-level AFAStructure in SetTheoryAFA.lean.
class QuineHost (L : Type*) where
  /-- The host's membership relation. -/
  mem : L → L → Prop
  /-- The distinguished bottom element. -/
  bot : L
  /-- (Y) The bottom is a Quine atom: ⊥ = {⊥}. -/
  bot_selfMem : mem bot bot
  /-- (Z) Uniqueness: the only self-membered element is the bottom. -/
  selfMem_unique : ∀ x : L, mem x x → x = bot

/-! ## § II. (X) is forced — any host is Foundation-free -/

/-- **(X), forced.** A Quine host's membership relation is not well-founded: (Y) puts a
    self-loop at `bot`, and a well-founded relation admits no self-loop (`wf_no_selfloop`).
    So the host cannot carry Foundation — Foundation-freeness is a *consequence* of hosting
    a Quine atom, not an independent assumption. -/
theorem quineHost_not_wellFounded (L : Type*) [QuineHost L] :
    ¬ WellFounded (QuineHost.mem : L → L → Prop) :=
  fun h => wf_no_selfloop h QuineHost.bot QuineHost.bot_selfMem

/-- The bottom is the unique self-membered element, packaged as a biconditional:
    an element is self-membered iff it is the bottom. -/
theorem quineHost_selfMem_iff (L : Type*) [QuineHost L] (x : L) :
    QuineHost.mem x x ↔ x = QuineHost.bot :=
  ⟨QuineHost.selfMem_unique x, fun h => h ▸ QuineHost.bot_selfMem⟩

/-! ## § III. Foundation fails (Y) — no Quine atom under ZFC -/

/-- **ZFC + Foundation fails requirement (Y).** Under Foundation, `∈` is well-founded on
    `ZFSet` (`ZFSet.mem_wf`), so no set is self-membered (`no_quine_atom`). Hence there is
    no candidate bottom for a `QuineHost` structure on `ZFSet` with `mem = (· ∈ ·)`: the
    (Y) field is unsatisfiable. This is the in-kernel exclusion of the literal Quine atom. -/
theorem zfSet_no_quine_bottom : ¬ ∃ b : ZFSet, b ∈ b :=
  fun ⟨b, hb⟩ => no_quine_atom b hb

/-! ## § IV. Boffa fails (Z) — permissiveness admits many atoms -/

/-- A Boffa-shaped membership on `Bool`: every element is self-membered. Boffa's
    anti-foundation axiom permits a proper class of Quine atoms; two suffice to break
    uniqueness. -/
def BoffaMem : Bool → Bool → Prop := fun _ _ => True

theorem boffaMem_all_selfMem (x : Bool) : BoffaMem x x := trivial

/-- **Boffa fails requirement (Z).** With every element self-membered, no single element is
    *the* self-membered one: `true` and `false` are both Quine atoms and distinct. So (Y)
    without (Z) does not pin down a bottom — uniqueness is exactly the requirement that
    rules Boffa out, and it is not derivable from self-membership alone. -/
theorem boffa_fails_unique : ¬ ∃ b : Bool, ∀ x : Bool, BoffaMem x x → x = b := by
  rintro ⟨b, hb⟩
  have h1 : true = b := hb true trivial
  have h2 : false = b := hb false trivial
  exact Bool.noConfusion (h1.trans h2.symm)

/-! ## § V. The requirements are realizable — a concrete one-atom model -/

/-- A concrete two-element host: `bot` (self-membered) and one `other` element (not). This
    is the minimal shape AFA supplies — a single Quine atom, everything else ordinary — and
    it witnesses that the `QuineHost` requirements are jointly consistent (non-vacuous). -/
inductive OneAtom where
  | bot
  | other

instance : QuineHost OneAtom where
  mem := fun x y => x = OneAtom.bot ∧ y = OneAtom.bot
  bot := OneAtom.bot
  bot_selfMem := ⟨rfl, rfl⟩
  selfMem_unique := fun _ hx => hx.1

/-- The concrete model does host a Quine atom (its `bot` is self-membered) yet is not
    well-founded — the requirements are satisfiable. -/
theorem oneAtom_not_wellFounded :
    ¬ WellFounded (QuineHost.mem : OneAtom → OneAtom → Prop) :=
  quineHost_not_wellFounded OneAtom

/-! ## § VI. AFA is the canonical example -/

/-- **AFA is a Quine host.** The framework's lattice-level AFA grounding (`AFAStructure`,
    the encoding of what ZF + AFA supplies — see `ZeroParadox/Settheory/SetTheoryAFA.lean`)
    satisfies the `QuineHost` requirements: take `mem x y := selfMem x ∧ x = y`, so
    `mem x x ↔ selfMem x`; then (Y) is `bot_self_mem` and (Z) is `quine_unique`. This
    exhibits AFA as the canonical example meeting the requirements — the witness the honest
    framing points to, not a committed choice. -/
@[reducible]
def afaStructure_isQuineHost (L : Type*) [ZPSemilattice L] [AFAStructure L] :
    QuineHost L where
  mem := fun x y => AFAStructure.selfMem x ∧ x = y
  bot := bot
  bot_selfMem := ⟨AFAStructure.bot_self_mem, rfl⟩
  selfMem_unique := fun x hx =>
    AFAStructure.quine_unique x bot hx.1 AFAStructure.bot_self_mem

end ZeroParadox

/-! ## Axiom Purity Check

Expected footprint:
- quineHost_not_wellFounded:  class fields + `wf_no_selfloop` (axiom-free)
- quineHost_selfMem_iff:      class fields only
- boffa_fails_unique:         axiom-free (Bool.noConfusion)
- oneAtom_not_wellFounded:    axiom-free
- zfSet_no_quine_bottom:      inherits `no_quine_atom`'s footprint (Foundation via ZFSet;
                              choice-free — [propext, Quot.sound])

The one non-empty footprint (`zfSet_no_quine_bottom`) is expected: it is the ZFSet /
Foundation exclusion, and rides on Mathlib's `ZFSet.mem_wf`. -/

section PurityCheck
open ZeroParadox

#print axioms quineHost_not_wellFounded
#print axioms quineHost_selfMem_iff
#print axioms boffa_fails_unique
#print axioms oneAtom_not_wellFounded
#print axioms zfSet_no_quine_bottom
#print axioms afaStructure_isQuineHost

end PurityCheck
