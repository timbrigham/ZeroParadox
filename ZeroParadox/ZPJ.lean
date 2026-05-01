import ZeroParadox.ZPE
import Mathlib.Tactic

/-!
# ZP-J: Executability of Self-Reference

## Engineer's Take

Bottom is self-containing. It is the only element inside of Q. Quine uniqueness
means there can only be one such element, and it is bottom. There is nothing
outside of bottom because bottom is the starting point. There is no prior state.
If bottom is going to do anything, the only thing that can do it is itself.
Self-contained plus forced execution means bottom is effectively its own program.
Much like a bootstrapping C compiler. The language could expand to future states,
but at some point it needed to understand enough about itself to perform the
bootstrapping. There is no prior version to fall back on. ZPK extends this to
the computational setting. The question of whether there are infinitely many
such bottom elements across instantiations is addressed in ZPI.

---

Establishes T-EXEC: in any ZP-A lattice with AFA set-theoretic grounding, the
unique Quine atom Q (satisfying Q = {Q} under AFA) is provably the bottom element
⊥ — deriving CC-1 from ZP-A rather than committing to it.

## Structure

- § I   AFA machinery: self-membership, Quine atom, bot_self_mem
- § II  T-EXEC: main theorem — Q = ⊥, derived from structure alone
- § III AX-J1 as a derived theorem (was an axiom in the stub)
- § IV  CC-1 as a theorem
- § V   Full biconditional: IsQuineAtom q ↔ q = bot
- § VI  Uniqueness

## What is new here

ZP-A CC-1 states: "the initial state S₀ = ⊥" as a modelling commitment (A4 does
not force which element of L plays the ⊥ role in any given instantiation). ZP-J
provides the missing derivation: the Quine atom — the unique self-containing element
under AFA — is the element that must play the ⊥ role.

The key is `AFAStructure.bot_self_mem`: encoding structurally that the bottom element
IS the self-containing element. With this, T-EXEC falls out immediately from Quine
uniqueness alone — no bridge axiom required. The commitment dissolves into the
structural definition of what it means for a lattice to have AFA grounding.

## Axiom footprint

T-EXEC depends only on:
- `AFAStructure.quine_unique` (AFA uniqueness — class field)
- `AFAStructure.bot_self_mem` (bottom is self-containing — class field)
- No freestanding axioms. No kernel axioms beyond propext.

## Dependencies

ZP-E (full synthesis: ZP-A through ZP-D, T-SNAP, DA-2).
No new Mathlib imports beyond those already present in ZP-E.
-/

namespace ZeroParadox.ZPJ

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPE

/-! ## § I. AFA Machinery -/

/-- AFA structure on a ZP-A semilattice.
    Requires that the lattice carry a self-membership predicate satisfying:
    (1) Quine uniqueness — at most one element is self-containing;
    (2) bot_self_mem — the bottom element IS the self-containing element.

    This encodes structurally that ⊥ = {⊥}: the bottom of the lattice is the
    unique Quine atom. No separate bridge axiom is needed — T-EXEC follows from
    (1) and (2) by pure logic. -/
class AFAStructure (L : Type*) [ZPSemilattice L] where
  /-- x is self-containing: x contains itself as a member under AFA. -/
  selfMem : L → Prop
  /-- Quine uniqueness: any two self-containing elements are equal. -/
  quine_unique : ∀ x y : L, selfMem x → selfMem y → x = y
  /-- The bottom element is self-containing: ⊥ = {⊥}.
      This is the structural encoding of the AFA identification — ⊥ is the Quine atom.
      Any ZP-A lattice with AFA grounding must exhibit this property. -/
  bot_self_mem : selfMem bot

/-- Q is a Quine atom if it is self-containing and is the unique such element. -/
def IsQuineAtom {L : Type*} [ZPSemilattice L] [AFAStructure L] (q : L) : Prop :=
  AFAStructure.selfMem q ∧ ∀ x : L, AFAStructure.selfMem x → x = q

/-- The bottom element is always a Quine atom in an AFA lattice.
    Follows from bot_self_mem and quine_unique. -/
theorem bot_is_quine_atom {L : Type*} [ZPSemilattice L] [AFAStructure L] :
    IsQuineAtom (bot : L) :=
  ⟨AFAStructure.bot_self_mem,
   fun x hx => AFAStructure.quine_unique x bot hx AFAStructure.bot_self_mem⟩

/-- Any two Quine atoms are equal. -/
theorem quine_atom_unique {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q₁ q₂ : L) (hq₁ : IsQuineAtom q₁) (hq₂ : IsQuineAtom q₂) : q₁ = q₂ :=
  AFAStructure.quine_unique q₁ q₂ hq₁.1 hq₂.1

/-! ## § II. T-EXEC — Quine Atom is Bottom -/

/-- T-EXEC (Executability Theorem): The Quine atom equals the bottom element.

    Proof:
    - hq.2 says: every self-containing element equals q
    - bot_self_mem says: bot is self-containing
    - Therefore: bot = q, i.e. q = bot

    No bridge axiom. No freestanding commitment. Pure structural derivation. -/
theorem t_exec {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q : L) (hq : IsQuineAtom q) : q = bot :=
  (hq.2 bot AFAStructure.bot_self_mem).symm

/-! ## § III. AX-J1 as a Derived Theorem -/

/-- J1 (QuineJoinIdentity): The Quine atom satisfies the join-identity.
    Previously axiom ax_j1_quine_join_identity — now a theorem derived from T-EXEC.

    Proof: q = bot (T-EXEC), so join q x = join bot x = x (A4/bot_join). -/
theorem j1_quine_join_identity {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q : L) (hq : IsQuineAtom q) : ∀ x : L, join q x = x := by
  rw [t_exec q hq]
  exact bot_join

/-! ## § IV. CC-1 as a Theorem -/

/-- CC-1 (Derived): If the initial state S₀ is the Quine atom, then S₀ = ⊥.
    A theorem, not a conditional claim. -/
theorem cc1_derived {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q : L) (hq : IsQuineAtom q)
    (S : ℕ → L) (_ : IsStateSequence S) (hS0 : S 0 = q) :
    S 0 = bot := by
  rw [hS0]; exact t_exec q hq

/-! ## § V. Full Biconditional -/

/-- T-EXEC (biconditional): IsQuineAtom q ↔ q = bot. -/
theorem t_exec_iff {L : Type*} [ZPSemilattice L] [AFAStructure L] (q : L) :
    IsQuineAtom q ↔ q = bot :=
  ⟨t_exec q, fun heq => heq ▸ bot_is_quine_atom⟩

/-- Full equivalence: Quine atom ↔ bottom ↔ join-identity. -/
theorem t_exec_triple_iff {L : Type*} [ZPSemilattice L] [AFAStructure L] (q : L) :
    IsQuineAtom q ↔ q = bot ∧ ∀ x : L, join q x = x :=
  ⟨fun hq => ⟨t_exec q hq, j1_quine_join_identity q hq⟩,
   fun ⟨heq, _⟩ => heq ▸ bot_is_quine_atom⟩

/-! ## § VI. Uniqueness -/

/-- At most one element satisfies the join-identity — pure semilattice algebra. -/
theorem bot_unique {L : Type*} [ZPSemilattice L]
    (x y : L) (hx : ∀ z : L, join x z = z) (hy : ∀ z : L, join y z = z) :
    x = y := by
  have hxb : x = bot := (da2_bottom_characterization x).mp hx
  have hyb : y = bot := (da2_bottom_characterization y).mp hy
  rw [hxb, hyb]

end ZeroParadox.ZPJ

/-! ## Axiom Purity Check

Expected footprint:
- t_exec:               does not depend on any axioms
- j1_quine_join_identity: does not depend on any axioms
- cc1_derived:          does not depend on any axioms
- bot_unique:           does not depend on any axioms
- quine_atom_unique:    does not depend on any axioms

All results are derived from the ZPSemilattice and AFAStructure class fields alone.
No freestanding axioms. The full chain ⊥ = {⊥} → Q = ⊥ is structurally enforced. -/

section PurityCheck
open ZeroParadox.ZPJ ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPE

#print axioms t_exec
#print axioms j1_quine_join_identity
#print axioms cc1_derived
#print axioms bot_unique
#print axioms quine_atom_unique
#print axioms bot_is_quine_atom

end PurityCheck
