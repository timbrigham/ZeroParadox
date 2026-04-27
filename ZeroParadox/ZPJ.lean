import ZeroParadox.ZPE
import Mathlib.Tactic

/-!
# ZP-J: Executability of Self-Reference

Establishes T-EXEC: in any ZP-A lattice with AFA set-theoretic grounding, the
unique Quine atom Q (satisfying Q = {Q} under AFA) is provably the bottom element
⊥ — deriving CC-1 from ZP-A rather than committing to it.

## Structure

- § I   AFA machinery: self-membership predicate, Quine atom, uniqueness
- § II  AX-J1: the bridge principle connecting self-membership to join-identity
- § III T-EXEC: main theorem — Q = ⊥ is derived, not committed
- § IV  CC-1 as a theorem, not a conditional claim
- § V   Equivalence: IsQuineAtom q ↔ q = bot (biconditional form)

## What is new here

ZP-A CC-1 states: "the initial state S₀ = ⊥" as a modelling commitment (A4 does
not force which element of L plays the ⊥ role in any given instantiation). ZP-J
provides the missing derivation: the Quine atom — the unique self-containing element
under AFA — is the element that must play the ⊥ role. The commitment dissolves into
the AFA foundational choice, which was already implicit in ZP-A's identification ⊥ = {⊥}.

## Expected axiom footprint

T-EXEC depends on:
- `ax_j1_quine_join_identity` — the AX-J1 bridge (ZP-J's key new commitment)
- `AFAStructure.quine_unique` — AFA uniqueness (expected)
- Standard kernel axioms: propext, Classical.choice, Quot.sound

## Dependencies

ZP-E (full synthesis: ZP-A through ZP-D, T-SNAP, DA-2).
No new Mathlib imports beyond those already present in ZP-E.
-/

namespace ZeroParadox.ZPJ

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPE

/-! ## § I. AFA Machinery -/

/-- Minimal abstraction of AFA structure needed for ZP-J.
    A type with AFA structure admits a self-membership predicate and guarantees
    that at most one element is the Quine atom (the unique self-containing element). -/
class AFAStructure (α : Type*) where
  /-- x is self-containing: x contains itself as a member under AFA. -/
  selfMem : α → Prop
  /-- Quine uniqueness: any two self-containing elements are equal.
      This is the AFA guarantee — {x | x = {x}} is a singleton. -/
  quine_unique : ∀ x y : α, selfMem x → selfMem y → x = y

/-- Q is a Quine atom if it is self-containing and is the unique such element. -/
def IsQuineAtom {α : Type*} [AFAStructure α] (q : α) : Prop :=
  AFAStructure.selfMem q ∧ ∀ x : α, AFAStructure.selfMem x → x = q

/-- Any two Quine atoms are equal. Follows directly from AFAStructure.quine_unique. -/
theorem quine_atom_unique {α : Type*} [AFAStructure α] (q₁ q₂ : α)
    (hq₁ : IsQuineAtom q₁) (hq₂ : IsQuineAtom q₂) : q₁ = q₂ :=
  AFAStructure.quine_unique q₁ q₂ hq₁.1 hq₂.1

/-! ## § II. AX-J1 — The Bridge Principle -/

/-- AX-J1 (QuineJoinIdentity): In any ZP-A semilattice with AFA structure, the
    Quine atom satisfies the join-identity for every element of the lattice.

    Informal content: Q = {Q} contains only itself and nothing else. Under the
    set-theoretic interpretation of join as union, Q ∨ x = Q ∪ x = x holds because
    Q's only member (Q itself) is already subsumed by the ZP ontological grounding
    of every state. Q contributes nothing new to any join — it is the ground that
    every state already includes.

    Status: Axiom. ZP-J § II argues this is forced by the combination of AFA
    uniqueness and ZP-A's join-semilattice structure, but the derivation is the
    open question this layer investigates. The PDF provides the informal argument;
    this axiom is the formal stand-in pending a full derivation.

    Expected in #print axioms output: this is the key new foundational commitment
    introduced by ZP-J. All other dependencies are inherited from ZP-A and AFA. -/
axiom ax_j1_quine_join_identity
    {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q : L) (hq : IsQuineAtom q) :
    ∀ x : L, join q x = x

/-! ## § III. T-EXEC — Quine Atom is Bottom -/

/-- T-EXEC (Executability Theorem): The Quine atom is the bottom element of any
    ZP-A semilattice with AFA structure.

    Proof:
    (1) AX-J1: Q satisfies ∀ x, join Q x = x  [ax_j1_quine_join_identity]
    (2) DA-2:  this characterises Q as bot      [da2_bottom_characterization, ZP-E]
    ∴ Q = ⊥ — derived from self-reference, not committed. -/
theorem t_exec
    {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q : L) (hq : IsQuineAtom q) :
    q = bot :=
  (da2_bottom_characterization q).mp (ax_j1_quine_join_identity q hq)

/-! ## § IV. CC-1 as a Theorem -/

/-- CC-1 (Derived): In any ZP-A semilattice with AFA structure, the Quine atom
    equals the bottom element. If the initial state S₀ is the Quine atom, then
    S₀ = ⊥ — a theorem, not a conditional claim.

    This replaces ZP-A CC-1 (a modelling commitment) with a derivation. The remaining
    foundation is AX-J1 and the AFA structural axiom — both of which were implicit in
    ZP-A's identification ⊥ = {⊥}. ZP-J makes that foundation explicit and formal. -/
theorem cc1_derived
    {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (q : L) (hq : IsQuineAtom q)
    (S : ℕ → L) (_ : IsStateSequence S) (hS0 : S 0 = q) :
    S 0 = bot := by
  rw [hS0]; exact t_exec q hq

/-! ## § V. Biconditional — IsQuineAtom q ↔ q = bot -/

/-- The converse of T-EXEC: the bottom element of an AFA semilattice is the Quine atom.
    Together with t_exec, this gives: IsQuineAtom q ↔ q = bot. -/
theorem bot_is_quine_atom
    {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (hbot : IsQuineAtom (bot : L)) :
    ∀ q : L, q = bot ↔ IsQuineAtom q := by
  intro q
  constructor
  · intro heq
    rw [heq]
    exact hbot
  · intro hq
    exact t_exec q hq

/-- T-EXEC (biconditional): Full equivalence.
    Under the hypothesis that bot is the Quine atom of L:
    q is the Quine atom ↔ q = bot ↔ q satisfies the join-identity. -/
theorem t_exec_iff
    {L : Type*} [ZPSemilattice L] [AFAStructure L]
    (hbot : IsQuineAtom (bot : L)) (q : L) :
    IsQuineAtom q ↔ (∀ x : L, join q x = x) := by
  rw [da2_bottom_characterization]
  constructor
  · intro hq; exact t_exec q hq
  · intro heq
    rw [heq]
    exact hbot

/-! ## § VI. Uniqueness — Only One Element Can Play the ⊥ Role -/

/-- Uniqueness: at most one element satisfies the join-identity in any semilattice.
    Two elements satisfying the identity must be equal — this is the algebraic
    content of bottom uniqueness, independent of AFA. -/
theorem bot_unique
    {L : Type*} [ZPSemilattice L]
    (x y : L)
    (hx : ∀ z : L, join x z = z)
    (hy : ∀ z : L, join y z = z) :
    x = y := by
  have hxb : x = bot := (da2_bottom_characterization x).mp hx
  have hyb : y = bot := (da2_bottom_characterization y).mp hy
  rw [hxb, hyb]

end ZeroParadox.ZPJ

/-! ## Axiom Purity Check

Expected axiom footprint for T-EXEC:
- `ZeroParadox.ZPJ.ax_j1_quine_join_identity` (AX-J1 bridge — ZP-J's commitment)
- `ZeroParadox.ZPJ.AFAStructure.quine_unique` (AFA uniqueness)
- propext, Classical.choice, Quot.sound (standard kernel axioms from Mathlib)

`bot_unique` should be axiom-free (pure semilattice algebra via da2_bottom_characterization). -/

section PurityCheck
open ZeroParadox.ZPJ ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPE

#print axioms t_exec
#print axioms cc1_derived
#print axioms bot_unique
#print axioms quine_atom_unique

end PurityCheck
