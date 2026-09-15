import ZeroParadox.Order.Snap
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

`Statement:` in a ZP-A lattice with `AFAStructure`, any Quine atom (self-containing, and the only such) is ⊥ (`t_exec`,
from `bot_self_mem`; no axioms), and CC-1 is restated: `cc1_derived` with `t_exec_iff` makes a Quine-atom start and a ⊥
start one condition. On a carrier with a second point it is not forced (`ZeroParadox/Settheory/OntBridge.lean`).
`Reading:` the role encodes the ZF+AFA set Q = {Q}; that ⊥ is that set is CC-2's commitment. (NO-GO gauge below.)
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox

/-! ## § I. AFA Machinery -/

/-- AFA structure on a ZP-A semilattice.
    Requires that the lattice carry a self-membership predicate satisfying:
    (1) Quine uniqueness — at most one element is self-containing;
    (2) bot_self_mem — the bottom element IS the self-containing element.

    Field (2) places ⊥ in the Quine-atom role (the lattice encoding of the ZF+AFA set Q = {Q}).
    T-EXEC follows from field (2) and its own hypothesis; field (1) is used by the converse. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's ZFSet uses the Axiom of Foundation (ZFSet.regularity), which forbids x ∈ x. No ZFSet element can satisfy x ∈ x, so a Quine atom is not directly available as a ZFSet; AFA content is still MODELLABLE over a well-founded universe, as Aczel does via decorations of accessible pointed graphs. AFAStructure is the lattice-level encoding of what ZF+AFA provides set-theoretically, with selfMem/quine_unique/bot_self_mem as the three minimal class fields.
class AFAStructure (L : Type*) [ZPSemilattice L] where
  /-- x plays the self-containment role; read in ZF+AFA, x = {x} (its own sole member). Not bare
      x ∈ x: under AFA, 0* = {∅, 0*} is self-membered and is not Ω (Aczel 1988, Example 1.5),
      so `quine_unique` would fail for membership. -/
  selfMem : L → Prop
  /-- Quine uniqueness: any two self-containing elements are equal.
      In ZF+AFA this follows directly from AFA's own statement ("every graph has a unique
      decoration") — any self-containing set q satisfying q = {q} is a decoration of the
      one-node self-loop apg (a graph with one node and one self-edge, accessible from its
      root); AFA uniqueness then forces at most one such set. This field encodes what AFA
      already provides in ZF+AFA, not a new axiom beyond that — though in the Lean encoding
      it must be asserted as a class field, since the abstract lattice lacks the
      graph-decoration semantics and set-membership infrastructure that give AFA's uniqueness
      clause its content.
      Source: Aczel, Non-Well-Founded Sets (CSLI 1988), ch. 1. -/
  quine_unique : ∀ x y : L, selfMem x → selfMem y → x = y
  /-- The bottom element is self-containing: this field places ⊥ in the Quine-atom role (the
      lattice encoding of the ZF+AFA set Q = {Q}). Every ZP-A lattice can supply it (NO-GO gauge). -/
  bot_self_mem : selfMem bot

/-! ### NO-GO gauge — nothing fails, and that is EXPECTED (Tim, 2026-08-09).

Measured by building it: `selfMem x := x = bot` discharges both fields on *any* `[ZPSemilattice L]`,
as `ZeroParadox/Computability/SelfApp.lean`'s `toAFAStructure` does generically. `⊥ = {⊥}` is a
cross-type `=`, so the class encodes the **role**: the `ZeroParadox/Settheory/QuineHost.lean` pattern.

**Two readings it must not license.** `[AFAStructure L]` imports no anti-foundation content, so
*"L carries it, therefore ⊥ is a Quine atom"* is circular; and universal inhabitation is no evidence
for a universality claim about AFA, the construction being definitional. ⚠ **There is no
non-member** — `selfMem := fun _ => False` is a failing field VALUE, not a failing carrier. -/

/-- Q is a Quine atom if it is self-containing and is the unique such element. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Lattice-level analog of Aczel's Quine atom (the unique set satisfying x = {x}). No Mathlib definition covers this: it requires AFAStructure context and encodes the conjunction of self-containment + uniqueness as a single predicate.
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

    No bridge axiom: the field bot_self_mem is the input, and quine_unique is not used. -/
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

/-! ## § IV. CC-1, Conditional Form -/

/-- CC-1, conditional form: if the initial state S₀ is a Quine atom, then S₀ = ⊥. With `t_exec_iff`
    the converse holds, so the two starting conditions are one; neither is forced on a carrier with a second point. -/
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

end ZeroParadox

/-! ## Axiom Purity Check

Expected footprint: no axioms for every declaration printed below (the lines are the measurement).
All results take the ZPSemilattice and AFAStructure class fields as hypotheses; none adds an axiom. -/

section PurityCheck
open ZeroParadox ZeroParadox ZPSemilattice ZeroParadox

#print axioms t_exec
#print axioms j1_quine_join_identity
#print axioms cc1_derived
#print axioms bot_unique
#print axioms quine_atom_unique
#print axioms bot_is_quine_atom
#print axioms t_exec_iff
#print axioms t_exec_triple_iff

end PurityCheck
