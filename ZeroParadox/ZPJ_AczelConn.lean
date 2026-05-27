import ZeroParadox.ZPJ
import Mathlib.Tactic

/-!
# ZPJ — Aczel Fixed Point Connection (Exploratory)

Aczel (Non-Well-Founded Sets, 1988, ch. 6, p. 77) proves that
J_Φ = ⋃{x | x ⊆ Φx} is the largest fixed point of a set continuous
operator Φ. The proof uses the axiom of dependent choices (DC) to
construct an ω-chain, and Aczel explicitly notes:

  "I do not know if this use of the axiom of dependent choices was essential."

**The ZP claim:** For the self-membership operator induced by AFA, DC is
unnecessary. AFA's uniqueness clause (quine_unique: "every graph has a
unique decoration") directly identifies the largest pre-fixed-point as bot.
No ω-chain construction needed — identification replaces construction.

**Why:** DC is used when you must *build* a witness step by step because
the fixed point cannot be identified structurally. In ZF+AFA, the Quine
atom is unique by the axiom itself. In the ZP encoding, quine_unique is
a class field that directly gives this. The chain is redundant.

**Scope:** This applies to the self-membership case. Whether the principle
extends to all set continuous operators depends on whether uniqueness holds
for each Φ — open in general, as Aczel's "I do not know" reflects.

**Connection to ZP's discrete/transfinite bridge:** ZP's framework is
discrete on the input side (binary states, Quine atom, ZF+AFA grounding).
DC is used in Aczel's continuous/coinductive applications (streams, ω-chains).
The absence of DC here is a consequence of ZP's discrete foundation — the
fixed point is forced, not constructed.
-/

namespace ZeroParadox.AczelConn

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ

/-! ## § I. The Self-Membership Operator and its Largest Pre-Fixed-Point -/

section SelfMembershipOperator

variable {L : Type*} [ZPSemilattice L] [AFAStructure L]

/-- J_self: elements satisfying selfMem — the "largest pre-fixed-point"
    of the self-membership operator, corresponding to Aczel's J_Φ.
    In Aczel's set theory: J = ⋃{x | x = {x}} = {Ω} (the Quine atom).
    Here: J_self = {x : L | selfMem x}. -/
def J_self : Set L := {x | AFAStructure.selfMem x}

/-- bot ∈ J_self: the bottom element is self-containing. (Aczel 6.5 part 1.) -/
theorem bot_mem_J_self : (bot : L) ∈ J_self :=
  AFAStructure.bot_self_mem

/-- Every element of J_self equals bot.
    This is the ZP substitute for Aczel's DC ω-chain: quine_unique forces
    any self-containing element to equal bot in one step. -/
theorem J_self_eq_bot (x : L) (hx : x ∈ J_self) : x = bot :=
  AFAStructure.quine_unique x bot hx AFAStructure.bot_self_mem

/-- J_self = {bot}: the unique self-containing element is bot.
    Aczel Theorem 6.5, self-membership case — proved WITHOUT DC.
    The ω-chain is replaced by a single application of quine_unique. -/
theorem J_self_eq_singleton_bot : J_self = ({bot} : Set L) := by
  ext x
  unfold J_self
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun hx => AFAStructure.quine_unique x bot hx AFAStructure.bot_self_mem,
         fun heq => heq ▸ AFAStructure.bot_self_mem⟩

/-- J_self is itself a pre-fixed-point: every element of J_self is self-containing.
    (In Aczel's language: J ⊆ ΦJ.) -/
theorem J_self_is_prefixed (x : L) (hx : x ∈ J_self) : AFAStructure.selfMem x :=
  hx

/-- J_self is the largest pre-fixed-point.
    If S is any set of self-containing elements, then S ⊆ J_self.
    This corresponds to Aczel 6.5 part (2) — without DC. -/
theorem J_self_is_largest (S : Set L)
    (hS : ∀ x ∈ S, AFAStructure.selfMem x) : S ⊆ J_self :=
  fun x hx => hS x hx

/-- Equivalently: any pre-fixed-point set S has all elements equal to bot. -/
theorem prefixed_elems_eq_bot (S : Set L)
    (hS : ∀ x ∈ S, AFAStructure.selfMem x)
    (x : L) (hx : x ∈ S) : x = bot :=
  J_self_eq_bot x (hS x hx)

end SelfMembershipOperator

/-! ## § II. The General Principle: Uniqueness Eliminates DC

    Aczel uses DC to *construct* a witness. The abstract principle:
    when a predicate P has a unique witness, the witness is identified
    directly — no chain needed.
-/

section UniquenessEliminatesDC

variable {α : Type*}

/-- If predicate P has a unique witness w, then {x | P x} = {w}.
    DC-free: uniqueness collapses construction to identification.
    Abstract form of the ZP argument (P = selfMem, w = bot). -/
theorem singleton_from_unique_witness
    (P : α → Prop)
    (w : α) (hw : P w)
    (h_unique : ∀ x, P x → x = w) :
    {x | P x} = ({w} : Set α) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨h_unique x, fun heq => heq ▸ hw⟩

/-- Application: selfMem is a unique predicate in any AFAStructure. -/
theorem selfMem_determines_singleton {L : Type*} [ZPSemilattice L] [AFAStructure L] :
    {x : L | AFAStructure.selfMem x} = ({bot} : Set L) :=
  singleton_from_unique_witness
    AFAStructure.selfMem
    bot
    AFAStructure.bot_self_mem
    (fun x hx => AFAStructure.quine_unique x bot hx AFAStructure.bot_self_mem)

end UniquenessEliminatesDC

end ZeroParadox.AczelConn

/-! ## Axiom Purity Check

DC-free claim: none of these results should depend on Classical.choice
or any axiom beyond propext (from Set extensionality) and the class
fields of ZPSemilattice and AFAStructure.
-/

section PurityCheck
open ZeroParadox.AczelConn

#print axioms J_self_eq_singleton_bot
#print axioms J_self_is_largest
#print axioms prefixed_elems_eq_bot
#print axioms singleton_from_unique_witness
#print axioms selfMem_determines_singleton

end PurityCheck
