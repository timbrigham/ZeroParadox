import ZeroParadox.Settheory.SetTheoryAFA
import Mathlib.Tactic

/-!
# ZPJ — Aczel Fixed Point Connection

## Engineer's Take

A ZP-J/AFA sub-file. See the Engineer's Take in `ZeroParadox/Settheory/SetTheoryAFA.lean`.

---

`Statement:` in an `AFAStructure` lattice the self-containing set is `{⊥}` and holds every set of
self-containing elements, with no `Classical.choice`. `Reading:` `J_self` is shaped like Aczel's `J_Φ`
(Non-Well-Founded Sets, 1988, Theorem 6.5), not an instance: no set-continuous operator is defined, so
the step where his proof of 6.5(2) uses Dependent Choice has no counterpart here (pp. 76–77).
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox

/-! ## § I. The Self-Containing Set J_self -/

section SelfMembershipOperator

variable {L : Type*} [ZPSemilattice L] [AFAStructure L]

/-- J_self: the elements satisfying selfMem, defined directly by comprehension.
    `Reading:` shaped like Aczel's J_Φ, not an instance of it — no operator Φ is defined here.
    Here: J_self = {x : L | selfMem x}. -/
def J_self : Set L := {x | AFAStructure.selfMem x}

/-- bot ∈ J_self: the lattice bottom is self-containing. (AFAStructure.bot_self_mem.) -/
theorem bot_mem_J_self : (bot : L) ∈ J_self :=
  AFAStructure.bot_self_mem

/-- Every element of J_self equals bot.
    quine_unique identifies any self-containing element as bot in one step; that
    identification corresponds to no step of Aczel's proof. -/
theorem J_self_eq_bot (x : L) (hx : x ∈ J_self) : x = bot :=
  AFAStructure.quine_unique x bot hx AFAStructure.bot_self_mem

/-- J_self = {bot}: the unique self-containing element is bot, with no Classical.choice.
    Corresponds to no clause of Aczel's Theorem 6.5. -/
theorem J_self_eq_singleton_bot : J_self = ({bot} : Set L) := by
  ext x
  unfold J_self
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun hx => AFAStructure.quine_unique x bot hx AFAStructure.bot_self_mem,
         fun heq => heq ▸ AFAStructure.bot_self_mem⟩

/-- Every element of J_self is self-containing.
    The shape of Aczel 6.5 part (1), J ⊆ ΦJ, not an instance of it: no operator Φ is defined here. -/
theorem J_self_is_prefixed (x : L) (hx : x ∈ J_self) : AFAStructure.selfMem x :=
  hx

/-- If S is any set of self-containing elements, then S ⊆ J_self.
    Holds by the definition of J_self, for any predicate, and uses no uniqueness: the shape of
    Aczel 6.5 part (2), not an instance of it. -/
theorem J_self_is_largest (S : Set L)
    (hS : ∀ x ∈ S, AFAStructure.selfMem x) : S ⊆ J_self :=
  fun x hx => hS x hx

/-- Any set S of self-containing elements has all its elements equal to bot. No axioms. -/
theorem prefixed_elems_eq_bot (S : Set L)
    (hS : ∀ x ∈ S, AFAStructure.selfMem x)
    (x : L) (hx : x ∈ S) : x = bot :=
  J_self_eq_bot x (hS x hx)

end SelfMembershipOperator

/-! ## § II. A Unique Witness Determines Its Set

    When a predicate P has a unique witness w, its extension is exactly {w}.
-/

section UniqueWitness

variable {α : Type*}

/-- If predicate P has a unique witness w, then {x | P x} = {w}. No Classical.choice.
    Abstract form of J_self_eq_singleton_bot (P = selfMem, w = bot). -/
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

end UniqueWitness

end ZeroParadox

/-! ## Axiom Purity Check

Target: no `Classical.choice`. The lines below are the measurement.
-/

section PurityCheck
open ZeroParadox

#print axioms J_self_eq_singleton_bot
#print axioms J_self_is_largest
#print axioms prefixed_elems_eq_bot
#print axioms singleton_from_unique_witness
#print axioms selfMem_determines_singleton

end PurityCheck
