import ZeroParadox.ZPB
import ZeroParadox.ZPJ_SelfApp
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZPJ_OntBridge — OntologicalStates → AbstractSelfApp → AFA Content

## Engineer's Take

ZPJ_Scale proved the full derivation chain ValuationStructure → AbstractSelfApp → AFA
content, and ZPJ_Model gave ℕ∞ as the concrete ValuationStructure instance. That chain
requires an infinite domain: the val_scale axiom (val(scale x) = val x + 1) has no room
to operate in a two-element type.

OntologicalStates — ZPB's {null, exist} — cannot be a ValuationStructure instance for
exactly this reason. A finite two-element lattice cannot satisfy val_scale. But it can
be an AbstractSelfApp instance directly. The self-application operation is the
constant-to-null function: every element maps to null. This makes null the unique fixed
point — the only element that maps to itself — which is all AbstractSelfApp requires.
AFA content follows immediately.

This is the shorter on-ramp. ℕ∞ takes the full ValuationStructure path. OntologicalStates
takes the direct AbstractSelfApp path. Both end at the same AFA content. The architecture
is sound because the reasoning is mathematically honest: two elements is not enough for
val_scale, and saying so is cleaner than pretending otherwise.

Result: null is the unique self-containing element of OntologicalStates — formally proved
in Lean, from ZPB structure alone, without importing any AFA axioms.
-/

namespace ZeroParadox.OntBridge

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPB
open ZeroParadox.SelfApp

/-! ## §I. ZPSemilattice Instance for OntologicalStates

null is the bottom element (identity for join). exist absorbs: joining anything
with exist gives exist. The ZP partial order: null ≤_ZP exist. -/

/-- OntologicalStates with null-identity join and bot = null is a ZPSemilattice. -/
-- [ZP-CUSTOM] instance: ZPSemilattice OntologicalStates | reason: OntologicalStates carries no Mathlib lattice structure. The join (null-identity, exist-absorbing) matches ZP-A's A1–A4 but doesn't correspond to any Mathlib-provided instance on a two-element type.
instance instOntZPS : ZPSemilattice OntologicalStates where
  join       := fun a b => match a with | .null => b | .exist => .exist
  bot        := .null
  join_assoc := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  join_comm  := by intro a b; cases a <;> cases b <;> rfl
  join_idem  := by intro a; cases a <;> rfl
  bot_join   := by intro a; cases a <;> rfl

/-! ## §II. AbstractSelfApp Instance for OntologicalStates

selfApp is the constant-to-null function. null maps to itself (fixed_bot).
exist maps to null and is therefore not a fixed point (unique_fp holds vacuously). -/

/-- OntologicalStates carries an AbstractSelfApp structure via the constant-to-null map. -/
-- [ZP-CUSTOM] instance: AbstractSelfApp OntologicalStates via constant-to-null | reason: OntologicalStates (two elements) cannot satisfy ValuationStructure's val_scale axiom — a finite two-element type has no room for val to strictly increase. Direct AbstractSelfApp instance using the constant-to-null map (every element → null) is the shorter path to AFA content for finite types.
instance instOntSelfApp : AbstractSelfApp OntologicalStates where
  selfApp   := fun _ => .null
  fixed_bot := rfl
  unique_fp := by
    intro x hx
    cases x with
    | null  => rfl
    | exist => exact absurd hx (by decide)

/-! ## §III. Derived AFA Content

All three fields of AFAStructure are now theorems, derived from the
AbstractSelfApp instance above. No AFA axioms are imported. -/

/-- null is self-containing: the constant-to-null map fixes null. -/
theorem ont_bot_self_mem : selfMemDerived (bot : OntologicalStates) :=
  derived_bot_self_mem

/-- Any two self-containing elements of OntologicalStates are equal. -/
theorem ont_quine_unique (x y : OntologicalStates)
    (hx : selfMemDerived x) (hy : selfMemDerived y) : x = y :=
  derived_quine_unique x y hx hy

/-- The self-containing set has exactly one element: null (= ⊥). DC-free. -/
theorem ont_selfMem_singleton :
    {x : OntologicalStates | selfMemDerived x} = ({bot} : Set OntologicalStates) :=
  selfMem_eq_singleton_bot

end ZeroParadox.OntBridge

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox.OntBridge

#print axioms instOntZPS
#print axioms instOntSelfApp
#print axioms ont_bot_self_mem
#print axioms ont_quine_unique
#print axioms ont_selfMem_singleton

end PurityCheck
