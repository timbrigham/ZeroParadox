import ZeroParadox.Valuation.Padic
import ZeroParadox.Computability.SelfApp
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZPJ — OntologicalStates → AbstractSelfApp → AFA Content

## Engineer's Take

ZPJ_Scale proved the full derivation chain ValuationStructure → AbstractSelfApp → AFA
content, and ZPJ_Model gave ℕ∞ as the concrete ValuationStructure instance. That chain
requires an infinite domain: the val_scale axiom (val(scale x) = val x + 1) has no room
to operate in a two-element type.

*(Editor's note, outside the Take: the Take above says "ZPJ_Scale" and "ZPJ_Model", pre-reorg module
names that resolve to nothing at HEAD — they are now `ZeroParadox/Valuation/Scale.lean` and
`ZeroParadox/Settheory/Model.lean`. **The Take is Tim's voice and is left exactly as written**; a
mechanical path sweep rewrote it on 2026-08-02 and was reverted. Only Tim edits a Take, so the pointer
lives here instead.)*

OntologicalStates — ZPB's {null, exist} — admits no ValuationStructure. The Take's CONCLUSION
is right and its MECHANISM is not: the axioms JOINTLY force the scale orbit to embed ℕ and so
force the CARRIER infinite — not because val lacks room, its codomain ℕ∞ being unbounded.
Proved by valuationStructure_forces_infinite (ZeroParadox/Valuation/ScaleBridge.lean § VI). ⚠ The
obstruction is JOINT, not val_scale alone — val_scale by itself holds on two elements
(val everywhere infinity, scale the identity); it is val_unique that then fails. And it can
be an AbstractSelfApp instance directly. The self-application operation is the
constant-to-null function: every element maps to null. This makes null the unique fixed
point — the only element that maps to itself — which is all AbstractSelfApp requires.
AFA content follows immediately.

This is the shorter on-ramp. ℕ∞ takes the full ValuationStructure path. OntologicalStates
takes the direct AbstractSelfApp path. Both end at the same AFA content.

Result: null is the unique self-containing element of OntologicalStates — formally proved
in Lean, from ZPB structure alone, without importing any AFA axioms.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox
open ZeroParadox

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
-- [ZP-CUSTOM] instance: AbstractSelfApp OntologicalStates via constant-to-null | reason: OntologicalStates (two elements) admits no ValuationStructure — no_valBridge_of_finite (ZeroParadox/Valuation/ScaleBridge.lean § VI) proves no finite carrier with two or more points does, because the axioms JOINTLY force the scale orbit to embed ℕ and so force the CARRIER infinite. ⚠ Not because val lacks room: its codomain ℕ∞ is unbounded, and val_scale alone is satisfiable on two elements. Direct AbstractSelfApp instance using the constant-to-null map (every element → null) is the shorter path to AFA content for finite types.
instance instOntSelfApp : AbstractSelfApp OntologicalStates where
  selfApp   := fun _ => .null
  fixed_bot := rfl
  unique_fp := by
    intro x hx
    cases x with
    | null  => rfl
    | exist => exact absurd hx (by decide)

/-! ## §III. Derived AFA Content

AFAStructure's two LAWS — `bot_self_mem` and `quine_unique` — are now theorems, derived
from the AbstractSelfApp instance above. Its `selfMem` field is DATA, supplied by
`def selfMemDerived`, not proved. No AFA axioms are imported. -/

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

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms instOntZPS
#print axioms instOntSelfApp
#print axioms ont_bot_self_mem
#print axioms ont_quine_unique
#print axioms ont_selfMem_singleton

end PurityCheck
