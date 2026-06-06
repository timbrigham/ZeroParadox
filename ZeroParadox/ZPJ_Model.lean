import ZeroParadox.ZPJ_Scale
import Mathlib.Tactic

/-!
# ZPJ_Model — Concrete ValuationStructure Instance: (ℕ∞, min, ⊤)

## Engineer's Take

The abstract machine in ZPJ_Scale proves that *if* a type has a scale operation with
the right valuation behaviour, *then* AFA content follows. This file builds the type
that has that behaviour. The concrete carrier is ℕ∞ = WithTop ℕ — the extended naturals
— where the join operation is min, the bottom element is ⊤ (the natural maximum), and
scale is just add-one. ⊤ + 1 = ⊤ in WithTop ℕ, so ⊤ is the unique fixed point.
Everything else is provable by arithmetic.

## The model

ℕ∞ with join = min and bot = ⊤ satisfies ZPSemilattice:

  - A1–A3: min is associative, commutative, idempotent
  - A4: min ⊤ x = x because ⊤ is the maximum, so x ≤ ⊤ for all x

With scale = (· + 1) and val = id, ValuationStructure holds:

  - scale_bot: ⊤ + 1 = ⊤   (WithTop.top_add)
  - val_bot:   id ⊤ = ⊤     (trivial)
  - val_unique: id x = ⊤ → x = ⊤   (trivial)
  - val_scale: x ≠ ⊤ → id (x + 1) = id x + 1   (rfl)

The induced ZP order reverses ℕ∞'s natural order: x ≤_ZP y iff min x y = y iff x ≥ y.
So ⊤ is the ZP-bottom (valuation ∞, unique fixed point), and 0 is the ZP-maximum
(valuation 0, the fully constrained state).

## The indexed-family picture

The abstract gap in ZPJ_Scale asked for an infinite domain where scale can increase
valuation without bound. ℕ∞ resolves this: each n : ℕ is a level with val n = n,
scale shifts n to n + 1, and ⊤ is the limit point that all sequences converge to.
The "indexed family (L₀, L₁, L₂, ...)" is just this structure with each Lₙ = {n, ⊤}.

## What this delivers

The full derivation chain now has a concrete model:

  (ℕ∞, min, ⊤) : ZPSemilattice
    + ValuationStructure (scale = +1, val = id)
    → AbstractSelfApp (via ZPJ_Scale.toAbstractSelfApp)
    → AFA content: natInf_selfMem_singleton = {⊤}

All results are sorry-free and derived from ℕ∞ arithmetic + ZPJ_Scale theorems.
-/

namespace ZeroParadox.Model

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.Scale

/-! ## § I. ZPSemilattice Instance for ℕ∞ -/

/-- ℕ∞ with join = min and bot = ⊤ is a ZPSemilattice.
    The ZP partial order (x ≤_ZP y ↔ min x y = y) reverses ℕ∞'s natural ordering. -/
-- [ZP-CUSTOM] instance: ZPSemilattice ℕ∞ with inverted order | reason: Mathlib's WithTop ℕ has ≤ as its standard order (⊤ is maximum). Here join = min and bot = ⊤ — a deliberate reversal. The ZP partial order x ≤_ZP y ↔ min x y = y makes ⊤ the bottom (valuation ∞) and 0 the maximum (fully constrained). No Mathlib instance covers this inverted reading.
noncomputable instance instNatInfZPS : ZPSemilattice ℕ∞ where
  join       := min
  bot        := ⊤
  join_assoc := min_assoc
  join_comm  := min_comm
  join_idem  := min_self
  bot_join   := fun _ => min_eq_right le_top

/-! ## § II. ValuationStructure Instance for ℕ∞ -/

/-- ℕ∞ carries a ValuationStructure with scale = (· + 1) and val = id.
    All four axioms reduce to one-line ℕ∞ arithmetic. -/
-- [ZP-CUSTOM] instance: ValuationStructure ℕ∞ (scale = +1, val = id) | reason: The concrete model witnessing that ValuationStructure's abstract gap (a type satisfying all four axioms) has an actual inhabitant. val = id works because ℕ∞ already carries its own depth as its value; scale = +1 satisfies val_scale by rfl.
noncomputable instance instNatInfVal : ValuationStructure ℕ∞ where
  scale      := fun x => x + 1
  val        := id
  scale_bot  := WithTop.top_add 1
  val_bot    := rfl
  val_unique := fun _x hx => hx
  val_scale  := fun _x _hx => rfl

/-! ## § III. Derived AFA Content -/

/-- The unique fixed point of (· + 1) in ℕ∞ is ⊤. -/
theorem natInf_scale_unique_fp (x : ℕ∞) (h : x + 1 = x) : x = ⊤ :=
  scale_unique_fp x h

/-- {x : ℕ∞ | x + 1 = x} = {⊤}. -/
theorem natInf_selfMem_singleton :
    {x : ℕ∞ | x + 1 = x} = ({⊤} : Set ℕ∞) :=
  val_selfMem_singleton

end ZeroParadox.Model

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.Model

#print axioms instNatInfZPS
#print axioms instNatInfVal
#print axioms natInf_scale_unique_fp
#print axioms natInf_selfMem_singleton

end PurityCheck
