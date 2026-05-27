import ZeroParadox.ZPJ
import ZeroParadox.ZPJ_AczelConn
import Mathlib.Tactic

/-!
# ZPJ — Abstract Self-Application Bridge (Exploratory)

## The question

ZPJ imports three fields from AFA (via AFAStructure):
  `selfMem`, `bot_self_mem`, `quine_unique`

These encode Aczel's AFA content but appear as axioms in the Lean encoding
because the abstract lattice lacks the graph-decoration semantics needed to
derive them. This file asks: can they be derived from something more primitive?

## The fixed-point identification

Two facts from different ZP layers:
  - Set theory (ZPJ / AFA): ⊥ is the unique fixed point of x ↦ {x}
  - 2-adic (ZPB): 0 is the unique fixed point of x ↦ 2x (characterised by v₂ = +∞)

These are the same abstract pattern: the domain's self-application operation has a
unique fixed point, and that fixed point is the "bottom" of the domain. Neither
requires DC — uniqueness collapses construction to identification (ZPJ_AczelConn).

## What this file does

Introduces `AbstractSelfApp`: a typeclass encoding the minimal fixed-point
structure. From it, `selfMem`, `bot_self_mem`, and `quine_unique` are derived
as theorems rather than class fields — reducing AFAStructure's axiom load to a
single structural commitment (selfApp + fixed_bot + unique_fp).

The 2-adic parallel is then proved standalone: `singleton_from_unique_witness`
(already proved in ZPJ_AczelConn) closes the Q₂ case with the same proof term.
Both domains are formally instances of the same abstract pattern.

## What remains open

The formal map connecting the two domains — deriving selfApp on ZPSemilattice
from the p-adic valuative structure — requires an abstract valuation typeclass
not yet defined. That is the remaining ZPB→ZPJ gap. See:
  .claude-local/notes/fixed_point_identification_2026-05-26.md
-/

namespace ZeroParadox.SelfApp

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ
open ZeroParadox.AczelConn

/-! ## § I. AbstractSelfApp Typeclass -/

/-- A ZPSemilattice with a self-application operation whose unique fixed point is ⊥.
    Abstracts the shared structure between:
      Set theory (AFA): f x = {x},  unique fixed point = Quine atom = ⊥
      2-adic integers:  f x = 2 * x, unique fixed point = 0 (v₂ = +∞)
    From these two fields, AFAStructure's three class fields become theorems. -/
class AbstractSelfApp (L : Type*) [ZPSemilattice L] where
  /-- The self-application operation: x ↦ f(x). -/
  selfApp : L → L
  /-- ⊥ is a fixed point of selfApp. -/
  fixed_bot : selfApp bot = bot
  /-- ⊥ is the ONLY fixed point of selfApp. -/
  unique_fp : ∀ x : L, selfApp x = x → x = bot

/-! ## § II. selfMem, bot_self_mem, quine_unique as Derived Theorems -/

variable {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]

/-- selfMem derived from AbstractSelfApp: x is self-containing iff it is
    a fixed point of selfApp. This replaces the AFAStructure class field. -/
def selfMemDerived (x : L) : Prop :=
  AbstractSelfApp.selfApp x = x

/-- ⊥ is self-containing — derived from fixed_bot, not asserted as an axiom. -/
theorem derived_bot_self_mem : selfMemDerived (bot : L) :=
  AbstractSelfApp.fixed_bot

/-- Any two self-containing elements are equal.
    Proof: each equals ⊥ by unique_fp; hence equal to each other. -/
theorem derived_quine_unique (x y : L)
    (hx : selfMemDerived x) (hy : selfMemDerived y) : x = y := by
  have hxbot : x = bot := AbstractSelfApp.unique_fp x hx
  have hybot : y = bot := AbstractSelfApp.unique_fp y hy
  rw [hxbot, hybot]

/-- The set of self-containing elements equals {⊥} — DC-free.
    Uses singleton_from_unique_witness: uniqueness collapses construction
    to identification with no Dependent Choice required. -/
theorem selfMem_eq_singleton_bot :
    {x : L | selfMemDerived x} = ({bot} : Set L) :=
  singleton_from_unique_witness
    selfMemDerived
    bot
    derived_bot_self_mem
    (fun x hx => AbstractSelfApp.unique_fp x hx)

/-! ## § III. AFAStructure Instance from AbstractSelfApp

    Any AbstractSelfApp structure yields an AFAStructure.
    selfMem, bot_self_mem, and quine_unique are now theorems, not axioms. -/

instance toAFAStructure : AFAStructure L where
  selfMem      := selfMemDerived
  bot_self_mem := derived_bot_self_mem
  quine_unique := derived_quine_unique

/-! ## § IV. The 2-Adic Parallel

    The same abstract fixed-point pattern in ℚ_[2]: multiplication by 2
    has 0 as its unique fixed point, characterised by v₂(0) = +∞.

    Note: ℚ_[2] is a field, not a ZPSemilattice — it cannot be an instance
    of AbstractSelfApp. This section proves the parallel as standalone theorems,
    demonstrating that singleton_from_unique_witness closes both cases with the
    same proof structure. -/

section PadicParallel

/-- The self-application in ℚ_[2]: multiplication by 2. -/
noncomputable def q2SelfApp (x : ℚ_[2]) : ℚ_[2] := 2 * x

/-- The fixed-point predicate in ℚ_[2]: x is "self-containing" iff 2x = x. -/
noncomputable def q2SelfMem (x : ℚ_[2]) : Prop := q2SelfApp x = x

/-- 0 ∈ ℚ_[2] is a fixed point of ×2: 2 * 0 = 0. -/
theorem q2_zero_is_fixed : q2SelfMem 0 := by
  simp [q2SelfMem, q2SelfApp]

/-- 0 is the unique fixed point of ×2 in ℚ_[2].
    Proof: 2x = x → x = 0 (one step of ring arithmetic). -/
theorem q2_unique_fp (x : ℚ_[2]) (h : q2SelfMem x) : x = 0 := by
  unfold q2SelfMem q2SelfApp at h
  linear_combination h

/-- The fixed-point set of ×2 in ℚ_[2] is {0} — DC-free.
    Formally parallel to selfMem_eq_singleton_bot: the same
    singleton_from_unique_witness closes both cases. -/
theorem q2_selfMem_singleton :
    {x : ℚ_[2] | q2SelfMem x} = ({0} : Set ℚ_[2]) :=
  singleton_from_unique_witness q2SelfMem 0 q2_zero_is_fixed q2_unique_fp

end PadicParallel

end ZeroParadox.SelfApp

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.SelfApp

#print axioms derived_bot_self_mem
#print axioms derived_quine_unique
#print axioms selfMem_eq_singleton_bot
#print axioms toAFAStructure
#print axioms q2_zero_is_fixed
#print axioms q2_unique_fp
#print axioms q2_selfMem_singleton

end PurityCheck
