import ZeroParadox.ZPJ_SelfApp
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-!
# ZPJ — Valuation Bridge: Deriving AFA Content from Scale Structure (Exploratory)

## The road surface

ZPJ_SelfApp reduced AFAStructure to AbstractSelfApp (two axioms: fixed_bot, unique_fp).
This file adds the next layer: a ValuationStructure that explains *why* ⊥ is the unique
fixed point — because scale strictly increases valuation, and ⊥ is the unique element
with infinite valuation. unique_fp becomes a theorem, not an axiom.

## The valuation argument

In ℚ_[2]: v₂(2x) = v₂(x) + 1 for x ≠ 0. Scale increases the 2-adic valuation by 1
each step. If 2x = x, then v₂(x) = v₂(x) + 1 — impossible for any finite valuation.
Only 0 has v₂ = ∞, and 2·0 = 0. So the fixed point of ×2 is exactly 0.

In ZPSemilattice: the same argument in the abstract. val : L → ℕ∞, val ⊥ = ⊤,
val strictly increases under scale. Unique fixed point = unique element with val = ⊤ = ⊥.

## What this derives without AFA

  ValuationStructure (scale + val axioms)
    → scale_ne_fixed (scale x ≠ x for x ≠ ⊥)
    → AbstractSelfApp (selfApp = scale, fixed_bot, unique_fp as theorems)
    → AFAStructure (selfMem, bot_self_mem, quine_unique as theorems)

AFA content is derived from the valuation structure — not imported from Aczel.

## What remains open

The ZPSemilattice instance: giving a concrete ZP structure a ValuationStructure
requires identifying the scale operation and val function on that structure. The
Q₂ parallel below shows the p-adic instance satisfies all conditions (val_scale
for Q₂ follows from v₂(2x) = v₂(x) + 1, a standard p-adic result). The formal
instance connecting OntologicalStates or ℤ_[2] to ZPSemilattice remains the
final gap — a bridge file importing both ZPA and ZPB.
-/

namespace ZeroParadox.Scale

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ
open ZeroParadox.SelfApp
open ZeroParadox.AczelConn

/-! ## § I. ValuationStructure — The Abstract Typeclass -/

/-- A ZPSemilattice with a scale operation and valuation satisfying:
      (1) scale fixes ⊥
      (2) val ⊥ = ⊤  (⊥ has infinite valuation)
      (3) val x = ⊤ → x = ⊥  (uniqueness of infinite valuation)
      (4) val (scale x) = val x + 1 for x ≠ ⊥  (scale strictly increases valuation)

    In ℚ_[2]: scale = ×2, val = 2-adic valuation. All four hold.
    In ZPSemilattice: abstract encoding of the same structure. -/
class ValuationStructure (L : Type*) [ZPSemilattice L] where
  scale : L → L
  val        : L → ℕ∞
  scale_bot  : scale bot = bot
  val_bot    : val bot = ⊤
  val_unique : ∀ x : L, val x = ⊤ → x = bot
  val_scale  : ∀ x : L, x ≠ bot → val (scale x) = val x + 1

/-! ## § II. Derived Theorems from ValuationStructure -/

variable {L : Type*} [ZPSemilattice L] [ValuationStructure L]

/-- val x ≠ ⊤ when x ≠ ⊥ — contrapositive of val_unique. -/
theorem val_finite_of_ne_bot (x : L) (hx : x ≠ bot) :
    ValuationStructure.val x ≠ ⊤ :=
  fun h => hx (ValuationStructure.val_unique x h)

/-- scale x ≠ x for x ≠ ⊥.
    Proof: val (scale x) = val x + 1 ≠ val x (since val x is finite). -/
theorem scale_ne_fixed (x : L) (hx : x ≠ bot) :
    ValuationStructure.scale x ≠ x := by
  intro hfp
  have hfin := val_finite_of_ne_bot x hx
  have hval := ValuationStructure.val_scale x hx
  rw [hfp] at hval
  -- hval : val x = val x + 1, but val x ≠ ⊤
  rcases hv : ValuationStructure.val x with _ | n
  · exact hfin hv
  · rw [hv] at hval
    change (n : ℕ∞) = (n : ℕ∞) + 1 at hval
    exact absurd hval.symm (by exact_mod_cast Nat.succ_ne_self n)

/-- ⊥ is the unique fixed point of scale.
    Proof: if scale x = x and x ≠ ⊥, scale_ne_fixed gives a contradiction. -/
theorem scale_unique_fp (x : L) (hfp : ValuationStructure.scale x = x) :
    x = bot := by
  by_contra hne
  exact scale_ne_fixed x hne hfp

/-! ## § III. AbstractSelfApp Instance from ValuationStructure

    selfApp = scale. fixed_bot and unique_fp are now theorems, not axioms. -/

instance toAbstractSelfApp : AbstractSelfApp L where
  selfApp   := ValuationStructure.scale
  fixed_bot := ValuationStructure.scale_bot
  unique_fp := scale_unique_fp

/-! ## § IV. AFAStructure — Full Derivation Chain

    ValuationStructure → AbstractSelfApp → AFAStructure
    All three fields of AFAStructure are now theorems derived from valuation axioms. -/

/-- selfMem derived from ValuationStructure: x is self-containing iff
    it is a fixed point of scale (i.e., scale x = x). -/
def selfMemFromVal (x : L) : Prop :=
  ValuationStructure.scale x = x

/-- ⊥ satisfies selfMemFromVal — derived from scale_bot. -/
theorem val_bot_self_mem : selfMemFromVal (bot : L) :=
  ValuationStructure.scale_bot

/-- selfMemFromVal has a unique witness: ⊥. -/
theorem val_quine_unique (x y : L)
    (hx : selfMemFromVal x) (hy : selfMemFromVal y) : x = y := by
  rw [scale_unique_fp x hx, scale_unique_fp y hy]

/-- {x | selfMemFromVal x} = {⊥} — DC-free. -/
theorem val_selfMem_singleton :
    {x : L | selfMemFromVal x} = ({bot} : Set L) :=
  singleton_from_unique_witness
    selfMemFromVal bot val_bot_self_mem
    (fun x hx => scale_unique_fp x hx)

/-! ## § V. The 2-Adic Parallel — ℤ_[2] Satisfies ValuationStructure Conditions

    ℤ_[2] is not a ZPSemilattice (it is a ring, not a join-semilattice), so it cannot
    be a formal ValuationStructure instance. These standalone theorems show every
    ValuationStructure axiom holds in ℤ_[2] with scale = ×2 and val = 2-adic valuation.

    ℤ_[2] is used (not ℚ_[2]) because PadicInt.valuation : ℤ_[2] → ℕ is ℕ-valued,
    making q2Val_scale provable. In ℚ_[2], valuation : ℚ_[2] → ℤ can be negative,
    and the .toNat truncation makes the key identity false (e.g. x = 2⁻¹).

    The formal connection — a ZPSemilattice instance for a concrete type carrying
    a ValuationStructure — is the remaining open gap. -/

section PadicParallel

noncomputable instance instDecidableEqZ2 : DecidableEq ℤ_[2] := Classical.decEq _

/-- The 2-adic valuation as a function ℤ_[2] → ℕ∞.
    0 maps to ⊤ (infinite valuation); nonzero x maps to its 2-adic valuation.
    PadicInt.valuation : ℤ_[2] → ℕ is ℕ-valued (ℤ_[2] elements always have
    non-negative valuation), so no .toNat truncation is needed and the key
    identity v₂(2x) = v₂(x) + 1 is provable without sorry. -/
noncomputable def q2Val (x : ℤ_[2]) : ℕ∞ :=
  if x = 0 then ⊤ else (x.valuation : ℕ∞)

/-- q2Val 0 = ⊤ — zero has infinite 2-adic valuation. -/
theorem q2Val_bot : q2Val (0 : ℤ_[2]) = ⊤ := by
  simp [q2Val]

/-- q2Val x = ⊤ → x = 0 — only zero has infinite valuation. -/
theorem q2Val_unique (x : ℤ_[2]) (h : q2Val x = ⊤) : x = 0 := by
  simp only [q2Val] at h
  split_ifs at h with hx
  · exact hx
  · simp at h

/-- scale = ×2 fixes 0. -/
theorem q2Scale_bot : (2 : ℤ_[2]) * 0 = 0 := by ring

/-- v₂(2x) = v₂(x) + 1 for x ≠ 0 in ℤ_[2].
    Proof: valuation_mul gives v(2x) = v(2) + v(x); valuation_p gives v(2) = 1.
    Note: valuation_p expects the cast form ((2:ℕ) : ℤ_[2]), so we rewrite the
    numeral (2 : ℤ_[2]) via Nat.cast_ofNat.symm before applying valuation_p. -/
theorem q2Val_scale (x : ℤ_[2]) (hx : x ≠ 0) :
    q2Val (2 * x) = q2Val x + 1 := by
  have h2x : 2 * x ≠ 0 := mul_ne_zero two_ne_zero hx
  simp only [q2Val, if_neg h2x, if_neg hx]
  have key : (2 * x).valuation = x.valuation + 1 := by
    have h1 : (2 * x).valuation = (2 : ℤ_[2]).valuation + x.valuation :=
      PadicInt.valuation_mul two_ne_zero hx
    have h2 : (2 : ℤ_[2]).valuation = 1 := by
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm]
      exact PadicInt.valuation_p
    omega
  exact_mod_cast key

/-- The unique fixed point of ×2 in ℤ_[2] is 0. -/
theorem q2Scale_unique_fp (x : ℤ_[2]) (h : 2 * x = x) : x = 0 := by
  linear_combination h

end PadicParallel

end ZeroParadox.Scale

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.Scale

#print axioms scale_ne_fixed
#print axioms scale_unique_fp
#print axioms toAbstractSelfApp
#print axioms val_bot_self_mem
#print axioms val_quine_unique
#print axioms val_selfMem_singleton
#print axioms q2Val_scale
#print axioms q2Scale_unique_fp

end PurityCheck
