import ZeroParadox.Computability.SelfApp
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-!
# ZPJ — Valuation Bridge: Deriving AFA Content from Scale Structure

## Engineer's Take

A ZP-J valuation-bridge sub-file. See the Engineer's Take in `ZeroParadox/Settheory/SetTheoryAFA.lean`.

---

## The road surface

ZeroParadox/Computability/SelfApp.lean reduced AFAStructure to AbstractSelfApp (two axioms: fixed_bot, unique_fp).
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

## What ZeroParadox/Valuation/ScaleBridge.lean resolved

The ZPSemilattice constraint was an encoding artefact: ValuationStructure required
[ZPSemilattice L] but the join operation ⊔ never appears in any of its four axioms.
ZeroParadox/Valuation/ScaleBridge.lean resolves this by defining ValBridge — the same four axioms
with bot as a plain field — and builds a formal ℤ_[2] instance using the standalone
theorems in §V below. A toValBridge instance makes any ZPSemilattice+ValuationStructure
type also a ValBridge instance, unifying both tracks under a common ancestor.
The formal gap described here is closed.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox
open ZeroParadox
open ZeroParadox

/-! ## § I. ValuationStructure — The Abstract Typeclass -/

/-- A ZPSemilattice with a scale operation and valuation satisfying:
      (1) scale fixes ⊥
      (2) val ⊥ = ⊤  (⊥ has infinite valuation)
      (3) val x = ⊤ → x = ⊥  (uniqueness of infinite valuation)
      (4) val (scale x) = val x + 1 for x ≠ ⊥  (scale strictly increases valuation)

    In ℚ_[2]: scale = ×2, val = 2-adic valuation. All four hold.
    In ZPSemilattice: abstract encoding of the same structure. -/
-- [ZP-CUSTOM] replaces: Mathlib.RingTheory.Valuation.Valued | reason: Mathlib's Valued typeclass requires ring/field structure (it formalizes algebraic valuations over rings). ZPSemilattice has join only — no ring. ValuationStructure uses val : L → ℕ∞ (not a GroupWithZero target) and the single axiom val_scale (val strictly increases under scale), which is the only machinery needed for the fixed-point uniqueness argument.
class ValuationStructure (L : Type*) [ZPSemilattice L] where
  scale : L → L
  val        : L → ℕ∞
  scale_bot  : scale bot = bot
  val_bot    : val bot = ⊤
  val_unique : ∀ x : L, val x = ⊤ → x = bot
  val_scale  : ∀ x : L, x ≠ bot → val (scale x) = val x + 1

/-! ### NO-GO gauge for this class — proved in the sibling file, and sharp here too

    What FAILS to be a `ValuationStructure`: every carrier with a point other than `bot` is forced
    INFINITE, so no finite carrier with two or more points admits one. The gauge is proved once for
    `ValBridge` and reaches this class through the `toValBridge` instance of
    ZeroParadox/Valuation/ScaleBridge.lean § V — `valuationStructure_forces_infinite`.

    ⚠ **Only the FORCING half transfers through `toValBridge`**, which runs
    `ValuationStructure ⇒ ValBridge`: it carries obstructions INTO this class and cannot carry a
    membership witness back, so `trivialValBridge` inhabits `ValBridge Unit` and says nothing about
    this class. Sharpness is therefore established HERE, by exhibiting the degenerate carrier
    directly — `trivialZPSemilattice` and `trivialValuationStructure` below. The one-point carrier
    satisfies the semilattice equations and all four valuation axioms, the latter because
    `val_scale`'s `x ≠ bot` guard is vacuous on a subsingleton. **The bound is sharp for this class
    as well:** `Unit` is a finite member, and every member with a second point is infinite.

    Neither witness is registered as a global instance, so neither can leak into instance resolution
    elsewhere — the pattern `trivialValBridge` already follows in the sibling file. Full statement
    and proof of the gauge: ZeroParadox/Valuation/ScaleBridge.lean § VI. -/

section DegenerateWitness

/-- The one-point semilattice. A `def`, not an `instance`. -/
@[reducible] def trivialZPSemilattice : ZPSemilattice Unit where
  join := fun _ _ => ()
  bot := ()
  join_assoc := fun _ _ _ => rfl
  join_comm := fun _ _ => rfl
  join_idem := fun _ => rfl
  bot_join := fun _ => rfl

attribute [local instance] trivialZPSemilattice

/-- **The degenerate member, which makes the gauge's bound sharp for this class.** `val_scale` is
    guarded by `x ≠ bot`, and no point of `Unit` clears the guard. -/
@[reducible] noncomputable def trivialValuationStructure : ValuationStructure Unit where
  scale := id
  val := fun _ => ⊤
  scale_bot := rfl
  val_bot := rfl
  val_unique := fun x _ => Subsingleton.elim x _
  val_scale := fun x hx => absurd (Subsingleton.elim x _) hx

end DegenerateWitness

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
    AFAStructure's two LAWS are now theorems derived from valuation axioms. ⚠ This file
    declares only the `AbstractSelfApp` instance; the `AFAStructure` itself arrives
    generically from `ZeroParadox/Computability/SelfApp.lean`'s `toAFAStructure`, whose
    `selfMem` is DATA supplied by `def selfMemDerived`. `selfMemFromVal` below is this
    file's own predicate for the valuation-side theorems — definitionally that same
    predicate under `selfApp := scale`, not a second binding of the field. -/

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

    No `ZPSemilattice ℤ_[2]` is defined — its ring structure supplies no natural join with 0 as
    bottom — so ℤ_[2] cannot be a formal ValuationStructure instance, which requires one. ⚠ Being a
    ring is not itself the obstruction: no ZPSemilattice axiom mentions a ring operation, and
    `ZPSemilattice ℕ` exists. These standalone theorems show every ValuationStructure axiom holds in
    ℤ_[2] with scale = ×2 and val = 2-adic valuation.

    ℤ_[2] is used (not ℚ_[2]) because PadicInt.valuation : ℤ_[2] → ℕ is ℕ-valued,
    making q2Val_scale provable. In ℚ_[2], valuation : ℚ_[2] → ℤ can be negative,
    and the .toNat truncation makes the key identity false (e.g. x = 2⁻¹).

    The formal connection — a ZPSemilattice instance for a concrete type carrying
    a ValuationStructure — is the remaining open gap. -/

/-! ⚠⚠ **THE PARAGRAPH ABOVE IS OUT OF DATE, AND §V's ℤ_[2] SENTENCE IS FALSE.** ℕ∞ carries
    BOTH structures — `instNatInfZPS` and `instNatInfVal` in `ZeroParadox/Settheory/Model.lean`,
    which IMPORTS this file. §V also says ℤ_[2] "cannot be a formal ValuationStructure
    instance"; the example below SUPPLIES a semilattice with bottom 0 and discharges all four
    axioms over it (end of § V, where its inputs are in scope). No `ZPSemilattice ℤ_[2]`
    INSTANCE is registered, so the bare expression fails synthesis — a fact about the
    instance database, never about existence.
    Both stale sentences stay only because their block is frozen by content hash; the route
    out is a `/claim-review` debaseline. -/

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

/-- Statement: ℤ_[2] DOES admit a `ValuationStructure`, once a semilattice is supplied. The join
    is free — the four axioms mention only `bot` and never the join — so any associative,
    commutative, idempotent operation with 0 as its identity serves. ⚠ Choice-dependent: it
    well-orders the carrier. That adds NO new axiom, since `q2Val_unique` and `q2Val_scale`
    below already carry `Classical.choice`. A choice-free join is not ruled out; none is built
    here. -/
example : ∃ h : ZPSemilattice ℤ_[2], Nonempty (@ValuationStructure ℤ_[2] h) := by
  classical
  letI : LinearOrder ℤ_[2] := IsWellOrder.linearOrder (WellOrderingRel (α := ℤ_[2]))
  letI SL : ZPSemilattice ℤ_[2] :=
    { join := fun x y => if x = 0 then y else if y = 0 then x else max x y
      bot := 0
      join_assoc := by
        intro x y z
        by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hz : z = 0 <;> simp_all
        have hxy : max x y ≠ 0 := by rcases max_choice x y with h | h <;> simp_all
        have hyz : max y z ≠ 0 := by rcases max_choice y z with h | h <;> simp_all
        simp [hxy, hyz, max_assoc]
      join_comm := by
        intro x y
        by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp_all [max_comm]
      join_idem := by
        intro x
        by_cases hx : x = 0 <;> simp_all
      bot_join := by intro x; simp }
  have hbot : (ZPSemilattice.bot : ℤ_[2]) = 0 := rfl
  exact ⟨SL, ⟨{ scale := (2 * ·)
              , val := q2Val
              , scale_bot := by rw [hbot]; exact q2Scale_bot
              , val_bot := by rw [hbot]; exact q2Val_bot
              , val_unique := by intro x hx; rw [hbot]; exact q2Val_unique x hx
              , val_scale := by intro x hx; rw [hbot] at hx; exact q2Val_scale x hx }⟩⟩

end PadicParallel

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms scale_ne_fixed
#print axioms scale_unique_fp
#print axioms toAbstractSelfApp
#print axioms val_bot_self_mem
#print axioms val_quine_unique
#print axioms val_selfMem_singleton
#print axioms q2Val_scale
#print axioms q2Scale_unique_fp

-- The degenerate witnesses making the NO-GO gauge's bound sharp for this class.
#print axioms trivialZPSemilattice
#print axioms trivialValuationStructure

end PurityCheck
