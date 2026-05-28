import ZeroParadox.ZPJ_Scale
import Mathlib.Tactic

/-!
# ZPJ — Scale Bridge: AFA Content from Valuation Without ZPSemilattice (Exploratory)

## Engineer's Take

-- TODO: Tim fills this in

## The question

ZPJ_Scale defines ValuationStructure over `[ZPSemilattice L]`, but the four
axioms (scale_bot, val_bot, val_unique, val_scale) only ever use `bot` — the
join operation ⊔ never appears. This means ZPSemilattice is an over-strong
constraint, and ℤ_[2] cannot be a formal ValuationStructure instance despite
satisfying all four axioms (proved as standalone theorems in ZPJ_Scale §V).

This file tests the conjecture that the constraint is an encoding artefact, not
a mathematical gap. It defines ValBridge — the same four axioms with `bot` as a
plain field rather than a ZPSemilattice bottom — and builds a formal ℤ_[2]
instance using the theorems already proved in ZPJ_Scale.

If the instance builds and the AFA content chain follows, the formal bridge is
complete: ℤ_[2] provably carries AFA content as a theorem of ZFC, not an
import from Aczel.

## The chain

  ValBridge (scale + val axioms, bot as plain field)
    → scale_ne_fixed_free
    → scale_unique_fp_free
    → selfMem_eq_singleton_free  ({x | scale x = x} = {bot})

This is the same chain as ZPJ_Scale §II–IV, without the ZPSemilattice dependency.
-/

namespace ZeroParadox.ScaleBridge

open ZeroParadox.Scale

/-! ## § I. ValBridge — The Unconstrained Typeclass -/

/-- Same four axioms as ValuationStructure, but `bot` is a plain field.
    No ZPSemilattice required — the join operation ⊔ never appears in any axiom. -/
-- [ZP-CUSTOM] replaces: ValuationStructure (ZPJ_Scale) | reason: ValuationStructure required [ZPSemilattice L] but the join operation ⊔ never appears in any of its four axioms — the constraint was an encoding artefact. ValBridge carries the same four axioms with bot as a plain field, allowing ℤ_[2] (a ring, not a ZPSemilattice) to be a formal instance. Unifies both tracks under one ancestor.
class ValBridge (L : Type*) where
  bot : L
  scale : L → L
  val : L → ℕ∞
  scale_bot : scale bot = bot
  val_bot : val bot = ⊤
  val_unique : ∀ x : L, val x = ⊤ → x = bot
  val_scale : ∀ x : L, x ≠ bot → val (scale x) = val x + 1

/-! ## § II. Derived Theorems — Same Proofs, No ZPSemilattice -/

variable {L : Type*} [ValBridge L]

/-- val x ≠ ⊤ when x ≠ bot — contrapositive of val_unique. -/
theorem val_finite_free (x : L) (hx : x ≠ ValBridge.bot) : ValBridge.val x ≠ ⊤ :=
  fun h => hx (ValBridge.val_unique x h)

/-- scale x ≠ x for x ≠ bot.
    Proof: val (scale x) = val x + 1 ≠ val x (since val x is finite). -/
theorem scale_ne_fixed_free (x : L) (hx : x ≠ ValBridge.bot) : ValBridge.scale x ≠ x := by
  intro hfp
  have hfin := val_finite_free x hx
  have hval := ValBridge.val_scale x hx
  rw [hfp] at hval
  rcases hv : ValBridge.val x with _ | n
  · exact hfin hv
  · rw [hv] at hval
    change (n : ℕ∞) = (n : ℕ∞) + 1 at hval
    exact absurd hval.symm (by exact_mod_cast Nat.succ_ne_self n)

/-- ValBridge.bot is the unique fixed point of scale. -/
theorem scale_unique_fp_free (x : L) (hfp : ValBridge.scale x = x) : x = ValBridge.bot := by
  by_contra hne
  exact scale_ne_fixed_free x hne hfp

/-- {x | scale x = x} = {bot} — the AFA uniqueness content, DC-free. -/
theorem selfMem_eq_singleton_free :
    {x : L | ValBridge.scale x = x} = ({ValBridge.bot} : Set L) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  exact ⟨fun h => scale_unique_fp_free x h, fun h => h ▸ ValBridge.scale_bot⟩

/-! ## § III. ℤ_[2] Instance — The Formal Bridge -/

/-- ℤ_[2] with scale = ×2 and val = v₂ is a ValBridge.
    bot = 0. All four axioms proved in ZPJ_Scale §V as standalone theorems.
    This is the formal instance that ZPJ_Scale could not build because
    ℤ_[2] is not a ZPSemilattice — showing the ZPSemilattice constraint
    was an encoding artefact, not a mathematical requirement. -/
-- [ZP-CUSTOM] instance: ValBridge ℤ_[2] | reason: ℤ_[2] is a ring — it cannot be a ZPSemilattice instance and could not satisfy ValuationStructure. ValBridge's bot-as-plain-field design makes this instance possible. All four axioms delegate directly to theorems proved in ZPJ_Scale §V (q2Scale_bot, q2Val_bot, q2Val_unique, q2Val_scale).
noncomputable instance instZ2ValBridge : ValBridge ℤ_[2] where
  bot := 0
  scale := (2 * ·)
  val := q2Val
  scale_bot := q2Scale_bot
  val_bot := q2Val_bot
  val_unique := q2Val_unique
  val_scale := q2Val_scale

/-! ## § IV. AFA Content for ℤ_[2] — The Closed Bridge -/

/-- The unique fixed point of ×2 in ℤ_[2] is 0.
    Formal consequence of ValBridge; no sorry, no ZPSemilattice. -/
theorem z2_scale_unique_fp (x : ℤ_[2]) (h : 2 * x = x) : x = 0 :=
  scale_unique_fp_free x h

/-- {x : ℤ_[2] | 2 * x = x} = {0} — AFA self-membership content in ℤ_[2].
    A theorem of ZFC (via Mathlib's p-adic library). No AFA import. -/
theorem z2_selfMem_singleton :
    {x : ℤ_[2] | 2 * x = x} = ({0} : Set ℤ_[2]) :=
  selfMem_eq_singleton_free

/-! ## § V. Unification — ZPSemilattice+ValuationStructure is a ValBridge

    Any type carrying both ZPSemilattice and ValuationStructure satisfies ValBridge.
    Combined with the ℤ_[2] instance above, this makes ValBridge the common ancestor:
    both tracks are now instances of one structure, not parallel analogies.

    Consequence: every ValBridge theorem (scale_unique_fp_free, selfMem_eq_singleton_free,
    etc.) applies uniformly to abstract ZP semilattice types AND to ℤ_[2] — a single
    proof serves both. -/

/-- Any ZPSemilattice with a ValuationStructure is a ValBridge.
    Proof: all four fields come directly from ZPSemilattice.bot and ValuationStructure. -/
instance toValBridge (L : Type*) [ZeroParadox.ZPA.ZPSemilattice L]
    [ValuationStructure L] : ValBridge L where
  bot := ZeroParadox.ZPA.ZPSemilattice.bot
  scale := ValuationStructure.scale
  val := ValuationStructure.val
  scale_bot := ValuationStructure.scale_bot
  val_bot := ValuationStructure.val_bot
  val_unique := ValuationStructure.val_unique
  val_scale := ValuationStructure.val_scale

/-- Both tracks produce the same singleton theorem via a single ValBridge proof.
    For any ZPSemilattice L with ValuationStructure: {x | scale x = x} = {bot}. -/
theorem zp_selfMem_singleton (L : Type*) [ZeroParadox.ZPA.ZPSemilattice L]
    [ValuationStructure L] :
    {x : L | ValuationStructure.scale x = x} =
      ({ZeroParadox.ZPA.ZPSemilattice.bot} : Set L) :=
  selfMem_eq_singleton_free

end ZeroParadox.ScaleBridge

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ScaleBridge

#print axioms scale_ne_fixed_free
#print axioms scale_unique_fp_free
#print axioms selfMem_eq_singleton_free
#print axioms z2_scale_unique_fp
#print axioms z2_selfMem_singleton
#print axioms toValBridge
#print axioms zp_selfMem_singleton

end PurityCheck
