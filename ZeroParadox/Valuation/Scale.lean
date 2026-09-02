import ZeroParadox.Computability.SelfApp
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic

/-!
# ZPJ — Valuation Bridge: Deriving AFA Content from Scale Structure

## Engineer's Take

A ZP-J valuation-bridge sub-file. See the Engineer's Take in `ZeroParadox/Settheory/SetTheoryAFA.lean`.

## Formal Overview
`val_unique` and `val_scale` carry the unique-fixed-point argument; WITHIN § I `val_bot` is consumed nowhere
on it (measured 2026-08-30, § I). § V proves all four axioms in ℤ_[2]. Road surface, valuation
argument, derivation chain, § V's synthesis fence, what ScaleBridge resolved: the ride-along
`ZeroParadox/Valuation/Scale.md`, beside this file.
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
-- [ZP-CUSTOM] replaces: Valued (Mathlib/Topology/Algebra/Valued/ValuationTopology.lean) | reason: Mathlib's Valued typeclass requires ring/field structure (it formalizes algebraic valuations over rings). ZPSemilattice has join only — no ring. ValuationStructure uses val : L → ℕ∞ (not a GroupWithZero target) and four axioms (§ I lists them). The fixed-point uniqueness argument consumes TWO of them — val_unique and val_scale; scale_bot and val_bot appear in none of the three proof terms on that chain, measured 2026-08-30. ⚠ val_scale alone does NOT suffice, measured 2026-08-30: on Bool with bot = false, scale = id and val everywhere ⊤, scale_bot/val_bot/val_scale all hold and true is a fixed point of scale that is not the bottom. val_unique supplies the FINITENESS that makes val_scale bite. ⚠ THE NEARER NEIGHBOUR IS `AddValuation`, NOT `Valued`, and this reason answered the wrong one until 2026-09-01: `AddValuation R ℕ∞` targets a `LinearOrderedAddCommMonoidWithTop`, which is exactly this class's target, so "not a `GroupWithZero` target" rebuts `Valuation` and says nothing about it. The real discriminator is the CARRIER: `AddValuation` requires `[Ring R]` and a `ZPSemilattice` has only a join — the same discriminator `ZeroParadox/Algebra/Wheel.lean` recorded for `AddValuation A ℕ∞` on 2026-08-01, which this tag had not picked up. ⚠ `AddValuation.top_iff` IS NOT THE NAME FOR THE `val_bot` + `val_unique` PAIR HERE, and this tag said it was until 2026-09-01: `top_iff` is stated over a `[DivisionRing K]` (Mathlib/RingTheory/Valuation/Basic.lean:71, and its own docstring says "on a division ring"), and ℤ_[2] is a DVR, not a division ring — 2 is not invertible. On ℤ_[2] the stock route to `val_unique` is `emultiplicity_eq_top` together with `FiniteMultiplicity.of_prime_left`: x ≠ 0 with 2 prime gives finite multiplicity, hence val x ≠ ⊤. Found by both prose gates independently, one of which compiled the failure. ⚠ On a RING carrier there is no gap at all: `multiplicity_addValuation PadicInt.prime_p` discharges all four axioms on ℤ_[2] from stock API with an unguarded `val_scale` — see § V.
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

    All four axioms hold in ℤ_[2] (scale = ×2, val = the 2-adic valuation), proved below as
    standalone theorems; the closing example supplies a `ZPSemilattice ℤ_[2]` and discharges
    every axiom over it. ⭐ PRIOR ART — these theorems DUPLICATE it:
    `multiplicity_addValuation PadicInt.prime_p : AddValuation ℤ_[2] ℕ∞` discharges all four
    from stock Mathlib at the same axiom footprint, its `val_scale` STRICTLY STRONGER (unguarded,
    holding at 0 as well). The ℕ∞-target rationale, the classical names, the neighbour
    `BottomValuation`, and the synthesis fence are in `ZeroParadox/Valuation/Scale.md` § V. -/

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

-- `linter.flexible` fires on the `simp_all`s in the proof below: a STYLE lint about a tactic
-- that modifies the goal, not a soundness warning. Suppressed rather than replaced, because the
-- replacement is a hand-written simp set and a guessed lemma list is how this proof broke once.
set_option linter.flexible false in
/-- Statement: ℤ_[2] DOES admit a `ValuationStructure`, once a semilattice is supplied. The join
    is free — the four axioms mention only `bot` and never the join — so any associative,
    commutative, idempotent operation with 0 as its identity serves. ⚠ It adds NO new axiom:
    `q2Val_unique` and `q2Val_scale` above already carry `Classical.choice`. ⚠⚠ **The CARRIER is
    the source, it subsumes every other, and it CLOSES the question.** `ZPSemilattice ℤ_[2]` is
    choice-tainted AS A TYPE. `#print axioms` walks a declaration's TYPE as well as its term, so
    `PadicInt` carrying choice (emitted below) taints every declaration whose type mentions
    ℤ_[2] — including any semilattice on it. So a choice-free join here is ruled out for every
    spelling of the join ON THIS TYPE, under the `#print axioms` metric; whether a constructively
    re-founded 2-adic type would change the question is separate and not addressed. ⚠ `ZPSemilattice`
    itself is clean — it is this carrier, not that class. `PadicInt` is the evidence and
    `q2Scale_bot` is the consequence — a theorem with no ℕ∞ and no equality test
    in it, tainted anyway. ⚠ The class's own
    numeral is a SEPARATE cost, and an ACCIDENTAL one in the sense
    `ZeroParadox/Category/ChoiceCannotBe.lean` defines and sources: respelling the successor as a
    cast from ℕ clears the class outright. ⚠ Two INDEPENDENT reasons to read the numeral half as
    pin-relative: Brasca and Clemente (arXiv:2603.17457, §2.2) record the same `OfNat` route being
    tainted and then repaired upstream, and `ZeroParadox/Valuation/PricedPadicInterface.lean` § I
    dates its own measurements for that reason. The CARRIER half is not pin-relative in the same
    way — it follows from the printer walking the TYPE, so it holds of any statement mentioning
    `ℤ_[2]` for as long as `PadicInt` is built with choice. ⚠ The two counterfactual PAIRS below emit exactly that — carrier,
    then numeral. ⚠ The UNIVERSALS here (any lawful join serves; ruled out for every spelling)
    are not emitted and cannot be — a footprint list settles instances, never universals. The
    printer's own type-walk IS emitted, by `_trivialAboutZ2` / `_trivialAboutNat` below. -/
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
-- ⭐ THE PRINTER'S TYPE-WALK, EMITTED. Both are proved by `rfl` and neither TERM contains any
-- 2-adic content; the only difference is a binder TYPE. So the choice in the first can have come
-- from nowhere but the type walk, which is the mechanism this whole block relies on.
private theorem _trivialAboutZ2 : ∀ _ : ℤ_[2], (0 : ℕ) = 0 := fun _ => rfl
private theorem _trivialAboutNat : ∀ _ : ℕ, (0 : ℕ) = 0 := fun _ => rfl
#print axioms _trivialAboutZ2
#print axioms _trivialAboutNat

-- The CARRIER, and a theorem whose only ZP-specific content is the carrier. `PadicInt` is the
-- evidence; `q2Scale_bot` is the consequence. Together they are why every ℤ_[2] footprint below
-- is choice-tainted regardless of join, valuation or numeral.
#print axioms PadicInt
#print axioms q2Scale_bot
#print axioms q2Val
#print axioms instDecidableEqZ2
#print axioms q2Val_unique
#print axioms q2Val_scale
-- ⭐ THE COUNTERFACTUALS. Two minimal pairs, each varying exactly one thing, so the attribution
-- is checkable rather than argued.
-- ⚠ `tools/verify/check_classes.py` does NOT audit the two classes below: its `DECL` regex
-- admits only whitespace or an attribute before `class`, so a leading `private` blocks the match.
-- Searched 2026-08-30 (`private` followed by `class`/`structure` over `ZeroParadox/**/*.lean`,
-- and that checker's own regex run over this file): these two are the only such declarations
-- located. They are purity probes, never requirements classes, and NEITHER IS REGISTERED AS AN
-- `instance`, so neither can reach instance resolution. ⚠ That exemption is an artifact of a
-- regex rather than a decision, and the decision belongs to `/rely`, which owns `tools/verify`.
-- Carrier, not class: same class, two carriers, opposite answers.
private def _zpsZ2 : Type := ZPSemilattice ℤ_[2]
private def _zpsN : Type := ZPSemilattice ℕ
-- Numeral, and ACCIDENTAL: `ValuationStructure`'s six fields transcribed TWICE (§ I), differing
-- only in how the successor is spelled. Stated at the class, not at a bare ℕ∞ value, because
-- that is the level the claim is about.
private class _VSlit (L : Type*) [ZPSemilattice L] where
  scale : L → L
  val : L → ℕ∞
  scale_bot : scale ZPSemilattice.bot = ZPSemilattice.bot
  val_bot : val ZPSemilattice.bot = ⊤
  val_unique : ∀ x : L, val x = ⊤ → x = ZPSemilattice.bot
  val_scale : ∀ x : L, x ≠ ZPSemilattice.bot → val (scale x) = val x + 1
private class _VScast (L : Type*) [ZPSemilattice L] where
  scale : L → L
  val : L → ℕ∞
  scale_bot : scale ZPSemilattice.bot = ZPSemilattice.bot
  val_bot : val ZPSemilattice.bot = ⊤
  val_unique : ∀ x : L, val x = ⊤ → x = ZPSemilattice.bot
  val_scale : ∀ x : L, x ≠ ZPSemilattice.bot → val (scale x) = val x + ((1 : ℕ) : ℕ∞)
-- ⚠ `_VSlit` and `_VScast` hand-transcribe `ValuationStructure`'s six fields (§ I). The examples
-- below map each pair BOTH WAYS, so a field added WITHOUT A DEFAULT, dropped, or renamed
-- anywhere in the three breaks the build. Both directions are needed: one catches a field lost,
-- the other a field gained. ⚠⚠ TWO THINGS THEY CANNOT CATCH, both measured 2026-08-30:
--   (1) a field added WITH a default -- build green, both guards silent, footprints unchanged,
--       and the transcription is then short by one field;
--   (2) a field RETYPED to something DEFEQ -- respelling the canonical `val_scale` as
--       `+ ((1 : ℕ) : ℕ∞)` elaborates through every example unchanged, exit 0, while the
--       footprints flip. Elaboration preserves definitional equality; `#print axioms` does not,
--       and that difference is precisely what this block measures.
-- So build-breaks implies the field lists diverged; build-passes does NOT imply they agree.
-- Anonymous, so nothing is owed.
example {L : Type*} [ZPSemilattice L] (v : ValuationStructure L) : _VSlit L :=
  { scale := v.scale, val := v.val, scale_bot := v.scale_bot, val_bot := v.val_bot,
    val_unique := v.val_unique, val_scale := v.val_scale }
example {L : Type*} [ZPSemilattice L] (w : _VSlit L) : ValuationStructure L :=
  { scale := w.scale, val := w.val, scale_bot := w.scale_bot, val_bot := w.val_bot,
    val_unique := w.val_unique, val_scale := w.val_scale }
example {L : Type*} [ZPSemilattice L] (a : _VSlit L) : _VScast L :=
  { scale := a.scale, val := a.val, scale_bot := a.scale_bot, val_bot := a.val_bot,
    val_unique := a.val_unique, val_scale := a.val_scale }
example {L : Type*} [ZPSemilattice L] (b : _VScast L) : _VSlit L :=
  { scale := b.scale, val := b.val, scale_bot := b.scale_bot, val_bot := b.val_bot,
    val_unique := b.val_unique, val_scale := b.val_scale }

#print axioms _zpsZ2
#print axioms _zpsN
#print axioms _VSlit
#print axioms _VScast
-- The class TYPE carries choice, and the numeral in `val_scale` is THE route, not merely one
-- of several: `_VScast` above respells that numeral and NOTHING else, and comes out clean, so
-- no other constituent of the class is tainted. Both lines below are carrier-free.
#print axioms ValuationStructure
#print axioms instAddMonoidWithOneENat

-- Back to the 2-adic side: this one names the carrier, and is tainted accordingly.
#print axioms q2Scale_unique_fp

-- The degenerate witnesses making the NO-GO gauge's bound sharp for this class.
#print axioms trivialZPSemilattice
#print axioms trivialValuationStructure

end PurityCheck
