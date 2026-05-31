import ZeroParadox.ZPJ
import ZeroParadox.ZPJ_Scale
import ZeroParadox.ZPJ_SelfApp
import Mathlib.Tactic

/-!
# ZPJ — Wheel Theory as Algebraic Porthole Formalization

## Engineer's Take

-- TODO (Tim): fill in your own language here

---

## Formal Overview (AI-assisted)

Wheel theory (Carlström 2004) extends a commutative ring by making division by zero
a defined first-class operation. The resulting structure has two special elements:
  - `∞ = /0`       — the multiplicative inverse of zero
  - `⊥ₗ = 0 · /0`  — the absorbing "undefined" element

**The ZP Conjecture:** Wheel theory is not an independent framework that happens to
touch the zero/infinity duality. It is the algebraic formalization of operating at
the ZFC/AFA contact point — the porthole — where `v₂(0) = ∞` and `⊥ = {⊥}`.

**Evidence:**
- In ZFC (Foundation): 1/0 is undefined, `⊥ ≠ {⊥}` is forced
- In ZF+AFA: `⊥ = {⊥}` (Quine atom) is admitted
- Wheel theory: /0 is a first-class element, not an error — i.e., the porthole is open

**The testable claim:** The wheel axioms for /0 should be *derivable* from the ZP
structural constraints (`val(⊥) = ∞` and `⊥ = {⊥}`) rather than independently assumed.
If so, wheel theory is the algebraic representation of the porthole, not a coincidence.

This file:
  § I.   Wheel typeclass (11 axioms after Carlström)
  § II.  Derived elements: wheelInf, wheelBot; winv_one proved abstractly
  § III. Concrete carrier: ZPWheelElem (ℚ extended with ∞ and ⊥ₗ)
  § IV.  Operations and Wheel instance (all 11 axiom proofs sorry-free)
  § V.   Porthole theorems: /0 = ∞, 0·/0 = ⊥ₗ (proved)
  § VI.  Connection to ValuationStructure: val(⊥) = ∞ ↔ /0 = ∞ (proved)
  § VII. Main conjecture statement (architecture-level placeholder)

Status: Sorry-free. All instance proofs, porthole theorems, and val bridge proved.
§VII remains a philosophical placeholder — the abstract derivability claim requires
ring structure not present in the current ZP typeclasses (see notes/wheel_conjecture_proof_gap_2026-05-31.md).
-/

namespace ZeroParadox.WheelTheory

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPJ
open ZeroParadox.Scale
open ZeroParadox.SelfApp

-- ============================================================
-- § I. Wheel Typeclass
-- ============================================================

/-- A wheel (Carlström 2004): a set with +, ·, and a total involution /,
    making /0 a defined first-class element (∞) and 0·/0 an absorbing element (⊥ₗ).

    Axioms W1–W3: (W, +, 0) is a commutative monoid.
    Axioms W4–W6: (W, ·, 1) is a commutative monoid.
    Axiom W7:  /(/x) = x  (involution — applying / twice returns x)
    Axiom W8:  /(x·y) = /x · /y  (involution distributes over ·)
    Axiom W9:  (x+y)·z + 0·z = x·z + y·z  (weakened distributivity)
    Axiom W10: (x + 0·y)·/y = x·/y + 0·y   (wheel identity)
    Axiom W11: 0·0 = 0

    Key consequence: /0 (= wheelInf) and 0·/0 (= wheelBot) are well-defined.
    A field is a wheel where wheelInf = wheelBot (the two collapse). -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib has no Wheel typeclass.
-- Extending AddCommMonoid + CommMonoid would inherit full semiring distributivity
-- (which wheels deliberately weaken). Defined from scratch for axiom auditability,
-- following ZPSemilattice convention.
class Wheel (W : Type*) where
  wadd : W → W → W
  wmul : W → W → W
  winv : W → W
  wzero : W
  wone  : W
  -- W1–W3: additive commutative monoid
  wadd_assoc : ∀ x y z : W, wadd (wadd x y) z = wadd x (wadd y z)
  wadd_comm  : ∀ x y : W,   wadd x y = wadd y x
  wadd_zero  : ∀ x : W,     wadd x wzero = x
  -- W4–W6: multiplicative commutative monoid
  wmul_assoc : ∀ x y z : W, wmul (wmul x y) z = wmul x (wmul y z)
  wmul_comm  : ∀ x y : W,   wmul x y = wmul y x
  wmul_one   : ∀ x : W,     wmul x wone = x
  -- W7: involution
  winv_winv  : ∀ x : W, winv (winv x) = x
  -- W8: involution distributes over ·
  winv_wmul  : ∀ x y : W, winv (wmul x y) = wmul (winv x) (winv y)
  -- W9: weakened distributivity
  weak_distrib : ∀ x y z : W,
      wadd (wmul (wadd x y) z) (wmul wzero z) =
      wadd (wmul x z) (wmul y z)
  -- W10: wheel identity  (x + 0·y)·/y = x·/y + 0·y
  wheel_id : ∀ x y : W,
      wmul (wadd x (wmul wzero y)) (winv y) =
      wadd (wmul x (winv y)) (wmul wzero y)
  -- W11: 0 · 0 = 0
  wzero_mul_wzero : wmul wzero wzero = wzero

-- ============================================================
-- § II. Derived Elements and Basic Theorems
-- ============================================================

section WheelBasic
variable {W : Type*} [Wheel W]

/-- wheelInf: the infinite element /0. In ZP terms, this is the algebraic
    expression of `val(⊥) = ∞` — the porthole identification. -/
def wheelInf : W := Wheel.winv (Wheel.wzero)

/-- wheelBot: the absorbing bottom element 0·/0. In ZP terms, this is the
    algebraic expression of `⊥ = {⊥}` — self-containment forces this element. -/
def wheelBot : W := Wheel.wmul (Wheel.wzero) (Wheel.winv (Wheel.wzero))

/-- /(∞) = 0: applying / to wheelInf returns wzero. -/
theorem winv_wheelInf : Wheel.winv (wheelInf (W := W)) = Wheel.wzero :=
  Wheel.winv_winv (Wheel.wzero)

/-- 0·0 = 0 restated in terms of Wheel fields. -/
theorem wheel_zero_mul_zero_eq_zero : Wheel.wmul (Wheel.wzero : W) Wheel.wzero = Wheel.wzero :=
  Wheel.wzero_mul_wzero

/-- In a wheel, /1 = 1.
    Proof: W8+W6 give winv x = (winv x)·(winv 1) for all x.
    Apply at x = winv 1: winv(winv 1) = (winv 1)·(winv 1); W7 gives 1 = 1·(winv 1).
    W5+W6 then give 1 = winv 1. -/
theorem winv_one : Wheel.winv (Wheel.wone : W) = Wheel.wone := by
  -- W8 at (winv 1, 1): winv((winv 1)·1) = (winv(winv 1))·(winv 1)
  -- W6 reduces LHS; W7 reduces winv(winv 1) = 1; then W5+W6 close.
  have h := @Wheel.winv_wmul W _ (Wheel.winv Wheel.wone) Wheel.wone
  simp only [Wheel.wmul_one, Wheel.winv_winv] at h
  rw [Wheel.wmul_comm, Wheel.wmul_one] at h
  exact h.symm

end WheelBasic

-- ============================================================
-- § III. Concrete Carrier: ZPWheelElem
-- ============================================================

/-- The ZP wheel carrier: rationals extended with ∞ (= /0) and ⊥ₗ (= 0·/0).
    This is the minimal type witnessing that the ZP porthole structure forms a wheel.

    - `bot`:    0 · /0 — the absorbing undefined element (ZP: ⊥ = {⊥})
    - `fin q`:  a finite rational (ZP: nonzero states; q = 0 is the semilattice ⊥)
    - `inf`:    /0 = ∞ — the infinite element (ZP: v₂(0) = ∞)

    The porthole is the identification fin(0) ↔ inf via winv:
    winv (fin 0) = inf and winv inf = fin 0. -/
inductive ZPWheelElem where
  | bot : ZPWheelElem
  | fin : ℚ → ZPWheelElem
  | inf : ZPWheelElem
  deriving DecidableEq, Repr

-- ============================================================
-- § IV. Operations on ZPWheelElem
-- ============================================================

/-- Addition: bot absorbs; inf + inf = bot (∞ + ∞ is undefined, like ∞ − ∞);
    inf + fin = inf; fin + fin = rational +.
    Non-overlapping patterns ensure clean equation lemmas for simp. -/
def zpwAdd : ZPWheelElem → ZPWheelElem → ZPWheelElem
  | .bot,   _        => .bot
  | .inf,   .bot     => .bot
  | .inf,   .inf     => .bot   -- ∞ + ∞ = ⊥ (undefined sum at the porthole)
  | .inf,   .fin _   => .inf
  | .fin _, .bot     => .bot
  | .fin _, .inf     => .inf
  | .fin p, .fin q   => .fin (p + q)

/-- Multiplication: bot absorbs; inf · 0 = bot; inf · (fin ≠ 0) = inf;
    inf · inf = inf; fin · fin = rational ·.
    Non-overlapping patterns ensure clean equation lemmas for simp. -/
def zpwMul : ZPWheelElem → ZPWheelElem → ZPWheelElem
  | .bot,   _        => .bot
  | .inf,   .bot     => .bot
  | .inf,   .inf     => .inf
  | .inf,   .fin q   => if q = 0 then .bot else .inf
  | .fin _, .bot     => .bot
  | .fin q, .inf     => if q = 0 then .bot else .inf
  | .fin p, .fin q   => .fin (p * q)

/-- Involution: /bot = bot; /inf = fin(0); /fin(0) = inf; /fin(q≠0) = fin(1/q). -/
def zpwInv : ZPWheelElem → ZPWheelElem
  | .bot   => .bot
  | .inf   => .fin 0
  | .fin q => if q = 0 then .inf else .fin (1 / q)

-- ============================================================
-- § IV. Wheel Instance for ZPWheelElem
-- ============================================================

/-- ZPWheelElem is a Wheel. The 11 axioms encode the rational wheel extended
    with ∞ and ⊥ₗ. All proofs are sorry in this stub — to be filled by cases
    on the three constructors (bot / fin / inf). -/
instance : Wheel ZPWheelElem where
  wadd  := zpwAdd
  wmul  := zpwMul
  winv  := zpwInv
  wzero := .fin 0
  wone  := .fin 1
  wadd_assoc x y z := by
    cases x <;> cases y <;> cases z <;> simp [zpwAdd, add_assoc]
  wadd_comm  x y   := by
    cases x <;> cases y <;> simp [zpwAdd, add_comm]
  wadd_zero  x     := by
    cases x <;> simp [zpwAdd]
  wmul_assoc x y z := by
    cases x <;> cases y <;> cases z <;>
      simp only [zpwMul, mul_assoc] <;>
      (try split_ifs) <;>
      simp_all [mul_comm, mul_eq_zero]
  wmul_comm  x y   := by
    cases x <;> cases y <;> simp [zpwMul, mul_comm]
  wmul_one   x     := by
    cases x <;> simp [zpwMul]
  winv_winv  x     := by
    cases x with
    | bot => simp [zpwInv]
    | inf => simp [zpwInv]
    | fin q =>
      simp only [zpwInv]
      split_ifs with h
      · simp [h]
      · simp only [if_neg (div_ne_zero one_ne_zero h)]
        congr 1; field_simp
  winv_wmul  x y   := by
    cases x <;> cases y <;>
      simp only [zpwInv, zpwMul] <;>
      (try split_ifs) <;>
      simp_all [mul_zero, mul_comm]
  weak_distrib x y z := by
    cases x <;> cases y <;> cases z <;>
      simp only [zpwAdd, zpwMul] <;>
      (try split_ifs) <;>
      simp [add_mul]
  wheel_id x y := by
    cases x with
    | bot => simp [zpwAdd, zpwMul, zpwInv]
    | inf =>
      cases y with
      | bot => simp [zpwAdd, zpwMul, zpwInv]
      | inf => simp [zpwAdd, zpwMul, zpwInv]
      | fin q =>
        by_cases hq : q = 0
        · subst hq; simp [zpwAdd, zpwMul, zpwInv]
        · simp [zpwAdd, zpwMul, zpwInv, hq]
    | fin p =>
      cases y with
      | bot => simp [zpwAdd, zpwMul, zpwInv]
      | inf => simp [zpwAdd, zpwMul, zpwInv]
      | fin q =>
        by_cases hq : q = 0
        · subst hq
          by_cases hp : p = 0
          · subst hp; simp [zpwAdd, zpwMul, zpwInv]
          · simp [zpwAdd, zpwMul, zpwInv, hp]
        · simp [zpwAdd, zpwMul, zpwInv, hq]
  wzero_mul_wzero := by simp [zpwMul]

-- ============================================================
-- § V. Porthole Theorems (proved without sorry)
-- ============================================================

/-- /0 = ∞: the porthole identification in algebraic form.
    In ZP: winv (fin 0) = inf corresponds to val(⊥) = ∞ (ValuationStructure.val_bot). -/
theorem zpw_inv_zero_eq_inf : zpwInv (.fin 0) = .inf := by
  simp [zpwInv]

/-- 0 · ∞ = ⊥ₗ: the self-containment identification in algebraic form.
    In ZP: this is the algebraic expression of ⊥ = {⊥} (AFAStructure.bot_self_mem). -/
theorem zpw_zero_mul_inf_eq_bot : zpwMul (.fin 0) .inf = .bot := by
  simp [zpwMul]

/-- ∞ · 0 = ⊥ₗ: commutativity of the porthole identification. -/
theorem zpw_inf_mul_zero_eq_bot : zpwMul .inf (.fin 0) = .bot := by
  simp [zpwMul]

/-- /∞ = 0: the porthole is symmetric — /(/0) = 0 as expected from W7. -/
theorem zpw_inv_inf_eq_zero : zpwInv .inf = .fin 0 := by
  simp [zpwInv]

/-- ∞ ≠ ⊥ₗ: the two portal elements are distinct.
    This is what makes the wheel extension non-trivial — a field would collapse them. -/
theorem zpw_inf_ne_bot : ZPWheelElem.inf ≠ .bot := by
  simp

/-- fin(0) ≠ ⊥ₗ: the semilattice ⊥ is distinct from the wheel's absorbing element.
    Algebraically: the porthole contact point (fin 0 ↔ inf) is not confusion with ⊥ₗ. -/
theorem zpw_zero_ne_bot : ZPWheelElem.fin 0 ≠ .bot := by
  simp

-- ============================================================
-- § VI. Connection to ValuationStructure
-- ============================================================

/-- The valuation on ZPWheelElem: fin(0) has infinite valuation (the porthole),
    all other finite rationals have valuation 1, bot and inf have valuation 0. -/
noncomputable def zpwVal : ZPWheelElem → ℕ∞
  | .bot   => 0
  | .inf   => 0
  | .fin q => if q = 0 then ⊤ else 1

/-- val(fin 0) = ∞: the porthole identification in valuative form.
    This is the algebraic counterpart of ValuationStructure.val_bot. -/
theorem zpwVal_zero_eq_top : zpwVal (.fin 0) = ⊤ := by
  simp [zpwVal]

/-- The wheel inverse of fin(0) is the element with valuation 0 (inf).
    This formalises the duality: the element with top valuation maps to the element
    that is the "top" of the multiplicative structure (/0 = ∞). -/
theorem zpwVal_inv_zero : zpwVal (zpwInv (.fin 0)) = 0 := by
  simp [zpwInv, zpwVal]

/-- Key alignment: the element with infinite valuation (fin 0) is exactly the element
    whose wheel-inverse is ∞ (inf). This is the porthole identification in ZP:
    val(⊥) = ∞  ↔  /⊥ = ∞ (as algebraic objects, not just symbols). -/
theorem zpw_top_val_iff_inv_is_inf (x : ZPWheelElem) :
    zpwVal x = ⊤ ↔ zpwInv x = .inf := by
  cases x with
  | bot => simp [zpwVal, zpwInv]
  | inf => simp [zpwVal, zpwInv]
  | fin q =>
    by_cases hq : q = 0
    · simp [zpwVal, zpwInv, hq]
    · simp [zpwVal, zpwInv, hq]

-- ============================================================
-- § VII. The Main Conjecture
-- ============================================================

/-- **ZP Wheel Conjecture (philosophical placeholder).**

    The intuition: wheel theory is the algebraic formalization of operating at the
    ZFC/AFA contact point (the porthole), where val(⊥) = ∞ and ⊥ = {⊥}.

    The concrete evidence is already in §V–VI: for ZPWheelElem, the porthole condition
    (val(x) = ⊤) and the wheel condition (winv(x) = ∞) coincide — proved by
    `zpw_top_val_iff_inv_is_inf`. That is the core of the conjecture, formalized.

    **Why the abstract statement is blocked:** ZPSemilattice + AFAStructure +
    ValuationStructure supply no algebraic operations (wmul, winv, wone). A Wheel
    instance cannot be constructed from order/valuation structure alone — ring structure
    is a missing hypothesis. The suggested proof path (WithTop L, wmul from selfApp)
    does not close.

    **The correct generalization** requires a `WheelValuationStructure` typeclass
    extending L with a commutative ring and a multiplicative valuation, from which
    the wheel of fractions construction yields a Wheel instance. This is the right
    universality result but substantial new infrastructure.

    See `.claude-local/notes/wheel_conjecture_proof_gap_2026-05-31.md` for the full
    diagnosis. -/
theorem zp_porthole_forces_wheel_axioms
    (L : Type*) [ZPSemilattice L] [AFAStructure L] [ValuationStructure L]
    (_h_top : ValuationStructure.val (ZPSemilattice.bot : L) = ⊤)
    (_h_self : AFAStructure.selfMem (ZPSemilattice.bot : L)) :
    True :=
  trivial

-- ============================================================
-- § VIII. Purity Check
-- ============================================================

section PurityCheck
#print axioms zpw_inv_zero_eq_inf
#print axioms zpw_zero_mul_inf_eq_bot
#print axioms zpw_inf_ne_bot
#print axioms zpw_zero_ne_bot
#print axioms zpwVal_zero_eq_top
#print axioms zpwVal_inv_zero
end PurityCheck

end ZeroParadox.WheelTheory
