import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Valuation.Scale
import ZeroParadox.Computability.SelfApp
import Mathlib.Tactic

/-!
# ZPJ — Wheel Theory Formalization: /0 as a First-Class Element

## Engineer's Take

In past iterations we weren't able to definitively determine whether the Zero Paradox
theorem acted as a wheel or as a meadow.

After researching and failing on several occasions, we found Carlström 2001:11, which
provided the construction we'd been missing and the ability to distinguish between meadow
and wheel. The core of the Zero Paradox could have landed either way.

After building that construction out and verifying the rest of the required wheel axioms,
we're confident calling it a wheel. In particular, `inf_ne_bot` (∞ ≠ ⊥).

---

## Formal Overview (AI-assisted)

**⚠ SCOPE OF `⊥ = {⊥}` IN THIS FILE (CC-2 convention, applied 2026-08-02).** Every occurrence below is
the **ZF+AFA metatheoretic** statement — anti-foundation's actual content, where Aczel's Quine atom is a
real object and the equation is well-formed and true. **It is never a claim about a Lean carrier.**
Asserted of a carrier it would be a cross-type `=` (`bot : L` against `{bot} : Set L`), which is on the
framework's bedrock-violation list. Carrier-level statements take the **instance-of-family** form the
corpus already proves: `IsQuineAtom q := selfMem q ∧ ∀ x, selfMem x → x = q`, with
`da1_closed_concrete : IsQuineAtom (bot : MachinePhase)` as an instance and
`selfMem_eq_singleton_bot : {x | selfMemDerived x} = {bot}` as the `Set L` equality. **Do not "retire"
the equation** — that would deny a true theorem of a real set theory; scope it.

**Terminology — porthole (shorthand):** The zero-infinity identification point: the
element where `val(x) = ∞` and `/x = ∞` coincide, corresponding to `⊥ = {⊥}` in
ZF+AFA and `v₂(0) = ∞` in the 2-adic valuation. In wheel theory this is the element
where `/0` is a first-class defined value rather than an error. Used throughout as
shorthand for "the ZFC/AFA contact point where these structural identifications hold."

Wheel theory (Carlström 2001:11) extends a commutative ring by making division by zero
a defined first-class operation. The resulting structure has two special elements:
  - `∞ = /0`       — the multiplicative inverse of zero
  - `⊥ₗ = 0 · /0`  — the absorbing "undefined" element

**The ZP Conjecture (see §VIII — construction now formalized in `ZeroParadox/Algebra/WheelFrac.lean`):**
The wheel axioms for /0 are derivable from ring structure rather than independently
assumed, with the porthole (`val(⊥) = ∞` and `⊥ = {⊥}`) pinning the special element —
making wheel theory the algebraic representation of the porthole rather than a coincidence.

**Structural alignment (not proof):**
- In ZFC+Foundation: division by zero is undefined; the Axiom of Regularity prohibits
  x ∈ x for all sets x, ruling out self-containing elements
- In ZF+AFA: `⊥ = {⊥}` (the Quine atom) is admitted as the unique self-containing set
- In wheel theory: /0 is a first-class defined element — the porthole is structurally open

**The gap:** Derivation requires ring structure not present in the current ZP typeclasses.
`WheelValuationStructure` (§VII) is the intended bridge, and §VII-b is the NO-GO gauge showing it is
degenerately inhabited and so constrains nothing on its own. See §VIII for the full status.

This file:
  § I.   Wheel typeclass (Carlström Def 1.1: 8 axioms, 14 unbundled fields)
  § II.  Derived elements: wheelInf, wheelBot; winv_one proved abstractly
  § III. Concrete carrier: ZPWheelElem (ℚ extended with ∞ and ⊥ₗ)
  § IV.  Operations and Wheel instance (all axiom proofs sorry-free)
  § V.   Porthole theorems: /0 = ∞, 0·/0 = ⊥ₗ (proved)
  § VI.  Connection to ValuationStructure: val(⊥) = ∞ ↔ /0 = ∞ (proved)
  § VII.  WheelValuationStructure: the algebraic bridge (typeclass)
  § VII-b. NO-GO gauge: the class is degenerately inhabited; nondegeneracy as an explicit predicate
  § VIII. Main conjecture: resolved (construction formalized in `ZeroParadox/Algebra/WheelFrac.lean`)
  § IX.   Purity check

Status: Sorry-free. §VIII is now a documentation anchor with no theorem object; the
construction it points to is proved in `ZeroParadox/Algebra/WheelFrac.lean` — `instWheel` shows
the wheel of fractions `⊙_S A = (A × A)/≡_S` is a `Wheel` for any commutative ring `A` and
multiplicative submonoid `S` (sorry-free, `Classical.choice`-free, `[propext, Quot.sound]`).
§VII defines WheelValuationStructure — the typeclass identifying the bridge: a commutative
ring + multiplicative valuation with val(0) = ⊤, with the porthole (the ZF+AFA Quine atom
`⊥ = {⊥}` **motivating** val(⊥) = ∞ — see § VIII; nothing in the Lean derives it) pinning
the special element. The construction closes the construction
gap; §VI closes the identification gap. The universality result previously scoped as Tier 3
(a substantial, non-near-term target) is now formalized.
See notes/wheel_conjecture_proof_gap_2026-05-31.md for the original three-tier diagnosis.
-/

namespace ZeroParadox

open ZeroParadox ZPSemilattice
open ZeroParadox
open ZeroParadox
open ZeroParadox

-- ============================================================
-- § I. Wheel Typeclass
-- ============================================================

/-- A wheel: a set with +, ·, and a total involution /, making /0 a defined first-class element (∞)
    and 0·/0 an absorbing element (⊥ₗ).

    **Lineage — the name and the construction are Setzer's; Carlström is the generalizer.**
    Carlström 2001:11 p. 3 records it: Edalat and Potts adjoined `∞ = 1/0` and `⊥ = 0/0` to the
    reals; Martin-Löf proposed building them into the construction of the rationals from the
    integers; *"Such structures were called `wheels' … by Setzer [Set97], who showed how to modify
    the construction of fields of fractions from integral domains so that wheels are obtained
    instead of fields"*; and *"In this paper, we generalize Setzer's construction, so that it
    applies not only to integral domains, but to any commutative semiring."* This file follows
    Carlström's Definition 1.1, which is the general one.

    The axiom fields below are exactly Carlström's eight Definition 1.1 axioms, with his two
    "commutative monoid" axioms unbundled into their separate equational laws:
    Axioms W1–W3: (W, +, 0) commutative monoid                  [Carlström (1)]
    Axioms W4–W6: (W, ·, 1) commutative monoid                  [Carlström (2), monoid part]
    Axiom W7:  /(/x) = x  (involution)                          [Carlström (2), involution]
    Axiom W8:  /(x·y) = /x · /y                                 [Carlström (2), involution]
    Axiom W9:  (x+y)·z + 0·z = x·z + y·z  (distributivity)      [Carlström (3)]
    Axiom W10: x/y + z + 0y = (x + yz)/y                        [Carlström (4)]
    Axiom W11: 0·0 = 0                                          [Carlström (5)]
    Axiom W12: (x + 0y)·z = x·z + 0y                            [Carlström (6)]
    Axiom W13: /(x + 0y) = /x + 0y                              [Carlström (7)]
    Axiom W14: x + 0/0 = 0/0                                    [Carlström (8)]

    Key consequence: /0 (= wheelInf) and 0·/0 (= wheelBot) are well-defined.
    ⚠ **They must stay DISTINCT, and so must 0 and 1.** If any two of `0`, `1`, `/0`, `0·/0`
    coincide the wheel is trivial — one element (Carlström 2001:11, Prop. 4.4). `inf_ne_bot`
    (`Algebra/WheelFrac.lean`, given `0 ∉ S`) is what buys non-triviality; on this carrier,
    `zpw_inf_ne_bot` and `zpw_zero_ne_bot` (§V). -/
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
  -- W10: Carlström (4) — division/addition law:  x/y + z + 0y = (x + yz)/y
  wheel_id : ∀ x y z : W,
      wadd (wadd (wmul x (winv y)) z) (wmul wzero y) =
      wmul (wadd x (wmul y z)) (winv y)
  -- W11: Carlström (5) — 0·0 = 0
  wzero_mul_wzero : wmul wzero wzero = wzero
  -- W12: Carlström (6) — a zero-term commutes out of a product:  (x + 0y)z = xz + 0y
  wadd_zeromul_mul : ∀ x y z : W,
      wmul (wadd x (wmul wzero y)) z = wadd (wmul x z) (wmul wzero y)
  -- W13: Carlström (7) — a zero-term commutes through reciprocal:  /(x + 0y) = /x + 0y
  winv_add_zeromul : ∀ x y : W,
      winv (wadd x (wmul wzero y)) = wadd (winv x) (wmul wzero y)
  -- W14: Carlström (8) — the bottom 0/0 absorbs addition:  x + 0/0 = 0/0
  wadd_zeroinv_absorb : ∀ x : W,
      wadd x (wmul wzero (winv wzero)) = wmul wzero (winv wzero)

-- ============================================================
-- § II. Derived Elements and Basic Theorems
-- ============================================================

section WheelBasic
variable {W : Type*} [Wheel W]

/-- wheelInf: the infinite element /0. Conjectured ZP counterpart: the algebraic
    expression of `val(⊥) = ∞` at the porthole — see §VIII for status. -/
def wheelInf : W := Wheel.winv (Wheel.wzero)

/-- wheelBot: the absorbing bottom element 0·/0. Conjectured ZP counterpart: the
    algebraic expression of `⊥ = {⊥}` at the porthole — see §VIII for status. -/
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

    ⚠ **Not new, and it is the ORIGINAL example rather than a general one.** `ℚ ∪ {∞, ⊥}` is
    Carlström 2001:11's own first example, and it is `S₀A` for `A = ℤ` — *"A wheel in Setzer's sense
    will be recognized as what we denote by `S₀A`, where A is an integral domain, S₀ the subset
    A \ {0}"* (p. 3). So this carrier is a wheel in **Setzer's** narrower sense; what is contributed
    here is the machine-checked encoding and the ZP reading below, never the object.

    - `bot`:    0 · /0 — the absorbing undefined element (ZP: the porthole; the algebraic counterpart
                of the Quine-atom role, not an identity with it — different types)
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

-- The case-bash proofs below (over the custom `ZPWheelElem` inductive) use `simp_all`/`field_simp`
-- chains that trip two Mathlib house-style linters (`flexible`, `unnecessarySeqFocus`). They are
-- relaxed locally here, consistent with the standalone-repo lint policy (cf. lakefile.toml).
set_option linter.flexible false in
set_option linter.unnecessarySeqFocus false in
/-- ZPWheelElem is a Wheel. The fields encode Carlström's Definition 1.1 wheel axioms (his eight,
    with the two commutative-monoid axioms unbundled into their equational laws) for the rationals
    extended with ∞ and ⊥ₗ. All proofs are sorry-free, proceeding by cases on the three
    constructors (bot / fin / inf). -/
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
  wheel_id x y z := by
    cases x <;> cases y <;> cases z <;>
      (try dsimp only [zpwAdd, zpwMul, zpwInv]) <;>
      (try split_ifs) <;>
      (try dsimp only [zpwAdd, zpwMul, zpwInv]) <;>
      (try split_ifs) <;>
      simp_all [add_mul, mul_comm, add_zero, mul_zero] <;>
      (try field_simp)
  wzero_mul_wzero := by simp [zpwMul]
  wadd_zeromul_mul x y z := by
    cases x <;> cases y <;> cases z <;>
      simp only [zpwAdd, zpwMul] <;>
      (try split_ifs) <;>
      simp_all [mul_comm, add_zero]
  winv_add_zeromul x y := by
    cases x <;> cases y <;>
      simp only [zpwAdd, zpwMul, zpwInv] <;>
      (try split_ifs) <;>
      simp_all [add_zero]
  wadd_zeroinv_absorb x := by
    cases x <;> simp [zpwAdd, zpwMul, zpwInv]

-- ============================================================
-- § V. Porthole Theorems (proved without sorry)
-- ============================================================

/-- /0 = ∞: the porthole identification in algebraic form, proved for ZPWheelElem.
    Conjectured ZP counterpart: corresponds to val(⊥) = ∞ — see §VIII for status. -/
theorem zpw_inv_zero_eq_inf : zpwInv (.fin 0) = .inf := by
  simp [zpwInv]

/-- 0 · ∞ = ⊥ₗ: the absorbing-element identity, proved for ZPWheelElem.
    Conjectured ZP counterpart: algebraic expression of ⊥ = {⊥} — see §VIII for status. -/
theorem zpw_zero_mul_inf_eq_bot : zpwMul (.fin 0) .inf = .bot := by
  simp [zpwMul]

/-- ∞ · 0 = ⊥ₗ: commutativity of the porthole identification. -/
theorem zpw_inf_mul_zero_eq_bot : zpwMul .inf (.fin 0) = .bot := by
  simp [zpwMul]

/-- /∞ = 0: the porthole is symmetric — /(/0) = 0 as expected from W7. -/
theorem zpw_inv_inf_eq_zero : zpwInv .inf = .fin 0 := by
  simp [zpwInv]

/-- ∞ ≠ ⊥ₗ: the two portal elements stay distinct — wheel behaviour, not meadow collapse.
    Identifying them would force triviality (Carlström 2001:11, Prop. 4.4). -/
theorem zpw_inf_ne_bot : ZPWheelElem.inf ≠ .bot := by
  simp

-- Carlström Prop. 4.4 for this pair, abstract in any `Wheel`: identifying `/0` with `0·/0`
-- forces every element equal — so `1 = 0`, which no field admits.
example {W : Type*} [Wheel W] (h : (wheelInf : W) = wheelBot) : ∀ x y : W, x = y := by
  have hb : Wheel.winv (wheelBot (W := W)) = wheelBot := by
    show Wheel.winv (Wheel.wmul (Wheel.wzero : W) (Wheel.winv Wheel.wzero))
        = Wheel.wmul (Wheel.wzero : W) (Wheel.winv Wheel.wzero)
    rw [Wheel.winv_wmul, Wheel.winv_winv, Wheel.wmul_comm]
  have h0 : (Wheel.wzero : W) = wheelBot := by
    have hc := congrArg Wheel.winv h
    rw [hb, winv_wheelInf] at hc
    exact hc
  have hz : ∀ x : W, x = Wheel.wzero := by
    intro x
    have h14 : Wheel.wadd x (wheelBot (W := W)) = wheelBot := Wheel.wadd_zeroinv_absorb x
    rw [← h0, Wheel.wadd_zero] at h14
    exact h14
  intro x y
  rw [hz x, hz y]

/-- fin(0) ≠ ⊥ₗ: the semilattice ⊥ is distinct from the wheel's absorbing element.
    Algebraically: the porthole contact point (fin 0 ↔ inf) is not confusion with ⊥ₗ. -/
theorem zpw_zero_ne_bot : ZPWheelElem.fin 0 ≠ .bot := by
  simp

-- ============================================================
-- § VI. Connection to ValuationStructure
-- ============================================================

/-- The valuation on ZPWheelElem: fin(0) has infinite valuation (the porthole),
    all other finite rationals have valuation 1, bot and inf have valuation 0. -/
def zpwVal : ZPWheelElem → ℕ∞
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

/-- For ZPWheelElem: the element with infinite valuation (fin 0) is exactly the element
    whose wheel-inverse is ∞ (inf). This proves the porthole correspondence concretely:
    val(x) = ⊤  ↔  winv(x) = ∞  holds in ZPWheelElem.
    The abstract version — that this holds in any wheel satisfying the ZP structural
    constraints — is the content of the §VIII conjecture. -/
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
-- § VII. WheelValuationStructure — The Algebraic Bridge
-- ============================================================

/-- WheelValuationStructure: a commutative ring with a multiplicative valuation
    satisfying val(0) = ⊤. This typeclass identifies the bridge needed to close the
    structural gap between the ZP typeclasses and Wheel theory.

    **The "infinitudes of zero" argument** motivates the porthole condition val(0) = ⊤ from the
    self-referential structure of the bottom. It is a **motivation, not a derivation**: the condition
    is an assumed field here, and it is an assumed field under the standard structure too (see the
    PRIOR ART block below). Val(⊥) = ∞ is the algebraic signature of the Quine atom:
    the ring's zero is simultaneously the floor of the domain (as ⊥) and the point
    where its measure hits infinity (as val(⊥) = ⊤).

    **⚠ SCOPE, corrected 2026-08-01.** This paragraph used to end "This identification is structural
    necessity, not a modeling choice." That is contradicted by the `wvs_val_zero` field docstring
    thirty lines below ("an axiom — an assumed requirement, not a derived result") and by the
    published ZP-J addendum ("Ring structure is an input, not a conclusion"). The argument motivates
    the identification; the type-checker does not verify its necessity.

    **PRIOR ART — the neighbour is Mathlib's `AddValuation A ℕ∞` (found 2026-08-01).** `ℕ∞` is a
    `LinearOrderedAddCommMonoidWithTop`, so `AddValuation A ℕ∞` is well-formed at this generality.
    `AddValuation.of` (`Mathlib/RingTheory/Valuation/Basic.lean`) takes **four** axioms — `map_zero'`,
    `map_one'`, `map_add_le_max'` (the **ultrametric** inequality `min (v x) (v y) ≤ v (x+y)`), and
    `map_mul'`. This class supplies only the first and last, so it omits **two**, and the omissions
    do different work:
    * `map_one : v 1 = 0` is what admits § VII-b's degenerate instance — the constant-`⊤` map
      violates it, and every `AddValuation A ℕ∞` satisfies `WVSNondegenerate` with witness `1`.
      The converse holds too, so the omission is exactly recoverable: `nondegenerate_iff_map_one`
      (§ VII-b).
    * the **ultrametric** axiom is a genuine strengthening this class does not require. Witness:
      `v n = v₂ n + v₃ n` on `ℤ` is multiplicative, sends `0 ↦ ⊤` and `1 ↦ 0`, and is nondegenerate,
      yet `min (v 2) (v 3) = 1 ≰ 0 = v 5`. So this class does **not** imply `AddValuation`, and it is
      not a reduct of it by one axiom.

    **The two are INCOMPARABLE, not ordered — do not call this class "strictly weaker".**
    `AddValuation` is defined over a `Ring`; `WheelValuationStructure` bundles a `CommRing`. So neither
    implies the other in general: this class asks for less on the valuation conditions and more on the
    carrier. The weakening claim holds **only** for the valuation conditions, over a fixed commutative
    carrier — say that, or say nothing. *(Corrected 2026-08-01. "Strictly weaker than `AddValuation`"
    stood here and in the PUBLIC `LEAN_CUSTOM_REGISTRY.md`; it was the third revision of this one
    sentence across successive revisions, each of which fixed the arithmetic while leaving the
    ordering claim in place.)*

    **And the porthole condition is NOT discharged by adopting the standard structure.** `map_zero'`
    is a structure *field* (reached via `Valuation` → `MonoidWithZeroHom` → `ZeroHom`; `AddValuation.map_zero`
    is the projection — **not** the `map_zero'` assignment inside `AddValuation.of`, which is a
    different thing), and `ZeroParadox/Valuation/FloorWitness.lean`'s `addVal_bot`
    is literally the projection `v.map_zero`. Adoption **relocates** the assumption; it does not
    derive it. (Corrected 2026-08-01: an earlier revision of this block said the condition becomes a
    theorem, and said the class omits one axiom. Both were wrong, and the definition itself is what
    refutes them.) Adopting `AddValuation` would dissolve § VII-b's degeneracy, at the cost
    of also assuming the ultrametric inequality; that trade is **not** made here.

    However, the "infinitudes of zero" argument works at the *identification* layer —
    it tells you which element plays the porthole role. To *construct* a Wheel from
    this requires binary multiplication. ValuationStructure supplies only
    `scale : L → L` (a unary endomorphism, "multiply by p"), not a binary product.
    WheelValuationStructure closes this gap by adding ring structure explicitly.

    **From a commutative ring + multiplicative submonoid, the wheel of fractions construction**
      ⊙_S L = (L × L) / ≡_S   where   (a,b) ≡_S (c,d)  iff  ∃ s s' ∈ S, s·a = s'·c ∧ s·b = s'·d
    (the submonoid-quotient relation; naive cross-multiplication `a·d = b·c` is *not* an
    equivalence on a general commutative ring — transitivity fails without cancellation)
    yields a Wheel instance where:
      - wzero  = [0, 1]          — porthole element
      - winv([a, b]) = [b, a]    — involution is pair-swap
      - wmul([a,b],[c,d]) = [a·c, b·d] — inherited from ring multiplication
    The wheel axioms (Carlström Def 1.1) follow from the ring axioms on L plus the submonoid structure of S.
    This construction is now formalized in `ZeroParadox/Algebra/WheelFrac.lean` (`instWheel`) — the
    Tier 3 result of the porthole conjecture (§VIII). -/
-- [ZP-CUSTOM] incomparable with: Mathlib `AddValuation A ℕ∞` (RingTheory/Valuation/Basic.lean) | reason:
-- INCOMPARABLE, not ordered — it drops `map_one'` AND the ultrametric `map_add_le_max'`, so it is not a
-- reduct by one axiom; but `AddValuation` needs only `[Ring R]` while this class
-- `extends CommRing`, so neither implies the other and `AddValuation` cannot simply be substituted.
-- The weakening holds only for the valuation conditions over a fixed commutative carrier. See the
-- PRIOR ART block above for the separating witness. Kept as a named handle for the wheel bridge.
-- (The tag read "no Mathlib analog" until 2026-08-01, then "same three fields minus `map_one`" for one
-- revision, then "strictly WEAKER" — all three false. The last survived 32 lines below the block that
-- forbids the phrase, in the same file, in the same commit that wrote the prohibition; two gates
-- caught it independently. This tag is the grep target the public registry mirrors, so a stale tag
-- silently contradicts a corrected registry.
-- Note `AddValuation.supp` is NOT available here — its `add_mem'` uses `v.map_add`, which this class
-- does not have — so do not describe `WVSNondegenerate` in terms of `supp`. It is also NOT
-- `Valuation.IsNontrivial` (`∃ x, v x ≠ 0 ∧ v x ≠ 1`, two conjuncts, strictly stronger).)
class WheelValuationStructure (L : Type*) extends CommRing L where
  /-- The porthole valuation: measures proximity to the porthole element. -/
  wvs_val : L → ℕ∞
  /-- Multiplicativity: val is a semiring homomorphism to (ℕ∞, +). -/
  wvs_val_mul : ∀ x y : L, wvs_val (x * y) = wvs_val x + wvs_val y
  /-- Porthole condition: val(0_L) = ⊤. This is an axiom — an assumed requirement,
      not a derived result. The motivation: in ZP-compatible extensions the ring's zero is intended to
      **play the Quine-atom role** (`IsQuineAtom`, the family predicate — not to *be* the ZF+AFA Quine
      atom, which lives in a different type), and anything in that role has infinite valuation; this
      axiom encodes that as a formal requirement on any instance. The ZP argument motivates the choice;
      the type-checker does not verify the necessity. -/
  wvs_val_zero : wvs_val 0 = ⊤

-- ============================================================
-- § VII-b. NO-GO GAUGE — the class is degenerately inhabited
-- ============================================================

/-! ### The gauge

**Nothing depends on this class.** Outside this gauge no theorem takes `[WheelValuationStructure L]`
and no instance is registered; the wheel is carried by `Algebra/WheelFrac.lean`'s `instWheel` over
`[CommRing A]` plus a submonoid. So the defect below is preventive, not propagating, and the
published ZP-J addendum already says so — *"Ring structure is an input, not a conclusion"*,
`scripts/build_zpj_wheel_addendum.py:264`, the tracked script `register.md` fingerprints.
Mirrors `Computability/SelfApp.lean`'s `trivialSelfApp`: a warning comment is not checkable,
an inhabiting term is. -/

/-- **The degenerate instance.** The constant-`⊤` valuation satisfies every field on any commutative
    ring — `⊤ = ⊤ + ⊤`, `⊤ = ⊤` — and `ℤ` carries it, so this is no artifact of a trivial ring.
    ⚠ `@[reducible] def`, deliberately NOT an `instance`, and the absent keyword is load-bearing:
    registering it would resolve every downstream `[WheelValuationStructure A]` to the constant-`⊤`
    one, turning the gauge into the disease it measures. -/
@[reducible] def degenerateWVS (A : Type*) [inst : CommRing A] : WheelValuationStructure A where
  toCommRing := inst
  wvs_val := fun _ => ⊤
  wvs_val_mul := fun _ _ => rfl
  wvs_val_zero := rfl

/-- **The gauge, weak form.** Every commutative ring carries a `WheelValuationStructure`, so the bare
    hypothesis adds no discriminating power and a construction needing one must assume
    `WVSNondegenerate`. ⚠ `Nonempty` forgets the ring structure, so this does not by itself license
    transferring a conclusion back to `inst` — `gauge_strong` is the form that does. -/
theorem wheelValuationStructure_always_inhabited (A : Type*) [CommRing A] :
    Nonempty (WheelValuationStructure A) :=
  ⟨degenerateWVS A⟩

/-- **The gauge, strong form.** `Statement:` every commutative ring carries a
    `WheelValuationStructure` **on the ring structure it already has** — which is what licenses the
    transfer. Witness `degenerateWVS A`, kept a separate `def` so the gauge stays nameable. -/
theorem gauge_strong (A : Type*) [inst : CommRing A] :
    ∃ W : WheelValuationStructure A, W.toCommRing = inst :=
  ⟨degenerateWVS A, rfl⟩

/-- Nondegeneracy — the content the class does **not** carry. Per the commitments-in-hypotheses rule
    this is a **predicate to be assumed where needed**, deliberately NOT a class field: a carrier may
    or may not satisfy it, and bundling it would hide the assumption at every use site. -/
def WVSNondegenerate (L : Type*) [W : WheelValuationStructure L] : Prop :=
  ∃ x : L, W.wvs_val x ≠ ⊤

/-- The degenerate instance fails nondegeneracy, so the predicate is not vacuous. ⚠ It separates the
    constant-`⊤` map and nothing more: nondegeneracy is `map_one` (`nondegenerate_iff_map_one`), not
    `⊤`-exactly-at-`0`. The parity witness below is nondegenerate with `wvs_val 2 = ⊤` and `2 ≠ 0`. -/
theorem degenerateWVS_not_nondegenerate (A : Type*) [CommRing A] :
    ¬ @WVSNondegenerate A (degenerateWVS A) := by
  rintro ⟨x, hx⟩
  exact hx rfl

/-- **The unit decides the whole map.** `Statement:` `wvs_val 1 = ⊤` forces `wvs_val` constantly `⊤`,
    since `wvs_val x = wvs_val (x * 1) = wvs_val x + ⊤`. So § VII-b's degeneracy is not one bad member
    among many — it is reached from a single field value. -/
theorem collapse_from_unit {L : Type*} [W : WheelValuationStructure L]
    (h1 : W.wvs_val 1 = ⊤) (x : L) : W.wvs_val x = ⊤ := by
  have h := W.wvs_val_mul x 1
  rw [mul_one, h1] at h
  exact h.trans (WithTop.add_top _)

/-- `Statement:` `WVSNondegenerate L ↔ wvs_val 1 ≠ ⊤` — nondegeneracy is a fact about the unit alone.
    ⚠ Use this form, not `nondegenerate_iff_map_one`, in anything that must stay axiom-free: same
    content, and only this one avoids the `ℕ∞` numeral. -/
theorem nondegenerate_iff_unit_ne_top (L : Type*) [W : WheelValuationStructure L] :
    WVSNondegenerate L ↔ W.wvs_val 1 ≠ ⊤ :=
  ⟨fun ⟨x, hx⟩ h1 => hx (collapse_from_unit h1 x), fun h => ⟨1, h⟩⟩

/-- **The predicate IS the omitted axiom.** `Statement:` `WVSNondegenerate L ↔ wvs_val 1 = 0` — the
    nondegeneracy this class states by hand is exactly `map_one`, the `AddValuation.of` axiom the
    PRIOR ART block above records this class as dropping. § VII:420 carried the one-way half
    informally; this is the biconditional.

    The step is `wvs_val 1 = wvs_val 1 + wvs_val 1`, so `wvs_val 1` is `+`-idempotent. In an ordered
    value **group** cancellation would finish it and `map_one` would be a theorem, which is why the
    textbook statement is an identity rather than a dichotomy. Over `ℕ∞` cancellation fails at
    exactly one point, so idempotence yields `0` **or** `⊤` — and that dichotomy is what turns
    `map_one` into a biconditional with nondegeneracy rather than a consequence of it.

    Prior art, searched 2026-09-12, none closer located: the group-valued half is standard (Aitken,
    arXiv:2102.11725, Lemma 1); where the codomain absorbs, `map_one` is an axiom not a theorem
    (Gunn, arXiv:2211.06480v2, Prop. 2.26). No located source states the dichotomy; no novelty claimed. -/
theorem nondegenerate_iff_map_one (L : Type*) [W : WheelValuationStructure L] :
    WVSNondegenerate L ↔ W.wvs_val 1 = 0 := by
  rw [nondegenerate_iff_unit_ne_top]
  refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
  have hidem : W.wvs_val 1 + W.wvs_val 1 = W.wvs_val 1 := by
    have h2 := W.wvs_val_mul 1 1
    rw [mul_one] at h2
    exact h2.symm
  generalize hv : W.wvs_val 1 = a at h hidem
  induction a using ENat.recTopCoe with
  | top => exact absurd rfl h
  | coe n =>
    have hn : n + n = n := ENat.coe_inj.mp hidem
    have h0 : n = 0 := by omega
    rw [h0]; rfl

/-- **The control on the paragraph above: nondegeneracy does not buy `⊤`-exactly-at-`0`.** The
    parity valuation on `ℤ` — `⊤` on the evens, `0` on the odds — satisfies every field of the class,
    is nondegenerate, and still sends `2 ↦ ⊤` with `2 ≠ 0`.

    So a nondegenerate `WheelValuationStructure` is **not** an `AddValuation`: nondegeneracy restores
    `map_one` and leaves the ultrametric axiom absent, and a porthole valuation in the intended sense
    is strictly stronger than both. Anonymous, so it declares nothing and owes no registry row. -/
example : ∃ W : WheelValuationStructure ℤ,
    @WVSNondegenerate ℤ W ∧ ∃ x : ℤ, x ≠ 0 ∧ W.wvs_val x = ⊤ := by
  refine ⟨{ toCommRing := inferInstance
            wvs_val := fun n => if n % 2 = 0 then ⊤ else 0
            wvs_val_mul := ?_
            wvs_val_zero := ?_ }, ⟨1, ?_⟩, 2, by norm_num, ?_⟩
  · intro x y
    have h : (x * y) % 2 = (x % 2) * (y % 2) % 2 := Int.mul_emod x y 2
    rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
      rcases Int.emod_two_eq_zero_or_one y with hy | hy <;>
      rw [hx, hy] at h <;> norm_num at h <;> simp [h, hx, hy]
  · norm_num
  · show ¬ (if (1 : ℤ) % 2 = 0 then (⊤ : ℕ∞) else 0) = ⊤
    norm_num
  · show (if (2 : ℤ) % 2 = 0 then (⊤ : ℕ∞) else 0) = ⊤
    norm_num

/-! **Axiom footprint**, checked by § IX rather than asserted here. Six of the seven gauge
declarations are axiom-free; `nondegenerate_iff_map_one` reports `[propext, Classical.choice,
Quot.sound]` — and that footprint is carried by the STATEMENT, not the proof.
⚠ The two `nondegenerate_iff_*` theorems are the measurement: same fact, same file, same style, only
the second writing the `ℕ∞` numeral `0`. Measured 2026-09-12 in this pinned Mathlib — at `ℕ∞`,
`(⊤ : ℕ∞) = ⊤`, `((n : ℕ) : ℕ∞) = n` and `a + b = a + b` are each axiom-free by `rfl`, while
`(0 : ℕ∞) = 0` and `(1 : ℕ∞) = 1` by `rfl` each report the same triple. Scope: those five `rfl`s; no
claim about which instance declaration carries it. `ZeroParadox/Ordinal/SyntacticCollapse.lean`
records the same shape on `ℚ`. -/

-- ============================================================
-- § VIII. The Main Conjecture (Resolved)
-- ============================================================

/-! ### Resolution

A documentation anchor; no theorem object. The conjecture — that the ZP porthole forces the wheel
axioms — is proved in `ZeroParadox/Algebra/WheelFrac.lean` (`instWheel`, `inf_ne_bot`), not
importable here without a cycle; concretely for this carrier, `zpw_top_val_iff_inv_is_inf` (§VI).

Two gaps, and only one closes. "Infinitudes of zero" closes the IDENTIFICATION gap — which element
plays the porthole role — leaving `wvs_val 0 = ⊤` an assumed class field, motivated and not forced
(§VII). It does not close the CONSTRUCTION gap: `scale` is unary and `wmul` binary, so ring structure
is the missing hypothesis (the `WithTop L` + `selfApp` route does not close). Read § VII-b first. -/

-- ============================================================
-- § IX. Purity Check
-- ============================================================

section PurityCheck
#print axioms zpw_inv_zero_eq_inf
#print axioms zpw_zero_mul_inf_eq_bot
#print axioms zpw_inf_ne_bot
#print axioms zpw_zero_ne_bot
#print axioms zpwVal_zero_eq_top
#print axioms zpwVal_inv_zero
-- § VII-b NO-GO gauge. The footprint block there asserts nothing; it is checked here.
-- Six axiom-free, and `nondegenerate_iff_map_one` is the one that is not — read the two
-- `nondegenerate_iff_*` lines together, they are the measurement that block describes.
#print axioms degenerateWVS
#print axioms wheelValuationStructure_always_inhabited
#print axioms gauge_strong
#print axioms degenerateWVS_not_nondegenerate
#print axioms collapse_from_unit
#print axioms nondegenerate_iff_unit_ne_top
#print axioms nondegenerate_iff_map_one
end PurityCheck

end ZeroParadox
