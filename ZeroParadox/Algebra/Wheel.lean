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

/-- A wheel (Carlström 2001:11): a set with +, ·, and a total involution /,
    making /0 a defined first-class element (∞) and 0·/0 an absorbing element (⊥ₗ).

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

/-! ### The gauge (2026-08-01)

**No mathematical result depends on this class** — outside the gauge below, no theorem takes
`[WheelValuationStructure L]` and no instance is registered — and the results that carry the wheel
(`Algebra/WheelFrac.lean`'s `instWheel`) are built on `[CommRing A]` plus a multiplicative submonoid,
never on this class. (`WVSNondegenerate` below does take the class; it is part of the gauge, and it
asserts nothing about a carrier on its own.) That
is what keeps the defect below **preventive** rather than propagating. The published documents were
already honest about it: the ZP-J addendum states *"Ring structure is an input, not a conclusion"*
and says this class's porthole condition *"is an assumed axiom, motivated by the ZP argument rather
than type-checked as necessary."* *(Quotation corrected 2026-08-01: an earlier revision rendered the
tail as "… **not** type-checked as necessary", putting a word inside the quotation marks that the
source — `scripts/build_zpj_wheel_addendum.py` (the public mirror; the active script is gitignored),
    the paragraph ending "…motivated by the ZP argument rather than type-checked as necessary." — does not contain.)*

The gauge exists so the trap cannot be sprung later. It mirrors
`Computability/SelfApp.lean`'s `trivialSelfApp` gauge, and it exists because a warning comment is
not checkable while an inhabiting term is. -/

/-- **The degenerate instance.** The constant-`⊤` valuation satisfies **every** field on **any**
    commutative ring: `⊤ = ⊤ + ⊤` discharges multiplicativity and `⊤ = ⊤` discharges the porthole
    condition. Note the carrier is unrestricted — `ℤ` carries this, so the degeneracy is not an
    artifact of a trivial ring. -/
@[reducible] def degenerateWVS (A : Type*) [inst : CommRing A] : WheelValuationStructure A where
  toCommRing := inst
  wvs_val := fun _ => ⊤
  wvs_val_mul := fun _ _ => rfl
  wvs_val_zero := rfl

/-- **The gauge.** Every commutative ring carries a `WheelValuationStructure`. Therefore **nothing
    BEYOND the commutative-ring structure already assumed** follows from adding the bare hypothesis
    `[WheelValuationStructure A]` — any argument of the form "A carries `WheelValuationStructure`,
    therefore [something not already true of every `CommRing`]" is **vacuous**, and any future
    construction over this class must carry `WVSNondegenerate` as an explicit hypothesis.

    *(Scoped 2026-08-01. This read "no property of `A` follows from the bare hypothesis", which is
    over-broad: `A` carries `CommRing` throughout, so ring-derived properties do follow and a reader
    was being told to discard legitimate results. What the theorem below shows is that the class adds
    no discriminating power, not that `A` has no properties.)* -/
theorem wheelValuationStructure_always_inhabited (A : Type*) [CommRing A] :
    Nonempty (WheelValuationStructure A) :=
  ⟨degenerateWVS A⟩

/-- Nondegeneracy — the content the class does **not** carry. Per the commitments-in-hypotheses rule
    this is a **predicate to be assumed where needed**, deliberately NOT a class field: a carrier may
    or may not satisfy it, and bundling it would hide the assumption at every use site. -/
def WVSNondegenerate (L : Type*) [W : WheelValuationStructure L] : Prop :=
  ∃ x : L, W.wvs_val x ≠ ⊤

/-- The degenerate instance fails nondegeneracy — so the predicate is not itself vacuous, and it is
    exactly what separates a real porthole valuation from the constant-`⊤` one. -/
theorem degenerateWVS_not_nondegenerate (A : Type*) [CommRing A] :
    ¬ @WVSNondegenerate A (degenerateWVS A) := by
  rintro ⟨x, hx⟩
  exact hx rfl

/-! **Axiom footprint: `degenerateWVS`, `wheelValuationStructure_always_inhabited` and
`degenerateWVS_not_nondegenerate` are AXIOM-FREE**, checked by the `#print axioms` block in § IX
rather than asserted here. (`WVSNondegenerate` is a `def`, so it carries no footprint of its own.) -/

-- ============================================================
-- § VIII. The Main Conjecture (Resolved)
-- ============================================================

/-! ### Resolution

This section is a documentation anchor only — there is no theorem object here. The conjecture
that the ZP porthole forces the wheel axioms is now a theorem, formalized in `ZeroParadox/Algebra/WheelFrac.lean`
(which cannot be imported here without an import cycle, hence the prose pointer rather than a
re-export).

**What is proved (§V–VI):** For ZPWheelElem, the porthole condition and the wheel
condition coincide — proved by `zpw_top_val_iff_inv_is_inf`:
  val(x) = ⊤  ↔  winv(x) = ∞
This is the core of the conjecture, concretely formalized.

**The "infinitudes of zero" insight:** val(0) = ⊤ is not a free hypothesis in
ZP — it is **motivated** by the self-referential structure ⊥ = {⊥} (the Quine atom, in the ZF+AFA
metatheory). *(Not "forced": nothing in the Lean derives `wvs_val 0 = ⊤` from anything — it is an
assumed class field, as § VII says and as the ZP-J addendum quoted there states. Corrected
2026-08-02; the scope note at the head of this file says every `⊥ = {⊥}` here is metatheoretic. That
correction recorded "forced" as **the one** carrier-level occurrence, which was itself wrong: § VII's
overview said the equation "structurally requires" val(⊥) = ∞ — the same modality, left standing by
the same pass. Corrected 2026-08-03. All nine occurrences re-read individually that day; the other
seven are metatheory-scoped or hedged as conjectural and are correct as written.)*
The ring's zero is simultaneously the lattice floor *and* the point where the
valuation hits infinity. This structural motivation identifies *which* element
plays the porthole role (wzero), but it does not construct the binary operation
wmul. The "infinitudes of zero" argument closes the identification gap; it cannot
close the construction gap.

**Why the abstract statement is blocked:** ValuationStructure supplies
`scale : L → L` (unary — "multiply by p"). `wmul : W → W → W` is binary.
Arbitrary binary multiplication cannot be recovered from a single unary endomorphism
without knowing what operation you are iterating. Ring structure is the missing
hypothesis; the suggested path (WithTop L, wmul from selfApp) does not close.

**The intended bridge:** `WheelValuationStructure` (§VII) — a commutative ring with
multiplicative valuation satisfying wvs_val(0) = ⊤. From this, the wheel of
fractions construction Wh(L) = (L × L)/~ yields a Wheel instance, and the porthole
condition pins wzero. Wheel axioms follow from ring axioms + valuation axioms.
**Read § VII-b before building on it:** the class as stated is **degenerately inhabited**
(`wheelValuationStructure_always_inhabited`), so it adds **no constraint beyond the `CommRing`
already assumed**, and anything built over the bare hypothesis that is not already true of every
commutative ring is vacuous. The working results below take `[CommRing A]` and a
multiplicative submonoid instead, and do not route through this class. A construction that
genuinely needs a porthole valuation must assume `WVSNondegenerate` explicitly.

**The construction, formalized:** see `ZeroParadox/Algebra/WheelFrac.lean`.
`instWheel` proves that the wheel of fractions `⊙_S A = (A × A)/≡_S` is a `Wheel`
for any commutative ring `A` and multiplicative submonoid `S` — sorry-free and
`Classical.choice`-free (`[propext, Quot.sound]`). The porthole `∞ ≠ ⊥` is
`inf_ne_bot` (given `0 ∉ S`). The ZP `Wheel` typeclass is a faithful encoding of
Carlström's Definition 1.1 (all eight axioms, with his two commutative-monoid axioms unbundled
into 14 equational fields), so this is Carlström's wheel-of-fractions theorem, machine-verified —
the Tier 3 universality result previously scoped as a substantial, non-near-term target.
-/

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
-- § VII-b NO-GO gauge. All three are axiom-free; the § VII-b footprint block's claim is checked here
-- rather than asserted, which is the whole point of the correction recorded there.
#print axioms degenerateWVS
#print axioms wheelValuationStructure_always_inhabited
#print axioms degenerateWVS_not_nondegenerate
end PurityCheck

end ZeroParadox
