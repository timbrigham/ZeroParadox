import ZeroParadox.Ordinal.SnapNucleusConstructive
import Mathlib.SetTheory.Ordinal.Veblen

set_option maxHeartbeats 1000000

/-!
# A priced interface: a carrier sized to ε₀, a map into `Ordinal`, and both sides' axiom footprints

## What this file is

A **measurement**, not a construction. The carrier below and the map out of it are both instances of
constructions that already exist in the literature (see "Prior art" — they are Castéran's, and the
citation is not a courtesy). What is being contributed here is the *price tag*: the axiom footprint of
each side of the constructive/classical boundary, exhibited on declarations that sit on either side of a
single named map, in a setting where the classical target is a real library type (Mathlib's `Ordinal`)
rather than an axiomatized module.

## Why this file exists — a correction of record

ZP-N v1.0 states as its headline finding that ZP-L's `Classical.choice` at ε₀ is "representational, not
intrinsic," justified by ZP-L working in Mathlib's `Ordinal` type, "which is choice-saturated." **Both
halves are wrong.**

The justification is false as measured: `#print axioms Ordinal` reports `[propext, Quot.sound]` — there
is no choice in the type. And the conclusion overreaches its evidence by one step: everything ZP-N proved
choice-free (`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`) is a fact about the *ascent*, while ε₀ is
the supremum the notation system provably cannot name (`no_snap_closure`,
`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`).

Worse, the claim was **not measurable by the instrument used to support it.** `Classical.choice` sits in
the `Ordinal.partialOrder` *instance term*, so every statement mentioning that order inherits it however
it is proved — `a ≤ a` carries choice while `a = a` does not
(`order_footprint_is_uninformative`, `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`). Axiom footprints
on ε₀ results measure the ambient instance, not the proofs.

This file replaces the unanswerable question with a measurable one: not *is the choice real*, but *what
does crossing cost*.

## The measured price of the crossing

Measured by `#print axioms` (the purity check at the bottom of this file is the instrument; these are
the numbers it reported, not the numbers that were hoped for):

* **Constructive side — choice-free, but not uniformly `[propext]`.**
  `E0Note` and `e0Coe` report **no axioms at all**. `e0DecidableEq`, `e0OmegaPow`, `e0OmegaPow_top`,
  `e0OmegaPow_coe` and `e0OmegaPow_fixedpoint_iff` report `[propext]`. `e0DecidableLE`,
  `e0DecidableLT`, `e0Coe_lt_top` and `e0_le_top` report `[propext, Quot.sound]`.
* **The map — `Classical.choice`.** `repr_lt_epsilon0`, `e0Repr`, `e0Repr_top`, `e0Repr_coe`,
  `e0Repr_le_epsilon0`, `e0Repr_eq_epsilon0_iff` and `e0Repr_not_injective` all report
  `[propext, Classical.choice, Quot.sound]`.

**The `Quot.sound` on part of the constructive side was not predicted, and is reported rather than
explained away.** It arrives through Mathlib's `WithTop` order lemmas, not through anything about
ordinals; it is *not* `Classical.choice`, and the constructive side carries no choice anywhere. The
prediction that the whole carrier side would come out at exactly `[propext]` was wrong, and the
measurement, not the prediction, is what stands.

So the boundary is *priced*: staying on the notation side costs at most `[propext, Quot.sound]` and
never `Classical.choice`; crossing to `Ordinal` costs `Classical.choice` at every declaration; and the
crossing is one named map rather than a diffuse correspondence.

**What that measurement does and does not license.** It locates where the classical assumption is paid
on this pair of carriers. It does **not** show that Mathlib's ε₀ results are eliminable — that would
require re-proving them, on this carrier, and no such re-proof exists here or anywhere in this
repository. This is the same limit `ZeroParadox/Ordinal/SyntacticCollapse.lean` records. The honest
sentence remains: *the ε₀ results borrow a tool far stronger than they need.* Note also the standing
caveat from `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` — `Classical.choice` sits in
`Ordinal`'s order *instance term*, so a choice footprint on any `Ordinal`-mentioning statement is
partly an artifact of the ambient instance rather than of the proof. The measurement below is a
measurement of the interface, not a verdict on any particular proof's essential needs.

## The carrier, and what it actually is

`E0Note := WithTop SynONote` — Mathlib's ordinal notations under the choice-free comparator order
(`SynONote`, built in `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` from `ONote.cmp` directly,
because Mathlib's own `Preorder ONote` is `repr`-routed and would drag `Ordinal`'s order instance in),
with a single point adjoined above everything.

**`E0Note` is a notation system for ε₀ + 1, not for ε₀.** Its points denote the ordinals strictly below
ε₀ *together with* ε₀ itself, so as a notation system it names the segment below ε₀ + 1. Stating it as
"a constructive carrier for ε₀" would be wrong on the arithmetic and wrong on the credit.

**The standard alternative is to step up the notation system rather than adjoin a top.** In a
Veblen-style system, ε₀ = φ(1,0) is an ordinary term, named without any ad-hoc extremum; hydra-battles
ships such a system. That is the better-known and arguably cheaper route. The only honest advantage of
the adjoined top is engineering: it is minimal, and it leaves `ONote.cmp` completely untouched, so the
constructive side's footprint is inherited rather than re-established.

## The closure at the top is STIPULATED, not discovered

`e0OmegaPow ⊤ = ⊤` holds **by definition**. The tower operator is *defined* to fix the adjoined point;
nothing forced it, nothing discovered it, and no obstruction was defeated by it. The one non-trivial
half is the *uniqueness*: `e0OmegaPow_fixedpoint_iff` shows ⊤ is the **only** fixed point, and that half
is real — it is `omegaPow_ne_self` doing the work below the top. So the honest split is: **existence of
the fixed point is by fiat at the added point; uniqueness is a theorem.**

**This is not in tension with `no_snap_closure`.** That result
(`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`) says no idempotent endomap of `ONote` has
ε-number closed points, and it is fenced there — explicitly, in that file's own header — to
`ONote`-shaped notation systems, for exactly this reason. `E0Note` is not `ONote`: it has an extra
point, and the fixed point lives at that extra point. Neither file's claim reaches the other's carrier,
and neither should be read as weakening the other. `no_snap_closure` remains exactly as strong as it
was, on exactly the carrier it was stated for.

## What is NOT proved here, and must not be inferred

`ON_correct` (Castéran; see below) asks three things of a denotation map: that every notation denotes
below the target ordinal, that the map is **onto** the segment below it, and that the syntactic
comparator **agrees** with the semantic order. Only the first is proved here (`repr_lt_epsilon0`,
lifted to `e0Repr_le_epsilon0`).

The other two **fail on this carrier as stated**, and that is a fact about raw `ONote`, not an
omission: `e0Repr_not_injective` below exhibits two distinct notations with the same denotation, so
the comparator cannot agree with the semantic order on raw syntax. Mathlib's positive counterpart
(`ONote.repr_inj`) requires the `NF` normal-form predicate on both arguments — and `NF` is itself
defined through `repr`, which is why the constructive development here stays off it. So: **`E0Note` is
not claimed to be `ON_correct` at ε₀ + 1.** Restricting to normal forms is the standard fix and is not
done here.

## Triviality assessment

The carrier is an `abbrev`. The order, the decidability instances, and the lattice structure are all
inherited from Mathlib's `WithTop` instances applied to an order built in a sibling file — this file
proves none of that and should get no credit for it. `e0OmegaPow_top` is `rfl`. `e0Repr_top` is `rfl`.

Two things here are not free. `repr_lt_epsilon0` — every raw notation denotes strictly below ε₀ — is a
short structural induction, but it does need the right closure facts about ε₀ (additive and
multiplicative principality, both obtained from `ω ^ ε₀ = ε₀`), and it is stated for **all** of `ONote`,
including non-normal forms, where Mathlib's own machinery does not directly apply.
`e0OmegaPow_fixedpoint_iff` is the uniqueness half discussed above. Neither is deep.

The measurement itself is arithmetically trivial — it is a `#print axioms` block. Its value, if any, is
that it is *stated as a price* on a specific named map, rather than left as a general impression that
"the ordinal side is classical." That is a difference in bookkeeping, not in mathematics.

## Prior art — the construction is not ours

**Castéran and Contejean, *hydra-battles* (rocq-community/hydra-battles), is the source of both halves.**

* **The carrier.** `theories/ordinals/OrdinalNotations/ON_plus.v` builds the **sum of two ordinal
  notation systems** — `t := (A + B)`, everything in `A` below everything in `B`, with the comparator
  `compare_plus`, its correctness `plus_comp`, well-foundedness `lt_wf`, the resulting instance
  `ON_plus`, and crucially `lt_eq_lt_dec` proving that **decidability of comparison is preserved,
  generically**. `E0Note` is that construction instantiated with a one-point right summand. Castéran
  does not name the `+1` case separately, but the construction and the decidability-preservation lemma
  are his, and they are more general than what is used here. The abstraction being instantiated,
  `Class ON` (`ON_Generic.v`) — a well-founded ordered datatype with a comparison function — is
  published. Mathlib's `WithBot`/`WithTop` decidability and lattice instances
  (`Mathlib/Order/WithBot.lean`) are the same move at instance level, and are what this file actually
  calls.
* **The map.** The canonical name for "a notation system correctly denotes into a classical ordinal"
  is **`ON_correct`** (`ON_Generic.v`), with the three fields listed above. It is **already
  instantiated at ε₀**: `theories/ordinals/Schutte/Correctness_E0.v` builds `inject : T1 → Ord` with
  `inject_lt_epsilon0`, `embedding`, and `Instance Epsilon0_correct`. Our `e0Repr` is an instance of
  the same notion — Mathlib's `Ordinal` instead of Schütte's axiomatized `Ord`, Lean 4 instead of Coq,
  and, as fenced above, only the first of the three `ON_correct` fields established.
* **The price is priced there too.** hydra-battles is constructive except its Schütte module, which
  axiomatizes the classical countable ordinals — so `inject` is exactly where the classical assumptions
  are paid in that development, and the library localizes them there by design. The measurement below
  is the same observation, relocated to a library whose classical target is a constructed type rather
  than an axiom module.

**Mathlib states the same split in its own words.** The docstring of `NONote.repr`
(`Mathlib/SetTheory/Ordinal/Notation.lean`): *"This function is noncomputable because ordinal arithmetic
is noncomputable. In computational applications `NONote` can be used exclusively without reference to
`Ordinal`, but this function allows for correctness results to be stated."* That is the
constructive-side/classical-side interface, its purpose, and its price, stated by the library.

**Also in the neighbourhood, named but not described:** the `gaia-hydras` package bridges Grimm's Gaia
(classical, EM + AC) to hydra-battles' constructive notations — a second and larger instance of the same
interface. Its internals are not read here and nothing about them is claimed.

`ONote`, `ONote.cmp`, `ONote.repr`, `WithTop` and its instances, `Ordinal.epsilon`,
`isPrincipal_add_omega0_opow` and `isPrincipal_mul_omega0_opow_opow` are all Mathlib. `SynONote` and
its `LinearOrder` are from `ZeroParadox/Ordinal/SnapNucleusConstructive.lean`, and are themselves a
re-derivation of hydra-battles' `T1.v` order construction, as that file records.

**The "two faces of one interface" framing is our presentation, not a discovered correspondence.** The
framework pairs a logic-side modality (`dnegNucleus`, `ZeroParadox/Category/DoubleNegationNucleus.lean`
— the double-negation nucleus) with the carrier-side map here, and presents the two as two faces of one
constructive/classical boundary. A prior-art search for that pairing returned **"searched, none found."**
Each half is separately canonical — the ¬¬-translation is Gödel–Gentzen–Kolmogorov, with Glivenko's
variant and the CPS transform under Curry–Howard as its recognized computational reading; the
carrier-side map is `ON_correct` / `repr` per above. **The pairing is a presentational choice of ours.**
No theorem here relates the two faces, and none is claimed.

## Engineer's Take

If ZP-N is unclassified, we should reevaluate the Lean and see if we can get it right before bumping the
version.

I was hoping this was one of those cases where you take the entire class and make it an instance of that,
the same as we have for other solutions where the scope was one order of magnitude too high or too low.
In programming terms it is the initialization of a class you did not need.

The idea is to build it using this framework and then cross reference it to the more general category.
That looks like an interface between constructive and choice based logic, and that in itself is valuable
even if it means going single instance versus general. I think that is exactly how this interface is
going to have to work.
-/

namespace ZeroParadox

open Ordinal

/-! ### The carrier

`SynONote` with one point adjoined on top. An instance of Castéran's `ON_plus` (sum of notation
systems) with a one-point right summand; the order, lattice and decidability structure below is all
Mathlib's `WithTop` machinery, not built here. -/

/-- **The carrier: ordinal notations with a single adjoined top.**

`⊤` is the intended denotation site for ε₀, and `e0Repr` sends it there. Everything below `⊤` is an
ordinal notation carrying the choice-free comparator order of `SynONote`.

As a notation system this names the ordinals below **ε₀ + 1** (the segment below ε₀, plus ε₀ itself) —
it is not a notation system for ε₀. -/
abbrev E0Note : Type := WithTop SynONote

/-- The notations, viewed inside the carrier. -/
def e0Coe (x : ONote) : E0Note := (toSyn x : SynONote)

/-- Comparison on the carrier is decidable — inherited from Mathlib's `WithTop.decidableLE` applied to
the comparator-derived order on `SynONote`. This is Castéran's `lt_eq_lt_dec` (decidability survives
adjunction) at instance level; nothing is proved here. -/
@[reducible] def e0DecidableLE : DecidableLE E0Note := inferInstance

/-- Strict comparison on the carrier is decidable. -/
@[reducible] def e0DecidableLT : DecidableLT E0Note := inferInstance

/-- Equality on the carrier is decidable. -/
@[reducible] def e0DecidableEq : DecidableEq E0Note := inferInstance

/-- Every notation sits strictly below the adjoined top. -/
theorem e0Coe_lt_top (x : ONote) : e0Coe x < (⊤ : E0Note) := WithTop.coe_lt_top _

/-- The adjoined top bounds the whole carrier. -/
theorem e0_le_top (a : E0Note) : a ≤ (⊤ : E0Note) := le_top

/-! ### The tower operator, and the stipulated fixed point

`e0OmegaPow` extends `omegaPow` by *defining* it to fix `⊤`. The fixed point exists by that definition.
Only its uniqueness is a theorem. -/

/-- **The tower operator on the carrier.** Below the top it is `omegaPow`; at the top it is **defined**
to be the identity.

The value at `⊤` is a stipulation. It is not derived, not forced, and defeats no obstruction. -/
def e0OmegaPow : E0Note → E0Note :=
  WithTop.recTopCoe ⊤ fun x => ((toSyn (omegaPow (ofSyn x)) : SynONote) : E0Note)

/-- **The fixed point, by definition.** `⊤` is fixed because `e0OmegaPow` was written that way. -/
@[simp] theorem e0OmegaPow_top : e0OmegaPow ⊤ = ⊤ := rfl

/-- Below the top, the tower operator is the syntactic `omegaPow`. -/
@[simp] theorem e0OmegaPow_coe (x : ONote) :
    e0OmegaPow (e0Coe x) = e0Coe (omegaPow x) := rfl

/-- **Uniqueness of the fixed point — this half is a theorem.** `⊤` is the *only* fixed point of
`e0OmegaPow`, because below the top `omegaPow` moves everything (`omegaPow_ne_self`).

Read together with `e0OmegaPow_top`: existence is by fiat at the adjoined point, uniqueness is proved. -/
theorem e0OmegaPow_fixedpoint_iff (a : E0Note) : e0OmegaPow a = a ↔ a = ⊤ := by
  constructor
  · induction a using WithTop.recTopCoe with
    | top => intro _; rfl
    | coe x =>
        intro h
        have h' : (toSyn (omegaPow (ofSyn x)) : SynONote) = x := WithTop.coe_injective h
        exact absurd h' (omegaPow_ne_self (ofSyn x))
  · rintro rfl; rfl

/-! ### The map into `Ordinal` — the crossing

This is where the classical assumption is paid. `ONote.repr` is Mathlib's denotation map, and it is
`noncomputable` there for exactly the reason its docstring gives. -/

/-- **Every ordinal notation denotes strictly below ε₀.**

The first of `ON_correct`'s three fields (Castéran, `ON_Generic.v`), here for Mathlib's `ONote` and
Mathlib's ε₀. Structural induction: ε₀ is a fixed point of `ω ^ ·`, hence both additively and
multiplicatively principal, which is exactly what closes the `oadd` case.

Stated for **all** of `ONote`, including notations not in normal form. -/
theorem repr_lt_epsilon0 : ∀ x : ONote, ONote.repr x < ε₀ := by
  have hfp : ω ^ ε₀ = ε₀ := omega0_opow_epsilon 0
  have hadd : IsPrincipal (· + ·) ε₀ := by
    have := isPrincipal_add_omega0_opow ε₀
    rwa [hfp] at this
  have hmul : IsPrincipal (· * ·) ε₀ := by
    have := isPrincipal_mul_omega0_opow_opow ε₀
    rwa [hfp, hfp] at this
  intro x
  induction x with
  | zero => simp
  | oadd e n a ihe iha =>
      have hpow : ω ^ ONote.repr e < ε₀ := by
        rw [← hfp]
        exact (opow_lt_opow_iff_right one_lt_omega0).2 ihe
      have hn : ((n : ℕ) : Ordinal) < ε₀ := natCast_lt_epsilon n 0
      have hmulp : ω ^ ONote.repr e * ((n : ℕ) : Ordinal) < ε₀ := hmul hpow hn
      simpa using hadd hmulp iha

/-- **The crossing.** The carrier's denotation map into Mathlib's classical `Ordinal`: notations go by
`ONote.repr`, and the adjoined top goes to ε₀.

An instance of Castéran's `ON_correct` shape (`Schutte/Correctness_E0.v` is the existing ε₀
instantiation), with Mathlib's constructed `Ordinal` as the classical target instead of Schütte's
axiomatized `Ord`. Only the "denotes below the target" field is established here — see the header for
what fails and why. -/
noncomputable def e0Repr : E0Note → Ordinal :=
  WithTop.recTopCoe ε₀ fun x => ONote.repr (ofSyn x)

/-- The adjoined top denotes ε₀. -/
@[simp] theorem e0Repr_top : e0Repr ⊤ = ε₀ := rfl

/-- Notations denote by Mathlib's `ONote.repr`. -/
@[simp] theorem e0Repr_coe (x : ONote) : e0Repr (e0Coe x) = ONote.repr x := rfl

/-- The whole carrier denotes at or below ε₀. -/
theorem e0Repr_le_epsilon0 (a : E0Note) : e0Repr a ≤ ε₀ := by
  induction a using WithTop.recTopCoe with
  | top => exact le_rfl
  | coe x => exact (repr_lt_epsilon0 (ofSyn x)).le

/-- **ε₀ is denoted by the adjoined point and by nothing else.** The fibre of the map over ε₀ is
exactly `{⊤}` — which is the precise sense in which "the top is ε₀". -/
theorem e0Repr_eq_epsilon0_iff (a : E0Note) : e0Repr a = ε₀ ↔ a = ⊤ := by
  constructor
  · induction a using WithTop.recTopCoe with
    | top => intro _; rfl
    | coe x => intro h; exact absurd h (repr_lt_epsilon0 (ofSyn x)).ne
  · rintro rfl; rfl

/-- **The fence: the map is not injective, so this carrier is NOT `ON_correct` at ε₀ + 1.**

`ON_correct` additionally requires the map to be onto the segment below the target and the syntactic
comparator to agree with the semantic order. Both fail on raw `ONote`, because distinct notations that
are not in normal form can denote the same ordinal — `1 + ω` and `ω` are the smallest witness (the
same one used by `mathlib_ONote_order_not_antisymm` in
`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`).

Restricting to `NF` notations is the standard repair and is **not** performed here; `NF` is defined
through `repr` and would import the choice-carrying side into the constructive development. -/
theorem e0Repr_not_injective : ¬ Function.Injective e0Repr := by
  intro hinj
  obtain ⟨x, y, hne, hrepr⟩ := mathlib_ONote_order_not_antisymm
  exact hne (congrArg ofSyn (WithTop.coe_injective (hinj (a₁ := e0Coe x) (a₂ := e0Coe y) hrepr)))

end ZeroParadox

/-! ## Axiom Purity Check — this block IS the deliverable

The two sides of the interface, measured. Observed: the carrier side is choice-free, ranging from no
axioms at all up to `[propext, Quot.sound]`; the map side is uniformly
`[propext, Classical.choice, Quot.sound]`. The header's "measured price of the crossing" section
reports the per-declaration numbers. If this block ever prints something different, the header is wrong
and must be corrected to match the instrument — the instrument is the deliverable. -/

section PurityCheck
open ZeroParadox

-- Constructive side: the carrier, its decidable order, and the tower operator on it.
#print axioms E0Note
#print axioms e0Coe
#print axioms e0DecidableLE
#print axioms e0DecidableLT
#print axioms e0DecidableEq
#print axioms e0Coe_lt_top
#print axioms e0_le_top
#print axioms e0OmegaPow
#print axioms e0OmegaPow_top
#print axioms e0OmegaPow_coe
#print axioms e0OmegaPow_fixedpoint_iff

-- The crossing, and statements mentioning `Ordinal`'s order. This is where the price is paid.
#print axioms repr_lt_epsilon0
#print axioms e0Repr
#print axioms e0Repr_top
#print axioms e0Repr_coe
#print axioms e0Repr_le_epsilon0
#print axioms e0Repr_eq_epsilon0_iff
#print axioms e0Repr_not_injective
end PurityCheck
