import ZeroParadox.Ordinal.SnapNucleusConstructive
import ZeroParadox.Information.Surprisal
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
intrinsic," justified by ZP-L working in Mathlib's `Ordinal` type, "which is choice-saturated." **The
justification is false and the conclusion is unsupported.**

The justification is false as measured: `#print axioms Ordinal` reports `[propext, Quot.sound]` — there
is no choice in the type. And the conclusion overreaches its evidence by one step: everything ZP-N proved
choice-free (`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`) is a fact about the *ascent*, while ε₀ is
past what the notation system can name (`tower_cofinal`,
`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`). Note the weaker verb: the ε₀ results' status is
**unclassified**, not refuted — no choice-free re-proof was located either way as of 2026-08-02.

Worse, the claim was **not measurable by the instrument used to support it.** `Classical.choice` sits in
the `Ordinal.partialOrder` *instance term*, so every statement mentioning that order inherits it however
it is proved — `a ≤ a` carries choice while `a = a` does not (`order_footprint_le` and
`order_footprint_eq`, `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`, stated as two theorems
precisely so that file's purity block *prints* the contrast rather than asserting it). Axiom footprints
on ε₀ results measure the ambient instance, not the proofs.

This file replaces the unanswerable question with a measurable one: not *is the choice real*, but *what
does crossing cost*.

## The measured price of the crossing

Measured by `#print axioms` (the purity check at the bottom of this file is the instrument; these are
the numbers it reported, not the numbers that were hoped for):

⚠ **The per-declaration numbers are NOT reproduced here.** An earlier draft listed every name against
its footprint; the list then went stale the moment two declarations were added, which is this project's
most reliably recurring defect. **The block at the bottom of this file is the register — read it, do
not copy it.** What is stated here is only the shape it prints, which is the finding:

* **Constructive side — choice-free, and not uniformly `[propext]`.** Footprints range from **no axioms
  at all** (the carrier and its coercion) up through `[propext]` to `[propext, Quot.sound]`. No
  declaration on this side carries `Classical.choice`.
* **The map — `Classical.choice`, uniformly.** Every declaration **in the block below** whose statement
  mentions `Ordinal` reports `[propext, Classical.choice, Quot.sound]`, with no exceptions and no
  gradation among them. ⚠ **Scoped to this block on purpose, and an earlier draft was not.** It is not
  a fact about `Ordinal`-mentioning statements in general: `order_footprint_eq : ∀ (a : Ordinal), a = a`
  measures `[propext, Quot.sound]`, and this file cites that very theorem 20 lines above. Mentioning
  `Ordinal` is not what costs choice; reaching its **order instance** is.
* **⚠ `exists_fiber_supported_non_pure_pmf` is not evidence about the crossing.** It prints the same
  footprint, but so does `not_pure_of_two_support` — a PMF lemma with no `Ordinal` in its statement at
  all. **Measured**, and that measurement is the exhibited witness the claim needs: its choice is
  inherited from Mathlib's PMF layer and would be there with or without the crossing. It is printed here because this is where it is proved.
  ⚠ **This does NOT extend to `repr_collision`, and a first draft of this bullet swept it in by calling
  both "the two PMF declarations".** `repr_collision` contains no `PMF` in its statement or its proof —
  it is `e0Repr_not_injective` plus `Function.not_injective_iff`. It is a **crossing** declaration, it
  belongs exactly where the block files it, and it prices the crossing like every other one.

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
require re-proving them, on this carrier, and no such re-proof was present in this
repository as of 2026-08-02. This is the same limit `ZeroParadox/Ordinal/SyntacticCollapse.lean` records. The honest
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
through `repr` and would import the choice-carrying side into the constructive development.

⚠ **AND THE SAME FACT READS THE OTHER WAY — added 2026-08-05 (Tim).** A failure of faithfulness is an
availability of **uncertainty**. The fiber this non-injectivity creates — two notations, one denotation —
carries a genuinely non-degenerate distribution (`repr_collision`,
`exists_fiber_supported_non_pure_pmf` below).

⚠ **State the fiber's role correctly; a first draft did not.** It is NOT that the fiber "lifts
`pmf_subsingleton_isPure`'s obstruction" — `E0Note` is already non-subsingleton (`⊤` and `e0Coe 0`
differ), so that obstruction was **never binding here**. What the collision supplies is the strictly
stronger fact: a spread distribution **confined to a single denotation**. Any two distinct notations
give a non-degenerate distribution; only a *collision* gives one whose entire support denotes one
ordinal.

**AND THE COLLISION IS NECESSARY — measured, not assumed.**
`confined_non_pure_refutes_injective` (`ZeroParadox/Information/Surprisal.lean`) proves the converse:
under an *injective* map a confined distribution collapses to one support point, so a spread one
refutes injectivity outright. Measured at round-3 revalidation, after the sentence had been re-worded
three times without anyone asking whether the claim underneath was true.

**The IN-FIELD name is already in this file, 250 lines above: `ONote.repr_inj`.** Mathlib's
`ONote.repr_inj` (`Mathlib/SetTheory/Ordinal/Notation.lean`) requires `NF` on both arguments, and this
file's § *What is NOT proved here* already says *"restricting to normal forms is the standard fix."*
That is **stronger** than naming the defect: it characterizes exactly when injectivity is **restored**,
and the `1 + ω` vs `ω` witness is precisely a non-normal-form term. Use it first.

`Reading:` (conjectural, and **an earlier draft asserted this as a flat identification, which was an
over-reach**) the framework reads the fiber as an instance of the **shape** that statistics calls
*identifiability* — the parameter-to-observable map failing to be injective. ⚠ **Do not write
"structural identifiability" for this.** Both sources on disk (Villaverde 2016; Castro & de Boer 2020,
`.claude-local/papers/`) scope that term to **parametrized dynamic models**, where "structural"
contrasts with *practical* identifiability limited by data. `e0Repr` has no data, no dynamics and no
such contrast, so the modifier does no work here. And `CLAIMS.md`'s use of the term is about **ZP-B's
real-valued threshold** under Buckingham π — a different object, and that row's own 2026-07-30 scope
correction states the term does *not* apply to ε₀ — so "it had never reached the Lean" claims a
continuity that is not there.

**NO POV KIND is claimed here, and that is deliberate** — none of the five (COINCIDENCE / INVERSION /
DRIFT / CARRIER / INVARIANT) describes "two structures share a shape". What is asserted is only the
**shape**, never an instance-of relation, which is the same fence this project keeps for the min≡max
family (whose own coincidences are separately labelled where they live). Citing that fence here is a
pointer to the precedent, not a POV claim about `e0Repr`.

`Reading:` (conjectural) the framework reads this as where statistics enters, under Tim's framing that
**succession is a state of representation**: what is uncertain is *which representation*, never *what
happened*. ⚠ **Nothing here posits that anything moved** — the no-traversal commitment is untouched, and
the distribution below is over notations, not over histories. Long form:
`.claude-local/notes/future-research/offset_from_the_origin_2026-08-05.md`. -/
theorem e0Repr_not_injective : ¬ Function.Injective e0Repr := by
  intro hinj
  obtain ⟨x, y, hne, hrepr⟩ := mathlib_ONote_order_not_antisymm
  exact hne (congrArg ofSyn (WithTop.coe_injective (hinj (a₁ := e0Coe x) (a₂ := e0Coe y) hrepr)))


/-- **`Statement:` the fiber, exhibited.** Two distinct notations with one denotation — the unfolding of
`e0Repr_not_injective`, with `1 + ω` and `ω` as the underlying witness. -/
theorem repr_collision : ∃ x y : E0Note, x ≠ y ∧ e0Repr x = e0Repr y := by
  have h := e0Repr_not_injective
  rw [Function.not_injective_iff] at h
  obtain ⟨x, y, heq, hne⟩ := h
  exact ⟨x, y, hne, heq⟩

/-- **`Statement:` a non-degenerate distribution confined to a SINGLE fiber.** There is an ordinal `o`
and a distribution on notations which is **not** a point mass, yet **every** notation in its support
denotes `o`. Uncertainty about the representation; none whatsoever about the object.

Assembled from `repr_collision` (the fiber, new here), `exists_spread_pmf` (new, in
`ZeroParadox/Information/Surprisal.lean`), and `not_pure_of_two_support` (**pre-existing** in that same
file, cited rather than re-proved).

⚠ **Do not read this as a distribution over pasts.** The support is a set of *notations*; the theorem
says they are indistinguishable by `e0Repr`, not that one preceded another. -/
theorem exists_fiber_supported_non_pure_pmf :
    ∃ (o : Ordinal) (p : PMF E0Note),
      (∀ a, p ≠ PMF.pure a) ∧ ∀ x ∈ p.support, e0Repr x = o := by
  obtain ⟨x, y, hne, hxy⟩ := repr_collision
  obtain ⟨p, hx, hy, hsub⟩ := exists_spread_pmf x y
  refine ⟨e0Repr x, p, not_pure_of_two_support hx hy hne, ?_⟩
  intro z hz
  rcases hsub hz with rfl | hz'
  · rfl
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz', ← hxy]

/-- **`Statement:` the round trip closes.** `e0Repr_not_injective` — the fence this section is built on
— is **round-tripped** through the statistical side: take the collision, spread a distribution across it,
observe that the distribution is confined to one denotation, and `confined_non_pure_refutes_injective`
returns the non-injectivity.

**Why this exists (round-4 gate finding).** The necessity theorems were stated and never *applied*, and
an unapplied theorem is one whose non-vacuity nobody has exercised. This composition exercises it: the
implication runs both ways, so the identification of "failure of faithfulness" with "room for a
confined distribution" is not an interpretation laid over the theorems — it is a round trip through
them. ⚠ **This consumes its own conclusion and is not an independent second proof** — `repr_collision` is
itself derived from `e0Repr_not_injective`. What it establishes is exactly that the converse's
hypotheses are **satisfiable at a concrete `f`**, and nothing further about `e0Repr`. Recorded as
next-touch debt: an `example` would exercise that identically without minting a second citable
`theorem` whose statement duplicates one already in this file. -/
theorem e0Repr_not_injective_via_confinement : ¬ Function.Injective e0Repr := by
  obtain ⟨x, y, hne, hxy⟩ := repr_collision
  obtain ⟨p, hx, hy, hsub⟩ := exists_spread_pmf x y
  refine confined_non_pure_refutes_injective e0Repr p (e0Repr x) ?_ ⟨x, hx, y, hy, hne⟩
  intro z hz
  rcases hsub hz with rfl | hz'
  · rfl
  · rw [Set.mem_singleton_iff] at hz'
    rw [hz', ← hxy]

/-! ### Where the ambiguity ISN'T — both poles are faithful

**Origin (Tim, 2026-08-06): "almost like the roles of zero and infinity are reversed."** Chasing that
gave a result neither of us predicted: the representation map is injective **at both ends** and
ambiguous only in between.

**The polarity contrast, which is what his reading names.** Put these beside complexity, which the
corpus already pins in the other direction: `infinitude_forces_infinite_complexity`
(`ZeroParadox/Valuation/InfinitudeFloor.lean`) puts complexity at the top of its range **at the
floor**, while `member_cx_lt_top` keeps every member finite. So at the bottom, complexity is maximal
and representational ambiguity is minimal — **the same point is extremal in both measures, in
opposite directions.**

`Reading:` **DRIFT kind** (conjectural) — two measures running opposite along one structure, the same
shape as `pole_inversion` (`ZeroParadox/Valuation/InfinitudeFloor.lean`) but a **different pair**. It
is a shared shape, never an instance-of relation.

⚠ **THREE FENCES, because two of these results are easy to oversell.**
1. **No monotonicity is proved.** What is established is the two endpoint values plus one positive
   instance in between (`repr_collision`, at `ω`). *"Ambiguity grows as you ascend"* is **not** proved
   and should not be written; fibers are not monotone in the ordinal.
2. **The top result is partly structural.** `⊤` is *adjoined*, so there is exactly one of it by
   construction; that half leans on the construction as much as on `repr_lt_epsilon0`. The bottom
   result is the earned one — it needs a positivity argument and holds **without** normal form, so
   uniqueness at zero is not bought by restricting the syntax (contrast `ONote.repr_inj`, which needs
   `NF` on both arguments).
3. **This closes a door.** Because the fiber at the bottom is a single point, the statistics of the
   section above lives **strictly between** the poles and cannot be seeded at the bottom by this
   route. -/

/-- **`Statement:` zero is uniquely denoted, and NO normal-form hypothesis is needed.** Structural:
`repr (oadd e n a) = ω ^ repr e * n + repr a` with `n ≥ 1`, so it is strictly positive.

**Prior art:** Mathlib's `ONote.repr_inj` (`Mathlib/SetTheory/Ordinal/Notation.lean`) gives injectivity
but requires `NF` on both arguments; no `repr = 0` characterization was located in the pin as of
`9dffe26`. This is the one point where faithfulness is free. -/
theorem onote_repr_eq_zero_iff (x : ONote) : x.repr = 0 ↔ x = 0 := by
  constructor
  · intro h
    cases x with
    | zero => rfl
    | oadd e n a =>
      exfalso
      rw [ONote.repr] at h
      have hmul := Ordinal.left_eq_zero_of_add_eq_zero h
      rcases mul_eq_zero.mp hmul with hz | hz
      · exact absurd hz (Ordinal.opow_pos _ Ordinal.omega0_pos).ne'
      · have : (n : ℕ) = 0 := by exact_mod_cast hz
        exact absurd this n.pos.ne'
  · rintro rfl; rfl

/-- **`Statement:` the fiber over the BOTTOM is a singleton.** Zero representational ambiguity at the
floor. The adjoined top is excluded because it denotes the top value, which is
strictly positive — by Mathlib's own `Ordinal.epsilon_pos` (`Mathlib/SetTheory/Ordinal/Veblen.lean`),
adopted rather than routing through the corpus's `epsilon0_ne_zero` canary, which would have cost an
import for a fact the library already states. -/
theorem e0Repr_fiber_at_bot_singleton :
    {x : E0Note | e0Repr x = 0} = {e0Coe 0} := by
  ext x
  constructor
  · intro hx
    induction x using WithTop.recTopCoe with
    | top => exact absurd hx (Ordinal.epsilon_pos 0).ne'
    | coe y =>
      simp only [Set.mem_setOf_eq, e0Repr] at hx
      simp only [Set.mem_singleton_iff, e0Coe]
      congr 1
      have := (onote_repr_eq_zero_iff (ofSyn y)).mp hx
      rw [← this]; rfl
  · rintro rfl; rfl

/-- **`Statement:` the fiber over the TOP is a singleton too.** Every notation denotes strictly below
it (`repr_lt_epsilon0`), so only the adjoined point lands there. See fence 2 above: this half is
partly by construction. -/
theorem e0Repr_fiber_at_top_singleton :
    {x : E0Note | e0Repr x = Ordinal.epsilon 0} = {(⊤ : E0Note)} := by
  ext x
  constructor
  · intro hx
    induction x using WithTop.recTopCoe with
    | top => rfl
    | coe y =>
      exfalso
      have hx' : (ofSyn y).repr = Ordinal.epsilon 0 := hx
      exact absurd hx' (ne_of_lt (repr_lt_epsilon0 (ofSyn y)))
  · rintro rfl
    exact e0Repr_top

end ZeroParadox

/-! ## Axiom Purity Check — this block IS the deliverable

The two sides of the interface, measured. Observed: the carrier side is choice-free, ranging from no
axioms at all up to `[propext, Quot.sound]`; the map side is uniformly
`[propext, Classical.choice, Quot.sound]`. **The per-declaration numbers live HERE and nowhere else** —
the header states only the shape, deliberately, because an enumeration duplicated into prose is what
went stale once already. If this block ever prints something outside the shape the header describes,
the header is wrong and must be corrected to match the instrument — the instrument is the
deliverable. -/

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
#print axioms repr_collision
#print axioms exists_fiber_supported_non_pure_pmf
#print axioms e0Repr_not_injective_via_confinement
#print axioms onote_repr_eq_zero_iff
#print axioms e0Repr_fiber_at_bot_singleton
#print axioms e0Repr_fiber_at_top_singleton

-- The ε₀-producing operations themselves, measured here because this file already imports Veblen.
-- ZP-N's prose names these (with `typein` and `omega0`, printed in
-- `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`) as where `Classical.choice` actually enters
-- Mathlib's ordinals. Printed rather than asserted: naming a site without measuring it is exactly
-- the error ZP-N v1.0 made, and a claim about where choice lives should be reproducible.
#print axioms Ordinal.nfp
#print axioms Ordinal.deriv
#print axioms Ordinal.epsilon
end PurityCheck
