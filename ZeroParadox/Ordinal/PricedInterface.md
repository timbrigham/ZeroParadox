# PricedInterface — ride-along documentation

Long form of `ZeroParadox/Ordinal/PricedInterface.lean`.

## What this file is

A **measurement**, not a construction. The carrier and the map out of it, declared in `ZeroParadox/Ordinal/PricedInterface.lean`, both follow
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
`ZeroParadox/Ordinal/SnapNucleusConstructive.lean`). What can be said instead: the ε₀ results, as stated, are
**STATEMENT-CARRIED** (statement control, measured 2026-10-08; `ZeroParadox/Category/ChoiceCannotBe.md`),
and whether a restatement on a choice-free carrier holds is open, not refuted.

Worse, the claim was **not measurable by the instrument used to support it.** `Classical.choice` sits in
the `Ordinal.partialOrder` *instance term*, so every statement written through that instance inherits it,
as written, however it is proved — `a ≤ a` carries choice while `a = a` does not (`order_footprint_le` and
`order_footprint_eq`, `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`, stated as two theorems
precisely so that file's purity block *prints* the contrast rather than asserting it). Axiom footprints
on ε₀ results measure the ambient instance, not the proofs.

This file replaces the unanswerable question with a measurable one: not *is the choice real*, but *what
does crossing cost*.

## The measured price of the crossing

Measured by `#print axioms` (the purity check at the bottom of `ZeroParadox/Ordinal/PricedInterface.lean` is the instrument):

⚠ **The per-declaration numbers are NOT reproduced here.** A copied list goes stale the moment a
declaration is added. **The block at the bottom of the `.lean` file is the register — read it, do
not copy it.** What is stated here is only the shape it prints, which is the finding:

* **Constructive side — choice-free, and not uniformly `[propext]`.** Footprints range from **no axioms
  at all** (the carrier and its coercion) up through `[propext]` to `[propext, Quot.sound]`. No
  declaration on this side carries `Classical.choice`.
* **The map — `Classical.choice`, uniformly.** Every declaration **in that block** whose statement
  mentions `Ordinal` reports `[propext, Classical.choice, Quot.sound]`, with no exceptions and no
  gradation among them. ⚠ **Scoped to this block on purpose.** It is not
  a fact about `Ordinal`-mentioning statements in general: `order_footprint_eq : ∀ (a : Ordinal), a = a`
  measures `[propext, Quot.sound]`, and § *Why this file exists* above cites that very theorem. Mentioning
  `Ordinal` is not what costs choice; reaching its **order instance** is.
* **⚠ `exists_fiber_supported_non_pure_pmf` is not evidence about the crossing.** It prints the same
  footprint, but so does `not_pure_of_two_support` — a PMF lemma with no `Ordinal` in its statement at
  all. **Measured**, and that measurement is the exhibited witness the claim needs: its choice is
  inherited from Mathlib's PMF layer and would be there with or without the crossing. It is printed in that block because `PricedInterface.lean` is where it is proved.
  ⚠ **This does NOT extend to `repr_collision`; the two are not both PMF declarations.**
  `repr_collision` contains no `PMF` in its statement or its proof —
  it is `e0Repr_not_injective` plus `Function.not_injective_iff`. It is a **crossing** declaration, it
  belongs exactly where the block files it, and it prices the crossing like every other one.

**The `Quot.sound` on part of the constructive side** arrives through Mathlib's `WithTop` order
instances and lemmas (`WithTop.instPreorder`, `WithTop.decidableLE`, `WithTop.decidableLT`,
`WithTop.instOrderTop`, `WithTop.coe_lt_top`, each `[propext, Quot.sound]`), not through anything
about ordinals: `SynONote`'s own order, `instLinearOrderSynONote`, measures `[propext]`. It is *not*
`Classical.choice`, and no declaration on the constructive side carries choice. The one proof here
that does is the `example` stating `¬ WellFoundedLT E0Note`, through `WellFounded.has_min`; its
statement does not.

So the boundary is *priced*: the notation side's declarations cost at most `[propext, Quot.sound]` and
never `Classical.choice`; crossing to `Ordinal` costs `Classical.choice` at every declaration; and the
crossing is one named map rather than a diffuse correspondence.

**What that measurement does and does not license.** It locates where the classical assumption is paid
on this pair of carriers. It does **not** show that Mathlib's ε₀ results are eliminable: as stated they
are STATEMENT-CARRIED, so no proof of them can drop the choice, and the open question is a restatement
on a choice-free carrier. Its state is in `ZeroParadox/Ordinal/SnapNucleus.md` § "Axiom footprint":
the ascent is restated; for the results that name ε₀, this file's carrier gives the defined reading
(the fixed point at ⊤ by definition, its uniqueness a theorem, on an order that is not well-founded),
and the derived reading is open there. This is the same limit `ZeroParadox/Ordinal/SyntacticCollapse.md` records. Scoped to
what is measured: *the ascent below ε₀ borrows a tool far stronger than it needs*, because its
counterpart on notations measures `[propext]`; whether the same holds for the results that name ε₀,
leastness included, on a carrier where the fixed point is derived, is the open question, not a
finding. Note also the standing caveat from
`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` — `Classical.choice` sits in `Ordinal`'s order
*instance term*, so a statement that reaches that instance carries the choice whatever its proof, and
a statement that mentions `Ordinal` without reaching it does not (`order_footprint_le` against
`order_footprint_eq`, as in § *The measured price* above). The purity block is a measurement of the
interface, not a verdict on any particular proof's essential needs.

## The carrier, and what it actually is

`E0Note := WithTop SynONote` — Mathlib's ordinal notations under the choice-free comparator order
(`SynONote`, built in `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` from `ONote.cmp` directly,
because Mathlib's own `Preorder ONote` is `repr`-routed and would drag `Ordinal`'s order instance in),
with a single point adjoined above everything.

**`E0Note` denotes the ordinals up to ε₀, and its own order is not a well-order.** Its points denote the
ordinals strictly below ε₀ *together with* ε₀ itself: the segment below ε₀ + 1. Its order is not well-founded:
on raw notations `oadd 0 1 x < x` holds at `x = ω` and at each later term of the chain ω, `oadd 0 1 ω`, …
(it fails at `x = 0` and `x = 1`), so that chain descends forever (the `example` stating
`¬ WellFoundedLT E0Note`). So it is not a notation system for ε₀ + 1 in the well-ordered sense, and stating it as
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
and neither should be read as weakening the other. `no_snap_closure` holds unweakened, on the carrier
it is stated for.

## What is NOT proved here, and must not be inferred

`ON_correct` (Castéran, `ON_Generic.v`; see below) is a class stated over an `ON`, a type with a
comparison whose order is well-founded (`Class ON`'s field `ON_wf`), together with a target ordinal
and a denotation map. Its three fields ask that every notation denotes below the target ordinal, that
the map is **onto** the segment below it, and that the syntactic comparator **agrees** with the
semantic order. `E0Note` is not an `ON` (§ *The carrier*), so the class does not apply to `e0Repr`;
what can be asked is which of the three properties the map has. The first is `repr_lt_epsilon0`, lifted to
`e0Repr_le_epsilon0`. The second holds: `repr_surj_below_epsilon0` gives every ordinal below ε₀ an
`NF` notation, so `e0Repr` is onto the ordinals at or below ε₀ (the `example` after
`e0Repr_eq_epsilon0_iff` in `ZeroParadox/Ordinal/PricedInterface.lean`).

The third **fails on this carrier as stated**, and that is a fact about raw `ONote`, not an
omission: `e0Repr_not_injective` exhibits two distinct notations with the same denotation, so
the comparator cannot agree with the semantic order on raw syntax (the `example` after
`e0Repr_not_injective`: two points strictly ordered in the carrier with equal denotations). Mathlib's positive counterpart
(`ONote.repr_inj`) requires the `NF` normal-form predicate on both arguments — and `NF` is itself
defined through `repr`, which is why the constructive development stays off it;
`repr_surj_below_epsilon0` uses `NF` on the crossing side only. So **`e0Repr` has the into and onto
properties, not the comparator property, and is not an `ON_correct` instance at ε₀ + 1**: the class
needs an `ON`, and the comparator property fails. Restricting to normal forms is the standard fix and
is not done here.

## Where the ambiguity isn't — faithful at 0 and at ε₀

**Origin (Tim): "almost like the roles of zero and infinity are reversed."** What follows is what
holds, and it is not a reversal.

**What holds.** The representation map has a singleton fiber at *each* end and is genuinely ambiguous
in between: `e0Repr_fiber_at_bot_singleton` at 0, `e0Repr_eq_epsilon0_iff` at ε₀, and
`repr_collision` between them, all in `ZeroParadox/Ordinal/PricedInterface.lean`.

⚠ **At the top, EXISTENCE is stipulated**: `⊤` is *adjoined*, so `e0Repr_top` is `rfl` and there is
exactly one of it by construction. Nothing at 0 is adjoined. **No comparative is drawn
between the two uniqueness proofs**; the positivity argument at 0 is Mathlib's (the
`onote_repr_eq_zero_iff` docstring).

⚠ **Only the half at 0 is new.** The half at ε₀ is `e0Repr_eq_epsilon0_iff`, whose docstring states
that the fibre of the map over ε₀ is exactly `{⊤}`; a separate top-fiber theorem would duplicate it.

⚠ **No "polarity reversal" — a DRIFT against complexity — is witnessed here, for two reasons.**
1. **Cross-carrier.** The complexity results (`infinitude_forces_infinite_complexity`,
   `member_cx_lt_top`, `ZeroParadox/Valuation/InfinitudeFloor.lean`) are stated over
   `[InfinitudeFloor α]`. **`E0Note` carries no such instance, and `InfinitudeFloor` is not in scope
   in `PricedInterface.lean`.** "The same point is extremal in both measures" would name a point of
   one type and a point of another: the MC-1 cross-category identity, retired as ill-typed.
2. **And the measure has no direction to reverse.** Ambiguity here is minimal at **both** ends. A DRIFT
   needs two measures running *opposite along* a structure; a quantity that is symmetric at the two
   ends cannot run opposite to anything.

`Reading:` **INVARIANT kind** (conjectural) — fiber cardinality is **one quantity measured at two
points of one carrier**, and it takes the same value at both, so exchanging the ends gains nothing.
That is the INVARIANT row, not COINCIDENCE (which needs two readings of one object) and not DRIFT
(which needs a direction).

⚠ **Not COINCIDENCE, and the "shared shape, never an instance-of relation" fence of the
`e0Repr_not_injective` docstring does not apply here.** That fence belongs to a different comparison —
`e0Repr` against the identifiability literature, which genuinely is two structures sharing a shape and
is tagged with no KIND at all. The INVARIANT claim is not of that form — it is one quantity at two
points of one carrier.

⚠ **Two fences.**
1. **No monotonicity is proved**, and none is claimed: two endpoint values plus one positive instance
   between them (`repr_collision`, whose witness is exhibited at
   `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` — the existential statement itself names no
   value, so do not attribute one to it).
2. **This closes a door.** Because the fiber at 0 is a single point, the statistics of the
   fiber-supported distribution (`exists_fiber_supported_non_pure_pmf`) lives **strictly between**
   the ends, 0 and ε₀, and cannot be seeded at 0 by this route.

## Triviality assessment

The carrier is an `abbrev`. The order, the decidability instances, and the lattice structure are all
inherited from Mathlib's `WithTop` instances applied to an order built in a sibling file — `PricedInterface.lean`
proves none of that and should get no credit for it. `e0OmegaPow_top` is `rfl`. `e0Repr_top` is `rfl`.

Not everything here is free. `repr_lt_epsilon0` — every raw notation denotes strictly below ε₀ — is a
short structural induction, but it does need the right closure facts about ε₀ (additive and
multiplicative principality, both obtained from `ω ^ ε₀ = ε₀`), and it is stated for **all** of `ONote`,
including non-normal forms, where Mathlib's own machinery does not directly apply.
`e0OmegaPow_fixedpoint_iff` is the uniqueness half discussed above. `repr_surj_below_epsilon0` is a
strong induction on the Cantor normal form split (`log`, `/`, `%`). None of the three is deep.

The measurement itself is arithmetically trivial — it is a `#print axioms` block. Its value, if any, is
that it is *stated as a price* on a specific named map, rather than left as a general impression that
"the ordinal side is classical." That is a difference in bookkeeping, not in mathematics.

## Prior art — the construction is not ours

**Castéran and Contejean, *hydra-battles* (rocq-community/hydra-battles), is the source of both halves.**

* **The carrier.** `theories/ordinals/OrdinalNotations/ON_plus.v` builds the **sum of two ordinal
  notation systems** — `t := (A + B)`, everything in `A` below everything in `B`, with the comparator
  `compare_plus`, its correctness `plus_comp`, well-foundedness `lt_wf`, the resulting instance
  `ON_plus`, and crucially `lt_eq_lt_dec` proving that **decidability of comparison is preserved,
  generically**. `E0Note` has that construction's shape with a one-point right summand, and is not an instance of it:
  `ON_plus` sums two `ON`s, and `SynONote` is not one, because its order is not well-founded (above), so
  `lt_wf` does not transfer. The decidability-preservation idea is his and is what `WithTop` repeats. The
  abstraction `ON_plus` is stated over, `Class ON` (`ON_Generic.v`) — a well-founded ordered datatype
  with a comparison function — is published. Mathlib's `WithBot`/`WithTop` decidability and lattice instances
  (`Mathlib/Order/WithBot.lean`) are the same move at instance level, and are what `PricedInterface.lean` actually
  calls.
* **The map.** The canonical name for "a notation system correctly denotes into a classical ordinal"
  is **`ON_correct`** (`ON_Generic.v`), with the three fields listed above. It is **already
  instantiated at ε₀**: `theories/ordinals/Schutte/Correctness_E0.v` builds `inject : T1 → Ord` with
  `inject_lt_epsilon0`, `embedding`, and `Instance Epsilon0_correct`. Our `e0Repr` has `ON_correct`'s
  into and onto properties and is not an instance: `ON_correct` is stated over an `ON`, which needs a
  well-founded order, and the comparator property fails (both fenced above). Its target is Mathlib's
  `Ordinal` instead of Schütte's axiomatized `Ord`, in Lean 4 instead of Coq.
* **The price is priced there too.** hydra-battles is constructive except its Schütte module, which
  axiomatizes the classical countable ordinals — so `inject` is exactly where the classical assumptions
  are paid in that development, and the library localizes them there by design. The purity block in `PricedInterface.lean`
  is the same observation, relocated to a library whose classical target is a constructed type rather
  than an axiom module.

**Mathlib states the same split in its own words.** The docstring of `NONote.repr`
(`Mathlib/SetTheory/Ordinal/Notation.lean`): *"This function is noncomputable because ordinal arithmetic
is noncomputable. In computational applications `NONote` can be used exclusively without reference to
`Ordinal`, but this function allows for correctness results to be stated."* That is the
constructive-side/classical-side interface, its purpose, and its price, stated by the library.

**Also in the neighbourhood, named but not described:** the `gaia-hydras` package bridges Grimm's Gaia
(classical, EM + AC) to hydra-battles' constructive notations. Its internals are not read here and
nothing about them is claimed.

`ONote`, `ONote.cmp`, `ONote.repr`, `WithTop` and its instances, `Ordinal.epsilon`,
`isPrincipal_add_omega0_opow` and `isPrincipal_mul_omega0_opow_opow` are all Mathlib. `SynONote` and
its `LinearOrder` are from `ZeroParadox/Ordinal/SnapNucleusConstructive.lean`, and are themselves a
re-derivation of hydra-battles' `T1.v` order construction, as that file records.

**The "two faces of one interface" framing is our presentation, not a discovered correspondence.** The
framework pairs a logic-side modality (`dnegNucleus`, `ZeroParadox/Category/DoubleNegationNucleus.lean`
— the double-negation nucleus) with the carrier-side map here, and presents the two as two faces of one
constructive/classical boundary. No prior work pairing the two was located as of 2026-10-04, searched
as follows: theoremsearch, three phrasings (the double-negation nucleus with an ordinal-notation
denotation map; the negative translation compared with interpreting notations into classical ordinals;
the classical price localized at a denotation map together with the double-negation topology). Each
returned double-negation or negative-translation results only, and that tool's null is uninformative,
so this is not a claim that none exists. Each half is separately canonical — the ¬¬-translation is Gödel–Gentzen–Kolmogorov, with Glivenko's
variant and the CPS transform under Curry–Howard as its recognized computational reading; the
carrier-side map is `repr`, with `ON_correct`'s into and onto properties, per above. **The pairing is a presentational choice of ours.**
No theorem here relates the two faces, and none is claimed.

