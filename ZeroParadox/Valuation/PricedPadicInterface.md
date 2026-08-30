# Pricing the crossing: where choice enters a 2-adic interface, and where it does not

Ride-along documentation for [`ZeroParadox/Valuation/PricedPadicInterface.lean`](PricedPadicInterface.lean). The Lean file holds the declarations and a statement per
declaration; this document holds the rationale, the measured prices, the fences and the prior art.
Where the two would overlap, **the Lean is authoritative**.

## What the Lean file is

A **measurement**, not a construction — the p-adic analogue of
`ZeroParadox/Ordinal/PricedInterface.lean`. It exhibits a small, concrete, choice-free carrier on
which the *Group A* content of the framework's `Valuation/` cluster is statable and provable — the
ZP-J valuation axioms and the ZP-B ball/separation core — together with a single named crossing into
Mathlib's `ℤ_[2]`, and the axiom footprint of each side. What is contributed is the **price tag**: the
carrier is choice-free, the crossing is `Classical.choice` at every declaration, and the price is
localized one layer deeper than a footprint on `Padic` would suggest.

Neither the carrier nor the crossing is original. The apartness-based separation is
Pelayo–Voevodsky–Warren's design (and Bishop's before them); the constructive-p-adic and
domain-theoretic prior art is Vickers's; the digit tree is Bruhat–Tits (already cited in
`ZeroParadox/Valuation/PadicTree.lean`). See "Prior art".

## Why the Lean file exists — the roots enumeration's constructive payoff

A footprint sweep of the `Valuation/` cluster found its `Classical.choice` sites **dominated** by the
`Padic` type's own footprint — every one of them sits downstream of `Padic`, so `#print axioms` on a
`Valuation/` declaration measures `Padic`, not the framework's proof. This file makes the framework's
own Group A content *measurable* by restating it on a carrier that does not mention `Padic` at all, so
the choice that does appear appears only at the one named crossing.

The `Valuation/` cluster splits, and the split is the whole scoping finding:

* **Group A — needs only the valuation and its order.** The ZP-J `ValuationStructure` axioms, the ZP-B
  ultrametric/clopen-ball content, the descent to a single point, total separation. Their mathematical
  content is *agreement to depth n* and *the valuation of the bottom is the top of the value monoid* —
  combinatorial and valuative statements that use neither division, nor completeness, nor ℝ. **This is
  the slice built here.**
* **Group B — genuinely needs the complete field.** `ZeroParadox/Valuation/RiemannSphere.lean` /
  `rInv_swaps` (field inversion plus continuity at two special points),
  `ZeroParadox/Valuation/Ostrowski.lean` (a classification of absolute values into ℝ), and the
  Haar/Kozyrev/ergodic layer (invariant measure, spectral theory). There is no cheaper carrier for
  these, and the Lean file does not attempt one. Recorded as needing the field.

## The layered localization of the crossing's choice

The crossing's `Classical.choice` is **not** paid at the metric completion. Traced through Mathlib:
`Padic p := CauSeq.Completion.Cauchy (padicNorm p)`, and `padicNorm` is built from `padicValRat`, from
`padicValInt`, from **`padicValNat`** — the p-adic valuation on ℕ, below the Cauchy quotient, below the
field, below the metric. `padicValNat` unfolds to `Nat.maxPowDvdDiv`, on the `multiplicity` layer, and
that is where the footprint enters: `padicValNat`, `Nat.maxPowDvdDiv`, and `multiplicity` each measure
`[propext, Classical.choice, Quot.sound]`, while `Nat.find`/`Nat.findGreatest` — the obvious primitives
for "least/greatest k with pᵏ ∣ n" — are axiom-free. The Lean file's purity block prints the whole chain so
this is reproducible rather than asserted.

A corollary, settled negatively: **`ℤ_[p]` is not cheaper than `ℚ_[p]`.** Both are downstream of the
same layer-0 valuation, so dropping the field for the ring of integers buys nothing.

## The measured price of the crossing

Measured by the `#print axioms` block at the bottom of the Lean file (the instrument is the deliverable;
these are the numbers it reported, not the numbers that were hoped for).

* **Constructive side — choice-free.** The carrier carries no `Classical.choice`. `v2nat`, `v2`,
  `nScale_bot`, `AgreeTo`, `Apart`, `agree_trans`, `agree_mono`, `separated_of_apart` and
  `not_apart_of_agree_all` report **no axioms at all**; `v2_bot`, `v2_unique` and `clopen_gap_at_bot`
  report `[propext]`; `v2_scale_nat`, `nScale_unique_fp`, `nScale_ne_self` report `[propext, Quot.sound]`
  and `agree_all_iff` reports `[Quot.sound]` (the `funext`).
* **One instance-level exception, on the constructive side, reported not hidden.** The ZP-J `val_scale`
  axiom in its literal form `v2_scale : v2 (2n) = v2 n + 1` reports `[propext, Classical.choice,
  Quot.sound]` — **and on this carrier (ℕ) it is not the carrier's.** It is the ambient `ℕ∞`
  NUMERAL: `One ℕ∞` carries it, while `Add ℕ∞`, `Nat.cast : ℕ → ℕ∞` and `(a : ℕ∞) + (b : ℕ∞)`
  are all axiom-free — measured 2026-08-30, and `(2 : ℕ∞)` is clean too, so it is the `0` and `1`
  numerals specifically. The content of the axiom is choice-free — `v2_scale_nat` states the same
  fact with the successor on `ℕ` and comes out `[propext, Quot.sound]`. ⚠ None of this carries over
  to `ℤ_[2]`, where the carrier itself is tainted. See "The `ℕ∞`-numeral finding".
* **The crossing — `Classical.choice`.** `natToZ2`, `natToZ2_bot`, `natToZ2_scale` and
  `crossVal_bot_agrees` all report `[propext, Classical.choice, Quot.sound]`.

**What that measurement does and does not license.** It locates where the classical assumption is paid
on this pair of carriers, and shows the Group A content does not need it. It does **not** show that
Mathlib's p-adic results are eliminable, and it does **not** show `padicValNat`'s choice is removable
*in Mathlib* — that would require re-proving Mathlib's valuation API on a different definition, which is
not attempted here. `#print axioms` reports how a proof was written, never what a theorem requires.

## The `ℕ∞`-numeral finding — reported, not explained away

The one `Classical.choice` on the constructive side was not predicted. On the ℕ side it arrives
through Mathlib's `ℕ∞` NUMERAL, not the addition and not the valuation — and, on ℕ, not the carrier:
`enat_add_choice` (`(a : ℕ∞) + (b : ℕ∞) = ↑(a + b)`) reports `[propext, Classical.choice, Quot.sound]`
— but that is its PROOF TERM, not an instance: the same proposition proved by induction and `rfl`
reports no axioms at all. Measured 2026-08-30, `ℕ∞` ADDITION is choice-free and the LITERAL `1` is
what is tainted (`One ℕ∞`, `AddMonoidWithOne ℕ∞`). This is the documented instance hazard,
here located exactly — and it has a consequence for the ZP-J layer: because `ValuationStructure.val`
targets `ℕ∞` and `val_scale` is stated as `val x + 1`, the *statement* of that axiom carries
`Classical.choice` on **any** carrier, `ℕ` and `ℤ_[2]` alike. So `q2Val_scale` (`ZeroParadox/Valuation/Scale.lean`)
footprint is not evidence about what the p-adic completion mathematically REQUIRES — but it is not
separable either: `PadicInt` reports `Classical.choice`, so on `ℤ_[2]` the carrier alone already
accounts for it. This file separates the two contributions: `v2_scale_nat` isolates the choice-free
valuation content, and the numeral accounts for the rest ON ℕ. ⚠ It does NOT carry over to ℤ_[2]:
`PadicInt` is itself choice-tainted, so nothing there separates. The remaining
`Classical.choice` in the crossing (`natToZ2`, `crossVal_bot_agrees`) is attributable to the p-adic
target alone.

## The carrier, and what it actually is

Two faces, matching the two faces of Group A:

* **The valuation face — ℕ with `v2 : ℕ → ℕ∞`.** `v2` is a 2-adic valuation defined by structural fuel
  recursion (`v2nat`), not well-founded recursion, so it is computable and choice-free. `v2 0 = ⊤`; on
  nonzero inputs it counts factors of 2. On this carrier three of the four ZP-J `ValuationStructure`
  axioms hold choice-free with `scale = (2 * ·)`: `scale_bot` (`nScale_bot`), `val_bot` (`v2_bot`),
  `val_unique` (`v2_unique`); and the fixed-point content `nScale_unique_fp` (the bottom is the unique
  fixed point of doubling) is proved directly. The fourth axiom, `val_scale`, holds choice-free *in
  content* (`v2_scale_nat`) but carries `Classical.choice` *in its literal `ℕ∞`-successor form*
  (`v2_scale`) — from the ambient `ℕ∞` NUMERAL, not the addition and, on ℕ, not the carrier
  (see "The `ℕ∞`-numeral finding").
  This is the choice-free mirror of `q2Val_bot`, `q2Val_unique`, `q2Scale_bot` and `q2Scale_unique_fp`
  (`ZeroParadox/Valuation/Scale.lean`), which prove the same axioms in `ℤ_[2]` via
  `PadicInt.valuation`; the comparison localizes § V's choice on the ℕ side only. ⚠ On `ℤ_[2]`
  nothing separates: `PadicInt` is itself choice-tainted, so the carrier alone already accounts
  for it whatever the numeral does.
* **The ball face — digit streams `Str := ℕ → Fin 2`.** `AgreeTo n x y` ("agree to depth n") is the
  ball relation; `Apart x y := ∃ n, x n ≠ y n` is its positive complement. The ultrametric strong
  triangle (depth form), nested balls, descent to a single point, and total separation all hold
  choice-free — **provided separation takes the positive `Apart` hypothesis, not the negative `x ≠ y`.**

## The apartness finding, and its independent vindication

The separation statements **must take a positive hypothesis.** From `¬(x = y)` one cannot
constructively produce the depth at which two streams first differ; from `Apart x y` the witness is
computed, and the statement is choice-free. This matches, independently, the design
Pelayo–Voevodsky–Warren were forced into: because `ℤ[[X]]` lacks decidable equality they work "with an
apartness relation and with the corresponding notions of integral domains and fields" (Heyting fields).
Two developments reaching the same design from opposite directions is the strongest evidence the carrier
is the right one — and the credit is theirs, not ours.

## What is NOT proved here, and must not be inferred

* **The ZP-B results are not re-proved.** A different carrier means **different theorems**. ZP-B's
  `c3_irreversible` quantifies over continuous paths from `Set.Icc (0:ℝ) 1`; the stream-carrier
  separation statements are *different propositions* about digit depth, not a re-proof of anything
  stated over ℝ. State them exactly as such.
* **This carrier is not the completion.** It carries no topology object, no metric, no field, and
  cannot express anything that genuinely needs the complete field (Group B). It is not a constructive
  `ℤ_[2]`; it is a carrier for the Group A *content*.
* **Locating choice is not eliminating it.** Nothing here re-proves any Mathlib p-adic result, and no
  failed or avoided elaboration in the Lean file is an independence result or may be upgraded to one.
* **`v₂(0) = ⊤` is a *valuative* property** — the valuation of the bottom is the top of the value
  monoid. Never describe it with topological vocabulary; "isolated" in particular is wrong and is on
  the project's vocabulary watch list.

## Triviality assessment

The valuation face is elementary: `v2nat` is a short structural recursion, and its only non-immediate
lemma is fuel saturation (the value stabilizes once the fuel exceeds the input), used once to prove
`v2_scale_nat`. The ball face is pure combinatorics on `ℕ → Fin 2`; `agree_all_iff` is `funext` in one
direction (hence its `Quot.sound`), and `clopen_gap_at_bot` is the decidability of a bounded quantifier.
The crossing is `Nat.cast` into `ℤ_[2]` and one comparison at the bottom. Nothing here is deep. The
value, if any, is the same as its ordinal sibling's: the boundary is *stated as a price* on a specific
named map, on a carrier where the classical target is a real library type, rather than left as the
general impression that "the p-adic side is classical".

## Prior art — the carrier is not ours

* **Apartness / constructive p-adics.** Á. Pelayo, V. Voevodsky, M. A. Warren, "A univalent
  formalization of the p-adic numbers," *Mathematical Structures in Computer Science* **25**(5), 2015,
  pp. 1147–1171, doi:10.1017/S0960129514000541 (preprint arXiv:1302.1207). Constructs `ℤ_p` as a
  quotient of `ℤ[[X]]` and `ℚ_p` as its field of fractions, algebraically rather than analytically, and
  is forced to an apartness relation and Heyting fields by the lack of decidable equality on `ℤ[[X]]`.
  Verified in Coq/UniMath (so not importable into Lean), an *algebraic* route (so it supplies the
  ring/field but not the metric/ball apparatus of Group A), and labeled "preliminary" by its authors.
  It is the direct prior art for the apartness face here.
* **Domain-theoretic p-adics.** S. Vickers, "A fixpoint construction of the p-adic domain," LNCS **283**
  (1987), pp. 270–289; and "An algorithmic approach to the p-adic integers," LNCS **298** (1988),
  pp. 599–616. The p-adic integers appear as the maximal elements of a Scott domain with algebraic
  structure, presented as a fixpoint of a functor in a category of sheaves of rings — the
  partial-element / algorithmic route, on-thread with this framework's fixpoint theme, and distinct from
  the concrete digit-stream carrier used here.
* **The tree.** The digit tree is the Bruhat–Tits tree, already cited in
  `ZeroParadox/Valuation/PadicTree.lean` (Ludwig & Merten, arXiv:2505.12933); not rediscovered here.
* **The inverse-limit carrier's viability.** A. Crighton, "Hensel's Lemma for the p-adic Integers,"
  Archive of Formal Proofs, 2021, formalizes `ℤ_p` as the inverse limit of `ℤ / pⁿ` in Isabelle/HOL
  (classical) — evidence the inverse-limit carrier is viable, not a choice-free result.

A prior-art search for a Lean/Agda constructive or coinductive-stream p-adic development, a Bishop-style
non-archimedean completion naming the p-adics, and a source comparing a primitive-recursive p-adic
valuation on ℕ against Mathlib's `multiplicity`-based `padicValNat` returned "searched, none found" in
each case — recorded as searches, never as claims that none exists.

**What is ours is the price tag, exactly as on the ordinal side** — not the carrier, not the apartness
design, not the tree.

## Structure

- § I   The valuation face — `v2` on ℕ, the ZP-J axioms priced (three choice-free; `val_scale`'s
        content choice-free, its literal `ℕ∞` form carrying the instance choice).
- § II  The ball face — digit streams, agreement, apartness, separation, choice-free.
- § III The crossing — one named map ℕ → `ℤ_[2]`, priced.
- § IV  Axiom Purity Check — the deliverable.
