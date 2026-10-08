# Comparability of well-orders is a constructive taboo: result, prior art and fences

Ride-along documentation for [`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`](OrdinalChoiceEssential.lean).
The Lean file holds the declarations, the Engineer's Take and a statement per declaration; this file holds
the result, the prior art and the fences. Where the two would overlap, **the Lean is authoritative**.

Examined `Classical.choice` footprints fall into four classes, accidental, essential, statement-carried
and unclassified (`ZeroParadox/Category/ChoiceCannotBe.md`). The Lean file records an essential one, on the premise stated
in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV, and this file fences what it does and does not license.

`ZeroParadox/Category/ChoiceCannotBe.lean` § IV is the index of the essential cases and is the place
to count them. **No figure is recorded here** — a count kept at the site of one instance goes stale
silently the moment another is found.

The result: **comparability of arbitrary well-orders implies excluded middle**
(`em_of_wellOrder_comparable`), proved with **no `Classical.choice`**
(`[propext, Quot.sound]`).

`Statement:` comparability of well-orders and `le_total` on `Ordinal.{0}` are interderivable, and only
the second carries choice in its statement. The principle, comparability of well-orders in its
`InitialSeg` form, is essential on the premise stated in `ZeroParadox/Category/ChoiceCannotBe.lean`
§ IV. Mathlib's `le_total` on `Ordinal.{0}` is that principle at `Type`: `Ordinal.type_le_iff`
(`Iff.rfl`) gives `le_total` ⇒ principle, and the converse uses `Ordinal.inductionOn` (both are
`example`s in the Lean file's § III). So it implies excluded middle too, though on `Ordinal` that
implication is not choice-free.
Mathlib's `Ordinal` order is
built with choice, and the statement itself carries it, so `le_total` on `Ordinal.{0}` is
STATEMENT-CARRIED: a theorem that takes
`∀ a b : Ordinal.{0}, a ≤ b ∨ b ≤ a` as a hypothesis and proves `True` by `trivial` reports
`[propext, Classical.choice, Quot.sound]` (measured 2026-10-08; the instance-term trace is the Lean
file's § III).

## PRIOR ART — the mathematics here is KNOWN and is NOT claimed as new

This is a **Lean formalization of a published taboo**. The mathematics is Kraus, Nordvall Forsberg
and Xu's and is not claimed as new. Their Theorem 38 is a **paper proof**: it appears in their
Appendix D without their formalized-result marker, their formalization is scoped to Cantor normal
forms and Brouwer trees, and their Agda index records the corresponding statement as commented out
(`-- × (isTrichotomous O._<_ ↔ LEM) × (isConvex O._≤_ ↔ LEM)`, whose second clause is exactly the
connexity statement of Theorem 38(d)). **No machine-checked version of this taboo was located**, in
their development or elsewhere. That is a report of one search, not a priority claim — the honest
statement is that we did not find one, not that none exists.

* **N. Kraus, F. Nordvall Forsberg, C. Xu, "Connecting Constructive Notions of Ordinals in
  Homotopy Type Theory," MFCS 2021, arXiv:2104.02549.** Theorem 1: for `Ord` (extensional
  wellfounded orders), "`<` is trichotomous iff `≤` is connex iff LEM holds." Theorem 38(d):
  connexity of `≤` implies LEM. **The witnesses in the Lean file are theirs** — their proof compares a
  carrier that is empty-or-two-element against the one-point order. The Lean file supplies their
  argument, not a new one.
* **M. Escardó, TypeTopology, `Taboos.Decomposability` (2022)**, `Ordinal-decomposition-iff-WEM`:
  the type of ordinals "has no non-trivial decidable property unless weak excluded middle holds."
  This is the decidability-side companion to `em_of_wellOrder_comparable`.
* **Escardó, TypeTopology, `Ordinals.Taboos`**, e.g.
  `EM-if-Every-Discrete-Ordinal-Is-Trichotomous`; and de Jong-Kraus-Nordvall Forsberg-Xu,
  "Constructive Ordinal Exponentiation," arXiv:2501.14542, **Lemma 54**
  in the current version (every order-preserving map between ordinals is a simulation iff LEM),
  which *is* marked formalized and whose proof credits Escardó's `Ordinals.OrdinalOfOrdinals` —
  neighbouring taboos in the same genre. The field's own word for these is **taboo**.

**The mathematics is theirs and is not claimed as new.** What is added here is a machine-checked
proof of it — we did not locate one elsewhere — together with the packaging. Three differences from
KNX are worth stating precisely, and none is a mathematical advance:

1. KNX state connexity in the **data** form `(X ≤ Y) ⊎ (X ≥ Y)`. The hypothesis of
   `em_of_wellOrder_comparable` is the
   **propositional** form `Nonempty (r ≼i s) ∨ Nonempty (s ≼i r)` — a *weaker* hypothesis, so the
   implication is formally a little stronger. It is the form Mathlib's `le_total` actually has.
   (Mathlib's `InitialSeg.total` is the data form, and is where Mathlib spends a literal
   `Classical.choice`; see the trace in the Lean file's § III.)
2. It is stated against `InitialSeg` rather than `Ordinal`, for the measurement reason in the Lean
   file's § III.
3. KNX's `Ord` is **extensional** wellfounded orders — replacing trichotomy with extensionality is
   their explicit design point — whereas Mathlib's `IsWellOrder` builds trichotomy in. The proof is
   unaffected, since the witnesses in the Lean file carry constructive `Std.Trichotomous` instances, but the
   two statements are about different carriers and the difference should not go unstated.

## What this DOES establish

The *substrate* is essential in the sense, and on the premise, of
`ZeroParadox/Category/ChoiceCannotBe.lean` § IV: "any two well-orders are comparable" implies excluded
middle by a choice-free reduction. `le_total` on `Ordinal.{0}` is that principle at `Type`
(`Ordinal.type_le_iff`, `Iff.rfl`, one way; `Ordinal.inductionOn` the other), and `lt_or_ge` on it
implies it through `le_of_lt`, so both
imply the principle as well as follow from it; every `sup`/`nfp`/`deriv` argument that leans on
trichotomy uses it. On `Ordinal` the order instance carries choice in its own term (the Lean file's
§ III), so neither direction is choice-free there.

## What this does NOT establish — read before citing the Lean file

**It does not show that the framework's ε₀ results need choice**, and must not be cited as
showing that. `epsilon0_ne_zero`, `epsilon0_ne_bot`, `epsilon0_eq_nfp_bot` concern *specific,
notation-nameable* ordinals, not arbitrary well-orders. Comparison of ordinal *notations* is
decidable and choice-free — Mathlib's `ONote.cmp` is `[propext]`-only, and ZP-N
(`ZeroParadox/Ordinal/ConstructiveOrdinals.lean`) already proves the ascent facts `exp_lt_term`,
`omegaPow_no_fixedpoint`, `tower_strictMono` at `[propext]` on raw `ONote`. The taboo needs
*arbitrary* well-orders, including the degenerate ones the Lean file builds out of a proposition.
Nothing about ε₀ supplies those.

So the classification splits, and the split is the point:

* **comparability of well-orders, which `le_total` on `Ordinal.{0}` states at `Type` — ESSENTIAL**
  on the premise above (`em_of_wellOrder_comparable`); `Ordinal`'s order instance itself carries choice
  in its term (the Lean file's § III);
* **the ε₀ results — STATEMENT-CARRIED** (`ε₀ ≠ 0` as a hypothesis already reports the choice,
  measured 2026-10-08). They inherit choice from Mathlib's `Ordinal` machinery:
  `Ordinal.instLinearOrder`, `nfp`, `omega0` and `epsilon`, as `ZeroParadox/Ordinal/ConstructiveOrdinals.lean`
  lists, and limit recursion (`SuccOrder.limitRecOn`), measured 2026-10-08.
  ZP-N's `ONote` results (`exp_lt_term`, `omegaPow_no_fixedpoint`, `tower_strictMono`, each
  `[propext]`) are evidence that the ascent content does not need it, not a re-proof: they are
  statements on a different carrier.

Nothing in the Lean file is declared `axiom`, and nothing there uses `sorry`.

## Structure of `OrdinalChoiceEssential.lean`

- § I   The witness: a well-order that is empty when `p` fails and two-element when `p` holds
- § II  The taboo: comparability implies excluded middle, choice-free
- § III Why this had to be stated about `InitialSeg` and not about `Ordinal`
