# Comparability of well-orders is a constructive taboo: result, prior art and fences

Ride-along documentation for [`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`](OrdinalChoiceEssential.lean).
The Lean file holds the declarations, the Engineer's Take and a statement per declaration; this file holds
the result, the prior art and the fences. Where the two would overlap, **the Lean is authoritative**.

**Most** `Classical.choice` footprints this framework has examined have turned out **accidental** — a
choice-free re-proof existed, or plausibly could. **Some do not.** The Lean file records one of those, and
this file fences what it does and does not license.

`ZeroParadox/Category/ChoiceCannotBe.lean` § IV is the index of the essential cases and is the place
to count them. **No figure is recorded here** — a count kept at the site of one instance goes stale
silently the moment another is found, which is exactly what happened to the sentence this paragraph
replaces. *(Corrected 2026-08-01: this header read "**every** footprint … accidental" and "**the one**
place examined so far" until then. Both were already false — `wem_of_fixedPointFree`
(`ZeroParadox/Category/LawvereTaboo.lean`) was committed 2026-07-20 and is a second essential case,
sitting on the diagonal keystone rather than on an imported order instance.)*

The result: **comparability of arbitrary well-orders implies excluded middle**
(`em_of_wellOrder_comparable`), proved with **no `Classical.choice`**
(`[propext, Quot.sound]`). Comparability is the mathematical content of `le_total` in Mathlib's
`LinearOrder Ordinal` instance — "any two ordinals are comparable" — so a choice-free proof of that
field would be a choice-free proof of excluded middle; that this makes it non-removable rests on the
premise stated in `ZeroParadox/Category/ChoiceCannotBe.lean` § IV.

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
`ZeroParadox/Category/ChoiceCannotBe.lean` § IV: "Any two well-orders are comparable" — hence
`Ordinal`'s `LinearOrder`, hence `Ordinal.lt_or_ge`, hence every `sup`/`nfp`/`deriv` argument that
leans on trichotomy — implies excluded middle by a choice-free reduction.

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

* **the general order on `Ordinal` — ESSENTIAL** on the premise above (the Lean file);
* **the ε₀ results' inheritance of it — still ACCIDENTAL-or-unclassified.** They use a
  general-purpose classically-built order where a decidable fragment would do.

Nothing in the Lean file is declared `axiom`, and nothing there uses `sorry`.

## Structure of `OrdinalChoiceEssential.lean`

- § I   The witness: a well-order that is empty when `p` fails and two-element when `p` holds
- § II  The taboo: comparability implies excluded middle, choice-free
- § III Why this had to be stated about `InitialSeg` and not about `Ordinal`
