# Disjunctive sequences: prior art, footprints and fences

Ride-along for `ZeroParadox/Information/Disjunctive.lean`. The Lean file holds the declarations, the
Engineer's Take and the per-declaration glosses.

## Prior art

"Disjunctive sequence" (also "rich sequence") is the standard term. Barnsley and Leśniak, *The chaos
game on an iterated function system from a topological point of view*, arXiv:1203.0481v2, § 3, p. 6
(read from the retrieved PDF): an infinite word is *disjunctive* "if it contains all possible finite
words"; "In fact any finite word appears in a disjunctive sequence of symbols infinitely often";
Proposition 1 states the beyond-every-position form; Example 1 is the Champernowne sequence, with the
note that "all normal sequences are disjunctive but the converse is not true". They cite Calude,
Priese and Staiger, *Disjunctive sequences: An overview*, CDMTCS Research Report 63 (1997), as
their reference [11]. That survey is the standard reference; it was **not retrieved** (two URLs
refused), so nothing here describes its contents.

`Disjunctive` is the infinitely-often form and `DisjunctiveOnce` the at-least-once form;
`disjunctive_iff_once` is the equivalence Barnsley and Leśniak state.

The almost-sure result is the infinite monkey theorem, proved here by the second Borel–Cantelli lemma
(`measure_limsup_eq_one`) on disjoint aligned blocks.

## Search record (2026-10-04)

- Corpus, `ZeroParadox/**/*.lean`: `disjunctive|champernowne|monkey`. Not located.
- Mathlib pin, `.lake/packages/mathlib/Mathlib`: `disjunctive|rich sequence|champernowne`, then
  `normal number|borel normal|every (finite) word/string/block occurs/appears|infinite monkey`.
  Not located as of 2026-10-04. Martin-Löf randomness and Kolmogorov complexity: not located in the
  pin as of 2026-10-04, nine phrasings, recorded with the scratch probe that preceded this file.
- `.claude-local/papers/`: no disjunctive, Champernowne or algorithmic-randomness paper filed.
- theoremsearch, three phrasings (definition; "rich sequence"; Martin-Löf random and Champernowne).
  Returned the Barnsley–Leśniak and Barnsley–Vince definitions and Landsman, *Typical = random*
  (arXiv:2306.09226, Thm 4.2: every word occurs infinitely often in every fair-coin random
  sequence). Landsman was not retrieved; it is a discovery lead, not a citation.

## Footprints (`#print axioms`, as built)

- `champ`, `untri`, `bitAt`, `tri`: no axioms. `champ_disjunctiveOnce`, `untri_tri_add`,
  `occurs_past_of_once`, `bitAt_ofBits`: `[propext, Quot.sound]`.
- `champ_disjunctive` and `disjunctive_iff_once` carry `Classical.choice`. The statement
  `Disjunctive` itself measures `[propext, Quot.sound]`; the choice enters through Mathlib's
  `Filter.frequently_atTop` and `Filter.Frequently.exists`, each measured
  `[propext, Classical.choice, Quot.sound]` on 2026-10-04.
- A first draft laid the tape out with `Nat.sqrt` and `Nat.pair`. Mathlib's `Nat.sqrt_add_eq`,
  `Nat.unpair_pair` and `Nat.left_le_pair` each carry `Classical.choice`, so the slot layout was
  rebuilt on `tri` / `untri`, whose lemmas are proved by `omega`.
- `codeWord` and every § IV theorem carry `Classical.choice`, through `Encodable.encode` on `Code`
  (the `Denumerable Code` instance; see `ZeroParadox/Category/ChoiceCannotBe.lean` § III and
  `ZeroParadox/Computability/Kleene.lean` § VII).
- `not_disjunctive_of_periodic` and `disjunctive_not_periodic` (§ V) carry `Classical.choice`,
  measured 2026-10-04; the proof uses `Filter.Frequently.exists`, measured with it above.

## Fences

1. **Presence, not execution.** `code_occurs_of_disjunctive` says a code's binary is written on the
   tape. Nothing reads or runs it; occurrence is the occurrence commitment (`ZeroParadox/Order/Snap.lean`).
2. **Disjunctive is weak.** `champ` is disjunctive and primitive recursive. Maximal complexity
   (Martin-Löf randomness) implies disjunctive in standard theory; the converse fails, and neither
   direction about randomness is proved here.
3. **`Code.zero`'s word is empty** (`codeWord_zero_width`), so presence there is vacuous.
4. **The measure fences of `ZeroParadox/Information/CrossingTrials.lean` stand.** Measure one is not
   necessity, and nothing here says any framework object IS a fair-coin tape.
