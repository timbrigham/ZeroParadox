# Disjunctive sequences: prior art, footprints and fences

Ride-along for `ZeroParadox/Information/Disjunctive.lean`. The Lean file holds the declarations, the
Engineer's Take and the per-declaration glosses.

## Prior art

"Disjunctive sequence" is the standard term. Barnsley and Leśniak, *The chaos game on an iterated
function system from a topological point of view*, arXiv:1203.0481v2, § 3, p. 6 (read from the
retrieved PDF): an infinite word is *disjunctive* "if it contains all possible finite words"; "In fact
any finite word appears in a disjunctive sequence of symbols infinitely often"; Proposition 1 states
the beyond-every-position form; Example 1 is the Champernowne sequence, with the note that "all normal
sequences are disjunctive but the converse is not true". Their definition cites [11] Calude and
Staiger, *Generalisations of disjunctive sequences*, Math. Log. Q. 51 (2005), and [35] Staiger, *How
large is the set of disjunctive sequences?*, J. UCS 8 (2002) (reference list, pp. 13-14). Neither was
retrieved, so nothing here describes their contents.

`Disjunctive` is the infinitely-often form and `DisjunctiveOnce` the at-least-once form;
`disjunctive_iff_once` is the equivalence Barnsley and Leśniak state.

The almost-sure result is the infinite monkey theorem, proved here as `fairTape_disjunctive_ae`: the
second Borel–Cantelli lemma (`measure_limsup_eq_one`) on disjoint aligned blocks gives `monkey_limsup`.

No periodic tape is disjunctive. Barnsley and Leśniak, pp. 7-8, recall from Muchnik, Semenov and
Ushakov (their [30]) that a sequence is *almost periodic* when every word occurring in it infinitely
often occurs in every segment of some fixed length, and note: "Obviously a disjunctive sequence cannot
be almost periodic." A tape equal to its own shift by some `a > 0` is almost periodic in that sense, so
`not_disjunctive_of_periodic` (§ V) is a special case of their remark.

## Search record (2026-10-04)

- Corpus, `ZeroParadox/**/*.lean`: `disjunctive|champernowne|monkey`. Not located.
- Mathlib pin, `.lake/packages/mathlib/Mathlib`: `disjunctive|rich sequence|champernowne`, then
  `normal number|borel normal|every (finite) word/string/block occurs/appears|infinite monkey`.
  Not located as of 2026-10-04.
- Martin-Löf randomness and Kolmogorov complexity, Mathlib pin at `5450b53` (7933 `.lean` files),
  2026-10-04, case-insensitive regular expressions, one at a time: `kolmogorov complexity`,
  `kolmogorovComplexity`, `Martin-L`, `MartinLof`, `algorithmic(ally)? random`, `incompressib`,
  `prefix-free complexity`, `Chaitin`, `Schnorr`, `randomness test`, `descriptive complexity`. Zero
  files each. Control: `Kolmogorov` alone hits 10 files, one an author line and the rest probability
  and measure theory (the extension theorem, the 0-1 law, Chapman–Kolmogorov, the Kolmogorov
  condition). Not located as of 2026-10-04, searched as above.
- theoremsearch, three phrasings (definition; "rich sequence"; Martin-Löf random and Champernowne).
  Returned the Barnsley–Leśniak and Barnsley–Vince definitions and Landsman, *Typical = random*
  (arXiv:2306.09226, Thm 4.2, as summarized by the search result: every word occurs infinitely often in
  every fair-coin random sequence). Landsman was not retrieved; it is a discovery lead, not a citation.

## Footprints

The `PurityCheck` section of `ZeroParadox/Information/Disjunctive.lean` is the register for every
declaration in that file; read it there. Measured here, because they are Mathlib's and not in that
block (`#print axioms`, 2026-10-04):

- `Filter.frequently_atTop` and `Filter.Frequently.exists` each carry `Classical.choice`
  (`[propext, Classical.choice, Quot.sound]`). The statement `Disjunctive` measures
  `[propext, Quot.sound]`, so the choice in `champ_disjunctive`, `disjunctive_iff_once` and § V
  enters through these proofs, not through the definition.
- `Nat.sqrt_add_eq`, `Nat.unpair_pair` and `Nat.left_le_pair` each carry `Classical.choice`. The slot
  layout of `champ` uses `tri` / `untri`, whose lemmas are proved by `omega`.
- `codeWord` and the § IV theorems carry `Classical.choice` through `Encodable.encode` on `Code` (the
  `Denumerable Code` instance; see `ZeroParadox/Category/ChoiceCannotBe.lean` § III and
  `ZeroParadox/Computability/Kleene.lean` § VII).

## Fences

1. **Presence, not execution.** `code_occurs_of_disjunctive` says a code's binary is written on the
   tape. Nothing reads or runs it; occurrence is the occurrence commitment (`ZeroParadox/Order/Snap.lean`).
2. **Disjunctive is weak.** `champ` is disjunctive and primitive recursive (§ II). Standard theory,
   not proved here: a sequence is Martin-Löf random exactly when its prefixes are incompressible in
   PREFIX-FREE Kolmogorov complexity, `K(x↾n) ≥ n − c` for some constant `c` (Levin–Schnorr, Chaitin),
   and a Martin-Löf random sequence is disjunctive; the converse fails (`champ`). With PLAIN
   complexity no infinite sequence has all prefixes incompressible (Martin-Löf), so the prefix-free
   form is the one meant.
3. **The commitment is separate.** `Reading:` Tim's commitment that the framework's ⊥, read as a
   tape, is maximally complex, in the prefix-free sense of fence 2. Through the standard theorem it
   would make that tape disjunctive. The framework's ⊥ here is the role, not ⊥ of `ℕ → Bool` under
   the pointwise order: that occupant is the all-false tape, which is not disjunctive
   (`allFalse_not_disjunctive`). Neither the commitment nor the standard theorem is in Lean (Search
   record).
4. **`Code.zero`'s word is empty** (`codeWord_zero_width`), so presence there is vacuous.
5. **The measure fences of `ZeroParadox/Information/CrossingTrials.lean` stand.** Measure one is not
   necessity, and nothing here says any framework object IS a fair-coin tape.
