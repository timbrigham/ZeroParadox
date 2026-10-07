# The diagonal engine's supplier is a constructive taboo: result, fences and prior art

Ride-along documentation for [`ZeroParadox/Category/LawvereTaboo.lean`](LawvereTaboo.lean). The Lean
file holds the declarations, the Engineer's Take and a statement per declaration; this file holds the
argument, the fences and the prior art. Where the two would overlap, **the Lean is authoritative**.

`ZeroParadox/Category/Lawvere.lean` proves `fixedPointFree_of_nontrivial`: **any type with two
distinct elements admits a fixed-point-free endofunction.** It is the *supplier* of Lawvere's engine
— every "no Lawvere witness" result in the framework (`no_witness_of_nontrivial`,
`nontrivial_lattice_no_witness`, `q2_no_witness`) consumes it, and the consumer
`no_witness_of_fixedPointFree` is axiom-free. The supplier measures
`[propext, Classical.choice, Quot.sound]`, and a single `classical` tactic is its entire classical
footprint.

`ZeroParadox/Category/LawvereDecidable.lean` prices that footprint: with `[DecidableEq β]` the same
proof body measures `[propext]`. It closes with the correct fence — *"It does not show the general
version's choice is necessary. `classical` is how the proof was written, and a footprint never
reports necessity."*

**`LawvereTaboo.lean` answers that open question, and the answer is that the choice is NOT removable.**

## The result

`wem_of_fixedPointFree` — the ∀-closed general statement

```
∀ (β : Type) (b₀ b₁ : β), b₀ ≠ b₁ → ∃ g : β → β, ∀ x, g x ≠ x
```

implies **weak excluded middle** (`¬p ∨ ¬¬p` for every proposition `p`, equivalently De Morgan's
law), proved with **no `Classical.choice`**. The classical content is entirely in the hypothesis,
which is what makes this an implication rather than a restatement — the same shape as
`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`'s `em_of_wellOrder_comparable`, and the file is
modelled on it.

So `fixedPointFree_of_nontrivial`'s `classical` is **essential**, not accidental: no rewriting of
that proof removes it, because a choice-free proof of the general statement would be a choice-free
proof of weak excluded middle. This is the framework's second located essential case, and unlike the
first it sits on the keystone (the diagonal engine) rather than on an imported order instance.

## What is NOT claimed

* **Not full excluded middle.** The taboo landed on is weak excluded middle, which is strictly
  weaker than `ExcludedMiddle` in intuitionistic logic. No attempt was made here to strengthen it,
  and the reader should not assume it can be strengthened.
* **The converse is not proved.** Weak excluded middle gives the general statement back in
  univalent foundations, and that argument is published, not ours: de Jong–Escardó,
  arXiv:2601.12536, Prop 6.4, p. 24, *"If weak excluded middle holds and the type X has two distinct
  points, then X has a decomposition"*, proved by sending `x` to 0 if `¬(x ≠ x₀)` and to 1 if
  `¬¬(x ≠ x₀)`; the decomposition-to-endomap step in the prior-art section below then gives the
  fixed-point-free map. It is the argument this file had sketched as its own (the two mutually
  exclusive subobjects `¬(x = b₀)` and `¬¬(x = b₀)` cover, so a map can be glued from them). It
  does not go through in Lean for the same reason recorded in
  `ZeroParadox/Category/ExcludedMiddleBridge.lean` — `Or` in `Prop` does not eliminate into data, so
  a `Prop`-level disjunction cannot construct the function `g`. Whether the two statements are
  equivalent **in Lean** is left open, and a failed elaboration would not settle it either way.
* **No priority claim.** See the prior-art section; a search was run and is reported as a search.
* **It does not deprecate `ZeroParadox/Category/Lawvere.lean`.** The general statement stays general
  and stays the keystone. What changes is only its ledger classification: its `Classical.choice` is
  no longer unclassified or presumed accidental.

## Prior art

The mathematics of this genre is not new and is not claimed as new.

* **M. Escardó, TypeTopology, `Taboos.Decomposability`.** A type `X` is *decomposable* when there is
  `f : X → 𝟚` hitting both values; the module proves
  `Ordinal-decomposition-iff-WEM : decomposition (Ordinal 𝓤) ↔ typal-WEM 𝓤`, glossed there as *"the
  type of ordinals has no non-trivial decidable property unless weak excluded middle holds."* Read
  from source. **This is a close neighbour, and it is a different statement**; Booij–Escardó–
  Lumsdaine–Shulman Thm 3 and Thm 5 and de Jong–Escardó Prop 6.4 (both below) are as close.
  Decomposability is strictly stronger than what is used in `wem_of_fixedPointFree`: a decomposition
  `f : X → 𝟚` with witnesses `x₀ x₁` yields the fixed-point-free endomap
  `x ↦ if f x = 0 then x₁ else x₀` (it changes the value of `f`, so it cannot fix anything). So a
  fixed-point-free endomap is the *weaker* conclusion, which makes the implication to weak excluded
  middle formally the stronger one. That derivation is elementary and is ours, not Escardó's. No
  source stating the fixed-point-free form was located as of 2026-10-07, searched by phrase in
  theoremsearch and on the open web and among the sources listed here.
* **A. B. Booij, M. Escardó, P. LeFanu Lumsdaine and M. Shulman, "Parametricity, automorphisms of the
  universe, and excluded middle"** (arXiv:1701.05617). Read from source. Thm 3, p. 4, and Thm 5
  (Simpson), p. 5: the statements and the contrast with `wem_of_fixedPointFree` are in the comment
  above that theorem in `LawvereTaboo.lean`, which also credits Simpson's proof technique.
* **T. de Jong and M. Escardó, "Examples and counterexamples of injective types"**
  (arXiv:2601.12536, 18 January 2026). Read in full from the held copy; Prop 6.4, p. 24, is quoted
  under "What is NOT claimed" above. From the abstract verbatim: *"any type with an apartness
  relation and two points apart cannot be injective unless weak excluded middle holds"*, and
  *"injective types have no non-trivial decidable properties, unless weak excluded middle holds,
  which amounts to a Rice-like theorem for injective types."* Same genre and same landing principle
  — a hypothesis about a type with two separated points forcing weak excluded middle — about a
  different property (injectivity, not the existence of a fixed-point-free endomap).
* **Lawvere (1969)**; the diagonal-across-domains reading is **Yanofsky (2003)**. Both already cited
  in `ZeroParadox/Category/Lawvere.lean`; neither concerns the constructive strength of the
  supplier.
* Weak excluded middle, and the taboo methodology generally: **constructive reverse mathematics**
  (Ishihara; Diener-Ishihara). Cited, not claimed.

**Searched, none found** for the exact statement of `wem_of_fixedPointFree` — that is a report of one
search, not a priority claim.

## Structure of `LawvereTaboo.lean`

- § I   Weak excluded middle, as a hypothesis
- § II  The witness: three tokens glued by `p` on one side and by `¬p` on the other
- § III The taboo: the general fixed-point-free statement implies weak excluded middle
- § IV  Non-vacuity, and the ledger consequence for `Lawvere.lean`
