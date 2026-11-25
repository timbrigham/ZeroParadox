# ZP-G's surprisal against Kolmogorov complexity: the import, what the class carries, and what it does not

Overview for `ZeroParadox/Category/Category.lean`, on its § II and § IV. The Lean file holds the declarations,
the Engineer's Take and the per-declaration glosses.

## I-KC, the Kolmogorov import

ZP-G's surprisal D7' uses conditional Kolmogorov complexity. The pinned Lake dependency
kolmogorov-complexity-lean defines it as `Kolmogorov.condK` (plain, valued in `ℕ∞`;
`KolmogorovMathlib/Core/Basic.lean`), where `condK U x y` is the complexity of `x` given `y`, and proves a
conditional coding theorem for prefix complexity (`Kolmogorov.conditional_coding_equivalence`,
`KolmogorovMathlib/AlgorithmicProbability/ConditionalUniversalSemimeasure.lean`). `ZPSurprisal` is built from
neither. `Reading:` the import is cited, not consumed.

## D7' and the class `ZPSurprisal`

Given an encoding `enc : C → BitString` and an optimal decompressor `U`, D7' reads as
`fun {A B} (_ : A ⟶ B) => Kolmogorov.condK U (enc B) (enc A) : ℕ∞`. That is not an instance of
`ZPSurprisal`: the class asks for `ℕ` values and an exact zero on identities (`surp_id`), and `condK` gives
`ℕ∞` values and a bound. An exact zero on identities gives the bound, with constant `0`; the bound does not
give an exact zero. The class is also met by `surp := fun _ => 0`
(the NO-GO gauge in § I of the Lean file). This form was not elaborated.

## T6-a, identity surprisal

In Kolmogorov form T6-a is `Kolmogorov.condK_self` (`KolmogorovMathlib/Complexity/Properties.lean`): for an
optimal `U`, one constant `c` bounds `condK U x x` for every `x`. That matches the PDF's "0 up to the additive
constant". In `ZPSurprisal` it is the field `surp_id`, assumed and returned unchanged by
`t6a_identity_surprisal`.

## T6-b, non-negative surprisal, and its strict clause

"≥ 0" holds by type: `t6b_surprisal_nonneg` is `Nat.zero_le`. The PDF's strict clause, `I(f) > 0` when
`A ≠ B`, is not stated in Lean and is not invariant under the additive constant the PDF restricts its claims
to: `Kolmogorov.condK_comp` bounds `condK U (f x) x` by one constant for a computable `f`, distinct strings
included (for example `f x = true :: x`).

**Counting form of T6-b.** For every decompressor `V`, every `y` and every `k`, at most `2^(k+1) - 1`
strings `x` have `condK V x y ≤ k`: `Kolmogorov.card_condK_le_boundedPrograms_length`
(`KolmogorovMathlib/AlgorithmicStatistics/StrongModels/ProfileCardinality.lean`) bounds the size of any such
finite set by `(boundedPrograms k).length`, and `Kolmogorov.length_boundedPrograms_succ_eq`
(`KolmogorovMathlib/AlgorithmicStatistics/Selector.lean`) puts that length at `2^(k+1) - 1`. So at each
bound only finitely many targets fall at or below it. That no single target is forced above the constant
is `condK_comp`'s content, in the paragraph above, not the counting lemmas'. The
unconditional counterpart is `Kolmogorov.card_plainK_lt_mem_Icc`
(`KolmogorovMathlib/Complexity/CanonicalObjects/Counting.lean`).

## T6-c, surprisal along chains

`t6c_surprisal_sum_nonneg` states only that the sum is `≥ 0`, by `Nat.zero_le`; the sum of non-negative steps
is non-decreasing in the chain length with no lemma. Subadditivity bounds the end-to-end complexity from
ABOVE, so it shows no accumulation: `Kolmogorov.condK_triangle`
(`KolmogorovMathlib/Complexity/ConditionalComplexity/Continuity.lean`) carries a logarithmic term, and
`Kolmogorov.condK_trans_nat` (`KolmogorovMathlib/AlgorithmicStatistics/BoundedLists/StandardBlock/PrefixEquiv.lean`)
the bound `2a + b + C`. Strict growth of the sum would need T6-b's strict clause.
