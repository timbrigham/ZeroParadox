# Locators for AMM, the credit chain past them, and why the obvious descent fails

Prior art, delta and technique for `ZeroParadox/Category/NextTimeCategorical.lean`. The Lean file holds
the declarations, the Engineer's Take and the per-declaration glosses.

## What is built

`ZeroParadox/Category/WellFoundedCoalgebra.lean` states well-foundedness over `Set X` with a concrete
`nextTime`. Adámek–Milius–Moss state it over `Sub(A)` in a **category**. The Lean file builds their
version and proves the two agree, so the concrete predicate is no longer merely *shaped like* theirs.

## Prior art — locators, not quotations

Source: `.claude-local/papers/adamek_milius_moss_wellfounded_recursive_coalgebras.pdf`.

| AMM | what is there | built as |
|---|---|---|
| **Def 4.1, p. 14** | the next time operator `⃝(s) = α⁻¹(F s)` on `Sub(A)` | `nextTimeCat` |
| **Def 4.3, p. 15** | well-founded = `id_A` is the only fixed point of `⃝` | `IsWellFoundedCoalgCat` |
| **Def 4.7, p. 16** | the canonical graph (cited for orientation, not used) | — |

**⚠ AMM ARE NOT THE ORIGIN — the credit chain continues past them.** Def 4.1's own header reads
`Definition 4.1 [5, Def. 8.9]`, crediting their *Fixed points of functors* (JLAMP 95, 2018); the
next-time operator itself they credit to **Jacobs** `[17]`; and Def 4.3 they give *"as characterized by
Taylor [28, Exercise VI.17]"*.

⚠ **`[28]` is Taylor's *Practical Foundations of Mathematics* (CUP 1999), which this project does NOT
hold** — the Taylor PDF in `.claude-local/papers/` is his *Well founded coalgebras and recursion*, a
different document with no Exercise VI.17. The same caveat is stated at
`ZeroParadox/Category/WellFoundedCoalgebra.lean`'s overview.

## The delta

AMM's definitions are theirs; what is added is that they are now Lean objects, that `nextTimeCat` is
stated at **full generality** (any category with pullbacks, any mono-preserving endofunctor), and that
`isWellFoundedCoalgCat_iff` proves the categorical and concrete predicates equivalent for polynomial
functors on `Type u`.

## The technique, because the obvious route does not work

Mathlib's `Types.subobjectEquivSet : Subobject α ≃o Set α` is built from
`Equivalence.thinSkeletonOrderIso`, which selects representatives out of a quotient — it is
`noncomputable` and **nothing reduces through it**; `subobjectEquivSet X (Subobject.mk i) = Set.range i`
is neither `rfl` nor `simp`, and Mathlib supplies no computation lemmas for it.

The route taken instead: `Subobject X` **is** `ThinSkeleton (MonoOver X)`, a plain `Quotient`, so
descend with `Quotient.lift` directly, taking well-definedness from the fact that **`Set X` is a partial
order, where an isomorphism simply is an equality**. That makes `toSet_mk` hold by `rfl` and everything
downstream follows.

⚠ **`toSet` IS NOT CLAIMED TO BE `subobjectEquivSet`.** They are built from the same functor and ought to
agree, and **that agreement is not proved and is not needed**: the bridge uses only `toSet_injective`,
`toSet_surjective`, `toSet_eq_univ_iff` and `le_of_toSet_le`. Do not assert the two are the same
function without proving it.

## Axiom purity — the proofs are not the reason

Measured 2026-08-05.

**`CategoryTheory.Subobject` — the TYPE — carries `Classical.choice`, and so does `MonoOver`:**

```
CategoryTheory.Subobject          [propext, Classical.choice, Quot.sound]   <- the TYPE
CategoryTheory.MonoOver           [propext, Classical.choice, Quot.sound]   <- the TYPE
Subobject.mk / .arrow / .pullback / .lower   all the same
```

`#print axioms` follows the **statement**, so **every result mentioning `Subobject` is choice-carrying
no matter how it is proved.** Per `CLAUDE.md` § *Revalidate, don't redraft*: a type carrying an axiom
makes "removable" false for every possible proof. This is a fact about Mathlib's subobject machinery,
not about anything here.

**⚠ BUT `Subobject`-freedom is NECESSARY, NOT SUFFICIENT — and this control pair proves it.** These are
two of the four declarations whose statements avoid the subobject machinery entirely; the other two,
`monoOverPost` and `range_eq_of_monoOver_iso`, mention `MonoOver` and carry choice from it.

```
ofTypeFunctor_pfunctor_map   [propext, Quot.sound]          -- no Subobject, and clean
mem_range_pfunctor_map       [Classical.choice, Quot.sound] -- no Subobject, and NOT clean
```

`mem_range_pfunctor_map`'s reverse direction picks a preimage per child with `.choose`, and **that is
genuinely where its choice comes from** — measured: the forward direction alone, same statement
ingredients, is **axiom-free**, and `PFunctor.map` / `Set.range` are axiom-free. So `.choose` is an
**independent** source, not a shadow of the type.

`le_of_toSet_le` also selects (a factoring witness per element), but its statement mentions `Subobject`,
so the type has already settled its footprint and the selection is not separately visible there.

⚠ **Nothing is claimed removable.** That is a modal claim needing an exhibited clean proof or a
reduction. For anything mentioning `Subobject` it is in fact **false**, by the type; for
`mem_range_pfunctor_map` no such claim is made either way.
