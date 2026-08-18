# Which Rutten example governs which family, and a discriminator that fails

Argument, prior art and fences for `ZeroParadox/Computability/OutputSeparates.lean`. The Lean file holds
the declarations, the Engineer's Take and the per-declaration glosses.

**Experimental probe** in the bottom-diagram mapping campaign — not a finalized layer.

## What is claimed

**No new mathematics.** Two Lean-checked instances of a published formula, plus a cross-link to a third
the corpus already had.

**The governing result — Rutten, *Universal coalgebra: a theory of systems*, TCS 249 (2000), Example
10.2(5), printed p. 44** (`.claude-local/papers/rutten_universal_coalgebra_2000.pdf`; Rutten credits it
to his [52], Manes & Arbib 1986): for `F(S) = A × S^B` the final system is `A^{B*}`. A polynomial
functor `⟨A, fun _ => B⟩` is exactly that `F`, so its final coalgebra has `|A|^{|B*|}` elements — **a
single point iff `|A| = 1`, for every `B` whatsoever.** The head type decides; the arity `B` is
irrelevant to whether the final coalgebra is a single point.

The two instances proved:

* `binCofix_subsingleton` — `binPF = ⟨Unit, fun _ => Bool⟩` (`A = 1`, `B = 2`): `1^{2*}` is one element,
  so `Cofix binPF.Obj` is a **subsingleton**. Two recursive positions buy nothing.
  `ZeroParadox/Category/RootCutBinary.lean`'s `arity_collapse` already showed arity does not move the
  *seam* question; this shows it does not move the *cardinality* question either.
* `output_separates` — `streamPF = ⟨Bool, fun _ => PUnit⟩` (`A = 2`, `B = 1`): `2^{1*}` is the
  `Bool`-streams, and two of them are provably distinct.

**The corpus already had the `B = 0` instance and it was never connected:**
`ZeroParadox/Category/RootCutDegeneracy.lean`'s `cofixEquiv : Cofix (constPF A).Obj ≃ A`, since `B*` is
then a single point and `A^1 = A`. Three instances of one formula, in three files.

## ⚠ Read this before citing the file against `notEL_unique`

**Nothing here bears on `natPF`, and this file must not be cited as explaining `notEL_unique`.**

`natPF_NatListRegime = ⟨Bool, fun b => cond b PUnit PEmpty⟩` has head type `Bool` — the **same head type
as `streamPF`** — yet `GroundZero.notEL_unique` proves its non-terminating part is a single point. So
"what a step emits" does not discriminate: it is identical on both sides of that comparison.

The reason is a **family** difference, not a head difference. `natPF`'s child type *depends on its
head*, so it is **not** of the form `⟨A, fun _ => B⟩` and Rutten 10.2(5) does not apply to it.

**But `natPF` is outside 10.2(5), NOT outside the literature.** Rutten gives the dependent-arity case
three lines below on the same printed page — Example 10.2(6), `F(S) = C + (A × S^B)`, *"this example
subsumes all of the above examples"* — and `natPF.Obj X ≅ 1 + X` is his item (4), whose final system is
`(ℕ̄, pred)`. That is what `notEL_unique` witnesses, and `ZeroParadox/Computability/GroundZero.lean`
already cites it. So **both** families sit on one page of Rutten, as two different items.

## A discriminator that FAILS, recorded so it is not proposed again

*The number of head values with inhabited child type* does not discriminate. Machine-checked against it:

* `natPF` has count one yet `Cofix natPF` is not a point — `eventuallyLeaf_ne_infinity`
  (`ZeroParadox/Computability/NatListRegime.lean`) shows any behaviour reaching a leaf differs from
  `natInfinity`, so there are at least two;
* `constPF` has count zero yet `Cofix (constPF Bool)` has two elements.

It survives only if restricted to the non-terminating part, which is not what it said. Dropped rather
than repaired — it predicted nothing the cited formulas do not.

## Reading

`Reading:` CARRIER — the framework reads this as the computational-face counterpart of
`ZeroParadox/Valuation/BranchingRequirement.lean`, which argues branching is what makes the 2-adic
boundary a continuum "rather than a single chain's single end"; that file proves the *seed*
(`branches_incomparable`) and leans on `PadicTree`'s boundary for the continuum half, as its own
honest-scope paragraph states. On the 2-adic tree a branch choice **is** a digit, so branching and
head-labelling coincide there and come apart here. **Conjectural**: different carriers, no map between
them is claimed, and no framework bottom is identified with any behaviour here (⊥ does not appear).

## Fences

`output_separates` proves exactly **two** distinct behaviours, not the continuum. Rutten 10.2(5)
identifies the carrier as `2^{1*}` and states **no cardinality** — that the set is uncountable is
**Cantor's**, and is claimed nowhere here. **Uncountability is likewise NOT Adámek–Milius–Moss's**:
their Example 7.7 (p. 31, arXiv:1910.09401v2) gives the terminal coalgebra `A^∞ ∪ A*` and the initial
algebra `A*`, and no cardinality either. The general formula is cited, not formalized: what is
machine-checked is two of its instances.
