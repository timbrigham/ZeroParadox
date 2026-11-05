# MC-1 over the real domain categories: what is assembled, and what is not claimed

Overview for `ZeroParadox/Multihomed/MC1Bridge.lean`. The Lean file holds the declarations, the Engineer's Take and the
per-declaration commentary. The results are described at each declaration, not listed again here.

## The retired identity reading

MC-1 is the cross-framework claim about the four domain bottoms. It was stated in two halves, and the second is retired:

* a **correspondence** half: each domain's floor has a categorical characterization in that domain's own real
  category, and it differs by category: a zero object (`Statement:` COINCIDENCE, initial and terminal at once) in `ModuleCat ℂ`, initial and not
  terminal in `KleisliCat PMF`, terminal and not initial in `TopCat`; the three full positions are stated together in
  `floor_positions_full` (`ZeroParadox/Category/TreeSeam.lean`: a zero object; initial and not terminal; terminal and not
  initial); the four agree on the snap;
* a **literal-identity** half: the four bottoms are numerically one object across four different categories. That
  identity is **retired as ill-typed** (object equality across categories does not typecheck and is not invariant under
  equivalence); what separates the members is proved property by property (`seam_unique_among_named`,
  `ZeroParadox/Category/SeamUniqueness.lean`, for the named bottoms, in a lattice with no top). What MC-1 keeps is the bottom *family*, characterized by a
  shared list of criteria; the choice of criteria is the commitment (CLAIMS.md, MC-1 row).

## What this file formalizes

The **correspondence half, over the real domain categories**. Earlier, ZP-H exhibited it only inside ℕ-shaped *proxy*
categories (`Q₂BallDepth`, `InfoDepth`, `HilbDimDepth`). Here the snap floor is realized inside the genuine Mathlib
categories:

* **F_B / `TopCat`** (`fB_functor`): ⊥ is the inverse limit of the clopen-ball system, as a limit cone
  in `TopCat` (`floorConeIsLimit`, `ZeroParadox/Order/PadicLimitCone.lean`); the set equation beneath it
  is `⋂ n, B(0,2⁻ⁿ) = {0}` (`fB_bottom_is_limit`). `{0}` is terminal in `TopCat` (it has one point;
  `padic_bottom_isTerminal`) and not initial (`padic_bottom_not_initial`), so "initial" is false here; the limit
  statement is `floorConeIsLimit`.
* **F_D / `ModuleCat ℂ`** (`fD_functor`): ⊥ = `StateSpace 0` is the genuine initial object (`fD_zero_isInitial`) and a
  zero object, terminal as well (`hilbert_bottom_isZero`); the embeddings are isometric (`fD_embed_inner`).
* **F_C / `KleisliCat PMF`** (`fC_functor`): ⊥ = `Fin 0` is the genuine initial object (`fC_zero_isInitial`), and there
  is **no** stochastic map into it from any later stage of the functor (`fC_no_return`), so it is not terminal
  (`kleisli_bottom_not_terminal`). That is AX-G2 realized as a theorem, the snap's irreversibility.

`F_A` (the join-semilattice ℕ with 0 initial) is already in `ZeroParadox/Multihomed/CategoricalBridge.lean`. It is
omitted here only to keep ℕ's category instance unambiguous, not for any mathematical reason.

## Prior art and positioning

None of the categorical structure here is new.
- `KleisliCat PMF` is the Kleisli category of a probability monad: a *Markov category* in the sense of Fritz (2020),
  the categorical home of stochastic maps. Stoch and BorelStoch arise as Kleisli categories of the Giry monad (Fritz 2020,
  § 4, via Cor. 3.2); FinStoch is defined directly (Ex. 2.5) (cf. Golubtsov, Cho–Jacobs, Lawvere).
- A *strict* initial object is one where every morphism into it is an isomorphism; nLab cites Carboni–Lack–Walters
  1993, Def. 2.7, for strict initial objects. `fC_no_return` is scoped to the functor's image: it states
  `IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0)` for `0 < n`, not strict initiality in the whole category.
- F_B's `⋂ B(0,2⁻ⁿ) = {0}` is the standard fact that nested closed balls about a point with radii
  tending to 0 meet in that point; the inverse system here is of subspace inclusions, not the
  quotient system of the presentation ℤ₂ = lim ℤ/2ⁿ. That `{0}` with its inclusions is then a limit cone
  (`floorConeIsLimit`) is the standard computation of limits in `Top` on underlying sets with the initial topology
  (Mathlib `TopCat.limitCone`, `TopCat.limitConeIsLimit`); the proof here builds the cone directly rather than
  through them.
- F_D's zero module is the zero object (`Statement:` COINCIDENCE, initial and terminal at once) of an abelian category; Mathlib
  `ModuleCat.isZero_of_subsingleton`.

ZP-H's contribution is not new category theory but the cross-domain *assembly*: each ZP floor characterized in its own
real category, at a different position in each (above), agreeing on the snap.

## What the witness does and does not say

`mc1_correspondence` bundles two `IsInitial` fields (`ModuleCat ℂ`, `KleisliCat PMF`), the no-return field
(`fC_no_return`) and the `TopCat` set equation (`fB_bottom_is_limit`) into one witness; `floorConeIsLimit`,
`padic_bottom_isTerminal` and `padic_bottom_not_initial` sit outside it. It is the **correspondence** half only. It is
*not* claimed that the four bottoms are one object, which is retired as ill-typed; the claim is only the per-category
characterization above and that they agree on the snap. This is the same discipline the framework applies elsewhere, with one difference kept visible:

- AX-1 is retired. Its shape is proved as T-SNAP, and that the snap occurs follows from the occurrence commitment
  together with DA-1 (closed given DP-2); that commitment remains. The identity reading leaves nothing to commit to:
  in the typed language it was never a well-formed proposition.
- CC-2 and the diagonal fixed point are fenced the same way.
