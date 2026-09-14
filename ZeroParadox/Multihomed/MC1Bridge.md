# MC-1 over the real domain categories: what is assembled, and what is not claimed

Overview for `ZeroParadox/Multihomed/MC1Bridge.lean`. The Lean file holds the declarations, the Engineer's Take and the
per-declaration commentary. The results are described at each declaration, not listed again here.

## The two halves of MC-1

MC-1 is the cross-framework claim about the four domain bottoms. It has two halves:

* a **correspondence** half: each domain's bottom is the categorical bottom (initial object or inverse limit) of that
  domain's own real structure, and the four agree on the snap;
* a **literal-identity** half: the four bottoms are numerically one object across four different categories. That
  identity is **retired as ill-typed**, because `x = y` across distinct categories is not a well-formed proposition,
  and the members are provably distinct (the walls). What MC-1 keeps is the bottom *family*, characterized by a
  shared list of criteria; the choice of criteria is the commitment (CLAIMS.md, MC-1 row).

## What this file formalizes

The **correspondence half, over the real domain categories**. Earlier, ZP-H exhibited it only inside ℕ-shaped *proxy*
categories (`Q₂BallDepth`, `InfoDepth`, `HilbDimDepth`). Here the snap floor is realized inside the genuine Mathlib
categories:

* **F_B / `TopCat`** (`fB_functor`): ⊥ is the inverse limit of the clopen-ball system,
  `⋂ n, B(0,2⁻ⁿ) = {0}` (`fB_bottom_is_limit`). `TopCat` has a terminal object, so the honest statement is "limit",
  not "initial".
* **F_D / `ModuleCat ℂ`** (`fD_functor`): ⊥ = `StateSpace 0` is the genuine initial (zero) object (`fD_zero_isInitial`),
  and the embeddings are isometric (`fD_embed_inner`).
* **F_C / `KleisliCat PMF`** (`fC_functor`): ⊥ = `Fin 0` is the genuine initial object (`fC_zero_isInitial`), and there
  is **no** stochastic map back into it (`fC_no_return`). That is AX-G2 realized as a theorem, the snap's
  irreversibility.

`F_A` (the join-semilattice ℕ with 0 initial) is already in `ZeroParadox/Multihomed/CategoricalBridge.lean`. It is
omitted here only to keep ℕ's category instance unambiguous, not for any mathematical reason.

## Prior art and positioning

None of the categorical structure here is new.
- `KleisliCat PMF` is the Kleisli category of a probability monad: a *Markov category* in the sense of Fritz (2020),
  the categorical home of stochastic maps. Stoch and FinStoch arise as the Kleisli category of the Giry monad (cf.
  Golubtsov, Cho–Jacobs, Lawvere).
- In that setting `fC_no_return` is the *strict initiality* of the empty object (Carboni–Lack–Walters 1993): every
  morphism into the initial object is an isomorphism, so nothing maps back in.
- F_B's `⋂ B(0,2⁻ⁿ) = {0}` is the standard 2-adic inverse limit (ℤ₂ = lim ℤ/2ⁿ).
- F_D's zero module is the zero/initial object of an abelian category.

ZP-H's contribution is not new category theory but the cross-domain *assembly*: each ZP bottom realized as its own real
category's categorical bottom, agreeing on the snap.

## What the witness does and does not say

`mc1_correspondence` bundles these into one witness. It is the **correspondence** half only. It is *not* claimed that
the four bottoms are one object, which is retired as ill-typed; the claim is only that each is the categorical bottom of
its own real category and that they agree on the snap. This is the same discipline the framework applies elsewhere:

- AX-1 is retired. Its shape is proved as T-SNAP, and that the snap occurs follows from the occurrence commitment
  together with DA-1.
- CC-2 and the diagonal fixed point are fenced the same way.
