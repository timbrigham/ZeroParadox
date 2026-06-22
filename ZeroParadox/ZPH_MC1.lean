import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_InfoFunctor

set_option maxHeartbeats 400000

/-!
# ZP-H MC-1 Correspondence: the snap floor realized across the real domain categories

## Engineer's Take

This is a hard one and inherently incomplete. The zero states correspond across domains, all of
which are vantage points to the same non returnable, 'empty' object. This is the same snap and
same verdict described by the original depth definitions in ZPH.

Identification with the same symbology is a commitment of this framework.

---

## Formal Overview (AI-assisted)

MC-1 is the cross-framework claim that the four domain bottoms are "the same single bottom".
It has two halves:

* a **correspondence** half — each domain's bottom is the categorical bottom (initial object /
  inverse limit) of that domain's own real structure, agreeing on the snap; and
* a **literal-identity** half — the four bottoms are numerically one object across four different
  categories.

This file formalizes the **correspondence half over the real domain categories**. Earlier, ZP-H
only exhibited this inside ℕ-shaped *proxy* categories (`Q₂BallDepth`, `InfoDepth`, `HilbDimDepth`).
Here the snap floor is realized inside the genuine Mathlib categories:

* **F_B / `TopCat`** (`fB_functor`): ⊥ is the inverse limit of the clopen-ball system,
  `⋂ n, B(0,2⁻ⁿ) = {0}` (`fB_bottom_is_limit`). `TopCat` has a terminal object, so the honest
  statement is "limit", not "initial".
* **F_D / `ModuleCat ℂ`** (`fD_functor`): ⊥ = `StateSpace 0` is the genuine initial (zero) object
  (`fD_zero_isInitial`); the embeddings are isometric (`fD_embed_inner`).
* **F_C / `KleisliCat PMF`** (`fC_functor`): ⊥ = `Fin 0` is the genuine initial object
  (`fC_zero_isInitial`), and there is **no** stochastic map back into it (`fC_no_return`) — AX-G2
  realized as a theorem, the snap's irreversibility.

(`F_A` — the join-semilattice ℕ with 0 initial — is already in `ZPH.lean`; it is omitted here only
to keep ℕ's category instance unambiguous, not for any mathematical reason.)

**Prior art / positioning.** None of the categorical structure here is new. `KleisliCat PMF` is the
Kleisli category of a probability monad — a *Markov category* in the sense of Fritz (2020), the
categorical home of stochastic maps (Stoch / FinStoch arise as the Kleisli category of the Giry monad;
cf. Golubtsov, Cho–Jacobs, Lawvere). In that setting `fC_no_return` is the *strict initiality* of the
empty object (Carboni–Lack–Walters 1993): every morphism into the initial object is an isomorphism, so
nothing maps back in. F_B's `⋂ B(0,2⁻ⁿ) = {0}` is the standard 2-adic inverse limit (ℤ₂ = lim ℤ/2ⁿ);
F_D's zero module is the zero/initial object of an abelian category. ZP-H's contribution is not new
category theory but the cross-domain *assembly* — each ZP bottom realized as its own real category's
categorical bottom, agreeing on the snap — with the single-object identification left as the MC-1
commitment.

`mc1_correspondence` bundles these into one witness. This is the **correspondence** half only; the
literal cross-category identity remains a chosen identification (the residual modeling commitment),
exactly as AX-1 became T-SNAP while a residue was kept, and as CC-2 / the diagonal fixed point are
fenced. It is *not* claimed here that the four bottoms are one object — only that each is the
categorical bottom of its own real category and they agree on the snap.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory ZeroParadox.ZPB ZeroParadox.ZPH_TopFunctor ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor

/-- The MC-1 correspondence over the real domain categories: the snap floor is the categorical
    bottom (initial object / inverse limit) of each domain's genuine Mathlib category, and the
    information bottom admits no return morphism. Bundles the three real-category realizations.
    This is the correspondence half of MC-1; the literal cross-category identity is not asserted. -/
structure MC1Correspondence : Type _ where
  /-- F_D: in `ModuleCat ℂ`, the snap floor `StateSpace 0` is the genuine initial (zero) object. -/
  hilb_initial : Limits.IsInitial (fD_functor.obj 0)
  /-- F_C: in `KleisliCat PMF`, the snap floor `Fin 0` is the genuine initial object. -/
  info_initial : Limits.IsInitial (fC_functor.obj 0)
  /-- F_C: AX-G2 realized — no stochastic map returns into the snap floor from a nonempty object. -/
  info_no_return : ∀ {n : ℕ}, 0 < n → IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0)
  /-- F_B: in `TopCat`, the snap floor is the inverse limit of the clopen-ball system. -/
  top_limit : (⋂ n, q2Ball n) = {(0 : Q₂)}

/-- The witness: all three real-category realizations hold simultaneously. -/
noncomputable def mc1_correspondence : MC1Correspondence where
  hilb_initial := fD_zero_isInitial
  info_initial := fC_zero_isInitial
  info_no_return := fun {_} hn => fC_no_return hn
  top_limit := fB_bottom_is_limit

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1

#print axioms mc1_correspondence

end PurityCheck
