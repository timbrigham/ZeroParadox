# Generation by iteration: the successor chain from the empty floor `Fin 0` to its colimit `ℕ`

Moved from `ZeroParadox/Category/Node4Generation.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

## Formal Overview (AI-assisted)

The GEN slot of the ⊥-matrix is **generation by iteration**: the floor ⊥ generates the structure built
above it as the least fixed point `lfp F = ⊔ₙ Fⁿ(⊥)` — the categorical Adámek construction (initial
algebra = colimit of the initial chain `0 → F0 → F²0 → …`; J. Adámek, *Free algebras and automata
realizations in the language of categories*, Comment. Math. Univ. Carolin. 15 (1974), 589–602). Mathlib
carries the *order-theoretic* engine
(`fixedPoints.lfp_eq_sSup_iterate`) and ZP carries the *ordinal* instance (`epsilonZero_eq_nfp`:
ε₀ = nfp(ω^·)0), but the *categorical* Adámek theorem (the initial algebra as the colimit of the initial
chain) was not located in the Mathlib then pinned (`5450b53`) as of 2026-10-31. Searched by grep along three
axes, each of which returns material that is near it and is not it: the proper name `Adámek` (citations
of Adámek–Rosický and Adámek–Rosický–Vitale, as bibliography entries and theorem references, in
`CategoryTheory/Presentable/`, `Generator/StrongGenerator.lean` and `Limits/Sifted.lean`, none of them the
initial-chain colimit); the
nouns `initial algebra` / `terminal coalgebra` (`CategoryTheory/Endofunctor/Algebra.lean`, Lambek's
lemma that the structure map of an initial algebra or terminal coalgebra is an isomorphism, and the
polynomial-functor W- and M-types under `Data/PFunctor/` and `Data/QPF/`, with no colimit
construction); and `transfinite` (`Order/TransfiniteIteration.lean`, the order-theoretic transfinite
iterate of `φ : I → I`; `CategoryTheory/SmallObject/Iteration/`, transfinite iteration of a successor
structure for the small object argument, which states no initial-algebra theorem). This file builds the canonical instance for node #4's floor.

**The construction.** Take the endofunctor `F X = X + 1` (whose initial algebra is `ℕ`). Its initial
chain is `Fⁿ(∅) = Fin n`, with connecting maps the inclusions `Fin n ↪ Fin (n+1)` (`Fin.castSucc`). The
**base of the chain is `Fin 0 = ∅` — node #4's Kleisli floor** (`fC_obj 0 = Fin 0`). Its colimit is `ℕ`,
with cocone legs `Fin.val : Fin n → ℕ`.

**`node4_generates_nat` — the GEN witness, stated as the colimit universal property** (in `Type`, to avoid
the bundled-hom category boilerplate; the universal property *is* the statement "ℕ is the colimit of the
chain"): for any target `P` and any compatible family `f n : Fin n → P` along the chain
(`f (n+1) i.castSucc = f n i`), there is a **unique** `g : ℕ → P` factoring every leg through `Fin.val`
(`g i.val = f n i`). So the floor `Fin 0` generates `ℕ` as the colimit of the iteration chain — the
categorical form of `lfp F = ⊔ₙ Fⁿ(⊥)`, rooted at node #4's bottom. Node #4 is thus not merely the initial
*object* (the μ-base, `node4_isColimit`) but the *seed of generation*.

**Honest scope.** One concrete Adámek instance (`X ↦ X+1`, initial algebra `ℕ`), at the `Type` level where
`Fin 0` is node #4's underlying object. NOT the general Adámek theorem (any ω-cocontinuous endofunctor),
which remains unbuilt. Proved: `ℕ` (with legs `Fin.val`) is the colimit of the successor chain rooted at
the floor `Fin 0`.
