-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree TC18 — is the seam a genuine BRIDGE between the subtrees, or a coincidentally two-sided object?

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC08 proved #5 (`fD_functor.obj 0`, the Hilbert bottom) is the only zero object among the named
categorical bottoms; the seam file (`ZPH_MC1_TreeSeam`) proved it *straddles* — it is initial ∧
terminal in its own category `ModuleCat ℂ`. The tree's structural claim is stronger: the seam should
**connect** the μ-subtree and the ν-subtree, i.e. admit a canonical morphism FROM every μ-side bottom
and a canonical morphism TO every ν-side bottom inside a single ambient category. TC18 races the
two readings.

**GO reading (provable, but generic).** Within `ModuleCat ℂ`, the zero object `Z = fD_functor.obj 0`
is genuinely two-sided: for every object `X` there is a map `Z ⟶ X` (initiality) AND `X ⟶ Z`
(terminality). This is `seam_two_sided`. It is honest, and it is exactly the *definition* of a zero
object restated (`IsZero.unique_to` / `IsZero.unique_from`) — true of ANY zero object in ANY category,
not a special bridging fact about these bottoms. We state it as what it is.

**NO-GO reading (the substantive finding).** The two-sidedness is **parametrized over
`ModuleCat ℂ` objects only**. The actual cross-subtree bottoms do NOT live in `ModuleCat ℂ`:
#4 the Kleisli bottom `Fin 0` lives in `KleisliCat PMF`, #3 the p-adic floor `{0}` lives in `TopCat`,
#1 the order floor `0` lives in `ℕ`. They are not objects `X : ModuleCat ℂ`, so `seam_two_sided`
**cannot be instantiated at them** — there is no map `Z ⟶ (Fin 0 : KleisliCat)` or
`(Fin 0 : KleisliCat) ⟶ Z`, because those would be morphisms between objects of different categories,
which do not typecheck. The witness that the seam does not reach the μ-subtree as a *bridge node* is
`kleisli_bottom_not_terminal` (reused from the seam file): #4 `Fin 0` is initial but NOT terminal in
its OWN category — its universal-property profile differs from the seam's, so even up to the obvious
correspondence the seam's two-sidedness is not shared by the μ-side bottom. The deflation theorem
`seam_is_intra_category` records the honest scope: two-sidedness holds for ModuleCat objects, and the
μ-side bottom fails terminality in its own category — so the seam is a two-sided *object*, not a
two-sided *bridge* across the categories where the other bottoms actually live.

**Verdict: NO-GO (deflation confirmed).** The GO statement is true but is the definitional content of
"zero object" (generic), not a cross-subtree edge. The seam has a seam *node* (#5) but no seam
*edges* to the μ/ν bottoms in their own categories — confirming the table §4(b) finding that the
diagram has separations but no global tie. The cross-framework bridge is interpretation, not Lean.

**Honest fence.** What Lean proves: (1) `seam_two_sided` — within `ModuleCat ℂ`, the zero object is
two-sided for every ModuleCat object (definitional); (2) `seam_is_intra_category` — the two-sidedness
is paired with the μ-side bottom's failure of terminality in its own category, so the two profiles
differ. What is interpretation: that this pattern means "the seam is/ is not the diagonal-fixed-point
bridge." The Lean content is the scope, not the metaphysics.
-/

namespace ZeroParadox.ZPH_MC1_TC18

open CategoryTheory
open ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor
open ZeroParadox.ZPH_MC1_TreeSeam

/-- The seam object: the Hilbert bottom `fD_functor.obj 0`, a zero object of `ModuleCat ℂ`. -/
noncomputable abbrev Z : ModuleCat ℂ := fD_functor.obj 0

/-- **GO (true, but generic).** Within `ModuleCat ℂ`, the seam `Z` is two-sided: for every object `X`
    there is a canonical map `Z ⟶ X` (from initiality, the colimit-target / μ end) AND `X ⟶ Z`
    (from terminality, the limit-source / ν end). Reuses `hilbert_bottom_isZero`.

    HONEST SCOPE: this is the *definition* of a zero object restated (`IsZero.unique_to` /
    `IsZero.unique_from`). It is true of ANY zero object in ANY category — it is NOT a special
    bridging fact about the framework bottoms. The quantifier ranges over `ModuleCat ℂ` ONLY. -/
theorem seam_two_sided (X : ModuleCat ℂ) : Nonempty (Z ⟶ X) ∧ Nonempty (X ⟶ Z) :=
  ⟨⟨hilbert_bottom_isZero.isInitial.to X⟩, ⟨hilbert_bottom_isZero.isTerminal.from X⟩⟩

/-- **NO-GO / deflation.** The seam's two-sidedness is an **intra-category** property of `ModuleCat ℂ`:
    it holds for every `ModuleCat ℂ` object, and the actual μ-subtree bottom #4 (`fC_functor.obj 0 = Fin 0`,
    living in `KleisliCat PMF`, NOT in `ModuleCat ℂ`) does not share the seam's universal-property
    profile — it is initial but **not terminal** in its own category (`kleisli_bottom_not_terminal`).
    So the seam is a two-sided *object*, not a two-sided *bridge*: `seam_two_sided` cannot be
    instantiated at the cross-category bottoms (they are not `ModuleCat ℂ` objects — no such morphism
    typechecks), and the μ-side bottom's profile differs even in its own home. The conjunction is the
    load-bearing witness that there is a seam node but no seam edge to the μ-subtree. -/
theorem seam_is_intra_category :
    (∀ X : ModuleCat ℂ, Nonempty (Z ⟶ X) ∧ Nonempty (X ⟶ Z))
    ∧ IsEmpty (Limits.IsTerminal (fC_functor.obj 0)) :=
  ⟨seam_two_sided, kleisli_bottom_not_terminal⟩

end ZeroParadox.ZPH_MC1_TC18

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC18

#print axioms seam_two_sided
#print axioms seam_is_intra_category

end PurityCheck
