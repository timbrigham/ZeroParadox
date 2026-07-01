-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1
import ZeroParadox.ZPH_MC1_Heterogeneous

set_option maxHeartbeats 400000

/-!
# A conjunction of three already-proved facts about the three domain bottoms

**Proves.** `no_uniform_character` bundles three pre-existing witnesses into one record: (C)
`fC_functor.obj 0` is initial in `KleisliCat PMF` (`fC_zero_isInitial`) with no return morphism for `n>0`
(`fC_no_return`); (D) `fD_functor.obj 0` is initial in `ModuleCat ℂ` (`fD_zero_isInitial`) and admits a
morphism back (`fD_has_return`, which is the ZERO morphism `⟨0⟩`); (B) `⋂ q2Ball n = {0}`
(`fB_bottom_is_limit`, a set equation). `initial_underdetermines` restates the C/D halves. No NEW theorem
is proved — it is a conjunction of facts proved elsewhere.

**Reaching for (intent, NOT proved here).** This was *meant to be* the "no uniform universal character"
shadow of the unification obstruction — the observation that F_C (strict-initial), F_D (non-strict
zero-object), and F_B (a limit, not an initial object) carry different universal characters, so no single
universal property is the uniform "character of ⊥", and a unified object would have to live one level up.

**Gap (as far as this reaches).** Two honest qualifications. (i) It is a *bundling* of already-available
witnesses, not new content. (ii) The F_D "return morphism" is the **zero morphism** — the trivial map that
every zero object has — so "F_D's bottom is bidirectional, a richer character" reads more than the
witness gives. The "no unification / obstruction shadow / one level up" framing is interpretation; the
unified-object claim is conjecture (`mc1_global_zero_construction_spec_2026-06-28.md`, see its correction).

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPH_MC1

open CategoryTheory ZeroParadox.ZPB ZeroParadox.ZPH_TopFunctor
  ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor

/-- The three heterogeneous universal characters of the MC-1 bottoms, bundled: F_C strict-initial,
    F_D non-strict-initial (zero object), F_B an inverse limit (not an initial object). Witness that no
    single universal character is shared — the formal shadow of the Global-Zero unification obstruction. -/
structure NoUniformCharacter : Prop where
  /-- F_C's bottom is an initial object of `KleisliCat PMF`. -/
  c_initial : Nonempty (Limits.IsInitial (fC_functor.obj 0))
  /-- F_C's bottom is STRICT initial: for `0 < n` no morphism returns into it. -/
  c_strict : ∀ {n : ℕ}, 0 < n → IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0)
  /-- F_D's bottom is ALSO an initial object of `ModuleCat ℂ`. -/
  d_initial : Nonempty (Limits.IsInitial (fD_functor.obj 0))
  /-- F_D's bottom is NON-strict (a zero object): a return morphism always exists. Same "initial"
      label as F_C, different character. -/
  d_nonstrict : ∀ {n : ℕ}, Nonempty (fD_functor.obj n ⟶ fD_functor.obj 0)
  /-- F_B's bottom is the inverse LIMIT of the ball system, `⋂ q2Ball n = {0}` — a limit-of-the-diagram,
      not a functor value, categorically a different kind of bottom from the F_C/F_D initials. -/
  b_limit : (⋂ n, q2Ball n) = {(0 : Q₂)}

/-- **M1.** The MC-1 bottoms share no uniform universal character: F_C strict-initial, F_D
    non-strict-initial (zero object), F_B an inverse limit. All from proved witnesses. -/
theorem no_uniform_character : NoUniformCharacter where
  c_initial := ⟨fC_zero_isInitial⟩
  c_strict := fun {_} hn => fC_no_return hn
  d_initial := ⟨fD_zero_isInitial⟩
  d_nonstrict := fun {_} => fD_has_return
  b_limit := fB_bottom_is_limit

/-- **"Initial" under-determines the bottom.** F_C and F_D bottoms are both initial yet categorically
    distinct: for `0 < n`, F_C admits no return while F_D does. The surplus character beyond "initial"
    disagrees across domains — the core of the obstruction, in one line. -/
theorem initial_underdetermines {n : ℕ} (hn : 0 < n) :
    IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0) ∧
      Nonempty (fD_functor.obj n ⟶ fD_functor.obj 0) :=
  ⟨fC_no_return hn, fD_has_return⟩

end ZeroParadox.ZPH_MC1

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1
#print axioms no_uniform_character
#print axioms initial_underdetermines
end PurityCheck
