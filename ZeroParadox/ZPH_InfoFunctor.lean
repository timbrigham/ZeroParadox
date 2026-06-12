import ZeroParadox.ZPC
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H Info Functor: F_C into the real category `KleisliCat PMF` (MC-1 remediation)

## Engineer's Take

Information theory is interesting here. Zero information in is zero information out by definition.
Any existence of non zero information in results in some statistically distributed, and by
definition a non zero distribution of information out.

---

## Formal Overview (AI-assisted)

ZP-H proves the snap floor ⊥ is the categorical initial object inside the *proxy* category
`InfoDepth` (a wrapper around ℕ). This file does the stronger, honest thing for the information
domain: it realizes the snap chain as a genuine functor into a *real* Mathlib category.

The real "category of information" is the Kleisli category of the finite-distribution monad `PMF` —
objects are finite types, morphisms are genuine stochastic maps (Markov kernels) `α → PMF β`,
composition is monadic bind. Mathlib already provides this for free: `KleisliCat.category` makes any
`LawfulMonad` into a `Category`, and `PMF` is a lawful monad. No category is defined here.

- `fC_functor : ℕ ⥤ KleisliCat PMF` — the snap chain as a real diagram of stochastic maps:
  object `n ↦ Fin n` (n distinguishable outcomes), morphism = the deterministic embedding
  `i ↦ pure (Fin.castLE h i)`.
- `fC_zero_isInitial` — ⊥ = `Fin 0` (the empty type, zero distinguishable outcomes) is the genuine
  initial object of `KleisliCat PMF`.
- `fC_no_return` — AX-G2 realized as a theorem, not an axiom: there is **no** stochastic map back
  into ⊥ = `Fin 0` from any nonempty object, because `PMF (Fin 0)` is empty (no distribution lives on
  the empty type). The snap's irreversibility, categorically.
- `fC_snap_info_grounded` — the snap step's informational cost is grounded in ZPC `t1b_jsd`
  (`jsdPQ = log 2`, one bit).

This is the F_C half of the OQ-G3 upgrade (MC-1 correspondence into the real domain categories).
-/

namespace ZeroParadox.ZPHInfo

open ZeroParadox.ZPC
open CategoryTheory

/-- Object map: depth `n` ↦ `Fin n`, the finite type of `n` distinguishable outcomes,
    as an object of the Kleisli category of `PMF`. -/
def fC_obj (n : ℕ) : KleisliCat PMF := KleisliCat.mk PMF (Fin n)

/-- The deterministic embedding stochastic map `Fin n → PMF (Fin m)` for `n ≤ m`:
    each outcome maps to its image under `Fin.castLE`, with certainty (`pure`). -/
noncomputable def fC_map {n m : ℕ} (h : n ≤ m) : fC_obj n ⟶ fC_obj m :=
  fun i => pure (Fin.castLE h i)

/-- F_C: the snap chain realized as a genuine functor into the real category `KleisliCat PMF`
    (the category of finite stochastic maps). Direct system (more outcomes as depth grows). -/
noncomputable def fC_functor : ℕ ⥤ KleisliCat PMF where
  obj n := fC_obj n
  map f := fC_map (leOfHom f)
  map_id n := by
    funext i
    simp [fC_map, KleisliCat.id_def]
  map_comp f g := by
    funext i
    simp [fC_map, KleisliCat.comp_def]

/-- ⊥ = `Fin 0` is the genuine initial object of `KleisliCat PMF`:
    there is exactly one stochastic map out of the empty type. -/
noncomputable def fC_zero_isInitial : Limits.IsInitial (fC_functor.obj 0) := by
  haveI : ∀ Y : KleisliCat PMF, Unique (fC_functor.obj 0 ⟶ Y) := fun _ =>
    { default := fun i => i.elim0
      uniq := fun _ => funext fun i => i.elim0 }
  exact Limits.IsInitial.ofUnique _

/-- AX-G2 realized as a theorem: no stochastic map returns into ⊥ = `Fin 0` from a nonempty
    object, because `PMF (Fin 0)` is empty. The categorical content of snap irreversibility. -/
theorem fC_no_return {n : ℕ} (hn : 0 < n) :
    IsEmpty (fC_functor.obj n ⟶ fC_functor.obj 0) := by
  refine ⟨fun f => ?_⟩
  have hsum : ∑' a : Fin 0, (f ⟨0, hn⟩) a = 1 := PMF.tsum_coe _
  rw [tsum_empty] at hsum
  exact zero_ne_one hsum

/-- The snap step's informational cost is grounded in ZPC: the P → Q transition costs exactly
    one bit (`jsdPQ = log 2`, T1b), paired with the existence of the snap morphism. -/
theorem fC_snap_info_grounded :
    Nonempty (fC_functor.obj 0 ⟶ fC_functor.obj 1) ∧ jsdPQ = Real.log 2 :=
  ⟨⟨fC_map (Nat.zero_le 1)⟩, t1b_jsd⟩

end ZeroParadox.ZPHInfo

/-! ## Axiom Purity Check

`Classical.choice` is expected here: it enters through Mathlib's `PMF` / `tsum` / `KleisliCat`
library. It is a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPHInfo

#print axioms fC_functor
#print axioms fC_zero_isInitial
#print axioms fC_no_return
#print axioms fC_snap_info_grounded

end PurityCheck

