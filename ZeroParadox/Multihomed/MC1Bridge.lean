import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.State.HilbFunctor
import ZeroParadox.Multihomed.InfoFunctor

set_option maxHeartbeats 400000

/-!
# ZP-H MC-1 Correspondence: the snap floor realized across the real domain categories

## Engineer's Take

This is a hard one and inherently incomplete. The zero states correspond across domains, all of
which are vantage points to the same non returnable, 'empty' object. This is the same snap and
same verdict described by the original depth definitions in ZPH.

Identification with the same symbology is a commitment of this framework.

---

## Formal Overview
The correspondence half of MC-1 over the real domain categories (`TopCat`, `ModuleCat ℂ`, `KleisliCat PMF`): each
domain bottom is the categorical bottom of its own category, bundled in `mc1_correspondence`. The literal cross-category
identity is retired as ill-typed. Halves, prior art and positioning: `ZeroParadox/Multihomed/MC1Bridge.md`.
-/

namespace ZeroParadox

open CategoryTheory ZeroParadox ZeroParadox ZeroParadox ZeroParadox

/-! ### NO-GO gauge — `MC1Correspondence` is a BUNDLED WITNESS, not a requirements class.
It takes no parameter, so no carrier can fail to be a member — that follows from the missing
parameter, not from Prop-ness: two of its four fields are `IsInitial` **data**, which is why
`MC1Correspondence : Type 1` and `mc1_correspondence` is a `def`, the one inhabitant.

⚠ **The reading it must not license.** Bundling the three bottoms into one term does **not** make
them one object — that cross-category identity is **retired as ill-typed** (`x = y` across distinct
categories is not a well-formed proposition), and the members are provably distinct. What the bundle
establishes is the **correspondence** half: each domain bottom is the categorical bottom of its own
real Mathlib category. Cite the fields, never the bundle's existence. -/

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

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox ZeroParadox ZeroParadox ZeroParadox

-- M1 metric: per-functor choice footprint of the three MC-1 correspondence realizations.
-- F_B / TopCat
#print axioms fB_functor
#print axioms fB_bottom_is_limit
-- F_D / ModuleCat ℂ
#print axioms fD_functor
#print axioms fD_zero_isInitial
-- F_C / KleisliCat PMF
#print axioms fC_functor
#print axioms fC_zero_isInitial
#print axioms fC_no_return
-- Capstone
#print axioms mc1_correspondence

/- **M1 result (lake build, 2026-06-27).** All eight — `fB_functor`, `fB_bottom_is_limit`,
   `fD_functor`, `fD_zero_isInitial`, `fC_functor`, `fC_zero_isInitial`, `fC_no_return`,
   `mc1_correspondence` — footprint `[propext, Classical.choice, Quot.sound]`. The footprint is
   UNIFORM, not split: the kernel/fiber prediction (bottom choice-free / realization choice-bearing)
   is invisible here — even the bottom-identification `fB_bottom_is_limit` carries choice. That
   `Classical.choice` is inherited Mathlib tooling (TopCat / ModuleCat ℂ / KleisliCat PMF +
   category-theory machinery), NOT shown to be structural; separating library-vs-structural needs a
   choice-minimal re-derivation, not this footprint pass. -/

end PurityCheck
