-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree, TC20 / TC17 — does the seam keystone hold AT THE ARROW LEVEL (μ-arrow = ν-arrow)?

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC12/TC13 (`ZPH_MC1_TreeSeam.hilbert_bottom_isZero`) proved the seam node #5 is a **zero object**
(initial ∧ terminal) — an *object-level* coincidence of μ (initial / least-fixed-point / colimit) and
ν (terminal / greatest-fixed-point / limit). The deeper diagonal-fixed-point reading asks for an
*arrow-level* coincidence: at the seam the μ-witness arrow and the ν-witness arrow should be **the
same arrow**, an equality of the two universal endomorphisms, not merely two universal properties of
one object.

**Pre-registered GO (the claim under test):** for a zero object `Z`, the μ-arrow
`IsZero.isInitial.to Z : Z ⟶ Z` and the ν-arrow `IsZero.isTerminal.from Z : Z ⟶ Z` are equal — and
in fact both equal `𝟙 Z`. Instantiated at node #5 (`fD_functor.obj 0 = StateSpace 0`). This is the
literal μ=ν-as-arrow-equality at the seam.

**Pre-registered NO-GO (the deflation this race had to settle):** that equality is **DECORATIVE** —
it is a special case of two *generic* uniqueness facts (`IsInitial.to_self`, `IsTerminal.from_self`):
EVERY initial object `I` already has `hI.to I = 𝟙 I`, and EVERY terminal object `T` already has
`hT.from T = 𝟙 T`, each by the same "the only endomorphism of an initial/terminal object is the
identity" argument. So `to = id = from` carries no information that distinguishes the seam from a bare
initial object alone or a bare terminal object alone; it is not a property of the *seam* specifically.

**Verdict: NO-GO — the arrow-level keystone is DECORATIVE.** The race is decided IN Lean, both sides:

- `seam_mu_eq_nu_arrow` (node #5) and `zero_mu_eq_nu_arrow` (general Z) DO prove the GO equality
  `μ-arrow = ν-arrow`. So the construction is not false — the arrows literally coincide at the seam.
- BUT `initial_endo_is_id` and `terminal_endo_is_id` prove the *same* identity-collapse holds of any
  bare initial object and any bare terminal object, with **no zero/seam hypothesis**. And
  `seam_arrow_equality_factors_through_identity` packages the deflation: the seam equality factors
  through exactly these two generic facts (`= 𝟙 Z` on each side), so it inherits no seam-specific
  content. `collapse_fires_off_seam` then witnesses, in one statement about node #4, an initial object
  whose μ-collapse `to = 𝟙` holds while it is NOT a zero object — the genericity made decisive.

The genuine seam content therefore stays at the object level (TC13: #5 is a zero object, #4 is initial
∧ not terminal, #3 is not initial — a real three-way fork separation). The arrow-equality is true but
generic: it tells you nothing about the seam that it does not also tell you about every initial object
and every terminal object in isolation. Reported honestly as DECORATIVE rather than dressed up as a new
keystone result.

**Honest fence.** The Lean content is: (a) at a zero object the two universal endomorphisms are both
the identity hence equal (GO, true), and (b) that collapse is generic to initial-alone and
terminal-alone objects (the deflation, also true). "The seam IS the diagonal fixed point at the arrow
level" is NOT supported — the arrow level adds nothing past TC13.
-/

namespace ZeroParadox.ZPH_MC1_TC20

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPH_HilbFunctor

universe v u
variable {C : Type u} [Category.{v} C]

/-! ## The GO side: at a zero object the μ-arrow and the ν-arrow coincide. -/

/-- **GO (general).** For a zero object `Z`, the μ-witness endomorphism `Z → Z` from initiality and
    the ν-witness endomorphism `Z → Z` from terminality are equal — both are `𝟙 Z`. This is the
    literal μ=ν-as-arrow-equality the keystone asks for. -/
theorem zero_mu_eq_nu_arrow {Z : C} (hZ : Limits.IsZero Z) :
    hZ.isInitial.to Z = hZ.isTerminal.from Z := by
  rw [hZ.isInitial.to_self, hZ.isTerminal.from_self]

/-- **GO (node #5).** Instantiated at the Hilbert bottom `fD_functor.obj 0 = StateSpace 0`: the
    μ-arrow and the ν-arrow at the seam are the same arrow. Uses `hilbert_bottom_isZero` (TC13). -/
theorem seam_mu_eq_nu_arrow :
    (ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero).isInitial.to (fD_functor.obj 0)
      = (ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero).isTerminal.from (fD_functor.obj 0) :=
  zero_mu_eq_nu_arrow ZeroParadox.ZPH_MC1_TreeSeam.hilbert_bottom_isZero

/-! ## The NO-GO / deflation side: the collapse is generic, not seam-specific. -/

/-- **Deflation 1.** EVERY initial object `I` (no zero/seam hypothesis) has its canonical
    self-endomorphism equal to the identity. This is `IsInitial.to_self`; restated here to put the
    generic collapse IN a theorem of this module — it is the μ half of the arrow equality, available
    with no terminality at all. -/
theorem initial_endo_is_id {I : C} (hI : Limits.IsInitial I) : hI.to I = 𝟙 I :=
  hI.to_self

/-- **Deflation 2.** EVERY terminal object `T` (no zero/seam hypothesis) has its canonical
    self-endomorphism equal to the identity (`IsTerminal.from_self`) — the ν half, available with no
    initiality at all. -/
theorem terminal_endo_is_id {T : C} (hT : Limits.IsTerminal T) : hT.from T = 𝟙 T :=
  hT.from_self

/-- **The seam arrow equality factors through the identity (NO-GO capstone, content IN the statement).**
    At a zero object `Z` the seam equality `μ-arrow = ν-arrow` holds *because* each side is
    independently `𝟙 Z`: the μ-side equals `𝟙 Z` by initiality ALONE (`initial_endo_is_id`, no
    terminality used) and the ν-side equals `𝟙 Z` by terminality ALONE (`terminal_endo_is_id`, no
    initiality used). Since each generic fact is a property of bare initial / bare terminal objects,
    the seam contributes nothing beyond the object-level TC13: the arrow-level keystone is DECORATIVE.

    (Renamed from `arrow_collapse_is_generic`: the *statement* only asserts the factorization through
    `𝟙 Z`; the genericity claim — that this collapse needs no zero/seam hypothesis — is carried by the
    no-hypothesis lemmas `initial_endo_is_id` / `terminal_endo_is_id` and decisively witnessed by
    `collapse_fires_off_seam` below, not by this statement. The name now matches what it proves.) -/
theorem seam_arrow_equality_factors_through_identity {Z : C} (hZ : Limits.IsZero Z) :
    hZ.isInitial.to Z = 𝟙 Z
    ∧ hZ.isTerminal.from Z = 𝟙 Z
    ∧ hZ.isInitial.to Z = hZ.isTerminal.from Z :=
  ⟨initial_endo_is_id hZ.isInitial,
   terminal_endo_is_id hZ.isTerminal,
   zero_mu_eq_nu_arrow hZ⟩

/-- **The decisiveness witness (genericity IN the statement).** The deflation is sharp: there EXISTS
    an initial object whose μ-self-endomorphism is `𝟙` while the object is NOT a zero object — namely
    node #4, the Kleisli bottom `Fin 0`, which is initial but not terminal
    (`kleisli_bottom_not_terminal`). The statement bundles both facts about the SAME object: it is not
    a zero object, AND its initial self-endomorphism is still `𝟙`. So the μ-arrow collapse `to = 𝟙`
    genuinely fires off the seam — it does not characterize the seam. This is the load-bearing content
    that makes `seam_arrow_equality_factors_through_identity` a deflation rather than a keystone. -/
theorem collapse_fires_off_seam :
    ∃ (h : Limits.IsInitial (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)),
      ¬ Limits.IsZero (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)
      ∧ h.to (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0)
          = 𝟙 (ZeroParadox.ZPH_InfoFunctor.fC_functor.obj 0) := by
  refine ⟨ZeroParadox.ZPH_InfoFunctor.fC_zero_isInitial, ?_, ?_⟩
  · intro hZ
    exact (ZeroParadox.ZPH_MC1_TreeSeam.kleisli_bottom_not_terminal).false hZ.isTerminal
  · exact initial_endo_is_id ZeroParadox.ZPH_InfoFunctor.fC_zero_isInitial

end ZeroParadox.ZPH_MC1_TC20

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC20

#print axioms zero_mu_eq_nu_arrow
#print axioms seam_mu_eq_nu_arrow
#print axioms initial_endo_is_id
#print axioms terminal_endo_is_id
#print axioms seam_arrow_equality_factors_through_identity
#print axioms collapse_fires_off_seam

end PurityCheck
