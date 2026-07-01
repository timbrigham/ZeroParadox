-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — TC13: the seam as a GENERIC theorem (the μ=ν coincidence is a real categorical fact)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

The seam node #5 (`fD_functor.obj 0 = StateSpace 0`) was previously characterised in
`ZPH_MC1_TreeSeam` as a zero object whose reading as "the μ=ν coincidence point / the diagonal
fixed point" was **explicitly fenced as framework interpretation, not a Lean claim**. This module
removes that fence for the structural half of the claim by upgrading it to a *generic* categorical
theorem.

**The load-bearing generic theorem** (`isZero_iff_isInitial_and_isTerminal`): in ANY category `C`,
for any object `Z`,
```
IsZero Z  ↔  Nonempty (IsInitial Z) ∧ Nonempty (IsTerminal Z).
```
This is exactly the statement "the zero object is the place where the least-fixed-point
characterisation (initial / colimit / μ) and the greatest-fixed-point characterisation
(terminal / limit / ν) literally coincide." It is proved with NO extra structure on `C` — no
pointed / preadditive / connecting-iso hypothesis. The backward direction is the content: an object
that is *both* initial and terminal already satisfies the `IsZero` predicate (which demands a unique
map out, from initiality, and a unique map in, from terminality). So the pre-registered NO-GO
(zero object strictly stronger than initial ∧ terminal, requiring preadditive) is **refuted**: the
coincidence is genuinely the whole story at the bare-category level.

**The named instance** (`seam_isZero_iff` and `seam_is_mu_nu_coincidence`): the equivalence is then
instantiated at `Z := fD_functor.obj 0`, reusing `hilbert_bottom_isZero`. The seam node concretely
witnesses both sides of the coincidence.

**What is proved vs. what stays interpretation.** PROVED (generic + instance): a zero object is
*exactly* an object that is simultaneously initial (μ) and terminal (ν), and the seam node #5 is such
an object. STILL INTERPRETATION (unchanged fence): that this μ=ν coincidence "is THE diagonal fixed
point" shared across the framework's other bottoms, and any cross-framework identity, remain the
meaning attached to the pattern — not asserted here. The upgrade is precisely: the *categorical*
meaning of "seam" ("μ and ν coincide here") is now a witnessed theorem, no longer a docstring gloss.
-/

namespace ZeroParadox.ZPH_MC1_TC13

open CategoryTheory CategoryTheory.Limits
open ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_MC1_TreeSeam

variable {C : Type*} [Category C]

/-- **The generic μ=ν coincidence theorem.** In any category, an object is a zero object
    (`IsZero`) **iff** it is both initial and terminal. The backward direction is the load-bearing
    content: bare initiality (a unique map *out* to every object — the μ / colimit side) together
    with bare terminality (a unique map *in* from every object — the ν / limit side) already
    furnishes the full `IsZero` predicate, with **no** pointed / preadditive hypothesis. So "zero
    object = the point where the least- and greatest-fixed-point characterisations coincide" is a
    real categorical fact, not extra structure. -/
theorem isZero_iff_isInitial_and_isTerminal (Z : C) :
    IsZero Z ↔ Nonempty (IsInitial Z) ∧ Nonempty (IsTerminal Z) := by
  constructor
  · intro h
    exact ⟨⟨h.isInitial⟩, ⟨h.isTerminal⟩⟩
  · rintro ⟨⟨hI⟩, ⟨hT⟩⟩
    refine ⟨fun Y => ?_, fun Y => ?_⟩
    · -- unique map OUT: from initiality (μ side)
      exact ⟨{ default := hI.to Y
               uniq := fun f => hI.hom_ext f (hI.to Y) }⟩
    · -- unique map IN: from terminality (ν side)
      exact ⟨{ default := hT.from Y
               uniq := fun f => hT.hom_ext f (hT.from Y) }⟩

/-- The seam node #5 (`fD_functor.obj 0`) satisfies the generic coincidence equivalence:
    it is a zero object iff it is both initial and terminal — and `hilbert_bottom_isZero` discharges
    the left side, so both sides hold for it. -/
theorem seam_isZero_iff :
    IsZero (fD_functor.obj 0)
      ↔ Nonempty (IsInitial (fD_functor.obj 0)) ∧ Nonempty (IsTerminal (fD_functor.obj 0)) :=
  isZero_iff_isInitial_and_isTerminal (fD_functor.obj 0)

/-- **The seam IS the μ=ν coincidence, as a theorem.** The seam node #5 is simultaneously initial
    (μ: least-fixed-point / colimit side) and terminal (ν: greatest-fixed-point / limit side). This
    is the structural content of "the seam is the μ=ν coincidence point," now witnessed rather than
    glossed: both `IsInitial` and `IsTerminal` are produced for the concrete node. -/
theorem seam_is_mu_nu_coincidence :
    Nonempty (IsInitial (fD_functor.obj 0)) ∧ Nonempty (IsTerminal (fD_functor.obj 0)) :=
  (seam_isZero_iff).mp hilbert_bottom_isZero

end ZeroParadox.ZPH_MC1_TC13

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC13

#print axioms isZero_iff_isInitial_and_isTerminal
#print axioms seam_isZero_iff
#print axioms seam_is_mu_nu_coincidence

end PurityCheck
