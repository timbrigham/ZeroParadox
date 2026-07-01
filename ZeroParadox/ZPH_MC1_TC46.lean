-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPH_InfoFunctor
import ZeroParadox.ZPH_MC1_TreeObstructions
import ZeroParadox.ZPH_MC1_TreeSeam
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H tree — TC44: the seam's arrow-level signature (zero object vs bare-initial)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

TC20/TC38 found `IsInitial.to = IsTerminal.from` at the seam node #5 (the Hilbert bottom
`fD_functor.obj 0`, a *zero object* of `ModuleCat ℂ`) and **deflated** it: that particular equation
is generic — each side is independently the identity `𝟙`, so the equation also fires at #4 (the
Kleisli bottom `Fin 0`, which is initial-only) on the available endo. The deflation question TC44
asks is sharper: is there ANY purely arrow-level (hom-set-level) property that genuinely *separates*
the zero object (#5) from the bare-initial object (#4) — or is terminality contributing no new
arrow-level constraint, so the seam is characterizable only at the OBJECT level (initial ∧ terminal)?

**Verdict: GO — there is a genuine arrow-level separator.** It is the *existence half of terminality
stated as a hom-set property*:

> **P_in(Z)** : for every object `Y`, the in-hom-set `Hom(Y, Z)` is **nonempty**.

This is a statement about hom-sets only (no object-level data), and:

- `seam_has_Pin` — **P_in holds at #5.** `fD_functor.obj 0` is terminal in `ModuleCat ℂ`
  (`ZPH_MC1_TreeObstructions.fD_zero_isTerminal`), so every in-hom-set is nonempty (it has the
  terminal arrow `IsTerminal.from`).
- `bare_initial_fails_Pin` — **P_in FAILS at #4.** `Hom(fC_functor.obj 1, fC_functor.obj 0)` is
  **empty** (`fC_no_return`: no stochastic map returns into `Fin 0` from a nonempty type), so there
  is an object `Y` with `Hom(Y, #4)` empty. P_in is false at the bare-initial bottom.
- `tc44_arrow_level_separates` — the headline: P_in(#5) ∧ ¬P_in(#4). Terminality DOES add
  arrow-level content (all in-hom-sets become inhabited) that initiality alone does not supply at
  these bottoms. The seam has an arrow-level signature, sharpening TC20 from "generic collapse" to a
  genuine arrow-level distinction.

**The control — the deflation TC20 was right about.** The endomorphism-subsingleton property is
NOT a separator (it is the property TC20/TC38 over-read):

- `seam_endo_subsingleton` — `Hom(#5, #5)` is a subsingleton (initial ⇒ unique out).
- `bare_initial_endo_subsingleton` — `Hom(#4, #4)` is ALSO a subsingleton (initial ⇒ unique out),
  vacuous-or-unique. So endo-subsingleton holds at both → does NOT characterize the seam.
- `endo_subsingleton_does_not_separate` — both endo-monoids are subsingletons: this property is
  generic, confirming TC20's deflation *for this property*.

**Honest fence — what is Lean vs interpretation.** Lean proves exactly: P_in holds at #5 and fails
at #4 (a hom-set-nonemptiness property genuinely separating the two), while endo-subsingleton holds
at both. The reading "P_in is THE arrow-level seam signature, so the seam is arrow-characterizable"
is the interpretation; P_in is the *existence half* of terminality re-expressed at the hom-set
level, so what is rigorously shown is that terminality's existence content is not generic across
these specific bottoms — initiality alone does not force it. We do NOT claim P_in characterizes the
seam among ALL objects (that would need a uniqueness/quantification statement over every object);
the Lean content is the named-bottom separation #5 vs #4. The earlier endo-equation reading (TC20)
remains correctly deflated.
-/

namespace ZeroParadox.ZPH_MC1_TC46

open CategoryTheory
open ZeroParadox.ZPD ZeroParadox.ZPB
open ZeroParadox.ZPH_HilbFunctor ZeroParadox.ZPH_InfoFunctor
open ZeroParadox.ZPH_MC1_TreeObstructions

/-! ## The separating arrow-level property: P_in (all in-hom-sets nonempty) -/

/-- **P_in holds at the seam (#5).** For every object `Y` of `ModuleCat ℂ`, the in-hom-set
    `Hom(Y, fD_functor.obj 0)` is nonempty — because the Hilbert bottom is *terminal*
    (`fD_zero_isTerminal`), so it receives a (terminal) arrow from every object. This is the
    existence half of terminality stated purely as a hom-set property. -/
theorem seam_has_Pin :
    ∀ Y : ModuleCat ℂ, Nonempty (Y ⟶ fD_functor.obj 0) :=
  fun Y => ⟨fD_zero_isTerminal.from Y⟩

/-- **P_in FAILS at the bare-initial bottom (#4).** The in-hom-set
    `Hom(fC_functor.obj 1, fC_functor.obj 0)` is *empty* (`fC_no_return`: no stochastic map returns
    into `Fin 0` from the nonempty `Fin 1`). So there is an object `Y` with `Hom(Y, #4)` empty —
    P_in is false. This is exactly the failure of terminality at #4. -/
theorem bare_initial_fails_Pin :
    ¬ (∀ Y : KleisliCat PMF, Nonempty (Y ⟶ fC_functor.obj 0)) := by
  intro h
  exact (fC_no_return (by norm_num : 0 < 1)).false (h (fC_functor.obj 1)).some

/-- **TC44 headline — an arrow-level property genuinely separates the seam from the bare-initial.**
    P_in (every in-hom-set nonempty) holds at #5 (the zero object) and FAILS at #4 (initial-only).
    Terminality therefore contributes arrow-level content — all in-hom-sets inhabited — that
    initiality alone does not give at these bottoms. This sharpens TC20/TC38's "generic collapse"
    into a genuine arrow-level distinction: the seam carries a hom-set-level signature. -/
theorem tc44_arrow_level_separates :
    (∀ Y : ModuleCat ℂ, Nonempty (Y ⟶ fD_functor.obj 0))
    ∧ ¬ (∀ Y : KleisliCat PMF, Nonempty (Y ⟶ fC_functor.obj 0)) :=
  ⟨seam_has_Pin, bare_initial_fails_Pin⟩

/-! ## The control: endo-subsingleton is generic (the TC20 deflation, confirmed) -/

/-- **Endo-subsingleton at #5.** `Hom(fD_functor.obj 0, fD_functor.obj 0)` is a subsingleton:
    the Hilbert bottom is initial (`fD_zero_isInitial`), and an initial object has a unique arrow
    out of it (to itself), so its endomorphism monoid has at most one element. -/
theorem seam_endo_subsingleton :
    Subsingleton (fD_functor.obj 0 ⟶ fD_functor.obj 0) :=
  ⟨fun f g => fD_zero_isInitial.hom_ext f g⟩

/-- **Endo-subsingleton at #4 — the SAME property holds.** `Hom(fC_functor.obj 0, fC_functor.obj 0)`
    is a subsingleton: `Fin 0` is initial (`fC_zero_isInitial`), so its self-hom-set has a unique
    element. Endo-subsingleton therefore does NOT separate #5 from #4 — it is generic. -/
theorem bare_initial_endo_subsingleton :
    Subsingleton (fC_functor.obj 0 ⟶ fC_functor.obj 0) :=
  ⟨fun f g => fC_zero_isInitial.hom_ext f g⟩

/-- **The control result — endo-subsingleton is generic.** The endomorphism monoid is a subsingleton
    at BOTH the seam (#5) and the bare-initial bottom (#4). So the endo-subsingleton property does
    not distinguish them: this is the property TC20/TC38 over-read as a seam signature, and it is
    confirmed here to be generic (driven by initiality alone, present off-seam). Contrast with
    `tc44_arrow_level_separates`, where P_in genuinely separates. -/
theorem endo_subsingleton_does_not_separate :
    Subsingleton (fD_functor.obj 0 ⟶ fD_functor.obj 0)
    ∧ Subsingleton (fC_functor.obj 0 ⟶ fC_functor.obj 0) :=
  ⟨seam_endo_subsingleton, bare_initial_endo_subsingleton⟩

/-! ## The full TC44 picture in one statement -/

/-- **TC44, assembled.** A clean four-way summary at the arrow level:
    (1) P_in holds at the seam #5; (2) P_in fails at the bare-initial #4 — so P_in *separates*;
    (3) endo-subsingleton holds at #5; (4) endo-subsingleton holds at #4 — so endo-subsingleton
    does *not* separate. The contrast (separator found, generic property correctly excluded) is the
    sharpening of the TC20/TC38 deflation: the seam DOES have an arrow-level signature, but it is
    the in-hom-nonemptiness (terminality-existence) property, not the endo-equation TC20 used. -/
theorem tc44_full :
    (∀ Y : ModuleCat ℂ, Nonempty (Y ⟶ fD_functor.obj 0))
    ∧ ¬ (∀ Y : KleisliCat PMF, Nonempty (Y ⟶ fC_functor.obj 0))
    ∧ Subsingleton (fD_functor.obj 0 ⟶ fD_functor.obj 0)
    ∧ Subsingleton (fC_functor.obj 0 ⟶ fC_functor.obj 0) :=
  ⟨seam_has_Pin, bare_initial_fails_Pin, seam_endo_subsingleton, bare_initial_endo_subsingleton⟩

end ZeroParadox.ZPH_MC1_TC46

/-! ## Axiom Purity Check

`Classical.choice` is expected via the Mathlib `ModuleCat` / `KleisliCat` / `PMF` / `EuclideanSpace`
libraries — a library dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC46

#print axioms seam_has_Pin
#print axioms bare_initial_fails_Pin
#print axioms tc44_arrow_level_separates
#print axioms seam_endo_subsingleton
#print axioms bare_initial_endo_subsingleton
#print axioms endo_subsingleton_does_not_separate
#print axioms tc44_full

end PurityCheck
