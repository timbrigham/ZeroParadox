import ZeroParadox.ZPG

/-!
# B4 (pipeline): AX-G2 is derivable from strict-initiality (a ZP-G posit collapses)

Experiment B4 (T2 reduce-the-posit): `ZPCategory.ax_g2` (source asymmetry:
`IsEmpty (X ≅ 0) → IsEmpty (X ⟶ 0)`) is posited. Its own docstring claims it "is the standard notion of a
strict initial object (Carboni–Lack–Walters 1993): every morphism into 0 is an iso." This experiment tests
whether that prose claim is a THEOREM — i.e. whether AX-G2 reduces to strict-initiality with no extra
hypothesis.

**Result: CONFIRMED.** AX-G2 derives from strict-initiality alone (no non-terminal/balancedness needed).
If every morphism into `zero` is an iso, then a morphism `f : X → zero` makes `X ≅ zero`; contrapositive
is exactly AX-G2. So ZP-G's AX-G2 is NOT an independent commitment beyond the standard strict-initial
notion it cites — the docstring claim is a theorem. (The could-fail outcome — "needs more than
strict-initial" — did not occur.)

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPG

open CategoryTheory

/-- **AX-G2 from strict-initiality (B4).** If `zero` is strict initial — every morphism into it is an iso
    (Carboni–Lack–Walters) — then the AX-G2 source-asymmetry shape holds: no morphism into `zero` from an
    object not isomorphic to it. Reduces a posited ZP-G axiom to a recognized categorical notion. -/
theorem ax_g2_from_strict_initial {C : Type*} [Category C] (zero : C)
    (hstrict : ∀ (X : C) (f : X ⟶ zero), IsIso f) (X : C)
    (hne : IsEmpty (X ≅ zero)) : IsEmpty (X ⟶ zero) := by
  constructor
  intro f
  haveI := hstrict X f
  exact hne.false (asIso f)

end ZeroParadox.ZPG

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPG
#print axioms ax_g2_from_strict_initial
end PurityCheck
