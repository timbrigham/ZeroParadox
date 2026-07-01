import ZeroParadox.ZPJ

/-!
# P10: AFA self-containment derived from a bottom-valuation (the theorem-anchor)

`AFAStructure.selfMem` is an abstract class field — self-containment is *posited*. This file regrounds
it: given a `BottomValuation` (a valuation `v` whose unique `⊤`-valued point is `⊥`), the predicate
`v x = ⊤` is a *valid* AFA self-membership — it satisfies `quine_unique` and `bot_self_mem`. So the
lattice form of ⊥ = {⊥} becomes a CONSEQUENCE of the valuation axioms rather than a bare posit.

**Honest scope (FMEA).** This is a REDUCTION, not an elimination: the AFA self-membership posit is
traded for the valuation posit (`v_bot`, `v_top_unique`). Its value is that the valuation grounding is
independently motivated — `ZPB`'s `v₂(0)=∞` and P7's `addVal_bot` (any additive valuation sends the
bottom to ⊤, choice-free). So self-containment is no longer free-floating; it is forced by valuation
geometry. This closes the "AFA-squeeze circularity" by relocating the commitment to a more motivated
axiom, not by removing it.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

namespace ZeroParadox.ZPJ

open ZeroParadox.ZPA ZPSemilattice

/-- A **bottom-valuation** on a ZPSemilattice: a valuation `v : L → Γ` into a type with `⊤` whose
    UNIQUE `⊤`-valued point is the bottom (`v_top_unique`), with `v ⊥ = ⊤` (`v_bot`). These two
    valuation axioms are the independently-motivated grounding from which AFA self-containment is
    derived below. -/
class BottomValuation (L : Type*) [ZPSemilattice L] (Γ : Type*) [Top Γ] where
  /-- The valuation. -/
  v : L → Γ
  /-- The bottom has the maximal (⊤ = +∞) valuation. -/
  v_bot : v bot = ⊤
  /-- The bottom is the ONLY point of ⊤ valuation. -/
  v_top_unique : ∀ x : L, v x = ⊤ → x = bot

/-- **The anchor (P10): AFA self-containment DERIVED from a bottom-valuation.** Defining
    `selfMem x := v x = ⊤` satisfies the `AFAStructure` axioms — `bot_self_mem` is `v_bot`,
    `quine_unique` is `v_top_unique`. So the lattice form of ⊥ = {⊥} is a consequence of the valuation
    axioms, not a primitive. -/
@[reducible] def BottomValuation.toAFA (L : Type*) [ZPSemilattice L] {Γ : Type*} [Top Γ]
    [BottomValuation L Γ] : AFAStructure L where
  selfMem x := BottomValuation.v (Γ := Γ) x = ⊤
  quine_unique x y hx hy :=
    (BottomValuation.v_top_unique x hx).trans (BottomValuation.v_top_unique y hy).symm
  bot_self_mem := BottomValuation.v_bot

/-- Under a bottom-valuation, `v x = ⊤` forces the derived self-membership. The direct anchor
    statement `v(x) = ⊤ → selfMem x`. -/
theorem valuation_forces_selfMem (L : Type*) [ZPSemilattice L] {Γ : Type*} [Top Γ]
    [BottomValuation L Γ] (x : L) (hx : BottomValuation.v (Γ := Γ) x = ⊤) :
    (BottomValuation.toAFA L (Γ := Γ)).selfMem x := hx

/-- With the derived AFA structure, the bottom is the Quine atom — now grounded in the valuation
    rather than posited. -/
theorem valuation_bot_is_quine (L : Type*) [ZPSemilattice L] {Γ : Type*} [Top Γ]
    [BottomValuation L Γ] :
    @IsQuineAtom L _ (BottomValuation.toAFA L (Γ := Γ)) bot :=
  @bot_is_quine_atom L _ (BottomValuation.toAFA L (Γ := Γ))

end ZeroParadox.ZPJ

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPJ
#print axioms BottomValuation.toAFA
#print axioms valuation_forces_selfMem
#print axioms valuation_bot_is_quine
end PurityCheck
