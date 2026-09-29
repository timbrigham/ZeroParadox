import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Pataraia's statement from Bourbaki–Witt, classically

## Engineer's Take

Mathlib runs on classical logic by default, choice included. Working inside that default, the two
things Taylor needs from Pataraia, the least fixed point and the induction principle that goes with
it, aren't actually missing: both fall out of Bourbaki–Witt, which Mathlib already has, and this
file is the adapter that shows it works in Lean. It uses choice like everything else built on that
default, and that is a fact about this route, not about the theorem. Pataraia's own proof needs
neither choice nor excluded middle, and it has been formalized in Agda. We finally got a port of it
working in Lean, in PataraiaChoiceFree.lean, with no axioms at all. I defer to my AI assistant
regarding the specifics of how the internals work.

---
## Formal Overview (AI-assisted)
Monotone `f` on a Mathlib `CompletePartialOrder` (directed-complete, least element `⊥`) has a least fixed point
(Taylor Thm 118), in every set holding `⊥` and closed under `f` and directed joins (Pataraia induction, Cor. 119).
Bourbaki–Witt plus classical logic ⇒ both STATEMENTS, not Pataraia's intuitionistic proof, which is
`ZeroParadox/Order/PataraiaChoiceFree.lean` (no axioms); prior art: `ZeroParadox/Order/PataraiaFromBourbakiWitt.md`.
-/

namespace ZeroParadox

/-- `Statement:` for `[CompletePartialOrder α]` and monotone `f`, some `y` is a fixed point of `f`
    lying below every fixed point: Pataraia's theorem (Adámek–Milius–Moss, CALCO 2021, Thm 2.4);
    the citations are in `ZeroParadox/Order/PataraiaFromBourbakiWitt.md`. Footprint
    `[propext, Classical.choice, Quot.sound]` measures this proof, not the principle, which
    `pataraia_least_prefixedPoint` gives with no axioms. -/
theorem dcpo_exists_least_fixedPoint {α : Type*} [CompletePartialOrder α] (f : α →o α) :
    ∃ y, f y = y ∧ ∀ p, f p = p → y ≤ p := by
  -- `S`: post-fixed points of `f` lying below every fixed point.
  let S : Set α := {x | x ≤ f x ∧ ∀ p, f p = p → x ≤ p}
  -- A nonempty chain in `S` is directed, so the dcpo's directed sups serve as chain sups.
  have hdir (c : NonemptyChain S) : DirectedOn (· ≤ ·) (Subtype.val '' c.carrier) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases eq_or_ne x y with rfl | hne
    · exact ⟨x.1, ⟨x, hx, rfl⟩, le_rfl, le_rfl⟩
    · rcases c.isChain' hx hy hne with h | h
      · exact ⟨y.1, ⟨y, hy, rfl⟩, h, le_rfl⟩
      · exact ⟨x.1, ⟨x, hx, rfl⟩, le_rfl, h⟩
  letI : ChainCompletePartialOrder S :=
    { cSup := fun c => ⟨sSup (Subtype.val '' c.carrier), by
        have hl := CompletePartialOrder.lubOfDirected _ (hdir c)
        refine ⟨hl.2 ?_, fun p hp => hl.2 ?_⟩
        · rintro _ ⟨x, hx, rfl⟩
          exact x.2.1.trans (f.monotone (hl.1 ⟨x, hx, rfl⟩))
        · rintro _ ⟨x, hx, rfl⟩
          exact x.2.2 p hp⟩
      le_cSup := fun c x hx => (CompletePartialOrder.lubOfDirected _ (hdir c)).1 ⟨x, hx, rfl⟩
      cSup_le := fun c x hx => (CompletePartialOrder.lubOfDirected _ (hdir c)).2 (by
        rintro _ ⟨y, hy, rfl⟩
        exact hx y hy) }
  -- The order's least element `⊥` lies in `S`, and `f` restricts to an inflationary map on `S`.
  haveI : Nonempty S := ⟨⟨⊥, bot_le, fun _ _ => bot_le⟩⟩
  let g : S → S := fun x => ⟨f x, f.monotone x.2.1, fun p hp => hp ▸ f.monotone (x.2.2 p hp)⟩
  obtain ⟨y, hy⟩ := ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary
    (f := g) (fun x => x.2.1)
  exact ⟨y.1, congrArg Subtype.val hy, y.2.2⟩

/-- `Statement:` Pataraia induction (Taylor Cor. 119; Adámek–Milius–Moss, CALCO 2021, Cor 2.6): if
    `U` contains `⊥` and is closed under `f` and under joins of nonempty directed subsets, then `U`
    contains every least fixed point `y` of `f`. Footprint `[propext, Classical.choice, Quot.sound]` measures this proof, not the principle: `pataraia_induction_constructive` has this signature and no axioms. -/
theorem pataraia_induction {α : Type*} [CompletePartialOrder α] (f : α →o α) (U : Set α)
    (hbot : ⊥ ∈ U) (hf : ∀ x ∈ U, f x ∈ U)
    (hsup : ∀ d ⊆ U, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ U)
    {y : α} (hy : f y = y ∧ ∀ p, f p = p → y ≤ p) : y ∈ U := by
  -- `W`: post-fixed points of `f` in `U` lying below `y`.
  let W : Set α := {x | x ∈ U ∧ x ≤ y ∧ x ≤ f x}
  have hdir (c : NonemptyChain W) : DirectedOn (· ≤ ·) (Subtype.val '' c.carrier) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨z, hz, rfl⟩
    rcases eq_or_ne x z with rfl | hne
    · exact ⟨x.1, ⟨x, hx, rfl⟩, le_rfl, le_rfl⟩
    · rcases c.isChain' hx hz hne with h | h
      · exact ⟨z.1, ⟨z, hz, rfl⟩, h, le_rfl⟩
      · exact ⟨x.1, ⟨x, hx, rfl⟩, le_rfl, h⟩
  have hsub (c : NonemptyChain W) : Subtype.val '' c.carrier ⊆ U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  have hne (c : NonemptyChain W) : (Subtype.val '' c.carrier).Nonempty :=
    c.Nonempty'.image _
  letI : ChainCompletePartialOrder W :=
    { cSup := fun c => ⟨sSup (Subtype.val '' c.carrier), by
        have hl := CompletePartialOrder.lubOfDirected _ (hdir c)
        refine ⟨hsup _ (hsub c) (hne c) (hdir c), hl.2 ?_, hl.2 ?_⟩
        · rintro _ ⟨x, -, rfl⟩
          exact x.2.2.1
        · rintro _ ⟨x, hx, rfl⟩
          exact x.2.2.2.trans (f.monotone (hl.1 ⟨x, hx, rfl⟩))⟩
      le_cSup := fun c x hx => (CompletePartialOrder.lubOfDirected _ (hdir c)).1 ⟨x, hx, rfl⟩
      cSup_le := fun c x hx => (CompletePartialOrder.lubOfDirected _ (hdir c)).2 (by
        rintro _ ⟨z, hz, rfl⟩
        exact hx z hz) }
  -- `⊥ ∈ W`, and `f` restricts to an inflationary map on `W` (`x ≤ y ⇒ f x ≤ f y = y`).
  haveI : Nonempty W := ⟨⟨⊥, hbot, bot_le, bot_le⟩⟩
  let g : W → W := fun x =>
    ⟨f x, hf x x.2.1, hy.1 ▸ f.monotone x.2.2.1, f.monotone x.2.2.2⟩
  obtain ⟨v, hv⟩ := ChainCompletePartialOrder.nonempty_fixedPoints_of_inflationary
    (f := g) (fun x => x.2.2.2)
  -- `v` is a fixed point below `y`, so leastness of `y` forces `y = v ∈ U`.
  have hfv : f v.1 = v.1 := congrArg Subtype.val hv
  exact le_antisymm (hy.2 v.1 hfv) v.2.2.1 ▸ v.2.1

/-! ## Controls -/

-- `Bool` is a member of the class (via `CompleteLattice.toCompletePartialOrder`).
noncomputable example : CompletePartialOrder Bool := inferInstance

-- Monotonicity has teeth: on `Bool`, the non-monotone `not` has no fixed point at all.
example : ¬ ∀ g : Bool → Bool, ∃ y, g y = y ∧ ∀ p, g p = p → y ≤ p := fun h => by
  obtain ⟨y, hy, -⟩ := h not
  cases y <;> simp at hy

-- "Least" is informative: `id` on `Bool` fixes both points, and only `false` (= `⊥`) is least.
example : (OrderHom.id : Bool →o Bool) true = true ∧ (OrderHom.id : Bool →o Bool) false = false :=
  ⟨rfl, rfl⟩
example : ∀ y : Bool, ((OrderHom.id : Bool →o Bool) y = y ∧
    ∀ p, (OrderHom.id : Bool →o Bool) p = p → y ≤ p) → y = false := by
  rintro y ⟨-, h⟩
  exact le_bot_iff.mp (h false rfl)

-- Pataraia induction, closure under `f` has teeth: on `Bool`, `true` is the least fixed point of
-- the constant map `true`, and `U = {false}` contains `⊥` and its directed joins but not `true`.
example : ((fun _ : Bool => true) true = true ∧ ∀ p, (fun _ : Bool => true) p = p → true ≤ p) ∧
    ⊥ ∈ ({false} : Set Bool) ∧
    (∀ d ⊆ ({false} : Set Bool), d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ ({false} : Set Bool)) ∧
    true ∉ ({false} : Set Bool) := by
  refine ⟨⟨rfl, fun p hp => le_of_eq hp⟩, rfl, fun d hd hne _ => ?_, by simp⟩
  rw [(hne.subset_singleton_iff).mp hd, sSup_singleton]
  rfl

-- Containing `⊥` has teeth: `false` is the least fixed point of `id` on `Bool`, and `U = {true}` is
-- closed under `id` and its directed joins but misses it.
example : (id false = false ∧ ∀ p : Bool, id p = p → false ≤ p) ∧
    (∀ x ∈ ({true} : Set Bool), id x ∈ ({true} : Set Bool)) ∧
    (∀ d ⊆ ({true} : Set Bool), d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ ({true} : Set Bool)) ∧
    false ∉ ({true} : Set Bool) := by
  refine ⟨⟨rfl, fun p _ => bot_le⟩, fun x hx => hx, fun d hd hne _ => ?_, by simp⟩
  rw [(hne.subset_singleton_iff).mp hd, sSup_singleton]
  rfl

-- Closure under directed joins has teeth, on `ℕ∞` (a finite carrier cannot show it: there every
-- nonempty directed set has a greatest element). `⊤` is the least fixed point of `x ↦ x + 1`, and
-- the finite values contain `⊥` and are closed under `+ 1` but miss `⊤`.
example : ((⊤ : ℕ∞) + 1 = ⊤ ∧ ∀ p : ℕ∞, p + 1 = p → ⊤ ≤ p) ∧
    (⊥ : ℕ∞) ∈ {x : ℕ∞ | x ≠ ⊤} ∧ (∀ x ∈ {x : ℕ∞ | x ≠ ⊤}, x + 1 ∈ {x : ℕ∞ | x ≠ ⊤}) ∧
    (⊤ : ℕ∞) ∉ {x : ℕ∞ | x ≠ ⊤} := by
  refine ⟨⟨rfl, fun p hp => ?_⟩, by simp, fun x hx => ?_, by simp⟩
  · induction p using ENat.recTopCoe with
    | top => exact le_rfl
    | coe n => exact absurd (by exact_mod_cast hp) (Nat.succ_ne_self n)
  · simp only [Set.mem_setOf_eq] at hx ⊢
    exact WithTop.add_ne_top.mpr ⟨hx, ENat.one_ne_top⟩

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms dcpo_exists_least_fixedPoint
#print axioms pataraia_induction

end PurityCheck
