import ZeroParadox.Order.LeastFixedPoint
import Mathlib.Order.CompletePartialOrder

set_option maxHeartbeats 400000

/-!
# Pataraia's theorem and induction, with no axioms

## Engineer's Take

I had to ask how this shifted from the last file. That one got a least fixed point by way of
Bourbaki-Witt, and it carried choice because Mathlib does. This one gets a fixed point below every
pre-fixed point, which is a stronger promise about the same point, and it needs no axioms at all.
The proof isn't ours; it is Pataraia's, in the form Taylor gives it, ported from an Agda version,
and as of September 2026 we didn't find another one in Mathlib or Lean core.

A fixed point and a pre-fixed point sounded a whole lot like epsilon zero and the asymptote that
approaches it. The asymptote turned out to be the other side: the post-fixed points climb up from
below, the pre-fixed points are ceilings coming down from above, and the fixed point is where they
meet. Whether that is more than a resemblance is still open. I defer to my AI assistant regarding
the specifics of how the internals work.

---
## Formal Overview (AI-assisted)
Monotone `f` on a Mathlib `CompletePartialOrder` (directed-complete, least element `⊥`): a fixed
point below every pre-fixed point, hence least fixed (here also conversely), and Pataraia induction.
Ported from TypeTopology `Various.Pataraia-Taylor` (Escardó–de Jong, Agda, 2024); the proof's
comments map `Y` and `T` to it. Classical route: `ZeroParadox/Order/PataraiaFromBourbakiWitt.lean`.
-/

namespace ZeroParadox

/-- `Statement:` for monotone `f` on `[CompletePartialOrder α]` and any `U` containing `⊥`, closed
    under `f` and under joins of nonempty directed subsets, some `z ∈ U` is a fixed point of `f`
    lying below every pre-fixed point of `f`. -/
theorem pataraia_least_prefixedPoint_mem {α : Type*} [CompletePartialOrder α] (f : α →o α)
    (U : Set α) (hbot : ⊥ ∈ U) (hf : ∀ x ∈ U, f x ∈ U)
    (hsup : ∀ d ⊆ U, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ U) :
    ∃ z, z ∈ U ∧ f z = z ∧ ∀ p, f p ≤ p → z ≤ p := by
  -- `Y` (Taylor's `TC`, plus `x ∈ U` as in their `lfp-induction`): post-fixed points in `U`
  -- lying below every pre-fixed point.
  let Y : α → Prop := fun x => x ≤ f x ∧ (∀ p, f p ≤ p → x ≤ p) ∧ x ∈ U
  have hYsup : ∀ d : Set α, (∀ x ∈ d, Y x) → d.Nonempty → DirectedOn (· ≤ ·) d → Y (sSup d) := by
    intro d hd hne hdir
    have hl := CompletePartialOrder.lubOfDirected d hdir
    exact ⟨hl.2 (fun x hx => (hd x hx).1.trans (f.monotone (hl.1 hx))),
           fun p hp => hl.2 (fun x hx => (hd x hx).2.1 p hp),
           hsup d (fun x hx => (hd x hx).2.2) hne hdir⟩
  -- `M`: maps sending `Y` into `Y`, inflationary and monotone on `Y`.
  let M : Set (α → α) := {g | ∀ x, Y x → (Y (g x) ∧ x ≤ g x ∧ ∀ y, Y y → x ≤ y → g x ≤ g y)}
  have hid : (fun x => x) ∈ M := fun x hx => ⟨hx, le_rfl, fun _ _ h => h⟩
  have hcomp : ∀ g ∈ M, ∀ h ∈ M, (fun x => g (h x)) ∈ M := by
    intro g hg h hh x hx
    obtain ⟨hhY, hhinf, hhmono⟩ := hh x hx
    obtain ⟨hgY, hginf, -⟩ := hg (h x) hhY
    refine ⟨hgY, hhinf.trans hginf, fun y hy hxy => ?_⟩
    exact (hg (h x) hhY).2.2 (h y) (hh y hy).1 (hhmono y hy hxy)
  let img : α → Set α := fun x => {z | ∃ g ∈ M, g x = z}
  have himgne : ∀ x, (img x).Nonempty := fun x => ⟨x, _, hid, rfl⟩
  have himgdir : ∀ x, Y x → DirectedOn (· ≤ ·) (img x) := by
    rintro x hx _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    refine ⟨g (h x), ⟨_, hcomp g hg h hh, rfl⟩, ?_, ?_⟩
    · exact (hg x hx).2.2 (h x) (hh x hx).1 (hh x hx).2.1
    · exact (hg (h x) (hh x hx).1).2.1
  have himgY : ∀ x, Y x → ∀ z ∈ img x, Y z := by
    rintro x hx _ ⟨g, hg, rfl⟩
    exact (hg x hx).1
  -- `T` (`γ` of `lemma₂·₁`): the pointwise sup of `M`, itself the greatest member of `M`.
  let T : α → α := fun x => sSup (img x)
  have hTlub : ∀ x, Y x → IsLUB (img x) (T x) := fun x hx =>
    CompletePartialOrder.lubOfDirected _ (himgdir x hx)
  have hTM : T ∈ M := by
    intro x hx
    refine ⟨hYsup _ (himgY x hx) (himgne x) (himgdir x hx), (hTlub x hx).1 ⟨_, hid, rfl⟩, ?_⟩
    intro y hy hxy
    refine (hTlub x hx).2 ?_
    rintro _ ⟨g, hg, rfl⟩
    exact ((hg x hx).2.2 y hy hxy).trans ((hTlub y hy).1 ⟨g, hg, rfl⟩)
  have hfM : (fun x => f x) ∈ M := by
    intro x hx
    exact ⟨⟨f.monotone hx.1, fun p hp => (f.monotone (hx.2.1 p hp)).trans hp, hf x hx.2.2⟩,
      hx.1, fun y _ h => f.monotone h⟩
  have hbotY : Y ⊥ := ⟨bot_le, fun _ _ => bot_le, hbot⟩
  have hY0 : Y (T ⊥) := (hTM ⊥ hbotY).1
  have hle : f (T ⊥) ≤ T ⊥ := (hTlub ⊥ hbotY).1 ⟨_, hcomp _ hfM T hTM, rfl⟩
  exact ⟨T ⊥, hY0.2.2, le_antisymm hle hY0.1, hY0.2.1⟩

/-- `Statement:` for monotone `f` on `[CompletePartialOrder α]`, some `y` is a fixed point of `f`
    lying below every pre-fixed point (`f p ≤ p`) of `f`. -/
theorem pataraia_least_prefixedPoint {α : Type*} [CompletePartialOrder α] (f : α →o α) :
    ∃ y, f y = y ∧ ∀ p, f p ≤ p → y ≤ p :=
  let ⟨z, _, hz⟩ :=pataraia_least_prefixedPoint_mem f Set.univ trivial (fun _ _ => trivial)
    (fun _ _ _ _ => trivial)
  ⟨z, hz⟩

-- The fixed point below every pre-fixed point instantiates the corpus schema from `⊥`.
example {α : Type*} [CompletePartialOrder α] (f : α →o α) :
    ∃ y, IsLeastFixedPointFrom (· ≤ ·) (⇑f) ⊥ y :=
  let ⟨y, hfy, hy⟩ := pataraia_least_prefixedPoint f
  ⟨y, ⟨bot_le, hfy, fun b hb _ => hy b (le_of_eq hb)⟩⟩

-- The converse holds in this setting: every least fixed point lies below every pre-fixed point.
example {α : Type*} [CompletePartialOrder α] (f : α →o α) (y : α)
    (hy : f y = y ∧ ∀ p, f p = p → y ≤ p) : ∀ p, f p ≤ p → y ≤ p := by
  obtain ⟨z, hfz, hz⟩ := pataraia_least_prefixedPoint f
  obtain rfl : y = z := le_antisymm (hy.2 z hfz) (hz y (le_of_eq hy.1))
  exact hz

/-- `Statement:` Pataraia induction, with the signature of `pataraia_induction`: if `U` contains `⊥`
    and is closed under `f` and under joins of nonempty directed subsets, then `U` contains every
    least fixed point `y` of `f`. -/
theorem pataraia_induction_constructive {α : Type*} [CompletePartialOrder α] (f : α →o α)
    (U : Set α) (hbot : ⊥ ∈ U) (hf : ∀ x ∈ U, f x ∈ U)
    (hsup : ∀ d ⊆ U, d.Nonempty → DirectedOn (· ≤ ·) d → sSup d ∈ U)
    {y : α} (hy : f y = y ∧ ∀ p, f p = p → y ≤ p) : y ∈ U :=
  -- A fixed `z ∈ U` below every pre-fixed point; `y` is pre-fixed and `z` is fixed, so `y = z`.
  let ⟨z, hzU, hfz, hz⟩ := pataraia_least_prefixedPoint_mem f U hbot hf hsup
  le_antisymm (hy.2 z hfz) (hz y (le_of_eq hy.1)) ▸ hzU

/-! ## Controls -/

-- Monotonicity has teeth: on `Bool`, the non-monotone `not` has no fixed point at all.
example : ¬ ∀ g : Bool → Bool, ∃ y, g y = y ∧ ∀ p, g p ≤ p → y ≤ p := fun h => by
  obtain ⟨y, hy, -⟩ := h not
  cases y <;> cases hy

-- "Pre-fixed" ranges over a strictly larger set: for the constant map `_ ↦ ⊥` on `Bool`, `true`
-- is pre-fixed (`⊥ ≤ true`) and not fixed.
example : (OrderHom.const Bool (⊥ : Bool)) true ≤ true ∧
    (OrderHom.const Bool (⊥ : Bool)) true ≠ true :=
  ⟨bot_le, Bool.false_ne_true⟩

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms pataraia_least_prefixedPoint_mem
#print axioms pataraia_least_prefixedPoint
#print axioms pataraia_induction_constructive

end PurityCheck
