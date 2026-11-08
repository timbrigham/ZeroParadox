import Mathlib.Order.WithBot
import Mathlib.Tactic

/-!
# Choice-free orders on `WithTop α` and `WithBot α`

`Preorder`, `PartialOrder`, `OrderBot`, `OrderTop` on `WithTop α` and `WithBot α` over Mathlib's bare
`instLE`/`instLT`, so `≤` and `<` are Mathlib's; fields proved by cases on the constructors, where
Mathlib's go through `le_def` (`grind`, `Classical.choice`). `abbrev`s: opt in with
`attribute [local instance high]`.

## Engineer's Take

So this is a re-implementation to avoid classical.choice we do relationship operators between top elements, created. Specifically because classical.Choice is introduced into our footprint otherwise

---
-/

namespace ZeroParadox

set_option maxHeartbeats 400000

universe u

variable {α : Type u}

/-! ### § I. `WithTop α` -/

/-- `Statement:` the `Preorder` on `WithTop α` over `WithTop.instLE`/`instLT`; not an instance. -/
abbrev withTopPreorderCF [Preorder α] : Preorder (WithTop α) where
  toLE := WithTop.instLE
  toLT := WithTop.instLT
  le_refl x := by
    cases x with
    | top => exact WithTop.LE.le_top _
    | coe a => exact WithTop.LE.coe_le_coe (le_refl a)
  le_trans x y z hxy hyz := by
    change WithTop.LE x y at hxy
    change WithTop.LE y z at hyz
    cases hyz with
    | le_top => exact WithTop.LE.le_top _
    | coe_le_coe hyz =>
      cases hxy with
      | coe_le_coe hxy => exact WithTop.LE.coe_le_coe (le_trans hxy hyz)
  lt_iff_le_not_ge x y := by
    change WithTop.LT x y ↔ WithTop.LE x y ∧ ¬ WithTop.LE y x
    constructor
    · intro h
      cases h with
      | lt_top a => exact ⟨WithTop.LE.le_top _, fun h => by cases h⟩
      | coe_lt_coe h =>
        exact ⟨WithTop.LE.coe_le_coe (lt_iff_le_not_ge.1 h).1,
          fun h' => by cases h' with | coe_le_coe h' => exact (lt_iff_le_not_ge.1 h).2 h'⟩
    · rintro ⟨h, h'⟩
      cases h with
      | le_top => cases x with
        | top => exact absurd (WithTop.LE.le_top _) h'
        | coe a => exact WithTop.LT.lt_top a
      | coe_le_coe h =>
        exact WithTop.LT.coe_lt_coe
          (lt_iff_le_not_ge.2 ⟨h, fun h'' => h' (WithTop.LE.coe_le_coe h'')⟩)

/-- `Statement:` the `PartialOrder` on `WithTop α` extending `withTopPreorderCF`; not an instance. -/
abbrev withTopPartialOrderCF [PartialOrder α] : PartialOrder (WithTop α) where
  toPreorder := withTopPreorderCF
  le_antisymm x y hxy hyx := by
    change WithTop.LE x y at hxy
    change WithTop.LE y x at hyx
    cases hxy with
    | le_top => cases hyx with
      | le_top => rfl
    | coe_le_coe hxy => cases hyx with
      | coe_le_coe hyx => exact congrArg _ (le_antisymm hxy hyx)

/-- `Statement:` ⊤ of `WithTop α` is greatest under `WithTop.instLE`; not an instance. -/
abbrev withTopOrderTopCF [LE α] : @OrderTop (WithTop α) WithTop.instLE where
  toTop := inferInstance
  le_top := WithTop.LE.le_top

/-- `Statement:` `↑⊥` is least in `WithTop α` under `WithTop.instLE`; not an instance. -/
abbrev withTopOrderBotCF [LE α] [OrderBot α] : @OrderBot (WithTop α) WithTop.instLE where
  toBot := inferInstance
  bot_le x := by
    cases x with
    | top => exact WithTop.LE.le_top _
    | coe a => exact WithTop.LE.coe_le_coe bot_le

/-! ### § II. `WithBot α` -/

/-- `Statement:` the `Preorder` on `WithBot α` over `WithBot.instLE`/`instLT`; not an instance. -/
abbrev withBotPreorderCF [Preorder α] : Preorder (WithBot α) where
  toLE := WithBot.instLE
  toLT := WithBot.instLT
  le_refl x := by
    cases x with
    | bot => exact WithBot.LE.bot_le _
    | coe a => exact WithBot.LE.coe_le_coe (le_refl a)
  le_trans x y z hxy hyz := by
    change WithBot.LE x y at hxy
    change WithBot.LE y z at hyz
    cases hxy with
    | bot_le => exact WithBot.LE.bot_le _
    | coe_le_coe hxy =>
      cases hyz with
      | coe_le_coe hyz => exact WithBot.LE.coe_le_coe (le_trans hxy hyz)
  lt_iff_le_not_ge x y := by
    change WithBot.LT x y ↔ WithBot.LE x y ∧ ¬ WithBot.LE y x
    constructor
    · intro h
      cases h with
      | bot_lt b => exact ⟨WithBot.LE.bot_le _, fun h => by cases h⟩
      | coe_lt_coe h =>
        exact ⟨WithBot.LE.coe_le_coe (lt_iff_le_not_ge.1 h).1,
          fun h' => by cases h' with | coe_le_coe h' => exact (lt_iff_le_not_ge.1 h).2 h'⟩
    · rintro ⟨h, h'⟩
      cases h with
      | bot_le => cases y with
        | bot => exact absurd (WithBot.LE.bot_le _) h'
        | coe b => exact WithBot.LT.bot_lt b
      | coe_le_coe h =>
        exact WithBot.LT.coe_lt_coe
          (lt_iff_le_not_ge.2 ⟨h, fun h'' => h' (WithBot.LE.coe_le_coe h'')⟩)

/-- `Statement:` the `PartialOrder` on `WithBot α` extending `withBotPreorderCF`; not an instance. -/
abbrev withBotPartialOrderCF [PartialOrder α] : PartialOrder (WithBot α) where
  toPreorder := withBotPreorderCF
  le_antisymm x y hxy hyx := by
    change WithBot.LE x y at hxy
    change WithBot.LE y x at hyx
    cases hxy with
    | bot_le => cases hyx with
      | bot_le => rfl
    | coe_le_coe hxy => cases hyx with
      | coe_le_coe hyx => exact congrArg _ (le_antisymm hxy hyx)

/-- `Statement:` ⊥ of `WithBot α` is least under `WithBot.instLE`; not an instance. -/
abbrev withBotOrderBotCF [LE α] : @OrderBot (WithBot α) WithBot.instLE where
  toBot := inferInstance
  bot_le := WithBot.LE.bot_le

/-- `Statement:` `↑⊤` is greatest in `WithBot α` under `WithBot.instLE`; not an instance. -/
abbrev withBotOrderTopCF [LE α] [OrderTop α] : @OrderTop (WithBot α) WithBot.instLE where
  toTop := inferInstance
  le_top x := by
    cases x with
    | bot => exact WithBot.LE.bot_le _
    | coe a => exact WithBot.LE.coe_le_coe le_top

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms withTopPreorderCF
#print axioms withTopPartialOrderCF
#print axioms withTopOrderTopCF
#print axioms withTopOrderBotCF
#print axioms withBotPreorderCF
#print axioms withBotPartialOrderCF
#print axioms withBotOrderBotCF
#print axioms withBotOrderTopCF

end PurityCheck
