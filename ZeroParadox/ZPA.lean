import Mathlib.Tactic

/-!
# ZP-A: Lattice Algebra

Formalizes the Zero Paradox join-semilattice with bottom (L, ∨, ⊥).
Axioms A1–A4, definitions D1–D3, and theorems T1–T3 are proved directly
from the axioms. CC-1 is stated as a conditional claim.

Self-contained within semilattice theory; no topology or probability imported.
-/

namespace ZeroParadox.ZPA

/-- The ZP-A algebraic structure: a join-semilattice with bottom.
    Corresponds to Axiom Block A (A1–A4) in ZP-A §1.1. -/
class ZPSemilattice (L : Type*) where
  join : L → L → L
  bot  : L
  -- A1: Associativity
  join_assoc : ∀ x y z : L, join (join x y) z = join x (join y z)
  -- A2: Commutativity
  join_comm  : ∀ x y : L, join x y = join y x
  -- A3: Idempotency
  join_idem  : ∀ x : L, join x x = x
  -- A4: Additive identity (⊥ contributes nothing to a join)
  bot_join   : ∀ x : L, join bot x = x

namespace ZPSemilattice

variable {L : Type*} [ZPSemilattice L]

-- Notation local to this namespace
local infixl:65 " ⊔ " => (join : L → L → L)
local notation "⊥ₗ" => (bot : L)

/-! ## Definition D1 — The Induced Partial Order -/

/-- D1: x ≤ y iff x ∨ y = y -/
def le (x y : L) : Prop := x ⊔ y = y

local infix:50 " ≼ " => le

/-! ## Theorem T1 — ≼ is a Partial Order -/

theorem le_refl (x : L) : x ≼ x :=
  join_idem x

theorem le_antisymm {x y : L} (hxy : x ≼ y) (hyx : y ≼ x) : x = y :=
  -- x = y ∨ x  (from hyx reversed)
  -- y ∨ x = x ∨ y  (A2)
  -- x ∨ y = y  (hxy)
  calc x = y ⊔ x := hyx.symm
    _ = x ⊔ y   := join_comm y x
    _ = y       := hxy

theorem le_trans {x y z : L} (hxy : x ≼ y) (hyz : y ≼ z) : x ≼ z := by
  -- x ∨ z = x ∨ (y ∨ z) = (x ∨ y) ∨ z = y ∨ z = z
  change x ⊔ z = z
  calc x ⊔ z = x ⊔ (y ⊔ z) := by rw [hyz]
    _ = (x ⊔ y) ⊔ z         := by rw [join_assoc]
    _ = y ⊔ z               := by rw [hxy]
    _ = z                   := hyz

/-! ## Theorem T2 — ⊥ is the Global Minimum -/

/-- T2: ⊥ ≤ x for all x ∈ L. Follows immediately from A4. -/
theorem bot_le (x : L) : ⊥ₗ ≼ x :=
  bot_join x

/-! ## Definition D2 — State Transition -/

/-- A state transition is a function f : L → L satisfying x ≼ f(x) for all x.
    Equivalently, f(x) = x ∨ α for some α ∈ L. -/
def IsStateTransition (f : L → L) : Prop :=
  ∀ x, x ≼ f x

/-- D2 equivalence: x ≼ f(x)  ↔  ∃ α, f(x) = x ∨ α -/
theorem state_transition_iff (f : L → L) :
    IsStateTransition f ↔ ∀ x, ∃ α : L, f x = x ⊔ α := by
  constructor
  · -- (⇒) take α = f(x); then f(x) = x ∨ f(x) by D1
    intro h x
    exact ⟨f x, (h x).symm⟩
  · -- (⇐) given f(x) = x ∨ α, show x ∨ f(x) = f(x)
    intro h x
    obtain ⟨α, hα⟩ := h x
    change x ⊔ f x = f x
    -- x ∨ f(x) = x ∨ (x ∨ α) = (x ∨ x) ∨ α = x ∨ α = f(x)
    rw [hα]
    calc x ⊔ (x ⊔ α) = (x ⊔ x) ⊔ α := by rw [join_assoc]
      _ = x ⊔ α                      := by rw [join_idem]

/-! ## Definition D3 and Theorem T3 — Monotone State Sequences -/

/-- D3: A state sequence S : ℕ → L with S(n+1) = S(n) ∨ α(n) for some choice of increments. -/
def IsStateSequence (S : ℕ → L) : Prop :=
  ∃ α : ℕ → L, ∀ n, S (n + 1) = S n ⊔ α n

/-- T3: Every state sequence is monotone: S(n) ≼ S(n+1). -/
theorem state_sequence_monotone (S : ℕ → L) (hS : IsStateSequence S) :
    ∀ n, S n ≼ S (n + 1) := by
  obtain ⟨α, hα⟩ := hS
  intro n
  -- S(n) ∨ S(n+1) = S(n) ∨ (S(n) ∨ α(n)) = (S(n) ∨ S(n)) ∨ α(n) = S(n) ∨ α(n) = S(n+1)
  change S n ⊔ S (n + 1) = S (n + 1)
  rw [hα n]
  calc S n ⊔ (S n ⊔ α n) = (S n ⊔ S n) ⊔ α n := by rw [join_assoc]
    _ = S n ⊔ α n                               := by rw [join_idem]

/-! ## Conditional Claim CC-1 — S₀ = ⊥ -/

/-- CC-1: If the sequence is initialised at ⊥, then ⊥ ≼ S(n) for all n.
    This is a conditional claim (a modelling commitment), not derived from A1–A4. -/
theorem cc1 (S : ℕ → L) (_ : IsStateSequence S) (_ : S 0 = ⊥ₗ) :
    ∀ n, ⊥ₗ ≼ S n :=
  fun n => bot_le (S n)

end ZPSemilattice

end ZeroParadox.ZPA
