import Mathlib.Tactic

/-!
# ZP-A: Lattice Algebra

## Engineer's Take

When you join bottom to itself, it doesn't change. Anytime you join zero to
something above it, it likewise doesn't change. Joining anything to itself
returns you back to the same thing. You get the partial order from A1, A2,
and A3, which we can leverage later. Bottom isn't algebraic zero. It's the
bottom of a series of actions, the null state, where nothing has occurred yet.
D2 says that states always have to grow. If you take the null action you stay
where you are. Any other action moves you forward. Bottom is literally the
bottom value. Start at null, take any non-null action, and you cannot get back
to it. At this level it looks like a modeling choice. It's not something the
algebra forces here. Bottom is where we define the starting point to be. ZPJ
derives it from structure.

---

## Formal Overview (AI-assisted)

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

/-! ## R1 — No Top Element; Strict State Sequences -/

/-- R1: L has no top element — every state has a strictly greater successor.
    Algebraic expression of unbounded ascent: the framework never terminates. -/
def HasNoTop (L : Type*) [ZPSemilattice L] : Prop :=
  ∀ x : L, ∃ y : L, le x y ∧ x ≠ y

/-- A strict state sequence: monotone by T3 AND every step is a proper ascent.
    Models a maximal ascending chain in a no-top lattice (R1 prevents stalling). -/
def IsStrictStateSequence {L : Type*} [ZPSemilattice L] (S : ℕ → L) : Prop :=
  IsStateSequence S ∧ ∀ n, S n ≠ S (n + 1)

/-! ## Conditional Claim CC-1 — S₀ = ⊥ -/

/-- CC-1: If the sequence is initialised at ⊥, then ⊥ ≼ S(n) for all n.
    This is a conditional claim (a modelling commitment), not derived from A1–A4. -/
theorem cc1 (S : ℕ → L) (_ : IsStateSequence S) (_ : S 0 = ⊥ₗ) :
    ∀ n, ⊥ₗ ≼ S n :=
  fun n => bot_le (S n)

end ZPSemilattice

end ZeroParadox.ZPA

/-! ## Axiom Purity Check

`#print axioms` reports every foundational axiom a theorem depends on.
Clean ZP-A proofs should depend only on the ZPSemilattice typeclass fields
and Lean's kernel axioms (propext, Classical.choice, Quot.sound).
No Mathlib-specific axioms should appear.
-/

section PurityCheck
open ZeroParadox.ZPA ZPSemilattice

variable {L : Type*} [ZPSemilattice L]

#check @HasNoTop
#check @IsStrictStateSequence
#print axioms le_refl
#print axioms le_antisymm
#print axioms le_trans
#print axioms bot_le
#print axioms state_transition_iff
#print axioms state_sequence_monotone
#print axioms cc1

end PurityCheck
