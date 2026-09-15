import Mathlib.Tactic
import Mathlib.Order.Irreducible

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

namespace ZeroParadox

/-! ### NO-GO gauge — for an OPERATIONAL class, "who fails?" is the wrong question.
`ZPSemilattice` supplies its own operations, so membership is structure to be EQUIPPED, not a property
a carrier has or lacks: every inhabited carrier can be given one, and inhabitation is the sole
obstruction — the two `example`s below the class. So "lacks an identity" describes a chosen operation,
never a carrier, and a one-element witness (`trivialZPSemilattice`, `ZeroParadox/Valuation/Scale.lean`)
says nothing in particular. The theorems consume the LAWS, not membership, so *"L carries
`ZPSemilattice`, therefore…"* is never an argument here; contrast the classes whose fields are PROPS. -/

/-- The ZP-A algebraic structure: a join-semilattice with bottom.
    Corresponds to Axiom Block A (A1–A4) in ZP-A §1.1. -/
-- [ZP-CUSTOM] replaces: Mathlib SemilatticeSup + OrderBot | reason: Mathlib's SemilatticeSup + OrderBot would satisfy the algebra, and using them is cheap — measured 2026-08-30 at the pin, both classes are axiom-free and bot_sup_eq and sup_assoc cost [propext] only. ZPSemilattice states A1–A4 as FIELDS anyway, so each theorem's footprint is fixed by the axioms it consumes rather than by whichever hierarchy lemma the elaborator reached for. ⚠⚠ An AUDITABILITY choice, not an axiom-avoidance one: an IMPORT never changes a footprint, only USING a proof does — this file's own line 1 imports Mathlib.Tactic and the class measures clean.
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

/-! The gauge above, as two witnesses rather than a sentence. Generic ON PURPOSE: the claim each
refutes is a universal, so a specific carrier would be strictly weaker. Both are anonymous, so
neither adds a declaration to the corpus. -/

-- Statement: every INHABITED carrier can be equipped — well-order it, join := `max`, ⊥ := the least
-- element. So there is no carrier that "fails a law": the laws come with the operations.
example (L : Type*) [Nonempty L] : Nonempty (ZPSemilattice L) := by
  classical
  letI : LinearOrder L := IsWellOrder.linearOrder (WellOrderingRel (α := L))
  letI : WellFoundedLT L := ⟨(IsWellFounded.wf : WellFounded (WellOrderingRel (α := L)))⟩
  letI : OrderBot L := WellFoundedLT.toOrderBot L
  exact ⟨{ join := max, bot := ⊥
         , join_assoc := fun x y z => max_assoc x y z
         , join_comm := fun x y => max_comm x y
         , join_idem := fun x => max_self x
         , bot_join := fun _ => max_eq_right bot_le }⟩

-- Statement: inhabitation is the ONLY obstruction — the `bot` field demands a point.
example : IsEmpty (ZPSemilattice Empty) := ⟨fun s => s.bot.elim⟩

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

-- `Statement:` a step changes nothing exactly when the increment is already below the state.
-- In Mathlib's lattices this is `sup_eq_left`.
example {L : Type*} [ZPSemilattice L] (S α : ℕ → L) (hα : ∀ n, S (n + 1) = join (S n) (α n)) (n : ℕ) :
    S (n + 1) = S n ↔ le (α n) (S n) := by
  rw [hα n]
  constructor
  · intro h
    change join (α n) (S n) = S n
    rw [join_comm]; exact h
  · intro h
    change join (α n) (S n) = S n at h
    rw [join_comm]; exact h

-- `Statement:` if the run is constant from step x on, S x is the least upper bound of the whole run.
-- That EVERY run is eventually constant is the ascending chain condition
-- (Mathlib `wellFoundedGT_iff_monotone_chain_condition`).
example {L : Type*} [ZPSemilattice L] (S : ℕ → L) (hS : IsStateSequence S) (x : ℕ)
    (hstab : ∀ k, S (x + k) = S x) :
    (∀ n, le (S n) (S x)) ∧ (∀ u, (∀ n, le (S n) u) → le (S x) u) := by
  have up : ∀ n k, le (S n) (S (n + k)) := by
    intro n k
    induction k with
    | zero => exact ZPSemilattice.le_refl _
    | succ k ih => exact ZPSemilattice.le_trans ih (state_sequence_monotone S hS (n + k))
  refine ⟨fun n => ?_, fun u hu => hu x⟩
  rcases Nat.lt_or_ge n x with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    exact up n k
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [hstab k]; exact ZPSemilattice.le_refl _

-- `Statement:` control — one idempotent step does not fix the limit.
example : ∃ S : ℕ → ℕ, (∀ n, S n ≤ S (n + 1)) ∧ S 1 = S 0 ∧ S 2 ≠ S 1 :=
  ⟨fun n => if n ≤ 1 then 0 else n, fun n => by simp only []; split_ifs <;> omega, rfl, by decide⟩

-- `Statement:` a state sequence that reaches a top at step x stays there: every later state is S x.
example {L : Type*} [ZPSemilattice L] (S : ℕ → L) (hS : IsStateSequence S) (x : ℕ)
    (htop : ∀ y, le y (S x)) : ∀ k, S (x + k) = S x := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hmono := state_sequence_monotone S hS (x + k)
    rw [ih] at hmono
    exact ZPSemilattice.le_antisymm (htop _) hmono

/-! ## No Top Element (`HasNoTop`); Strict State Sequences

⚠ **NOT ZP-A's R1**, which is NO-SUBTRACTION (`scripts/build_zpa.py` Remark R1, exported there as
"no subtraction / additive ontology"; `t_snap_irreversible` cites it that way). Cite `HasNoTop`
and this file for the ORDER property. One label over two propositions is a citation nothing can
check: both readings verify, of different claims.

⚠ **`HasNoTop` is AVAILABILITY; `IsStrictStateSequence` is OCCURRENCE** — a next step existing is
not a chain taking one. NO-GO gauge: `ZeroParadox/Valuation/SemilatticeInstance.lean` § Ib (DC-32). -/

/-- `HasNoTop`: L has no top element — every state has a strictly greater successor.
    The order CONDITION for unbounded ascent; it does not assert that any chain ascends. -/
def HasNoTop (L : Type*) [ZPSemilattice L] : Prop :=
  ∀ x : L, ∃ y : L, le x y ∧ x ≠ y

/-- A strict state sequence: monotone by T3 AND every step is a proper ascent — the OCCURRENCE. -/
def IsStrictStateSequence {L : Type*} [ZPSemilattice L] (S : ℕ → L) : Prop :=
  IsStateSequence S ∧ ∀ n, S n ≠ S (n + 1)

/-! ## Conditional Claim CC-1 — S₀ = ⊥ -/

/-- CC-1: If the sequence is initialised at ⊥, then ⊥ ≼ S(n) for all n.
    This is a conditional claim (a modelling commitment), not derived from A1–A4. -/
theorem cc1 (S : ℕ → L) (_ : IsStateSequence S) (_ : S 0 = ⊥ₗ) :
    ∀ n, ⊥ₗ ≼ S n :=
  fun n => bot_le (S n)

end ZPSemilattice

/-! OQ-A1a (join-irreducible increments), in Mathlib's `SupIrred` vocabulary, outside the local `⊔`. -/

-- `Statement:` on a chain the restriction is vacuous: every nonzero natural is join-irreducible under max.
example (n : ℕ) (hn : n ≠ 0) : SupIrred n := by
  refine ⟨?_, fun a b h => ?_⟩
  · exact fun hmin => hn (Nat.le_zero.1 (hmin (Nat.zero_le n)))
  · rcases le_total a b with hab | hab
    · right; simpa [max_eq_right hab] using h
    · left; simpa [max_eq_left hab] using h

-- `Statement:` on a branching carrier it is not: the top of `Set Bool` is `{true} ⊔ {false}`.
example : ¬ SupIrred (Set.univ : Set Bool) := by
  intro h
  have hj : ({true} : Set Bool) ⊔ {false} = Set.univ := by ext x; cases x <;> simp
  rcases h.2 hj with h1 | h1
  · have : false ∈ ({true} : Set Bool) := h1 ▸ Set.mem_univ false
    simp at this
  · have : true ∈ ({false} : Set Bool) := h1 ▸ Set.mem_univ true
    simp at this

-- `Statement:` in a well-founded carrier one increment `a` equals a finite join of join-irreducibles
-- applied to the same state (Birkhoff; Mathlib `exists_supIrred_decomposition`).
example {α : Type*} [SemilatticeSup α] [OrderBot α] [WellFoundedLT α] (s a : α) :
    ∃ t : Finset α, (∀ b ∈ t, SupIrred b) ∧ s ⊔ a = t.sup id ⊔ s := by
  obtain ⟨t, ht, hirr⟩ := exists_supIrred_decomposition a
  exact ⟨t, hirr, by rw [ht, sup_comm]⟩

end ZeroParadox

/-! ## Axiom Purity Check

`#print axioms` reports every foundational axiom a theorem depends on.
Clean ZP-A proofs should depend only on the ZPSemilattice typeclass fields
and Lean's kernel axioms (propext, Classical.choice, Quot.sound).
No Mathlib-specific axioms should appear.
-/

section PurityCheck
open ZeroParadox ZPSemilattice

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
