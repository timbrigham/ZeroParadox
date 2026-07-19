import ZeroParadox.Ordinal.SnapSuccession
import ZeroParadox.State.StateSpace

set_option maxHeartbeats 400000

/-!
# The type bridge: a separated succession as an interface, with two known implementations

The snap's succession of new bottoms shows up in two charts of the framework that are DIFFERENT TYPES:
- the **ordinal chart** — the ε-numbers `ε₀ < ε₁ < ε₂ < …`, consecutive ones separated by strict order
  (`Ordinal/SnapSuccession.lean`, `succession_lt_succ`);
- the **Hilbert chart** — the state vectors `T(S₀), T(S₁), …`, consecutive ones separated by orthogonality
  (`State/StateSpace.lean`, `t5_strict_orthogonal`, on ZP-D's DP-1).

These are the same phenomenon — "when one instance ends, another begins separated from the last" — but their
carriers are distinct types at **different universe levels** (`Ordinal : Type 1`, `StateSpace n : Type 0`).
They literally cannot be equated; asking whether the ordinal succession *is* the Hilbert succession is
ill-typed, the same type boundary as MC-1.

The honest bridge is therefore **not an identity but an interface**: state the *required attributes* of a
separated generating succession — a carrier, a separation relation, an ℕ-indexed succession, and the law
that consecutive terms are separated — and exhibit each chart as a *known implementation*. This is the
framework's own instance-vs-requirements move (you cannot name the object, only the requirements it meets,
of which each structure is a witness — the Yoneda/representability reading), built the same way
`Computability/SelfApp.lean` handles `AbstractSelfApp` across set theory and the 2-adics.

**Honest scope.** This states no new theorem: the two `separated` laws are the already-proved
`succession_lt_succ` (ordinal) and `t5_strict_orthogonal` (Hilbert). The content is the *identification* —
that both are witnesses of one interface — and the honest fence that the carriers are provably distinct
types, so the shared shape is the interface, never a cross-type `=`. One asymmetry is kept visible: the
ordinal implementation separates unconditionally, the Hilbert one only given a genuine-transition sequence
(consecutive states distinct).

## Engineer's Take

By using the abstract shape of epsilon zero from least fixed point, we can now define a generic
relationship to the entire class. We cannot cross a type boundary, however we can dictate shared shape and
position.
-/

namespace ZeroParadox

open Order Ordinal

universe u

/-- **The required attributes of a separated generating succession** (class X): a carrier, a separation
    relation `sep` (the apartness consecutive instances satisfy), an ℕ-indexed succession `seq`, and the
    law that consecutive terms are always separated. The ordinal ε-chain and the Hilbert state-chain are
    each a known implementation. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: an interface bundling a carrier with a separation relation and
-- an ℕ-indexed succession whose consecutive terms are separated. Mathlib has chains and apartness
-- relations separately but no bundled "separated succession" interface used to bridge differently-typed
-- framework charts (ordinal strict-order vs Hilbert orthogonality) as implementations of one shape.
structure SeparatedSuccession where
  /-- The carrier of this implementation. -/
  carrier : Type u
  /-- The separation relation consecutive instances satisfy. -/
  sep : carrier → carrier → Prop
  /-- The succession of instances, indexed by ℕ. -/
  seq : ℕ → carrier
  /-- Consecutive instances are always separated — the succession never repeats. -/
  separated : ∀ k, sep (seq k) (seq (k + 1))

/-- **Implementation 1 — the ordinal chart.** The ε-numbers `ε_ k`, separated by strict order. The
    `separated` law is tonight's `succession_lt_succ`. -/
noncomputable def ordinalSuccession : SeparatedSuccession.{1} where
  carrier := Ordinal.{0}
  sep := (· < ·)
  seq := fun k => Ordinal.epsilon (k : Ordinal.{0})
  separated := fun k => by
    have h := succession_lt_succ (k : Ordinal.{0})
    simpa [Nat.cast_succ, Order.succ_eq_add_one] using h

/-- **Implementation 2 — the Hilbert chart.** The state vectors `T(Sₖ)`, separated by orthogonality
    (`⟨·,·⟩ = 0`). The `separated` law is ZP-D's `t5_strict_orthogonal`, given a genuine-transition
    sequence (consecutive states distinct). -/
noncomputable def hilbertSuccession (n : ℕ) (S : ℕ → Fin n) (hS : ∀ k, S k ≠ S (k + 1)) :
    SeparatedSuccession where
  carrier := StateSpace n
  sep := fun x y => @inner ℂ (StateSpace n) _ x y = 0
  seq := fun k => transitionOp n (S k)
  separated := fun k => t5_strict_orthogonal n S k (hS k)

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox
#print axioms ordinalSuccession
#print axioms hilbertSuccession
end PurityCheck
