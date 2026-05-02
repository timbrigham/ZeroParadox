import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-!
# ZP-E: Bridge Document

## Engineer's Take

By wiring together the state changes out of ZPC and the mandatory increments in
ZPA, it turned AX-1 into a theorem we can prove instead of an axiom. In
programming you can have a state change eventually return to non-running.
However, once a program is executed, it's executed. It doesn't change the fact
that it executed at one point in the past. DA-1, DA-2, and DA-3 need to be
treated as forward references. These were not solved until a much later point.
DA-1 is addressed in ZPJ and ZPK. DA-2 is addressed in ZPI.

---

## Formal Overview (AI-assisted)

Cross-framework synthesis of ZP-A through ZP-D. Provides three formal inserts:

- DA-1 (Instantiation as Execution): Paths 1 and 3 are now in Lean scope via ZP-K.
  ZPK.machinePhaseKleene gives MachinePhase a KleeneStructure instance; ZPK.da1_closed_concrete
  proves IsQuineAtom (bot : MachinePhase) — the initial state is self-containing and
  self-executing, not a static description. Path 2 (informational bridge, L-INF) remains
  outside Lean scope. See § I-DA1 for the full argument and ZP-K for the formal closure.
- DA-2 (Instantiation Succession): algebraic characterisation of the ⊥ role across instantiations
- DA-3 (Perspective-Relative Cardinality): DA-3-D1 as a definition; DA-3-C1 is a
  candidate claim and is not formalised here

Key result: T-SNAP — the Binary Snap ⊥ → ε₀ is a derived theorem, not an axiom.
AX-1 is retired. The cross-framework link is established by giving ZPC.MachinePhase
a ZPSemilattice instance, making T-SNAP a direct consequence of ZPA.bot_join.
-/

namespace ZeroParadox.ZPE

open ZeroParadox.ZPA ZPSemilattice
open ZeroParadox.ZPC

/-! ## I. MachinePhase as a ZPSemilattice

The formal cross-framework bridge. ZPC's MachinePhase (two-element type: initial,
running) satisfies all four ZPA axioms A1–A4. Under this instance:
- bot  = initial = c₀  (the Null State, ⊥)
- join = the binary maximum (running absorbs; initial is identity)
- ε₀   = running = c₁  (the First Atomic State)
This makes T-SNAP type-theoretically grounded: ⊥ ∨ ε₀ = ε₀ is definitional. -/

instance machinePhaseZPS : ZPSemilattice MachinePhase where
  join x y := match x, y with
    | .initial, y       => y
    | x,        .initial => x
    | .running, .running => .running
  bot := .initial
  join_assoc := by intro x y z; cases x <;> cases y <;> cases z <;> rfl
  join_comm  := by intro x y;   cases x <;> cases y              <;> rfl
  join_idem  := by intro x;     cases x                          <;> rfl
  bot_join   := by intro x;     cases x                          <;> rfl

/-! ## I-DA1. DA-1 — Derived Proposition: Instantiation as Execution

DA-1 states: a machine configuration at the incompressibility threshold P₀ is a
live execution event, not a static description.

Three paths support this (ZP-E v3.6 framing):
  Path 1 — Structural (ZP-J T-EXEC + ZP-K): nothing external to ⊥ can execute ⊥;
    ⊥ must execute itself → ⊥ = {⊥} is forced. ZPK.machinePhaseAFA gives MachinePhase
    an AFAStructure instance encoding this. ZPK.da1_closed_concrete : IsQuineAtom bot.
    IN LEAN SCOPE via ZP-K.
  Path 2 — Informational (ZP-C L-INF): surprisal at ⊥ is unbounded → no finite
    interpreter can hold ⊥ → static-description state eliminated.
    OUTSIDE LEAN SCOPE: "unbounded surprisal → necessarily executing" is an ontological
    bridge claim not derivable in type theory.
  Path 3 — Computational (ZP-K Kleene): no shorter program is prior to ⊥ →
    ⊥ is its own program. ZPK.machinePhaseKleene gives MachinePhase a KleeneStructure
    instance with botCode witnessing the Kleene fixed point.
    IN LEAN SCOPE via ZP-K.

DA-1 Lean scope status (updated ZP-K, April 2026):
  Paths 1 and 3: formally closed — ZPK.da1_closed_concrete : IsQuineAtom (bot : MachinePhase).
  Path 2: outside Lean scope — informational bridge remains an ontological commitment.
  T-SNAP derivation: complete independently via l_run, tq_ih, bot_join (see t_snap_derived).

Prior "Outside Lean Scope" designation is superseded. ZP-K is the formal closure. -/

/-! ## II. T-SNAP — Binary Snap Causality (AX-1 Retired)

Status: DERIVED — cross-framework.
Dependencies: ZPC.l_run, ZPC.tq_ih, ZPA A4 (bot_join), ZPB C3 (cited below). -/

/-- T-SNAP (algebraic core): In any ZPSemilattice, ⊥ joined with ε₀ gives ε₀.
    The Binary Snap ⊥ → ε₀ is modelled as the join ⊥ ∨ ε₀ = ε₀.
    Immediate from A4 (bot_join). -/
theorem t_snap_join {L : Type*} [ZPSemilattice L] (ε₀ : L) :
    join (bot : L) ε₀ = ε₀ :=
  bot_join ε₀

/-- T-SNAP (concrete): In the MachinePhase semilattice, c₀ ∨ c₁ = c₁.
    The Binary Snap is exactly the join transition initial → running. -/
theorem t_snap_machine : join c₀ c₁ = c₁ := rfl

/-- T-SNAP (derived): Assembly theorem.
    (1) c₀ ≠ c₁  — ZPC L-RUN: execution is a non-null state change.
    (2) c₁ ≠ c₀  — ZPC TQ-IH: no execution avoids a non-null configuration.
    (3) join c₀ c₁ = c₁  — the snap is a valid join transition (A4/bot_join).
    Conclusion: the Binary Snap is a derived consequence. AX-1 is no longer an axiom. -/
theorem t_snap_derived :
    c₀ ≠ c₁ ∧ c₁ ≠ c₀ ∧ join c₀ c₁ = c₁ :=
  ⟨l_run, tq_ih, rfl⟩

/-- T-SNAP (irreversibility): Algebraic form of ZP-A R1 (no subtraction operator).
    If x ≼ y and x ≠ y, no join from y can return to x.
    Complements ZPB.c3_irreversible (topological irreversibility in Q₂). -/
theorem t_snap_irreversible {L : Type*} [ZPSemilattice L] {x y : L}
    (hle : le x y) (hne : x ≠ y) :
    ¬∃ z : L, join y z = x := by
  intro ⟨z, hz⟩
  -- If join y z = x, then y ≼ x: join y x = join y (join y z) = join (join y y) z
  --   = join y z = x. So le y x. Combined with le x y, antisymmetry gives x = y.
  have hyx : le y x := show join y x = x by
    rw [← hz, ← join_assoc, join_idem]
  exact hne (le_antisymm hle hyx)

/-! ## III. DA-2 — Instantiation Succession

DA-2: A state S satisfies the structural ⊥ role for instantiation I_{n+1} iff
∀ x, join S x = x — i.e., S is an additive identity under join (A4 characterisation).
By da2_bottom_characterization, this uniquely identifies S as ⊥ within that semilattice.
The Zero Paradox iterated: the terminal state of Iₙ is informationally rich (≠ ⊥ₙ)
yet algebraically acts as ⊥_{n+1} for the successor instantiation. -/

/-- DA-2 (algebraic): The ⊥ role is uniquely characterised by A4.
    S satisfies "∀ x, join S x = x" if and only if S = bot. -/
theorem da2_bottom_characterization {L : Type*} [ZPSemilattice L] (S : L) :
    (∀ x : L, join S x = x) ↔ S = bot := by
  constructor
  · intro h
    -- join S bot = bot  (hypothesis at x = bot)
    -- S = join bot S    (A4: bot_join)
    --   = join S bot    (A2: join_comm)
    --   = bot           (above)
    calc S = join bot S   := (bot_join S).symm
      _    = join S bot   := join_comm bot S
      _    = bot          := h bot
  · intro h
    subst h
    exact bot_join

/-- C-DA2 (corollary): In any sequence starting at ⊥ that has advanced,
    the current state plays the ⊥ role for a distinct successor instantiation.
    The terminal state satisfies ∀ x, join S x = x in the new semilattice
    while S ≠ bot in the prior one — the Zero Paradox at the instantiation boundary.
    Formal consequence: da2_bottom_characterization applied to the successor semilattice. -/
theorem c_da2_novelty {L : Type*} [ZPSemilattice L] (S : L)
    (hS_not_bot : S ≠ bot) :
    ¬(∀ x : L, join S x = x) := by
  rw [da2_bottom_characterization]
  exact hS_not_bot

/-! ## IV. DA-3 — Perspective-Relative Cardinality (DA-3-D1)

DA-3-D1: The accessible cardinality of a position p in semilattice L is the
cardinality of the set of states reachable from p by the partial order ≼.
This captures that cardinality is position-dependent, not an intrinsic absolute.

DA-3-C1 (candidate claim: appearance of absolute cardinality is an artifact of
treating L as having a view from outside) is NOT formalised here — explicitly
marked CANDIDATE in ZP-E v2.0; formal derivation deferred to OQ-E2. -/

/-- DA-3-D1: Accessible cardinality from position p — the Cardinal of states ≽ p. -/
noncomputable def da3_accessibleCardinality {L : Type*} [ZPSemilattice L] (p : L) : Cardinal :=
  Cardinal.mk { x : L // le p x }

/-! ## V. T-SNAP (Accessible Shrink) — Structural Content of the Binary Snap

T-SNAP's algebraic core (join ⊥ ε₀ = ε₀, proved by rfl from A4) is an identity
on the join operation. The deeper result is what the snap does to reachability:
before the snap, ⊥ can reach ALL of L; after the snap, ε₀ can reach only a proper
subset. This is the inverse face of the Zero Paradox: ⊥ is the universal source,
yet transitioning away from it permanently forecloses access to ⊥ itself. -/

/-- T-SNAP (accessible states shrink): the Binary Snap strictly narrows the set of
    reachable states. From ⊥, every element of L is accessible (A4: bot_le x always).
    From ε₀, only {x | ε₀ ≤ x} is accessible — a proper subset, since ⊥ is excluded:
    if le ε₀ ⊥ then le_antisymm (with le ⊥ ε₀, always true) gives ⊥ = ε₀,
    contradicting hne. This is the structural content beyond t_snap_machine := rfl.
    Note: for infinite L, proper subset does not imply a smaller Cardinal (ℕ\{0} ≃ ℕ).
    For Fintype L, this does imply da3_accessibleCardinality ε₀ < da3_accessibleCardinality ⊥. -/
theorem t_snap_accessible_proper_subset {L : Type*} [ZPSemilattice L] {ε₀ : L}
    (hne : (bot : L) ≠ ε₀) :
    {x : L | le ε₀ x} ⊂ {x : L | le bot x} := by
  constructor
  · intro x _; exact bot_le x
  · intro h
    exact hne (le_antisymm (bot_le ε₀) (h (bot_le bot)))

/-! ## VI. DP-2 — Execution Distinguishability and DA-1 Lean Formalization

DP-2 (Design Principle — Execution Distinguishability): Machine states carry execution
history independently of output values. A machine in state c₁ can output ⊥ (the null
value) while being in a configuration entirely distinct from a machine in state c₀. The
post-execution null and the pre-execution null are different instances.

This separates two things the narrative might conflate: the *value* a machine produces
(which can be ⊥ in both cases) and the *machine state* (c₀ before execution, c₁ after).

Given DP-2, DA-1 (instantiation = execution) is Lean-formalizable at the minimal-path
level: the act of instantiating ⊥ moves the machine from c₀ to c₁, regardless of what
value the operation returns. The "return to null" is a new null — not a return to c₀. -/

/-- A machine output tagged with the state that produced it.
    Separates the output value (what the machine returns) from the machine state
    (where the machine is). This structure is the formal content of DP-2. -/
structure TrackedOutput where
  value : MachinePhase   -- the value the machine returns
  state : MachinePhase   -- the machine state producing it
  deriving DecidableEq

/-- The pre-instantiation configuration: null value, c₀ machine state. -/
def preInstantiation : TrackedOutput := ⟨c₀, c₀⟩

/-- The post-instantiation configuration: null value returned, c₁ machine state.
    This is the "different instance of null" — same output value as preInstantiation,
    but the machine has executed. The snap occurred; c₀ is not recoverable. -/
def postInstantiation : TrackedOutput := ⟨c₀, c₁⟩

/-- DP-2 (formal content): pre- and post-instantiation states are provably distinct
    even when both produce the null value ⊥. Execution history is encoded in the
    machine state, not the output value. -/
theorem dp2_execution_distinguishability :
    preInstantiation.value = postInstantiation.value ∧
    preInstantiation.state ≠ postInstantiation.state :=
  ⟨rfl, by decide⟩

/-- DA-1 Minimal Path: The act of instantiating ⊥ moves the machine to c₁,
    even when the operation returns ⊥ as its output value.
    The "return to null" is postInstantiation — a new null, not preInstantiation.
    Given DP-2, this is DA-1 at the formally minimal level: instantiation is execution.
    One step from c₀ to c₁ is structurally unavoidable; the output value is irrelevant
    to whether execution occurred. -/
theorem da1_minimal_path :
    let before := preInstantiation
    let after  := postInstantiation
    before.value = after.value ∧   -- same output value (both ⊥)
    before.state ≠ after.state ∧   -- distinct machine states
    before.state = c₀ ∧            -- before: pre-execution null
    after.state  = c₁ :=           -- after: execution occurred (the snap)
  ⟨rfl, by decide, rfl, rfl⟩

end ZeroParadox.ZPE

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox.ZPE ZeroParadox.ZPA ZPSemilattice ZeroParadox.ZPC

#print axioms t_snap_join
#print axioms t_snap_machine
#print axioms t_snap_derived
#print axioms t_snap_irreversible
#print axioms da2_bottom_characterization
#print axioms c_da2_novelty
#print axioms t_snap_accessible_proper_subset
#print axioms dp2_execution_distinguishability
#print axioms da1_minimal_path

end PurityCheck
