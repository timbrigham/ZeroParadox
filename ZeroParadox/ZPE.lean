import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-!
# ZP-E: Bridge Document

Cross-framework synthesis of ZP-A through ZP-D. Provides three formal inserts:

- DA-1 (Instantiation as Execution): DESIGN PRINCIPLE — cites ZPC.l_inf (not D7).
  Informational extremity at P₀ (unbounded surprisal, L-INF) forces execution rather
  than static description. Explicit ontological commitment, not a definitional
  clarification. No Lean theorem — the mathematical premise is ZPC.l_inf; the bridge
  from extremity to execution is a named design principle documented below (§ I-DA1).
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

/-! ## I-DA1. DA-1 — Design Principle: Informational Extremity Forces Execution

DA-1 states: a machine configuration at the incompressibility threshold P₀ is a
live execution event, not a static description.

Mathematical premise (ZPC.l_inf): the surprisal at ball-hierarchy depths approaching
0 ∈ Q₂ is unbounded — for any finite M, ∃ depth n with I(n) > M. The null state
c₀ = ⊥ corresponds to this limit point. Its informational content has no finite bound.

Design commitment: a configuration with unbounded informational content cannot be
a static description awaiting external interpretation. Any external interpreter would
need to be at least as informationally rich as what it interprets, but ⊥ has no
finite bound — it is the compressed limit of all possible binary programs, prior to
any interpreter. Therefore c₀ at P₀ is necessarily an execution event, not a
description awaiting instantiation.

This replaces the circular D7 citation in prior ZP-E prose. D7 defines what a
configuration IS; it cannot prove that the configuration is EXECUTING without
presupposing execution. L-INF supplies the formal premise that breaks this circularity:
the reason c₀ is executing is not that D7 says so, but that its informational
extremity admits no external interpreter.

DA-1 is labelled DESIGN PRINCIPLE — it introduces a genuine ontological commitment.
The commitment is targeted: unbounded surprisal at ⊥ (L-INF) closes the
description/execution gap. CC-1 (S₀ = ⊥ is a modelling commitment, ZP-A) propagates
as a named dependency: T-SNAP is derived given DA-1 and CC-1, both explicit.

Lean status: no Lean theorem. L-INF (ZPC) is the formal premise; the bridge is
interpretive and documented here as a named, honest design commitment. -/

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

end PurityCheck
