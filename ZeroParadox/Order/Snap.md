# ZP-E formal inserts, and what T-SNAP does and does not carry

Overview for `ZeroParadox/Order/Snap.lean`. The Lean file holds the declarations, the Engineer's Take and
the per-declaration commentary; the results are described at each declaration, not listed again here.

## The three formal inserts

Cross-framework synthesis of ZP-A through ZP-D. Provides three formal inserts:

- DA-1 (Instantiation as Execution): Paths 1 and 3 are in Lean scope via ZP-K.
  machinePhaseKleene gives MachinePhase a KleeneStructure instance; da1_closed_concrete
  proves IsQuineAtom (bot : MachinePhase) — the initial state is self-containing, and it is
  the only such state. The further reading "self-executing, not a static description" is
  DA-1's claim, carried by the KleeneStructure commitment rather than by that theorem
  (which mentions no Code and no execution). Path 2 (informational bridge, L-INF) remains
  outside Lean scope. See § I-DA1 of the Lean file for the full argument and ZP-K for what is and is not proved.
- DA-2 (Instantiation Succession): algebraic characterisation of the ⊥ role across instantiations
- DA-3 (Perspective-Relative Cardinality): DA-3-D1 as a definition; DA-3-C1 is a
  candidate claim and is not formalised here

## T-SNAP, and the retirement of AX-1

AX-1 (Binary Snap Causality) is retired. Its content was split in two: the SHAPE of the snap is proved,
as Theorem T-SNAP, and that the snap OCCURS is stated separately, as the occurrence commitment
(`tsnap_holds_but_nothing_moves` shows T-SNAP does not carry it). Here the Binary Snap is ⊥ → ε₀ with ε₀
the running phase c₁ of MachinePhase, the first state above ⊥ in the discrete-state chart. The cross-framework link is
established by giving `MachinePhase` (`ZeroParadox/Information/Surprisal.lean`) a `ZPSemilattice`
instance, which makes the join conjunct of T-SNAP a direct consequence of the semilattice bottom law
`bot_join` (`ZeroParadox/Order/Lattice.lean`). `t_snap_given` states two of T-SNAP's premises as
hypotheses: CC-1 (the start at ⊥) and occurrence at the first step.
