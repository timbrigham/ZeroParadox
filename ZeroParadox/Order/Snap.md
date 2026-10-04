# ZP-E formal inserts, and what T-SNAP does and does not carry

Overview for `ZeroParadox/Order/Snap.lean`. The Lean file holds the declarations, the Engineer's Take and
the per-declaration commentary; the results are described at each declaration, not listed again here.

## The three formal inserts

Cross-framework synthesis of ZP-A through ZP-D. Provides three formal inserts:

- DA-1 (Instantiation as Execution), closed given DP-2. Given its precondition, that the
  configuration reaching P₀ is a running machine's current configuration (Sense B) and not an inert
  string, c₀ → c₁ is D7's (T-SNAP Step 3), and DP-2 with `da1_minimal_path` shows the two
  configurations distinct while returning the same output value. The precondition is what the
  occurrence commitment asserts; DA-1 consumes it and does not supply it. Three paths argue for the
  precondition and none derives it (ZP-E § IV):
  - Path 1 (structural, ZP-J T-EXEC + ZP-K): nothing external to ⊥ can execute ⊥, so if ⊥ executes
    at all, the executor is ⊥ itself. That rules out an external executor, not an inert ⊥. Its Lean
    counterpart is `da1_closed_concrete`, which proves IsQuineAtom (bot : MachinePhase) and nothing
    computational; the self-executing reading is carried by the KleeneStructure commitment.
  - Path 2 (informational, ZP-C L-INF): surprisal at ⊥ is unbounded, so no finite interpreter holds
    ⊥ as a static description. The step from there to executing is a bridge principle of its own,
    which the framework does not adopt, which is not the occurrence commitment, and which is not a
    premise of the Snap.
  - Path 3 (computational, ZP-C D1 + AIT): incompressibility rules out a shorter external
    generator, not an inert string, so executing is not derivable from incompressibility. Its Lean
    counterpart is the machinePhaseKleene instance's botCode_is_quine field, a KleeneStructure
    requirement that constant codes also meet, not a witness of execution and not a second
    independent proof.

  The Lean counterparts of Paths 1 and 3 are carried together by `da1_paths_unified` as a
  conjunction; that they name one structural fact is the framework's reading. ZP-K states what is
  and is not proved.
- DA-2 (Instantiation Succession): algebraic characterisation of the ⊥ role across instantiations
- DA-3 (Perspective-Relative Cardinality): DA-3-D1 as a definition; DA-3-C1 is a
  candidate claim and is not formalised here

## T-SNAP, and the retirement of AX-1

AX-1 (Binary Snap Causality) is retired. Its content was split in two: the SHAPE of the snap is proved,
as Theorem T-SNAP, and that the snap OCCURS is stated separately: it follows from the occurrence commitment
(instantiation occurs) together with DA-1 (closed given DP-2). `tsnap_holds_but_nothing_moves` shows T-SNAP does not carry it. Here the Binary Snap is ⊥ → ε₀ with ε₀
the running phase c₁ of MachinePhase, the first state above ⊥ in the discrete-state chart. The cross-framework link is
established by giving `MachinePhase` (`ZeroParadox/Information/Surprisal.lean`) a `ZPSemilattice`
instance, which makes the join conjunct of T-SNAP a direct consequence of the semilattice bottom law
`bot_join` (`ZeroParadox/Order/Lattice.lean`). `t_snap_given` states two of T-SNAP's premises as
hypotheses: CC-1 (the start at ⊥) and occurrence at the first step.
