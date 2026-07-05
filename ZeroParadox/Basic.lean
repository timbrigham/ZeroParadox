import ZeroParadox.Order.Lattice
import ZeroParadox.Valuation.Padic
import ZeroParadox.Information.Surprisal
import ZeroParadox.State.StateSpace
import ZeroParadox.Order.Snap
import ZeroParadox.Reals.OrderedField
import ZeroParadox.Category.Category
import ZeroParadox.Multihomed.CategoricalBridge
import ZeroParadox.Order.PowerSet
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.State.HilbFunctor
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.Multihomed.MC1Bridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Settheory.AczelConn
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Valuation.Scale
import ZeroParadox.Valuation.ScaleBridge
import ZeroParadox.Settheory.Model
import ZeroParadox.Computability.Kleene
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Settheory.OntBridge
import ZeroParadox.Settheory.APG
import ZeroParadox.Algebra.Wheel
import ZeroParadox.Algebra.WheelFrac
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Valuation.Ostrowski
import ZeroParadox.Settheory.Coalgebra
import ZeroParadox.Category.Lawvere
import ZeroParadox.Multihomed.Boundary
import ZeroParadox.Multihomed.BoundaryBridge
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Settheory.QuineDichotomy

/-!
# Zero Paradox — Library Root

Umbrella import for the full Zero Paradox Lean library. Importing this single file
pulls in all formalized layers (ZP-A through ZP-L, plus ZP-F). For per-file summaries,
dependency order, axiom profile, and honest scope boundaries, see `ZeroParadox/README.md`.

Dependency order of the layers:

  ZP-A → ZP-B → ZP-C → ZP-D → ZP-E → ZP-J → ZP-K → ZP-L → ZP-M → ZP-I

  ZP-F (self-contained — real numbers counterexample)

  ZP-G (self-contained) → ZP-H (depends on ZP-G, ZP-C, ZP-D)
  ZP-H-PowerSet (self-contained Mathlib-only witness for structural floor)

  ZP-P (self-contained synthesis — the fixed-point fork; Mathlib-only)

The central result is **T-SNAP** (`ZeroParadox.t_snap_machine` and
`ZeroParadox.t_snap_derived`): the Binary Snap c₀ ∨ c₁ = c₁ — derived from the
standard join-semilattice bottom axiom A4, with no snap-specific commitments.
-/
