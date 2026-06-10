import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import ZeroParadox.ZPD
import ZeroParadox.ZPE
import ZeroParadox.ZPF
import ZeroParadox.ZPG
import ZeroParadox.ZPH
import ZeroParadox.ZPH_PowerSet
import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPH_HilbFunctor
import ZeroParadox.ZPI
import ZeroParadox.ZPJ
import ZeroParadox.ZPJ_AczelConn
import ZeroParadox.ZPJ_SelfApp
import ZeroParadox.ZPJ_Scale
import ZeroParadox.ZPJ_Model
import ZeroParadox.ZPK
import ZeroParadox.ZPL
import ZeroParadox.ZPM
import ZeroParadox.ZPJ_OntBridge
import ZeroParadox.ZPJ_APG
import ZeroParadox.ZPJ_Wheel
import ZeroParadox.ZPJ_WheelFrac

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

The central result is **T-SNAP** (`ZeroParadox.ZPE.t_snap_machine` and
`ZeroParadox.ZPE.t_snap_derived`): the Binary Snap c₀ ∨ c₁ = c₁ — derived from the
standard join-semilattice bottom axiom A4, with no snap-specific commitments.
-/
