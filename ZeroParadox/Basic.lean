import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import ZeroParadox.ZPD
import ZeroParadox.ZPE
import ZeroParadox.ZPG
import ZeroParadox.ZPH
import ZeroParadox.ZPI
import ZeroParadox.ZPJ
import ZeroParadox.ZPK

/-!
# Zero Paradox — Library Root

Umbrella import for the full Zero Paradox Lean library. Importing this single file
pulls in all formalized layers (ZP-A through ZP-K). For per-file summaries, dependency
order, axiom profile, and honest scope boundaries, see `ZeroParadox/README.md`.

Dependency order of the layers:

  ZP-A → ZP-B → ZP-C → ZP-D → ZP-E → ZP-J → ZP-K → ZP-I

  ZP-G (self-contained) → ZP-H (depends on ZP-G, ZP-C, ZP-D)

The central result is **T-SNAP** (`ZeroParadox.ZPE.t_snap_machine` and
`ZeroParadox.ZPE.t_snap_derived`): the Binary Snap c₀ ∨ c₁ = c₁ — derived from the
standard join-semilattice bottom axiom A4, with no snap-specific commitments.
-/
