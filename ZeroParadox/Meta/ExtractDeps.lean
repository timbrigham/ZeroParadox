import ZeroParadox.Algebra.Wheel
import ZeroParadox.Algebra.WheelFrac
import ZeroParadox.AxiomProfile
import ZeroParadox.Basic
import ZeroParadox.Category.AxG2Reduce
import ZeroParadox.Category.Category
import ZeroParadox.Category.Directed
import ZeroParadox.Category.GlobalZero
import ZeroParadox.Category.Heterogeneous
import ZeroParadox.Category.Lawvere
import ZeroParadox.Category.LinFunctor
import ZeroParadox.Category.Linearize
import ZeroParadox.Category.NoUniformCharacter
import ZeroParadox.Category.Obstruction
import ZeroParadox.Category.TopNoGo
import ZeroParadox.Category.TreeSeam
import ZeroParadox.Computability.Kleene
import ZeroParadox.Computability.Periodicity
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Information.BottomMeasure
import ZeroParadox.Information.PadicSurprisal
import ZeroParadox.Information.Surprisal
import ZeroParadox.Multihomed.Boundary
import ZeroParadox.Multihomed.BoundaryBridge
import ZeroParadox.Multihomed.CategoricalBridge
import ZeroParadox.Multihomed.EigenvectorExists
import ZeroParadox.Multihomed.Fork
import ZeroParadox.Multihomed.HilbertDiagonal
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.Multihomed.MC1Bridge
import ZeroParadox.Multihomed.PadicBridge
import ZeroParadox.Multihomed.TopNumEdge
import ZeroParadox.Multihomed.TreeObstructions
import ZeroParadox.Multihomed.TreeT1
import ZeroParadox.Multihomed.TreeT2
import ZeroParadox.Multihomed.TwoFacesBot
import ZeroParadox.Order.Lattice
import ZeroParadox.Order.PerronCapstone
import ZeroParadox.Order.PowerSet
import ZeroParadox.Order.Snap
import ZeroParadox.Ordinal.B6_CanonicalCNF
import ZeroParadox.Ordinal.ConstructiveOrdinals
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Goodstein
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.KirbyParis
import ZeroParadox.Ordinal.Kruskal
import ZeroParadox.Ordinal.P8
import ZeroParadox.Ordinal.WeakGoodstein
import ZeroParadox.Reals.MarkovSpectralGap
import ZeroParadox.Reals.OrderedField
import ZeroParadox.Reals.PerronFrobenius
import ZeroParadox.Reals.SpectralRadius
import ZeroParadox.Settheory.APG
import ZeroParadox.Settheory.AczelConn
import ZeroParadox.Settheory.Coalgebra
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Settheory.Model
import ZeroParadox.Settheory.OntBridge
import ZeroParadox.Settheory.QuineDichotomy
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.Wall_OneRoot
import ZeroParadox.State.HilbFunctor
import ZeroParadox.State.MeanErgodic
import ZeroParadox.State.ProbeSeparates
import ZeroParadox.State.ReversibleSpectrum
import ZeroParadox.State.StateSpace
import ZeroParadox.Valuation.AdeleGlobal
import ZeroParadox.Valuation.ArchPlace
import ZeroParadox.Valuation.FloorWitness
import ZeroParadox.Valuation.InvTowerNorm
import ZeroParadox.Valuation.InversionValuation
import ZeroParadox.Valuation.Ostrowski
import ZeroParadox.Valuation.Padic
import ZeroParadox.Valuation.PadicPerfect
import ZeroParadox.Valuation.PadicTree
import ZeroParadox.Valuation.PlaceAllPrimes
import ZeroParadox.Valuation.PlaceForcing
import ZeroParadox.Valuation.PlaceMetric
import ZeroParadox.Valuation.PolarityFlip
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Valuation.Scale
import ZeroParadox.Valuation.ScaleBridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Valuation.StrippedBottom
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.Valuation.ValuationAFA
import ZeroParadox.Valuation.ValuationAFA_Padic
import ZeroParadox.Vendored.NaturalOps
import ZeroParadox.Vendored.NaturalOpsPow
import ZeroParadox.ZPH_BottomCannotBe
import ZeroParadox.ZPH_MC1_TC04
import ZeroParadox.ZPH_MC1_TC05
import ZeroParadox.ZPH_MC1_TC06
import ZeroParadox.ZPH_MC1_TC07
import ZeroParadox.ZPH_MC1_TC08
import ZeroParadox.ZPH_MC1_TC09
import ZeroParadox.ZPH_MC1_TC10
import ZeroParadox.ZPH_MC1_TC11
import ZeroParadox.ZPH_MC1_TC12
import ZeroParadox.ZPH_MC1_TC13
import ZeroParadox.ZPH_MC1_TC14
import ZeroParadox.ZPH_MC1_TC15
import ZeroParadox.ZPH_MC1_TC16
import ZeroParadox.ZPH_MC1_TC17
import ZeroParadox.ZPH_MC1_TC18
import ZeroParadox.ZPH_MC1_TC19
import ZeroParadox.ZPH_MC1_TC20
import ZeroParadox.ZPH_MC1_TC21
import ZeroParadox.ZPH_MC1_TC22
import ZeroParadox.ZPH_MC1_TC23
import ZeroParadox.ZPH_MC1_TC24
import ZeroParadox.ZPH_MC1_TC25
import ZeroParadox.ZPH_MC1_TC26
import ZeroParadox.ZPH_MC1_TC27
import ZeroParadox.ZPH_MC1_TC28
import ZeroParadox.ZPH_MC1_TC29
import ZeroParadox.ZPH_MC1_TC30
import ZeroParadox.ZPH_MC1_TC31
import ZeroParadox.ZPH_MC1_TC32
import ZeroParadox.ZPH_MC1_TC33
import ZeroParadox.ZPH_MC1_TC34
import ZeroParadox.ZPH_MC1_TC35
import ZeroParadox.ZPH_MC1_TC36
import ZeroParadox.ZPH_MC1_TC37
import ZeroParadox.ZPH_MC1_TC38
import ZeroParadox.ZPH_MC1_TC39
import ZeroParadox.ZPH_MC1_TC40
import ZeroParadox.ZPH_MC1_TC41
import ZeroParadox.ZPH_MC1_TC42
import ZeroParadox.ZPH_MC1_TC43
import ZeroParadox.ZPH_MC1_TC44
import ZeroParadox.ZPH_MC1_TC45
import ZeroParadox.ZPH_MC1_TC46
import ZeroParadox.ZPH_MC1_TC47
import ZeroParadox.ZPH_MC1_TC48
import ZeroParadox.ZPH_MC1_TC49
import ZeroParadox.ZPH_MC1_TC50
import ZeroParadox.ZPN_ChoiceProbe
import Lean

/-!
# Declaration-level dependency extractor (interop Issue 13, ZP side)

Walks the fully-loaded environment and, for every declaration that lives in a tracked
ZeroParadox source module (Vendored excluded), records the constants referenced in its
TYPE (hard, structural dependencies -- they pin the module boundary) and in its VALUE /
proof term (softer dependencies). Emits a RAW dump to
`.claude-local/translation_matrix/deps_raw.json`.

`deps_build.py` then intersects BOTH endpoints of every edge with the registry's tracked
qualified-name set, so the final `deps.json` cannot contain an endpoint that is not a
registered declaration (no dangling edges -- satisfies interop Issue 13 / D3 by construction).
Private names are de-mangled to their user-facing form so they match the registry's
`old.qualified` (the trust-root check demangled the same way).

This module is intentionally NOT imported by `ZeroParadox.Basic`, so a normal `lake build`
skips it. Run the extraction explicitly:

    lake build ZeroParadox.Meta.ExtractDeps

(It re-runs whenever the module is (re)elaborated; the file write is a build side effect.)
-/

open Lean

namespace ZeroParadox.Meta

/-- A tracked ZP source module: under the `ZeroParadox` namespace, excluding `Vendored`. -/
def isTrackedModule (m : Name) : Bool :=
  (`ZeroParadox).isPrefixOf m && ! (`ZeroParadox.Vendored).isPrefixOf m

/-- De-mangle private names to their user-facing form (the registry stores the source name). -/
def userName (n : Name) : Name :=
  (privateToUserName? n).getD n

def nameStr (n : Name) : String := toString (userName n)

def namesToJson (arr : Array Name) : Json :=
  Json.arr (arr.map (fun c => Json.str (nameStr c)))

run_cmd do
  let env ← getEnv
  let mut recs : Array Json := #[]
  for (name, ci) in env.constants.toList do
    match env.getModuleFor? name with
    | some m =>
      if isTrackedModule m then
        let tdeps := ci.type.getUsedConstants
        let vdeps := (ci.value?.map (·.getUsedConstants)).getD #[]
        recs := recs.push <| Json.mkObj [
          ("from", Json.str (nameStr name)),
          ("module", Json.str (toString m)),
          ("type_deps", namesToJson tdeps),
          ("val_deps", namesToJson vdeps)
        ]
    | none => pure ()
  IO.FS.writeFile ".claude-local/translation_matrix/deps_raw.json" (Json.arr recs).compress
  logInfo s!"[ExtractDeps] wrote deps_raw.json -- {recs.size} tracked declarations"

end ZeroParadox.Meta
