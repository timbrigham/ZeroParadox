import ZeroParadox.Algebra.Wheel
import ZeroParadox.Algebra.WheelFrac
import ZeroParadox.AxiomProfile
import ZeroParadox.BottomCannotBe
import ZeroParadox.Category.AxG2Reduce
import ZeroParadox.Category.CardinalitySplit
import ZeroParadox.Category.Category
import ZeroParadox.Category.CoalgebraForkPlace
import ZeroParadox.Category.CrossCategoryArrow
import ZeroParadox.Category.CrossRootEdge
import ZeroParadox.Category.Directed
import ZeroParadox.Category.GlobalZero
import ZeroParadox.Category.Heterogeneous
import ZeroParadox.Category.KleisliInitialColimit
import ZeroParadox.Category.Lawvere
import ZeroParadox.Category.LinFunctor
import ZeroParadox.Category.Linearize
import ZeroParadox.Category.NoUniformCharacter
import ZeroParadox.Category.Node4Generation
import ZeroParadox.Category.Obstruction
import ZeroParadox.Category.PointednessSharp
import ZeroParadox.Category.RootCutBinary
import ZeroParadox.Category.RootCutDegeneracy
import ZeroParadox.Category.SeamArrowLevel
import ZeroParadox.Category.SeamArrowSignature
import ZeroParadox.Category.SeamBiproductUnit
import ZeroParadox.Category.SeamBridge
import ZeroParadox.Category.SeamCoincidence
import ZeroParadox.Category.SeamComparisonMap
import ZeroParadox.Category.SeamGeneric
import ZeroParadox.Category.SeamLimColim
import ZeroParadox.Category.SeamNotColimit
import ZeroParadox.Category.SeamUniqueness
import ZeroParadox.Category.TopNoGo
import ZeroParadox.Category.TreeSeam
import ZeroParadox.Computability.ChoicePurityInvariant
import ZeroParadox.Computability.Kleene
import ZeroParadox.Computability.MarkovNuUniversal
import ZeroParadox.Computability.NatListRegime
import ZeroParadox.Computability.Periodicity
import ZeroParadox.Computability.RootCutTrichotomy
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Computability.StationaryUnique
import ZeroParadox.Information.BottomMeasure
import ZeroParadox.Information.PadicSurprisal
import ZeroParadox.Information.Surprisal
import ZeroParadox.Multihomed.Boundary
import ZeroParadox.Multihomed.BoundaryBridge
import ZeroParadox.Multihomed.CategoricalBridge
import ZeroParadox.Multihomed.CrossRootCompleteness
import ZeroParadox.Multihomed.EigenvectorExists
import ZeroParadox.Multihomed.FloorFactsCooccur
import ZeroParadox.Multihomed.Fork
import ZeroParadox.Multihomed.HilbertDiagonal
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.Multihomed.MC1Bridge
import ZeroParadox.Multihomed.PadicBridge
import ZeroParadox.Multihomed.RootCutObstruction
import ZeroParadox.Multihomed.SeamConnectorFail
import ZeroParadox.Multihomed.SelfAppForkPlace
import ZeroParadox.Multihomed.SelfAppSeam
import ZeroParadox.Multihomed.SpanObstruction
import ZeroParadox.Multihomed.TopNumEdge
import ZeroParadox.Multihomed.TreeObstructions
import ZeroParadox.Multihomed.TreeT1
import ZeroParadox.Multihomed.TreeT2
import ZeroParadox.Multihomed.TwoFacesBot
import ZeroParadox.Multihomed.WallSpanRobust
import ZeroParadox.Order.Lattice
import ZeroParadox.Order.MarkovContractionDual
import ZeroParadox.Order.MarkovPlacement
import ZeroParadox.Order.PadicLimitCone
import ZeroParadox.Order.PerronCapstone
import ZeroParadox.Order.PowerSet
import ZeroParadox.Order.ProofFloorHomset
import ZeroParadox.Order.SeamSchema
import ZeroParadox.Order.Snap
import ZeroParadox.Order.WellFoundedObstruct
import ZeroParadox.Ordinal.B6_CanonicalCNF
import ZeroParadox.Ordinal.ConstructiveOrdinals
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Goodstein
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.KirbyParis
import ZeroParadox.Ordinal.Kruskal
import ZeroParadox.Ordinal.NaturalOpsPow
import ZeroParadox.Ordinal.P8
import ZeroParadox.Ordinal.ProofFloorCanonical
import ZeroParadox.Ordinal.WeakGoodstein
import ZeroParadox.Reals.MarkovSpectralGap
import ZeroParadox.Reals.OrderedField
import ZeroParadox.Reals.PerronFrobenius
import ZeroParadox.Reals.RateClassInvariant
import ZeroParadox.Reals.SpectralRadius
import ZeroParadox.Settheory.APG
import ZeroParadox.Settheory.AczelConn
import ZeroParadox.Settheory.Coalgebra
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Settheory.MetaFork
import ZeroParadox.Settheory.Model
import ZeroParadox.Settheory.OntBridge
import ZeroParadox.Settheory.QuineDichotomy
import ZeroParadox.Settheory.QuineHost
import ZeroParadox.Settheory.RequirementsGap
import ZeroParadox.Settheory.SetTheoryAFA
import ZeroParadox.Settheory.Wall
import ZeroParadox.Settheory.Wall_OneRoot
import ZeroParadox.State.HilbFunctor
import ZeroParadox.State.MeanErgodic
import ZeroParadox.State.ProbeSeparates
import ZeroParadox.State.ReversibleSpectrum
import ZeroParadox.State.StateSpace
import ZeroParadox.State.ThreeCarrierLeaf
import ZeroParadox.Valuation.AdeleGlobal
import ZeroParadox.Valuation.ArchPlace
import ZeroParadox.Valuation.ContractionRate
import ZeroParadox.Valuation.FloorWitness
import ZeroParadox.Valuation.InvTowerNorm
import ZeroParadox.Valuation.InversionValuation
import ZeroParadox.Valuation.NuLeafReconcile
import ZeroParadox.Valuation.NuRateEdge
import ZeroParadox.Valuation.NuRateMatch
import ZeroParadox.Valuation.Ostrowski
import ZeroParadox.Valuation.Padic
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Valuation.PadicPerfect
import ZeroParadox.Valuation.PadicTree
import ZeroParadox.Valuation.PlaceAllPrimes
import ZeroParadox.Valuation.PlaceForcing
import ZeroParadox.Valuation.PlaceMetric
import ZeroParadox.Valuation.PolarityFlip
import ZeroParadox.Valuation.RateTransport
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Valuation.RootAsymmetry
import ZeroParadox.Valuation.Scale
import ZeroParadox.Valuation.ScaleBridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Valuation.StrippedBottom
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.Valuation.ValuationAFA
import ZeroParadox.Valuation.ValuationAFA_Padic
import ZeroParadox.Vendored.NaturalOps
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

With the lakefile's full-tree `globs`, a normal `lake build` compiles this module, so the
extraction runs as a side effect of any full build. To run it in isolation:

    lake build ZeroParadox.Meta.ExtractDeps

(It re-runs whenever the module is (re)elaborated; the file write is the side effect.)
-/

open Lean

namespace ZeroParadox.Meta

/-- A tracked ZP source module: under the `ZeroParadox` namespace, excluding `Vendored`. -/
def isTrackedSrcModule (m : Name) : Bool :=
  (`ZeroParadox).isPrefixOf m && ! (`ZeroParadox.Vendored).isPrefixOf m

/-- De-mangle private names to their user-facing form (the registry stores the source name). -/
def deMangleName (n : Name) : Name :=
  (privateToUserName? n).getD n

def nameStr (n : Name) : String := toString (deMangleName n)

def namesToJson (arr : Array Name) : Json :=
  Json.arr (arr.map (fun c => Json.str (nameStr c)))

run_cmd do
  -- Dev tool: reads/writes the gitignored `.claude-local/`. Skip on any clean checkout
  -- (CI, fresh clone) where that dir is absent, so the catch-all lake glob can build this
  -- module without doing (or failing) build-time IO. Runs normally where the dir exists.
  unless (← System.FilePath.pathExists ".claude-local/translation_matrix") do return
  let env ← getEnv
  let mut recs : Array Json := #[]
  for (name, ci) in env.constants.toList do
    match env.getModuleFor? name with
    | some m =>
      if isTrackedSrcModule m then
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
