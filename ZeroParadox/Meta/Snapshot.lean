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
# Golden-master snapshot for refactor verification (content-preservation harness)

For every tracked declaration, records a structural fingerprint of its TYPE (`Expr.hash`)
and its transitive AXIOM profile. Diffing two snapshots (before/after a refactor cut) proves
content preservation: a decl whose type-hash changed had its STATEMENT altered; a decl whose
axiom set changed had a purity regression. A pure move/rename leaves both identical.

NOT imported by Basic (normal builds skip it). Run:  lake build ZeroParadox.Meta.Snapshot
Out: .claude-local/translation_matrix/golden_master.json
-/

open Lean

namespace ZeroParadox.Meta

def isTrackedModule (m : Name) : Bool :=
  (`ZeroParadox).isPrefixOf m && ! (`ZeroParadox.Vendored).isPrefixOf m
def userName (n : Name) : Name := (privateToUserName? n).getD n

run_cmd do
  -- Dev tool: writes into the gitignored `.claude-local/`. Skip on any clean checkout
  -- (CI, fresh clone) where that dir is absent, so the catch-all lake glob can build this
  -- module without doing (or failing) build-time IO. Runs normally where the dir exists.
  unless (← System.FilePath.pathExists ".claude-local/translation_matrix") do return
  let env ← getEnv
  let mut recs : Array Json := #[]
  for (name, ci) in env.constants.toList do
    match env.getModuleFor? name with
    | some m =>
      if isTrackedModule m then
        let axs ← Lean.collectAxioms name
        let axl := (axs.qsort (fun a b => toString a < toString b)).map (fun a => Json.str (toString a))
        recs := recs.push <| Json.mkObj [
          ("q", Json.str (toString (userName name))),
          ("th", Json.str (toString ci.type.hash)),
          ("ax", Json.arr axl)
        ]
    | none => pure ()
  IO.FS.writeFile ".claude-local/translation_matrix/golden_master.json" (Json.arr recs).compress
  logInfo s!"[Snapshot] wrote golden_master.json -- {recs.size} decls"

end ZeroParadox.Meta
