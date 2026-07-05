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
