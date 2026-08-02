# ZeroParadox Lean sources - manifest

This folder holds the Lean 4 formalization for the Zero Paradox framework. It contains two kinds of file,
and this manifest says which is which so a reader knows what to read. Files in the **experimental** class
also carry a one-line `-- EXPERIMENTAL (branch scaffolding)` header at the top.

This material grew out of a broader exploratory arc that is kept privately; only the rigorous, review-cleared
Lean is surfaced here. The speculative interpretation behind it is deliberately not part of this repository.

The single best entry point is **`BottomCannotBe.lean`**: a machine-checked (`#check`-only) index that
gathers the established results about the framework's bottom element across every layer and organizes them
by a classification schema. Within this repository the shorthand for it is "Bottom-Meta". It declares
nothing of its own and only `#check`s already-proved results, so building it recompiles every result it
cites; it is a curated map of what is established, not a source of new claims.

**On the central claim (read this first).** The organizing thesis is that the bottom element recurs in the
same structural role across several domains. What is **proved** is the *membership* and the *recurrence of
the slot structure*. What is **not** proved, and is stated only as a conjecture/program, is that the various
bottoms are *one object*: they are provably distinct as structures (the "walls" results in the campaign).
The index above is where the precise line between proved and conjectural is kept.

## Core (finalized results - read these)

The framework's reviewed, load-bearing Lean, organized by domain folder. The formal layers ZP-A through ZP-P live here; `BottomCannotBe.lean` (Bottom-Meta) is the curated index over them.

### Order / lattice (ZP-A, ZP-E)

- `ZeroParadox/Order/Lattice.lean` - ZP-A: Lattice Algebra
- `ZeroParadox/Order/LeastFixedPoint.lean` - The μ abstraction: least fixed point reached from a seed (the ceiling analogue of `AbstractSelfApp`)
- `ZeroParadox/Order/PerronCapstone.lean` - Capstone: Perron–Frobenius for finite stochastic operators
- `ZeroParadox/Order/PowerSet.lean` - ZP-H Extension: Power Set Lattice as Structural Floor Witness
- `ZeroParadox/Order/Snap.lean` - ZP-E: Bridge Document
- `ZeroParadox/Order/SnapCannotBe.lean` - Machine-checked characterization index of the snap ⊥ → ε₀ — what the snap IS and IS NOT

### Valuation / number theory (ZP-B, ZP-F)

- `ZeroParadox/Valuation/AdeleGlobal.lean` - ZP-H Direction A, Cycle A4 (depth b) — the adele ring as the global object for ℚ's places (assembly)
- `ZeroParadox/Valuation/ArchPlace.lean` - ZP-H Direction A, Cycle A1 — #2 (Markov) is the archimedean place; #3 (p-adic) is the 2-adic place
- `ZeroParadox/Valuation/FloorWitness.lean` - Floor-class witnesses: valuation = ⊤ at the bottom (P7)
- `ZeroParadox/Valuation/InvTowerNorm.lean` - Batch 2 / G3 (pipeline, T6): the 0↔∞ duality on the 2-adic NORM (metric side of the flip)
- `ZeroParadox/Valuation/InversionValuation.lean` - An elementary fact: 2-adic inversion reverses the valuation filtration
- `ZeroParadox/Valuation/Ostrowski.lean` - ZP-P instance: the number-system fork (ℝ vs ℚ_p), via Ostrowski
- `ZeroParadox/Valuation/Padic.lean` - ZP-B: p-Adic Topology
- `ZeroParadox/Valuation/PadicPerfect.lean` - M11 (re-attempt): the 2-adic ball is perfect — Cantor–Bendixson rank 0
- `ZeroParadox/Valuation/PadicTree.lean` - A rooted 2-adic tree as a `SimpleGraph`
- `ZeroParadox/Valuation/PlaceAllPrimes.lean` - ZP-H Direction A, Cycle A5 (depth c) — the framework's OWN bottom family = all places of ℚ
- `ZeroParadox/Valuation/PlaceForcing.lean` - ZP-H Direction A, Cycle A2 — the archimedean place is the product-formula balancer
- `ZeroParadox/Valuation/PlaceMetric.lean` - ZP-H Direction A, Cycle A3 — the place is load-bearing in the DYNAMICS: ⊥ as a place-relative limit
- `ZeroParadox/Valuation/PoleChartSelection.lean` - Chart selection at the pole: free on the built sphere, choice-forcing only under an added commitment
- `ZeroParadox/Valuation/PricedPadicInterface.lean` - A priced p-adic interface: a choice-free carrier for ZP-B/ZP-J Group A, a map into `ℤ_[2]`, and both sides' axiom footprints
- `ZeroParadox/Valuation/RiemannSphere.lean` - The p-adic Riemann sphere: inversion swaps the floor 0 and its antipode ∞
- `ZeroParadox/Valuation/Scale.lean` - ZPJ — Valuation Bridge: Deriving AFA Content from Scale Structure
- `ZeroParadox/Valuation/ScaleBridge.lean` - ZPJ — Scale Bridge: AFA Content from Valuation Without ZPSemilattice
- `ZeroParadox/Valuation/SemilatticeInstance.lean` - ZP-I: Inside Zero
- `ZeroParadox/Valuation/SnapDichotomy.lean` - ZPF — the snap-occurrence dichotomy over ℚ
- `ZeroParadox/Valuation/TopFunctor.lean` - ZP-H Top Functor: F_B into the real category `TopCat` (MC-1 remediation)
- `ZeroParadox/Valuation/ValuationAFA.lean` - P10: AFA self-containment derived from a bottom-valuation (the theorem-anchor)
- `ZeroParadox/Valuation/ValuationAFA_Padic.lean` - P10 concrete: the bottom-valuation axioms are THEOREMS for the 2-adic numbers

### Information (ZP-C)

- `ZeroParadox/Information/BottomMeasure.lean` - P6: measure = +∞ at the bottom — per-domain bundle, and the type-boundary finding
- `ZeroParadox/Information/PadicSurprisal.lean` - B3 (pipeline): information surprisal ≡ 2-adic depth at the floor
- `ZeroParadox/Information/Surprisal.lean` - ZP-C: Information Theory

### State / Hilbert (ZP-D)

- `ZeroParadox/State/HilbFunctor.lean` - ZP-H Hilbert Functor: F_D into the real category `ModuleCat ℂ` (MC-1 remediation)
- `ZeroParadox/State/MeanErgodic.lean` - Mean ergodic convergence for doubly-stochastic kernels (STRETCH)
- `ZeroParadox/State/ReversibleSpectrum.lean` - Reversible chains have real spectrum (genuine Hilbert / self-adjoint content)
- `ZeroParadox/State/StateSpace.lean` - ZP-D: State Layer (Hilbert Space)

### Reals (counterexamples)

- `ZeroParadox/Reals/MarkovSpectralGap.lean` - ZP-H: Spectral-gap irreversibility of the Markov transfer operator (the #2 DYN witness)
- `ZeroParadox/Reals/OrderedField.lean` - ZP-F: The Real Numbers as Counterexample
- `ZeroParadox/Reals/PerronFrobenius.lean` - Perron–Frobenius: existence of a stationary distribution (the first NON-thin dictionary entry)
- `ZeroParadox/Reals/SpectralRadius.lean` - Spectral side: the transfer operator is ℓ¹-nonexpansive, so every eigenvalue has |λ| ≤ 1

### Category theory (ZP-G, ZP-H)

- `ZeroParadox/Category/AxG2Reduce.lean` - B4 (pipeline): AX-G2 is derivable from strict-initiality (a ZP-G posit collapses)
- `ZeroParadox/Category/BottomUndecidable.lean` - Where the keystone's classical cost sits: unresolved identity, and NOT self-containment
- `ZeroParadox/Category/Category.lean` - ZP-G: Category Theory
- `ZeroParadox/Category/ChoiceCannotBe.lean` - Machine-checked characterization index of the framework's relationship to `Classical.choice`
- `ZeroParadox/Category/DiagonalWitness.lean` - The minimum requirements to be a diagonal fixed point — the relativized Lawvere witness
- `ZeroParadox/Category/DifferenceGeneratesSystem.lean` - Nuclei and sublocales — the home of "a predicated difference generates a system"
- `ZeroParadox/Category/DoubleNegationNucleus.lean` - The double-negation nucleus: the excluded-middle modality
- `ZeroParadox/Category/ExcludedMiddleBridge.lean` - The excluded-middle bridge: choice → excluded middle → the `Prop` nucleus is trivial
- `ZeroParadox/Category/Lawvere.lean` - ZPJ — The Lawvere bridge (keystone Tier-6 upgrade probe)
- `ZeroParadox/Category/LawvereDecidable.lean` - Lawvere's engine, priced: the same theorems over decidable equality
- `ZeroParadox/Category/LawvereTaboo.lean` - The diagonal engine's supplier is a constructive taboo

### Multi-homed bridges (ZP-H)

- `ZeroParadox/Multihomed/Boundary.lean` - ZPJ — The well-foundedness boundary (keystone snap-as-boundary probe)
- `ZeroParadox/Multihomed/BoundaryBridge.lean` - ZPJ — The snap-boundary, QPF bridge (best-effort; Rung C-QPF)
- `ZeroParadox/Multihomed/CategoricalBridge.lean` - ZP-H: Categorical Bridge
- `ZeroParadox/Multihomed/EigenvectorExists.lean` - Deep cross-domain entry: the transfer operator has a unit eigenvector (existence ⟹ existence)
- `ZeroParadox/Multihomed/HilbertDiagonal.lean` - ZP-H: ⊥ is the unique finite-dimensional fixed point of the biproduct-diagonal
- `ZeroParadox/Multihomed/InfoFunctor.lean` - ZP-H Info Functor: F_C into the real category `KleisliCat PMF` (MC-1 remediation)
- `ZeroParadox/Multihomed/MC1Bridge.lean` - ZP-H MC-1 Correspondence: the snap floor realized across the real domain categories
- `ZeroParadox/Multihomed/PadicBridge.lean` - B2 (pipeline): the computational bottom maps to the 2-adic floor
- `ZeroParadox/Multihomed/SelfClosureObstruction.lean` - Self-Closure Obstructions: the wall-side mirror of the diagonal fixed point (experimental probe)
- `ZeroParadox/Multihomed/SeparatedSuccession.lean` - The type bridge: a separated succession as an interface, with two known implementations
- `ZeroParadox/Multihomed/TopNumEdge.lean` - Web edge: topology ↔ number theory (the valuation generates the ball topology)

### Set theory / AFA (ZP-J)

- `ZeroParadox/Settheory/APG.lean` - ZPJ — Accessible Pointed Graphs and AFA Decoration Uniqueness
- `ZeroParadox/Settheory/AczelConn.lean` - ZPJ — Aczel Fixed Point Connection
- `ZeroParadox/Settheory/Coalgebra.lean` - ZP-P instance: the categorical parent (initial algebra vs final coalgebra)
- `ZeroParadox/Settheory/Curry.lean` - Curry's paradox — the diagonal family's EXPLOSION face (probe)
- `ZeroParadox/Settheory/FixedPointFork.lean` - ZP-P: The Fixed-Point Fork
- `ZeroParadox/Settheory/Loeb.lean` - Löb's theorem — the diagonal family's PROVABILITY-modal face (probe, from scratch)
- `ZeroParadox/Settheory/Model.lean` - ZPJ — Concrete ValuationStructure Instance: (ℕ∞, min, ⊤)
- `ZeroParadox/Settheory/OntBridge.lean` - ZPJ — OntologicalStates → AbstractSelfApp → AFA Content
- `ZeroParadox/Settheory/QuineDichotomy.lean` - ZPJ — the Quine-atom dichotomy
- `ZeroParadox/Settheory/QuineHost.lean` - The Quine-Host Requirements — the AFA fragment the framework actually needs
- `ZeroParadox/Settheory/SetTheoryAFA.lean` - ZP-J: Executability of Self-Reference
- `ZeroParadox/Settheory/Tarski.lean` - Tarski's undefinability of truth — the diagonal family's TRUTH face (probe)
- `ZeroParadox/Settheory/Wall.lean` - Zero as a Wall — the metatheoretic boundary, as a failure-mode taxonomy (formal object)
- `ZeroParadox/Settheory/Wall_OneRoot.lean` - Two small facts: self-loops exist without well-foundedness; the Lawvere lemma needs no order

### Computability (ZP-K, ZP-J)

- `ZeroParadox/Computability/ComputationCannotBe.lean` - Machine-checked characterization index of COMPUTATION — what it can and cannot be
- `ZeroParadox/Computability/GroundZero.lean` - Ground zero — the bottom as a behaviour, not a configuration
- `ZeroParadox/Computability/Kleene.lean` - ZP-K: Computational Grounding of Self-Reference
- `ZeroParadox/Computability/Occurrence.lean` - Occurrence — what it takes for the bottom to move, in the computational face
- `ZeroParadox/Computability/Periodicity.lean` - ZP-K metric: the selfApply periodicity invariant (P5)
- `ZeroParadox/Computability/Rice.lean` - Rice's theorem — the computability face's UNDECIDABILITY, from the recursion theorem (probe)
- `ZeroParadox/Computability/SelfApp.lean` - ZPJ — Abstract Self-Application Bridge

### Ordinals / proof theory (ZP-L, ZP-M, ZP-N)

- `ZeroParadox/Ordinal/B6_CanonicalCNF.lean` - B6 (pipeline): canonical (CNF / log-ω) ordinal → 2-adic, valuation growth NOT tower-defined
- `ZeroParadox/Ordinal/CnfBridge.lean` - The CNF/ℤ₂ value bridge, at the construction level (Gentzen.lean item 4)
- `ZeroParadox/Ordinal/ConstructiveOrdinals.lean` - ZP-N: the ε₀ snap, constructively, on ordinal notations (choice-free)
- `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` - Machine-checked characterization index of ε₀ — what ε₀ IS and what it IS NOT
- `ZeroParadox/Ordinal/Epsilon0LeastFP.lean` - Batch 2 / G1 (pipeline, T6): ε₀ is the LEAST fixed point of α ↦ ωᵅ — the snap sits at minimal closure
- `ZeroParadox/Ordinal/Epsilon0MinMax.lean` - ε₀ is min ≡ max: the snap ⊥ → ε₀ is one Kleene chain (seed → closure)
- `ZeroParadox/Ordinal/Gentzen.lean` - ZP-L: Incomputability Convergence
- `ZeroParadox/Ordinal/Goodstein.lean` - Goodstein's theorem (full, hereditary base) — ε₀ ordinal descent
- `ZeroParadox/Ordinal/Incompleteness.lean` - ZP-M: Kleene–Ordinal Bridge Layer
- `ZeroParadox/Ordinal/KirbyParis.lean` - Kirby–Paris hydra termination (the ε₀ gap) — proved
- `ZeroParadox/Ordinal/Kruskal.lean` - Kruskal's Tree Theorem (labeled) — finite rose trees are well-quasi-ordered
- `ZeroParadox/Ordinal/NaturalOpsPow.lean` - Natural sum on powers of ω — the deferred CNF characterization (ported)
- `ZeroParadox/Ordinal/OrdinalChoiceEssential.lean` - Comparability of well-orders is a constructive taboo
- `ZeroParadox/Ordinal/P8.lean` - P8 re-attempt: ε₀ → 0 in ℤ₂ via a tower-rank 2-adic encoding
- `ZeroParadox/Ordinal/PricedInterface.lean` - A priced interface: a carrier sized to ε₀, a map into `Ordinal`, and both sides' axiom footprints
- `ZeroParadox/Ordinal/SnapMetaLattice.lean` - The lattice of systems: adjoining the point at infinity makes the ordinals a frame
- `ZeroParadox/Ordinal/SnapNucleus.lean` - The snap is a nucleus: ε₀ is the modality generated from the bottom ⊥
- `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` - No snap-shaped closure on the `ONote` carrier: a proved obstruction
- `ZeroParadox/Ordinal/SnapSuccession.lean` - The succession as a chain: the ε-numbers are the snap's successive targets, strictly climbing
- `ZeroParadox/Ordinal/SyntacticCollapse.lean` - Syntactic surrogate for the 2-adic metric collapse (choice-free)
- `ZeroParadox/Ordinal/WeakGoodstein.lean` - Weak Goodstein termination (second-domain depth test: ordinals / proof theory)

### Algebra / wheel (ZP-J)

- `ZeroParadox/Algebra/Wheel.lean` - ZPJ — Wheel Theory Formalization: /0 as a First-Class Element
- `ZeroParadox/Algebra/WheelFrac.lean` - The Wheel of Fractions `⊙_S A` (Carlström 2001:11, pp. 4-5, 10)

### Root

- `ZeroParadox/AxiomProfile.lean` - Axiom Profile — the choice-free core of the Zero Paradox
- `ZeroParadox/BottomCannotBe.lean` - Machine-checked verification index of results characterizing ⊥ (the bottom element)
- `ZeroParadox/ClaimsMirror.lean` - ZP Claims Mirror — the machine-checked representation of the claim graph
- `ZeroParadox/DiagonalFixedPoint.lean` - Machine-checked characterization index of self-reference — the diagonal fixed point
- `ZeroParadox/Miniature.lean` - The Zero Paradox in miniature — the minimal core

### Meta / tooling (not framework content)

- `ZeroParadox/Meta/ExtractDeps.lean` - Declaration-level dependency extractor (interop Issue 13, ZP side)
- `ZeroParadox/Meta/Snapshot.lean` - Golden-master snapshot for refactor verification (content-preservation harness)

### Vendored external code (Mathlib / CGT)

- `ZeroParadox/Vendored/NaturalOps.lean` - Natural operations on ordinals

## Experimental (branch scaffolding - the lab notebook)

These carry the `-- EXPERIMENTAL` header: the exploratory work the core results were distilled from, kept for transparency. The load-bearing results among them are cited by `BottomCannotBe.lean`; the rest are probes, dead ends, and honest negatives.

### Order / lattice (ZP-A, ZP-E)

- `ZeroParadox/Order/MarkovContractionDual.lean` - The dual contraction dichotomy on the Markov ν-side (#2)
- `ZeroParadox/Order/MarkovPlacement.lean` - The unplaced node: does the Markov attractor (#2) admit ANY order-extremal or categorical placement?
- `ZeroParadox/Order/OrbitDichotomy.lean` - The orbit dichotomy — "one or infinitely many", no finite middle (probe)
- `ZeroParadox/Order/PadicLimitCone.lean` - The p-adic floor `{0}` is a genuine categorical limit cone
- `ZeroParadox/Order/ProofFloorHomset.lean` - Axis III over the proof-theory floor #1 (the hom-set carrier convention)
- `ZeroParadox/Order/SeamSchema.lean` - A shared "seam schema" for the QPF root-seam and the lattice selfApp seam,
- `ZeroParadox/Order/WellFoundedObstruct.lean` - Well-foundedness obstructs the attractor character of the μ floor

### Valuation / number theory (ZP-B, ZP-F)

- `ZeroParadox/Valuation/AxisSweepProbe.lean` - Experimental probes: the fork is trivially satisfiable, and the pole vs chain / branching pairs
- `ZeroParadox/Valuation/BottomInvariant.lean` - A first universal: the bottom carries an invariant probability measure
- `ZeroParadox/Valuation/BoundaryGap.lean` - The boundary embedding: the exact gap to the Bruhat-Tits tree
- `ZeroParadox/Valuation/BranchingRequirement.lean` - A further requirement — the branching axis: branches are incomparable (the tower does not stack)
- `ZeroParadox/Valuation/BranchingSnapChain.lean` - The single chain: branching → disconnectedness → forbidden return → the snap
- `ZeroParadox/Valuation/CantorPropertiesProbe.lean` - Completeness-critic, final pass: homogeneity and ultrametric are derived; compactness is AX-B1
- `ZeroParadox/Valuation/CompletenessCriticProbe.lean` - Completeness-critic probe: what property of the generic object do the four axes NOT capture?
- `ZeroParadox/Valuation/ComplexityLadder.lean` - The complexity ladder: the arity is the variable-count, and it climbs without bound
- `ZeroParadox/Valuation/ContractionRate.lean` - The contraction-rate dichotomy at the p-adic floor #3
- `ZeroParadox/Valuation/ForkPoleProbe.lean` - Experimental probe: is the μ/ν fork independent of the pole?
- `ZeroParadox/Valuation/IndependenceProbe.lean` - Experimental probe: are the chain axis and the branching axis independent?
- `ZeroParadox/Valuation/InfinitudeFloor.lean` - The floor's infinite complexity AS an infinitude of zeros (research spike)
- `ZeroParadox/Valuation/IrreversibilityProbe.lean` - Experimental probe: is irreversibility (the snap direction) a fifth independent requirement?
- `ZeroParadox/Valuation/LocalFloor.lean` - Every node is a floor, literally: a genuine InfinitudeFloor at each node of the generic tree
- `ZeroParadox/Valuation/NuLeafReconcile.lean` - The within-ν edge reconciles at the LEAF, not the ambient
- `ZeroParadox/Valuation/NuRateEdge.lean` - The within-ν edge at the orbit-RATE level (#3 ↔ #2)
- `ZeroParadox/Valuation/NuRateMatch.lean` - Within-ν geometric-rate match: #2 (irreducible Markov) and #3 (p-adic) share rate 1/2
- `ZeroParadox/Valuation/PadicAttractor.lean` - The p-adic floor #3 as a dynamical attractor
- `ZeroParadox/Valuation/PadicBallIndicator.lean` - The p-adic ball indicator in L²(ℤ_p)
- `ZeroParadox/Valuation/PadicCharacter.lean` - p-adic additive characters and their orthogonality on ℤ_p
- `ZeroParadox/Valuation/PadicErgodic.lean` - Ergodicity of the p-adic odometer
- `ZeroParadox/Valuation/PadicHaar.lean` - p-adic Haar measure on ℤ_p
- `ZeroParadox/Valuation/PadicJointSpectrum.lean` - The joint spectrum: Koopman ⋈ Vladimirov share the character eigenbasis
- `ZeroParadox/Valuation/PadicKoopman.lean` - The Koopman operator on L²(ℤ_p)
- `ZeroParadox/Valuation/PadicKoopmanVladimirov.lean` - Koopman ⋈ Vladimirov: the odometer intertwines with D^α
- `ZeroParadox/Valuation/PadicKozyrev.lean` - A genuine eigenfunction of D^α: the level-1 p-adic character
- `ZeroParadox/Valuation/PadicStillPoint.lean` - The still-point: the trivial character is the joint fixed/annihilated bottom
- `ZeroParadox/Valuation/PadicVladimirov.lean` - The Taibleson–Vladimirov operator D^α on ℤ_p
- `ZeroParadox/Valuation/PolarityFlip.lean` - 2-adic inversion negates the valuation (a cited Mathlib fact + one tower corollary)
- `ZeroParadox/Valuation/PoleCompletion.lean` - The pole completion: the floor is a genuine self-application fixed point (the Quine atom on the tree)
- `ZeroParadox/Valuation/PoleCorners.lean` - The four corners: 0 and ∞ have exactly four representations to each other
- `ZeroParadox/Valuation/PoleCornersBridge.lean` - Bridge: the four corners are the corners of the tower to ω (shared-shape correspondence)
- `ZeroParadox/Valuation/RateTransport.lean` - within-Axis-I positive rate-transport via the shared geometric rate `2^(-n)`
- `ZeroParadox/Valuation/RootAsymmetry.lean` - Root-asymmetry test: #1 (μ order-floor) vs #3 (ν p-adic limit)
- `ZeroParadox/Valuation/StrippedBottom.lean` - ⊥ by inversion of attribute-classes — the "typecast" stand-in (Tim, 2026-06-30)
- `ZeroParadox/Valuation/TowerHeightFloor.lean` - Height meets floor: the ordinal tower IS an InfinitudeFloor, order-reversed — ε₀ ≠ ⊥ preserved

### State / Hilbert (ZP-D)

- `ZeroParadox/State/ProbeSeparates.lean` - `Fin 0` is empty; the zero ℂ-module on `Fin 0` is inhabited
- `ZeroParadox/State/ThreeCarrierLeaf.lean` - The THREE-carrier ν/seam leaf set is one-point (adds #5 Hilbert to `ZeroParadox/Valuation/NuLeafReconcile.lean`'s #3/#2)

### Reals (counterexamples)

- `ZeroParadox/Reals/RateClassInvariant.lean` - Axis IV: convergence-rate class as a cross-root invariant

### Category theory (ZP-G, ZP-H)

- `ZeroParadox/Category/CardinalitySplit.lean` - Axis III generality: is the #4/#5 cardinality split canonical?
- `ZeroParadox/Category/CoalgebraForkPlace.lean` - The ZP-P W/M coalgebra fork places on the μ/ν root
- `ZeroParadox/Category/CrossCategoryArrow.lean` - A genuine CROSS-category arrow from the μ-bottom #4 to the seam #5
- `ZeroParadox/Category/CrossRootEdge.lean` - The cross-root edge #4 (Kleisli μ-initial/colimit) ↔ #3 (p-adic ν-limit)
- `ZeroParadox/Category/Directed.lean` - The Kleisli snap floor is not isomorphic to any object above it
- `ZeroParadox/Category/GlobalZero.lean` - A 3-field structure bundling three objects, plus three pre-existing universal-property witnesses
- `ZeroParadox/Category/Heterogeneous.lean` - F_D's bottom admits a (zero) morphism back; F_C's does not
- `ZeroParadox/Category/KleisliInitialColimit.lean` - The Kleisli μ-bottom's `IsInitial` is definitionally an empty-colimit witness (a remark)
- `ZeroParadox/Category/LinFunctor.lean` - Info → Hilbert: the linearization functor (a genuine inter-domain edge — full functoriality proved)
- `ZeroParadox/Category/Linearize.lean` - The free ℂ-module on the empty type is initial, hence isomorphic to the Hilbert bottom
- `ZeroParadox/Category/NoUniformCharacter.lean` - A conjunction of three already-proved facts about the three domain bottoms
- `ZeroParadox/Category/Node4Generation.lean` - ZP-H node #4 GENERATION — the floor `Fin 0` generates the ceiling `ℕ` by iteration (an Adámek instance)
- `ZeroParadox/Category/Obstruction.lean` - Two Finsupp facts (one ℂ-linearization stand-in pair, one opposite-category initiality)
- `ZeroParadox/Category/PointednessSharp.lean` - The pointedness dichotomy SHARPENED (the gap `ZeroParadox/Category/CardinalitySplit.lean` left open)
- `ZeroParadox/Category/RootCutBinary.lean` - The root cut is binary in arity, not graded
- `ZeroParadox/Category/RootCutDegeneracy.lean` - The root-cut degeneracy dichotomy
- `ZeroParadox/Category/SeamArrowLevel.lean` - Does the seam keystone hold AT THE ARROW LEVEL (μ-arrow = ν-arrow)?
- `ZeroParadox/Category/SeamArrowSignature.lean` - The seam's arrow-level signature (zero object vs bare-initial)
- `ZeroParadox/Category/SeamBiproductUnit.lean` - The seam #5 is the additive UNIT of the biproduct on `ModuleCat ℂ`
- `ZeroParadox/Category/SeamBridge.lean` - Is the seam a genuine BRIDGE between the subtrees, or a coincidentally two-sided object?
- `ZeroParadox/Category/SeamCoincidence.lean` - The seam IS the categorical μ=ν coincidence
- `ZeroParadox/Category/SeamComparisonMap.lean` - The canonical μ→ν comparison map at the root seam, and the honest
- `ZeroParadox/Category/SeamFrameChange.lean` - The frame-change in the category frame: `op`-duality swaps initial ↔ terminal at the seam
- `ZeroParadox/Category/SeamGeneric.lean` - The seam as a GENERIC theorem (the μ=ν coincidence is a real categorical fact)
- `ZeroParadox/Category/SeamLimColim.lean` - The seam diagram-level coincidence (lim = colim at the zero object)
- `ZeroParadox/Category/SeamNotColimit.lean` - The seam is NOT a colimit (coproduct) apex over the μ-bottoms
- `ZeroParadox/Category/SeamUniqueness.lean` - Seam uniqueness extended: is any OTHER bottom a zero object?
- `ZeroParadox/Category/TopNoGo.lean` - In TopCat the empty space is not isomorphic to the one-point space
- `ZeroParadox/Category/TreeSeam.lean` - ZP-H tree — the #5 straddle resolved: the Hilbert bottom is the μ=ν seam

### Multi-homed bridges (ZP-H)

- `ZeroParadox/Multihomed/CrossRootCompleteness.lean` - #1↔#3 and #5↔#3
- `ZeroParadox/Multihomed/FloorFactsCooccur.lean` - Co-occurrence of four ambient bottom-facts (thin: new fact is generic)
- `ZeroParadox/Multihomed/Fork.lean` - Restating two `IsInitial` and one `IsTerminal` witness as `IsColimit` / `IsLimit`
- `ZeroParadox/Multihomed/RootCutObstruction.lean` - The ROOT cut is a strict, non-glueable μ/ν obstruction
- `ZeroParadox/Multihomed/SeamConnectorFail.lean` - The seam #5 fails as a two-sided connector to the ν-LIMIT node #3
- `ZeroParadox/Multihomed/SelfAppForkPlace.lean` - ZP-H tree, theory TH11 — placing the ZP-J selfApp fixed point on the μ/ν fork
- `ZeroParadox/Multihomed/SelfAppSeam.lean` - The selfApp bottom sits at the μ=ν seam, not on either branch
- `ZeroParadox/Multihomed/SnapFrameChange.lean` - The tower limit's two chart-readings: ⊥ and ∞ are two charts, swapped by `rInv`
- `ZeroParadox/Multihomed/SpanObstruction.lean` - The #1↔#3 cross-root obstruction under a SPAN (THIN-BUT-HONEST)
- `ZeroParadox/Multihomed/TreeObstructions.lean` - ZP-H: The bottom-diagram tree — machine-checked obstruction core (E4 + SPLIT, rebuilt)
- `ZeroParadox/Multihomed/TreeT1.lean` - ZP-H tree, edge T1 — the within-μ edge: proof-theory floor ↔ categorical-initial bottoms
- `ZeroParadox/Multihomed/TreeT2.lean` - ZP-H tree, edge T2 — the within-ν edge: Markov attractor ↔ p-adic inverse-limit
- `ZeroParadox/Multihomed/TwoFacesBot.lean` - Direction B — the two faces of ⊥ at the seam: VACUOUS (they coincide, but only as a bare singleton)
- `ZeroParadox/Multihomed/WallSpanRobust.lean` - Span-robustness of the well-founded cross-root wall (#1 vs #2)

### Set theory / AFA (ZP-J)

- `ZeroParadox/Settheory/ForkFrameChange.lean` - The order-theoretic universal frame-change: duality swaps the fork's ends
- `ZeroParadox/Settheory/LawvereBridge.lean` - The Lawvere dereference — selfApp as an instance of the general engine (probe)
- `ZeroParadox/Settheory/MetaFork.lean` - The meta-level fork — the double dereference (probe)
- `ZeroParadox/Settheory/RequirementsGap.lean` - The instance-vs-requirements gap as a fork instance (probe)

### Computability (ZP-K, ZP-J)

- `ZeroParadox/Computability/ChoicePurityInvariant.lean` - Is choice-purity an IN-STATEMENT μ/ν separating invariant?
- `ZeroParadox/Computability/CodeDataFrameChange.lean` - The frame-change in the computability frame: the code↔data involution and the quine on its fixed locus
- `ZeroParadox/Computability/ComputableCrossing.lean` - The Lawvere bridge, crossed in the computability face (probe)
- `ZeroParadox/Computability/MarkovNuUniversal.lean` - Does the Markov node (#2) get a ν (terminal/unique-fixed-point) universal property?
- `ZeroParadox/Computability/NatListRegime.lean` - The third root-cut regime: the nat/list functor (leaf + recursive position)
- `ZeroParadox/Computability/OutputSeparates.lean` - The head decides, the arity does not: two instances of Rutten's final-system formula
- `ZeroParadox/Computability/RootCutTrichotomy.lean` - The root cut is a TRICHOTOMY (leaf × recursive position)
- `ZeroParadox/Computability/StationaryUnique.lean` - Irreducibility forces a unique stationary distribution for node #2

### Ordinals / proof theory (ZP-L, ZP-M, ZP-N)

- `ZeroParadox/Ordinal/ProofFloorCanonical.lean` - Is the proof-theory bottom canonical across the depth campaign?

---

*Generated by `build_manifest.py` from the Lean tree + each file's `-- EXPERIMENTAL` header. Rerun after adding, moving, or renaming a file. (113 core, 102 experimental.)*
