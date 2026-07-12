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
- `ZeroParadox/Order/PerronCapstone.lean` - Capstone: Perron–Frobenius for finite stochastic operators
- `ZeroParadox/Order/PowerSet.lean` - ZP-H Extension: Power Set Lattice as Structural Floor Witness
- `ZeroParadox/Order/Snap.lean` - ZP-E: Bridge Document

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
- `ZeroParadox/State/MeanErgodic.lean` - Mean ergodic convergence for doubly-stochastic kernels (STRETCH; stub-first)
- `ZeroParadox/State/ReversibleSpectrum.lean` - Reversible chains have real spectrum (genuine Hilbert / self-adjoint content)
- `ZeroParadox/State/StateSpace.lean` - ZP-D: State Layer (Hilbert Space)

### Reals (counterexamples)

- `ZeroParadox/Reals/MarkovSpectralGap.lean` - ZP-H: Spectral-gap irreversibility of the Markov transfer operator (the #2 DYN witness)
- `ZeroParadox/Reals/OrderedField.lean` - ZP-F: The Real Numbers as Counterexample
- `ZeroParadox/Reals/PerronFrobenius.lean` - Perron–Frobenius: existence of a stationary distribution (the first NON-thin dictionary entry)
- `ZeroParadox/Reals/SpectralRadius.lean` - Spectral side: the transfer operator is ℓ¹-nonexpansive, so every eigenvalue has |λ| ≤ 1

### Category theory (ZP-G, ZP-H)

- `ZeroParadox/Category/AxG2Reduce.lean` - B4 (pipeline): AX-G2 is derivable from strict-initiality (a ZP-G posit collapses)
- `ZeroParadox/Category/Category.lean` - ZP-G: Category Theory
- `ZeroParadox/Category/Lawvere.lean` - ZPJ — The Lawvere bridge (keystone Tier-6 upgrade probe)

### Multi-homed bridges (ZP-H)

- `ZeroParadox/Multihomed/Boundary.lean` - ZPJ — The well-foundedness boundary (keystone snap-as-boundary probe)
- `ZeroParadox/Multihomed/BoundaryBridge.lean` - ZPJ — The snap-boundary, QPF bridge (best-effort; Rung C-QPF)
- `ZeroParadox/Multihomed/CategoricalBridge.lean` - ZP-H: Categorical Bridge
- `ZeroParadox/Multihomed/EigenvectorExists.lean` - Deep cross-domain entry: the transfer operator has a unit eigenvector (existence ⟹ existence)
- `ZeroParadox/Multihomed/HilbertDiagonal.lean` - ZP-H: ⊥ is the unique finite-dimensional fixed point of the biproduct-diagonal
- `ZeroParadox/Multihomed/InfoFunctor.lean` - ZP-H Info Functor: F_C into the real category `KleisliCat PMF` (MC-1 remediation)
- `ZeroParadox/Multihomed/MC1Bridge.lean` - ZP-H MC-1 Correspondence: the snap floor realized across the real domain categories
- `ZeroParadox/Multihomed/PadicBridge.lean` - B2 (pipeline): the computational bottom maps to the 2-adic floor
- `ZeroParadox/Multihomed/TopNumEdge.lean` - Web edge: topology ↔ number theory (the valuation generates the ball topology)

### Set theory / AFA (ZP-J)

- `ZeroParadox/Settheory/APG.lean` - ZPJ — Accessible Pointed Graphs and AFA Decoration Uniqueness
- `ZeroParadox/Settheory/AczelConn.lean` - ZPJ — Aczel Fixed Point Connection
- `ZeroParadox/Settheory/Coalgebra.lean` - ZP-P instance: the categorical parent (initial algebra vs final coalgebra)
- `ZeroParadox/Settheory/FixedPointFork.lean` - ZP-P: The Fixed-Point Fork
- `ZeroParadox/Settheory/Model.lean` - ZPJ — Concrete ValuationStructure Instance: (ℕ∞, min, ⊤)
- `ZeroParadox/Settheory/OntBridge.lean` - ZPJ — OntologicalStates → AbstractSelfApp → AFA Content
- `ZeroParadox/Settheory/QuineDichotomy.lean` - ZPJ — the Quine-atom dichotomy
- `ZeroParadox/Settheory/SetTheoryAFA.lean` - ZP-J: Executability of Self-Reference
- `ZeroParadox/Settheory/Wall.lean` - Zero as a Wall — the metatheoretic boundary, as a failure-mode taxonomy (formal object)
- `ZeroParadox/Settheory/Wall_OneRoot.lean` - Two small facts: self-loops exist without well-foundedness; the Lawvere lemma needs no order

### Computability (ZP-K, ZP-J)

- `ZeroParadox/Computability/Kleene.lean` - ZP-K: Computational Grounding of Self-Reference
- `ZeroParadox/Computability/Periodicity.lean` - ZP-K metric: the selfApply periodicity invariant (P5)
- `ZeroParadox/Computability/SelfApp.lean` - ZPJ — Abstract Self-Application Bridge

### Ordinals / proof theory (ZP-L, ZP-M, ZP-N)

- `ZeroParadox/Ordinal/B6_CanonicalCNF.lean` - B6 (pipeline): canonical (CNF / log-ω) ordinal → 2-adic, valuation growth NOT tower-defined
- `ZeroParadox/Ordinal/ConstructiveOrdinals.lean` - ZP-N: the ε₀ snap, constructively, on ordinal notations (choice-free)
- `ZeroParadox/Ordinal/Epsilon0LeastFP.lean` - Batch 2 / G1 (pipeline, T6): ε₀ is the LEAST fixed point of α ↦ ωᵅ — the snap sits at minimal closure
- `ZeroParadox/Ordinal/Gentzen.lean` - ZP-L: Incomputability Convergence
- `ZeroParadox/Ordinal/Goodstein.lean` - Goodstein's theorem (full, hereditary base) — ε₀ ordinal descent
- `ZeroParadox/Ordinal/Incompleteness.lean` - ZP-M: Kleene–Ordinal Bridge Layer
- `ZeroParadox/Ordinal/KirbyParis.lean` - Kirby–Paris hydra termination (the ε₀ gap) — proved
- `ZeroParadox/Ordinal/Kruskal.lean` - Kruskal's Tree Theorem (labeled) — finite rose trees are well-quasi-ordered
- `ZeroParadox/Ordinal/NaturalOpsPow.lean` - Natural sum on powers of ω — the deferred CNF characterization (ported)
- `ZeroParadox/Ordinal/P8.lean` - P8 re-attempt: ε₀ → 0 in ℤ₂ via a tower-rank 2-adic encoding
- `ZeroParadox/Ordinal/WeakGoodstein.lean` - Weak Goodstein termination (second-domain depth test: ordinals / proof theory)

### Algebra / wheel (ZP-J)

- `ZeroParadox/Algebra/Wheel.lean` - ZPJ — Wheel Theory Formalization: /0 as a First-Class Element
- `ZeroParadox/Algebra/WheelFrac.lean` - The Wheel of Fractions `⊙_S A` (Carlström 2001:11, pp. 4-5, 10)

### Root

- `ZeroParadox/AxiomProfile.lean` - Axiom Profile — the choice-free core of the Zero Paradox
- `ZeroParadox/BottomCannotBe.lean` - Machine-checked verification index of results characterizing ⊥ (the bottom element)

### Meta / tooling (not framework content)

- `ZeroParadox/Meta/ExtractDeps.lean` - Declaration-level dependency extractor (interop Issue 13, ZP side)
- `ZeroParadox/Meta/Snapshot.lean` - Golden-master snapshot for refactor verification (content-preservation harness)

### Vendored external code (Mathlib / CGT)

- `ZeroParadox/Vendored/NaturalOps.lean` - Natural operations on ordinals

## Experimental (branch scaffolding - the lab notebook)

These carry the `-- EXPERIMENTAL` header: the exploratory work the core results were distilled from, kept for transparency. The load-bearing results among them are cited by `BottomCannotBe.lean`; the rest are probes, dead ends, and honest negatives.

### Order / lattice (ZP-A, ZP-E)

- `ZeroParadox/Order/MarkovContractionDual.lean` - ZP-H tree, edge TC39 — the dual contraction dichotomy on the Markov ν-side (#2)
- `ZeroParadox/Order/MarkovPlacement.lean` - ZP-H tree, TC16 / TC13 — the unplaced node: does the Markov attractor (#2) admit ANY order-extremal or categorical placement?
- `ZeroParadox/Order/PadicLimitCone.lean` - ZP-H MC-1 TC10: the p-adic floor `{0}` is a genuine categorical limit cone
- `ZeroParadox/Order/ProofFloorHomset.lean` - ZP-H tree, TC43 — Axis III over the proof-theory floor #1 (the hom-set carrier convention)
- `ZeroParadox/Order/SeamSchema.lean` - ZP-H MC-1 tree test TC42: a shared "seam schema" for the QPF root-seam and the lattice selfApp seam,
- `ZeroParadox/Order/WellFoundedObstruct.lean` - ZP-H tree, edge TC28 — well-foundedness obstructs the attractor character of the μ floor

### Valuation / number theory (ZP-B, ZP-F)

- `ZeroParadox/Valuation/ContractionRate.lean` - ZP-H tree, edge TC30 — the contraction-rate dichotomy at the p-adic floor #3
- `ZeroParadox/Valuation/NuLeafReconcile.lean` - ZP-H tree, edge TC16 — the within-ν edge reconciles at the LEAF, not the ambient
- `ZeroParadox/Valuation/NuRateEdge.lean` - ZP-H tree, edge TC33 — the within-ν edge at the orbit-RATE level (#3 ↔ #2)
- `ZeroParadox/Valuation/NuRateMatch.lean` - ZP-H tree, TC43 — within-ν geometric-rate match: #2 (irreducible Markov) and #3 (p-adic) share rate 1/2
- `ZeroParadox/Valuation/PadicAttractor.lean` - ZP-H tree, edge TC05 — the p-adic floor #3 as a dynamical attractor
- `ZeroParadox/Valuation/PadicBallIndicator.lean` - The p-adic ball indicator in L²(ℤ_p)
- `ZeroParadox/Valuation/PadicCharacter.lean` - p-adic additive characters and their orthogonality on ℤ_p
- `ZeroParadox/Valuation/PadicHaar.lean` - p-adic Haar measure on ℤ_p
- `ZeroParadox/Valuation/PadicJointSpectrum.lean` - The joint spectrum: Koopman ⋈ Vladimirov share the character eigenbasis
- `ZeroParadox/Valuation/PadicKoopman.lean` - The Koopman operator on L²(ℤ_p)
- `ZeroParadox/Valuation/PadicKoopmanVladimirov.lean` - Koopman ⋈ Vladimirov: the odometer intertwines with D^α
- `ZeroParadox/Valuation/PadicKozyrev.lean` - A genuine eigenfunction of D^α: the level-1 p-adic character
- `ZeroParadox/Valuation/PadicStillPoint.lean` - The still-point: the trivial character is the joint fixed/annihilated bottom
- `ZeroParadox/Valuation/PadicVladimirov.lean` - The Taibleson–Vladimirov operator D^α on ℤ_p
- `ZeroParadox/Valuation/PolarityFlip.lean` - 2-adic inversion negates the valuation (a cited Mathlib fact + one tower corollary)
- `ZeroParadox/Valuation/RateTransport.lean` - ZP-H tree, TC34 — within-Axis-I positive rate-transport via the shared geometric rate `2^(-n)`
- `ZeroParadox/Valuation/RootAsymmetry.lean` - ZP-H tree, edge TC35 — root-asymmetry test: #1 (μ order-floor) vs #3 (ν p-adic limit)
- `ZeroParadox/Valuation/StrippedBottom.lean` - ⊥ by inversion of attribute-classes — the "typecast" stand-in (Tim, 2026-06-30)

### State / Hilbert (ZP-D)

- `ZeroParadox/State/ProbeSeparates.lean` - `Fin 0` is empty; the zero ℂ-module on `Fin 0` is inhabited
- `ZeroParadox/State/ThreeCarrierLeaf.lean` - ZP-H tree, TC29 — the THREE-carrier ν/seam leaf set is one-point (adds #5 Hilbert to TC19's #3/#2)

### Reals (counterexamples)

- `ZeroParadox/Reals/RateClassInvariant.lean` - ZP-H tree, TC41 — Axis IV: convergence-rate class as a cross-root invariant

### Category theory (ZP-G, ZP-H)

- `ZeroParadox/Category/CardinalitySplit.lean` - ZP-H tree, TC09 — Axis III generality: is the #4/#5 cardinality split canonical?
- `ZeroParadox/Category/CoalgebraForkPlace.lean` - ZP-H tree, TC06 — the ZP-P W/M coalgebra fork places on the μ/ν root
- `ZeroParadox/Category/CrossCategoryArrow.lean` - ZP-H tree — TC27: a genuine CROSS-category arrow from the μ-bottom #4 to the seam #5
- `ZeroParadox/Category/CrossRootEdge.lean` - ZP-H tree TC50 — the cross-root edge #4 (Kleisli μ-initial/colimit) ↔ #3 (p-adic ν-limit)
- `ZeroParadox/Category/Directed.lean` - The Kleisli snap floor is not isomorphic to any object above it
- `ZeroParadox/Category/GlobalZero.lean` - A 3-field structure bundling three objects, plus three pre-existing universal-property witnesses
- `ZeroParadox/Category/Heterogeneous.lean` - F_D's bottom admits a (zero) morphism back; F_C's does not
- `ZeroParadox/Category/KleisliInitialColimit.lean` - ZP-H TC24: the Kleisli μ-bottom's `IsInitial` is definitionally an empty-colimit witness (a remark)
- `ZeroParadox/Category/LinFunctor.lean` - Info → Hilbert: the linearization functor (a genuine inter-domain edge — full functoriality proved)
- `ZeroParadox/Category/Linearize.lean` - The free ℂ-module on the empty type is initial, hence isomorphic to the Hilbert bottom
- `ZeroParadox/Category/NoUniformCharacter.lean` - A conjunction of three already-proved facts about the three domain bottoms
- `ZeroParadox/Category/Node4Generation.lean` - ZP-H node #4 GENERATION — the floor `Fin 0` generates the ceiling `ℕ` by iteration (an Adámek instance)
- `ZeroParadox/Category/Obstruction.lean` - Two Finsupp facts (one ℂ-linearization stand-in pair, one opposite-category initiality)
- `ZeroParadox/Category/PointednessSharp.lean` - ZP-H tree, TC14 — the pointedness dichotomy SHARPENED (the gap TC09 left open)
- `ZeroParadox/Category/RootCutBinary.lean` - ZP-H MC-1 tree test TC32: the root cut is binary in arity, not graded
- `ZeroParadox/Category/RootCutDegeneracy.lean` - ZP-H MC-1 tree test TC26: the root-cut degeneracy dichotomy
- `ZeroParadox/Category/SeamArrowLevel.lean` - ZP-H tree, TC20 / TC17 — does the seam keystone hold AT THE ARROW LEVEL (μ-arrow = ν-arrow)?
- `ZeroParadox/Category/SeamArrowSignature.lean` - ZP-H tree — TC44: the seam's arrow-level signature (zero object vs bare-initial)
- `ZeroParadox/Category/SeamBiproductUnit.lean` - ZP-H tree — TC35: the seam #5 is the additive UNIT of the biproduct on `ModuleCat ℂ`
- `ZeroParadox/Category/SeamBridge.lean` - ZP-H tree TC18 — is the seam a genuine BRIDGE between the subtrees, or a coincidentally two-sided object?
- `ZeroParadox/Category/SeamCoincidence.lean` - ZP-H tree, keystone TC12 — the seam IS the categorical μ=ν coincidence
- `ZeroParadox/Category/SeamComparisonMap.lean` - ZP-H MC-1 tree test TC38: the canonical μ→ν comparison map at the root seam, and the honest
- `ZeroParadox/Category/SeamGeneric.lean` - ZP-H tree — TC13: the seam as a GENERIC theorem (the μ=ν coincidence is a real categorical fact)
- `ZeroParadox/Category/SeamLimColim.lean` - ZP-H tree TC25 — the seam diagram-level coincidence (lim = colim at the zero object)
- `ZeroParadox/Category/SeamNotColimit.lean` - ZP-H tree — TC38: the seam is NOT a colimit (coproduct) apex over the μ-bottoms
- `ZeroParadox/Category/SeamUniqueness.lean` - ZP-H tree TC-08 — seam uniqueness extended: is any OTHER bottom a zero object?
- `ZeroParadox/Category/TopNoGo.lean` - In TopCat the empty space is not isomorphic to the one-point space
- `ZeroParadox/Category/TreeSeam.lean` - ZP-H tree — the #5 straddle resolved: the Hilbert bottom is the μ=ν seam

### Multi-homed bridges (ZP-H)

- `ZeroParadox/Multihomed/CrossRootCompleteness.lean` - ZP-H tree, cross-root completeness — TC04: #1↔#3 and #5↔#3
- `ZeroParadox/Multihomed/FloorFactsCooccur.lean` - ZP-H tree, edge TC44 — co-occurrence of four ambient bottom-facts (thin: new fact is generic)
- `ZeroParadox/Multihomed/Fork.lean` - Restating two `IsInitial` and one `IsTerminal` witness as `IsColimit` / `IsLimit`
- `ZeroParadox/Multihomed/RootCutObstruction.lean` - ZP-H tree, TC18 (module TC21) — the ROOT cut is a strict, non-glueable μ/ν obstruction
- `ZeroParadox/Multihomed/SeamConnectorFail.lean` - ZP-H tree TC34 — the seam #5 fails as a two-sided connector to the ν-LIMIT node #3
- `ZeroParadox/Multihomed/SelfAppForkPlace.lean` - ZP-H tree, theory TH11 — placing the ZP-J selfApp fixed point on the μ/ν fork
- `ZeroParadox/Multihomed/SelfAppSeam.lean` - ZP-H tree — TC15: the selfApp bottom sits at the μ=ν seam, not on either branch
- `ZeroParadox/Multihomed/SnapFrameChange.lean` - The snap as a change of frame: ε₀-as-⊥ and ε₀-as-ceiling are two charts, swapped by `rInv`
- `ZeroParadox/Multihomed/SpanObstruction.lean` - ZP-H tree, TC17 / TC14 — the #1↔#3 cross-root obstruction under a SPAN (THIN-BUT-HONEST)
- `ZeroParadox/Multihomed/TreeObstructions.lean` - ZP-H: The bottom-diagram tree — machine-checked obstruction core (E4 + SPLIT, rebuilt)
- `ZeroParadox/Multihomed/TreeT1.lean` - ZP-H tree, edge T1 — the within-μ edge: proof-theory floor ↔ categorical-initial bottoms
- `ZeroParadox/Multihomed/TreeT2.lean` - ZP-H tree, edge T2 — the within-ν edge: Markov attractor ↔ p-adic inverse-limit
- `ZeroParadox/Multihomed/TwoFacesBot.lean` - Direction B — the two faces of ⊥ at the seam: VACUOUS (they coincide, but only as a bare singleton)
- `ZeroParadox/Multihomed/WallSpanRobust.lean` - ZP-H tree, TC19 — span-robustness of the well-founded cross-root wall (#1 vs #2)

### Computability (ZP-K, ZP-J)

- `ZeroParadox/Computability/ChoicePurityInvariant.lean` - ZP-H MC-1 tree test TC48: is choice-purity an IN-STATEMENT μ/ν separating invariant?
- `ZeroParadox/Computability/MarkovNuUniversal.lean` - ZP-H / TC20: does the Markov node (#2) get a ν (terminal/unique-fixed-point) universal property?
- `ZeroParadox/Computability/NatListRegime.lean` - ZP-H tree, TC49 — the third root-cut regime: the nat/list functor (leaf + recursive position)
- `ZeroParadox/Computability/RootCutTrichotomy.lean` - ZP-H: TC47 — the root cut is a TRICHOTOMY (leaf × recursive position)
- `ZeroParadox/Computability/StationaryUnique.lean` - ZP-H / TC31: irreducibility forces a unique stationary distribution for node #2

### Ordinals / proof theory (ZP-L, ZP-M, ZP-N)

- `ZeroParadox/Ordinal/ProofFloorCanonical.lean` - TC07 — Is the proof-theory bottom canonical across the depth campaign?

---

*Generated by `build_manifest.py` from the Lean tree + each file's `-- EXPERIMENTAL` header. Rerun after adding, moving, or renaming a file. (78 core, 75 experimental.)*
