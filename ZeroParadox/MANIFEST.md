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
- `ZeroParadox/Order/SnapCannotBe.lean` - Machine-checked characterization index of the snap ⊥ → ε₀ (what the snap is / is not; `#check`-only)

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
- `ZeroParadox/Multihomed/SelfClosureObstruction.lean` - Self-Closure Obstructions: the wall-side mirror of the diagonal fixed point (experimental probe)
- `ZeroParadox/Multihomed/TopNumEdge.lean` - Web edge: topology ↔ number theory (the valuation generates the ball topology)

### Set theory / AFA (ZP-J)

- `ZeroParadox/Settheory/APG.lean` - ZPJ — Accessible Pointed Graphs and AFA Decoration Uniqueness
- `ZeroParadox/Settheory/AczelConn.lean` - ZPJ — Aczel Fixed Point Connection
- `ZeroParadox/Settheory/Coalgebra.lean` - ZP-P instance: the categorical parent (initial algebra vs final coalgebra)
- `ZeroParadox/Settheory/FixedPointFork.lean` - ZP-P: The Fixed-Point Fork
- `ZeroParadox/Settheory/Model.lean` - ZPJ — Concrete ValuationStructure Instance: (ℕ∞, min, ⊤)
- `ZeroParadox/Settheory/OntBridge.lean` - ZPJ — OntologicalStates → AbstractSelfApp → AFA Content
- `ZeroParadox/Settheory/QuineDichotomy.lean` - ZPJ — the Quine-atom dichotomy
- `ZeroParadox/Settheory/QuineHost.lean` - The Quine-Host Requirements — the AFA fragment the framework actually needs
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
- `ZeroParadox/Ordinal/Epsilon0CannotBe.lean` - Machine-checked characterization index of ε₀ (what ε₀ is / is not; `#check`-only)
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
- `ZeroParadox/DiagonalFixedPoint.lean` - Machine-checked keystone index of self-reference (the diagonal fixed point), routing every face by the μ/ν fork; `#check`-only
- `ZeroParadox/Category/DiagonalWitness.lean` - The minimum-requirements level under the keystone: the relativized Lawvere witness `HasWitnessRel`, its map-class topology (`IsLowerSet`), and the effective-category floor (axis 2). Packages Lawvere/Yanofsky/effective-topos; the floor faces' shared landing at ⊥ is the one uncopied placement.
- `ZeroParadox/Category/DifferenceGeneratesSystem.lean` - The nucleus/sublocale home of "a predicated difference generates a system": identifies the conjecture with Lawvere–Tierney (nucleus → sublocale → lattice) structure, and machine-checks that double negation generates the classical (Boolean) core (`Heyting.Regular`). `example`-only; states no new result.
- `ZeroParadox/Category/DoubleNegationNucleus.lean` - The double-negation nucleus: `dnegNucleus : Nucleus X` (the map `a ↦ aᶜᶜ` on any Heyting algebra), the excluded-middle / classical-collapse modality, the double-negation-side parallel of `snapNucleus`. Its closed points are exactly the regular elements — the Boolean core (`dnegNucleus_isClosed_iff`). Textbook (¬¬ subtopos / Glivenko); generates classical logic (excluded middle), NOT the axiom of choice - **full** AC is strictly stronger by **Cohen 1963** / Fraenkel-Mostowski, NOT by Diaconescu, whose own theorem is an *equivalence* for the restricted shape. **Choice-free: footprint `[propext]`** — `dneg_inf_distrib` re-proves meet-preservation on the meet side only, avoiding the `sup` route (`compl_sup_distrib`) through which Mathlib's `compl_compl_inf_distrib` carries `Classical.choice`. Since Lean derives `Classical.em` from `Classical.choice` by Diaconescu's argument, this is the statement that the modality whose closed points are the classical core is itself built with no classical input. **Correction of record:** this file once named the object the framework's "choice modality" - wrong (choice is strictly stronger), corrected in `655c761` off an adversary kill-list, and recorded in the file rather than quietly rewritten.
- `ZeroParadox/Category/ChoiceCannotBe.lean` - Machine-checked characterization index of the framework's **relationship to `Classical.choice`** - the fourth `CannotBe` index, after ⊥, the snap, and ε₀. **A framing difference from the other three:** choice is NOT a framework object, it is an ambient kernel axiom, so this indexes where choice is provably not needed, what it must not be confused with, and what is actually established. **Headline fence:** the English word "choice" (an act of picking, a point of view, a chart selection) and the axiom `Classical.choice` are NOT the same thing, and every "choice = which way you view the split" reading is a MODEL of the choice-vs-no-choice distinction, never the axiom. Prior art stated precisely: **Diaconescu (1975) proves an EQUIVALENCE** for the shape our `ChoiceFragment` has (choice for inhabited subobjects of a two-element object IS excluded middle); that *full* AC is strictly stronger is **Cohen 1963** / Fraenkel-Mostowski independence, NOT Diaconescu - do not attribute it to him. That excluded middle nonetheless fails to yield the fragment *in Lean* is a fact about **Lean's `Prop`/`Type` stratification** (the fragment selects into `Bool`, so it is data-valued excluded middle), which a topos lacks - that reconciliation is the framework's own small finding. `#check`-only - creates no declarations, so it structurally cannot overclaim, and the `import`s force every indexed proof to recompile. **Records NO count of choice-carrying declarations, deliberately** - a corpus total measures how classically Mathlib is built rather than anything about this framework, it reads as "most of this is non-constructive" when the load-bearing fact is that T-SNAP is axiom-free and every examined footprint has been removable, and the figure has already been wrong three times (once quoted rather than measured, once measured and gone stale within a session). The file supplies the PowerShell to measure on demand instead. Indexes both directions: the choice-free results (§ I) and an actual choice-carrying case (`cofix_nonempty'`) beside its axiom-free counterpart, so the file cannot read as "the framework is choice-free" - it is not.
- `ZeroParadox/Valuation/PoleChartSelection.lean` - A **NEGATIVE result**, and the negative result is the point. Tests the reading "choice is which way you view the zero/infinity split." **§ I: refuted for the built pole.** On `OnePoint X` the two pole points are different constructors, so a canonical selector exists with **no axioms at all** (`chart_selection_is_freeG`); selecting a chart at the framework's own pole (`Sphere := OnePoint ℚ_[2]`, `rInv_swaps`) is constructively free, and the involution imposes nothing. Stated generically in `X` FIRST for a measured reason: at `ℚ_[2]` even the bare constructor-match discriminator measures `[propext, Classical.choice, Quot.sound]`, because `ℚ_[2]` is a Cauchy completion whose `Zero` instance is already noncomputable - that footprint is the price of `ℚ_[2]` existing, NOT the price of selection, and the generic section is the control that makes the attribution checkable. **§ II: a labelled CONDITIONAL model** of what the reading would need - the charts must be internally indistinguishable - with the non-constructivity inserted by hypothesis at exactly one place (`poleAdmissible`, an arbitrary undecided proposition) under an explicit **smuggling notice**; `em_of_uniformChartSelection` reuses `ChoiceFragment`/`em_of_choiceFragment` rather than reproving Diaconescu, and `select_of_decidable` machine-checks the contrast (decidable chart predicate ⇒ selection free). **§ III: the gap, named** - the reading holds only under the modeling commitment that the two charts are internally indistinguishable, which is the framework's apophatic claim about ⊥ and is a commitment, not a theorem. On `OnePoint ℚ_[2]` that claim is false by constructor.
- `ZeroParadox/Ordinal/SyntacticCollapse.lean` - An EXPERIMENT and a SURROGATE, not a re-proof. Tests whether the *content* of the 2-adic metric collapse is available without `Classical.choice` by staying on raw `ONote` syntax (never calling `repr`, never touching `NONote`/`NF` or the topology stack). `synVal : ONote → ℕ` (leading-exponent depth) with `synVal_tower`, `synCollapse_epsN` (convergence in explicit ε-N form, not via `Filter.Tendsto`), the load-bearing `le_synVal_of_tower_le` (the valuation floor is forced by position in the syntactic order, not exhibited by one chosen sequence), and `synVal_mono` (monotone for `ONote.cmp` - what earns `synVal` the name *valuation* rather than *depth counter*; produced by a verification pass that challenged whether the definition was faithful). All `[propext]`. Tests the standing conjecture "choice is forced by the metric collapse": the snap half is already resolved incidental (`t_snap_derived` is axiom-free), the metric half had never been attempted, and this moves it only to evidence. **Does NOT establish that the metric collapse is choice-free** - `tower_converges_to_zero` (`Ordinal/Gentzen.lean`) is a different statement on a different carrier and is neither replaced nor discharged, and the bridge `synVal = 2-adic valuation` is NOT proved in Lean. The honest reading is bounded: evidence that the choice in the 2-adic statement is Mathlib-imposed rather than forced. The file carries its own triviality assessment.
- `ZeroParadox/Category/ExcludedMiddleBridge.lean` - The bridge separating choice from excluded middle: a choice fragment (a hypothesis, never an axiom) implies excluded middle (`em_of_choiceFragment`, Diaconescu 1975 / Goodman-Myhill 1978, prior art - the framework claims only the packaging, no hypothesis-form version found in Mathlib), which holds iff every proposition is a closed point of `dnegNucleus` on `Prop` (`em_iff_dnegNucleus_trivial`, `[propext]`). **Scoped to `Prop`, and § IV machine-checks why:** `fin3_middle_not_closed_point` exhibits the three-element chain as a Heyting algebra that stays non-Boolean *inside Mathlib's classical metatheory* (`1ᶜᶜ = 2 ≠ 1`), so "excluded middle collapses the double-negation nucleus" is FALSE in general and is asserted nowhere. Instance hazard handled explicitly: `Prop.instBooleanAlgebra` carries `Classical.choice` (it discharges `top_le_sup_compl` with `Classical.em`) while `Prop.instHeytingAlgebra` is `[propext]`, so every `Prop`-scoped statement pins the Heyting instance. `ChoiceFragment` was probed in BOTH directions: `ExcludedMiddle -> ChoiceFragment` fails at the `Prop`-to-`Bool` elimination barrier (`Decidable (S true)`) and closes only under `classical`, so the fragment sits genuinely above excluded middle - evidence, NOT a formal independence result. **Correction of record:** the file was first drafted in the unscoped general form, which § IV refutes.
- `ZeroParadox/Ordinal/SnapNucleus.lean` - The snap IS a nucleus: `snapNucleus : Nucleus Ordinal` (the next-fixed-point of the snap-step `α ↦ ω^α`), a genuine point-free Lawvere–Tierney modality that sends the bottom ⊥ to ε₀ (`snapNucleus_bot`). The framework's own snap/ε₀/⊥ triad as a concrete difference-generator instance. Meet-preservation is free on the ordinal chain, so a `Nucleus` needs no frame/top; the missing top (the point-at-infinity) is needed only for the meta-lattice of nuclei.
- `ZeroParadox/Ordinal/SnapMetaLattice.lean` - The lattice of systems: adjoining the point at infinity (`WithTop Ordinal`) makes the ordinals a frame, on which the nuclei form a `Frame` and the sublocales a `Coframe` — the lattice the bare (top-less) ordinals lack. The snap is lifted into it: `snapNucleusTop : Nucleus (WithTop Ordinal)` (sends `↑⊥` to `↑ε₀`, `snapNucleusTop_coe_bot`) with `snapSublocale` its generated system, a named point in the lattice. Provably the top's doing: the machinery fires on `WithTop Ordinal`, not bare `Ordinal`.
- `ZeroParadox/Ordinal/SnapNucleusConstructive.lean` - **A machine-checked IMPOSSIBILITY, scoped to `ONote`-shaped notation systems.** Asks whether the snap has a closure-shaped counterpart on that carrier. Answer: **no, and not for choice reasons.** **Scope fence:** this does NOT show the snap nucleus is constructively impossible in general - a notation system extending past ε₀ (Veblen, Bachmann-Howard) is untouched and open, and none is in Mathlib - and it does NOT classify `snapNucleus`'s own footprint, which stays **UNCLASSIFIED** (no re-proof exists; `Ordinal` carries choice in the type). `no_snap_closure` - for ANY idempotent `j : ONote → ONote`, its closed points cannot be exactly the ε-numbers; idempotence alone suffices, no order or monotonicity assumed. `no_snap_nucleus` is the `Nucleus`-typed corollary, non-vacuous because `idNucleus` exhibits nuclei on the carrier. The reason is **expressive reach, not `Classical.choice`**: a nucleus achieves idempotence by landing on a fixed point, `omegaPow_no_fixedpoint` says the notation system has none, and `tower_cofinal`/`tower_no_upper_bound` locate why - ε₀ is the SUPREMUM of Cantor normal form, not a member, so **the system cannot name its own closure from inside**. Keep the two failure modes distinct: the proofs here are all `[propext]`, so nothing in THIS file's reasoning needs choice - but that does **not** classify `snapNucleus`'s own footprint, which stays **UNCLASSIFIED** (no re-proof of it exists, and `Ordinal` carries choice in the type). What is unavailable is the *construction*. Also establishes a choice-free `LinearOrder`/`SemilatticeInf` on a `SynONote` synonym built from `ONote.cmp` directly (`instLinearOrderSynONote`, `[propext]`), because **Mathlib's `ONote` order is unusable twice over**: it routes through `repr` into choice-saturated `Ordinal`, AND it is not antisymmetric - `mathlib_ONote_order_not_antisymm` exhibits `1 + ω` and `ω` as distinct notations with equal `repr`, which is why Mathlib declares only `Preorder`. Carries its own triviality assessment: given `omegaPow_no_fixedpoint` the impossibility is two lines; the value is converting "we tried and it did not work" into "it cannot exist, and here is why."
- `ZeroParadox/Ordinal/SnapSuccession.lean` - The succession as a strict chain: the ε-numbers (`ε_ = deriv (ω^·)`) are the snap's successive **targets**, exactly the closed points of `snapNucleus` (`snapNucleus_isClosed_iff`), climbing strictly (`succession_lt_succ`), each the snap re-seeded one step above the last (`succession_succ`). **They are NOT ⊥** - `ε₀ ≠ ⊥` is bedrock (`epsilon0_ne_bot`). The standard term for a rung is an **iterative bottom**: a bottom relative to its iteration, the base the next snap re-seeds above, never ⊥ itself (role, not identity - the family/instance distinction; standardized 2026-07-19, vocabulary reference § 1b, and NOT "local bottom", which is already taken for the per-domain MC-1 family in `ZeroParadox/Category/GlobalZero.lean`). The genuinely new bottom the arc returns to is `t_iz_limit_is_new_null`'s successor null, a `ZPSemilattice` fact, not an ordinal ε-number. An earlier header said "the new bottoms are the ε-numbers" and was corrected 2026-07-19 after it contradicted the file's own Engineer's Take. The orthogonality of the rungs is realized in the Hilbert chart (ZP-D `t5_strict_orthogonal`); the cross-chart bridge is `Multihomed/SeparatedSuccession.lean`.
- `ZeroParadox/Multihomed/SeparatedSuccession.lean` - The type bridge as an interface: `SeparatedSuccession` (carrier + separation relation + ℕ-succession + separated-law), with two known implementations — `ordinalSuccession` (ε-numbers, separation = strict order, `succession_lt_succ`) and `hilbertSuccession` (state vectors, separation = orthogonality, ZP-D `t5_strict_orthogonal`). The carriers are distinct types at different universes, so the shared shape is the interface, never a cross-type identity (instance-vs-requirements / Yoneda). `[ZP-CUSTOM]`.

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
- `ZeroParadox/Order/OrbitDichotomy.lean` - The orbit dichotomy — "one or infinitely many", no finite middle (probe)
- `ZeroParadox/Order/PadicLimitCone.lean` - ZP-H MC-1 TC10: the p-adic floor `{0}` is a genuine categorical limit cone
- `ZeroParadox/Order/ProofFloorHomset.lean` - ZP-H tree, TC43 — Axis III over the proof-theory floor #1 (the hom-set carrier convention)
- `ZeroParadox/Order/SeamSchema.lean` - ZP-H MC-1 tree test TC42: a shared "seam schema" for the QPF root-seam and the lattice selfApp seam,
- `ZeroParadox/Order/WellFoundedObstruct.lean` - ZP-H tree, edge TC28 — well-foundedness obstructs the attractor character of the μ floor

### Valuation / number theory (ZP-B, ZP-F)

- `ZeroParadox/Valuation/BottomInvariant.lean` - A first universal: the bottom carries an invariant probability measure
- `ZeroParadox/Valuation/ContractionRate.lean` - ZP-H tree, edge TC30 — the contraction-rate dichotomy at the p-adic floor #3
- `ZeroParadox/Valuation/NuLeafReconcile.lean` - ZP-H tree, edge TC16 — the within-ν edge reconciles at the LEAF, not the ambient
- `ZeroParadox/Valuation/NuRateEdge.lean` - ZP-H tree, edge TC33 — the within-ν edge at the orbit-RATE level (#3 ↔ #2)
- `ZeroParadox/Valuation/NuRateMatch.lean` - ZP-H tree, TC43 — within-ν geometric-rate match: #2 (irreducible Markov) and #3 (p-adic) share rate 1/2
- `ZeroParadox/Valuation/PadicAttractor.lean` - ZP-H tree, edge TC05 — the p-adic floor #3 as a dynamical attractor
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
- `ZeroParadox/Category/SeamFrameChange.lean` - The frame-change in the category frame: `op`-duality swaps initial ↔ terminal at the seam
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
- `ZeroParadox/Multihomed/SnapFrameChange.lean` - The snap as a change of frame: the tower's two limits (⊥ and ∞) are two charts, swapped by `rInv`
- `ZeroParadox/Multihomed/SpanObstruction.lean` - ZP-H tree, TC17 / TC14 — the #1↔#3 cross-root obstruction under a SPAN (THIN-BUT-HONEST)
- `ZeroParadox/Multihomed/TreeObstructions.lean` - ZP-H: The bottom-diagram tree — machine-checked obstruction core (E4 + SPLIT, rebuilt)
- `ZeroParadox/Multihomed/TreeT1.lean` - ZP-H tree, edge T1 — the within-μ edge: proof-theory floor ↔ categorical-initial bottoms
- `ZeroParadox/Multihomed/TreeT2.lean` - ZP-H tree, edge T2 — the within-ν edge: Markov attractor ↔ p-adic inverse-limit
- `ZeroParadox/Multihomed/TwoFacesBot.lean` - Direction B — the two faces of ⊥ at the seam: VACUOUS (they coincide, but only as a bare singleton)
- `ZeroParadox/Multihomed/WallSpanRobust.lean` - ZP-H tree, TC19 — span-robustness of the well-founded cross-root wall (#1 vs #2)

### Set theory / AFA (ZP-J)

- `ZeroParadox/Settheory/ForkFrameChange.lean` - The order-theoretic universal frame-change: duality swaps the fork's ends
- `ZeroParadox/Settheory/LawvereBridge.lean` - The Lawvere dereference — selfApp as an instance of the general engine (probe)
- `ZeroParadox/Settheory/MetaFork.lean` - The meta-level fork — the double dereference (probe)
- `ZeroParadox/Settheory/RequirementsGap.lean` - The instance-vs-requirements gap as a fork instance (probe)

### Computability (ZP-K, ZP-J)

- `ZeroParadox/Computability/ChoicePurityInvariant.lean` - ZP-H MC-1 tree test TC48: is choice-purity an IN-STATEMENT μ/ν separating invariant?
- `ZeroParadox/Computability/CodeDataFrameChange.lean` - The frame-change in the computability frame: the code↔data involution and the quine on its fixed locus
- `ZeroParadox/Computability/ComputableCrossing.lean` - The Lawvere bridge, crossed in the computability face (probe)
- `ZeroParadox/Computability/MarkovNuUniversal.lean` - ZP-H / TC20: does the Markov node (#2) get a ν (terminal/unique-fixed-point) universal property?
- `ZeroParadox/Computability/NatListRegime.lean` - ZP-H tree, TC49 — the third root-cut regime: the nat/list functor (leaf + recursive position)
- `ZeroParadox/Computability/RootCutTrichotomy.lean` - ZP-H: TC47 — the root cut is a TRICHOTOMY (leaf × recursive position)
- `ZeroParadox/Computability/StationaryUnique.lean` - ZP-H / TC31: irreducibility forces a unique stationary distribution for node #2

### Ordinals / proof theory (ZP-L, ZP-M, ZP-N)

- `ZeroParadox/Ordinal/ProofFloorCanonical.lean` - TC07 — Is the proof-theory bottom canonical across the depth campaign?

---

*Generated by `build_manifest.py` from the Lean tree + each file's `-- EXPERIMENTAL` header. Rerun after adding, moving, or renaming a file. (80 core, 85 experimental.)*
