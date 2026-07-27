# Zero Paradox — Lean Custom Definition Registry

This file documents every definition, typeclass, and instance in the Zero Paradox Lean library that diverges from Mathlib's standard formalization. Each entry records what was replaced or extended, and the precise reason the Mathlib version was insufficient.

Every entry corresponds to a `-- [ZP-CUSTOM]` inline comment in the source. The register is generated from those comments and is always consistent with them. To regenerate:

```
grep -rn "\[ZP-CUSTOM\]" ZeroParadox/ --include="*.lean"
```

---

## Custom Typeclasses

### `ZPSemilattice` — `ZeroParadox/Order/Lattice.lean:36`

**Relationship to Mathlib:** Replaces `SemilatticeSup` + `OrderBot`

**Reason:** Mathlib's semilattice hierarchy ties `⊔` to its order typeclass infrastructure (`LE`, `Preorder`) via hundreds of instances; importing it contaminates `#print axioms` with unrelated classical dependencies. `ZPSemilattice` states axioms A1–A4 from scratch so every theorem's axiom footprint is auditable.

---

### `AFAStructure` — `ZeroParadox/Settheory/SetTheoryAFA.lean:78`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` uses the Axiom of Foundation (`ZFSet.regularity`), which forbids `x ∈ x`. AFA content (self-containing sets, Quine atoms) cannot be encoded using `ZFSet`. `AFAStructure` is the lattice-level encoding of what ZF+AFA provides set-theoretically, with `selfMem` / `quine_unique` / `bot_self_mem` as the three minimal class fields.

---

### `AbstractSelfApp` — `ZeroParadox/Computability/SelfApp.lean:63`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Abstracts the shared fixed-point pattern between AFA set theory (`f x = {x}`, unique fixed point = Quine atom) and 2-adic multiplication (`f x = 2x`, unique fixed point = 0). Mathlib has `Function.IsFixedPt` (a predicate on total functions) but no typeclass for "type with a self-application operation whose unique fixed point is a designated bottom element." Introducing this typeclass allows `AFAStructure`'s three class fields to become derived theorems.

---

### `SeparatedSuccession` — `ZeroParadox/Multihomed/SeparatedSuccession.lean:54`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** An interface bundling a carrier with a separation relation and an ℕ-indexed succession whose consecutive terms are always separated. Mathlib has chains and apartness relations separately but no bundled "separated succession" interface. Used as the type bridge between differently-typed framework charts of one succession — the ordinal ε-chain (separation = strict order, `succession_lt_succ`) and the Hilbert state-chain (separation = orthogonality, `t5_strict_orthogonal`) — exhibited as two implementations of one shape rather than forced into an ill-typed cross-universe identity.

---

### `ValuationStructure` — `ZeroParadox/Valuation/Scale.lean:62`

**Relationship to Mathlib:** Replaces `Mathlib.RingTheory.Valuation.Valued`

**Reason:** Mathlib's `Valued` typeclass requires ring/field structure (it formalizes algebraic valuations over rings). `ZPSemilattice` has join only — no ring. `ValuationStructure` uses `val : L → ℕ∞` (not a `GroupWithZero` target) and the single axiom `val_scale` (val strictly increases under scale), which is the only machinery needed for the fixed-point uniqueness argument.

---

### `ValBridge` — `ZeroParadox/Valuation/ScaleBridge.lean:47`

**Relationship to Mathlib:** Replaces `ValuationStructure` (this project)

**Reason:** `ValuationStructure` required `[ZPSemilattice L]` but the join operation `⊔` never appears in any of its four axioms — the constraint was an encoding artefact. `ValBridge` carries the same four axioms with `bot` as a plain field, allowing `ℤ_[2]` (a ring, not a `ZPSemilattice`) to be a formal instance. Unifies both tracks under one common ancestor.

---

### `KleeneStructure` — `ZeroParadox/Computability/Kleene.lean:168`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Bridges `AFAStructure` (set-theoretic self-containment) with Mathlib's computability library (`Nat.Partrec.Code`). No Mathlib typeclass connects AFA and `Code`. `KleeneStructure` asserts that the AFA Quine atom and the Kleene computational Quine (`∃ c, eval c = f c`) name the same structural property — this identification is the motivating commitment of ZP-K, not a derived theorem.

---

### `ZPCategory` — `ZeroParadox/Category/Category.lean:42`

**Relationship to Mathlib:** Extends `Mathlib.CategoryTheory.Limits.IsInitial`

**Reason:** Mathlib has `IsInitial` and `IsTerminal` as separate structures; it has no typeclass bundling them together with AX-G2 (source asymmetry: `hom(X,0) = ∅` for non-isomorphic `X`). `ZPCategory` bundles both ZP-G axioms so they can be assumed uniformly across all ZP-G theorems without threading separate hypotheses.

---

### `ZPSurprisal` — `ZeroParadox/Category/Category.lean:54`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib has no formalization of Kolmogorov complexity. `ZPSurprisal` is an import stub for the I-KC axiom (D7'): it models conditional K-complexity as an abstract `ℕ`-valued morphism assignment. The one field (`surp_id`: identity morphisms have zero surprisal) is the only structurally usable I-KC axiom in the ZP-G theorems; the rest of K-complexity is outside Lean scope.

---

### `DecorationUniverse` — `ZeroParadox/Settheory/APG.lean:138`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` (the only set-theory formalization) uses Foundation — `x ∈ x` is forbidden, making it invalid as a decoration target for any APG with a self-loop. `DecorationUniverse` is an abstract type with `ValuationStructure` plus a `collect` operation and two axioms (`collect_singleton`, `collect_val_ge`), providing the minimum structure needed for AFA decoration uniqueness without importing any set-theoretic axiom.

---

### `Wheel` — `ZeroParadox/Algebra/Wheel.lean:106`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib has no wheel typeclass (Carlström's algebraic structure in which division is total — `1/0` is a defined element). Extending `AddCommMonoid` + `CommMonoid` would inherit full semiring distributivity, which wheels deliberately weaken (axiom W9). `Wheel` states the wheel axioms (Carlström W1–W14) from scratch for axiom auditability, following the `ZPSemilattice` convention.

---

### `WheelValuationStructure` — `ZeroParadox/Algebra/Wheel.lean:413`

**Relationship to Mathlib:** Extends `CommRing` (no Mathlib analog for the bridge)

**Reason:** The bridge typeclass connecting the ZP valuation hierarchy to wheel theory via the wheel-of-fractions construction. Over a `CommRing L` it carries a valuation `wvs_val : L → ℕ∞` that is additive on products (`wvs_val_mul`), with the assumed condition `wvs_val 0 = ⊤` (`wvs_val_zero`) — an axiom encoding that the ring's zero sits at infinite valuation. The ZP argument motivates the choice; the type-checker does not verify its necessity. No Mathlib typeclass bundles a ring with such a valuation for the wheel construction.

---

## Custom Types and Definitions

### `OntologicalStates` — `ZeroParadox/Valuation/Padic.lean:51`

**Relationship to Mathlib:** Replaces `Fin 2`

**Reason:** `Fin 2`'s constructors are `⟨0,_⟩` and `⟨1,_⟩` — natural numbers. `nullState` is not ℕ's 0 by convention; it is a semantic state with no numeric meaning. The free inductive eliminates the ℕ dependency and makes `⊥ ↦ null` a structural fact, not a labelling choice.

---

### `BinaryState` — `ZeroParadox/Information/Surprisal.lean:48`

**Relationship to Mathlib:** Replaces `Fin 2`

**Reason:** Surprisal is self-contained (no Padic import as a Lean dependency). `BinaryState` is a local copy of the same free-inductive encoding used by `OntologicalStates` in Padic. `Fin 2` would import ℕ arithmetic into an information-theoretic file whose proofs should not depend on it.

---

### `IsQuineAtom` — `ZeroParadox/Settheory/SetTheoryAFA.lean:99`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Lattice-level analog of Aczel's Quine atom (the unique set satisfying `x = {x}`). No Mathlib definition covers this: it requires `AFAStructure` context and encodes the conjunction of self-containment + uniqueness as a single predicate. Proved equivalent to `q = ⊥` by `t_exec_iff`.

---

### `APG` — `ZeroParadox/Settheory/APG.lean:84`

**Relationship to Mathlib:** Extends `Mathlib.Combinatorics.Quiver.Basic`

**Reason:** Mathlib's `Quiver` is a bare directed graph (objects + edges) with no distinguished root or accessibility requirement. `APG` adds `root : V` and the accessibility proof (every vertex reachable from root), matching Aczel's definition of Accessible Pointed Graph. Both fields are required by AFA's decoration theorem.

---

### `IsKleeneFixedPoint` — `ZeroParadox/Computability/Kleene.lean:92`

**Relationship to Mathlib:** Replaces `Mathlib.Function.IsFixedPt`

**Reason:** `Function.IsFixedPt` works on total functions `α → α`. Here `f : Code → ℕ →. ℕ` (partial function) and the fixed-point condition is `eval c = f c` — equality of partial functions. No Mathlib predicate covers this; `IsKleeneFixedPoint` is the partial-function analog needed for the computability layer.

---

### `IsComputationalQuine` — `ZeroParadox/Computability/Kleene.lean:129`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Named alias for `IsKleeneFixedPoint selfApply c`. Makes the connection to Quine atoms explicit in type signatures and theorem statements. Unlike the AFA Quine (unique by `quine_unique`), computational quines are not unique — each has a distinct Gödel number, generating the infinite family proved in §VI.

---

### `HasLawvereWitness` — `ZeroParadox/Category/Lawvere.lean:43`

**Relationship to Mathlib:** Names the hypothesis of `Function.exists_fixed_point_of_surjective` (no Mathlib named predicate)

**Reason:** Mathlib proves Lawvere's fixed-point theorem (`Function.exists_fixed_point_of_surjective`) but exposes no reusable predicate for "β admits a point-surjection α → (α → β)" — the diagonal hypothesis. Naming it lets the face-split state, per face, whether the hypothesis holds (the Set faces are refuted by Cantor; the computability face is genuine). A naming alias in the spirit of `IsComputationalQuine`; no new axiomatic content — every theorem about it reduces to the Mathlib lemma.

---

### `Phase` (with `floorRel`, `phaseRel`, `snap`) — `ZeroParadox/Multihomed/Boundary.lean:94`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The illustrative single-carrier model for the well-foundedness boundary: `floor` (the self-looping ⊥) and `up : Ordinal → Phase` (the ε₀ ascent), with `phaseRel` self-looping at the floor and following ordinal `<` above it, and `snap := up 0` the irreversible exit. Mathlib has no type bundling a non-well-founded floor with a well-founded ordinal ascent under one relation. The carrier is a *modeling choice* — the boundary theorems' content is the two proven endpoints plus the framework's existing ⊥/ε₀ identification (MC-1, ε₀ open under OQ-E2), not a new commitment; the real-⊥ endpoint (`floorRel` / `floor_not_wellFounded`) is axiom-free on the actual lattice.

---

## Custom Instances

### `machinePhaseZPS` — `ZeroParadox/Order/Snap.lean:55`
`ZPSemilattice MachinePhase`

The cross-framework bridge. `MachinePhase` is Surprisal's two-element type; giving it a `ZPSemilattice` instance makes T-SNAP (`bot_join` applied to `MachinePhase`) a direct consequence of ZP-A's A4, retiring AX-1 as an axiom. No Mathlib lattice instance exists for `MachinePhase`.

---

### `machinePhaseAFA` — `ZeroParadox/Computability/Kleene.lean:265`
`AFAStructure MachinePhase`

`selfMem x := x = bot` is the CIC-compatible encoding of AFA self-containment (`⊥ = {⊥}` cannot be stated in Lean's well-founded type theory). `quine_unique` and `bot_self_mem` are provable by `rfl`. This is the concrete closure of DA-1 for ZP-E's machine model.

---

### `machinePhaseKleene` — `ZeroParadox/Computability/Kleene.lean:275`
`KleeneStructure MachinePhase` (noncomputable)

`botCode` is chosen via `Classical.choose` — no algorithm can identify which `Code` is the `botCode` (`isComputationalQuine_undecidable`). The `noncomputable` marker is load-bearing, not a proof artifact: the non-constructivity is the formal content of DA-1's computational path. Removing it would misrepresent the result.

---

### `instZ2ValBridge` — `ZeroParadox/Valuation/ScaleBridge.lean:97`
`ValBridge ℤ_[2]`

`ℤ_[2]` is a ring — it cannot be a `ZPSemilattice` instance and could not satisfy `ValuationStructure`. `ValBridge`'s bot-as-plain-field design makes this instance possible. All four axioms delegate directly to theorems proved in `Scale` §V (`q2Scale_bot`, `q2Val_bot`, `q2Val_unique`, `q2Val_scale`).

---

### `instNatInfZPS` — `ZeroParadox/Settheory/Model.lean:63`
`ZPSemilattice ℕ∞` with inverted order

Mathlib's `WithTop ℕ` has `≤` as its standard order (`⊤` is maximum). Here `join = min` and `bot = ⊤` — a deliberate reversal. The ZP partial order `x ≤_ZP y ↔ min x y = y` makes `⊤` the bottom (valuation ∞) and `0` the maximum (fully constrained). No Mathlib instance covers this inverted reading.

---

### `instNatInfVal` — `ZeroParadox/Settheory/Model.lean:76`
`ValuationStructure ℕ∞` (scale = +1, val = id)

The concrete model confirming that `ValuationStructure`'s abstract axioms have an inhabitant. `val = id` works because `ℕ∞` already carries its own depth as its value; `scale = (· + 1)` satisfies `val_scale` by `rfl`.

---

### `instOntZPS` — `ZeroParadox/Settheory/OntBridge.lean:46`
`ZPSemilattice OntologicalStates`

`OntologicalStates` carries no Mathlib lattice structure. The join (null-identity, exist-absorbing) matches ZP-A's A1–A4 but does not correspond to any Mathlib-provided instance on a two-element type.

---

### `instOntSelfApp` — `ZeroParadox/Settheory/OntBridge.lean:61`
`AbstractSelfApp OntologicalStates` via constant-to-null map

`OntologicalStates` (two elements) cannot satisfy `ValuationStructure`'s `val_scale` axiom — a finite two-element type has no room for `val` to strictly increase. The direct `AbstractSelfApp` instance using the constant-to-null map (every element → null) is the shorter path to AFA content for finite types.

---

*Last updated: 2026-07-19. Regenerate with: `grep -rn "\[ZP-CUSTOM\]" ZeroParadox/ --include="*.lean"`*

### `IsLeastFixedPointFrom` — `ZeroParadox/Order/LeastFixedPoint.lean:77`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's least-fixed-point API (`OrderHom.lfp`, `isLeast_lfp`) is fixed to a `CompleteLattice` carrier. This predicate states the SAME mu characterization (least fixed point at or above a seed) over a bare relation, so it applies to the framework's non-lattice carriers — the axiom-clean `ZPSemilattice` L, and `Ordinal`, which is not a complete lattice. It is the order-generic placement schema, grounded back to `OrderHom.lfp` in that file's section II.

### `ProvabilityLogic` — `ZeroParadox/Settheory/Loeb.lean:60`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib carries no modal or provability logic — no Loeb, no GL, no derivability conditions, no modal Kripke apparatus (grep-verified). A minimal typeclass carrying just the Hilbert-Bernays-Loeb apparatus, so that Loeb's theorem can be presented as a face of the diagonal family.

### `QuineHost` — `ZeroParadox/Settheory/QuineHost.lean:95`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` carries Foundation (`ZFSet.mem_wf`), which forbids `x in x` and so cannot host a Quine atom; and no Mathlib typeclass abstracts "a membership relation with a unique self-membered bottom." `QuineHost` is the minimal set-theory-native encoding of the framework's requirements on a host theory (fields `bot_selfMem` / `selfMem_unique`), distinct from the lattice-level `AFAStructure` in `SetTheoryAFA.lean`.

### `trivialSelfApp` — `ZeroParadox/Computability/SelfApp.lean:177`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** A deliberately degenerate `AbstractSelfApp` witness — the constant-bottom self-application — built to bound what the typeclass hypothesis can be made to yield. Not a modelling instance but a NO-GO gauge: it shows every `ZPSemilattice` carries an `AbstractSelfApp`, so no property of the carrier follows from the bare hypothesis. Mathlib has no notion of a deliberately vacuous instance of a project-local class.

### `LoopsInPlace` — `ZeroParadox/Computability/Occurrence.lean:81`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Names the self-looping configuration of a state-transition function (`f s = some s`) as a first-class predicate, so the trichotomy and the trap result can be stated about it. Mathlib's `Computability/StateTransition.lean` supplies `Reaches` and `eval` but no name for "steps to itself", which is the case that turns out to be the self-referential object rather than a third route.

### `IsComputationalBottom` — `ZeroParadox/Computability/Occurrence.lean:110`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Bundles the framework's own two requirements on the computational bottom — that it is a fixed point of its own step, and that the snap departs from it — so their joint satisfiability can be decided. Framework-specific by construction; no Mathlib notion corresponds. The bundle is proved uninhabited (`machine_snap_impossible`), which is the point of naming it.

### `Occurs` — `ZeroParadox/Computability/Occurrence.lean:168`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Names the framework's "the transition fires" as a step-indexed predicate on codes (`∃ k, evaln k c n ≠ none`), so the classical halting results apply to it. Mathlib carries the halting predicate (`ComputablePred.halting_problem`) but not this reading of it; the identification of framework-occurrence with this predicate is the framework's modelling choice and is fenced as such at the definition.

### `Extremal` — `ZeroParadox/Computability/Occurrence.lean:233`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Names the two-element computational pole — a configuration is extremal when it is halted or looping in place — so the pole swap can be shown to preserve it as a set. Mathlib's `Computability/StateTransition.lean` has `Reaches` and `eval` but no notion of "sits at one of the two extremes of a state-transition function".

### `flipPoles` — `ZeroParadox/Computability/Occurrence.lean:238`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The computational analogue of `rInv` / `swap` — an involution on step functions that exchanges the halted and self-looping poles while fixing every configuration that steps onward. Mathlib has no such operation on `σ → Option σ`. Fenced at the definition: it is an automorphism of the SPACE of machines, not of one machine, so it is the same shape at a different level and never a cross-type identity.


### `stepCoalg` — `ZeroParadox/Computability/GroundZero.lean:73`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The connector between a `StateTransition`-style step function `σ → Option σ` and the framework's own `natPF_NatListRegime` presentation of the polynomial functor `X ↦ 1 + X`. Mathlib carries both sides — `Computability/StateTransition.lean` and `Data/QPF/Univariate/Basic.lean` — and no map between them, because the two live in unrelated corners of the library. This is that bridge, and it is where the framework's operational face (`Occurrence.lean`) meets its coalgebraic one (`NatListRegime.lean`). The construction itself is standard: reading a partial step function as a `1 + X`-coalgebra is textbook (Jacobs, *Introduction to Coalgebra*, Ch. 2), and no novelty is claimed for it.

### `TriStep` — `ZeroParadox/Computability/GroundZero.lean:169`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** A deliberate COUNTER-MODEL, not a construction to build on: a three-valued step outcome (halted / idle / stepping) whose only purpose is to be the carrier in which the § I forcing fails. Mathlib has no three-valued step outcome because there is no reason to want one. It must never be used as a framework object.

**Prior art (added 2026-07-27):** the halted-versus-idle distinction is the ACP split between *successful termination* and *deadlock* (Baeten & Weijland, *Process Algebra*, 1990) - process algebra calls the third value **deadlock**, where the framework reads it as *unstarted*. Same object, opposite valence; the standard term should lead in any reader-facing prose.
