# Zero Paradox — Lean Custom Definition Registry

This file documents the definitions, typeclasses and instances CARRYING A `[ZP-CUSTOM]` TAG, each recording what was replaced or extended and why the Mathlib version was insufficient. ⚠ It is not a completeness claim over the corpus: as of 2026-08-30 roughly twenty project-local `class` and `structure` declarations are untagged and therefore absent here (`StrippedBottom` in `ZeroParadox/Valuation/StrippedBottom.lean` among them), and the count check below is blind to that by construction — adding an untagged declaration leaves entry count and tag count equal.

Every entry corresponds to a `-- [ZP-CUSTOM]` inline comment in the source. ⚠⚠ **The register is NOT generated and is NOT automatically consistent with those comments.** It is maintained by hand. `tools/verify/check_invariants.py` compares the entry COUNT against the tag COUNT and nothing finer, so WORDING drift between the two copies is mechanically invisible and must be compared by eye — several entries here carry citations, dates or prior-art blocks their tag does not, and this file records one past case where the two contradicted each other outright. To list the tags (this prints them; it does not regenerate anything):

```powershell
Get-ChildItem ZeroParadox -Recurse -Filter *.lean | Select-String -Pattern '\[ZP-CUSTOM\]'
```

---

## Custom Typeclasses

### `ZPSemilattice` — `ZeroParadox/Order/Lattice.lean`

**Relationship to Mathlib:** Replaces `SemilatticeSup` + `OrderBot`

**Reason:** Mathlib's `SemilatticeSup` + `OrderBot` would satisfy the algebra, and using them is cheap — measured 2026-08-30 at the pinned Mathlib, both classes are axiom-free and `bot_sup_eq` and `sup_assoc` cost `[propext]` only. `ZPSemilattice` states A1–A4 as FIELDS anyway, so each theorem's footprint is fixed by the axioms it consumes rather than by whichever hierarchy lemma the elaborator reached for. ⚠⚠ This is an AUDITABILITY choice, not an axiom-avoidance one: an IMPORT never changes a footprint, only USING a proof does. (`ZeroParadox/Order/Lattice.lean` line 1 imports `Mathlib.Tactic` and the class still measures clean — this entry previously claimed the opposite.)

---

### `AFAStructure` — `ZeroParadox/Settheory/SetTheoryAFA.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` uses the Axiom of Foundation (`ZFSet.regularity`), which forbids `x ∈ x`. No `ZFSet` element can satisfy `x ∈ x`, so a Quine atom is not directly available as a `ZFSet` — AFA content is still MODELLABLE over a well-founded universe, as Aczel does via decorations of accessible pointed graphs (see the `APG` entry). `AFAStructure` is the lattice-level encoding of what ZF+AFA provides set-theoretically, with `selfMem` / `quine_unique` / `bot_self_mem` as the three minimal class fields.

---

### `AbstractSelfApp` — `ZeroParadox/Computability/SelfApp.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Abstracts the shared fixed-point pattern between AFA set theory (`f x = {x}`, unique fixed point = Quine atom) and 2-adic multiplication (`f x = 2x`, unique fixed point = 0). Mathlib has `Function.IsFixedPt` (a predicate on total functions) but no typeclass for "type with a self-application operation whose unique fixed point is a designated bottom element." Introducing this typeclass allows `AFAStructure`'s two LAWS (`bot_self_mem`, `quine_unique`) to become derived theorems; its `selfMem` field is DATA, supplied by `def selfMemDerived` rather than proved.

---

### `SeparatedSuccession` — `ZeroParadox/Multihomed/SeparatedSuccession.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** An interface bundling a carrier, a separation relation, an ℕ-indexed succession, the law that consecutive terms are separated, and — the field carrying the content — `sep_irrefl_on_seq`, without which the structure is exactly `Nonempty` (its own gauge says so). Mathlib has chains and apartness relations separately but no bundled "separated succession" interface. Used as the type bridge between differently-typed framework charts of one succession — the ordinal ε-chain (separation = strict order, `succession_lt_succ`) and the Hilbert state-chain (separation = orthogonality, `t5_strict_orthogonal`) — exhibited as two implementations of one shape rather than forced into an ill-typed cross-universe identity.

---

### `ValuationStructure` — `ZeroParadox/Valuation/Scale.lean`

**Relationship to Mathlib:** Replaces `Valued` (`Mathlib/Topology/Algebra/Valued/ValuationTopology.lean`)

**Reason:** Mathlib's `Valued` typeclass requires ring/field structure (it formalizes algebraic valuations over rings). `ZPSemilattice` has join only — no ring. `ValuationStructure` uses `val : L → ℕ∞` (not a `GroupWithZero` target) and four axioms (`ZeroParadox/Valuation/Scale.lean` § I lists them). The fixed-point uniqueness argument consumes TWO of them — `val_unique` and `val_scale`; `scale_bot` and `val_bot` appear in none of the three proof terms on that chain, measured 2026-08-30. ⚠ `val_scale` alone does NOT suffice, measured 2026-08-30: on `Bool` with `bot = false`, `scale = id` and `val` everywhere `⊤`, `scale_bot`, `val_bot` and `val_scale` all hold and `true` is a fixed point of `scale` that is not the bottom. `val_unique` supplies the FINITENESS that makes `val_scale` bite — `n = n + 1` is true at `⊤`, so without it the increment no-ops. ⚠ THE NEARER NEIGHBOUR IS `AddValuation`, NOT `Valued`, and this reason answered the wrong one until 2026-09-01: `AddValuation R ℕ∞` targets a `LinearOrderedAddCommMonoidWithTop`, which is exactly this class's target, so "not a `GroupWithZero` target" rebuts `Valuation` and says nothing about it. The real discriminator is the CARRIER: `AddValuation` requires `[Ring R]` and a `ZPSemilattice` has only a join — the same discriminator `ZeroParadox/Algebra/Wheel.lean` recorded for `AddValuation A ℕ∞` on 2026-08-01, which this tag had not picked up. ⚠ `AddValuation.top_iff` IS NOT THE NAME FOR THE `val_bot` + `val_unique` PAIR HERE, and this tag said it was until 2026-09-01: `top_iff` is stated over a `[DivisionRing K]` (Mathlib/RingTheory/Valuation/Basic.lean:71, and its own docstring says "on a division ring"), and ℤ_[2] is a DVR, not a division ring — 2 is not invertible. On ℤ_[2] the stock route to `val_unique` is `emultiplicity_eq_top` together with `FiniteMultiplicity.of_prime_left`: x ≠ 0 with 2 prime gives finite multiplicity, hence val x ≠ ⊤. Found by both prose gates independently, one of which compiled the failure. ⚠ On a RING carrier there is no gap at all: `multiplicity_addValuation PadicInt.prime_p` discharges all four axioms on `ℤ_[2]` from stock API with an unguarded `val_scale` — see `ZeroParadox/Valuation/Scale.lean` § V.

---

### `ValBridge` — `ZeroParadox/Valuation/ScaleBridge.lean`

**Relationship to Mathlib:** Replaces `ValuationStructure` (this project)

**Reason:** `ValuationStructure` required `[ZPSemilattice L]` but the join operation `⊔` never appears in any of its four axioms — the constraint was an encoding artefact. `ValBridge` carries the same four axioms with `bot` as a plain field, allowing `ℤ_[2]` (for which no `ZPSemilattice` is defined) to be a formal instance. Unifies both tracks under one common ancestor.

---

### `KleeneStructure` — `ZeroParadox/Computability/Kleene.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Bridges `AFAStructure` (set-theoretic self-containment) with Mathlib's computability library (`Nat.Partrec.Code`). No Mathlib typeclass connects AFA and `Code`. `KleeneStructure` asserts that the AFA Quine atom and the Kleene computational Quine (`∃ c, eval c = f c`) name the same structural property — this identification is the motivating commitment of ZP-K, not a derived theorem.

---

### `ZPCategory` — `ZeroParadox/Category/Category.lean`

**Relationship to Mathlib:** Extends `CategoryTheory.Limits.IsInitial` (`Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean`)

**Reason:** Mathlib has `IsInitial` and `IsTerminal` as separate structures; it has no typeclass bundling them together with AX-G2 (source asymmetry: `hom(X,0) = ∅` for non-isomorphic `X`). `ZPCategory` bundles both ZP-G axioms so they can be assumed uniformly across all ZP-G theorems without threading separate hypotheses.

---

### `ZPSurprisal` — `ZeroParadox/Category/Category.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib has no formalization of Kolmogorov complexity. `ZPSurprisal` is an import stub for the I-KC axiom (D7'): it models conditional K-complexity as an abstract `ℕ`-valued morphism assignment. The one field (`surp_id`: identity morphisms have zero surprisal) is the only structurally usable I-KC axiom in the ZP-G theorems; the rest of K-complexity is outside Lean scope.

---

### `DecorationUniverse` — `ZeroParadox/Settheory/APG.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` (the only set-theory formalization) uses Foundation — `x ∈ x` is forbidden, making it invalid as a decoration target for any APG with a self-loop. `DecorationUniverse` is an abstract type with `ValuationStructure` plus a `collect` operation and two axioms (`collect_singleton`, `collect_val_ge`), providing the structure the decoration-uniqueness proof consumes, without importing `ZFSet` or any axiomatic set theory. ⚠ It is NOT axiom-free, and the PROVENANCE SPLITS between the class and the theorem. `DecorationUniverse` measures `[propext, Classical.choice, Quot.sound]`, inherited from the required `[ValuationStructure U]`, whose route is the `ℕ∞` numeral in `val_scale` — see the purity block in `ZeroParadox/Valuation/Scale.lean`, where the `_VSlit`/`_VScast` pair exhibits the clean proof. `decoration_unique` measures the same three and does NOT merely inherit them: its proof CALLS `Nonempty.some`, which unfolds to `fun h => Classical.choice h`, and reaches choice again independently through `Set.ncard_pos` and `Set.ncard_lt_ncard`. Two of those three routes bypass `[ValuationStructure U]` entirely and no respelling of the numeral touches them, so the THEOREM's removability is UNMEASURED — provenance and necessity are independent axes (`ZeroParadox/AxiomProfile.lean` § 0). ⚠ "Minimum" is also unproved: the NO-GO gauge in `ZeroParadox/Settheory/APG.lean` records the class is inhabited over EVERY `ValuationStructure` carrier.

---

### `Wheel` — `ZeroParadox/Algebra/Wheel.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib has no wheel typeclass (Carlström's algebraic structure in which division is total — `1/0` is a defined element). Extending `AddCommMonoid` + `CommMonoid` would inherit full semiring distributivity, which wheels deliberately weaken (axiom W9). `Wheel` states the wheel axioms (Carlström W1–W14) from scratch for axiom auditability, following the `ZPSemilattice` convention.

---

### `WheelValuationStructure` — `ZeroParadox/Algebra/Wheel.lean`

**Relationship to Mathlib:** **Incomparable** with `AddValuation A ℕ∞` (`Mathlib/RingTheory/Valuation/Basic.lean`) - weaker on the valuation conditions, stronger on the carrier

**Reason:** The bridge typeclass connecting the ZP valuation hierarchy to wheel theory via the wheel-of-fractions construction. Over a `CommRing L` it carries a valuation `wvs_val : L → ℕ∞` that is additive on products (`wvs_val_mul`), with the assumed condition `wvs_val 0 = ⊤` (`wvs_val_zero`) — an axiom encoding that the ring's zero sits at infinite valuation. The ZP argument motivates the choice; the type-checker does not verify its necessity.

**On the comparison, precisely:** `AddValuation.of` takes four axioms; this class supplies two, omitting `map_one'` and the ultrametric inequality (separating witness: `v n = v₂ n + v₃ n` on the integers is multiplicative and sends 0 to ⊤, yet `min (v 2) (v 3) = 1` is not at most `0 = v 5`). But `AddValuation` requires only a `Ring` while this class bundles a `CommRing`, so **neither implies the other** — the weakening holds only for the valuation conditions over a fixed commutative carrier. This entry said "strictly weaker" until 2026-08-01, which asserted an ordering that does not hold.

**Corrected 2026-08-01** (this entry previously read "no Mathlib analog for the bridge", which was false). `AddValuation.of` takes **four** axioms — `map_zero'`, `map_one'`, the ultrametric `map_add_le_max'`, and `map_mul'`. This class supplies only the first and last, so it is **not** a one-axiom reduct: dropping `map_one'` is what admits the degenerate constant-`⊤` instance (§ VII-b's NO-GO gauge), and dropping the ultrametric makes the class weaker **on the valuation conditions, over a fixed commutative carrier** — `v n = v₂ n + v₃ n` on `ℤ` satisfies every field here and still fails `min (v 2) (v 3) ≤ v 5`. (That scope matters: across carriers the two are incomparable, per the paragraph above.) Adopting `AddValuation` would remove the degeneracy at the cost of also assuming the ultrametric inequality; that trade has not been made. Note also that `wvs_val 0 = ⊤` is **not** discharged by adoption — `map_zero'` is a structure field there too, so adoption relocates the assumption rather than deriving it.

---

## Custom Types and Definitions

### `OntologicalStates` — `ZeroParadox/Valuation/Padic.lean`

**Relationship to Mathlib:** Replaces `Fin 2`

**Reason:** `Fin 2`'s constructors are `⟨0,_⟩` and `⟨1,_⟩` — natural numbers. `nullState` is not ℕ's 0 by convention; it is a semantic state with no numeric meaning. The free inductive eliminates the ℕ dependency and makes `⊥ ↦ null` a structural fact, not a labelling choice.

---

### `BinaryState` — `ZeroParadox/Information/Surprisal.lean`

**Relationship to Mathlib:** Replaces `Fin 2`

**Reason:** Surprisal is self-contained (no Padic import as a Lean dependency). `BinaryState` is a local copy of the same free-inductive encoding used by `OntologicalStates` in Padic. `Fin 2` would import ℕ arithmetic into an information-theoretic file whose proofs should not depend on it.

---

### `IsQuineAtom` — `ZeroParadox/Settheory/SetTheoryAFA.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Lattice-level analog of Aczel's Quine atom (the unique set satisfying `x = {x}`). No Mathlib definition covers this: it requires `AFAStructure` context and encodes the conjunction of self-containment + uniqueness as a single predicate. Proved equivalent to `q = ⊥` by `t_exec_iff`.

---

### `APG` — `ZeroParadox/Settheory/APG.lean`

**Relationship to Mathlib:** Extends `Mathlib.Combinatorics.Quiver.Basic`

**Reason:** Mathlib's `Quiver` is a bare directed graph (objects + edges) with no distinguished root or accessibility requirement. `APG` adds `root : V` and the accessibility proof (every vertex reachable from root), matching Aczel's definition of Accessible Pointed Graph (1988 p. 4). ⚠ **Neither field is load-bearing for anything proved here, and no claim of necessity should be made in either direction**: `decoration_unique` binds the structure as `_G` and never uses it, so what is proved holds for every finite quiver, accessible or not — which is structurally Aczel's own generality (p. 6). Verified at the binders 2026-08-29; this entry previously claimed both fields were required, contradicting the `[ZP-CUSTOM]` comment it mirrors (`ZeroParadox/Settheory/APG.lean`, corrected 2026-08-09).

---

### `IsKleeneFixedPoint` — `ZeroParadox/Computability/Kleene.lean`

**Relationship to Mathlib:** Replaces `Function.IsFixedPt` (`Mathlib/Logic/Function/Defs.lean`)

**Reason:** `Function.IsFixedPt` works on total functions `α → α`. Here `f : Code → ℕ →. ℕ` (partial function) and the fixed-point condition is `eval c = f c` — equality of partial functions. No Mathlib predicate covers this; `IsKleeneFixedPoint` is the partial-function analog needed for the computability layer.

---

### `IsComputationalQuine` — `ZeroParadox/Computability/Kleene.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Named alias for `IsKleeneFixedPoint selfApply c`. Makes the connection to Quine atoms explicit in type signatures and theorem statements. Unlike the AFA Quine (unique by `quine_unique`), computational quines are not unique — each has a distinct Gödel number, generating the infinite family proved in §VI.

---

### `HasLawvereWitness` — `ZeroParadox/Category/Lawvere.lean`

**Relationship to Mathlib:** Names the hypothesis of `Function.exists_fixed_point_of_surjective` (no Mathlib named predicate)

**Reason:** Mathlib proves Lawvere's fixed-point theorem (`Function.exists_fixed_point_of_surjective`) but exposes no reusable predicate for "β admits a point-surjection α → (α → β)" — the diagonal hypothesis. Naming it lets the face-split state, per face, whether the hypothesis holds (the Set faces are refuted by Cantor; the computability face is genuine). A naming alias in the spirit of `IsComputationalQuine`; no new axiomatic content — every theorem about it reduces to the Mathlib lemma.

---

### `Phase` (with `floorRel`, `phaseRel`, `snap`) — `ZeroParadox/Multihomed/Boundary.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The illustrative single-carrier model for the well-foundedness boundary: `floor` (the self-looping ⊥) and `up : Ordinal → Phase` (the ε₀ ascent), with `phaseRel` self-looping at the floor and following ordinal `<` above it, and `snap := up 0` the irreversible exit. Mathlib has no type bundling a non-well-founded floor with a well-founded ordinal ascent under one relation. The carrier is a *modeling choice* — the boundary theorems' content is the two proven endpoints plus the framework's existing ⊥/ε₀ identification (MC-1, ε₀ open under OQ-E2), not a new commitment; the real-⊥ endpoint (`floorRel` / `floor_not_wellFounded`) is axiom-free on the actual lattice.

---

## Custom Instances

### `machinePhaseZPS` — `ZeroParadox/Order/Snap.lean`
`ZPSemilattice MachinePhase`

The cross-framework bridge. `MachinePhase` is one of two two-element inductives in `ZeroParadox/Information/Surprisal.lean` (the other, `BinaryState`, has its own entry above); giving it a `ZPSemilattice` instance makes T-SNAP (`bot_join` applied to `MachinePhase`) a direct consequence of ZP-A's A4, retiring AX-1 as an axiom. No Mathlib lattice instance exists for `MachinePhase`.

---

### `machinePhaseAFA` — `ZeroParadox/Computability/Kleene.lean`
`AFAStructure MachinePhase`

`selfMem x := x = bot` is the CIC-compatible encoding of AFA self-containment (`⊥ = {⊥}` cannot be stated in Lean's well-founded type theory). `quine_unique` and `bot_self_mem` are provable by `rfl`. This is the concrete closure of DA-1 for ZP-E's machine model.

---

### `machinePhaseKleene` — `ZeroParadox/Computability/Kleene.lean`
`KleeneStructure MachinePhase` (noncomputable)

`botCode` is chosen via `Classical.choose`, so it names SOME computational quine and not a distinguished one; `isComputationalQuine_undecidable` says the MEMBERSHIP PREDICATE is not a `ComputablePred`, which is why nothing can pin down which code was chosen — it does not say no algorithm names a witness, and the constant codes are witnesses. The `noncomputable` marker is load-bearing, not a proof artifact: the non-constructivity is the formal content of DA-1's computational path. Removing it would misrepresent the result.

---

### `instZ2ValBridge` — `ZeroParadox/Valuation/ScaleBridge.lean`
`ValBridge ℤ_[2]`

No `ZPSemilattice ℤ_[2]` is defined — its ring structure supplies no natural join with 0 as bottom — so it does not satisfy `ValuationStructure`, which requires one. ⚠⚠ That is a fact about what is DEFINED, never about what is POSSIBLE. ⚠ Inhabitation is the sole obstruction to `ZPSemilattice` ALONE, not to this class: `valBridge_nonempty_iff` (`ZeroParadox/Valuation/ScaleBridge.lean` § VI) settles membership exactly — infinite, or inhabited and trivial — and `Bool` is inhabited yet admits none. `ℤ_[2]` qualifies by being INFINITE; being a ring is not the obstruction either, and `ZPSemilattice ℕ` exists. What has NOT been located as of 2026-08-30 is a NATURAL join with 0 as bottom — searched over every registered `ZPSemilattice` instance in this corpus. That is an argument about naturality, not possibility. `ValBridge`'s bot-as-plain-field design makes this instance possible. All four axioms delegate directly to theorems proved in `ZeroParadox/Valuation/Scale.lean` §V (`q2Scale_bot`, `q2Val_bot`, `q2Val_unique`, `q2Val_scale`).

---

### `instNatInfZPS` — `ZeroParadox/Settheory/Model.lean`
`ZPSemilattice ℕ∞` with inverted order

Mathlib's `WithTop ℕ` has `≤` as its standard order (`⊤` is maximum). Here `join = min` and `bot = ⊤` — a deliberate reversal. The ZP partial order `x ≤_ZP y ↔ min x y = y` makes `⊤` the bottom (valuation ∞) and `0` the maximum (fully constrained). No Mathlib instance covers this inverted reading.

---

### `instNatInfVal` — `ZeroParadox/Settheory/Model.lean`
`ValuationStructure ℕ∞` (scale = +1, val = id)

The concrete model confirming that `ValuationStructure`'s abstract axioms have an inhabitant. `val = id` works because `ℕ∞` already carries its own depth as its value; `scale = (· + 1)` satisfies `val_scale` by `rfl`.

---

### `instOntZPS` — `ZeroParadox/Settheory/OntBridge.lean`
`ZPSemilattice OntologicalStates`

`OntologicalStates` carries no Mathlib lattice structure. The join (null-identity, exist-absorbing) matches ZP-A's A1–A4 but does not correspond to any Mathlib-provided instance on a two-element type.

---

### `instOntSelfApp` — `ZeroParadox/Settheory/OntBridge.lean`
`AbstractSelfApp OntologicalStates` via constant-to-null map

`OntologicalStates` (two elements) admits no `ValuationStructure` — `no_valBridge_of_finite` (`ZeroParadox/Valuation/ScaleBridge.lean` § VI) proves no finite carrier with two or more points does, because the axioms JOINTLY force the scale orbit to embed ℕ and so force the CARRIER infinite. ⚠ Not because `val` lacks room: its codomain `ℕ∞` is unbounded, and `val_scale` alone is satisfiable on two elements. The direct `AbstractSelfApp` instance using the constant-to-null map (every element → null) is the shorter path to AFA content for finite types.

---

## Further Entries

⚠ These continue the register; the sections above are not exhaustive. (A closing *"Last updated"* footer previously sat here, with further entries after it. Removed rather than re-dated: a single date on a hand-edited register goes stale silently, and each entry carries its own dates where they matter.)

### `IsLeastFixedPointFrom` — `ZeroParadox/Order/LeastFixedPoint.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's least-fixed-point API (`OrderHom.lfp`, `isLeast_lfp`) is fixed to a `CompleteLattice` carrier. This predicate states the SAME mu characterization (least fixed point at or above a seed) over a bare relation, so it applies to the framework's non-lattice carriers — the axiom-clean `ZPSemilattice` L, and `Ordinal`, which is not a complete lattice. It is the order-generic placement schema, grounded back to `OrderHom.lfp` in that file's section II.

### `ProvabilityLogic` — `ZeroParadox/Settheory/Loeb.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** No modal or provability logic was located in the pinned Mathlib as of 2026-08-30 — searched on three axes (Loeb/GL; Kripke and "modal logic"; provability/derivability): `Kripke` and `modal logic` return nothing, every `GL` hit is `GeneralLinearGroup`, and the `provability` hits are first-order material under `ModelTheory/` plus two incidental doc-comments under `Mathlib/Tactic/`. A minimal typeclass carrying just the Hilbert-Bernays-Loeb apparatus, so that Loeb's theorem can be presented as a face of the diagonal family.

### `QuineHost` — `ZeroParadox/Settheory/QuineHost.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` carries Foundation (`ZFSet.mem_wf`), which forbids `x in x` and so cannot host a Quine atom; and no Mathlib typeclass abstracts "a membership relation with a unique self-membered bottom." `QuineHost` is the minimal set-theory-native encoding of the framework's requirements on a host theory (fields `bot_selfMem` / `selfMem_unique`), distinct from the lattice-level `AFAStructure` in `SetTheoryAFA.lean`.

### `trivialSelfApp` — `ZeroParadox/Computability/SelfApp.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** A deliberately degenerate `AbstractSelfApp` witness — the constant-bottom self-application — built to bound what the typeclass hypothesis can be made to yield. Not a modelling instance but a NO-GO gauge: it shows every `ZPSemilattice` carries an `AbstractSelfApp`, so no property of the carrier follows from the bare hypothesis. Mathlib has no notion of a deliberately vacuous instance of a project-local class.

### `LoopsInPlace` — `ZeroParadox/Computability/Occurrence.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Names the self-looping configuration of a state-transition function (`f s = some s`) as a first-class predicate, so the trichotomy and the trap result can be stated about it. Mathlib's `Computability/StateTransition.lean` supplies `Reaches` and `eval` but no name for "steps to itself", which is the case that turns out to be the self-referential object rather than a third route.

### `IsComputationalBottom` — `ZeroParadox/Computability/Occurrence.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Bundles the framework's own two requirements on the computational bottom — that it is a fixed point of its own step, and that the snap departs from it — so their joint satisfiability can be decided. Framework-specific by construction; no Mathlib notion corresponds. The bundle is proved uninhabited (`machine_snap_impossible`), which is the point of naming it.

### `Occurs` — `ZeroParadox/Computability/Occurrence.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Names the framework's "the transition fires" as a step-indexed predicate on codes (`∃ k, evaln k c n ≠ none`), so the classical halting results apply to it. Mathlib carries the halting predicate (`ComputablePred.halting_problem`) but not this reading of it; the identification of framework-occurrence with this predicate is the framework's modelling choice and is fenced as such at the definition.

### `Extremal` — `ZeroParadox/Computability/Occurrence.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Names the two-element computational pole — a configuration is extremal when it is halted or looping in place — so the pole swap can be shown to preserve it as a set. Mathlib's `Computability/StateTransition.lean` has `Reaches` and `eval` but no notion of "sits at one of the two extremes of a state-transition function".

### `flipPoles` — `ZeroParadox/Computability/Occurrence.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The computational analogue of `rInv` / `swap` — an involution on step functions that exchanges the halted and self-looping poles while fixing every configuration that steps onward. Mathlib has no such operation on `σ → Option σ`. Fenced at the definition: it is an automorphism of the SPACE of machines, not of one machine, so it is the same shape at a different level and never a cross-type identity.


### `stepCoalg` — `ZeroParadox/Computability/GroundZero.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The connector between a `StateTransition`-style step function `σ → Option σ` and the framework's own `natPF_NatListRegime` presentation of the polynomial functor `X ↦ 1 + X`. Mathlib carries both sides — `Computability/StateTransition.lean` and `Data/QPF/Univariate/Basic.lean` — and no map between them, because the two live in unrelated corners of the library. This is that bridge, and it is where the framework's operational face (`Occurrence.lean`) meets its coalgebraic one (`NatListRegime.lean`). The construction itself is standard: reading a partial step function as a `1 + X`-coalgebra is textbook (Jacobs, *Introduction to Coalgebra*, Ch. 2), and no novelty is claimed for it.

### `streamPF` — `ZeroParadox/Computability/OutputSeparates.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The two-element-head chain polynomial functor `⟨Bool, fun _ => PUnit⟩`, held at the same arity as `idPF_Coalgebra` so that the head type is the only thing varying against `binPF`. Its final coalgebra is the `Bool`-streams. Mathlib has `Stream'` and it has `PFunctor`/`QPF`, and it connects them nowhere: `Stream` appears zero times under `Mathlib/Data/QPF/` and `Mathlib/Data/PFunctor/`, and `PFunctor`/`QPF` zero times under `Mathlib/Data/Stream/`. No novelty is claimed — the cardinality of its final coalgebra is Rutten, TCS 249 (2000), Example 10.2(5), p. 44 (`A^{B*}`), cited not reproved.

### `TriStep` — `ZeroParadox/Computability/GroundZero.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** A deliberate COUNTER-MODEL, not a construction to build on: a three-valued step outcome (halted / idle / stepping) whose only purpose is to be the carrier in which the § I forcing fails. Mathlib has no three-valued step outcome because there is no reason to want one. It must never be used as a framework object.

**Prior art (added 2026-07-27):** the halted-versus-idle distinction is the ACP split between *successful termination* and *deadlock* (Baeten & Weijland, *Process Algebra*, 1990) - process algebra calls the third value **deadlock**, where the framework reads it as *unstarted*. Same object, opposite valence; the standard term should lead in any reader-facing prose.
