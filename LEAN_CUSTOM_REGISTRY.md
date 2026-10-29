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

**Reason:** Mathlib's `ZFSet` uses the Axiom of Foundation, which forbids `x ∈ x` (`ZFSet.mem_irrefl`). No `ZFSet` element can satisfy `x ∈ x`, so a Quine atom is not directly available as a `ZFSet` — AFA content is still MODELLABLE over a well-founded universe, as Aczel does via decorations of accessible pointed graphs (see the `APG` entry). `AFAStructure` is the lattice-level encoding of what ZF+AFA provides set-theoretically, with `selfMem` / `quine_unique` / `bot_self_mem` as the three minimal class fields.

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

**Reason:** Bridges `AFAStructure` (set-theoretic self-containment) with Mathlib's computability library (`Nat.Partrec.Code`). No Mathlib typeclass connects AFA and `Code`. `KleeneStructure` is built for the reading that the AFA Quine atom and the Kleene computational Quine (`∃ c, eval c = f c`) name the same structural property — this identification is the motivating commitment, not a derived theorem, and no field asserts it.

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

**Reason:** Mathlib's `ZFSet` uses Foundation — `x ∈ x` is forbidden, making it invalid as a decoration target for any APG with a self-loop. `DecorationUniverse` is an abstract type with `ValuationStructure` plus a `collect` operation and two axioms (`collect_singleton`, `collect_val_ge`), providing the structure the decoration-uniqueness proof consumes, without importing `ZFSet` or any axiomatic set theory. ⚠ It is NOT axiom-free, and every attribution below was isolated by changing ONE constituent rather than reasoned from the signature. `DecorationUniverse` reaches `Classical.choice` by **two INDEPENDENT routes**: its OWN `ℕ∞` numeral (the `+ 1` in `collect_val_ge`) and the inherited `[ValuationStructure U]`, whose own route is the numeral in `val_scale` (pinned by the `_VSlit`/`_VScast` pair in `ZeroParadox/Valuation/Scale.lean`). Neither alone accounts for it: with `[ValuationStructure U]` DELETED and `val`/`scale` passed as plain data the class still reports `[propext, Classical.choice, Quot.sound]`; with `[ValuationStructure U]` also deleted, respelling its own numeral as `((1 : ℕ) : ℕ∞)` makes it report no axioms at all; and respelling only that numeral with the real binders kept leaves it tainted. ⚠⚠ `decoration_unique` carries the same three **IN ITS STATEMENT**: `∀ {U} [ZPSemilattice U] [ValuationStructure U], True` already reports them, while the same with `[ZPSemilattice U]` alone reports none — so the `[ValuationStructure U]` binder is sufficient by itself and the cost is **NOT REMOVABLE BY ANY PROOF** of that theorem. Its proof additionally CALLS `Nonempty.some`, which unfolds to `fun h => Classical.choice h`, and reaches choice through `Set.ncard_pos` and `Set.ncard_lt_ncard`, but those are further routes to a cost the TYPE has already incurred. Provenance and necessity are independent axes (`ZeroParadox/AxiomProfile.lean` § 0). ⚠ "Minimum" is also unproved: the NO-GO gauge in `ZeroParadox/Settheory/APG.lean` records the class is inhabited over EVERY `ValuationStructure` carrier.

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

**Reason:** Mathlib's `Quiver` is a bare directed graph (objects + edges) with no distinguished root. `APG` adds `root : V` and the accessibility proof (every vertex reachable from root), which is Mathlib's separate class `Quiver.RootedConnected root` (`Mathlib/Combinatorics/Quiver/Arborescence.lean`; the two `example`s below the structure in `ZeroParadox/Settheory/APG.lean`), matching Aczel's definition of Accessible Pointed Graph (1988 p. 4). ⚠ **Neither field is load-bearing for anything proved here, and no claim of necessity should be made in either direction**: `decoration_unique` binds the structure as `_G` and never uses it, so what is proved holds for every finite quiver, accessible or not — which is structurally Aczel's own generality (p. 6). Verified at the binders 2026-08-29; this entry previously claimed both fields were required, contradicting the `[ZP-CUSTOM]` comment it mirrors (`ZeroParadox/Settheory/APG.lean`, corrected 2026-08-09).

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

**Reason:** The illustrative single-carrier model for the well-foundedness boundary: `floor` (the self-looping ⊥) and `up : Ordinal → Phase` (the ε₀ ascent), with `phaseRel` self-looping at the floor and following ordinal `<` above it, and `snap := up 0` the irreversible exit. Mathlib has no type bundling a non-well-founded floor with a well-founded ordinal ascent under one relation. The carrier is a *modeling choice* — the boundary theorems' content is the two proven endpoints plus the reading of those endpoints as ZP's own ⊥ (the lattice chart's ⊥) and ε₀ respectively, a role assignment the framework already carries (for the ⊥ endpoint, MC-1 family membership; for the ε₀ endpoint, theorems about the model itself in both of its extreme orderings, floor below as `WithBot Ordinal` (`phase_epsilon0_isLeast_landing_above_floor`) and floor above as `WithTop Ordinal` (`phaseTop_epsilon0_isLeast_landing_above_snap`) (`ZeroParadox/Multihomed/BoundaryOrder.lean`), so no cross-type identity is involved), not a new commitment. In the carrier `Ordinal` the bottom role is filled by 0. The value `Ordinal.epsilon 0`, lifted as `↑ε₀`, fills the ε₀ role, the first landing (a fixed point of the closure) strictly above a floor: in `WithBot Ordinal`, above the boundary model's floor placed at the bottom (`phase_epsilon0_isLeast_landing_above_floor`), and in `WithTop Ordinal`, where that floor is placed at the top, the first landing strictly above that order's least element, the snap `↑0` (`phaseTop_epsilon0_isLeast_landing_above_snap`; both `ZeroParadox/Multihomed/BoundaryOrder.lean`). In `Ordinal` that value differs from the bottom role's occupant 0 (`epsilon0_ne_bot`, `epsilon0_ne_zero`). The lattice chart's ⊥ endpoint (`floorRel` / `floor_not_wellFounded`) is axiom-free on the actual lattice.

---

## Custom Instances

### `machinePhaseZPS` — `ZeroParadox/Order/Snap.lean`
`ZPSemilattice MachinePhase`

`MachinePhase` is one of two two-element inductives in `ZeroParadox/Information/Surprisal.lean` (the other, `BinaryState`, has its own entry above); giving it a `ZPSemilattice` instance makes T-SNAP (`bot_join` applied to `MachinePhase`) a direct consequence of ZP-A's A4. AX-1 is retired: its shape is proved as T-SNAP, and that the snap occurs is stated separately: it follows from the occurrence commitment (instantiation occurs) together with DA-1 (closed given DP-2). No Mathlib lattice instance exists for `MachinePhase`.

---

### `machinePhaseAFA` — `ZeroParadox/Computability/Kleene.lean`
`AFAStructure MachinePhase`

`selfMem x := x = bot` is the CIC-compatible encoding of AFA self-containment (`⊥ = {⊥}` cannot be stated in Lean's well-founded type theory). `quine_unique` and `bot_self_mem` are provable by `rfl`. This is the concrete Lean counterpart of Path 1 for ZP-E's machine model; DA-1 itself is closed given DP-2 (`da1_minimal_path`).

---

### `machinePhaseKleene` — `ZeroParadox/Computability/Kleene.lean`
`KleeneStructure MachinePhase` (noncomputable)

`botCode` is chosen via `Classical.choose`, so it names SOME computational quine and not a distinguished one; `isComputationalQuine_undecidable` says the MEMBERSHIP PREDICATE is not a `ComputablePred`, which is why nothing can pin down which code was chosen — it does not say no algorithm names a witness, and the constant codes are witnesses. The `noncomputable` marker comes from this instance's choice of `botCode`; a computable instance with a constant code also satisfies the class, so the noncomputable marker belongs to the instance, not to DA-1's computational path.

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

### `UpAndOver` — `ZeroParadox/Order/UpAndOver.lean`

**Relationship to Mathlib:** Has a `ClosureOperator` field; no Mathlib analog for the bundle

**Reason:** Mathlib's `ClosureOperator` admits the identity closure and the constant-top closure, and says nothing about covers. This structure bundles one with two fields: `corner`, a closed point with a cover in the carrier order (`CovBy`) that the closure moves, and `cover`, a cover at every non-maximal closed point. That some point moves and some closed point is not maximal are theorems (`UpAndOver.moves`, `UpAndOver.open_landing`). The cover in `corner` refuses every densely ordered carrier (`isEmpty_of_denselyOrdered`), so the ceiling map on ℝ, a closure operator, fails both fields; density is sufficient for that exclusion, not necessary, since `Bool` is refused too. Each of `corner` and `cover` refuses a control in that file's section III that the other passes. The three-point chain `Fin 3` is a member, and `corner` alone gives a three-point chain, so a finite member has at least three points.

### `ProvabilityLogic` — `ZeroParadox/Settheory/Loeb.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** No modal or provability logic was located in the pinned Mathlib as of 2026-08-30 — searched on three axes (Loeb/GL; Kripke and "modal logic"; provability/derivability): `Kripke` and `modal logic` return nothing, every `GL` hit is `GeneralLinearGroup`, and the `provability` hits are first-order material under `ModelTheory/` plus two incidental doc-comments under `Mathlib/Tactic/`. A minimal typeclass carrying just the Hilbert-Bernays-Loeb apparatus, so that Loeb's theorem can be presented as a face of the diagonal family.

### `QuineHost` — `ZeroParadox/Settheory/QuineHost.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` carries Foundation (`ZFSet.mem_wf`), which forbids `x in x`, so no `ZFSet` meets `bot_selfMem`; and no Mathlib typeclass abstracts "a membership relation with a self-membered bottom that is the only self-membered element." `QuineHost` encodes a self-membered bottom with uniqueness among self-members (fields `bot_selfMem` / `selfMem_unique`: ⊥ ∈ ⊥ and no other element self-membered), distinct from the lattice-level `AFAStructure` in `SetTheoryAFA.lean`. Under AFA's own membership its uniqueness field fails, since 0* = {∅, 0*} is self-membered (Aczel 1988, Example 1.5, p. 7); the framework's requirement in AFA's profile is `QuineAtomHost`, below.

### `QuineAtomHost` — `ZeroParadox/Settheory/QuineHost.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The framework's host requirement (CC-2) in AFA's profile: `bot_mem_iff` (the members of ⊥ are exactly ⊥, ⊥ = {⊥}) and `reflexive_unique` (the only element that is its own only member is ⊥), the uniqueness AFA gives (Aczel 1988, p. 19). It stands alone and is incomparable with `QuineHost` (both directions witnessed in `QuineHost.lean` § VII). Mathlib's `ZFSet` cannot host it (`zfSet_no_singleton_bottom`), and no Mathlib typeclass abstracts a membership relation with a unique reflexive bottom.

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

**Reason:** The two-element-head chain polynomial functor `⟨Bool, fun _ => PUnit⟩`, held at the same arity as `idPF_Coalgebra` so that the head type is the only thing varying against `binPF`. Its final coalgebra is the `Bool`-streams. Mathlib has `Stream'` and it has `PFunctor`/`QPF`; a connection between them was not located in the pinned Mathlib as of 2026-10-13, searched as follows: `Stream` appears zero times under `Mathlib/Data/QPF/` and `Mathlib/Data/PFunctor/`, and `PFunctor`/`QPF`/`Cofix` zero times under `Mathlib/Data/Stream/`. No novelty is claimed — the cardinality of its final coalgebra is Rutten, TCS 249 (2000), Example 10.2(5), p. 44 (`A^{B*}`), cited not reproved.

### `TriStep` — `ZeroParadox/Computability/GroundZero.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** A deliberate COUNTER-MODEL, not a construction to build on: a three-valued step outcome (halted / idle / stepping) whose only purpose is to be the carrier in which the § I forcing fails. Mathlib has no three-valued step outcome because there is no reason to want one. It must never be used as a framework object.

**Prior art (added 2026-07-27):** the halted-versus-idle distinction is the ACP split between *successful termination* and *deadlock* (Baeten & Weijland, *Process Algebra*, 1990) - process algebra calls the third value **deadlock**, where the framework reads it as *unstarted*. Same object, opposite valence; the standard term should lead in any reader-facing prose.

### `Motion` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Without the `up_idem` law, the pair is a Mathlib `Endofunctor.Coalgebra` for `FunctorToTypes.prod (ofTypeFunctor Part) (ofTypeFunctor Set)`; no Mathlib analog for that law on the `Part` component

**Reason:** Mathlib carries each part separately, a partial function (`PFun`) and a relation. As a coalgebra the pair is standard: a motion on `α` is the same as a map `α → Part α × Set α` whose `Part` component satisfies `up_idem`'s law (`motionEquiv`, an `Equiv` with both round trips by `rfl`, `ZeroParadox/Die.lean` § XX), and coalgebras with their homomorphisms are Rutten, "Universal coalgebra", TCS 249 (2000), pp. 8–10 (p. 10 treats labelled transition systems; the die's `Set` half is the one-label case). What is not standard is the law: a coalgebra whose structure map has an idempotent component was not located as of 2026-10-28, searched as follows: theoremsearch in six phrasings (four at the probe, counted but not recorded verbatim; two at landing: "coalgebra for the functor partial map times powerset whose partial component is idempotent"; "transition system together with an idempotent partial retraction onto its fixed points, homomorphism preserves both"); the extracted text of Rutten 2000 for "idempot" (no hit); the text and HTML files of the project's papers library (its local copies of retrieved papers and pages, `.claude-local/papers`) for "idempotent" (two hits, nLab's closure operator and nucleus pages, neither about coalgebras); and one open-web search (2026-10-28), no hit. The phrase "idempotent coalgebra" is in use for a different object: Hogancamp, "Constructing categorical idempotents", arXiv:2002.08905, Def. 3.3 (p. 7), a complex `P` in the homotopy category `K⁻(A)` with a chain map `ε : P → 1` such that `P ⋆ Cone(ε) ≃ 0 ≃ Cone(ε) ⋆ P` (`⋆` the monoidal product there), which determines a two-step idempotent decomposition of the identity (Obs. 3.5, p. 8); it is an object idempotent under that product up to homotopy, not a structure map on states. The law is closed under homomorphic images and one-to-one sources (`idem_of_surj`, `idem_of_inj`); closure under sums, the third covariety condition (Rutten p. 7, Theorem 17.3 p. 64), is not built. For the law, the nearest prior art located is rewriting logic's split of equations from rules (Meseguer, "Generalized Rewrite Theories and Coherence Completion", *Rewriting Logic and Its Applications*, LNCS, 2018, pp. 164–183, doi 10.1007/978-3-319-99840-4_10, bibliographic record checked at Crossref 2026-10-18; Def. 8, p. 10, pages being those of the 28-page copy read, which prints no venue and is not paginated as the LNCS text; R. Diaconescu, "Non-Deterministic Algebraic Rewriting as Adjunction", arXiv:2204.12133, Defs. 11–12). There the map beside the rules is total: in Meseguer the normal form modulo the axioms B of a convergent equation system, in R. Diaconescu (Def. 11) a homomorphism into a subset it fixes. Meseguer requires coherence for the canonical system to be faithful to the rules (p. 11, with Theorem 4); the counterpart condition in R. Diaconescu is β-coherence (Def. 12, a hypothesis of his Props. 5.1 and 5.5), to which he says the Maude literature's coherence conditions bear "some similarity" while playing "a different role" (p. 26). Neither is imposed here. A structure pairing a partial map whose every value is a fixed point, not required to be total or to come from equations, with a step relation was not located as of 2026-10-17, searched for the pair as follows: theoremsearch in six vocabularies (structural, categorical, coalgebraic, rewriting, dynamics, iteration theory) and three web searches. The pair is a record: every type carries one, recorded as a NO-GO gauge beside the declaration; its premises are indexed in `ZeroParadox/DieCannotBe.lean`.

### `MemGraph` — `ZeroParadox/Settheory/GraphBisim.lean`

**Relationship to Mathlib:** Extends `Mathlib.Combinatorics.Digraph.Basic`

**Reason:** Mathlib's `Digraph (Fin n)` already has a Prop-valued `Adj`; it lacks only the distinguished point, and `MemGraph n ≃ Digraph (Fin n) × Fin n` (the second `example` below the structure in `ZeroParadox/Settheory/GraphBisim.lean`). Kept as its own structure so `edge` reads member-to-set at every use site. `Quiver` edges are Type-valued, and as the corpus's `APG` (`ZeroParadox/Settheory/APG.lean`) uses them they point set to member, while `Acc` and bisimulation across two carriers want this Prop-valued member-to-set relation.

### `keepAboveKernel` — `ZeroParadox/Order/UpAndOver.lean`

**Relationship to Mathlib:** A `ClosureOperator` on the order dual; no named Mathlib declaration for it

**Reason:** Several of Mathlib's constructors build a `ClosureOperator` from a map with its laws or from a predicate, e.g. `ClosureOperator.mk'` (a map), `ClosureOperator.ofPred` (a map and a closedness predicate) and `ClosureOperator.ofCompletePred` (a predicate closed under infima in a complete lattice); others take other inputs (`ClosureOperator.id`, `ClosureOperator.conjBy`, `GaloisConnection.closureOperator`). This is the two-point kernel with closed points `{e, a}`, sending `x` to `a` if `a ≤ x` and to the least point `e` otherwise, in a partial order with decidable `≤` and a least point `e`; it supplies the UP of `nonempty_upAndOver_dual_of_covBy`. In `αᵒᵈ` the set `{e, a}` is a closure system in the sense of Glück, "Isolated Suborders and Their Application to Counting Closure Operators", LMCS 20(3), 2024, Def. 3.3, p. 11:4 (with Lemma 3.6, one closure operator per closure system). As a named Mathlib declaration it was not located as of 2026-10-21, searched as follows: `exact?` on the existence of a closure operator on `αᵒᵈ` with that value (no result); grep of the pinned Mathlib for `InteriorOperator`, "interior operator", "kernel operator" and "coclosure" (no hit); the constructor list of `Mathlib/Order/Closure.lean` read; the Galois-connection route, where every closure operator is the one of its own Galois insertion into its closed points (`ClosureOperator.gi`, `closureOperator_gi_self`), so that route names no particular kernel.

### `ordinalCornerStep` — `ZeroParadox/Order/UpAndOver.lean`

**Relationship to Mathlib:** No Mathlib analog; built from `Ordinal.nfp` and `Order.succ`

**Reason:** The corner composite of `ordinalSuccMotion`, `a ↦ nfp (ω^·) (succ a)` on every ordinal; iterated `n + 1` times from 0 it gives `ε_n` (`ordinalCornerStep_iterate`). Mathlib's `Ordinal.deriv_succ` has this shape only at the values of `Ordinal.deriv` (`deriv f (succ o) = nfp f (succ (deriv f o))`). As a named Mathlib declaration the map was not located as of 2026-10-21, searched as follows: the `def`s of `Mathlib/SetTheory/Ordinal/FixedPoint.lean` and `Veblen.lean` listed, and a grep of both for `nfp` applied to a successor or `+ 1` (hits: `deriv_add_one`, `deriv_succ`, `epsilon_succ_eq_nfp`, `gamma_succ_eq_nfp` and one `nfp (a * ·)` lemma, none a definition).

### `DieSelfCopyRef` — `ZeroParadox/Computability/SelfCopyReference.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** `SelfCopyRef` (one-to-one, not onto, exactly one fixed point) restated in the die's vocabulary on `Motion.ofFun g`: no point has fan-in, some point has no predecessor, exactly one point steps to itself only. Mathlib has the function-side notions (`Function.Injective`, `Function.Surjective`, `Function.IsFixedPt`) and not the die's, which is project-local (`Motion`, above). The two forms are related in both directions in that file, with their footprints printed.

### `Motion.restrict` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** OVER is Mathlib's `Subrel`; no Mathlib analog for UP's codomain restriction

**Reason:** The motion on the subtype of a set `S` that UP's values stay in (`UpClosed`): UP keeps its domain and its value, now as a point of `S`; OVER is `Subrel M.step (· ∈ S)`, the steps between points of `S`. Mathlib restricts a `PFun` on its DOMAIN (`PFun.restrict`, a subset of `Dom`), turns a total map into a partial one with a predicate as domain (`PFun.toSubtype`), and replaces a `Part`'s domain (`Part.restrict`). A codomain restriction of a `PFun` to a set its values lie in was not located as of 2026-10-21, searched as follows: the `def`s of `Mathlib/Data/PFun.lean` and `Mathlib/Data/Part.lean` listed (`restrict`, `toSubtype`; `Part.restrict`), and a grep of both for `codRestrict` (no hit). The inclusion maps are Mathlib's `Subrel.relEmbedding` and `Subrel.inclusionEmbedding`.

### `Motion.Arrives` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Neighbours `Relation.ReflTransGen`, `StateTransition.EvalsTo`, `Acc`; no Mathlib analog for a relation step

**Reason:** `x` arrives at `y` when `x = y`, or `x` has a step and every step from `x` lands at a point that arrives at `y`. This implies that every run from `x` passes through `y` (`exists_run_eq_of_arrives`, axiom-free), and the converse holds classically given `[DecidableEq α]` and a step at every point other than `y` (`arrives_of_forall_run`, through Mathlib's `not_acc_iff_exists_descending_chain`; the two together are `arrives_iff_forall_run`). Read against CTL, `Arrives y` is the inevitability `AF` at "is `y`" in its least-fixpoint form, with the structure's totality requirement carried inside the predicate (Clarke–Emerson 1981, p. 55; Emerson 1990, § 8.4 in the author's preprint, the published Handbook chapter's numbering not checked; cited in `ZeroParadox/DieCannotBe.lean` § XVI). Mathlib's `Relation.ReflTransGen` and `StateTransition.Reaches` state that SOME path reaches `y`; `StateTransition.EvalsTo` (`Mathlib/Computability/StateTransition.lean`) records that an `Option`-valued FUNCTION's iterates reach a value, the single-run case, matching `arrives_ofFun_iff` here. For a relation, arrival is `Acc` of the step with `y` removed as a source, given a step at every other point and `DecidableEq` (`acc_of_arrives`, `arrives_of_acc`). A Mathlib notion of every run reaching a point was not located as of 2026-10-21, searched as follows: Mathlib declaration names matching `reaches`, `Reaches`, `inevitab`, `attract` and `eventuallyReach`, and a grep for "AF ", "eventually reach", "inevitab" (the one relevant hit is `EvalsTo`'s docstring).

### `Motion.accHeight` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Neighbour `Acc.rank` (`Mathlib/SetTheory/Ordinal/Rank.lean`); no Mathlib analog for the `ℕ∞`-valued total form

**Reason:** For a relation `r`, `Set.ncard` of the strict descendants of an accessible point (their number on a finite carrier; `Set.ncard` is 0 on an infinite set), and ⊤ of `ℕ∞` at a point that is not accessible. Mathlib's `Acc.rank` is `Ordinal`-valued and takes the `Acc` proof as an argument, so it is undefined off the accessible part; the die's ranks are total `α → ℕ∞` maps dropping by at least one per step (`rank_eq_top_of_cycle`), and on a finite carrier `accHeight` is such a rank (`accHeight_drops`); it is finite exactly at the accessible points (`accHeight_ne_top_iff`), so on a finite carrier every such rank is ⊤ of `ℕ∞` at `a` iff `a` is not accessible (`forall_rank_eq_top_iff_not_acc`). `exact?` found no Mathlib lemma for the accessibility facts it rests on as of 2026-10-21 (`¬ s c c` from `Acc s c`; `Acc` passing down `ReflTransGen`; a point on a `TransGen` cycle is not accessible); a grep of the pinned Mathlib for theorems named `acc_*`, `*_acc` and `Acc.*` lists `acc_def`, `exists_not_acc_lt_of_not_acc`, `acc_iff_isEmpty_descending_chain`, `RelEmbedding.not_acc` and others, none of these three.

### `PoleEnds` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Built from Mathlib's `IsBot` and `IsTop`; no Mathlib analog for the pair as a cell

**Reason:** Under one `≤`, whether a least point exists and whether a greatest point exists, as a cell indexed by two `Bool`s, so that the order dual's exchange of the two answers is one lemma (`poleEnds_of_dual`). Mathlib's `OrderBot` and `OrderTop` are data and `∃ x, IsBot x` is a single proposition. A definition pairing the two was not located as of 2026-10-21, searched as follows: a grep of `Mathlib/Order/` for `def`, `abbrev`, `class` and `structure` lines naming both `IsBot`/`OrderBot` and `IsTop`/`OrderTop` (one hit, `orderIsoRangeOfLinearSuccPredArch`, not a cell).

### `Motion.closedSublattice` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Built with `CompleteSublattice.mk'`

**Reason:** The sets closed under a motion's UP and OVER, closed under arbitrary unions and intersections, hence a `CompleteSublattice (Set α)`. Mathlib supplies the constructor; the family of sets is the die's.

### `Motion.instLE` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** No Mathlib analog; a `PartialOrder` on the die's own record

**Reason:** `M ≤ N` when the UP legs are equal and every step of `M` is a step of `N`. Mathlib orders relations pointwise (`≤` on `α → α → Prop`) and has no order on the pair of a partial map and a relation, which is project-local (`Motion`, above). A Mathlib `PartialOrder` instance on a structure carrying a relation was not located as of 2026-10-21, searched as follows: a grep of `Mathlib/Order/` for `instance` lines giving `PartialOrder` or `LE` on a relation-valued type (one hit, `RelUpperSet`, upper sets, not relations).

### `IsLeastFixedPointUpTo` — `ZeroParadox/Order/LeastFixedPoint.lean`

**Relationship to Mathlib:** Extends `IsLeastFixedPointFrom` (same file)

**Reason:** The schema `IsLeastFixedPointFrom` with its equation `f mu = mu` passed as a relation `e`, so a carrier whose fixed points hold only up to `≃` (`Type`, with `Option`) meets the same three fields; `upTo_eq_iff` recovers the original at `e = Eq`. The reason `IsLeastFixedPointFrom` itself has no Mathlib analog is recorded in that file.

### `Motion.toNucleus` — `ZeroParadox/Category/DieNucleus.lean`

**Relationship to Mathlib:** Extends `Mathlib.Order.Nucleus`

**Reason:** On a meet-semilattice (`SemilatticeInf`, what Mathlib's `Nucleus` takes), a die motion whose UP is total, raises, and preserves `⊓` gives the `Nucleus` `x ↦ up x`; idempotence comes from the `Motion` field `up_idem`. On bare `Ordinal` it returns `snapNucleus` from `ordinalTowerMotion` (`toNucleus_ordinalTowerMotion`). Mathlib supplies `Nucleus`; the die's `Motion` is project-local.

### `Motion.ofNucleus` — `ZeroParadox/Category/DieNucleus.lean`

**Relationship to Mathlib:** Extends `Mathlib.Order.Nucleus`

**Reason:** The inverse reading of `Motion.toNucleus`: a `Nucleus` with any OVER relation gives a motion through `Motion.ofTotal`; the round trip returns the nucleus (`toNucleus_ofNucleus`).

### `PoleEndsInhabited` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Extends `PoleEnds` (same file) with Mathlib's `Nonempty`

**Reason:** `PoleEnds` puts `Empty` and ℤ in the same cell `(false, false)`; adding whether the carrier is inhabited as a third `Bool` separates them, and the order dual keeps that answer (`poleEndsInhabited_dual`). Why `PoleEnds` has no Mathlib analog is recorded in its entry above.

### `Motion.StepCompat` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Neighbours `StateTransition.Respects`, `Relation.Fibration`, `Quotient.map'`, and `IsBisimulation` for `Stream'`, `Seq`, `Computation`; no Mathlib analog for a relation step and a setoid

**Reason:** A setoid `s` is step-compatible with a motion when related starts have related successors: `s a a'` and a step `a → b` give a step `a' → b'` with `s b b'`. Since `s` is symmetric this gives the back clause as well, so a step-compatible setoid is a bisimulation of the step (the `example` after `StepCompat` in `ZeroParadox/DieCannotBe.lean` § XXII; the standard notion as cited in `ZeroParadox/Settheory/GraphBisim.lean`: Aczel 1988, p. 20, Park via Aczel). With it, the quotient's OVER (`Motion.quot`) is read off any representative (`quot_step_mk_iff`). Mathlib's `StateTransition.Respects` (`Mathlib/Computability/StateTransition.lean`) is a refinement between two `Option`-valued step functions, matched in one or more steps; `Relation.Fibration` lifts steps along a map in the other direction; `Quotient.map'` takes a function, whose hypothesis form `stepCompat_ofFun` adopts. A relation-and-setoid form was not located as of 2026-10-21, searched as follows: a grep of the pinned Mathlib for `def` lines named `IsBisimulation`, `IsSimulation`, `Simulation`, `StepCompat` or `Respects` (hits: `StateTransition.Respects`, and `IsBisimulation` for `Stream'`, `Seq` and `Computation`, each for its own type), the same names on `structure` lines (one further hit, 2026-10-21: `structure IsBisimulation` in `Mathlib/Data/PFunctor/Univariate/M.lean`, on M-types, a relation between trees with head and tail clauses, again for its own type), and `Mathlib/Logic/Relation.lean` read for `Map` and `Fibration`.

### `Motion.quot` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** OVER is Mathlib's `Relation.Map` along `Quotient.mk`

**Reason:** The motion on the classes of a setoid: UP the identity, OVER the image of the step under the class map, `Relation.Map M.step (Quotient.mk s) (Quotient.mk s)`. Mathlib supplies the image relation; the pairing with an identity UP is a `Motion`, the die's project-local structure (`ZeroParadox/Die.lean` § I), so the wrapper is ours. The original UP is not carried to the classes.

### `Motion.UpCompat` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** The UP-leg twin of `Motion.StepCompat`; `Quotient.map'`'s hypothesis is its total, single-valued case (`upCompat_ofTotal`); no Mathlib analog for a partial map (`Part`) and a setoid

**Reason:** A setoid `s` is UP-compatible with a motion when related points have related UP values: `s a a'` and `y ∈ up a` give `y' ∈ up a'` with `s y y'`. With it, `up` descends to the classes (`upCompat_map_eq`, `quotUp`). A `Part`-valued respect condition was not located as of 2026-10-21, searched as follows: `Mathlib/Data/PFun.lean` and `Mathlib/Data/Part.lean` grepped for `Quotient`, `Quot.` and `Setoid` (no hits), and the pinned Mathlib grepped for `Part (Quotient`, `→. Quotient`, `Quotient … →.`, and `Part.map` / `Quotient.lift` combined on one line (no hits).

### `Motion.quotUp` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** UP is Mathlib's `Quotient.lift` of `Part.map (Quotient.mk s) ∘ up`; OVER is `Motion.quot`'s `Relation.Map`

**Reason:** The motion on the classes of an UP-compatible setoid: UP sends the class of `a` to the class of `up a` (defined iff `up a` is), and `up_idem` descends. Mathlib supplies the lift and `Part.map`; the result is a `Motion`, the die's project-local structure (`ZeroParadox/Die.lean` § I), so the wrapper is ours (the dated search for a `Part`-valued respect condition is recorded under `Motion.UpCompat`). With the identity UP it is `Motion.quot` (`quotUp_eq_quot`).

### `Motion.Hom` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** OVER is Mathlib's `RelHom` condition and UP is Mathlib's `Endofunctor.Coalgebra.Hom` condition for `ofTypeFunctor Part`; with the back clause added the pair is Mathlib's `Endofunctor.Coalgebra.Hom` for `FunctorToTypes.prod (ofTypeFunctor Part) (ofTypeFunctor Set)`; without it, no Mathlib analog for the pair

**Reason:** A strict map of motions: a map carrying steps to steps (`RelHom`'s condition) such that UP at `f x` is UP at `x` mapped by `f` (`UpStrict`), the UP square commuting in Par. Mathlib supplies both halves separately: `RelHom` for the step, and `CategoryTheory.Endofunctor.Coalgebra.Hom` for the functor `Part` for UP (the `example` after `UpStrict`, `ZeroParadox/Die.lean` § XIX, both directions). The pairing of the two is over `Motion`, the die's project-local structure (`ZeroParadox/Die.lean` § I). The back clause, when wanted, is the separate `Motion.StepBack`, which is Mathlib's `Relation.Fibration` of the reversed steps (`Iff.rfl`, `ZeroParadox/Die.lean` § XIX). A map `f` underlies a coalgebra homomorphism between the motions read as coalgebras for `Part × Set` iff it is a strict map with the back clause (`coalgHom_iff`, both directions, `ZeroParadox/Die.lean` § XX); on the `Set` half that is Rutten's homomorphism (TCS 249 (2000), p. 10). A strict map without the back clause need not be one (the `Unit` control after `coalgHom_iff`), so `Motion.Hom` alone is the weaker notion; the § XIX transfers that do not use the back clause are stated along it. A map of the pair (partial map, step relation) without the back clause was not located in the pinned Mathlib as of 2026-10-28, searched as follows: `structure`/`def`/`class` names containing `Bisim`, `Simulation`, `TransitionSystem`, `LTS`, `Zigzag` or `Coalgebra` (hits: bisimulations for `WSeq`, `Seq`, `Computation`, `Stream'` and `PFunctor.M`, category-theoretic zigzags, `Endofunctor.Coalgebra` with its `Hom`, generic in the functor (for `Part` the UP half alone, for `Part × Set` the strict map with the back clause, by `coalgHom_iff`), and coalgebras over a ring, over a comonad and of descent data; none for a relation step paired with a partial map without the back clause).

### `Motion.LaxHom` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** As `Motion.Hom`, with the UP square lax in `Part`'s order

**Reason:** A lax map of motions: steps to steps, and every value of UP at `x` sent to a value of UP at `f x` (`UpLax`), equivalently `(M.up x).map f ≤ N.up (f x)` in `Part`'s order (`upLax_iff_le`), the restriction order of Cockett and Lack, TCS 270 (2002), § 2.1.4, p. 230. Strict iff lax with UP-definedness reflected (`upStrict_iff`). The search recorded under `Motion.Hom` covers this entry.

### `IsWeakPullback` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Mathlib's `IsPullback` with the uniqueness of the mediating map dropped; no Mathlib analog

**Reason:** Rutten, "Universal coalgebra", TCS 249 (2000), Appendix, p. 74: a weak pullback is defined as a pullback without the requirement that the mediating function be unique. Stated in the category `Type u`, with the cone over any type. A weak-pullback definition was not located in the pinned Mathlib as of 2026-10-29, searched as follows: a case-insensitive grep of `Mathlib/` (`.lean` files) for `weak pullback`, `weak_pullback` and `weakpullback`, and a grep for `WeakPullback`, `weakPullback` and `PreservesWeak` (no hits for any).

### `PreservesWeakPullbacks` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Over `IsWeakPullback`; Mathlib's `PreservesLimit` concerns limits with unique mediating maps

**Reason:** A functor `Type u ⥤ Type u` sending every `IsWeakPullback` square to one, Rutten's hypothesis on the functor from Convention 4.4 (TCS 249 (2000), p. 28), worded in Proposition A.3 (p. 76) as transforming weak pullbacks into weak pullbacks. Convention 4.4 stars the results whose proofs use it. The search recorded under `IsWeakPullback` covers this entry.

### `PreservesWeakPullbacksElementwise` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Stated over Mathlib's canonical pullback `CategoryTheory.Limits.Types.PullbackObj`; no Mathlib analog

**Reason:** The elementwise form of `PreservesWeakPullbacks`: each pair `x : F A`, `y : F B` with `F f x = F g y` lifts to `F` of the canonical pullback, Rutten's `P` (TCS 249 (2000), Appendix, p. 74). Taken over every pair `f`, `g`, it is the criterion of Gumm and Freese, Proposition 3 (arXiv:2103.09566, p. 4). It follows from `PreservesWeakPullbacks` without `Classical.choice` (`PreservesWeakPullbacks.elementwise`) and gives it with `Classical.choice` (`PreservesWeakPullbacksElementwise.preserves`). `part`, `set` and `partSet` prove it for `ofTypeFunctor Part`, `ofTypeFunctor Set` and their product, and `prod` closes it under products, each without `Classical.choice`. Mathlib's `Functor.Liftr` (`Mathlib/Control/Functor.lean`) lifts a relation on one type to `F` of the subtype of related pairs; it is a neighbour, not this condition. The search recorded under `IsWeakPullback` covers this entry.

### `Motion.IsBisim` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Mathlib's `IsBisimulation` is stated for `Stream'`, `Seq` and `Computation`, each for its own type; no Mathlib analog for `Motion`

**Reason:** Rutten's bisimulation (TCS 249 (2000), p. 11) between two motions read as coalgebras for `Part × Set` (`ZeroParadox/Die.lean` § XX; `isBisim_iff_coalgHom`, both carriers in one universe): some structure map on the related pairs for which both projections are homomorphisms, each square checked against `structMap`. `isBisim_iff` gives the equivalent transfer conditions on UP and the step relation. `Motion` is project-local (its entry above). The Mathlib bisimulation search is recorded under `Motion.StepCompat` (2026-10-21); repeated 2026-10-29 as a grep of `Mathlib/` for `def IsBisimulation`, `def Bisim`, `structure Bisim` and `def IsBisim` (hits: `IsBisimulation` in `Data/Seq/Computation.lean`, `Data/Seq/Defs.lean`, `Data/Stream/Init.lean`, and, through the `def Bisim` pattern, `BisimO` in `Data/Seq/Computation.lean`, `Data/Seq/Defs.lean`, `Data/WSeq/Relation.lean`; none for a general coalgebra).

### `Motion.Bisimilar` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Over `Motion.IsBisim`; no Mathlib analog

**Reason:** Related by some bisimulation: the union of all bisimulations, Rutten's greatest bisimulation of Corollary 5.6 (TCS 249 (2000), p. 33). `isBisim_bisimilar` shows it is a bisimulation, and `bisimilar_equivalence` that on one motion it is an equivalence relation. The search recorded under `Motion.IsBisim` covers this entry.

### `NInf` — `ZeroParadox/Die.lean`

**Relationship to Mathlib:** Mathlib's `ENat` is `WithTop ℕ` and `OnePoint ℕ` is `Option ℕ`, each with the point at infinity as a constructor; Mathlib's `Computation Unit` is equivalent to `NInf` (`NInf.ninfEquivComp`); no Mathlib analog for the decreasing-sequence presentation

**Reason:** Escardó's `ℕ∞`, the decreasing sequences `ℕ → Bool` (preprint of JSL 78(3) (2013), p. 1), in the presentation his selection function (Theorem 3.5, p. 5) and his Lemma 8.1 (p. 14) are stated for, so the proofs in `ZeroParadox/Die.lean` § XXIII follow his. The decreasing-sequence presentation was not located in the pinned Mathlib as of 2026-10-29, searched as follows: a grep of `Mathlib/` (`.lean` files) for `generic convergent` and `one-point compactification of` (hits only in `Topology/Compactification/OnePoint/`, whose `OnePoint` is `Option`), for the decreasing condition `x (i + 1) = true → x i = true` and `∀ n, f (n + 1) ≤ f n` (one hit, `antitone_nat_of_succ_le`, a lemma on antitone maps, not a type), and for `Conat`, `omniscient`, `Omniscient` and `Searchable` (no hits); and for `def ENat` (one hit, `WithTop ℕ`).

### `clockStep` — `ZeroParadox/Computability/Occurrence.lean`

**Relationship to Mathlib:** Built from Mathlib's `Nat.Partrec.Code.evaln`; no Mathlib analog

**Reason:** A step function on `(code, input, budget)`: halt once `evaln budget code input` has a value, else raise the budget. It is primitive recursive (`clockStep_primrec`, from `primrec_evaln`), and the run from `(c, n, 0)` halts iff `c` halts on `n` (`clock_eval_dom_iff`), so halting of codes becomes arrival in `runMotion clockStep`. Mathlib states halting through `eval` and `evaln`; a step function on `(code, input, budget)` was not located as of 2026-10-21, searched as follows: the pinned Mathlib grepped for `evaln` (two files, `Computability/PartrecCode.lean` and `Computability/Halting.lean`) and the `def` lines of both read (`eval`, `evaln`, `ComputablePred`, `REPred` and others; no such step), and `Mathlib/Computability/` grepped for `StateTransition.eval`, `Reaches`, `EvalsTo`, "clock" and "budget" (hits only in the Turing-machine files, whose steps act on machine configurations, not codes).

### `padId` — `ZeroParadox/Computability/Kleene.lean`

**Relationship to Mathlib:** Built from Mathlib's `Code.comp` and `Code.id`; no Mathlib analog as a named map

**Reason:** `c ↦ Code.comp c Code.id`, a computable map that never returns its argument (`padId_ne`) and keeps `eval` (`eval_padId`), so `ofFun padId` has no self-step while every class up to `eval` steps to itself only (`padId_drawing_vs_set`). The corpus's `padding` (same file, § VIII) is stated for the set of codes of one function, not as a map.

### `constEnc` — `ZeroParadox/Computability/Kleene.lean`

**Relationship to Mathlib:** Built from Mathlib's `Code.const` and `Encodable.encode`; no Mathlib analog

**Reason:** CONTROL map `c ↦ Code.const (encode c)`: computable and not `eval`-respecting (`constEnc_not_respects`), so its quotient by equal `eval` steps some class to two classes (`constEnc_two_successors`).

### `MemGraph.graphMotion` — `ZeroParadox/Settheory/HypersetOrder.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The member step on whole graphs: `A` steps to `A` re-rooted at each member of its root. `memberMotion` steps between nodes of one graph; this one acts on `MemGraph n`, so its quotient by `Same` acts on `HSet n`. `MemGraph` is project-local (its entry above).

### `MemGraph.sameSetoid` — `ZeroParadox/Settheory/HypersetOrder.lean`

**Relationship to Mathlib:** A Mathlib `Setoid`; no Mathlib analog for the relation

**Reason:** `Same` on graphs of every node count, on `Σ n, MemGraph n`, so that `wrap : MemGraph n → MemGraph (n + 1)` acts on one carrier. `HSet n` (Mathlib's `Antisymmetrization`) fixes `n`.

### `MemGraph.wrapMotion` — `ZeroParadox/Settheory/HypersetOrder.lean`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** `Motion.ofFun` of `(n, A) ↦ (n + 1, wrap A)` on `Σ n, MemGraph n`: a step that changes the node count, as one motion on a larger carrier. Its quotient by `sameSetoid` has exactly the class of `omegaLoop` stepping to itself (`wrapMotion_omegaLoop_selfOnlyAt`, `eq_omegaLoop_of_wrapMotion_step_self`).

### `optionMotion` — `ZeroParadox/Order/LeastFixedPoint.lean`

**Relationship to Mathlib:** No Mathlib analog; its quotient lives on Mathlib's `Cardinal`

**Reason:** `Motion.ofFun Option` on the carrier `Type`, so that the stages `optIter n` are one run (`optionMotion_isRun_optIter`). Quotiented by Mathlib's `Cardinal.isEquivalent`, its step is `c ↦ c + 1` on `Cardinal.{0}` (`quot_optionMotion_step_iff`, from `Cardinal.mk_option`).

### `sNorm` — `ZeroParadox/Valuation/RiemannSphere.lean`

**Relationship to Mathlib:** No Mathlib analog; built from `‖·‖₊` on `ℚ_[2]`

**Reason:** The extended norm on the 2-adic sphere `OnePoint ℚ_[2]`: `‖x‖₊` at a finite point and ⊤ of `ℝ≥0∞` at `∞`, so that `sNorm (rInv s) = (sNorm s)⁻¹` at every point (`sNorm_rInv`). Mathlib's extended norm `‖·‖ₑ` is defined on normed types, and `OnePoint ℚ_[2]` carries no norm. An extended norm on `OnePoint` was not located as of 2026-10-21, searched as follows: a grep of `Mathlib/Topology/Compactification/` for `enorm`, `ENNReal` and `ℝ≥0∞` (no hit).
