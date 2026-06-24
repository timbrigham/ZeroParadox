# Zero Paradox — Lean Custom Definition Registry

This file documents every definition, typeclass, and instance in the Zero Paradox Lean library that diverges from Mathlib's standard formalization. Each entry records what was replaced or extended, and the precise reason the Mathlib version was insufficient.

Every entry corresponds to a `-- [ZP-CUSTOM]` inline comment in the source. The register is generated from those comments and is always consistent with them. To regenerate:

```
grep -rn "\[ZP-CUSTOM\]" ZeroParadox/ --include="*.lean"
```

---

## Custom Typeclasses

### `ZPSemilattice` — `ZeroParadox/ZPA.lean:36`

**Relationship to Mathlib:** Replaces `SemilatticeSup` + `OrderBot`

**Reason:** Mathlib's semilattice hierarchy ties `⊔` to its order typeclass infrastructure (`LE`, `Preorder`) via hundreds of instances; importing it contaminates `#print axioms` with unrelated classical dependencies. `ZPSemilattice` states axioms A1–A4 from scratch so every theorem's axiom footprint is auditable.

---

### `AFAStructure` — `ZeroParadox/ZPJ.lean:78`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` uses the Axiom of Foundation (`ZFSet.regularity`), which forbids `x ∈ x`. AFA content (self-containing sets, Quine atoms) cannot be encoded using `ZFSet`. `AFAStructure` is the lattice-level encoding of what ZF+AFA provides set-theoretically, with `selfMem` / `quine_unique` / `bot_self_mem` as the three minimal class fields.

---

### `AbstractSelfApp` — `ZeroParadox/ZPJ_SelfApp.lean:63`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Abstracts the shared fixed-point pattern between AFA set theory (`f x = {x}`, unique fixed point = Quine atom) and 2-adic multiplication (`f x = 2x`, unique fixed point = 0). Mathlib has `Function.IsFixedPt` (a predicate on total functions) but no typeclass for "type with a self-application operation whose unique fixed point is a designated bottom element." Introducing this typeclass allows `AFAStructure`'s three class fields to become derived theorems.

---

### `ValuationStructure` — `ZeroParadox/ZPJ_Scale.lean:62`

**Relationship to Mathlib:** Replaces `Mathlib.RingTheory.Valuation.Valued`

**Reason:** Mathlib's `Valued` typeclass requires ring/field structure (it formalizes algebraic valuations over rings). `ZPSemilattice` has join only — no ring. `ValuationStructure` uses `val : L → ℕ∞` (not a `GroupWithZero` target) and the single axiom `val_scale` (val strictly increases under scale), which is the only machinery needed for the fixed-point uniqueness argument.

---

### `ValBridge` — `ZeroParadox/ZPJ_ScaleBridge.lean:47`

**Relationship to Mathlib:** Replaces `ValuationStructure` (this project)

**Reason:** `ValuationStructure` required `[ZPSemilattice L]` but the join operation `⊔` never appears in any of its four axioms — the constraint was an encoding artefact. `ValBridge` carries the same four axioms with `bot` as a plain field, allowing `ℤ_[2]` (a ring, not a `ZPSemilattice`) to be a formal instance. Unifies both tracks under one common ancestor.

---

### `KleeneStructure` — `ZeroParadox/ZPK.lean:168`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Bridges `AFAStructure` (set-theoretic self-containment) with Mathlib's computability library (`Nat.Partrec.Code`). No Mathlib typeclass connects AFA and `Code`. `KleeneStructure` asserts that the AFA Quine atom and the Kleene computational Quine (`∃ c, eval c = f c`) name the same structural property — this identification is the motivating commitment of ZP-K, not a derived theorem.

---

### `ZPCategory` — `ZeroParadox/ZPG.lean:42`

**Relationship to Mathlib:** Extends `Mathlib.CategoryTheory.Limits.IsInitial`

**Reason:** Mathlib has `IsInitial` and `IsTerminal` as separate structures; it has no typeclass bundling them together with AX-G2 (source asymmetry: `hom(X,0) = ∅` for non-isomorphic `X`). `ZPCategory` bundles both ZP-G axioms so they can be assumed uniformly across all ZP-G theorems without threading separate hypotheses.

---

### `ZPSurprisal` — `ZeroParadox/ZPG.lean:54`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib has no formalization of Kolmogorov complexity. `ZPSurprisal` is an import stub for the I-KC axiom (D7'): it models conditional K-complexity as an abstract `ℕ`-valued morphism assignment. The one field (`surp_id`: identity morphisms have zero surprisal) is the only structurally usable I-KC axiom in the ZP-G theorems; the rest of K-complexity is outside Lean scope.

---

### `DecorationUniverse` — `ZeroParadox/ZPJ_APG.lean:138`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib's `ZFSet` (the only set-theory formalization) uses Foundation — `x ∈ x` is forbidden, making it invalid as a decoration target for any APG with a self-loop. `DecorationUniverse` is an abstract type with `ValuationStructure` plus a `collect` operation and two axioms (`collect_singleton`, `collect_val_ge`), providing the minimum structure needed for AFA decoration uniqueness without importing any set-theoretic axiom.

---

### `Wheel` — `ZeroParadox/ZPJ_Wheel.lean:106`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Mathlib has no wheel typeclass (Carlström's algebraic structure in which division is total — `1/0` is a defined element). Extending `AddCommMonoid` + `CommMonoid` would inherit full semiring distributivity, which wheels deliberately weaken (axiom W9). `Wheel` states the wheel axioms (Carlström W1–W14) from scratch for axiom auditability, following the `ZPSemilattice` convention.

---

### `WheelValuationStructure` — `ZeroParadox/ZPJ_Wheel.lean:413`

**Relationship to Mathlib:** Extends `CommRing` (no Mathlib analog for the bridge)

**Reason:** The bridge typeclass connecting the ZP valuation hierarchy to wheel theory via the wheel-of-fractions construction. Over a `CommRing L` it carries a valuation `wvs_val : L → ℕ∞` that is additive on products (`wvs_val_mul`), with the assumed condition `wvs_val 0 = ⊤` (`wvs_val_zero`) — an axiom encoding that the ring's zero sits at infinite valuation. The ZP argument motivates the choice; the type-checker does not verify its necessity. No Mathlib typeclass bundles a ring with such a valuation for the wheel construction.

---

## Custom Types and Definitions

### `OntologicalStates` — `ZeroParadox/ZPB.lean:51`

**Relationship to Mathlib:** Replaces `Fin 2`

**Reason:** `Fin 2`'s constructors are `⟨0,_⟩` and `⟨1,_⟩` — natural numbers. `nullState` is not ℕ's 0 by convention; it is a semantic state with no numeric meaning. The free inductive eliminates the ℕ dependency and makes `⊥ ↦ null` a structural fact, not a labelling choice.

---

### `BinaryState` — `ZeroParadox/ZPC.lean:48`

**Relationship to Mathlib:** Replaces `Fin 2`

**Reason:** ZPC is self-contained (no ZPB import as a Lean dependency). `BinaryState` is a local copy of the same free-inductive encoding used by `OntologicalStates` in ZPB. `Fin 2` would import ℕ arithmetic into an information-theoretic file whose proofs should not depend on it.

---

### `IsQuineAtom` — `ZeroParadox/ZPJ.lean:99`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Lattice-level analog of Aczel's Quine atom (the unique set satisfying `x = {x}`). No Mathlib definition covers this: it requires `AFAStructure` context and encodes the conjunction of self-containment + uniqueness as a single predicate. Proved equivalent to `q = ⊥` by `t_exec_iff`.

---

### `APG` — `ZeroParadox/ZPJ_APG.lean:84`

**Relationship to Mathlib:** Extends `Mathlib.Combinatorics.Quiver.Basic`

**Reason:** Mathlib's `Quiver` is a bare directed graph (objects + edges) with no distinguished root or accessibility requirement. `APG` adds `root : V` and the accessibility proof (every vertex reachable from root), matching Aczel's definition of Accessible Pointed Graph. Both fields are required by AFA's decoration theorem.

---

### `IsKleeneFixedPoint` — `ZeroParadox/ZPK.lean:92`

**Relationship to Mathlib:** Replaces `Mathlib.Function.IsFixedPt`

**Reason:** `Function.IsFixedPt` works on total functions `α → α`. Here `f : Code → ℕ →. ℕ` (partial function) and the fixed-point condition is `eval c = f c` — equality of partial functions. No Mathlib predicate covers this; `IsKleeneFixedPoint` is the partial-function analog needed for the computability layer.

---

### `IsComputationalQuine` — `ZeroParadox/ZPK.lean:129`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** Named alias for `IsKleeneFixedPoint selfApply c`. Makes the connection to Quine atoms explicit in type signatures and theorem statements. Unlike the AFA Quine (unique by `quine_unique`), computational quines are not unique — each has a distinct Gödel number, generating the infinite family proved in §VI.

---

### `HasLawvereWitness` — `ZeroParadox/ZPJ_Lawvere.lean:43`

**Relationship to Mathlib:** Names the hypothesis of `Function.exists_fixed_point_of_surjective` (no Mathlib named predicate)

**Reason:** Mathlib proves Lawvere's fixed-point theorem (`Function.exists_fixed_point_of_surjective`) but exposes no reusable predicate for "β admits a point-surjection α → (α → β)" — the diagonal hypothesis. Naming it lets the face-split state, per face, whether the hypothesis holds (the Set faces are refuted by Cantor; the computability face is genuine). A naming alias in the spirit of `IsComputationalQuine`; no new axiomatic content — every theorem about it reduces to the Mathlib lemma.

---

### `Phase` (with `floorRel`, `phaseRel`, `snap`) — `ZeroParadox/ZPJ_Boundary.lean:94`

**Relationship to Mathlib:** No Mathlib analog

**Reason:** The illustrative single-carrier model for the well-foundedness boundary: `floor` (the self-looping ⊥) and `up : Ordinal → Phase` (the ε₀ ascent), with `phaseRel` self-looping at the floor and following ordinal `<` above it, and `snap := up 0` the irreversible exit. Mathlib has no type bundling a non-well-founded floor with a well-founded ordinal ascent under one relation. The carrier is a *modeling choice* — the boundary theorems' content is the two proven endpoints plus the framework's existing ⊥/ε₀ identification (MC-1, ε₀ open under OQ-E2), not a new commitment; the real-⊥ endpoint (`floorRel` / `floor_not_wellFounded`) is axiom-free on the actual lattice.

---

## Custom Instances

### `machinePhaseZPS` — `ZeroParadox/ZPE.lean:55`
`ZPSemilattice MachinePhase`

The cross-framework bridge. `MachinePhase` is ZPC's two-element type; giving it a `ZPSemilattice` instance makes T-SNAP (`bot_join` applied to `MachinePhase`) a direct consequence of ZP-A's A4, retiring AX-1 as an axiom. No Mathlib lattice instance exists for `MachinePhase`.

---

### `machinePhaseAFA` — `ZeroParadox/ZPK.lean:265`
`AFAStructure MachinePhase`

`selfMem x := x = bot` is the CIC-compatible encoding of AFA self-containment (`⊥ = {⊥}` cannot be stated in Lean's well-founded type theory). `quine_unique` and `bot_self_mem` are provable by `rfl`. This is the concrete closure of DA-1 for ZP-E's machine model.

---

### `machinePhaseKleene` — `ZeroParadox/ZPK.lean:275`
`KleeneStructure MachinePhase` (noncomputable)

`botCode` is chosen via `Classical.choose` — no algorithm can identify which `Code` is the `botCode` (`isComputationalQuine_undecidable`). The `noncomputable` marker is load-bearing, not a proof artifact: the non-constructivity is the formal content of DA-1's computational path. Removing it would misrepresent the result.

---

### `instZ2ValBridge` — `ZeroParadox/ZPJ_ScaleBridge.lean:97`
`ValBridge ℤ_[2]`

`ℤ_[2]` is a ring — it cannot be a `ZPSemilattice` instance and could not satisfy `ValuationStructure`. `ValBridge`'s bot-as-plain-field design makes this instance possible. All four axioms delegate directly to theorems proved in `ZPJ_Scale` §V (`q2Scale_bot`, `q2Val_bot`, `q2Val_unique`, `q2Val_scale`).

---

### `instNatInfZPS` — `ZeroParadox/ZPJ_Model.lean:63`
`ZPSemilattice ℕ∞` with inverted order

Mathlib's `WithTop ℕ` has `≤` as its standard order (`⊤` is maximum). Here `join = min` and `bot = ⊤` — a deliberate reversal. The ZP partial order `x ≤_ZP y ↔ min x y = y` makes `⊤` the bottom (valuation ∞) and `0` the maximum (fully constrained). No Mathlib instance covers this inverted reading.

---

### `instNatInfVal` — `ZeroParadox/ZPJ_Model.lean:76`
`ValuationStructure ℕ∞` (scale = +1, val = id)

The concrete model confirming that `ValuationStructure`'s abstract axioms have an inhabitant. `val = id` works because `ℕ∞` already carries its own depth as its value; `scale = (· + 1)` satisfies `val_scale` by `rfl`.

---

### `instOntZPS` — `ZeroParadox/ZPJ_OntBridge.lean:46`
`ZPSemilattice OntologicalStates`

`OntologicalStates` carries no Mathlib lattice structure. The join (null-identity, exist-absorbing) matches ZP-A's A1–A4 but does not correspond to any Mathlib-provided instance on a two-element type.

---

### `instOntSelfApp` — `ZeroParadox/ZPJ_OntBridge.lean:61`
`AbstractSelfApp OntologicalStates` via constant-to-null map

`OntologicalStates` (two elements) cannot satisfy `ValuationStructure`'s `val_scale` axiom — a finite two-element type has no room for `val` to strictly increase. The direct `AbstractSelfApp` instance using the constant-to-null map (every element → null) is the shorter path to AFA content for finite types.

---

*Last updated: 2026-06-24. Regenerate with: `grep -rn "\[ZP-CUSTOM\]" ZeroParadox/ --include="*.lean"`*
