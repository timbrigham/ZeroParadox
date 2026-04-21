# ZP-E Bridge Document - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** (see final commit hash after push)
**Lean source:** [`ZeroParadox/ZPE.lean`](../ZeroParadox/ZPE.lean)
**Document proved:** ZP-E Bridge Document v2.0

---

## Build Result

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```

**Result:** Clean — 3315 jobs, 0 errors, 0 warnings.

---

## Axiom Purity Check

```
'ZeroParadox.ZPE.t_snap_join'              does not depend on any axioms
'ZeroParadox.ZPE.t_snap_machine'           does not depend on any axioms
'ZeroParadox.ZPE.t_snap_derived'           does not depend on any axioms
'ZeroParadox.ZPE.t_snap_irreversible'      does not depend on any axioms
'ZeroParadox.ZPE.da2_bottom_characterization' does not depend on any axioms
'ZeroParadox.ZPE.c_da2_novelty'            depends on axioms: [propext]
```

**Interpretation:** Five of six theorems are axiom-free. `c_da2_novelty` uses `propext`
for the negation of a universal (`¬∀ x, join S x = x`), which is standard classical
logic — not a substantive commitment. No `sorryAx` anywhere.

---

## Import Strategy

ZP-E is a cross-framework synthesis. It imports ZPA and ZPC directly (to access
`ZPSemilattice` and `MachinePhase`) and adds `Mathlib.SetTheory.Cardinal.Basic` for
DA-3-D1. ZPB and ZPD are cited conceptually but not imported, keeping the elaboration
load minimal.

```lean
import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
```

---

## What Was Proved

### I. MachinePhase as a ZPSemilattice (Cross-Framework Bridge)

| Item | Lean name | Statement |
|------|-----------|-----------|
| ZPSemilattice instance | `machinePhaseZPS` | `instance machinePhaseZPS : ZPSemilattice MachinePhase` |

This is the key bridge: `MachinePhase` (from ZPC — two states: `initial`, `running`)
is given a `ZPSemilattice` instance where `bot = initial` and `join = max`. All four
A1–A4 axioms are discharged by `cases x <;> cases y <;> cases z <;> rfl`. This
makes T-SNAP definitionally true.

### II. T-SNAP — Binary Snap Causality (AX-1 Retired)

| ZP-E item | Lean name | Statement |
|-----------|-----------|-----------|
| T-SNAP (algebraic) | `t_snap_join` | `join (bot : L) ε₀ = ε₀` — immediate from A4 |
| T-SNAP (concrete) | `t_snap_machine` | `join c₀ c₁ = c₁` — `rfl` in MachinePhase |
| T-SNAP (derived) | `t_snap_derived` | `c₀ ≠ c₁ ∧ c₁ ≠ c₀ ∧ join c₀ c₁ = c₁` |
| T-SNAP (irreversibility) | `t_snap_irreversible` | `hle → hne → ¬∃ z, join y z = x` |

`t_snap_derived` bundles L-RUN, TQ-IH (both from ZPC), and the concrete snap into one
assembly theorem. AX-1 is retired: T-SNAP is a consequence of the instance, not an axiom.

### III. DA-2 — Instantiation Succession

| ZP-E item | Lean name | Statement |
|-----------|-----------|-----------|
| DA-2 (algebraic) | `da2_bottom_characterization` | `(∀ x, join S x = x) ↔ S = bot` |
| C-DA2 (corollary) | `c_da2_novelty` | `S ≠ bot → ¬(∀ x, join S x = x)` |

The ⊥ role is uniquely characterised by A4. Any state that advances beyond ⊥ cannot
play the identity role in the same semilattice — the Zero Paradox at the instantiation
boundary is formal.

### IV. DA-3 — Perspective-Relative Cardinality (DA-3-D1)

| ZP-E item | Lean name | Statement |
|-----------|-----------|-----------|
| DA-3-D1 | `da3_accessibleCardinality` | `noncomputable def ... : Cardinal` — `Cardinal.mk { x : L // le p x }` |

DA-3-D1 is a definition, not a theorem. DA-3-C1 (candidate claim) is explicitly not
formalised — marked `CANDIDATE` in ZP-E v2.0; formal derivation deferred to OQ-E2.

### Items not formalized (and why)

| ZP-E item | Reason |
|-----------|--------|
| DA-1 (Instantiation = Execution) | Definitional alignment — no Lean theorem; D7 configurations are live by definition |
| DA-3-C1 | Candidate claim, not formalised. Deferred to OQ-E2. |

---

## Proof Strategy Notes

**`machinePhaseZPS`:** All four axioms (A1–A4) are discharged by exhaustive case analysis
on the two-element type `MachinePhase`. `cases x <;> cases y <;> cases z <;> rfl` for
associativity (8 cases); `cases x <;> cases y <;> rfl` for commutativity and idempotence;
`cases x <;> rfl` for bot_join. All reduce to `rfl` by the match definition of `join`.

**`t_snap_machine`:** Reduces to `rfl` by definition — the `join` of `initial` and `running`
is `running` by the first match arm. This is the deepest form of T-SNAP.

**`t_snap_derived`:** Three-component anonymous constructor. `l_run` and `tq_ih` are
imported from ZPC (both axiom-free); the third component is `rfl`.

**`t_snap_irreversible`:** If `join y z = x`, derive `le y x` by:
`join y x = join y (join y z) = join (join y y) z = join y z = x` (using assoc + idem).
Combined with `le x y` (hypothesis), antisymmetry gives `x = y`, contradicting `hne`.

**`da2_bottom_characterization`:** Forward direction: evaluate at `x = bot` to get
`join S bot = bot`; then `S = join bot S = join S bot = bot` (using `bot_join` + comm).
Backward: `subst h; exact bot_join`.

**`da3_accessibleCardinality`:** `Cardinal.mk` applied to the subtype `{ x : L // le p x }`.
`noncomputable` because `Cardinal.mk` is noncomputable. No proof obligations.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
