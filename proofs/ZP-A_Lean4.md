# ZP-A Lattice Algebra - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** `314c76f`
**Lean source:** [`ZeroParadox/ZPA.lean`](../ZeroParadox/ZPA.lean)
**Document proved:** [`ZP-A Lattice Algebra v1.2`](../ZP-A_Lattice_Algebra_v1_2.pdf)

---

## Build Result

```
lake build 2>&1 | tee build.log
```

**Result:** Clean - 3300 jobs, 0 errors, 0 warnings.

## Axiom Purity Check

`#print axioms` is placed at the bottom of every ZP-X Lean file as a mandatory purity check. It reports every foundational kernel axiom a theorem depends on (e.g. `Classical.choice`, `propext`, `Quot.sound`). The expected result for clean ZP-A proofs is "does not depend on any axioms", meaning the proofs are entirely equational and constructive.

**Results for ZP-A (all theorems):**

```
'le_refl'                   does not depend on any axioms
'le_antisymm'               does not depend on any axioms
'le_trans'                  does not depend on any axioms
'bot_le'                    does not depend on any axioms
'state_transition_iff'      does not depend on any axioms
'state_sequence_monotone'   does not depend on any axioms
'cc1'                       does not depend on any axioms
```

**Interpretation:** The ZPSemilattice typeclass fields (A1–A4) function as proof hypotheses, not global axioms — so Lean's kernel sees them as assumptions in scope, not axiom declarations. No classical logic or choice principle was required. The proofs are purely equational and constructive.

---

## What Was Proved

Every theorem and definition in ZP-A v1.2 that is derivable from A1-A4 is machine-checked. CC-1 is stated faithfully as a conditional claim (hypothesis in signature, not derived).

### Structure

The Lean 4 file defines a `ZPSemilattice` typeclass with exactly the four ZP-A axioms as fields:

| Axiom | Field | Statement |
|-------|-------|-----------|
| A1 | `join_assoc` | `(x ⊔ y) ⊔ z = x ⊔ (y ⊔ z)` |
| A2 | `join_comm` | `x ⊔ y = y ⊔ x` |
| A3 | `join_idem` | `x ⊔ x = x` |
| A4 | `bot_join` | `⊥ ⊔ x = x` |

### Theorems and Definitions Proved

| ZP-A item | Lean name | Proved from | Notes |
|-----------|-----------|-------------|-------|
| D1 (lattice order) | `le` | - | `x ≼ y := x ⊔ y = y` |
| T1 - reflexivity | `le_refl` | A3 | `x ≼ x` |
| T1 - antisymmetry | `le_antisymm` | A2 | `x ≼ y → y ≼ x → x = y` |
| T1 - transitivity | `le_trans` | A1 | `x ≼ y → y ≼ z → x ≼ z` |
| T2 (⊥ is minimum) | `bot_le` | A4, D1 | `⊥ₗ ≼ x` for all `x` |
| D2 (state transition) | `IsStateTransition` | - | `∀ x, x ≼ f x` |
| D2 equivalence (⇒) | `state_transition_iff` | A1, A3 | Take `α = f x` |
| D2 equivalence (⇐) | `state_transition_iff` | A1, A3 | `x ⊔ (x ⊔ α) = (x ⊔ x) ⊔ α = x ⊔ α` |
| D3 (state sequence) | `IsStateSequence` | - | `∃ α, ∀ n, S(n+1) = S(n) ⊔ α(n)` |
| T3 (monotonicity) | `state_sequence_monotone` | A1, A3, D3 | `S(n) ≼ S(n+1)` |
| CC-1 (S₀ = ⊥) | `cc1` | T2 | Conditional - hypothesis in signature |

### What Was Not Proved (correctly)

- **CC-1 is not derived from A1-A4.** `S 0 = ⊥` appears as a hypothesis in `cc1`, faithfully reflecting the ZP-A v1.1 reclassification. The proof body uses only `bot_le`, which is universal - confirming the conclusion holds trivially once ⊥ is the minimum, regardless of the sequence's initialisation.
- **OQ-A1 is not resolved here.** Sufficiency of monotonicity is open within ZP-A; closure is in ZP-E T5.
- **No Mathlib lattice typeclasses are used.** The proof is self-contained under `ZPSemilattice`; no `SemilatticeSup` or `OrderBot` import is needed.

---

## Proof Strategy Notes

**T1 antisymmetry** uses a `calc` chain: `x = y ⊔ x` (from hyx reversed) `= x ⊔ y` (A2) `= y` (hxy). This is the exact two-step argument in ZP-A §2.1.

**T1 transitivity** follows the ZP-A proof verbatim: `x ⊔ z = x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z = y ⊔ z = z`.

**D2 equivalence** both directions use associativity + idempotency. The `(⇒)` direction takes `α = f x`; the `(⇐)` direction rewrites `x ⊔ (x ⊔ α)` to `(x ⊔ x) ⊔ α = x ⊔ α`.

**T3** uses the same associativity + idempotency pattern as D2 (⇐), applied to `S n ⊔ (S n ⊔ α n)`.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
