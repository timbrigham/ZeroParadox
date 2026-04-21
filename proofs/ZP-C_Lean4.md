# ZP-C Information Theory - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** `8e1642d`
**Lean source:** [`ZeroParadox/ZPC.lean`](../ZeroParadox/ZPC.lean)
**Document proved:** ZP-C Information Theory v1.4

---

## Build Result

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```

**Result:** Clean — 3313 jobs, 0 errors, 0 warnings.

---

## Axiom Purity Check

```
'ZeroParadox.ZPC.t1_distributions_distinct'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.t1b_kl_P'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.t1b_kl_Q'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.t1b_jsd'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.d5_antisymm'               depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.t2_partial_eq'             depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.t2_finite_loop'            depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.t2_diverges'               depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPC.l_run'                     does not depend on any axioms
'ZeroParadox.ZPC.tq_ih'                     does not depend on any axioms
```

**Interpretation:** `l_run` and `tq_ih` are provable by `decide` alone — no kernel axioms needed. The remaining theorems use only standard Mathlib kernel axioms inherited from real analysis and PMF infrastructure. No `sorryAx` anywhere.

---

## What Was Proved

### Formalizable items

| ZP-C item | Lean name | Statement |
|-----------|-----------|-----------|
| T1 (distinct distributions) | `t1_distributions_distinct` | `distP ≠ distQ` — point-mass distributions at 0 and 1 are distinct |
| T1b: KL(P‖M) = log 2 | `t1b_kl_P` | Direct computation over `BinaryState → ℝ` with `M = (1/2, 1/2)` |
| T1b: KL(Q‖M) = log 2 | `t1b_kl_Q` | Symmetric computation for Q = (0,1) |
| T1b: JSD(P,Q) = log 2 | `t1b_jsd` | `jsdPQ = Real.log 2` |
| D5 antisymmetry | `d5_antisymm` | `surprisal n - surprisal m = -(surprisal m - surprisal n)` |
| T2: C_n = n | `t2_partial_eq` | `circPartial n = (n : ℝ)` |
| T2: finite conservation | `t2_finite_loop` | `∑ i ∈ range n, (a(i+1) − a(i)) = 0` when `a n = a 0` |
| T2: circulation diverges | `t2_diverges` | `∀ M, ∃ n, M < circPartial n` (Archimedean) |
| L-RUN | `l_run` | `c₀ ≠ c₁` — execution is a non-null state change |
| TQ-IH | `tq_ih` | `c₁ ≠ c₀` — no execution avoids a non-null configuration |

### Items not formalized (and why)

| ZP-C item | Reason |
|-----------|--------|
| D1: P₀ = lim K(x\|n)/n | Requires a fixed universal Turing machine, not available in Lean without a full computability model |
| T-BUF (Candidate Theorem) | Crosses the DA-1 boundary into ZP-E; structurally complete in ZP-C but formally closed in ZP-E |
| D3: Dirac measure δ₀ | Standard Mathlib `MeasureTheory.Measure.dirac`; definitional, nothing novel to prove |
| R3: Smooth embedding retired | A consistency note, not a theorem |

---

## Proof Strategy Notes

**T1 (`t1_distributions_distinct`):** Derive a contradiction from `heq : distP = distQ` by evaluating both sides at `nullSt`. `PMF.pure_apply` gives `distP nullSt = 1` and `distQ nullSt = 0` in `ℝ≥0∞`, giving `1 = 0`.

**T1b (`t1b_kl_P`, `t1b_kl_Q`):** `klDiv` unfolds via `Fin.sum_univ_two` to a sum of two terms. After `simp only` with the distribution definitions, both terms reduce to concrete real arithmetic. `norm_num` closes the goal — it handles `0 * Real.log (0 / (1/2)) = 0` (since `0 / (1/2) = 0` and `Real.log 0 = 0`) and `1 * Real.log (1 / (1/2)) = Real.log 2` (since `1/(1/2) = 2`). The JSD follows immediately by `ring`.

**T2 (telescoping):** `t2_telescoping` proves the general telescoping identity `∑ i ∈ range n, (a(i+1) − a(i)) = a n − a 0` by induction with `Finset.sum_range_succ` and `ring`. The finite conservation corollary substitutes `a n = a 0`. The divergence uses `exists_nat_gt` (Archimedean) to find `n > M`, then `t2_partial_eq` to equate `circPartial n = n`.

**L-RUN / TQ-IH:** `MachinePhase` is a two-constructor inductive with `DecidableEq`. `l_run : c₀ ≠ c₁` closes by `decide`. `tq_ih` is `Ne.symm l_run`.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
