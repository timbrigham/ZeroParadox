# ZP-B p-Adic Topology - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** `8800355`
**Lean source:** [`ZeroParadox/ZPB.lean`](../ZeroParadox/ZPB.lean)
**Document proved:** ZP-B p-Adic Topology

---

## Build Result

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```

**Result:** Clean — 3305 jobs, 0 errors, 0 warnings.

---

## Axiom Purity Check

`#print axioms` blocks at the bottom of `ZPB.lean` report every kernel axiom each theorem depends on.

**Results for ZP-B (all theorems):**

```
'ZeroParadox.ZPB.t0_two_is_prime'         depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.t0_no_prime_below_two'   depends on axioms: [propext]
'ZeroParadox.ZPB.t0_redundancy'           depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.ax_b1_distinct'          depends on axioms: [propext]
'ZeroParadox.ZPB.t1_ultrametric'          depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.c1_isosceles'            depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.t2_closedBall_isClopen'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.c2_disjoint_no_path'     depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.t3_isolation'            depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.t5_totallyDisconnected'  depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPB.c3_irreversible'         depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Interpretation:** All three kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) are inherited from Mathlib's p-adic and topology instances — they are not introduced by ZP-B itself. No `sorryAx` appears. This is the expected and acceptable result for proofs over Mathlib's analytic infrastructure.

---

## What Was Proved

All theorems, corollaries, and the axiom in ZP-B are machine-checked over `Q₂ = ℚ_[2]` (the 2-adic rationals).

### Theorems and Definitions

| ZP-B item | Lean name | Statement |
|-----------|-----------|-----------|
| AX-B1 (binary existence) | `ax_b1_distinct` | `nullState ≠ firstAtomicState` |
| T0 (p = 2 minimum prime) | `t0_no_prime_below_two`, `t0_two_is_prime`, `t0_redundancy` | No prime below 2; 2 is prime; any p > 2 has redundant coefficients |
| T1 (ultrametric) | `t1_ultrametric` | `dist x z ≤ max (dist x y) (dist y z)` |
| C1 (isosceles triangles) | `c1_isosceles` | If `d(x,y) ≠ d(y,z)` then `d(x,z) = max(d(x,y), d(y,z))` |
| T2a (closed balls open) | `t2_closedBall_isOpen` | `IsOpen (closedBall a r)` for `r ≠ 0` |
| T2b (open balls closed) | `t2_ball_isClosed` | `IsClosed (ball a r)` (unconditional) |
| T2 (clopen balls) | `t2_closedBall_isClopen` | `IsClopen (closedBall a r)` for `r ≠ 0` |
| C2 (disjoint balls no path) | `c2_disjoint_no_path` | No continuous path connects disjoint closed balls in Q₂ |
| T3 (isolation of zero) | `t3_isolation` | `IsClopen (closedBall 0 r)` for `r ≠ 0` |
| T5 (totally disconnected) | `t5_totallyDisconnected` | `TotallyDisconnectedSpace Q₂` |
| C3 (Snap irreversible) | `c3_irreversible` | No continuous path from `x ≠ 0` back to `0` in Q₂ |

### Scope note on T2/T3

The hypothesis `r ≠ 0` in T2a and T3 is mathematically necessary: singleton balls (`r = 0`) are closed but not open in Q₂ (Q₂ is not discrete). For `r < 0` the closed ball is empty (trivially open). The Mathlib API `IsUltrametricDist.isOpen_closedBall` reflects this exactly.

---

## Proof Strategy Notes

**T0:** Purely decidable arithmetic. `t0_no_prime_below_two` delegates to `Nat.Prime.two_le`; `t0_redundancy` uses `simp` on `Fintype.card (Fin n)`.

**T1 (ultrametric):** One-line delegation to `dist_triangle_max` from Mathlib's ultrametric infrastructure, applied to the `IsUltrametricDist ℚ_[p]` instance.

**C1 (isosceles):** Case split on `d(x,y) < d(y,z)` vs `d(x,y) > d(y,z)`. Each branch applies `le_antisymm` with the ultrametric bound from T1, then derives a contradiction from the `max_lt` assumption using `linarith`.

**T2/T2a/T2b:** Delegate to `IsUltrametricDist.isOpen_closedBall`, `IsUltrametricDist.isClosed_ball`, and `Metric.isClosed_closedBall`. `IsClopen` in Mathlib is `IsClosed ∧ IsOpen` (closed first).

**C2 (no path between disjoint balls):** The key step is that any continuous path `γ : C([0,1], Q₂)` has a subsingleton range, proved by:
1. `Subtype.preconnectedSpace isPreconnected_Icc` — `[0,1]` is preconnected as a subspace of ℝ.
2. `isPreconnected_range γ.continuous` — the image of a preconnected space under a continuous map is preconnected.
3. `isTotallyDisconnected_of_totallyDisconnectedSpace Set.univ` — any preconnected subset of a totally disconnected space is a singleton.

**T5:** `inferInstance` — resolved automatically by the chain `IsUltrametricDist ℚ_[2]` → `TotallySeparatedSpace` (from `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`) → `TotallyDisconnectedSpace`.

**C3:** Same pattern as C2 applied to a path from `x ≠ 0` to `0`: subsingleton range forces `γ(0) = γ(1)`, contradicting `x ≠ 0`.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
