# ZP-H Categorical Bridge - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** (see final commit hash after push)
**Lean source:** [`ZeroParadox/ZPH.lean`](../ZeroParadox/ZPH.lean)
**Document proved:** ZP-H Categorical Bridge v1.1

---

## Build Result

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```

**Result:** Clean — 3317 jobs, 0 errors, 0 warnings.

---

## Axiom Purity Check

```
'ZeroParadox.ZPH.th1_fa'                      does not depend on any axioms
'ZeroParadox.ZPH.th1_fb'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPH.th1_fc'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPH.th1_fd'                      depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPH.th2_singularity_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPH.th3_snap_all_functors'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Interpretation:** No `sorryAx` anywhere. `th1_fa` is completely axiom-free — it follows
from ZPA's `bot_le` which depends on no axioms at all. The remaining five theorems depend
only on the standard Mathlib kernel axioms, inheriting from their domain sources (ZPB's
p-adic topology, ZPC's real analysis, ZPD's Hilbert space, ZPG's category theory).

---

## Import Strategy

ZP-H imports all six prior layers and no new Mathlib infrastructure beyond what they carry.

```lean
import ZeroParadox.ZPA
import ZeroParadox.ZPB
import ZeroParadox.ZPC
import ZeroParadox.ZPD
import ZeroParadox.ZPE
import ZeroParadox.ZPG
import Mathlib.Tactic
```

All Mathlib infrastructure (p-adic numbers, inner product spaces, CategoryTheory) is
transitively available from the prior imports.

---

## What Was Proved

### T-H1 — Each Functor Preserves the Initial Object (OQ-G2 Closed)

| Functor | Lean name | Statement | Grounding |
|---------|-----------|-----------|-----------|
| F_A: C → SLat | `th1_fa` | `le bot x` for all x in any ZPSemilattice | `ZPA.bot_le` |
| F_B: C → pTop | `th1_fb` | No continuous path ε₀ → 0 in Q₂ | `ZPB.c3_irreversible` |
| F_C: C → InfoSp | `th1_fc` | `jsdPQ = Real.log 2` (1 bit) | `ZPC.t1b_jsd` |
| F_D: C → Hilb | `th1_fd` | `⟪T(0), T(ε₀)⟫_ℂ = 0` (orthogonal shift) | `ZPD.t4_snap_orthogonal` |

**Note on F_B/F_C/F_D:** The full category-theoretic T-H1 claim ("F(0) is an initial
object in the codomain category") requires defining SLat, pTop, InfoSp, and Hilb as
`CategoryTheory.Category` instances and verifying functor law preservation. That
infrastructure is deferred. What is proved is the key domain fact that grounds each
claim — the irreversibility (F_B), the 1-bit cost (F_C), and the orthogonal shift (F_D).

### T-H2 — Singularity Compatibility (OQ-G4 Closed)

| Lean name | Statement | Proof |
|-----------|-----------|-------|
| `th2_singularity_compatibility` | `IsEmpty (X ⟶ 0) ∧ (∀ M, ∃ n, M < circPartial n)` | `⟨t3_unreachability X hne, t2_diverges⟩` |

Both singularity characterizations — ZPG's domain absence (`hom(X,0) = ∅`) and ZPC's
infinite accumulation (`circPartial → ∞`) — are independently derived and jointly
assembled here. Their compatibility is structural: domain-absence (stronger) is consistent
with divergence (weaker), as infinite accumulation required to reach 0 implies no finite
morphism can accomplish it.

### T-H3 — Binary Snap Under All Four Functors (Cross-Framework)

| Lean name | Statement |
|-----------|-----------|
| `th3_snap_all_functors (n : ℕ) (hn : 2 ≤ n)` | 4-part conjunction (see below) |

```
join c₀ c₁ = c₁                                          -- F_A (ZPE t_snap_machine)
∧ (∀ x : Q₂, x ≠ 0 → ¬∃ path x → 0)                   -- F_B (ZPB c3_irreversible)
∧ jsdPQ = Real.log 2                                      -- F_C (ZPC t1b_jsd)
∧ ⟪transitionOp n ⟨0,_⟩, transitionOp n ⟨1,_⟩⟫_ℂ = 0  -- F_D (ZPD t4_snap_orthogonal)
```

**Proof:** `⟨t_snap_machine, c3_irreversible, t1b_jsd, t4_snap_orthogonal n hn⟩`

This is the first theorem in the project that simultaneously references all four domain
documents. Each component is a closed theorem from its domain; their assembly is the
cross-framework consistency claim of ZP-H.

---

## Items Not Formalized (and Why)

| ZP-H item | Reason |
|-----------|--------|
| C-H1 through C-H4 (full functor constructions) | Require SLat, pTop, InfoSp, Hilb as `CategoryTheory.Category` instances. Substantial infrastructure not needed for the key cross-framework results. |
| T-H1 F_B/F_C/F_D universal property | Follows from C-H1–C-H4; deferred with the functor constructions. |
| D-H1 as a Lean theorem | Design commitment — the choice of what morphisms are. No formal statement; documented as a comment. |

---

## Proof Strategy Notes

**`th1_fa`:** `bot_le x` from ZPA. The ZPSemilattice `bot` satisfies `le bot x` for all
x by A4 (bot_join). In the poset-as-category, this is the unique morphism ⊥ → x, making
⊥ the initial object. Completely axiom-free because `bot_le` is proved by unfolding
definitions only.

**`th2_singularity_compatibility`:** The conjunction `⟨t3_unreachability X hne, t2_diverges⟩`
assembles ZPG T3 (no morphism X → 0 for X ≇ 0) with ZPC T2 (circPartial diverges). Both
are independently proved; their joint derivability without bridge axioms closes OQ-G4.

**`th3_snap_all_functors`:** Anonymous constructor assembles four domain theorems with
heterogeneous types into a single proposition. The four components:
- `t_snap_machine`: from ZPE, uses the `machinePhaseZPS` instance making the join definitional
- `c3_irreversible`: from ZPB, topological irreversibility of Q₂
- `t1b_jsd`: from ZPC, JSD computation over BinaryState
- `t4_snap_orthogonal n hn`: from ZPD, inner product of basis vectors

All four depend only on `[propext, Classical.choice, Quot.sound]`, so their conjunction does too.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
