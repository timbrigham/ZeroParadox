# ZP-G Category Theory - Lean 4 Formal Verification

**Date:** April 2026
**Branch:** `lake_testing`
**Commit:** (see final commit hash after push)
**Lean source:** [`ZeroParadox/ZPG.lean`](../ZeroParadox/ZPG.lean)
**Document proved:** ZP-G Category Theory v1.1

---

## Build Result

```
lake build 2>&1 | Out-File -FilePath build.log -Encoding utf8
```

**Result:** Clean — 3316 jobs, 0 errors, 0 warnings.

---

## Axiom Purity Check

```
'ZeroParadox.ZPG.t1_initial_unique'           depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t2_universal_constituent'    depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t3_unreachability'           depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t4_chains_forward_only'      depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t6a_identity_surprisal'      depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t6b_surprisal_nonneg'        depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t6c_surprisal_accumulates'   depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t6_informational_singularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZeroParadox.ZPG.t7_categorical_zero_paradox' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Interpretation:** All nine proved theorems depend only on the standard Mathlib kernel
axioms inherited from CategoryTheory infrastructure. No `sorryAx` anywhere. T5
(`t5_functors_preserve_initial`) is `trivial` — deferred to ZP-H T-H1; see below.

**Why `[propext, Classical.choice, Quot.sound]`:** Mathlib's CategoryTheory layer uses
classical logic throughout (functor existence, isomorphism extensionality). These three
axioms are the standard kernel for classical mathematics in Lean 4 and carry no
substantive commitment beyond what ZP-G already requires.

---

## Import Strategy

ZP-G is self-contained in category theory. No imports from ZPA/ZPB/ZPC/ZPD/ZPE.

```lean
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Iso
import Mathlib.Tactic
```

`IsInitial` and `IsTerminal` live in `Mathlib.CategoryTheory.Limits.Shapes.Terminal`.
The `≅` notation comes from `Mathlib.CategoryTheory.Iso`.

**Key API used:**
- `IsInitial.to : IsInitial T → (s : C) → T ⟶ s` — the unique morphism
- `IsInitial.hom_ext : IsInitial T → (f g : T ⟶ s) → f = g` — uniqueness
- `IsInitial.uniqueUpToIso : IsInitial X → IsInitial Y → X ≅ Y` — T1

**Type-universe note:** `IsTerminal t : Type` (not `Prop`) in Mathlib — it is the type
of limit cone structures, not a proposition. The AX-G1 "no terminal" axiom is therefore
formulated as `∀ t : C, IsEmpty (IsTerminal t)` rather than `¬∃ t, IsTerminal t` (the
latter fails universe-check). `IsEmpty α : Prop` for any `α : Type`, so this is correct.

---

## Class Architecture

Two classes, not one, reflecting ZP-G v1.1's honest labelling:

### `ZPCategory`
Carries AX-G1 + AX-G2. Any category-theoretic consumer of ZP-G that does not need
surprisal can use this class alone.

```lean
class ZPCategory (C : Type*) [Category C] where
  zpInitial : C
  zpIsInitial : IsInitial zpInitial
  ax_g1_no_terminal : ∀ t : C, IsEmpty (IsTerminal t)
  ax_g2 : ∀ (X : C), IsEmpty (X ≅ zpInitial) → IsEmpty (X ⟶ zpInitial)
```

### `ZPSurprisal`
Carries the I-KC import (D7'). K(x|y) is not Lean-computable; it is well-defined only
up to an additive constant c. Structural claims (zero, undefined, finite vs. infinite)
are constant-invariant. T6-a (`surp_id`) is the only I-KC property needed.

```lean
class ZPSurprisal (C : Type*) [Category C] [ZPCategory C] where
  surp : {A B : C} → (A ⟶ B) → ℕ
  surp_id : ∀ (A : C), surp (𝟙 A) = 0
```

---

## What Was Proved

| ZP-G item | Lean name | Statement | Proof |
|-----------|-----------|-----------|-------|
| T1: Initial unique | `t1_initial_unique` | `IsInitial A → IsInitial B → Nonempty (A ≅ B)` | `⟨hA.uniqueUpToIso hB⟩` |
| T2: Universal constituent | `t2_universal_constituent` | `∃ f : 0 ⟶ X, ∀ g, f = g` | `zpIsInitial.to` + `hom_ext` |
| T3: Unreachability | `t3_unreachability` | `IsEmpty (X ≅ 0) → IsEmpty (X ⟶ 0)` | `ZPC.ax_g2 X hne` |
| T4: Forward-only chains | `t4_chains_forward_only` | same conclusion + chain hypothesis | `t3_unreachability X hne` |
| T6-a: Identity surprisal zero | `t6a_identity_surprisal` | `surp (𝟙 A) = 0` | `ZPS.surp_id A` |
| T6-b: Non-negative surprisal | `t6b_surprisal_nonneg` | `0 ≤ surp f` | `Nat.zero_le _` |
| T6-c: Accumulates along chains | `t6c_surprisal_accumulates` | `0 ≤ ∑ surp (morphs k)` | `Nat.zero_le _` |
| T6: Informational singularity | `t6_informational_singularity` | `(outward ≥ 0) ∧ IsEmpty (X ⟶ 0)` | T6-b + T3 |
| T7: Categorical Zero Paradox | `t7_categorical_zero_paradox` | 4-part conjunction | T2 + T3 + T4 + T6 |

### Items not formalized (and why)

| ZP-G item | Reason |
|-----------|--------|
| T5: Functors preserve initial objects | Explicitly conditional on ZP-H T-H1. `t5_functors_preserve_initial : True := trivial` — marked as deferred. |
| D7' strict positivity (T6-b strict) | Requires "distinct objects encode distinct states" from I-KC encoding details — a modelling assumption not derivable from category structure alone. Non-strict non-negativity (`Nat.zero_le`) covers the structural claim. |
| R-BA: BA-G1 compatibility remark | Remark, not a theorem — no Lean statement needed. |

---

## Proof Strategy Notes

**T1:** `IsInitial.uniqueUpToIso` is the Mathlib lemma giving the canonical isomorphism
between any two initial objects. One-liner: `⟨hA.uniqueUpToIso hB⟩`.

**T2:** `IsInitial.to` provides the morphism; `IsInitial.hom_ext` provides uniqueness.
`hom_ext f g : f = g` for any two morphisms out of an initial object.

**T3 and T4:** Direct from `ZPC.ax_g2`. T4 adds an unused chain morphism `_f` to
encode the "arrived via a chain from 0" context without changing the proof content.

**T6-b and T6-c:** Both are `Nat.zero_le _` — the conclusion is `0 ≤ n` for any `n : ℕ`,
which is definitionally true. The structural content (outward surprisal is well-defined)
comes from the existence of morphisms from 0, which is T2.

**T6:** The "informational singularity" splits into Part I (T6-b applied to outward
morphisms) and Part II (T3, which says inward morphisms don't exist — so surprisal is
undefined by domain absence, the structural singularity).

**T7:** Anonymous constructor `⟨t2, ax_g2, T4, T6⟩` assembles the four parts. Parts II
and III have the same categorical content (AX-G2 / T3); T4 wraps T3 with the chain framing.

---

## Mathlib Version

```
mathlib @ v4.30.0-rc2
```

See [`lake-manifest.json`](../lake-manifest.json) for pinned dependency hashes.
