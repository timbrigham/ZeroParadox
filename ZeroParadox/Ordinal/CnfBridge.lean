import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Order.LeastFixedPoint
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The CNF/ℤ₂ value bridge, at the construction level (Gentzen.lean item 4)

`Ordinal/Gentzen.lean` §IV proves two convergences seeded at the same ω-tower:

* the ordinal tower `fundamentalSeq n` ascends to **ε₀** (`epsilonZero_eq_iSup`), which is the
  *least fixed point* of `α ↦ ω^α` from the ordinal bottom ⊥ (`epsilon0_isLeastFixedPointFrom`,
  `Order/LeastFixedPoint.lean`);
* the 2-adic encodings `cnfToZp2 (towerNONote n)` converge in norm to **0 = ⊥** in `ℤ_[2]`
  (`tower_converges_to_zero`).

Gentzen.lean flags the *identification of these two limits* — ε₀ (∈ `Ordinal`) with 0 (∈ `ℤ_[2]`) —
as "outside Lean scope: no type bridge." A literal `ε₀ = 0` is a **cross-type identity** (`Ordinal`
vs `ℤ_[2]`), the same category error the framework RETIRES as ill-typed for MC-1 and fences in ZP-P
and in `IsLeastFixedPointFrom` (`Order/LeastFixedPoint.lean`). This file does **not** prove it — that
proposition is not well-formed.

## What this file DOES add (all type-sound, connected by the MAP, never by `=`)

1. **Map-mediated order embedding on the tower** (`tower_valuation_orderEmbedding`,
   `tower_repr_orderEmbedding`): on the shared index `n`, ordinal order of the tower stages and the
   2-adic *valuation* order of their `cnfToZp2` images are the same order — `cnfToZp2` is
   order-reflecting *along the tower*, with valuation exactly tracking ordinal height.

2. **The shared seed maps to the bottom on BOTH sides** (`seed_maps_to_bot_both`): the NONote seed
   `towerNONote 0` (the NONote bottom `0`) is sent by `NONote.repr` to the `Ordinal` bottom ⊥, and by
   `cnfToZp2` to the `ℤ_[2]` bottom 0. One seed, two carriers, each carrier's ⊥.

3. **The 2-adic realization is a loop through ⊥** (`tower_image_loops_to_seed`): under `cnfToZp2`
   the seed's image *and* the tower's norm-limit are both the *value* 0. So the ordinal ascent
   ⊥ → ε₀ realizes, through the map, as a `ℤ_[2]` path that departs 0 and whose norm returns to 0.
   This is a value coincidence at 0, NOT an identity: ⊥ is never ε₀ (adjacent, never the same), and
   the finite stages are all ≠ 0 (next to the floor, never it); the returned-to ⊥ is a new instance.

4. **The construction-level correspondence** (`mu_construction_correspondence`): ONE sequence
   `towerNONote : ℕ → NONote` (the μ-ascent seeded at the NONote bottom) has TWO type-specific
   realizations — `NONote.repr` into `Ordinal` (closing at the least fixed point ε₀) and `cnfToZp2`
   into `ℤ_[2]` (norm-limit 0) — sharing the seed ⊥. This is the durable resolution of the
   "ε₀ looks single-carriered" worry: the object being realized is the *construction* (the tower on
   NONote), not a value; ε₀ and 0 are its two carrier-specific closures, not one number.

5. **The honest fence** (`cnf_bridge_type_boundary`): the ε₀ side is a genuine `IsLeastFixedPointFrom`
   μ; the `ℤ_[2]` side is a norm-limit of the *same index sequence*, NOT itself a least fixed point
   (no lattice ascent on `ℤ_[2]` to 0). The two are co-witnessed and connected by `towerNONote` — and
   the residual literal `ε₀ = 0` stays a **type boundary**, never a Lean `=`. Built in the spirit of
   `zpm_triangle` (`Ordinal/Incompleteness.lean`), which co-witnesses without a type identity.

## Engineer's Take

By using the abstract shape of epsilon zero from least fixed point, we can now define a generic
relationship for this one specific proven construction. We can't cross a type boundary, however we can dictate shared shape
and position.
-/

namespace ZeroParadox

open Ordinal Filter

/-! ## § I. Map-mediated order embedding on the tower

`cnfToZp2` restricted to the tower stages is order-reflecting: ordinal `<` on the stages matches
2-adic *valuation* `<` on the images, both equal to `<` on the index `n`. -/

/-- The ordinal tower is strictly monotone in the index (full `StrictMono` from the step lemma). -/
theorem fundamentalSeq_strictMono' : StrictMono fundamentalSeq :=
  strictMono_nat_of_lt_succ fundamentalSeq_strictMono

/-- **Order embedding, ordinal side.** On the tower, ordinal order is the index order. -/
theorem tower_repr_orderEmbedding (m n : ℕ) :
    m < n ↔ NONote.repr (towerNONote m) < NONote.repr (towerNONote n) := by
  rw [towerNONote_repr, towerNONote_repr]
  exact fundamentalSeq_strictMono'.lt_iff_lt.symm

/-- **Order embedding, 2-adic side.** On the tower, the 2-adic valuation of the `cnfToZp2` images is
    the index, so valuation order = index order: `cnfToZp2` is order-reflecting along the tower, with
    valuation tracking ordinal height exactly. -/
theorem tower_valuation_orderEmbedding (m n : ℕ) :
    m < n ↔ (cnfToZp2 (towerNONote m)).valuation < (cnfToZp2 (towerNONote n)).valuation := by
  rw [cnfToZp2_tower_valuation, cnfToZp2_tower_valuation]

/-- The two orders agree: ordinal order of the tower stages ↔ 2-adic valuation order of their
    images. This is the map-mediated "correspondence" — an equivalence of orders via `cnfToZp2`,
    NOT a value identity. -/
theorem tower_orders_agree (m n : ℕ) :
    (NONote.repr (towerNONote m) < NONote.repr (towerNONote n))
      ↔ (cnfToZp2 (towerNONote m)).valuation < (cnfToZp2 (towerNONote n)).valuation :=
  (tower_repr_orderEmbedding m n).symm.trans (tower_valuation_orderEmbedding m n)

/-! ## § II. The shared seed maps to ⊥ on both sides -/

/-- **Shared seed → both bottoms.** The NONote seed `towerNONote 0` (the NONote bottom `0`) maps to
    the `Ordinal` bottom ⊥ under `NONote.repr`, and to the `ℤ_[2]` bottom 0 under `cnfToZp2`. -/
theorem seed_maps_to_bot_both :
    NONote.repr (towerNONote 0) = (⊥ : Ordinal) ∧ cnfToZp2 (towerNONote 0) = (0 : ℤ_[2]) :=
  ⟨by rw [towerNONote_repr, tower_stage_zero]; exact Ordinal.bot_eq_zero.symm,
   cnfToZp2_zero⟩

/-! ## § III. The 2-adic realization loops through ⊥ (the diagonal fixed point, concretely) -/

/-- **Loop through ⊥.** Under `cnfToZp2` the seed's image and the tower's norm-limit are both the
    *value* 0 in `ℤ_[2]`. So the ordinal ascent ⊥ → ε₀ realizes as a `ℤ_[2]` path departing 0 and
    whose norm returns to 0. This is a value coincidence at 0, NOT an identity: ⊥ is never ε₀ (ε₀ is the first
    step off ⊥ — always adjacent, never the same), and the finite stages are all ≠ 0 (next to the
    floor, never it). `ε₀ = 0` stays ill-typed (`cnf_bridge_type_boundary`). -/
theorem tower_image_loops_to_seed :
    cnfToZp2 (towerNONote 0) = 0 ∧
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop
      (nhds (cnfToZp2 (towerNONote 0))) :=
  ⟨cnfToZp2_zero,
   by rw [show cnfToZp2 (towerNONote 0) = (0 : ℤ_[2]) from cnfToZp2_zero]
      exact tower_converges_to_zero⟩

/-! ## § IV. The construction-level correspondence (the durable resolution) -/

/-- **One construction, two carrier realizations.** The single sequence `towerNONote : ℕ → NONote`
    (the μ-ascent seeded at the NONote bottom) realizes:
    * in `Ordinal` via `NONote.repr`: as `fundamentalSeq`, closing at the **least fixed point** ε₀ of
      `α ↦ ω^α` from ⊥ (`epsilon0_isLeastFixedPointFrom`);
    * in `ℤ_[2]` via `cnfToZp2`: as a norm-limit to **0**;
    sharing the seed ⊥ (§II). The object realized is the construction, not a value: ε₀ and 0 are its
    two carrier-specific closures. -/
theorem mu_construction_correspondence :
    -- ordinal realization of the shared tower
    (∀ n : ℕ, NONote.repr (towerNONote n) = fundamentalSeq n) ∧
    epsilonZero = ⨆ n : ℕ, fundamentalSeq n ∧
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) epsilonZero ∧
    -- 2-adic realization of the SAME tower
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) ∧
    -- shared seed ⊥ on both carriers
    NONote.repr (towerNONote 0) = (⊥ : Ordinal) ∧ cnfToZp2 (towerNONote 0) = (0 : ℤ_[2]) :=
  ⟨towerNONote_repr, epsilonZero_eq_iSup, epsilon0_isLeastFixedPointFrom,
   tower_converges_to_zero, seed_maps_to_bot_both.1, seed_maps_to_bot_both.2⟩

/-! ## § V. The honest fence — co-witness, no type identity -/

/-- **Type boundary, fenced.** The ε₀ side is a genuine least-fixed-point μ
    (`IsLeastFixedPointFrom … epsilonZero`); the `ℤ_[2]` side is the norm-limit 0 of the same index
    sequence — NOT itself a least fixed point (no lattice ascent to 0 on `ℤ_[2]`). Both are
    co-witnessed and connected by the shared `towerNONote`; the literal `ε₀ = 0` is a cross-type
    identity (ill-typed per MC-1 / ZP-P) and is deliberately absent. In the spirit of `zpm_triangle`. -/
theorem cnf_bridge_type_boundary :
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) epsilonZero ∧
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) ∧
    (∀ n : ℕ, NONote.repr (towerNONote n) = fundamentalSeq n) :=
  ⟨epsilon0_isLeastFixedPointFrom, tower_converges_to_zero, towerNONote_repr⟩

/-! ## § VI. The snap arc as one object — the ℤ_[2] loop through ⊥ -/

/-- **The snap arc, as one `ℤ_[2]` loop through ⊥.** The ordinal ascent ⊥ → ε₀ realizes, through
    `cnfToZp2`, as a single arc in `ℤ_[2]` with three phases:

    1. **START at the floor** — `cnfToZp2 (towerNONote 0) = 0`: the arc begins at ⊥.
    2. **DEPARTURE by a discrete jump** — `∀ n ≥ 1, cnfToZp2 (towerNONote n) ≠ 0`: the trajectory
       genuinely leaves 0. The first stage has 2-adic valuation 1 (`cnfToZp2_tower_valuation`), hence
       norm 1/2, so the norm jumps 0 → 1/2 with no intermediate stage — there is no continuous path
       off 0, the snap's discreteness rendered as geometry.
    3. **REAPPROACH** — `Filter.Tendsto … (nhds 0)`: the stages return toward 0 in norm
       (`tower_converges_to_zero`).

    The loop closes because the tower's 2-adic **norm** reapproaches 0, landing back on the floor — NOT
    because ⊥ and ε₀ are one point: **⊥ is never ε₀** (ε₀ is the first step off ⊥), always adjacent, never identical, and
    the finite stages never even reach 0 (always next to, never the same). Honest fence: this is the
    `ℤ_[2]` realization *via the map*, NOT a proof of `ε₀ = 0`, which stays ill-typed
    (`cnf_bridge_type_boundary`, MC-1 / ZP-P). -/
theorem snap_arc_z2_loop :
    cnfToZp2 (towerNONote 0) = 0 ∧
    (∀ n : ℕ, 1 ≤ n → cnfToZp2 (towerNONote n) ≠ 0) ∧
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) := by
  refine ⟨cnfToZp2_zero, ?_, tower_converges_to_zero⟩
  intro n hn heq
  have hval : (cnfToZp2 (towerNONote n)).valuation = n := cnfToZp2_tower_valuation n
  rw [heq, PadicInt.valuation_zero] at hval
  omega

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox

#print axioms fundamentalSeq_strictMono'
#print axioms tower_repr_orderEmbedding
#print axioms tower_valuation_orderEmbedding
#print axioms tower_orders_agree
#print axioms seed_maps_to_bot_both
#print axioms tower_image_loops_to_seed
#print axioms mu_construction_correspondence
#print axioms cnf_bridge_type_boundary
#print axioms snap_arc_z2_loop

end PurityCheck
