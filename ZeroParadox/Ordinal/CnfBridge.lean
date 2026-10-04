import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Order.LeastFixedPoint
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The CNF/ℤ₂ value bridge, at the construction level (Gentzen.lean item 4)

One sequence `towerNONote` has two realizations, connected by maps and never by `=`: `NONote.repr`
into `Ordinal`, closing at the least fixed point ε₀, and `cnfToZp2` into `ℤ_[2]`, with norm-limit 0
(`mu_construction_correspondence`). The *identification of these two limits* — ε₀ (∈ `Ordinal`)
with 0 (∈ `ℤ_[2]`) — is not a well-formed statement: it fails to elaborate (a type mismatch between
`Ordinal` and `ℤ_[2]`). `cnf_bridge_type_boundary` co-witnesses the two limits instead.
Long form: `ZeroParadox/Ordinal/CnfBridge.md`.

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

/-- **Loop through ⊥.** Under `cnfToZp2` the seed's image and the limit of the stages' images are both the
    *value* 0 in `ℤ_[2]`. So the ordinal ascent ⊥ → ε₀ realizes as a `ℤ_[2]` path departing 0 and
    whose norm returns to 0. This is a value coincidence at 0, NOT an identity: ⊥ is never ε₀ (ε₀ is the least fixed
    point of `α ↦ ω^α`, never the same as ⊥ — and **not** order-adjacent to it, see
    `epsilonZero_tower_lt`), and the images of the finite stages n ≥ 1 are all ≠ 0 (next to the floor, never it; `snap_arc_z2_loop`). `ε₀ = 0` with 0 the 2-adic zero stays ill-typed: it fails to elaborate. -/
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

/-- **Type boundary, fenced.** ε₀ is the least fixed point from ⊥ (`IsLeastFixedPointFrom`); the 2-adic 0 is
    the norm-limit of the images `cnfToZp2 (towerNONote n)`, NOT a least fixed point. `ε₀ ≠ 0`, 0 the ordinal
    zero, is `epsilon0_ne_zero`; `ε₀ = (0 : ℤ_[2])` does not type-check, with no coercion between `Ordinal` and
    `ℤ_[2]` in either direction (guard below). Under `cnfToZp2` that 0 is the seed `towerNONote 0`'s image and
    the images' limit, and ε₀ has no image (`repr_lt_epsilon0`, `ZeroParadox/Ordinal/PricedInterface.lean`).
    Through the threshold map and `snapEmbed` ε₀ lands on 0: a map value, not an identity (long form, item 5). -/
theorem cnf_bridge_type_boundary :
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) epsilonZero ∧
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) ∧
    (∀ n : ℕ, NONote.repr (towerNONote n) = fundamentalSeq n) :=
  ⟨epsilon0_isLeastFixedPointFrom, tower_converges_to_zero, towerNONote_repr⟩

-- `Statement:` `ε₀ ≠ 0`, with 0 the ordinal zero, is a theorem (`epsilon0_ne_zero`).
example : epsilonZero ≠ (0 : Ordinal) := epsilon0_ne_zero
-- `Statement:` a guard: the cross-type literal, with 0 the 2-adic zero, fails to elaborate
-- (`Ordinal` against `ℤ_[2]`, with no coercion between them).
#check_failure (epsilonZero = (0 : ℤ_[2]))

/-! ## § VI. The snap arc as one object — the ℤ_[2] loop through ⊥ -/

/-- **The snap arc, as one `ℤ_[2]` loop through ⊥.** The ordinal ascent ⊥ → ε₀ realizes, through
    `cnfToZp2`, as a single arc in `ℤ_[2]` with three phases:

    1. **START at the floor** — `cnfToZp2 (towerNONote 0) = 0`: the arc begins at ⊥.
    2. **DEPARTURE by a discrete jump** — `∀ n ≥ 1, cnfToZp2 (towerNONote n) ≠ 0`: the trajectory
       genuinely leaves 0. The image of the first stage has 2-adic valuation 1 (`cnfToZp2_tower_valuation`), hence
       norm 1/2, so the norm jumps 0 → 1/2 with no intermediate stage — there is no continuous path
       off 0, the snap's discreteness rendered as geometry.
    3. **REAPPROACH** — `Filter.Tendsto … (nhds 0)`: the images of the stages return toward 0 in
       `ℤ_[2]` (`tower_converges_to_zero`).

    The loop closes because the images reapproach 0 in `ℤ_[2]` (equivalently, their 2-adic norms tend
    to 0 in `ℝ`: the equivalence is Mathlib's `tendsto_zero_iff_norm_tendsto_zero`, and the `example`
    below applies its forward direction `.1`), landing back on the floor — NOT
    because ⊥ and ε₀ are one point: **⊥ is never ε₀** (ε₀ is the least fixed point of `α ↦ ω^α`), never identical — and **not** order-adjacent, see
    `epsilonZero_tower_lt` — and
    the images of the finite stages n ≥ 1 never even reach 0 (always next to, never the same). Honest fence: this is the
    `ℤ_[2]` realization *via the map*, NOT a proof of `ε₀ = 0` with 0 the 2-adic zero, which stays ill-typed: it fails
    to elaborate (MC-1 / ZP-P). -/
theorem snap_arc_z2_loop :
    cnfToZp2 (towerNONote 0) = 0 ∧
    (∀ n : ℕ, 1 ≤ n → cnfToZp2 (towerNONote n) ≠ 0) ∧
    Filter.Tendsto (fun n => cnfToZp2 (towerNONote n)) Filter.atTop (nhds 0) := by
  refine ⟨cnfToZp2_zero, ?_, tower_converges_to_zero⟩
  intro n hn heq
  have hval : (cnfToZp2 (towerNONote n)).valuation = n := cnfToZp2_tower_valuation n
  rw [heq, PadicInt.valuation_zero] at hval
  omega

-- `Statement:` the reapproach read in the norm chart: the 2-adic norms of the images tend to 0 in `ℝ`.
example : Filter.Tendsto (fun n => ‖cnfToZp2 (towerNONote n)‖) Filter.atTop (nhds 0) :=
  tendsto_zero_iff_norm_tendsto_zero.1 tower_converges_to_zero

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
