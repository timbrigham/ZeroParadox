# CnfBridge — the CNF/ℤ₂ value bridge, at the construction level

Moved from `ZeroParadox/Ordinal/CnfBridge.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** Its claims are unverified until a claim review says otherwise.

`Ordinal/Gentzen.lean` §IV proves two convergences seeded at the same ω-tower:

* the ordinal tower `fundamentalSeq n` ascends to **ε₀** (`epsilonZero_eq_iSup`), which is the
  *least fixed point* of `α ↦ ω^α` from the ordinal bottom ⊥ (`epsilon0_isLeastFixedPointFrom`,
  `Order/LeastFixedPoint.lean`);
* the 2-adic encodings `cnfToZp2 (towerNONote n)` converge in norm to **0 = ⊥** in `ℤ_[2]`
  (`tower_converges_to_zero`).

The *identification of these two limits* — ε₀ (∈ `Ordinal`) with 0 (∈ `ℤ_[2]`) — is not a
well-formed statement: a literal `ε₀ = 0` is a **cross-type identity** (`Ordinal`
vs `ℤ_[2]`), the same category error the framework RETIRES as ill-typed for MC-1 and fences in ZP-P
and in `IsLeastFixedPointFrom` (`Order/LeastFixedPoint.lean`). `ZeroParadox/Ordinal/CnfBridge.lean`
does **not** prove it.

## What `ZeroParadox/Ordinal/CnfBridge.lean` DOES add (all type-sound, connected by the MAP, never by `=`)

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
   This is a value coincidence at 0, NOT an identity: ⊥ is never ε₀ (never the same; **not** order-adjacent — see
   `epsilonZero_tower_lt`), and the finite stages are all ≠ 0 (next to the floor, never it); the returned-to ⊥ is a new instance.

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
