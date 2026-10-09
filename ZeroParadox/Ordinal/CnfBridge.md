# CnfBridge — the CNF/ℤ₂ value bridge, at the construction level

Moved from `ZeroParadox/Ordinal/CnfBridge.lean`. ⚠ **This content was GRANDFATHERED — it was carried in an accepted-defect baseline, which means it was let through UNEXAMINED. Moving it changes that by exactly nothing.** It has since carried corrective edits, but its claims are unverified until a claim review says otherwise.

`Ordinal/Gentzen.lean` §IV proves two convergences seeded at the same ω-tower:

* the ordinal tower `fundamentalSeq n` ascends to **ε₀** (`epsilonZero_eq_iSup`), which is the
  *least fixed point* of `α ↦ ω^α` from the ordinal bottom ⊥ (`epsilon0_isLeastFixedPointFrom`,
  `Order/LeastFixedPoint.lean`);
* the 2-adic images `cnfToZp2 (towerNONote n)` converge in norm to **0 = ⊥** in `ℤ_[2]`
  (`tower_converges_to_zero`).

The *identification of these two limits* — ε₀ (∈ `Ordinal`) with 0 (∈ `ℤ_[2]`) — is not a
well-formed statement: a literal `ε₀ = 0` is a **cross-type identity** (`Ordinal`
vs `ℤ_[2]`), the same category error the framework RETIRES as ill-typed for MC-1 and fences in ZP-P
and in `IsLeastFixedPointFrom` (`Order/LeastFixedPoint.lean`). `ZeroParadox/Ordinal/CnfBridge.lean`
does **not** prove it.

## What `ZeroParadox/Ordinal/CnfBridge.lean` DOES add (all type-sound, connected by the MAP, never by a cross-carrier `=`)

1. **Map-mediated order embedding on the tower** (`tower_valuation_orderEmbedding`,
   `tower_repr_orderEmbedding`): on the shared index `n`, ordinal order of the tower stages and the
   2-adic *valuation* order of their `cnfToZp2` images are the same order — `cnfToZp2` is
   order-reflecting *along the tower*, with valuation exactly tracking ordinal height.

2. **The shared seed maps to the bottom on BOTH sides** (`seed_maps_to_bot_both`): the NONote seed
   `towerNONote 0` (the NONote bottom `0`) is sent by `NONote.repr` to the `Ordinal` bottom ⊥, and by
   `cnfToZp2` to the `ℤ_[2]` bottom 0. One seed, two carriers, each carrier's ⊥.

3. **The 2-adic realization is a loop through ⊥** (`tower_image_loops_to_seed`): under `cnfToZp2`
   the seed's image *and* the limit of the stages' images are both the *value* 0. So the ordinal ascent
   ⊥ → ε₀ realizes, through the map, as a `ℤ_[2]` path that departs 0 and whose norm returns to 0.
   This is a value coincidence at 0, NOT an identity: ⊥ is never ε₀ (never the same; **not** order-adjacent — see
   `epsilonZero_tower_lt`), and the images of the finite stages n ≥ 1 are all ≠ 0 (next to the floor, never it). In this realization the
   images reapproach the same 0 the seed maps to (`snap_arc_z2_loop`); reading the returned-to ⊥ as a new
   instance is a commitment, not a theorem.

4. **The construction-level correspondence** (`mu_construction_correspondence`): ONE sequence
   `towerNONote : ℕ → NONote` (the μ-ascent seeded at the NONote bottom) has TWO type-specific
   realizations — `NONote.repr` into `Ordinal` (closing at the least fixed point ε₀) and `cnfToZp2`
   into `ℤ_[2]` (norm-limit 0) — sharing the seed ⊥. This is the durable resolution of the
   "ε₀ looks single-carriered" worry: the object being realized is the *construction* (the tower on
   NONote), not a value; ε₀ and 0 are its two carrier-specific closures, not one number.

5. **The honest fence** (`cnf_bridge_type_boundary`): the ε₀ side is a genuine `IsLeastFixedPointFrom`
   μ; the `ℤ_[2]` side is the norm-limit of the *images* `cnfToZp2 (towerNONote n)`, NOT itself a least
   fixed point (no lattice ascent on `ℤ_[2]` to 0). The two are co-witnessed and connected by
   `towerNONote`, and no Lean `=` joins the two closures. `ε₀ ≠ 0`, with 0 the ordinal zero, is a theorem
   (`epsilon0_ne_zero`, in `Ordinal`). The cross-type `ε₀ = (0 : ℤ_[2])` does not type-check, with no
   coercion between `Ordinal` and `ℤ_[2]` in either direction; the `#check_failure` guard after the
   theorem detects that failure (MC-1 / ZP-P). Under `cnfToZp2` the 2-adic 0 is the image of the seed `towerNONote 0`,
   whose `repr` is ⊥ of `Ordinal` (`seed_maps_to_bot_both`), and the limit of the stages' images; ε₀
   has no image there, since `cnfToZp2` is defined on `NONote` and every notation denotes an ordinal
   below ε₀ (`repr_lt_epsilon0`, `ZeroParadox/Ordinal/PricedInterface.lean`). Through another map ε₀
   does land on that 0: the canonical threshold map sends ε₀ to c₁ and `snapEmbed` sends c₁ to 0
   (`snap_state_zp2_is_zero`), a map value, not an identity.
   Built in the spirit of
   `zpm_triangle` (`Ordinal/Incompleteness.lean`), which co-witnesses without a type identity.

6. **The syntactic depth meets the 2-adic valuation on the tower** (`towerNONote_val`,
   `synVal_tower_eq_valuation`). `Statement:` TOWER-ONLY. Along the tower `synCollapse_epsN` crosses it
   (the first `example` after it); off the tower the two need not agree, because `synVal` ignores the
   coefficient and the remainder (fails at ω+1, the second `example`: `synVal` 2 and 2-adic valuation
   1). At the seed n = 0 the agreement holds by Mathlib's `valuation 0 = 0`; in the other charts 0 has
   norm 0, and valuation ⊤ under `Padic.addValuation` on ℚ_[2]. The statement carries `Classical.choice` (`towerNONote` and
   `cnfToZp2` carry it in their own terms, measured 2026-10-08), so both declarations are
   STATEMENT-CARRIED (`ZeroParadox/Category/ChoiceCannotBe.md` § "Accidental versus essential") and
   the bridge sits here rather than in the choice-free `ZeroParadox/Ordinal/SyntacticCollapse.lean`.
