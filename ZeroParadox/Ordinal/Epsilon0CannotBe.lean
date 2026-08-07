import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Order.LeastFixedPoint
import ZeroParadox.Valuation.SemilatticeInstance

/-!
# Machine-checked characterization index of ε₀ — what ε₀ IS and what it IS NOT

The ε₀ counterpart of `ZeroParadox/BottomCannotBe.lean`. A `#check`-only index of established results
pinning ε₀ (Mathlib `Ordinal.epsilon 0 = veblen 1 0`), organized into **IS NOT** (the invariants — the
bedrock guards, apophatic register) and **IS** (its positive roles). No new claims are made here; every
line `#check`s an already-proven theorem, so the `import`s recompile each home file and the index cannot
point at a dead or renamed result. A `#check`-only index creates no declarations and so *structurally
cannot overclaim* ε₀'s nature.

## Engineer's Take

A canonical official representation of what ε₀ can and cannot be. Defined in Lean and referenced by the
proof assistant during development.

---

## Formal Overview (AI-assisted)

**This is the ε₀-characterization object.** ε₀ is not a "large ordinal" chosen by fiat; it is the
*first (least) fixed point of the ω-tower operator `α ↦ ω^α` reached from the base ⊥* — two conditions,
the operator AND the base (`ε₀ = nfp (ω^·) ⊥`, `epsilon0_eq_nfp_bot`; Mathlib `ε₀ = deriv (ω^·) 0`).
It is *simultaneously* the least fixed point (min) and the supremum of the ascending tower (max)
(`epsilon0_min_eq_max`); which face is in play is direction- and instance-specific — the two are never
to be collapsed into one. In the framework's Riemann-sphere reading it is the minimum step directly
next to the pole 0 = ∞ (Veblen coordinates (1, 0); the reciprocal 1/∞), *adjacent to it, never it*.
**ε₀ IS the minimum distinct step above ⊥, and that is now witnessed** — but "step" means a
**stable landing**, a fixed point of `α ↦ ω^α`, and the distinction is worth stating because both
readings are true of different orders:
* **In the FIXED-POINT order ε₀ is the minimum, and nothing below it is a step at all.**
  `nothing_between_is_a_step` — no ordinal strictly under ε₀ is fixed by the operator;
  `bot_is_not_a_step` — ⊥ is not one either, so ε₀ is the FIRST. The ordinals in between (`ω`,
  `ω^ω`, …) are **stages of the ascent, not landings**: the operator fixes none of them, so nothing
  stops there. This is why `snapNucleus ⊥ = ε₀` reaches it in **one** application — a closure
  operator's image *is* its fixed points, so the first landing is the least one.
* **In the ORDINAL order it is not adjacent, and no covering claim is made.** ⊥ ⋖ ε₀ is false;
  ordinals sit strictly between (`epsilonZero_tower_lt` with `fundamentalSeq_strictMono`), and
  applied to `Ordinal` the corpus's `HasFirstStep` is witnessed by `1`. So
  `epsilon0_least_fixedpoint` must never be cited as proving a covering relation — and note it is
  only the lower-bound half; the full `IsLeast` is `epsilon0_min_eq_max`.

⚠ **Correction history, because this line was wrong in BOTH directions.** It once read that
`epsilon0_least_fixedpoint` proves "the minimum step next to the pole", which credited it with an
adjacency it does not prove. A 2026-08-06 pass then **struck the whole phrase**, which was an
over-correction — the claim is true in the fixed-point order and is Tim's, and the strike removed a
grounded reading to buy a precision that a distinction supplies for free. Both errors are recorded so
neither is repeated.

**The bedrock invariant, stated first because every past error violated it: ε₀ ≠ 0. It cannot be.**
ε₀ is a fixed point (`ω^ε₀ = ε₀`); were it 0 that would say `1 = 0`. Since `⊥ = 0`, also `ε₀ ≠ ⊥`:
⊥ is the *base fed in*, ε₀ the *closure that comes out* — never equal. Any prose, figure, or docstring
that entertains `ε₀ = 0` (a "fence," a "co-location at 0") is wrong by this guard. When a 2-adic
encoding sends the tower's images toward the value 0, that 0 is ⊥ (read as a successor null — the
2-adic arc in fact reapproaches the same 0), NOT ε₀;
`cnfToZp2` is order-reversing, so the ordinal ascent toward ε₀ is the ℤ₂-norm descent toward ⊥.

Read this index (and the theorems it points at) before writing anything about ε₀.
-/

section Epsilon0CannotBeIndex

/-! ### § I. What ε₀ IS NOT — the invariants (the bedrock guards) -/
#check @ZeroParadox.epsilon0_ne_zero          -- ε₀ ≠ 0, in every reading — the guard beneath all else
#check @ZeroParadox.epsilon0_ne_bot           -- ε₀ ≠ ⊥ — the base is never its own closure

/-! ### § II. What ε₀ IS — the construction: first fixed point of the ω-tower from the base ⊥ -/
#check @ZeroParadox.epsilon0_eq_nfp_bot       -- ε₀ = nfp (ω^·) ⊥ (seeded at the base ⊥)
#check @ZeroParadox.epsilonZero_eq_nfp        -- ε₀ = nfp (ω^·) 0
#check @ZeroParadox.epsilon0_is_fixedpoint    -- ω ^ ε₀ = ε₀ (it is a fixed point)
#check @ZeroParadox.epsilon0_isLeastFixedPointFrom  -- ε₀ = the least fixed point from the base ⊥ (μ schema)
#check @ZeroParadox.epsilon0_eq_veblen_one_zero     -- ε₀ = veblen 1 0 — coords (1,0), the minimum closure, below Γ₀

/-! ### § III. ε₀ is BOTH min AND max at once — direction/instance-specific, never collapsed -/
#check @ZeroParadox.epsilon0_min_eq_max       -- one object: sup of the tower ∧ least fixed point
#check @ZeroParadox.epsilon0_least_fixedpoint -- the MIN face: least ordinal fixed by ω^·
#check @ZeroParadox.epsilonZero_eq_iSup       -- the MAX face: supremum of the ω-tower
#check @ZeroParadox.nothing_between_is_a_step -- sharpens the MIN face: NO ordinal below ε₀ is fixed by ω^· — the in-between ordinals are stages of the ascent, not landings
#check @ZeroParadox.bot_is_not_a_step         -- and ⊥ is not fixed either, so ε₀ is the FIRST landing. NB: "first" in the FIXED-POINT order; ⊥ ⋖ ε₀ is false and is not claimed

/-! ### § IV. ε₀ as the snap threshold ⊥ → ε₀, co-witnessed with the 2-adic limit and the machine snap -/
#check @ZeroParadox.epsilonZero_fixedPoint    -- ε₀ the fixed point the snap lands the ascent on
#check @ZeroParadox.snap_exactly_at_epsilon_zero
#check @ZeroParadox.c1_epsilon_zero_identification
#check @ZeroParadox.zpm_triangle              -- ε₀ ∧ 2-adic limit: tower stages, snap value, convergence, embedding (NB no computational conjunct)
#check @ZeroParadox.both_fixed_points_exist   -- quine ∧ ε₀ co-witnessed: each diagonalization yields a fixed point in its own domain (a conjunction, not a cross-domain identity)

/-! ### § V. The 2-adic realization (`cnfToZp2` order-reversing; ε₀ ≠ 0 preserved, no identity) -/
#check @ZeroParadox.snap_arc_z2_loop          -- start 0, ∀n≥1 ≠0, reapproach 0 (the loop)
#check @ZeroParadox.mu_construction_correspondence  -- one tower, two carrier closures (ε₀ ; 0)
#check @ZeroParadox.cnf_bridge_type_boundary  -- co-witness only; ε₀ = 0 never asserted (ill-typed)

/-! ### § VI. The loop returns to a ⊥, never to ε₀ (the *successor* reading is a commitment) -/
#check @ZeroParadox.t_iz_limit_is_new_null    -- role half only: (∀ x, join terminal x = x) → terminal = bot. No chain, no limit, no novelty in the statement; "a fresh instance" is the framework's reading, not this theorem

end Epsilon0CannotBeIndex
