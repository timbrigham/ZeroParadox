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
⚠ **"First"/"minimum" here means LEAST AMONG THE FIXED POINTS of `α ↦ ω^α`, never order-adjacent
to ⊥.** The corpus's own `epsilonZero_tower_lt` (`ZeroParadox/Ordinal/Gentzen.lean`) exhibits
infinitely many ordinals strictly between ⊥ and ε₀, so no adjacency claim is available on this
carrier; applied to `Ordinal`, `HasFirstStep` is witnessed by `1` (`0 ⋖ 1`), not by ε₀. The *never
it* half IS backed — `epsilon0_ne_zero`,
`epsilon0_ne_bot`; only the adjacency half is a reading, and it is labelled as one above.

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
