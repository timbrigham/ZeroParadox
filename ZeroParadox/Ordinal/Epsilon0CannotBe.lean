import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Order.LeastFixedPoint
import ZeroParadox.Valuation.SemilatticeInstance

/-!
# Machine-checked characterization index of ε₀ — what ε₀ IS and what it IS NOT

An index of established results pinning ε₀, Mathlib `Ordinal.epsilon 0`. Every indexed name is
`#check`ed, so the `import`s recompile each home file. It creates no named declarations; § I-b
carries anonymous `example`s, the only things proved here. The `#check`s cannot overclaim; the
glosses can. Long form: `ZeroParadox/Ordinal/Epsilon0CannotBe.md`.

## Engineer's Take

A canonical official representation of what ε₀ can and cannot be. Defined in Lean and referenced by the
proof assistant during development.

---
-/

section Epsilon0CannotBeIndex

/-! ### § I. What ε₀ IS NOT — the invariants (the bedrock guards) -/
#check @ZeroParadox.epsilon0_ne_zero          -- ε₀ ≠ 0, in every reading — the guard beneath all else
#check @ZeroParadox.epsilon0_ne_bot           -- ε₀ ≠ ⊥ of `Ordinal` — the base is never its own closure

/-! ### § I-b. The ε₀ ROLE is never its floor, at any floor in `Ordinal` (the role, not the value)

Unlike the rest of this index, this section proves anonymous `example`s, the file's only proofs. -/
-- Reading: the ε₀ role relative to a floor `f` is the least fixed point of `α ↦ ω^α` strictly above
-- `f`; `f` is the bottom of the carrier `Set.Ici f`.
#check @Ordinal.epsilon_succ_eq_nfp           -- Statement: Mathlib, `ε_(succ o) = nfp (ω^·) (succ ε_o)`
-- Statement: INVARIANT over ordinal floors under `α ↦ ω^α`. At every floor `f`, the least fixed point
-- strictly above ⊥ of `Set.Ici f` is `nfp (ω^·) (succ f)`, and it is not that ⊥.
example (f : Ordinal) :
    IsLeast {x : Ordinal | Ordinal.omega0 ^ x = x ∧ ((⊥ : Set.Ici f) : Ordinal) < x}
      (Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ f)) ∧
    Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ f) ≠ ((⊥ : Set.Ici f) : Ordinal) := by
  have hn := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  have hlt : f < Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ f) :=
    lt_of_lt_of_le (Order.lt_succ f) (Ordinal.le_nfp _ _)
  refine ⟨⟨⟨Ordinal.nfp_fp hn _, hlt⟩, ?_⟩, hlt.ne'⟩
  rintro x ⟨hx, hfx⟩
  exact Ordinal.nfp_le_fp hn.strictMono.monotone (Order.succ_le_of_lt hfx) (le_of_eq hx)
-- Statement: at the floor `0`, ⊥ of `Ordinal`, that occupant is ε₀.
example : Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ 0) = Ordinal.epsilon 0 :=
  ZeroParadox.nfp_seed_independent_below_epsilon0 _ (Order.succ_le_of_lt (Ordinal.epsilon_pos 0))
-- Statement: in `Ordinal`, the at-or-above form `nfp (ω^·) f` returns the floor `f` exactly when `f`
-- is itself a fixed point.
-- Reading: this is why the role is taken strictly above. The strict form differs from the
-- at-or-above μ schema `IsLeastFixedPointFrom` that § II uses for ε₀: at the floor ε₀ the μ schema
-- gives ε₀ (this example and the next) and the strict form gives ε₁ (the role-versus-value example).
example (f : Ordinal) :
    Ordinal.nfp (fun α => Ordinal.omega0 ^ α) f = f ↔ Ordinal.omega0 ^ f = f := by
  refine ⟨fun h => ?_, Ordinal.nfp_eq_self⟩
  have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) f
  rwa [h] at this
-- Statement: in `Ordinal`, the μ schema seeded at ε₀ closes at ε₀ itself.
example : ZeroParadox.IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α)
    (Ordinal.epsilon 0) (Ordinal.epsilon 0) :=
  ⟨le_rfl, Ordinal.omega0_opow_epsilon 0, fun _ _ h => h⟩
-- Statement: CARRIER, role versus value. The value ε₀ is ⊥ of the carrier `Set.Ici ε₀` (and is not
-- ⊥ of `Ordinal`, § I), and in that carrier the ε₀ role is filled by a different value, ε₁.
example :
    ((⊥ : Set.Ici (Ordinal.epsilon 0)) : Ordinal) = Ordinal.epsilon 0 ∧
    IsLeast {x : Ordinal | Ordinal.omega0 ^ x = x ∧ ((⊥ : Set.Ici (Ordinal.epsilon 0)) : Ordinal) < x}
      (Ordinal.epsilon 1) := by
  have hn := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  have e : Ordinal.epsilon 1
      = Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ (Ordinal.epsilon 0)) := by
    rw [← Ordinal.epsilon_succ_eq_nfp, Order.succ_eq_add_one, zero_add]
  refine ⟨rfl, ⟨Ordinal.omega0_opow_epsilon 1, ?_⟩, ?_⟩
  · rw [e]; exact lt_of_lt_of_le (Order.lt_succ _) (Ordinal.le_nfp _ _)
  · rintro x ⟨hx, hlt⟩
    rw [e]
    exact Ordinal.nfp_le_fp hn.strictMono.monotone (Order.succ_le_of_lt hlt) (le_of_eq hx)
-- Statement: every ordinal is ⊥ of its own `Set.Ici`.
-- Reading: so occupying a carrier's bottom singles out no value.
example : ∀ o : Ordinal, ((⊥ : Set.Ici o) : Ordinal) = o := fun _ => rfl
-- Reading: other chart. In ℤ₂ read by its norm, ℤ₂'s 0 is least (`norm_nonneg`); the tower's images
-- tend to that 0 (`mu_construction_correspondence`), and ε₀ gets no image: `cnfToZp2` takes `NONote`,
-- the notations below ε₀ (`cnf_bridge_type_boundary` co-witnesses the two limits, no identity).

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
#check @ZeroParadox.cnf_bridge_type_boundary  -- co-witness only; ε₀ = 0 never asserted (it fails to elaborate, `Ordinal` vs `ℤ_[2]`)

/-! ### § VI. The loop returns to a ⊥, never to ε₀ (the *successor* reading is a commitment) -/
#check @ZeroParadox.t_iz_limit_is_new_null    -- role half only: (∀ x, join terminal x = x) → terminal = bot. No chain, no limit, no novelty in the statement; "a fresh instance" is the framework's reading, not this theorem

end Epsilon0CannotBeIndex
