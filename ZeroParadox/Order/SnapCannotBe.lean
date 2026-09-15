import ZeroParadox.Order.Snap
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Valuation.SnapDichotomy
import ZeroParadox.Reals.OrderedField

/-!
# Machine-checked characterization index of the snap ⊥ → ε₀ — what the snap IS and IS NOT

The snap leg of the trio with `ZeroParadox/BottomCannotBe.lean` and
`ZeroParadox/Ordinal/Epsilon0CannotBe.lean`. Every line `#check`s an already-proven **declaration**.
⚠ The `#check`s cannot overclaim; the glosses can, and §§ I-IV predate § V's label convention.

Bedrock: shape **derived**, not an axiom (`t_snap_derived`; AX-1 is retired, and the snap occurs given the occurrence commitment and DA-1); **one-way** (`t_snap_irreversible`); returns to
a ⊥ read as a successor null, where **the novelty is a commitment** — the § IV glosses carry the fence.

## Engineer's Take

A canonical official representation of what the snap can and cannot be. Defined in Lean and referenced
by the proof assistant during development.
-/

section SnapCannotBeIndex

/-! ### § I. What the snap IS NOT — not an axiom, not reversible, not a return to the same ⊥ -/
#check @ZeroParadox.t_snap_derived                    -- DERIVED (c₀ ≠ c₁ ∧ c₁ ≠ c₀ ∧ join c₀ c₁ = c₁) — the shape (AX-1 is retired); that the snap occurs follows from the occurrence commitment together with DA-1, not from this line, and the next line is why
#check @ZeroParadox.tsnap_holds_but_nothing_moves     -- Statement: T-SNAP's statement holds together with a dynamics `stuckPhase` in which every phase is fixed, so T-SNAP is not an occurrence claim
#check @ZeroParadox.t_snap_irreversible              -- NOT reversible: no join from ε₀ returns to ⊥
#check @ZeroParadox.dp2_execution_distinguishability  -- the post-snap null ≠ the pre-snap null (distinct instances)
#check @ZeroParadox.da1_minimal_path                  -- Statement: the two configurations are DISTINCT while sharing an output value. It does NOT carry that the step is taken, and irrecoverability is not in it — see the fence in its home docstring

/-! ### § II. What the snap IS — the SHAPE of the join transition ⊥ → ε₀; that it occurs follows from the occurrence commitment and DA-1 -/
#check @ZeroParadox.t_snap_join                       -- the algebraic core: ⊥ ∨ ε₀ = ε₀ (from A4/bot_join)
#check @ZeroParadox.t_snap_machine                    -- concrete: c₀ ∨ c₁ = c₁ (initial → running)
#check @ZeroParadox.t_snap_given                      -- Statement: over any ZPSemilattice, `S 0 = bot` (CC-1) and `S 1 ≠ S 0` (occurrence at the first step) give `t_snap_derived`'s shape at S 0, S 1; the inequalities restate `hocc`, and only the join comes from A4. No binder makes `S 1` an atom above `S 0`, and the step is assumed (`hocc`), not forced. Two commitments are the binders; `t_snap_derived` is its MachinePhase instance at a sequence chosen to move, and `MachinePhase` does not discharge `hocc`
-- Reading: CARRIER. "⊥ → ε₀" in the lines that use c₁ (`t_snap_derived`, `t_snap_machine`) is the
--   discrete-state chart, where ε₀ names the first state above ⊥ (c₁ in `MachinePhase`), and "atom above
--   ⊥" is a claim in that chart only. `t_snap_join`, `t_snap_irreversible` and
--   `t_snap_accessible_proper_subset` are generic: they hold at other points too, `t_snap_join` at ⊥
--   itself. The ordinal ε₀ is indexed in `ZeroParadox/Ordinal/Epsilon0CannotBe.lean`: the operator
--   α ↦ ω^α seeded at the base ⊥ (`epsilon0_eq_nfp_bot`), least fixed point AND tower supremum at once
--   (`epsilon0_min_eq_max`), never ⊥ (`epsilon0_ne_bot`). One order, restricted to two carriers, gives
--   two answers on covering. On all ordinals ⊥ ⋖ ε₀ is FALSE: 1 lies strictly between (first example).
--   On the carrier {0} ∪ {fixed points of α ↦ ω^α}, where 0 is adjoined by definition (`Or.inl`), ε₀
--   DOES cover ⊥, since no fixed point lies below it (`nothing_between_is_a_step`; last example).
example : ¬ ((⊥ : Ordinal) ⋖ Ordinal.epsilon 0) := fun h =>
  h.2 (show (⊥ : Ordinal) < 1 by rw [Ordinal.bot_eq_zero]; exact zero_lt_one)
    (lt_trans Ordinal.one_lt_omega0 (Ordinal.omega0_lt_epsilon 0))
-- `Statement:` ε₀ is a limit ordinal: it is not minimal (`Ordinal.epsilon_pos`) and covers no ordinal
-- at all (no `b` has `b ⋖ ε₀`).
example : Order.IsSuccLimit (Ordinal.epsilon 0) := by
  refine Order.IsSuccPrelimit.isSuccLimit_of_not_isMin ?_ (not_isMin_iff.2 ⟨0, Ordinal.epsilon_pos 0⟩)
  rw [Ordinal.isSuccPrelimit_iff_omega0_dvd, ← Ordinal.omega0_opow_epsilon 0]
  simpa only [Ordinal.opow_one] using
    Ordinal.opow_dvd_opow Ordinal.omega0 (Order.one_le_iff_pos.2 (Ordinal.epsilon_pos 0))
example : (⟨0, Or.inl rfl⟩ : {o : Ordinal | o = 0 ∨ Ordinal.omega0 ^ o = o}) ⋖
    ⟨Ordinal.epsilon 0, Or.inr ZeroParadox.epsilon0_is_fixedpoint⟩ := by
  refine ⟨Ordinal.epsilon_pos 0, ?_⟩
  rintro ⟨c, hc | hc⟩ h0 hε
  · exact (ne_of_gt (show (0 : Ordinal) < c from h0)) hc
  · exact ZeroParadox.nothing_between_is_a_step c hε hc

/-! ### § III. What the snap DOES — it narrows reachability, permanently -/
#check @ZeroParadox.t_snap_accessible_proper_subset   -- from ε₀ only a proper subset is reachable; ⊥ is foreclosed
#check @ZeroParadox.da2_bottom_characterization       -- the ⊥ role: (∀ x, join S x = x) ↔ S = ⊥
#check @ZeroParadox.da3_accessibleCardinality         -- reachable cardinality is position-relative

/-! ### § IV. The snap returns to a ⊥ (read as a successor null — a commitment); its 2-adic realization is a loop -/
#check @ZeroParadox.c_da2_novelty                     -- contrapositive of the role fact: a non-⊥ state cannot satisfy the join-identity. "Distinct successor instantiation" is the reading, not the statement
#check @ZeroParadox.snap_arc_z2_loop                  -- the ℤ₂ realization: start 0, depart, reapproach 0
#check @ZeroParadox.t_iz_limit_is_new_null            -- role half only: (∀ x, join terminal x = x) → terminal = bot. Novelty is NOT in this statement; do not cite it as the novelty witness

/-! ### § V. WHERE the snap is RULED OUT — and what only removes the obstruction

Reading: CARRIER. These lines BOUND the snap; none supplies it. ZP-F rules it out in every ordered
field; ZP-B removes the topological obstruction in ℚ_p without replacing it. The first step is AX-B1,
a modelling commitment, never a carrier property. AX-B1 holds at the bottom and at every iterative
bottom: every state with anything above it has a first distinct state above it, with nothing strictly
between. A state with nothing above it owes no step. -/
#check @ZeroParadox.HasFirstStep                      -- Statement: an ORDER predicate — `∃ a, bot ⋖ a`, Mathlib's covering relation. ⚠ `LT ℚ_[p]` does not synthesize, so this is not statable of ℚ_p; the p-adic line below fences NORM values, a different predicate
#check @ZeroParadox.f_snap_blocked                    -- Statement: over `Field + LinearOrder + IsStrictOrderedRing`, every positive ε₀ admits a smaller positive δ
#check @ZeroParadox.f_snap_impossible                 -- Statement: hence no such field has a least positive element. No Archimedean hypothesis appears in the binders
#check @ZeroParadox.axb1_fails_in_ordered_field       -- Statement: `¬ HasFirstStep (0 : F)`. Reading: AX-B1 is what supplies the step, and it is a commitment rather than a carrier property
#check @ZeroParadox.axb1_fails_everywhere_iff_dense   -- Statement: the obstruction CHARACTERIZED, over a bare `Preorder` with no field and no topology — `DenselyOrdered α ↔ ∀ bot, ¬ HasFirstStep bot`. `axb1_fails_in_ordered_field` directly above is an instance of its right-hand side; `f_snap_impossible` is the same fact in the halving vocabulary, not an instance of this statement. Density is what obstructs a first step — connectedness is a separate, topological fence (`real_no_snap`)
#check @ZeroParadox.real_no_snap                      -- Statement: CARRIER — ℝ is NOT totally disconnected
#check @ZeroParadox.padic_snaps                       -- Statement: CARRIER — ℚ_p IS totally disconnected. Reading: this removes the obstruction and supplies no first step — norms accumulate at 0 in ANY non-trivially normed field (Mathlib `NormedField.exists_norm_lt`), ℝ included, so that half is not p-adic
#check @ZeroParadox.snap_dichotomy                    -- Statement: for NONTRIVIAL absolute values on ℚ, real and p-adic are exclusive and exhaustive (Ostrowski). ⚠ SCOPE: completions of ℚ only

end SnapCannotBeIndex
