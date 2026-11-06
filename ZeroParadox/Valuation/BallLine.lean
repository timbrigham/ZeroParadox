-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the line of closed balls about 0 of `ℚ_[2]`, indexed by `ℤ`, its covers, its two ends, and the radius chart. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCornersBridge
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.Valuation.InversionValuation
import ZeroParadox.Reals.OrderedField
import Mathlib.Data.Int.Log
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Path
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The line of closed balls about 0 of `ℚ_[2]`: a cover at every vertex, none at either end

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
`ballLine n`, the closed ball of radius `2^(-n)` about 0 of `ℚ_[2]`, `n : ℤ`. § I: membership is the
valuation. § II: shells, the arc, inversion. § III: covers at vertices, none at the ends of
`WithBot (WithTop ℤ)`. § IV: radii in `ℝ≥0∞`, a path with no cover, read back onto the vertices.
-/

namespace ZeroParadox

/-! ### § I. The line: one closed ball per integer, membership read off the valuation -/

/-- `Statement:` vertex `n`: the closed ball of radius `2 ^ (-n)` about 0 of `ℚ_[2]`. -/
noncomputable def ballLine (n : ℤ) : Set ℚ_[2] := Metric.closedBall (0 : ℚ_[2]) ((2 : ℝ) ^ (-n))

-- Statement: at `n : ℕ` it is the ball tower `q2Ball n` (`ZeroParadox/Valuation/TopFunctor.lean`).
example (n : ℕ) : ballLine n = q2Ball n := rfl

/-- `Statement:` a nonzero `x` lies in `ballLine n` iff `n ≤ x.valuation`. -/
theorem mem_ballLine_iff_le_valuation {x : ℚ_[2]} (hx : x ≠ 0) (n : ℤ) :
    x ∈ ballLine n ↔ n ≤ x.valuation := by
  rw [ballLine, Metric.mem_closedBall, dist_zero_right, Padic.norm_eq_zpow_neg_valuation hx]
  push_cast
  rw [zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)]
  omega

/-- `Statement:` `ballLine` is strictly antitone: a larger index gives a strictly smaller ball. -/
theorem ballLine_strictAnti : StrictAnti ballLine := by
  intro a b hab
  have h2 : ∀ k : ℤ, (2 : ℚ_[2]) ^ k ≠ 0 := fun k => zpow_ne_zero _ two_ne_zero
  have hv : ∀ k : ℤ, ((2 : ℚ_[2]) ^ k).valuation = k := fun k => by
    rw [Padic.valuation_zpow, (by simp : (2 : ℚ_[2]).valuation = 1), mul_one]
  refine ⟨Metric.closedBall_subset_closedBall
    (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)), fun h => ?_⟩
  have := (mem_ballLine_iff_le_valuation (h2 a) b).1
    (h ((mem_ballLine_iff_le_valuation (h2 a) a).2 (hv a).ge))
  rw [hv] at this
  omega

-- Statement: the balls meet in `{0}`, by `fB_bottom_is_limit` on the `ℕ` half.
example : (⋂ n : ℤ, ballLine n) = {0} := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · rw [← fB_bottom_is_limit]
    exact Set.mem_iInter.2 fun n : ℕ => Set.mem_iInter.1 hx (n : ℤ)
  · rintro x rfl
    exact Set.mem_iInter.2 fun n => Metric.mem_closedBall_self (by positivity)

/-- `Statement:` the balls cover `ℚ_[2]`. -/
theorem iUnion_ballLine : (⋃ n : ℤ, ballLine n) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  by_cases hx : x = 0
  · exact ⟨0, hx ▸ Metric.mem_closedBall_self (by positivity)⟩
  · exact ⟨x.valuation, (mem_ballLine_iff_le_valuation hx _).2 le_rfl⟩

/-! ### § II. Shells, the arc's stages, and inversion -/

/-- `Statement:` the shell `ballLine n \ ballLine (n + 1)` is the set of nonzero points of valuation
    `n`. -/
theorem mem_ballLine_shell_iff (x : ℚ_[2]) (n : ℤ) :
    x ∈ ballLine n \ ballLine (n + 1) ↔ x ≠ 0 ∧ x.valuation = n := by
  by_cases hx : x = 0
  · subst hx
    simp only [Set.mem_diff, ne_eq, not_true_eq_false, false_and, iff_false, not_and, not_not]
    exact fun _ => Metric.mem_closedBall_self (by positivity)
  · rw [Set.mem_diff, mem_ballLine_iff_le_valuation hx, mem_ballLine_iff_le_valuation hx]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hx, by omega⟩
    · rintro ⟨-, h⟩; omega

/-- `Statement:` the `cnfToZp2` image of `towerNONote (n + 1)`, read in `ℚ_[2]`, lies in the shell at
    vertex `n + 1`. -/
theorem arc_walks_ballLine (n : ℕ) :
    ((cnfToZp2 (towerNONote (n + 1)) : ℤ_[2]) : ℚ_[2]) ∈
      ballLine ((n : ℤ) + 1) \ ballLine ((n : ℤ) + 1 + 1) := by
  have hstage : cnfToZp2 (towerNONote (n + 1)) = (2 : ℤ_[2]) ^ (n + 1) := by
    rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote, towerImageStep, cnfToZp2_tower_valuation]
  have hc : (((2 : ℤ_[2]) ^ (n + 1) : ℤ_[2]) : ℚ_[2]) = (2 : ℚ_[2]) ^ ((n : ℤ) + 1) := by
    rw [PadicInt.coe_pow]; norm_cast
  rw [hstage, hc, mem_ballLine_shell_iff]
  exact ⟨zpow_ne_zero _ two_ne_zero,
    by rw [Padic.valuation_zpow, (by simp : (2 : ℚ_[2]).valuation = 1), mul_one]⟩

-- Statement: stage 0 is 0 of `ℚ_[2]` (`snap_arc_z2_loop`), which lies in every vertex.
example (n : ℤ) : ((cnfToZp2 (towerNONote 0) : ℤ_[2]) : ℚ_[2]) ∈ ballLine n := by
  rw [snap_arc_z2_loop.1, PadicInt.coe_zero]
  exact Metric.mem_closedBall_self (by positivity)

/-- `Statement:` `x ↦ x⁻¹` maps the shell at `n` onto the shell at `-n`. The sublevel form is
    `inversion_reverses_filtration`. -/
theorem ballLine_inv_shell (n : ℤ) :
    (fun x : ℚ_[2] => x⁻¹) '' (ballLine n \ ballLine (n + 1)) =
      ballLine (-n) \ ballLine (-n + 1) := by
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_ballLine_shell_iff] at hx ⊢
    exact ⟨inv_ne_zero hx.1, by rw [Padic.valuation_inv, hx.2]⟩
  · intro hy
    rw [mem_ballLine_shell_iff] at hy
    refine ⟨y⁻¹, ?_, inv_inv y⟩
    rw [mem_ballLine_shell_iff]
    exact ⟨inv_ne_zero hy.1, by rw [Padic.valuation_inv, hy.2, neg_neg]⟩

-- Statement: in `ℚ_[2]` inversion fixes 0 (`inv_zero`).
example : (0 : ℚ_[2])⁻¹ = 0 := inv_zero

-- Statement: `n ↦ -n` reverses inclusion of vertices.
example (a b : ℤ) : ballLine a ⊆ ballLine b ↔ ballLine (-b) ⊆ ballLine (-a) := by
  change ballLine a ≤ ballLine b ↔ ballLine (-b) ≤ ballLine (-a)
  rw [ballLine_strictAnti.le_iff_ge, ballLine_strictAnti.le_iff_ge]; omega

/-! ### § III. Covers at every vertex; none leaving either end -/

/-- `Statement:` in the vertex set `Set.range ballLine` under inclusion, `ballLine (n + 1)` is covered
    by `ballLine n`. -/
theorem ballLine_covBy (n : ℤ) :
    (⟨ballLine (n + 1), n + 1, rfl⟩ : Set.range ballLine) ⋖ ⟨ballLine n, n, rfl⟩ := by
  refine ⟨Subtype.mk_lt_mk.2 (ballLine_strictAnti (by omega)), ?_⟩
  rintro ⟨_, m, rfl⟩ h1 h2
  have h1' : ballLine (n + 1) < ballLine m := h1
  have h2' : ballLine m < ballLine n := h2
  rw [ballLine_strictAnti.lt_iff_gt] at h1' h2'
  omega

-- Statement: so every vertex has a first step (`HasFirstStep`).
example (n : ℤ) : HasFirstStep (⟨ballLine n, n, rfl⟩ : Set.range ballLine) :=
  ⟨_, by simpa using ballLine_covBy (n - 1)⟩

-- Statement: the vertex set is order-isomorphic to `ℤᵒᵈ` (Mathlib's `StrictMono.orderIso`).
noncomputable example : ℤᵒᵈ ≃o Set.range (ballLine ∘ OrderDual.ofDual) :=
  StrictMono.orderIso _ ballLine_strictAnti.dual_left

/-- `Statement:` in `WithBot (WithTop ℤ)`, the line with both ends adjoined, ⊥ has no first step. -/
theorem end_bot_no_first_step : ¬ HasFirstStep (⊥ : WithBot (WithTop ℤ)) := by
  rintro ⟨a, ha⟩
  induction a using WithBot.recBotCoe with
  | bot => exact lt_irrefl _ ha.1
  | coe b => exact not_isMin b (WithBot.bot_covBy_coe.1 ha)

/-- `Statement:` in `WithBot (WithTop ℤ)`, nothing is covered by ⊤. -/
theorem end_top_covers_nothing : ¬ ∃ b : WithBot (WithTop ℤ), b ⋖ ⊤ := by
  rintro ⟨b, hb⟩
  induction b using WithBot.recBotCoe with
  | bot => exact end_bot_no_first_step ⟨_, hb⟩
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact lt_irrefl _ hb.1
    | coe k => exact not_isMax k (WithTop.coe_covBy_top.1 (WithBot.coe_covBy_coe.1 hb))

/-! ### § IV. The radius chart: a path between the ends, no cover, collapse onto the vertices -/

/-- `Statement:` for `r > 0`, `closedBall 0 r = ballLine (-(Int.log 2 r))` in `ℚ_[2]`. -/
theorem closedBall_eq_ballLine {r : ℝ} (hr : 0 < r) :
    Metric.closedBall (0 : ℚ_[2]) r = ballLine (-(Int.log 2 r)) := by
  ext x
  rw [ballLine, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right, neg_neg]
  have hlo : (2 : ℝ) ^ (Int.log 2 r) ≤ r := by
    have := Int.zpow_log_le_self (R := ℝ) (b := 2) (by norm_num) hr; exact_mod_cast this
  have hhi : r < (2 : ℝ) ^ (Int.log 2 r + 1) := by
    have := Int.lt_zpow_succ_log_self (R := ℝ) (b := 2) (by norm_num) r; exact_mod_cast this
  by_cases hx : x = 0
  · subst hx; simp only [norm_zero]; exact ⟨fun _ => by positivity, fun _ => hr.le⟩
  · rw [Padic.norm_eq_zpow_neg_valuation hx]; push_cast
    constructor
    · intro h
      have hv : -x.valuation ≤ Int.log 2 r := by
        by_contra hc
        have := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : Int.log 2 r + 1 ≤ -x.valuation)
        linarith
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hv
    · exact fun h => le_trans h hlo

-- Statement: radius 0 gives `{0}`.
example : Metric.closedBall (0 : ℚ_[2]) 0 = {0} := Metric.closedBall_zero

/-- `Statement:` a path in `ℝ≥0∞` from 0 to ⊤, through `ENNReal.orderIsoUnitIntervalBirational`. -/
noncomputable def radiusPath : Path (0 : ENNReal) ⊤ where
  toFun t := ENNReal.orderIsoUnitIntervalBirational.symm t
  continuous_toFun := ENNReal.orderIsoUnitIntervalBirational.symm.toHomeomorph.continuous
  source' := ENNReal.orderIsoUnitIntervalBirational.symm.map_bot
  target' := ENNReal.orderIsoUnitIntervalBirational.symm.map_top

-- Statement: control, `ℝ≥0∞` is densely ordered, so 0 has no first step there
-- (`axb1_fails_everywhere_iff_dense`).
example : ¬ HasFirstStep (0 : ENNReal) := axb1_fails_everywhere_iff_dense.1 inferInstance 0

-- Statement: the two orders side by side. In `WithBot (WithTop ℤ)` every `n : ℤ` has a first step, ⊥
-- has none, ⊤ covers nothing and ⊥ ≠ ⊤; in `ℝ≥0∞` a path runs from 0 to ⊤ and 0 has no first step.
example : (∀ n : ℤ, HasFirstStep ((n : WithTop ℤ) : WithBot (WithTop ℤ))) ∧
    ¬ HasFirstStep (⊥ : WithBot (WithTop ℤ)) ∧ (¬ ∃ b : WithBot (WithTop ℤ), b ⋖ ⊤) ∧
    (⊥ : WithBot (WithTop ℤ)) ≠ ⊤ ∧
    Nonempty (Path (0 : ENNReal) ⊤) ∧ ¬ HasFirstStep (0 : ENNReal) :=
  ⟨fun n => ⟨_, WithBot.coe_covBy_coe.2 (WithTop.coe_covBy_coe.2 (Order.covBy_succ n))⟩,
    end_bot_no_first_step, end_top_covers_nothing, bot_ne_top, ⟨radiusPath⟩,
    axb1_fails_everywhere_iff_dense.1 inferInstance 0⟩
-- Reading: CARRIER. Indexed as `ballLine`'s `n`, ⊤ of `WithBot (WithTop ℤ)` stands at the `{0}` end and
-- ⊥ at the `ℚ_[2]` end; the two ends are distinct and neither is reached from a vertex by a cover. Of
-- the two orders here, the first has a cover at every vertex and none at either end, the second joins
-- its ends by a path and has no cover at 0; read back as balls, a positive radius lands on a vertex
-- (`closedBall_eq_ballLine`). Neither of the two has both a passage between its ends and a first step.

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms ballLine
#print axioms mem_ballLine_iff_le_valuation
#print axioms ballLine_strictAnti
#print axioms iUnion_ballLine
#print axioms mem_ballLine_shell_iff
#print axioms arc_walks_ballLine
#print axioms ballLine_inv_shell
#print axioms ballLine_covBy
#print axioms end_bot_no_first_step
#print axioms end_top_covers_nothing
#print axioms closedBall_eq_ballLine
#print axioms radiusPath
end PurityCheck
