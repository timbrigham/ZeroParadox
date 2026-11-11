-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the covers of ⊥ of `End` and the depth cells of `boundaryDouble`, one index. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PoleCompletion
import ZeroParadox.Valuation.InfinitudeFloor
import ZeroParadox.Information.TwoRequirements
import Mathlib.Topology.Constructions
import Mathlib.Tactic

/-!
# Cells and covers at ⊥ of `End`: depth and starting location carried by one index

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

"Bottom is concurrently infinitely deep and has infinitely many starting locations. That's what the
cells are for."

---

## Formal Overview (AI-assisted)
The covers (atoms) of ⊥ of `End` are the unit vectors `unitEnd k` (`covers_bot_iff`), the
`boundaryDouble`-orbit of `unitEnd 0`; `unitEnd k` lies in `boundaryCell k` only, depth is `endVal`
(`mem_boundaryCell_iff`), and both together force branching (`branching_forced`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology

/-! ### § I. ZP-A's induced order on `End`, pointwise, and Mathlib's `Pi` order. -/

/-- ZP-A's induced `≤` on `End` (via `instZPSemilatticeEnd`). -/
abbrev endZle (x y : End) : Prop := (zpSemilatticeSup End).le x y
/-- ZP-A's induced `<` on `End`. -/
abbrev endZlt (x y : End) : Prop := (zpSemilatticeSup End).lt x y
/-- ZP-A's induced cover relation on `End`. -/
abbrev endZcov (x y : End) : Prop := @CovBy End (zpSemilatticeSup End).toLT x y

/-- `Statement:` ZP-A's `≤` on `End` is digitwise `≤` on values. -/
theorem endZle_iff (x y : End) : endZle x y ↔ ∀ n, (x n).val ≤ (y n).val := by
  constructor
  · intro h n
    have := congrArg Fin.val (congrFun h n)
    change max (x n).val (y n).val = (y n).val at this
    exact this ▸ Nat.le_max_left _ _
  · intro h
    funext n
    exact Fin.ext (Nat.max_eq_right (h n))

/-- `Statement:` ZP-A's `≤` on `End` is Mathlib's `Pi` order. -/
theorem endZle_iff_le (x y : End) : endZle x y ↔ x ≤ y := endZle_iff x y

/-- `Statement:` ZP-A's `<` on `End` is `≤` and not `≥`. -/
theorem endZlt_iff (x y : End) : endZlt x y ↔ endZle x y ∧ ¬ endZle y x :=
  @lt_iff_le_not_ge End (zpSemilatticeSup End).toPreorder x y

/-- `Statement:` ZP-A's `<` on `End` is Mathlib's `Pi` `<`. -/
theorem endZlt_iff_lt (x y : End) : endZlt x y ↔ x < y := by
  rw [endZlt_iff, lt_iff_le_not_ge, endZle_iff_le, endZle_iff_le]

/-- `Statement:` ZP-A's cover relation on `End` is Mathlib's `CovBy` for the `Pi` order. -/
theorem endZcov_iff_covBy (x y : End) : endZcov x y ↔ x ⋖ y := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(endZlt_iff_lt _ _).1 h1,
      fun c hc1 hc2 => h2 ((endZlt_iff_lt _ _).2 hc1) ((endZlt_iff_lt _ _).2 hc2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(endZlt_iff_lt _ _).2 h1,
      fun c hc1 hc2 => h2 ((endZlt_iff_lt _ _).1 hc1) ((endZlt_iff_lt _ _).1 hc2)⟩

/-- `Statement:` every binary digit is `0` or `1`. -/
theorem fin2_eq_zero_or_one (a : Fin 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- `Statement:` the only end ZP-A-below ⊥ of `End` is `botEnd`. -/
theorem endZle_bot_iff (x : End) : endZle x botEnd ↔ x = botEnd := by
  rw [endZle_iff]
  constructor
  · intro h; funext n; exact Fin.ext (Nat.le_zero.1 (h n))
  · rintro rfl n; exact Nat.le_refl _

/-! ### § II. The unit vectors: one `boundaryDouble` per step. -/

/-- The unit vector `unitEnd k`: a single `1` at position `k` (`localMember [] k` of `LocalFloor`). -/
def unitEnd (k : ℕ) : End := fun n => if n = k then 1 else 0

theorem unitEnd_self (k : ℕ) : unitEnd k k = 1 := ite_eq_left rfl
theorem unitEnd_ne {k n : ℕ} (h : n ≠ k) : unitEnd k n = 0 := ite_eq_right h

/-- `Statement:` `unitEnd k ≠ botEnd`. -/
theorem unitEnd_ne_bot (k : ℕ) : unitEnd k ≠ botEnd := fun h => by
  have := congrFun h k
  rw [unitEnd_self] at this
  change (1 : Fin 2) = 0 at this
  exact absurd this (by decide)

/-- `Statement:` `unitEnd` is one-to-one. -/
theorem unitEnd_injective : Function.Injective unitEnd := fun a b h => by
  have := congrFun h a
  rw [unitEnd_self] at this
  exact Decidable.byContradiction fun hab =>
    absurd ((unitEnd_ne hab).symm.trans this.symm) (by decide)

/-- `Statement:` `boundaryDouble (unitEnd k) = unitEnd (k + 1)`. -/
theorem boundaryDouble_unitEnd (k : ℕ) : boundaryDouble (unitEnd k) = unitEnd (k + 1) := by
  funext n
  cases n with
  | zero => exact (unitEnd_ne (by omega)).symm
  | succ m =>
    show unitEnd k m = unitEnd (k + 1) (m + 1)
    by_cases h : m = k
    · subst h; rw [unitEnd_self, unitEnd_self]
    · rw [unitEnd_ne h, unitEnd_ne (by omega)]

/-- `Statement:` `boundaryDouble^[k] (unitEnd 0) = unitEnd k`. -/
theorem iterate_boundaryDouble_unitEnd_zero (k : ℕ) :
    boundaryDouble^[k] (unitEnd 0) = unitEnd k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, boundaryDouble_unitEnd]

-- Statement: control, the constant map `_ ↦ botEnd` never carries `unitEnd 0` to `unitEnd 1`.
example (k : ℕ) : (fun _ : End => botEnd)^[k + 1] (unitEnd 0) ≠ unitEnd 1 := by
  rw [Function.iterate_succ_apply']
  exact (unitEnd_ne_bot 1).symm

/-! ### § III. The covers of ⊥ of `End` are exactly the unit vectors. -/

theorem bot_endZlt_unitEnd (k : ℕ) : endZlt botEnd (unitEnd k) :=
  (endZlt_iff _ _).2 ⟨(endZle_iff _ _).2 fun _ => Nat.zero_le _,
    fun h => unitEnd_ne_bot k ((endZle_bot_iff _).1 h)⟩

/-- `Statement:` `unitEnd k` covers ⊥ of `End` in ZP-A's order. -/
theorem unitEnd_covers (k : ℕ) : endZcov botEnd (unitEnd k) := by
  refine ⟨bot_endZlt_unitEnd k, fun c h1 h2 => ?_⟩
  have hc : ∀ n, n ≠ k → c n = 0 := fun n hn => by
    have := ((endZle_iff _ _).1 ((endZlt_iff _ _).1 h2).1) n
    rw [unitEnd_ne hn] at this
    exact Fin.ext (Nat.le_zero.1 this)
  rcases fin2_eq_zero_or_one (c k) with h | h
  · apply ((endZlt_iff _ _).1 h1).2
    rw [endZle_bot_iff]
    funext n
    by_cases hn : n = k
    · subst hn; exact h
    · exact hc n hn
  · apply ((endZlt_iff _ _).1 h2).2
    rw [endZle_iff]
    intro n
    by_cases hn : n = k
    · subst hn; rw [h, unitEnd_self]
    · rw [unitEnd_ne hn]; exact Nat.zero_le _

/-- `Statement:` a cover of ⊥ of `End` with a `1` at `k` is `unitEnd k`. -/
theorem cover_eq_unitEnd (x : End) (hx : endZcov botEnd x) (k : ℕ) (hk : x k = 1) :
    x = unitEnd k := by
  funext n
  by_cases hn : n = k
  · subst hn; rw [hk, unitEnd_self]
  · rw [unitEnd_ne hn]
    rcases fin2_eq_zero_or_one (x n) with h | h
    · exact h
    · exfalso
      apply hx.2 (bot_endZlt_unitEnd n)
      refine (endZlt_iff _ _).2 ⟨(endZle_iff _ _).2 fun m => ?_, fun hle => ?_⟩
      · by_cases hm : m = n
        · subst hm; rw [h, unitEnd_self]
        · rw [unitEnd_ne hm]; exact Nat.zero_le _
      · have := (endZle_iff _ _).1 hle k
        rw [hk, unitEnd_ne (Ne.symm hn)] at this
        exact absurd this (by decide)

/-- `Statement:` the covers of ⊥ of `End` are exactly the `unitEnd k`. -/
theorem covers_bot_iff (x : End) : endZcov botEnd x ↔ ∃ k, x = unitEnd k := by
  constructor
  · intro hx
    have hex : ∃ k, x k = 1 := Classical.byContradiction fun hno => by
      apply ((endZlt_iff _ _).1 hx.1).2
      rw [endZle_bot_iff]
      funext n
      rcases fin2_eq_zero_or_one (x n) with h | h
      · exact h
      · exact absurd ⟨n, h⟩ hno
    obtain ⟨k, hk⟩ := hex
    exact ⟨k, cover_eq_unitEnd x hx k hk⟩
  · rintro ⟨k, rfl⟩; exact unitEnd_covers k

/-- `Statement:` ⊥ of `End` has a first step. -/
theorem end_botHasFirstStep : BotHasFirstStep End := ⟨unitEnd 0, unitEnd_covers 0⟩

/-- `Statement:` ⊥ of `End` has infinitely many covers. -/
theorem end_covers_infinite : {x : End | endZcov botEnd x}.Infinite :=
  Set.infinite_of_injective_forall_mem unitEnd_injective unitEnd_covers

/-! ### § IV. Each cover sits on the rim of its cell; depth is `endVal`. -/

/-- `Statement:` `unitEnd k ∈ boundaryCell k`. -/
theorem unitEnd_mem_cell (k : ℕ) : unitEnd k ∈ boundaryCell k := fun _ hi => unitEnd_ne (by omega)

/-- `Statement:` `unitEnd k ∉ boundaryCell (k + 1)`. -/
theorem unitEnd_not_mem_cell_succ (k : ℕ) : unitEnd k ∉ boundaryCell (k + 1) := fun h => by
  have := h k (Nat.lt_succ_self k)
  rw [unitEnd_self] at this
  exact absurd this (by decide)

/-- `Statement:` the cells nest. -/
theorem boundaryCell_succ_subset (k : ℕ) : boundaryCell (k + 1) ⊆ boundaryCell k :=
  fun _ hx i hi => hx i (by omega)

/-- `Statement:` `x ∈ boundaryCell k ↔ k ≤ endVal x`. -/
theorem mem_boundaryCell_iff (k : ℕ) (x : End) : x ∈ boundaryCell k ↔ (k : ℕ∞) ≤ endVal x := by
  constructor
  · intro h
    apply le_sInf
    rintro _ ⟨n, hn, rfl⟩
    exact Nat.cast_le.2 (Nat.le_of_not_lt fun hlt => hn (h n hlt))
  · intro h i hi
    by_cases hxi : x i = 0
    · exact hxi
    · exfalso
      have := Nat.cast_le.1 (le_trans h (sInf_le ⟨i, hxi, rfl⟩))
      omega

/-- `Statement:` the first nonzero digit's index is `endVal`. -/
theorem endVal_eq_of_first (x : End) (m : ℕ) (hm : x m ≠ 0) (hlt : ∀ i < m, x i = 0) :
    endVal x = m :=
  le_antisymm (sInf_le ⟨m, hm, rfl⟩) ((mem_boundaryCell_iff m x).1 hlt)

/-- `Statement:` `endVal (unitEnd k) = k`. -/
theorem endVal_unitEnd (k : ℕ) : endVal (unitEnd k) = k := endVal_indicator k

/-- `Statement:` an end other than `botEnd` has a first nonzero digit. -/
theorem exists_first_nonzero (x : End) (hx : x ≠ botEnd) :
    ∃ m, x m ≠ 0 ∧ ∀ i < m, x i = 0 := by
  have hex : ∃ n, x n ≠ 0 := Classical.byContradiction fun h =>
    hx (funext fun n => Decidable.byContradiction fun hn => h ⟨n, hn⟩)
  exact ⟨Nat.find hex, Nat.find_spec hex, fun i hi =>
    Decidable.byContradiction fun h => Nat.find_min hex hi h⟩

/-- `Statement:` `endVal (boundaryDouble x) = endVal x + 1`. -/
theorem endVal_boundaryDouble (x : End) : endVal (boundaryDouble x) = endVal x + 1 := by
  by_cases hx : x = botEnd
  · subst hx; rw [boundaryDouble_botEnd, botEnd_val_top, top_add]
  · obtain ⟨m, hm, hlt⟩ := exists_first_nonzero x hx
    rw [endVal_eq_of_first x m hm hlt, endVal_eq_of_first (boundaryDouble x) (m + 1) hm,
      Nat.cast_succ]
    intro i hi
    cases i with
    | zero => rfl
    | succ j => exact hlt j (by omega)

/-- `Statement:` `⨆ n : ℕ, (n : ℕ∞) = ⊤`. -/
theorem iSup_natCast_eq_top_enat : ⨆ n : ℕ, (n : ℕ∞) = ⊤ := by
  rw [iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  exact ⟨b + 1, by exact_mod_cast Nat.lt_succ_self b⟩

/-- The `InfinitudeFloor End`: floor `botEnd`, members the covers `unitEnd k`, complexity `endVal`. -/
@[reducible] noncomputable def cellsFloor : InfinitudeFloor End where
  floor := botEnd
  cx := endVal
  member := unitEnd
  cx_member_strictMono := fun a b h => by
    simp only [endVal_unitEnd]; exact_mod_cast h
  cx_floor_eq_iSup := by rw [botEnd_val_top, iSup_congr endVal_unitEnd, iSup_natCast_eq_top_enat]

/-- `Statement:` `cx (unitEnd k) = k`, `boundaryDouble^[k] (unitEnd 0) = unitEnd k`, `cx floor = ⊤`. -/
theorem cellsFloor_cx_unitEnd (k : ℕ) :
    cellsFloor.cx (unitEnd k) = k ∧ boundaryDouble^[k] (unitEnd 0) = unitEnd k ∧
      cellsFloor.cx cellsFloor.floor = ⊤ :=
  ⟨endVal_unitEnd k, iterate_boundaryDouble_unitEnd_zero k,
    infinitude_forces_infinite_complexity (I := cellsFloor) End⟩

/-- `Statement:` `unitEnd k → botEnd` in the product topology. -/
theorem unitEnd_tendsto_bot : Tendsto unitEnd atTop (𝓝 botEnd) := by
  rw [tendsto_pi_nhds]
  intro n
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop n] with k hk
  exact (unitEnd_ne (by omega)).symm

/-- The `InfinitudeFloorInversion End` extending `cellsFloor` (members tend to the floor). -/
@[reducible] noncomputable def cellsFloorInversion : InfinitudeFloorInversion End :=
  { cellsFloor with member_tendsto_floor := unitEnd_tendsto_bot }

/-! ### § V. The numbering is forced by the `+1` law. -/

theorem enat_eq_top_of_add_one_eq (a : ℕ∞) (h : a + 1 = a) : a = ⊤ := by
  induction a using ENat.recTopCoe with
  | top => rfl
  | coe n =>
    exfalso
    have : n + 1 = n := by exact_mod_cast h
    omega

/-- `Statement:` the `+1` law gives `d (boundaryDouble^[k] y) = d y + k`. -/
theorem depth_iterate (d : End → ℕ∞) (hstep : ∀ x, d (boundaryDouble x) = d x + 1) (k : ℕ)
    (y : End) : d (boundaryDouble^[k] y) = d y + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', hstep, ih, Nat.cast_succ, add_assoc]

/-- `Statement:` the `+1` law and `d (unitEnd 0) = 0` force `d botEnd = ⊤` and `d (unitEnd k) = k`. -/
theorem depth_forced_on_covers (d : End → ℕ∞) (hstep : ∀ x, d (boundaryDouble x) = d x + 1)
    (h0 : d (unitEnd 0) = 0) : d botEnd = ⊤ ∧ ∀ k, d (unitEnd k) = k := by
  refine ⟨enat_eq_top_of_add_one_eq _ ?_, fun k => ?_⟩
  · rw [← hstep, boundaryDouble_botEnd]
  · rw [← iterate_boundaryDouble_unitEnd_zero, depth_iterate d hstep, h0, zero_add]

/-- `Statement:` the `+1` law and `d = 0` on the rim `x 0 ≠ 0` force `d = endVal`. -/
theorem depth_forced_everywhere (d : End → ℕ∞) (hstep : ∀ x, d (boundaryDouble x) = d x + 1)
    (hroot : ∀ x, x 0 ≠ 0 → d x = 0) : ∀ x, d x = endVal x := by
  intro x
  by_cases hx : x = botEnd
  · subst hx
    rw [botEnd_val_top]
    exact enat_eq_top_of_add_one_eq _ (by rw [← hstep, boundaryDouble_botEnd])
  · obtain ⟨m, hm, hlt⟩ := exists_first_nonzero x hx
    have hrange : x ∈ Set.range (boundaryDouble^[m]) := by
      rw [range_iterate_boundaryDouble]; exact hlt
    obtain ⟨y, rfl⟩ := hrange
    have hy0 : y 0 ≠ 0 := by
      have := iterate_boundaryDouble m y m
      rw [ite_eq_right (Nat.lt_irrefl m), Nat.sub_self] at this
      rw [← this]; exact hm
    rw [depth_iterate d hstep, hroot y hy0, zero_add, endVal_eq_of_first _ m hm hlt]

-- Statement: control, `hroot` carries `depth_forced_everywhere`: `endVal` plus one on ends with two
-- nonzero digits obeys the `+1` law and vanishes at `unitEnd 0`, and differs from `endVal` at `1 1 0 …`.
open Classical in
example : ∃ d : End → ℕ∞, (∀ x, d (boundaryDouble x) = d x + 1) ∧ d (unitEnd 0) = 0 ∧
    d (fun n => if n ≤ 1 then 1 else 0) ≠ endVal (fun n => if n ≤ 1 then 1 else 0) := by
  let two : End → Prop := fun x => ∃ i j, i < j ∧ x i ≠ 0 ∧ x j ≠ 0
  have htwo : ∀ x, two (boundaryDouble x) ↔ two x := fun x => by
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      cases i with
      | zero => exact absurd rfl hi
      | succ i =>
        cases j with
        | zero => omega
        | succ j => exact ⟨i, j, by omega, hi, hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i + 1, j + 1, by omega, hi, hj⟩
  have hnot : ¬ two (unitEnd 0) := by
    rintro ⟨i, j, hij, hi, hj⟩
    by_cases h1 : i = 0
    · exact hj (unitEnd_ne (by omega))
    · exact hi (unitEnd_ne h1)
  refine ⟨fun x => endVal x + if two x then 1 else 0, fun x => ?_, ?_, ?_⟩
  · simp only [endVal_boundaryDouble, propext (htwo x)]; rw [add_right_comm]
  · simp only [ite_eq_right hnot, endVal_unitEnd]; rfl
  · have hv : endVal (fun n => if n ≤ 1 then (1 : Fin 2) else 0) = 0 :=
      endVal_eq_of_first _ 0 (by decide) (fun i hi => absurd hi (by omega))
    have ht : two (fun n => if n ≤ 1 then (1 : Fin 2) else 0) := ⟨0, 1, by omega, by decide, by decide⟩
    simp only [ite_eq_left ht, hv]
    decide

/-- `Statement:` no `ℕ`-valued depth obeys the `+1` law at every end. -/
theorem no_nat_depth (d : End → ℕ) (hstep : ∀ x, d (boundaryDouble x) = d x + 1) : False := by
  have := hstep botEnd
  rw [boundaryDouble_botEnd] at this
  omega

/-- `Statement:` the `+1` law along the orbit of `unitEnd 0` and `d (unitEnd 0) = 0` force
`d (unitEnd k) = k`, `ℕ`-valued. -/
theorem nat_depth_forced_on_orbit (d : End → ℕ)
    (hstep : ∀ k, d (boundaryDouble (unitEnd k)) = d (unitEnd k) + 1) (h0 : d (unitEnd 0) = 0) :
    ∀ k, d (unitEnd k) = k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih => rw [← boundaryDouble_unitEnd, hstep, ih]

/-- `Statement:` a coordinate map `π` with `x ↦ x ∘ π` commuting with `boundaryDouble` is `id`. -/
theorem coord_commute_boundaryDouble_eq_id (π : ℕ → ℕ)
    (h : ∀ x : End, boundaryDouble (x ∘ π) = boundaryDouble x ∘ π) : π = id := by
  have h0 : π 0 = 0 := by
    have := congrFun (h (fun _ => 1)) 0
    change (0 : Fin 2) = boundaryDouble (fun _ => 1) (π 0) at this
    rcases hπ : π 0 with _ | m
    · rfl
    · rw [hπ] at this
      change (0 : Fin 2) = 1 at this
      exact absurd this (by decide)
  have hs : ∀ k, π (k + 1) = π k + 1 := by
    intro k
    have := congrFun (h (unitEnd (π k))) (k + 1)
    change unitEnd (π k) (π k) = boundaryDouble (unitEnd (π k)) (π (k + 1)) at this
    rw [unitEnd_self] at this
    rcases hπ : π (k + 1) with _ | m
    · rw [hπ] at this
      change (1 : Fin 2) = 0 at this
      exact absurd this (by decide)
    · rw [hπ] at this
      change (1 : Fin 2) = unitEnd (π k) m at this
      by_cases hm : m = π k
      · rw [hm]
      · rw [unitEnd_ne hm] at this; exact absurd this (by decide)
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs, ih]; rfl

/-! ### § VI. Concurrency: one map, both readings at once. -/

/-- `Statement:` `boundaryDouble`'s fixed points are `{botEnd}`; its iterate ranges nest and meet in
`{botEnd}`; the covers of ⊥ of `End` are its orbit from `unitEnd 0`; the `k`-th lies in cell `k` only. -/
theorem cells_concurrent :
    (∀ x, boundaryDouble x = x ↔ x = botEnd) ∧
    (∀ k, Set.range (boundaryDouble^[k + 1]) ⊆ Set.range (boundaryDouble^[k])) ∧
    (⋂ k, Set.range (boundaryDouble^[k])) = {botEnd} ∧
    (∀ x, endZcov botEnd x ↔ ∃ k, x = boundaryDouble^[k] (unitEnd 0)) ∧
    (∀ k, boundaryDouble^[k] (unitEnd 0) ∈ Set.range (boundaryDouble^[k]) ∧
      boundaryDouble^[k] (unitEnd 0) ∉ Set.range (boundaryDouble^[k + 1])) := by
  refine ⟨fun x => ⟨boundaryDouble_unique_fp x, fun h => h ▸ boundaryDouble_botEnd⟩,
    fun k => ?_, iInter_range_iterate_boundaryDouble, fun x => ?_, fun k => ⟨⟨unitEnd 0, rfl⟩, ?_⟩⟩
  · rw [range_iterate_boundaryDouble, range_iterate_boundaryDouble]; exact boundaryCell_succ_subset k
  · rw [covers_bot_iff]; simp only [iterate_boundaryDouble_unitEnd_zero]
  · rw [range_iterate_boundaryDouble, iterate_boundaryDouble_unitEnd_zero]
    exact unitEnd_not_mem_cell_succ k

/-! ### § VII. Both sides at once force branching. -/

/-- `Statement:` in a linear `ZPSemilattice` where ⊥ is the glb of non-⊥ members, ⊥ has no cover. -/
theorem linear_glb_no_botFirstStep {L : Type*} [ZPSemilattice L]
    (hlin : ∀ x y : L, ZPSemilattice.le x y ∨ ZPSemilattice.le y x)
    (member : ℕ → L) (hmem : ∀ n, member n ≠ ZPSemilattice.bot)
    (hglb : ∀ c : L, (∀ n, ZPSemilattice.le c (member n)) → c = ZPSemilattice.bot) :
    ¬ BotHasFirstStep L := by
  rintro ⟨a, ha⟩
  let _ := zpSemilatticeSup L
  have hlow : ∀ n, ZPSemilattice.le a (member n) := by
    intro n
    rcases hlin a (member n) with h | h
    · exact h
    · rcases eq_or_ne (member n) a with e | e
      · rw [e]; exact ZPSemilattice.join_idem a
      · have hlt : member n < a := lt_of_le_of_ne (show member n ≤ a from h) e
        have hb : (ZPSemilattice.bot : L) < member n :=
          lt_of_le_of_ne (show ZPSemilattice.bot ≤ member n from ZPSemilattice.bot_le (member n))
            (hmem n).symm
        exact absurd hlt (ha.2 hb)
  exact ha.1.ne' (hglb a hlow)

/-- `Statement:` ⊥ the glb of non-⊥ members, and `BotHasFirstStep L`, imply ZP-A's order is not linear. -/
theorem branching_forced {L : Type*} [ZPSemilattice L]
    (member : ℕ → L) (hmem : ∀ n, member n ≠ ZPSemilattice.bot)
    (hglb : ∀ c : L, (∀ n, ZPSemilattice.le c (member n)) → c = ZPSemilattice.bot)
    (hstep : BotHasFirstStep L) :
    ¬ ∀ x y : L, ZPSemilattice.le x y ∨ ZPSemilattice.le y x :=
  fun hlin => linear_glb_no_botFirstStep hlin member hmem hglb hstep

/-- `Statement:` ⊥ of `End` is the glb of the `unitEnd n`. -/
theorem end_glb_unitEnd : ∀ c : End, (∀ n, ZPSemilattice.le c (unitEnd n)) → c = botEnd := by
  intro c hc
  funext k
  have := (endZle_iff _ _).1 (hc (k + 1)) k
  rw [unitEnd_ne (by omega)] at this
  exact Fin.ext (Nat.le_zero.1 this)

/-- `Statement:` ZP-A's order on `End` is not linear (from `branching_forced`). -/
theorem end_not_linear : ¬ ∀ x y : End, ZPSemilattice.le x y ∨ ZPSemilattice.le y x :=
  branching_forced unitEnd unitEnd_ne_bot end_glb_unitEnd end_botHasFirstStep

/-- `Statement:` distinct unit vectors are incomparable. -/
theorem unitEnd_incomparable {j k : ℕ} (hjk : j ≠ k) : ¬ endZle (unitEnd j) (unitEnd k) := fun h => by
  have := (endZle_iff _ _).1 h j
  rw [unitEnd_self, unitEnd_ne hjk] at this
  exact absurd this (by decide)

/-- `Statement:` every cell `boundaryCell k` holds infinitely many covers of ⊥ of `End`. -/
theorem cell_covers_infinite (k : ℕ) :
    {x : End | endZcov botEnd x ∧ x ∈ boundaryCell k}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun j => unitEnd (k + j))
    (fun a b h => by have := unitEnd_injective h; omega)
    (fun _ => ⟨unitEnd_covers _, fun _ hi => unitEnd_ne (by omega)⟩)

/-- `Statement:` every neighbourhood of `botEnd` holds infinitely many covers of ⊥ of `End`. -/
theorem nhds_botEnd_covers_infinite (U : Set End) (hU : U ∈ 𝓝 botEnd) :
    {x : End | endZcov botEnd x ∧ x ∈ U}.Infinite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (unitEnd_tendsto_bot hU)
  exact Set.infinite_of_injective_forall_mem (f := fun j => unitEnd (N + j))
    (fun a b h => by have := unitEnd_injective h; omega)
    (fun _ => ⟨unitEnd_covers _, hN _ (by omega)⟩)

section Controls
attribute [local instance] nnrealMaxZPS

-- Statement: control, drop the step side: `NNReal` under `max` is linear, ⊥ is the glb of the
-- non-⊥ `1/(n+1)`, and ⊥ has no first step.
example :
    (∀ x y : NNReal, ZPSemilattice.le x y ∨ ZPSemilattice.le y x) ∧
    (∀ n : ℕ, (1 / ((n : NNReal) + 1)) ≠ ZPSemilattice.bot) ∧
    (∀ c : NNReal, (∀ n : ℕ, ZPSemilattice.le c (1 / ((n : NNReal) + 1))) → c = ZPSemilattice.bot) ∧
    ¬ BotHasFirstStep NNReal := by
  refine ⟨fun x y => ?_, fun n => ?_, fun c hc => ?_, nnreal_not_botHasFirstStep⟩
  · show max x y = y ∨ max y x = x
    rcases le_total x y with h | h
    · exact Or.inl (max_eq_right h)
    · exact Or.inr (max_eq_right h)
  · show 1 / ((n : NNReal) + 1) ≠ 0
    positivity
  · show c = 0
    by_contra hc0
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (pos_iff_ne_zero.2 hc0)
    have : max c (1 / ((n : NNReal) + 1)) = 1 / ((n : NNReal) + 1) := hc n
    rw [max_eq_right_iff] at this
    exact absurd hn (not_lt.2 this)

end Controls

section Controls
attribute [local instance] boolOrZPS

-- Statement: control, drop the depth side: `Bool` under `or` is linear with a first step, and no
-- sequence of non-⊥ members has glb ⊥.
example :
    (∀ x y : Bool, ZPSemilattice.le x y ∨ ZPSemilattice.le y x) ∧ BotHasFirstStep Bool ∧
    ¬ ∃ member : ℕ → Bool, (∀ n, member n ≠ ZPSemilattice.bot) ∧
      (∀ c : Bool, (∀ n, ZPSemilattice.le c (member n)) → c = ZPSemilattice.bot) := by
  refine ⟨fun x y => ?_, bool_botHasFirstStep, ?_⟩
  · show (x || y) = y ∨ (y || x) = x
    cases x <;> cases y <;> decide
  · rintro ⟨m, hm, hglb⟩
    have ht : ∀ n, m n = true := fun n => by
      have := hm n
      cases h : m n
      · exact absurd h this
      · rfl
    have := hglb true fun n => by
      show (true || m n) = m n
      rw [ht n]; rfl
    exact absurd this (by decide)

end Controls

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms endZle
#print axioms endZlt
#print axioms endZcov
#print axioms iSup_natCast_eq_top_enat
#print axioms endZle_iff
#print axioms endZle_iff_le
#print axioms endZlt_iff
#print axioms endZlt_iff_lt
#print axioms endZcov_iff_covBy
#print axioms fin2_eq_zero_or_one
#print axioms endZle_bot_iff
#print axioms unitEnd
#print axioms unitEnd_self
#print axioms unitEnd_ne
#print axioms unitEnd_ne_bot
#print axioms unitEnd_injective
#print axioms boundaryDouble_unitEnd
#print axioms iterate_boundaryDouble_unitEnd_zero
#print axioms bot_endZlt_unitEnd
#print axioms unitEnd_covers
#print axioms cover_eq_unitEnd
#print axioms covers_bot_iff
#print axioms end_botHasFirstStep
#print axioms end_covers_infinite
#print axioms unitEnd_mem_cell
#print axioms unitEnd_not_mem_cell_succ
#print axioms boundaryCell_succ_subset
#print axioms mem_boundaryCell_iff
#print axioms endVal_eq_of_first
#print axioms endVal_unitEnd
#print axioms exists_first_nonzero
#print axioms endVal_boundaryDouble
#print axioms cellsFloor
#print axioms cellsFloor_cx_unitEnd
#print axioms unitEnd_tendsto_bot
#print axioms cellsFloorInversion
#print axioms enat_eq_top_of_add_one_eq
#print axioms depth_iterate
#print axioms depth_forced_on_covers
#print axioms depth_forced_everywhere
#print axioms no_nat_depth
#print axioms nat_depth_forced_on_orbit
#print axioms coord_commute_boundaryDouble_eq_id
#print axioms cells_concurrent
#print axioms linear_glb_no_botFirstStep
#print axioms branching_forced
#print axioms end_glb_unitEnd
#print axioms end_not_linear
#print axioms unitEnd_incomparable
#print axioms cell_covers_infinite
#print axioms nhds_botEnd_covers_infinite
end PurityCheck
