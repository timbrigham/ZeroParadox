-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): `boundaryDouble` attracts every end to ⊥ of `End` forward, and only ⊥ of `End` has an infinite backward orbit. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.LocalTowers
import Mathlib.Topology.Constructions
import Mathlib.Tactic

/-!
# The one-way flow: forward attraction and backward exit, two charts of `boundaryDouble`

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

"Stable in one direction is exactly why the flow moves the way it does"

---

## Formal Overview (AI-assisted)
Forward chart: every orbit tends to `botEnd` (`tendsto_iterate_boundaryDouble`). Backward chart: each
`x ≠ botEnd` leaves `boundaryCell 1` after `endVal x` undo-steps (`backward_orbit_exits`), and only
`botEnd` has an infinite backward orbit (`infinite_backward_orbit_iff`). Both: `one_way_flow`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology

/-! ### § I. Forward chart: attraction to `botEnd`. -/

/-- `Statement:` `boundaryDouble^[n] x ∈ boundaryCell n`. -/
theorem iterate_boundaryDouble_mem_cell (x : End) (n : ℕ) : boundaryDouble^[n] x ∈ boundaryCell n := by
  rw [← range_iterate_boundaryDouble]; exact ⟨x, rfl⟩

/-- `Statement:` every `boundaryDouble`-orbit tends to `botEnd` in the product topology. -/
theorem tendsto_iterate_boundaryDouble (x : End) :
    Tendsto (fun n => boundaryDouble^[n] x) atTop (𝓝 botEnd) := by
  rw [tendsto_pi_nhds]
  intro m
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop m] with n hn
  exact (iterate_boundaryDouble_mem_cell x n m hn).symm

/-- `Statement:` `boundaryDouble` is one-to-one. -/
theorem boundaryDouble_injective : Function.Injective boundaryDouble :=
  fun _ _ h => funext fun n => congrFun h (n + 1)

/-- `Statement:` from `x ≠ botEnd` the orbit never reaches `botEnd`. -/
theorem iterate_boundaryDouble_ne_bot (x : End) (hx : x ≠ botEnd) (n : ℕ) :
    boundaryDouble^[n] x ≠ botEnd := by
  intro h
  apply hx
  apply boundaryDouble_injective.iterate n
  rw [h, Function.iterate_fixed boundaryDouble_botEnd]

/-- `Statement:` `(localPush v)^[n+1] x = prependEnd v (boundaryDouble^[n+1] (shiftEnd |v| x))`. -/
theorem localPush_iterate_succ (v : List (Fin 2)) (x : End) (n : ℕ) :
    (localPush v)^[n + 1] x = prependEnd v (boundaryDouble^[n + 1] (shiftEnd v.length x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, localPush_prependEnd,
      ← Function.iterate_succ_apply' boundaryDouble]

/-- `Statement:` every `localPush v`-orbit tends to `localBotEnd v` in the product topology. -/
theorem tendsto_iterate_localPush (v : List (Fin 2)) (x : End) :
    Tendsto (fun n => (localPush v)^[n] x) atTop (𝓝 (localBotEnd v)) := by
  rw [tendsto_pi_nhds]
  intro m
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop m] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [localPush_iterate_succ]
  show prependEnd v botEnd m = prependEnd v _ m
  unfold prependEnd
  split_ifs with h
  · rfl
  · exact (iterate_boundaryDouble_mem_cell _ (k + 1) (m - v.length) (by omega)).symm

/-! ### § II. Backward chart: the undo step is partial. -/

/-- `Statement:` `Set.range boundaryDouble = boundaryCell 1`. -/
theorem range_boundaryDouble : Set.range boundaryDouble = boundaryCell 1 := by
  rw [← range_iterate_boundaryDouble 1, Function.iterate_one]

/-- `Statement:` `shiftEnd 1` is a left inverse of `boundaryDouble`. -/
theorem shiftEnd_one_leftInverse : Function.LeftInverse (shiftEnd 1) boundaryDouble := fun x => by
  funext n
  show boundaryDouble x (1 + n) = x n
  rw [Nat.add_comm]; rfl

/-- `Statement:` an end whose first digit is nonzero has no `boundaryDouble`-preimage. -/
theorem not_mem_range_boundaryDouble (x : End) (h : x 0 ≠ 0) : x ∉ Set.range boundaryDouble := by
  rintro ⟨y, rfl⟩; exact h rfl

/-- `Statement:` on `boundaryCell 1`, `boundaryDouble (shiftEnd 1 x) = x`. -/
theorem boundaryDouble_shiftEnd_one (x : End) (hx : x ∈ boundaryCell 1) :
    boundaryDouble (shiftEnd 1 x) = x := by
  rw [← range_boundaryDouble] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [shiftEnd_one_leftInverse y]

/-- `Statement:` on `boundaryCell 1`, `endVal x = endVal (shiftEnd 1 x) + 1`. -/
theorem endVal_shiftEnd_one (x : End) (hx : x ∈ boundaryCell 1) :
    endVal x = endVal (shiftEnd 1 x) + 1 := by
  conv_lhs => rw [← boundaryDouble_shiftEnd_one x hx]
  exact endVal_boundaryDouble _

/-- `Statement:` on `boundaryCell 1` off `botEnd`, `endVal x = m + 1` and `endVal (shiftEnd 1 x) = m`. -/
theorem endVal_shiftEnd_one_of_ne (x : End) (hx : x ∈ boundaryCell 1) (hne : x ≠ botEnd) :
    ∃ m : ℕ, endVal x = (m + 1 : ℕ) ∧ endVal (shiftEnd 1 x) = m := by
  obtain ⟨k, hk, hlt⟩ := exists_first_nonzero x hne
  have hk0 : k ≠ 0 := fun h => hk (h ▸ hx 0 (by omega))
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨m, endVal_eq_of_first x _ hk hlt, endVal_eq_of_first _ m ?_ ?_⟩
  · show x (1 + m) ≠ 0
    rwa [Nat.add_comm]
  · intro i hi
    show x (1 + i) = 0
    rw [Nat.add_comm]; exact hlt _ (by omega)

/-! ### § III. Backward chart: every end other than `botEnd` exits. -/

/-- `Statement:` `(shiftEnd 1)^[k] x = shiftEnd k x`. -/
theorem iterate_shiftEnd_one (k : ℕ) (x : End) : (shiftEnd 1)^[k] x = shiftEnd k x := by
  induction k generalizing x with
  | zero => exact (shiftEnd_zero x).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    funext n
    show x (1 + (k + n)) = x (k + 1 + n)
    congr 1; omega

/-- `Statement:` for `x ≠ botEnd` and `m = endVal x`: undo-steps `0, …, m-1` stay in `boundaryCell 1`,
the `m`-th has no preimage, and `m` pushes return it to `x`. -/
theorem backward_orbit_exits (x : End) (hx : x ≠ botEnd) :
    ∃ m : ℕ, endVal x = m ∧ (∀ k < m, (shiftEnd 1)^[k] x ∈ boundaryCell 1) ∧
      (shiftEnd 1)^[m] x ∉ Set.range boundaryDouble ∧
      boundaryDouble^[m] ((shiftEnd 1)^[m] x) = x := by
  obtain ⟨m, hm, hlt⟩ := exists_first_nonzero x hx
  refine ⟨m, endVal_eq_of_first x m hm hlt, fun k hk => ?_, ?_, ?_⟩
  · rw [iterate_shiftEnd_one]
    intro i hi
    show x (k + i) = 0
    exact hlt _ (by omega)
  · rw [iterate_shiftEnd_one]
    apply not_mem_range_boundaryDouble
    show x (m + 0) ≠ 0
    exact hm
  · rw [iterate_shiftEnd_one]
    funext n
    rw [iterate_boundaryDouble]
    split_ifs with h
    · exact (hlt n h).symm
    · show x (m + (n - m)) = x n
      congr 1; omega

/-- `Statement:` `x` has an infinite backward `boundaryDouble`-orbit iff `x = botEnd`. -/
theorem infinite_backward_orbit_iff (x : End) :
    (∃ y : ℕ → End, y 0 = x ∧ ∀ k, boundaryDouble (y (k + 1)) = y k) ↔ x = botEnd := by
  constructor
  · rintro ⟨y, rfl, hy⟩
    have h : ∀ k, boundaryDouble^[k] (y k) = y 0 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply, hy, ih]
    have hmem : y 0 ∈ ⋂ k, Set.range (boundaryDouble^[k]) := Set.mem_iInter.2 fun k => ⟨y k, h k⟩
    rw [iInter_range_iterate_boundaryDouble] at hmem
    exact hmem
  · rintro rfl
    exact ⟨fun _ => botEnd, rfl, fun _ => boundaryDouble_botEnd⟩

/-- `Statement:` both charts of `boundaryDouble`: every forward orbit tends to `botEnd`, and only
`botEnd` has an infinite backward orbit. -/
theorem one_way_flow :
    (∀ x : End, Tendsto (fun n => boundaryDouble^[n] x) atTop (𝓝 botEnd)) ∧
    (∀ x : End, (∃ y : ℕ → End, y 0 = x ∧ ∀ k, boundaryDouble (y (k + 1)) = y k) ↔ x = botEnd) :=
  ⟨tendsto_iterate_boundaryDouble, infinite_backward_orbit_iff⟩

/-! ### § IV. Controls. -/

-- Statement: control, `id` attracts nothing to `botEnd` (the orbit of `unitEnd 0` stays put) and
-- fixes every end, so the unique fixed point fails for it.
example : ¬ Tendsto (fun n => (id : End → End)^[n] (unitEnd 0)) atTop (𝓝 botEnd) ∧
    id (unitEnd 0) = unitEnd 0 ∧ unitEnd 0 ≠ botEnd := by
  refine ⟨fun h => unitEnd_ne_bot 0 ?_, rfl, unitEnd_ne_bot 0⟩
  simp only [Function.iterate_id, id] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

-- Statement: control, the shift inserting `1` attracts no end to `botEnd`: digit `0` is `1` from
-- step 1 on.
example (x : End) :
    ¬ Tendsto (fun n => (fun y : End => fun k => if k = 0 then (1 : Fin 2) else y (k - 1))^[n] x)
      atTop (𝓝 botEnd) := by
  intro h
  have h0 := (tendsto_pi_nhds.1 h) 0
  have h1 : Tendsto (fun n =>
      ((fun y : End => fun k => if k = 0 then (1 : Fin 2) else y (k - 1))^[n] x) 0) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Function.iterate_succ_apply']
    rfl
  exact absurd (tendsto_nhds_unique h1 h0) (by decide)

-- Statement: control, the constant map `_ ↦ botEnd` has `botEnd` as its only fixed point, yet it is
-- not one-to-one and carries `unitEnd 0` onto `botEnd` in one step.
example : (∀ x : End, (fun _ : End => botEnd) x = x ↔ x = botEnd) ∧
    ¬ Function.Injective (fun _ : End => botEnd) ∧ (fun _ : End => botEnd)^[1] (unitEnd 0) = botEnd :=
  ⟨fun _ => ⟨Eq.symm, Eq.symm⟩, fun h => unitEnd_ne_bot 0 (h rfl), rfl⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms iterate_boundaryDouble_mem_cell
#print axioms tendsto_iterate_boundaryDouble
#print axioms boundaryDouble_injective
#print axioms iterate_boundaryDouble_ne_bot
#print axioms localPush_iterate_succ
#print axioms tendsto_iterate_localPush
#print axioms range_boundaryDouble
#print axioms shiftEnd_one_leftInverse
#print axioms not_mem_range_boundaryDouble
#print axioms boundaryDouble_shiftEnd_one
#print axioms endVal_shiftEnd_one
#print axioms endVal_shiftEnd_one_of_ne
#print axioms iterate_shiftEnd_one
#print axioms backward_orbit_exits
#print axioms infinite_backward_orbit_iff
#print axioms one_way_flow
end PurityCheck
