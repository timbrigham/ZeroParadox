-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): Morton (Z-order) interleaving of `End` with its square, and the seed count of a push as an order-conjugacy invariant. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.CellsJoint
import ZeroParadox.Valuation.DepthIsWait
import Mathlib.Data.Stream.Init
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Order.Cover
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.Nat.Pairing
import Mathlib.Basic.NNReal.Defs
import Mathlib.Tactic

/-!
# Directions inside ⊥ of `End`: interleaving, and seeds as the invariant

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
Morton (Z-order) interleaving is an order isomorphism `End ≃o End × End` (`interleaveEnd`), so the
number of directions is not an order invariant; a push's seeds (`coverSeeds`) are, along conjugating
order isomorphisms (`coverSeeds_transport`), and digit width is (`no_orderIso_end_fin3`).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

/-! ### § I. Digit tapes `κ → Fin (q+2)` and their covers of the all-zeros tape. -/

section Tape
variable {κ : Type*} {q : ℕ}

/-- The all-zeros tape. On `End` it is `botEnd`. -/
def zeroTape : κ → Fin (q + 2) := fun _ => 0

/-- `Statement:` the all-zeros tape is least. -/
theorem zeroTape_le (x : κ → Fin (q + 2)) : (zeroTape : κ → Fin (q + 2)) ≤ x := fun n => by
  show (0 : Fin (q + 2)).val ≤ (x n).val
  rw [Fin.val_zero]; exact Nat.zero_le _

/-- The tape with digit `a` at `k` and `0` elsewhere. -/
def digitInd [DecidableEq κ] (k : κ) (a : Fin (q + 2)) : κ → Fin (q + 2) :=
  fun n => if n = k then a else 0

theorem finPlusTwo_one_ne_zero : (1 : Fin (q + 2)) ≠ 0 := fun h => by
  have := congrArg Fin.val h
  rw [Fin.val_one, Fin.val_zero] at this
  omega

/-- `Statement:` in `Fin (q+2)` the only cover of `0` is `1`. -/
theorem finPlusTwo_zero_covBy_iff (c : Fin (q + 2)) : (0 : Fin (q + 2)) ⋖ c ↔ c = 1 := by
  constructor
  · intro h
    have h0 : 0 < c.val := by
      have := h.1; rw [Fin.lt_def, Fin.val_zero] at this; exact this
    apply Fin.ext
    rw [Fin.val_one]
    rcases Nat.lt_or_ge c.val 2 with hlt | hge
    · omega
    · exfalso
      apply h.2 (c := 1)
      · rw [Fin.lt_def, Fin.val_zero, Fin.val_one]; omega
      · rw [Fin.lt_def, Fin.val_one]; omega
  · rintro rfl
    refine ⟨?_, fun d h1 h2 => ?_⟩
    · rw [Fin.lt_def, Fin.val_zero, Fin.val_one]; omega
    · rw [Fin.lt_def, Fin.val_zero] at h1
      rw [Fin.lt_def, Fin.val_one] at h2
      omega

/-- `Statement:` the covers of the all-zeros tape are exactly the `digitInd k 1`. -/
theorem covers_zeroTape_iff [DecidableEq κ] (x : κ → Fin (q + 2)) :
    (zeroTape : κ → Fin (q + 2)) ⋖ x ↔ ∃ k, x = digitInd k 1 := by
  rw [Pi.covBy_iff]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨i, funext fun n => ?_⟩
    unfold digitInd
    by_cases hn : n = i
    · subst hn; rw [ite_eq_left rfl]; exact (finPlusTwo_zero_covBy_iff _).1 hi
    · rw [ite_eq_right hn]; exact (hj n hn).symm
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_, fun j hj => ?_⟩
    · show (0 : Fin (q + 2)) ⋖ digitInd k 1 k
      unfold digitInd; rw [ite_eq_left rfl]; exact (finPlusTwo_zero_covBy_iff _).2 rfl
    · show (0 : Fin (q + 2)) = digitInd k 1 j
      unfold digitInd; rw [ite_eq_right hj]

end Tape

theorem zeroTape_eq_botEnd : (zeroTape : End) = botEnd := rfl
theorem digitInd_one_eq_unitEnd (k : ℕ) : (digitInd k 1 : End) = unitEnd k := rfl

/-- `Statement:` the covers of ⊥ of `End` in Mathlib's `Pi` order are exactly the `unitEnd k`. -/
theorem covBy_botEnd_iff (x : End) : botEnd ⋖ x ↔ ∃ k, x = unitEnd k :=
  covers_zeroTape_iff x

/-- `Statement:` `unitEnd i ∈ boundaryCell m ↔ m ≤ i`. -/
theorem unitEnd_mem_cell_iff (i m : ℕ) : unitEnd i ∈ boundaryCell m ↔ m ≤ i := by
  constructor
  · intro h
    by_contra hc
    have := h i (by omega)
    rw [unitEnd_self] at this
    exact absurd this (by decide)
  · intro h j hj; exact unitEnd_ne (by omega)

/-! ### § II. Order isomorphisms of digit tapes, and Morton interleaving. -/

/-- Re-indexing coordinates along an equivalence is an order isomorphism. -/
def reindexOrderIso (D : Type*) [Preorder D] {ι κ : Type*} (σ : ι ≃ κ) : (κ → D) ≃o (ι → D) where
  toFun x := x ∘ σ
  invFun y := y ∘ σ.symm
  left_inv x := funext fun n => congrArg x (σ.apply_symm_apply n)
  right_inv y := funext fun n => congrArg y (σ.symm_apply_apply n)
  map_rel_iff' := by
    intro a b
    constructor
    · intro h n
      have := h (σ.symm n)
      change a (σ (σ.symm n)) ≤ b (σ (σ.symm n)) at this
      rw [σ.apply_symm_apply] at this
      exact this
    · intro h n; exact h (σ n)

/-- Splitting sum-indexed coordinates is an order isomorphism onto the product. -/
def sumSplitOrderIso (D : Type*) [Preorder D] (α β : Type*) :
    (α ⊕ β → D) ≃o (α → D) × (β → D) where
  toFun x := (x ∘ Sum.inl, x ∘ Sum.inr)
  invFun p := Sum.elim p.1 p.2
  left_inv x := funext fun s => by cases s <;> rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · rintro ⟨h1, h2⟩ s
      cases s with
      | inl i => exact h1 i
      | inr i => exact h2 i
    · intro h; exact ⟨fun i => h (Sum.inl i), fun i => h (Sum.inr i)⟩

/-- Currying product-indexed coordinates is an order isomorphism. -/
def curryOrderIso (D : Type*) [Preorder D] (ι κ : Type*) : (ι × κ → D) ≃o (ι → κ → D) where
  toFun x i n := x (i, n)
  invFun y p := y p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · intro h p; exact h p.1 p.2
    · intro h i n; exact h (i, n)

/-- Morton (Z-order) interleaving: even digits to the first factor, odd digits to the second; the
    halves are Mathlib's `Stream'.even`, `Stream'.odd` (`Mathlib/Data/Stream/Defs.lean`). -/
def interleaveEnd : End ≃o End × End :=
  (reindexOrderIso (Fin 2) Equiv.natSumNatEquivNat).trans (sumSplitOrderIso (Fin 2) ℕ ℕ)

/-- `Statement:` `interleaveEnd x = (x ∘ (2 * ·), x ∘ (2 * · + 1))`. -/
theorem interleaveEnd_apply (x : End) :
    interleaveEnd x = (fun m => x (2 * m), fun m => x (2 * m + 1)) := by
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · exact congrArg x (congrFun Equiv.natSumNatEquivNat_apply (Sum.inl m))
  · exact congrArg x (congrFun Equiv.natSumNatEquivNat_apply (Sum.inr m))

-- Statement: the first component of `interleaveEnd` is Mathlib's `Stream'.even`.
example (x : End) : (interleaveEnd x).1 = Stream'.even x := by
  rw [interleaveEnd_apply]; funext m; exact (Stream'.get_even m x).symm

-- Statement: the second component of `interleaveEnd` is Mathlib's `Stream'.odd`.
example (x : End) : (interleaveEnd x).2 = Stream'.odd x := by
  rw [interleaveEnd_apply]; funext m; exact (Stream'.get_odd m x).symm

/-- `Statement:` `interleaveEnd botEnd = (botEnd, botEnd)`. -/
theorem interleaveEnd_bot : interleaveEnd botEnd = (botEnd, botEnd) := by
  rw [interleaveEnd_apply]; rfl

/-- `Statement:` the covers of `(botEnd, botEnd)` are exactly `(unitEnd k, botEnd)`, `(botEnd, unitEnd k)`. -/
theorem prod_covers_bot_iff (p : End × End) :
    ((botEnd, botEnd) : End × End) ⋖ p ↔
      (∃ k, p = (unitEnd k, botEnd)) ∨ (∃ k, p = (botEnd, unitEnd k)) := by
  obtain ⟨a, b⟩ := p
  rw [Prod.mk_covBy_mk_iff]
  constructor
  · rintro (⟨ha, rfl⟩ | ⟨hb, rfl⟩)
    · obtain ⟨k, rfl⟩ := (covBy_botEnd_iff a).1 ha; exact Or.inl ⟨k, rfl⟩
    · obtain ⟨k, rfl⟩ := (covBy_botEnd_iff b).1 hb; exact Or.inr ⟨k, rfl⟩
  · rintro (⟨k, h⟩ | ⟨k, h⟩) <;> cases h
    · exact Or.inl ⟨(covBy_botEnd_iff _).2 ⟨k, rfl⟩, rfl⟩
    · exact Or.inr ⟨(covBy_botEnd_iff _).2 ⟨k, rfl⟩, rfl⟩

/-- `Statement:` `interleaveEnd (unitEnd (2 * k)) = (unitEnd k, botEnd)`. -/
theorem interleaveEnd_unitEnd_even (k : ℕ) : interleaveEnd (unitEnd (2 * k)) = (unitEnd k, botEnd) := by
  rw [interleaveEnd_apply]
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · show (if 2 * m = 2 * k then (1 : Fin 2) else 0) = if m = k then 1 else 0
    by_cases h : m = k
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]
  · show (if 2 * m + 1 = 2 * k then (1 : Fin 2) else 0) = 0
    rw [ite_eq_right (by omega)]

/-- `Statement:` `interleaveEnd (unitEnd (2 * k + 1)) = (botEnd, unitEnd k)`. -/
theorem interleaveEnd_unitEnd_odd (k : ℕ) :
    interleaveEnd (unitEnd (2 * k + 1)) = (botEnd, unitEnd k) := by
  rw [interleaveEnd_apply]
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · show (if 2 * m = 2 * k + 1 then (1 : Fin 2) else 0) = 0
    rw [ite_eq_right (by omega)]
  · show (if 2 * m + 1 = 2 * k + 1 then (1 : Fin 2) else 0) = if m = k then 1 else 0
    by_cases h : m = k
    · rw [ite_eq_left (by omega), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right h]

/-- `Fin m × ℕ ≃ ℕ`, `(i, j) ↦ m * j + i`, for `0 < m`. -/
def finMulNatEquiv (m : ℕ) (hm : 0 < m) : Fin m × ℕ ≃ ℕ where
  toFun p := m * p.2 + p.1
  invFun k := (⟨k % m, Nat.mod_lt _ hm⟩, k / m)
  left_inv p := by
    obtain ⟨⟨i, hi⟩, j⟩ := p
    refine Prod.ext (Fin.ext ?_) ?_
    · show (m * j + i) % m = i
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
    · show (m * j + i) / m = j
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hi, Nat.zero_add]
  right_inv k := Nat.div_add_mod k m

/-- `m` directions: digit `m * j + i` is digit `j` of direction `i`. -/
def dirsOrderIso (m : ℕ) (hm : 0 < m) : End ≃o (Fin m → End) :=
  (reindexOrderIso (Fin 2) (finMulNatEquiv m hm)).trans (curryOrderIso (Fin 2) (Fin m) ℕ)

/-- ℕ-many directions via `Nat.pairEquiv`: through `tapeIso`, Mathlib's `cantorSpaceHomeomorphNatToCantorSpace`
    (`Mathlib/Topology/Instances/CantorSet.lean`) plus the order, which that map does not carry. -/
def natDirsOrderIso : End ≃o (ℕ → End) :=
  (reindexOrderIso (Fin 2) Nat.pairEquiv).trans (curryOrderIso (Fin 2) ℕ ℕ)

/-- `Statement:` `dirsOrderIso m hm x i j = x (m * j + i)`. -/
theorem dirsOrderIso_apply (m : ℕ) (hm : 0 < m) (x : End) (i : Fin m) (j : ℕ) :
    dirsOrderIso m hm x i j = x (m * j + i) := rfl

/-- `Statement:` `natDirsOrderIso x i j = x (Nat.pair i j)`. -/
theorem natDirsOrderIso_apply (x : End) (i j : ℕ) : natDirsOrderIso x i j = x (Nat.pair i j) := rfl

-- Statement: through `tapeIso`, `natDirsOrderIso` is Mathlib's `cantorSpaceHomeomorphNatToCantorSpace`.
example (x : End) (i j : ℕ) :
    cantorSpaceHomeomorphNatToCantorSpace (tapeIso x) i j = tapeIso (natDirsOrderIso x i) j := by
  have h : ((i, j) : ℕ × ℕ) = Nat.pairEquiv.symm (Nat.pair i j) := (Nat.unpair_pair i j).symm
  show (Homeomorph.piCongrLeft (Y := fun _ => Bool) Nat.pairEquiv.symm) (tapeIso x) (i, j) = _
  rw [h, Homeomorph.piCongrLeft_apply_apply]
  rfl

/-! ### § III. Digit width IS an order invariant. -/

/-- `Statement:` an order isomorphism sends a least element to a least element. -/
theorem orderIso_map_least {α β : Type*} [PartialOrder α] [PartialOrder β] (φ : α ≃o β) (b : α)
    (hb : ∀ x, b ≤ x) (b' : β) (hb' : ∀ y, b' ≤ y) : φ b = b' :=
  le_antisymm (by rw [← φ.apply_symm_apply b']; exact φ.monotone (hb _)) (hb' _)

/-- Above any cover `c` of `b`, every strictly larger point lies above another cover of `b`. -/
def CoversSeparate (α : Type*) [PartialOrder α] (b : α) : Prop :=
  ∀ c x : α, b ⋖ c → c < x → ∃ c', b ⋖ c' ∧ c' ≤ x ∧ c' ≠ c

/-- `Statement:` `CoversSeparate` transports along order isomorphisms. -/
theorem coversSeparate_transport {α β : Type*} [PartialOrder α] [PartialOrder β] (φ : α ≃o β) (b : α)
    (h : CoversSeparate α b) : CoversSeparate β (φ b) := by
  intro c x hc hx
  have hc0 : b ⋖ φ.symm c := (apply_covBy_apply_iff φ).1 (by rw [φ.apply_symm_apply]; exact hc)
  have hx0 : φ.symm c < φ.symm x := φ.symm.lt_iff_lt.2 hx
  obtain ⟨c', h1, h2, h3⟩ := h _ _ hc0 hx0
  refine ⟨φ c', (apply_covBy_apply_iff φ).2 h1, ?_, fun h => h3 ?_⟩
  · rw [← φ.apply_symm_apply x]; exact φ.monotone h2
  · rw [← h, φ.symm_apply_apply]

/-- `Statement:` `CoversSeparate End botEnd`. -/
theorem end_coversSeparate : CoversSeparate End botEnd := by
  intro c x hc hx
  obtain ⟨k, rfl⟩ := (covBy_botEnd_iff c).1 hc
  have hex : ∃ n, n ≠ k ∧ x n ≠ 0 := Classical.byContradiction fun hno => by
    apply lt_irrefl x
    have : x = unitEnd k := funext fun n => by
      by_cases hn : n = k
      · subst hn
        rw [unitEnd_self]
        have := hx.le n
        rw [unitEnd_self] at this
        apply Fin.ext
        have h1 := (x n).isLt
        show (x n).val = 1
        have h2 : 1 ≤ (x n).val := this
        omega
      · rw [unitEnd_ne hn]
        exact Decidable.byContradiction fun hx0 => hno ⟨n, hn, hx0⟩
    calc x = unitEnd k := this
      _ < x := hx
  obtain ⟨n, hn, hxn⟩ := hex
  have hx1 : x n = 1 := (fin2_eq_zero_or_one (x n)).resolve_left hxn
  refine ⟨unitEnd n, (covBy_botEnd_iff _).2 ⟨n, rfl⟩, fun m => ?_, fun h => hn ?_⟩
  · by_cases hm : m = n
    · subst hm; rw [unitEnd_self, hx1]
    · rw [unitEnd_ne hm]; exact Nat.zero_le _
  · exact unitEnd_injective h

/-- `Statement:` on `ℕ → Fin 3`, `digitInd k 2` is not a cover of the all-zeros tape. -/
theorem fin3_digitInd_two_not_cover (k : ℕ) :
    (zeroTape : ℕ → Fin 3) < digitInd k 1 ∧ (digitInd k 1 : ℕ → Fin 3) < digitInd k 2 ∧
      ¬ (zeroTape : ℕ → Fin 3) ⋖ digitInd k 2 := by
  have h12 : (digitInd k 1 : ℕ → Fin 3) < digitInd k 2 := by
    refine lt_of_le_not_ge (fun n => ?_) (fun h => ?_)
    · unfold digitInd
      by_cases hn : n = k
      · rw [ite_eq_left hn, ite_eq_left hn]; exact (by decide : (1 : Fin 3) ≤ 2)
      · rw [ite_eq_right hn, ite_eq_right hn]
    · have := h k; unfold digitInd at this; rw [ite_eq_left rfl, ite_eq_left rfl] at this
      exact (by decide : ¬ (2 : Fin 3) ≤ 1) this
  have h01 : (zeroTape : ℕ → Fin 3) < digitInd k 1 :=
    ((covers_zeroTape_iff (q := 1) _).2 ⟨k, rfl⟩).1
  exact ⟨h01, h12, fun h => h.2 h01 h12⟩

/-- `Statement:` `¬ CoversSeparate (ℕ → Fin 3) zeroTape`. -/
theorem fin3_not_coversSeparate : ¬ CoversSeparate (ℕ → Fin 3) zeroTape := by
  intro h
  obtain ⟨_, h12, _⟩ := fin3_digitInd_two_not_cover 0
  obtain ⟨c', hc', hle, hne⟩ :=
    h (digitInd 0 1) (digitInd 0 2) ((covers_zeroTape_iff _).2 ⟨0, rfl⟩) h12
  obtain ⟨n, rfl⟩ := (covers_zeroTape_iff c').1 hc'
  apply hne
  by_cases hn : n = 0
  · rw [hn]
  · exfalso
    have := hle n
    unfold digitInd at this
    rw [ite_eq_left rfl, ite_eq_right hn] at this
    exact (by decide : ¬ (1 : Fin 3) ≤ 0) this

/-- `Statement:` no order isomorphism `End ≃o (ℕ → Fin 3)`. -/
theorem no_orderIso_end_fin3 : IsEmpty (End ≃o (ℕ → Fin 3)) := by
  constructor
  intro φ
  have hb : φ botEnd = zeroTape :=
    orderIso_map_least φ botEnd (zeroTape_le (q := 0)) zeroTape (zeroTape_le (q := 1))
  have := coversSeparate_transport φ botEnd end_coversSeparate
  rw [hb] at this
  exact fin3_not_coversSeparate this

/-! ### § IV. The push, transported, and its seeds. -/

/-- The componentwise push on `End × End`. -/
def pushPair (p : End × End) : End × End := (boundaryDouble p.1, boundaryDouble p.2)

/-- `Statement:` interleaving turns `boundaryDouble^[2]` into `pushPair`. -/
theorem interleaveEnd_conj_sq (x : End) :
    interleaveEnd (boundaryDouble^[2] x) = pushPair (interleaveEnd x) := by
  rw [interleaveEnd_apply, interleaveEnd_apply]
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · show (boundaryDouble^[2] x) (2 * m) = boundaryDouble (fun m => x (2 * m)) m
    rw [iterate_boundaryDouble]
    cases m with
    | zero => rw [ite_eq_left (by omega)]; rfl
    | succ m' =>
      rw [ite_eq_right (by omega)]
      show x (2 * (m' + 1) - 2) = x (2 * m')
      exact congrArg x (by omega)
  · show (boundaryDouble^[2] x) (2 * m + 1) = boundaryDouble (fun m => x (2 * m + 1)) m
    rw [iterate_boundaryDouble]
    cases m with
    | zero => rw [ite_eq_left (by omega)]; rfl
    | succ m' =>
      rw [ite_eq_right (by omega)]
      show x (2 * (m' + 1) + 1 - 2) = x (2 * m' + 1)
      exact congrArg x (by omega)

/-- `Statement:` interleaving turns one `boundaryDouble` into `(a, b) ↦ (boundaryDouble b, a)`. -/
theorem interleaveEnd_conj_boundaryDouble (x : End) :
    interleaveEnd (boundaryDouble x) =
      (boundaryDouble (interleaveEnd x).2, (interleaveEnd x).1) := by
  rw [interleaveEnd_apply, interleaveEnd_apply]
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · show boundaryDouble x (2 * m) = boundaryDouble (fun m => x (2 * m + 1)) m
    cases m with
    | zero => rfl
    | succ m' =>
      rw [show 2 * (m' + 1) = (2 * m' + 1) + 1 by omega]
      rfl
  · rfl

/-- The seeds of a push `P` at `b`: covers of `b` not in the image of `P`. -/
def coverSeeds {α : Type*} [Preorder α] (P : α → α) (b : α) : Set α := {c | b ⋖ c ∧ c ∉ Set.range P}

/-- `Statement:` an order isomorphism conjugating `P` to `Q` carries the seeds of `P` onto those of `Q`. -/
theorem coverSeeds_transport {α β : Type*} [Preorder α] [Preorder β] (φ : α ≃o β) (P : α → α)
    (Q : β → β) (b : α) (hconj : ∀ x, φ (P x) = Q (φ x)) : φ '' coverSeeds P b = coverSeeds Q (φ b) := by
  ext y
  constructor
  · rintro ⟨c, ⟨hc, hnr⟩, rfl⟩
    refine ⟨(apply_covBy_apply_iff φ).2 hc, fun ⟨w, hw⟩ => hnr ⟨φ.symm w, φ.injective ?_⟩⟩
    rw [hconj, φ.apply_symm_apply, hw]
  · rintro ⟨hy, hnr⟩
    refine ⟨φ.symm y, ⟨(apply_covBy_apply_iff φ).1 (by rw [φ.apply_symm_apply]; exact hy),
      fun ⟨w, hw⟩ => hnr ⟨φ w, ?_⟩⟩, φ.apply_symm_apply y⟩
    rw [← hconj, hw, φ.apply_symm_apply]

/-- `Statement:` the seeds of `boundaryDouble^[m]` at `botEnd` are `unitEnd 0, …, unitEnd (m-1)`. -/
theorem coverSeeds_iterate_boundaryDouble (m : ℕ) :
    coverSeeds (boundaryDouble^[m]) botEnd = {x | ∃ i < m, x = unitEnd i} := by
  ext x
  simp only [coverSeeds, Set.mem_ofPred_eq]
  rw [covBy_botEnd_iff, range_iterate_boundaryDouble]
  constructor
  · rintro ⟨⟨k, rfl⟩, hk⟩
    rw [unitEnd_mem_cell_iff] at hk
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, rfl⟩, ?_⟩
    rw [unitEnd_mem_cell_iff]; omega

/-- `Statement:` `boundaryDouble` has the one seed `unitEnd 0` at `botEnd`. -/
theorem coverSeeds_boundaryDouble : coverSeeds boundaryDouble botEnd = {unitEnd 0} := by
  have := coverSeeds_iterate_boundaryDouble 1
  rw [Function.iterate_one] at this
  rw [this]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩; rw [show i = 0 by omega]
  · rintro rfl; exact ⟨0, by omega, rfl⟩

/-- `Statement:` `pushPair` has the two seeds `(unitEnd 0, botEnd)`, `(botEnd, unitEnd 0)`. -/
theorem coverSeeds_pushPair :
    coverSeeds pushPair (botEnd, botEnd) = {(unitEnd 0, botEnd), (botEnd, unitEnd 0)} := by
  rw [← interleaveEnd_bot, ← coverSeeds_transport interleaveEnd _ _ botEnd interleaveEnd_conj_sq,
    coverSeeds_iterate_boundaryDouble]
  ext p
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · left; exact interleaveEnd_unitEnd_even 0
    · right; exact interleaveEnd_unitEnd_odd 0
  · rintro (rfl | rfl)
    · exact ⟨unitEnd 0, ⟨0, by omega, rfl⟩, interleaveEnd_unitEnd_even 0⟩
    · exact ⟨unitEnd 1, ⟨1, by omega, rfl⟩, interleaveEnd_unitEnd_odd 0⟩

/-- `Statement:` no order automorphism of `End` conjugates `boundaryDouble` to `boundaryDouble^[2]`. -/
theorem boundaryDouble_not_conj_sq :
    ¬ ∃ φ : End ≃o End, ∀ x, φ (boundaryDouble x) = boundaryDouble^[2] (φ x) := by
  rintro ⟨φ, hφ⟩
  have hb : φ botEnd = botEnd :=
    orderIso_map_least φ botEnd (zeroTape_le (q := 0)) botEnd (zeroTape_le (q := 0))
  have key := coverSeeds_transport φ _ _ botEnd hφ
  rw [hb, coverSeeds_boundaryDouble, coverSeeds_iterate_boundaryDouble, Set.image_singleton] at key
  have h0 : unitEnd 0 ∈ ({φ (unitEnd 0)} : Set End) := by rw [key]; exact ⟨0, by omega, rfl⟩
  have h1 : unitEnd 1 ∈ ({φ (unitEnd 0)} : Set End) := by rw [key]; exact ⟨1, by omega, rfl⟩
  rw [Set.mem_singleton_iff] at h0 h1
  exact absurd (unitEnd_injective (h0.trans h1.symm)) (by decide)

-- Statement: control, ⊥ of `Unit` has no cover, so every push on `Unit` has no seed.
example (P : Unit → Unit) : coverSeeds P () = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hc => lt_irrefl () hc.1.1

-- Statement: control, `0` in `NNReal` has no cover (dense order), so every push has no seed.
example (P : NNReal → NNReal) : coverSeeds P 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hc => not_covBy_of_denselyOrdered hc.1

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms zeroTape
#print axioms zeroTape_le
#print axioms digitInd
#print axioms finPlusTwo_one_ne_zero
#print axioms finPlusTwo_zero_covBy_iff
#print axioms covers_zeroTape_iff
#print axioms zeroTape_eq_botEnd
#print axioms digitInd_one_eq_unitEnd
#print axioms covBy_botEnd_iff
#print axioms unitEnd_mem_cell_iff
#print axioms reindexOrderIso
#print axioms sumSplitOrderIso
#print axioms curryOrderIso
#print axioms interleaveEnd
#print axioms interleaveEnd_apply
#print axioms interleaveEnd_bot
#print axioms prod_covers_bot_iff
#print axioms interleaveEnd_unitEnd_even
#print axioms interleaveEnd_unitEnd_odd
#print axioms finMulNatEquiv
#print axioms dirsOrderIso
#print axioms natDirsOrderIso
#print axioms dirsOrderIso_apply
#print axioms natDirsOrderIso_apply
#print axioms orderIso_map_least
#print axioms CoversSeparate
#print axioms coversSeparate_transport
#print axioms end_coversSeparate
#print axioms fin3_digitInd_two_not_cover
#print axioms fin3_not_coversSeparate
#print axioms no_orderIso_end_fin3
#print axioms pushPair
#print axioms interleaveEnd_conj_sq
#print axioms interleaveEnd_conj_boundaryDouble
#print axioms coverSeeds
#print axioms coverSeeds_transport
#print axioms coverSeeds_iterate_boundaryDouble
#print axioms coverSeeds_boundaryDouble
#print axioms coverSeeds_pushPair
#print axioms boundaryDouble_not_conj_sq
end PurityCheck
