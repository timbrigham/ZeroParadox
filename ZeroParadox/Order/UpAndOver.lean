import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.SnapSuccession
import ZeroParadox.Reals.OrderedField
import Mathlib.Order.Closure
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The up-and-over shape: a closure operator with a corner and a cover at every non-maximal landing

## Engineer's Take

I think it is the same shape, what our "up and over" transform applied. The up and over always felt L
or J shaped. The cell width vs layer height. I think we're seeing it. The fundamental premise being
that that exact shape continues to recur, defining the shape when we can do it. Extrapolated away from
types, into the motions that it takes to get there.

---

## Formal Overview (AI-assisted)
`UpAndOver α` bundles a Mathlib `ClosureOperator` (UP) with a corner (a landing whose cover UP moves)
and a cover at each non-maximal landing (OVER). § III gives controls each field refuses, and `Fin 3`
as a member; § IV is the ordinal instance. Prior art and fences: `ZeroParadox/Order/UpAndOver.md`.
-/

namespace ZeroParadox

open Order Ordinal

universe u

/-! ### § I. The shape -/

/-- `Statement:` a closure operator `up` on a partial order with a closed point `y` and a cover `b`
    of `y` that `up` moves, and a cover in the carrier order at every non-maximal closed point.
    `Reading:` UP is `up`; OVER is the step from a landing to a cover of it; `corner` is a place
    where OVER then UP moves. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `ClosureOperator` admits the identity and the
-- constant-top closure and says nothing about covers; this bundles it with a corner (a closed
-- point whose cover the closure moves) and a carrier-order cover at each non-maximal closed point.
-- The corner's cover excludes every densely ordered carrier, ℝ with ceiling included.
structure UpAndOver (α : Type u) [PartialOrder α] where
  /-- The UP leg: a closure operator; its closed points are the landings. -/
  up : ClosureOperator α
  /-- The corner: a landing `y` with a cover `b` that `up` moves, so OVER then UP moves. -/
  corner : ∃ y b, up.IsClosed y ∧ y ⋖ b ∧ up b ≠ b
  /-- The OVER leg: every landing with something above it has a cover in the carrier order. -/
  cover : ∀ y, up.IsClosed y → ¬ IsMax y → ∃ b, y ⋖ b

namespace UpAndOver

variable {α : Type u} [PartialOrder α] (U : UpAndOver α)

/-! ### § II. Derived facts -/

/-- `Statement:` some point is moved by `up` (the corner's cover). -/
theorem moves : ∃ x, U.up x ≠ x := by
  obtain ⟨-, b, -, -, hb⟩ := U.corner
  exact ⟨b, hb⟩

/-- `Statement:` some landing is not maximal (the corner's landing). -/
theorem open_landing : ∃ y, U.up.IsClosed y ∧ ¬ IsMax y := by
  obtain ⟨y, b, hy, hb, -⟩ := U.corner
  exact ⟨y, hy, not_isMax_of_lt hb.lt⟩

-- `Statement:` the `cover` field is the corpus predicate `HasFirstStep`
-- (`ZeroParadox/Reals/OrderedField.lean`), asked landing by landing.
example {y : α} (hy : U.up.IsClosed y) (hmax : ¬ IsMax y) : HasFirstStep y := U.cover y hy hmax

-- `Statement:` COINCIDENCE — one cover `y ⋖ b` in two charts: an atom of the up-set `Set.Ici y`
-- read from below, a coatom of the down-set `Set.Iic b` read from above.
example {y b : α} (h : y ≤ b) :
    (y ⋖ b ↔ IsAtom (⟨b, h⟩ : Set.Ici y)) ∧ (y ⋖ b ↔ IsCoatom (⟨y, h⟩ : Set.Iic b)) :=
  ⟨covBy_iff_atom_Ici h, covBy_iff_coatom_Iic h⟩

/-- `Statement:` the corner law: `up` is constant on the interval `[x, up x]`. -/
theorem up_eq_of_mem_Icc {x s : α} (h1 : x ≤ s) (h2 : s ≤ U.up x) : U.up s = U.up x :=
  le_antisymm (U.up.le_closure_iff.mp h2) (U.up.monotone h1)

/-- `Statement:` `up` is not injective. -/
theorem up_not_injective : ¬ Function.Injective U.up := fun hinj => by
  obtain ⟨x, hx⟩ := U.moves
  exact hx (hinj (U.up.idempotent x))

/-- `Statement:` from a non-maximal landing `y`, a cover `b` of `y` followed by `up` lands on a
    landing strictly above `y`. -/
theorem exists_next_landing {y : α} (hy : U.up.IsClosed y) (hmax : ¬ IsMax y) :
    ∃ b, y ⋖ b ∧ U.up.IsClosed (U.up b) ∧ y < U.up b := by
  obtain ⟨b, hb⟩ := U.cover y hy hmax
  exact ⟨b, hb, U.up.isClosed_closure b, hb.1.trans_le (U.up.le_closure b)⟩

/-- `Statement:` on a linear order, the landing reached from a cover `b` of `y` is below every
    landing strictly above `y`. -/
theorem up_le_of_covBy {β : Type u} [LinearOrder β] (V : UpAndOver β) {y b z : β}
    (hb : y ⋖ b) (hz : V.up.IsClosed z) (hyz : y < z) : V.up b ≤ z :=
  V.up.closure_min (not_lt.1 fun hzb => hb.2 hyz hzb) hz

-- `Statement:` two distinct landings follow from `corner` alone: its landing `y` and the landing
-- `up b`, since `y < b ≤ up b`.
example : ∃ y z, U.up.IsClosed y ∧ U.up.IsClosed z ∧ y ≠ z := by
  obtain ⟨y, b, hy, hb, -⟩ := U.corner
  exact ⟨y, U.up b, hy, U.up.isClosed_closure b, (hb.lt.trans_le (U.up.le_closure b)).ne⟩

-- `Statement:` `corner` alone gives a three-point chain `y < b < up b`, so a finite member has at
-- least three points.
example : ∃ y b z : α, y < b ∧ b < z := by
  obtain ⟨y, b, -, hb, hne⟩ := U.corner
  exact ⟨y, b, U.up b, hb.lt, lt_of_le_of_ne (U.up.le_closure b) (Ne.symm hne)⟩
example [Fintype α] : 3 ≤ Fintype.card α := by
  obtain ⟨y, b, -, hb, hne⟩ := U.corner
  have h1 : y < b := hb.lt
  have h2 : b < U.up b := lt_of_le_of_ne (U.up.le_closure b) (Ne.symm hne)
  have h3 : y < U.up b := h1.trans h2
  have hinj : Function.Injective ![y, b, U.up b] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [h1.ne, h2.ne, h3.ne, h1.ne', h2.ne', h3.ne']
  simpa using Fintype.card_le_of_injective _ hinj

/-- `Statement:` a densely ordered carrier carries no `UpAndOver`: density refuses the cover in the
    corner (Mathlib `not_covBy`; the corpus form of "no cover anywhere" is
    `axb1_fails_everywhere_iff_dense`). Density is sufficient for exclusion, not necessary: `Bool`
    is not densely ordered and is refused too (§ III). -/
theorem isEmpty_of_denselyOrdered [DenselyOrdered α] : IsEmpty (UpAndOver α) :=
  ⟨fun U => by
    obtain ⟨y, b, -, hb, -⟩ := U.corner
    exact not_covBy hb⟩

end UpAndOver

/-! ### § III. NO-GO gauge — what fails to be an `UpAndOver`, and the smallest member. Each
control's `Statement:` names each field that refuses it. -/

-- `Statement:` the three-point chain `Fin 3` carries the shape: the closure sending `1` to `2` and
-- fixing every other point, with the landing `0`, its cover `1`, and `up` moving `1` to `2`. By the
-- three-point bound in § II, no carrier with fewer points is a member.
example : ∃ U : UpAndOver (Fin 3), (∀ x, U.up x = if x = 1 then 2 else x) ∧
    U.up.IsClosed 0 ∧ (0 : Fin 3) ⋖ 1 ∧ U.up 1 = 2 := by
  let f : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else x
  have hmono : ∀ a b : Fin 3, a ≤ b → f a ≤ f b := by decide
  have hinfl : ∀ a : Fin 3, a ≤ f a := by decide
  have hidem : ∀ a : Fin 3, f (f a) ≤ f a := by decide
  let c : ClosureOperator (Fin 3) := ClosureOperator.mk' f hmono hinfl hidem
  have h0 : c.IsClosed 0 := c.isClosed_iff.2 (show f 0 = 0 by decide)
  have hcov : (0 : Fin 3) ⋖ 1 := ⟨by decide, fun d h1 h2 => by revert d h1 h2; decide⟩
  have h1 : c 1 = 2 := show f 1 = 2 by decide
  refine ⟨⟨c, ⟨0, 1, h0, hcov, by rw [h1]; decide⟩, ?_⟩, fun _ => rfl, h0, hcov, h1⟩
  intro y hy hm
  fin_cases y
  · exact ⟨1, hcov⟩
  · exact absurd (show f 1 = 1 from c.isClosed_iff.1 hy) (by decide)
  · exact absurd (fun b _ => by revert b; decide) hm

-- `Statement:` `Bool` is not densely ordered and carries no `UpAndOver` (`corner` refuses it):
-- density is sufficient for exclusion (`UpAndOver.isEmpty_of_denselyOrdered`), not necessary.
example : ¬ DenselyOrdered Bool ∧ IsEmpty (UpAndOver Bool) := by
  refine ⟨fun h => ?_, ⟨fun U => ?_⟩⟩
  · obtain ⟨c, h1, h2⟩ := h.dense false true (by decide)
    cases c <;> simp_all
  · obtain ⟨y, b, -, hb, hne⟩ := U.corner
    have hbt : b = true := by
      cases b
      · exact absurd hb.lt (by cases y <;> decide)
      · rfl
    subst hbt
    exact hne U.up.isClosed_top.closure_eq

-- `Statement:` the ceiling map on ℝ is a closure operator that moves `1/2`, is not injective, and has
-- the two distinct closed points `0` and `1`, with `0` not maximal; ℝ has no cover anywhere, so
-- `cover` refuses it at `0` and `corner`, which asks for a cover, refuses it too.
example : ∃ c : ClosureOperator ℝ, (∀ x, c x = (⌈x⌉ : ℝ)) ∧ c (1 / 2) ≠ 1 / 2 ∧
    ¬ Function.Injective c ∧ c.IsClosed 0 ∧ c.IsClosed 1 ∧ (0 : ℝ) ≠ 1 ∧ ¬ IsMax (0 : ℝ) ∧
    (∀ a b : ℝ, ¬ a ⋖ b) := by
  let c : ClosureOperator ℝ := ClosureOperator.mk' (fun x => (⌈x⌉ : ℝ))
    (fun _ _ h => Int.cast_mono (Int.ceil_mono h)) (fun x => Int.le_ceil x) (fun x => by simp)
  refine ⟨c, fun _ => rfl, ?_, ?_, c.isClosed_iff.2 ?_, c.isClosed_iff.2 ?_, by norm_num,
    not_isMax 0, fun _ _ => not_covBy⟩
  · show ((⌈(1 / 2 : ℝ)⌉ : ℤ) : ℝ) ≠ 1 / 2
    norm_num [Int.ceil_eq_iff]
  · intro h
    have h12 : c (1 / 2) = c 1 := by
      show ((⌈(1 / 2 : ℝ)⌉ : ℤ) : ℝ) = ((⌈(1 : ℝ)⌉ : ℤ) : ℝ)
      norm_num [Int.ceil_eq_iff]
    have := h h12
    norm_num at this
  · show ((⌈(0 : ℝ)⌉ : ℤ) : ℝ) = 0
    simp
  · show ((⌈(1 : ℝ)⌉ : ℤ) : ℝ) = 1
    simp
example : IsEmpty (UpAndOver ℝ) := UpAndOver.isEmpty_of_denselyOrdered

-- `Statement:` the identity closure moves no cover, so `corner` refuses it: it is the `up` of no
-- `UpAndOver`.
example (α : Type u) [PartialOrder α] : ¬ ∃ U : UpAndOver α, U.up = ClosureOperator.id α := by
  rintro ⟨U, hU⟩
  obtain ⟨-, b, -, -, hb⟩ := U.corner
  exact hb (by rw [hU]; rfl)

-- `Statement:` `corner` refuses `Unit` (nothing moves) and `Empty` (`corner` is existential).
example : IsEmpty (UpAndOver Unit) :=
  ⟨fun U => by obtain ⟨-, b, -, -, hb⟩ := U.corner; exact hb (Subsingleton.elim _ _)⟩
example : IsEmpty (UpAndOver Empty) :=
  ⟨fun U => by obtain ⟨y, -⟩ := U.corner; exact y.elim⟩

-- `Statement:` a closure sending every point to `⊤` exists on `Bool` and moves `false`; any such
-- closure has `⊤` as its only closed point, which has no cover above it, so `corner` refuses it.
example : ∃ c : ClosureOperator Bool, (∀ x, c x = ⊤) ∧ c false ≠ false :=
  ⟨ClosureOperator.mk' (fun _ => ⊤) (fun _ _ _ => le_rfl) (fun _ => le_top) (fun _ => le_rfl),
    fun _ => rfl, fun h => Bool.noConfusion h⟩
example {α : Type u} [PartialOrder α] [OrderTop α] (c : ClosureOperator α) (hc : ∀ x, c x = ⊤) :
    ¬ ∃ y b, c.IsClosed y ∧ y ⋖ b ∧ c b ≠ b := by
  rintro ⟨y, b, hy, hb, -⟩
  have hy' : y = ⊤ := hy.closure_eq.symm.trans (hc y)
  exact not_top_lt (hy' ▸ hb.lt)

-- `Statement:` on two disjoint copies of `WithTop ℚ`, a densely ordered carrier with no cover
-- anywhere, sending each copy to its own `⊤` is a closure that moves a point and has two distinct
-- closed points, both maximal; `cover` asks nothing there, since no landing is non-maximal, and
-- `corner`, which asks for a cover, refuses it.
example : ∃ c : ClosureOperator (WithTop ℚ ⊕ WithTop ℚ),
    (∀ x, c x = Sum.elim (fun _ => Sum.inl ⊤) (fun _ => Sum.inr ⊤) x) ∧ (∃ x, c x ≠ x) ∧
    c.IsClosed (Sum.inl ⊤) ∧ c.IsClosed (Sum.inr ⊤) ∧
    (Sum.inl ⊤ : WithTop ℚ ⊕ WithTop ℚ) ≠ Sum.inr ⊤ ∧
    (∀ y, c.IsClosed y → IsMax y) ∧ (∀ a b : WithTop ℚ ⊕ WithTop ℚ, ¬ a ⋖ b) := by
  let f : WithTop ℚ ⊕ WithTop ℚ → WithTop ℚ ⊕ WithTop ℚ :=
    Sum.elim (fun _ => Sum.inl ⊤) (fun _ => Sum.inr ⊤)
  let c : ClosureOperator (WithTop ℚ ⊕ WithTop ℚ) := ClosureOperator.mk' f
    (fun _ _ h => by
      cases h with
      | inl _ => exact Sum.LiftRel.inl le_rfl
      | inr _ => exact Sum.LiftRel.inr le_rfl)
    (fun a => by
      cases a with
      | inl _ => exact Sum.LiftRel.inl le_top
      | inr _ => exact Sum.LiftRel.inr le_top)
    (fun a => by cases a <;> exact le_rfl)
  refine ⟨c, fun _ => rfl, ⟨Sum.inl ((0 : ℚ) : WithTop ℚ), fun h => ?_⟩, c.isClosed_iff.2 rfl,
    c.isClosed_iff.2 rfl, Sum.inl_ne_inr, fun y hy b hb => ?_, fun _ _ => not_covBy⟩
  · have : (Sum.inl ⊤ : WithTop ℚ ⊕ WithTop ℚ) = Sum.inl ((0 : ℚ) : WithTop ℚ) := h
    simp at this
  · have hy' : f y = y := c.isClosed_iff.1 hy
    cases y with
    | inl x =>
      cases b with
      | inl w =>
        obtain rfl : x = ⊤ := by simpa [f] using hy'.symm
        exact Sum.inl_le_inl_iff.2 le_top
      | inr w => exact absurd hb Sum.not_inl_le_inr
    | inr x =>
      cases b with
      | inl w => exact absurd hb Sum.not_inr_le_inl
      | inr w =>
        obtain rfl : x = ⊤ := by simpa [f] using hy'.symm
        exact Sum.inr_le_inr_iff.2 le_top
example : IsEmpty (UpAndOver (WithTop ℚ ⊕ WithTop ℚ)) := UpAndOver.isEmpty_of_denselyOrdered

-- `Statement:` on the linear carrier `ℕ ⊕ₗ WithTop ℚ` (ℕ below `WithTop ℚ`), the closure fixing ℕ
-- and sending every point of `WithTop ℚ` to its `⊤` moves a point, has a non-maximal landing, and
-- has a cover at every non-maximal landing, so it passes `cover`; no landing has a cover that the
-- closure moves, so `corner` refuses it.
example : ∃ c : ClosureOperator (ℕ ⊕ₗ WithTop ℚ),
    (∀ x, c x = Sum.elim (fun n => toLex (Sum.inl n)) (fun _ => toLex (Sum.inr ⊤)) (ofLex x)) ∧
    (∃ x, c x ≠ x) ∧
    (∃ y, c.IsClosed y ∧ ¬ IsMax y) ∧ (∀ y, c.IsClosed y → ¬ IsMax y → ∃ b, y ⋖ b) ∧
    ¬ ∃ y b, c.IsClosed y ∧ y ⋖ b ∧ c b ≠ b := by
  let g : ℕ ⊕ₗ WithTop ℚ → ℕ ⊕ₗ WithTop ℚ :=
    fun x => Sum.elim (fun n => toLex (Sum.inl n)) (fun _ => toLex (Sum.inr ⊤)) (ofLex x)
  have hmax : IsMax (toLex (Sum.inr ⊤) : ℕ ⊕ₗ WithTop ℚ) := fun b _ => by
    rcases b with n | q
    · exact Sum.Lex.inl_le_inr n ⊤
    · exact Sum.Lex.inr_le_inr_iff.2 le_top
  let c : ClosureOperator (ℕ ⊕ₗ WithTop ℚ) := ClosureOperator.mk' g
    (fun a b h => by
      rcases a with m | p <;> rcases b with n | q
      · exact h
      · exact Sum.Lex.inl_le_inr m ⊤
      · exact absurd h Sum.Lex.not_inr_le_inl
      · exact le_rfl)
    (fun a => by
      rcases a with n | q
      · exact le_rfl
      · exact Sum.Lex.inr_le_inr_iff.2 le_top)
    (fun a => by rcases a with n | q <;> exact le_rfl)
  have hcl : ∀ q, c.IsClosed (toLex (Sum.inr q)) → q = ⊤ := fun q h => by
    have h' : (toLex (Sum.inr ⊤) : ℕ ⊕ₗ WithTop ℚ) = toLex (Sum.inr q) := c.isClosed_iff.1 h
    exact (Sum.inr_injective (toLex.injective h')).symm
  refine ⟨c, fun _ => rfl, ⟨toLex (Sum.inr ((0 : ℚ) : WithTop ℚ)), fun h => ?_⟩,
    ⟨toLex (Sum.inl 0), c.isClosed_iff.2 rfl, fun h => ?_⟩, fun y hy hm => ?_, ?_⟩
  · have h' : (toLex (Sum.inr ⊤) : ℕ ⊕ₗ WithTop ℚ) = toLex (Sum.inr ((0 : ℚ) : WithTop ℚ)) := h
    have := Sum.inr_injective (toLex.injective h')
    simp at this
  · have := Sum.Lex.inl_le_inl_iff.1 (h (Sum.Lex.inl_le_inl_iff.2 (Nat.zero_le 1)))
    omega
  · rcases y with n | q
    · refine ⟨toLex (Sum.inl (n + 1)), Sum.Lex.inl_lt_inl_iff.2 (Nat.lt_succ_self n),
        fun d h1 h2 => ?_⟩
      rcases d with m | q
      · have := Sum.Lex.inl_lt_inl_iff.1 h1
        have := Sum.Lex.inl_lt_inl_iff.1 h2
        omega
      · exact Sum.Lex.not_inr_lt_inl h2
    · obtain rfl := hcl q hy
      exact absurd hmax hm
  · rintro ⟨y, b, hy, hb, hne⟩
    rcases y with n | q
    · rcases b with m | q
      · exact hne rfl
      · exact hb.2 (Sum.Lex.inl_lt_inl_iff.2 (Nat.lt_succ_self n)) (Sum.Lex.inl_lt_inr (n + 1) q)
    · obtain rfl := hcl q hy
      exact absurd hb.1 (not_lt.2 (hmax hb.1.le))

-- `Statement:` on the disjoint sum `Fin 3 ⊕ ℚ`, the closure sending `1` to `2` and fixing every
-- other point has a corner (the landing `0`, its cover `1`, moved to `2`), so it passes `corner`;
-- the landing `inr 0` is not maximal and has no cover, so `cover` refuses it.
example : ∃ c : ClosureOperator (Fin 3 ⊕ ℚ),
    (∀ x, c x = Sum.map (fun z : Fin 3 => if z = 1 then 2 else z) id x) ∧
    (c.IsClosed (Sum.inl 0) ∧ (Sum.inl 0 : Fin 3 ⊕ ℚ) ⋖ Sum.inl 1 ∧ c (Sum.inl 1) = Sum.inl 2) ∧
    c.IsClosed (Sum.inr 0) ∧ ¬ IsMax (Sum.inr 0 : Fin 3 ⊕ ℚ) ∧
    ¬ ∃ b, (Sum.inr 0 : Fin 3 ⊕ ℚ) ⋖ b := by
  let f : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else x
  have hmono : ∀ a b : Fin 3, a ≤ b → f a ≤ f b := by decide
  have hinfl : ∀ a : Fin 3, a ≤ f a := by decide
  have hidem : ∀ a : Fin 3, f (f a) ≤ f a := by decide
  let c : ClosureOperator (Fin 3 ⊕ ℚ) := ClosureOperator.mk' (Sum.map f id)
    (fun _ _ h => by
      cases h with
      | inl h => exact Sum.LiftRel.inl (hmono _ _ h)
      | inr h => exact Sum.LiftRel.inr h)
    (fun a => by
      cases a with
      | inl x => exact Sum.LiftRel.inl (hinfl x)
      | inr q => exact Sum.LiftRel.inr le_rfl)
    (fun a => by
      cases a with
      | inl x => exact Sum.LiftRel.inl (hidem x)
      | inr q => exact Sum.LiftRel.inr le_rfl)
  have hf0 : f 0 = 0 := by decide
  have hf1 : f 1 = 2 := by decide
  refine ⟨c, fun _ => rfl, ⟨c.isClosed_iff.2 ?_, ⟨Sum.inl_lt_inl_iff.2 (by decide),
    fun d h1 h2 => ?_⟩, ?_⟩, c.isClosed_iff.2 rfl, fun h => ?_, ?_⟩
  · show Sum.inl (f 0) = Sum.inl 0
    rw [hf0]
  · cases d with
    | inl z =>
      have h1' := Sum.inl_lt_inl_iff.1 h1
      have h2' := Sum.inl_lt_inl_iff.1 h2
      clear h1 h2
      revert z
      decide
    | inr q => exact Sum.not_inr_lt_inl h2
  · show Sum.inl (f 1) = Sum.inl 2
    rw [hf1]
  · have := Sum.inr_le_inr_iff.1 (h (Sum.inr_le_inr_iff.2 (zero_le_one' ℚ)))
    norm_num at this
  · rintro ⟨b, hb⟩
    cases b with
    | inl w => exact Sum.not_inr_le_inl hb.1.le
    | inr q =>
      obtain ⟨m, h1, h2⟩ := exists_between (Sum.inr_lt_inr_iff.1 hb.1)
      exact hb.2 (Sum.inr_lt_inr_iff.2 h1) (Sum.inr_lt_inr_iff.2 h2)

/-! ### § IV. The ordinal instance -/

/-- `Statement:` the ordinals carry the shape with `up` the snap-nucleus `nfp (ω^·)` (`snapNucleus`),
    covers by `Order.succ`, and the corner at the landing `ε_ 0` and its cover `succ (ε_ 0)`, which
    `up` sends to `ε_ (succ 0)` (`succession_succ`), a limit ordinal (Mathlib `Order.IsSuccLimit`,
    via `Ordinal.isSuccLimit_opow_left` and `Ordinal.omega0_opow_epsilon`) and so not `succ (ε_ 0)`. -/
noncomputable def ordinalUpAndOver : UpAndOver Ordinal.{u} where
  up := snapNucleus.toClosureOperator
  corner := ⟨Ordinal.epsilon 0, Order.succ (Ordinal.epsilon 0),
    snapNucleus.toClosureOperator.isClosed_iff.2 (snapNucleus_fixes_epsilon 0),
    Order.covBy_succ _, by
      show Ordinal.nfp (fun a => Ordinal.omega0 ^ a) (Order.succ (Ordinal.epsilon 0))
        ≠ Order.succ (Ordinal.epsilon 0)
      rw [← succession_succ]
      intro h
      have hl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
        (Ordinal.epsilon_pos (Order.succ 0)).ne'
      rw [Ordinal.omega0_opow_epsilon, h] at hl
      exact Order.not_isSuccLimit_succ _ hl⟩
  cover := fun y _ _ => ⟨Order.succ y, Order.covBy_succ y⟩

/-- `Statement:` `up` on the ordinal instance is `nfp (ω^·)`. -/
theorem ordinalUpAndOver_up (x : Ordinal.{u}) :
    ordinalUpAndOver.up x = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) x :=
  rfl

/-- `Statement:` Veblen's derivative of `ω^·` at a successor index is one over-then-up step from the
    previous value (Mathlib `Ordinal.deriv_add_one`; the `ε`-form is `succession_succ`). -/
theorem deriv_add_one_eq_up_succ (o : Ordinal.{u}) :
    Ordinal.deriv (fun a => Ordinal.omega0 ^ a) (o + 1)
      = ordinalUpAndOver.up (Order.succ (Ordinal.deriv (fun a => Ordinal.omega0 ^ a) o)) := by
  rw [Ordinal.deriv_add_one, Order.succ_eq_add_one]
  rfl

/-- `Statement:` at a limit index `o`, no lower rung reaches `ε_ o` by one over-then-up step. -/
theorem limit_rung_no_over_leg (o p : Ordinal.{u}) (ho : Order.IsSuccLimit o) (hp : p < o) :
    ordinalUpAndOver.up (Order.succ (Ordinal.epsilon p)) ≠ Ordinal.epsilon o := by
  rw [ordinalUpAndOver_up, ← succession_succ]
  exact (succession_strictMono (ho.succ_lt hp)).ne

-- `Statement:` from every rung `ε_ p`, lower or not, one over-then-up step never reaches a limit
-- rung `ε_ o`.
example (o p : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    ordinalUpAndOver.up (Order.succ (Ordinal.epsilon p)) ≠ Ordinal.epsilon o := by
  rw [ordinalUpAndOver_up, ← succession_succ]
  intro h
  exact ho.succ_ne p (succession_strictMono.injective h)

-- `Statement:` the cell of `ε_ (o+1)` contains every seed in `(ε_ o, ε_ (o+1)]`
-- (`nfp_seed_successor_cell`, Veblen 1908, Corollary 1 to Theorem 4, clause (B)).
example (o s : Ordinal.{u}) (h1 : Ordinal.epsilon o < s) (h2 : s ≤ Ordinal.epsilon (Order.succ o)) :
    ordinalUpAndOver.up s = Ordinal.epsilon (Order.succ o) :=
  nfp_seed_successor_cell o s h1 h2

-- `Statement:` the cell of a limit rung is the rung alone (`seed_eq_of_nfp_eq_epsilon_limit`).
example (o s : Ordinal.{u}) (ho : Order.IsSuccLimit o) (h : ordinalUpAndOver.up s = Ordinal.epsilon o) :
    s = Ordinal.epsilon o :=
  seed_eq_of_nfp_eq_epsilon_limit o s ho h

end ZeroParadox

/-! ## Axiom Purity Check

The named declarations of §§ I-II measure `[propext, Quot.sound]`. § IV inherits
`Classical.choice` from `snapNucleus` and Mathlib's `Ordinal` fixed-point theory, STATEMENT-CARRIED as in
`ZeroParadox/Ordinal/SnapNucleus.lean` (statement control on each, measured 2026-10-08). -/

section PurityCheck
open ZeroParadox

#print axioms UpAndOver
#print axioms UpAndOver.moves
#print axioms UpAndOver.open_landing
#print axioms UpAndOver.up_eq_of_mem_Icc
#print axioms UpAndOver.up_not_injective
#print axioms UpAndOver.exists_next_landing
#print axioms UpAndOver.up_le_of_covBy
#print axioms UpAndOver.isEmpty_of_denselyOrdered
#print axioms ordinalUpAndOver
#print axioms ordinalUpAndOver_up
#print axioms deriv_add_one_eq_up_succ
#print axioms limit_rung_no_over_leg

end PurityCheck
