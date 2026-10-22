import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.SnapSuccession
import ZeroParadox.Reals.OrderedField
import Mathlib.Order.Closure
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The up-and-over shape's climbing kind: a closure operator with a corner and a cover at every non-maximal landing

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

/-! ### § I. The climbing kind -/

/-- `Statement:` a closure operator `up` on a partial order with a closed point `y` and a cover `b`
    of `y` that `up` moves, and a cover in the carrier order at every non-maximal closed point.
    `UpAndOver.toMotion`, OVER every cover of the carrier (one chosen wiring), climbs and does not loop
    (`UpAndOver.toMotion_climb`, `UpAndOver.toMotion_not_loop`); with the always-true OVER, § III's
    `Fin 3` closure loops (the `CONTROL` in § VI).
    `Reading:` UP is `up`; OVER is the step from a landing to a cover of it; `corner` is a place
    where OVER then UP moves. This presents the climbing kind of the up-and-over shape; the loop kind
    is `Motion.Loop` (`ZeroParadox/Die.lean`). -/
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

-- `Statement:` the three-point chain `Fin 3` carries an `UpAndOver`: the closure sending `1` to `2` and
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

/-! ### § III-b. Members on an order dual: the keep-above kernel -/

/-- `Statement:` given a least point `e` and a point `a`, the map sending `x` to `a` if `a ≤ x` and to `e`
    otherwise, as a closure operator on `αᵒᵈ`: deflationary, monotone and idempotent in `α`.
    `Reading:` the closure operator on the order dual whose closed points are `e` and `a`; in `αᵒᵈ`
    the set `{e, a}` is a closure system (Glück, "Isolated Suborders and Their Application to Counting
    Closure Operators", LMCS 20(3), 2024, Def. 3.3, p. 11:4: every point has a least element of the
    set above it), which determines exactly one closure operator (his Lemma 3.6). Mathlib's form:
    `ClosureOperator.ofPred` builds one from a map and a closedness predicate when the map sends each
    point to a least closed point above it, and `ClosureOperator.eq_ofPred_closed` says every closure
    operator arises that way. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: several of Mathlib's constructors build a closure operator
-- from a map with its laws or from a predicate (e.g. `ClosureOperator.mk'`; `ClosureOperator.ofPred`,
-- a map with a closedness predicate; `ClosureOperator.ofCompletePred`). This kernel, with closed
-- points `{e, a}` in a partial order with decidable `≤` and a least point `e`, as a named Mathlib
-- declaration was not located as of 2026-10-21, searched as follows: `exact?` on its existence (no
-- result), a grep of the pinned Mathlib for `InteriorOperator`, "interior operator", "kernel
-- operator" and "coclosure" (no hit), `Mathlib/Order/Closure.lean` read, and the Galois-connection
-- route: every closure operator is the one of its own Galois insertion into its closed points
-- (`ClosureOperator.gi`, `closureOperator_gi_self`), which names no particular kernel
-- (`LEAN_CUSTOM_REGISTRY.md`).
def keepAboveKernel {α : Type u} [PartialOrder α] [DecidableLE α] (e a : α) (he : ∀ x, e ≤ x) :
    ClosureOperator αᵒᵈ where
  toFun x := OrderDual.toDual (if a ≤ OrderDual.ofDual x then a else e)
  monotone' x y hxy := by
    change (if a ≤ OrderDual.ofDual y then a else e) ≤ (if a ≤ OrderDual.ofDual x then a else e)
    have hyx : OrderDual.ofDual y ≤ OrderDual.ofDual x := hxy
    by_cases hy : a ≤ OrderDual.ofDual y
    · rw [if_pos hy, if_pos (hy.trans hyx)]
    · rw [if_neg hy]; exact he _
  le_closure' x := by
    change (if a ≤ OrderDual.ofDual x then a else e) ≤ OrderDual.ofDual x
    split_ifs with h
    · exact h
    · exact he _
  idempotent' x := by
    change (if a ≤ (if a ≤ OrderDual.ofDual x then a else e) then a else e)
      = (if a ≤ OrderDual.ofDual x then a else e)
    by_cases h : a ≤ OrderDual.ofDual x
    · rw [if_pos h, if_pos le_rfl]
    · rw [if_neg h]
      by_cases h2 : a ≤ e
      · exact absurd (h2.trans (he _)) h
      · rw [if_neg h2]

-- The `DecidableLE` binder is kept in the type on purpose: `nonempty_upAndOver_dual_of_covBy_classical`
-- below is the same statement without it, and the PurityCheck prints both footprints.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable `≤`, if `e` is a least point of `α` and `b ⋖ a` with `b ≠ e`, then `αᵒᵈ`
    carries an `UpAndOver`: UP the keep-above kernel of `e` and `a`, the corner at `a` with its dual
    cover `b`. -/
theorem nonempty_upAndOver_dual_of_covBy {α : Type u} [PartialOrder α] [DecidableLE α] (e a b : α)
    (he : ∀ x, e ≤ x) (hba : b ⋖ a) (hbe : b ≠ e) : Nonempty (UpAndOver αᵒᵈ) := by
  let K := keepAboveKernel e a he
  have Kval : ∀ x, OrderDual.ofDual (K x) = if a ≤ OrderDual.ofDual x then a else e :=
    fun _ => rfl
  have closed_iff : ∀ x, K.IsClosed x → OrderDual.ofDual x = a ∨ OrderDual.ofDual x = e := by
    intro x hx
    have := congrArg OrderDual.ofDual hx.closure_eq
    rw [Kval] at this
    split_ifs at this <;> [exact Or.inl this.symm; exact Or.inr this.symm]
  refine ⟨⟨K, ⟨OrderDual.toDual a, OrderDual.toDual b, ?_, ?_, ?_⟩, ?_⟩⟩
  · rw [ClosureOperator.isClosed_iff]
    apply congrArg OrderDual.toDual
    exact (Kval (OrderDual.toDual a)).trans (if_pos le_rfl)
  · exact toDual_covBy_toDual_iff.2 hba
  · intro h
    have := congrArg OrderDual.ofDual h
    rw [Kval] at this
    rw [OrderDual.ofDual_toDual, if_neg (fun h => lt_irrefl _ (hba.lt.trans_le h))] at this
    exact hbe this.symm
  · intro y hy hmax
    rcases closed_iff y hy with h | h
    · refine ⟨OrderDual.toDual b, ?_⟩
      have : y = OrderDual.toDual a := h
      rw [this]; exact toDual_covBy_toDual_iff.2 hba
    · exfalso; apply hmax
      intro z _
      show OrderDual.ofDual y ≤ OrderDual.ofDual z
      rw [h]; exact he _

/-- `Statement:` the same with no `DecidableLE` binder, proved with `classical`. -/
theorem nonempty_upAndOver_dual_of_covBy_classical {α : Type u} [PartialOrder α] (e a b : α)
    (he : ∀ x, e ≤ x) (hba : b ⋖ a) (hbe : b ≠ e) : Nonempty (UpAndOver αᵒᵈ) := by
  classical
  exact nonempty_upAndOver_dual_of_covBy e a b he hba hbe

/-! ### § IV. The ordinal instance -/

/-- `Statement:` the ordinals carry an `UpAndOver` with `up` the snap-nucleus `nfp (ω^·)` (`snapNucleus`),
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

/-! ### § V. The ordinal instance as a die motion (`ZeroParadox/Die.lean` § XI) -/

/-- `Statement:` on `Ordinal`, UP `nfp (ω^·)` (as in `ordinalUpAndOver`) and OVER `Order.succ`. -/
noncomputable def ordinalSuccMotion : Motion Ordinal.{u} :=
  Motion.ofTotal (Ordinal.nfp fun a => Ordinal.omega0 ^ a)
    (fun x => Ordinal.nfp_eq_self (Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) x))
    (fun a b => b = Order.succ a)

/-- `Statement:` no successor ordinal is fixed by `α ↦ ω^α`. -/
theorem omega0_opow_succ_ne (a : Ordinal.{u}) :
    Ordinal.omega0 ^ Order.succ a ≠ Order.succ a := by
  intro h
  have hlim := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0
    (lt_of_le_of_lt (zero_le a) (Order.lt_succ a)).ne'
  rw [h] at hlim
  exact Order.not_isSuccLimit_succ a hlim

/-- `Statement:` the corner of `ordinalSuccMotion` fires, at the landing ε₀ (`corner_ofTotal_iff`). -/
theorem ordinalSuccMotion_corner : ordinalSuccMotion.{u}.Corner :=
  (Motion.corner_ofTotal_iff _ (fun a => Ordinal.omega0 ^ a) Order.succ _
    (fun x => ⟨fun h => h ▸ Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) x,
      Ordinal.nfp_eq_self⟩)).2
    ⟨Ordinal.epsilon 0, Ordinal.omega0_opow_epsilon 0, omega0_opow_succ_ne _⟩

/-- `Statement:` `ordinalSuccMotion` climbs: from ε₀, a step to `succ ε₀`, and UP to a third point. -/
theorem ordinalSuccMotion_climb : ordinalSuccMotion.{u}.Climb := by
  have hn := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  refine ⟨Ordinal.epsilon 0, Order.succ (Ordinal.epsilon 0),
    Ordinal.nfp (fun a => Ordinal.omega0 ^ a) (Order.succ (Ordinal.epsilon 0)),
    Part.mem_some_iff.2 (Ordinal.nfp_eq_self (Ordinal.omega0_opow_epsilon 0)).symm, rfl,
    Part.mem_some _, fun h => ?_,
    (lt_of_lt_of_le (Order.lt_succ _) (Ordinal.le_nfp _ _)).ne'⟩
  have := Ordinal.nfp_fp hn (Order.succ (Ordinal.epsilon 0))
  rw [h] at this
  exact omega0_opow_succ_ne _ this

/-- `Statement:` UP sends `succ ε₀` to ε₁. -/
theorem ordinalSuccMotion_up_succ_epsilon0 :
    Ordinal.nfp (fun a => Ordinal.omega0 ^ a) (Order.succ (Ordinal.epsilon 0)) =
      Ordinal.epsilon.{u} 1 := by
  rw [← Ordinal.epsilon_succ_eq_nfp, Order.succ_eq_add_one, zero_add]

/-- `Statement:` the corner composite of `ordinalSuccMotion`: OVER `Order.succ`, then UP
    `nfp (ω^·)`, as one map on `Ordinal`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `Ordinal.deriv_succ` has this shape only at
-- the values of `Ordinal.deriv` (`deriv f (succ o) = nfp f (succ (deriv f o))`); the map
-- `a ↦ nfp (ω^·) (succ a)` on every ordinal, as a named Mathlib declaration, was not located as of
-- 2026-10-21, searched as follows: the `def`s of `Mathlib/SetTheory/Ordinal/FixedPoint.lean` and
-- `Veblen.lean` listed, and a grep of both for `nfp` applied to a successor or `+ 1` (hits:
-- `deriv_add_one`, `deriv_succ`, `epsilon_succ_eq_nfp`, `gamma_succ_eq_nfp` and one `nfp (a * ·)`
-- lemma, none a definition).
noncomputable def ordinalCornerStep (a : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.nfp (fun x => Ordinal.omega0 ^ x) (Order.succ a)

/-- `Statement:` the corner composite moves every ordinal strictly up. -/
theorem lt_ordinalCornerStep (a : Ordinal.{u}) : a < ordinalCornerStep a :=
  lt_of_lt_of_le (Order.lt_succ a) (Ordinal.le_nfp _ _)

/-- `Statement:` iterated `n + 1` times from 0, ⊥ of `Ordinal`, the corner composite gives `ε_n`. -/
theorem ordinalCornerStep_iterate (n : ℕ) :
    ordinalCornerStep^[n + 1] (0 : Ordinal.{u}) = Ordinal.epsilon (n : Ordinal.{u}) := by
  induction n with
  | zero =>
    show Ordinal.nfp _ (Order.succ 0) = Ordinal.epsilon ((0 : ℕ) : Ordinal.{u})
    have hm := (Ordinal.isNormal_opow (a := Ordinal.omega0.{u}) Ordinal.one_lt_omega0).strictMono.monotone
    rw [Nat.cast_zero]
    refine le_antisymm (Ordinal.nfp_le_fp hm (Order.succ_le_of_lt (Ordinal.epsilon_pos 0))
      (Ordinal.omega0_opow_epsilon 0).le) ?_
    rw [Ordinal.epsilon_zero_eq_nfp]
    exact Ordinal.nfp_monotone hm (Order.le_succ 0)
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    show Ordinal.nfp _ (Order.succ (Ordinal.epsilon (n : Ordinal.{u}))) = _
    rw [← Ordinal.epsilon_succ_eq_nfp, Order.succ_eq_add_one]
    push_cast; rfl

/-- `Statement:` the iterates of the corner composite from 0, ⊥ of `Ordinal`, strictly increase. -/
theorem ordinalCornerStep_iterate_strictMono :
    StrictMono fun n : ℕ => ordinalCornerStep^[n] (0 : Ordinal.{u}) :=
  strictMono_nat_of_lt_succ fun n => by
    simp only [Function.iterate_succ_apply']
    exact lt_ordinalCornerStep _

/-- `Statement:` no ordinal steps, under `ordinalSuccMotion`, to an iterate of the corner composite
    from 0: 0 is not a successor, and `ε_n` is fixed by `ω^·` while no successor is. -/
theorem not_step_into_ordinalCornerStep_iterate (n : ℕ) (a : Ordinal.{u}) :
    ¬ ordinalSuccMotion.step a (ordinalCornerStep^[n] 0) := by
  intro h
  have h' : ordinalCornerStep^[n] 0 = Order.succ a := h
  cases n with
  | zero => exact (Order.bot_lt_succ a).ne' h'.symm
  | succ n =>
    rw [ordinalCornerStep_iterate] at h'
    have hf := Ordinal.omega0_opow_epsilon (n : Ordinal.{u})
    rw [h'] at hf
    exact omega0_opow_succ_ne a hf

/-- `Statement:` `ordinalSuccMotion` does not loop: UP after a step lands strictly above. -/
theorem ordinalSuccMotion_not_loop : ¬ ordinalSuccMotion.{u}.Loop := by
  rintro ⟨y, b, -, hs, -, hyb⟩
  have hb : b = Order.succ y := hs
  have hy : y = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) b := Part.mem_some_iff.1 hyb
  have hlt : y < Ordinal.nfp (fun a => Ordinal.omega0 ^ a) b := by
    rw [hb]; exact lt_of_lt_of_le (Order.lt_succ y) (Ordinal.le_nfp _ _)
  exact absurd hy hlt.ne

/-- `Statement:` in `Ordinal`'s order the legs of `ordinalSuccMotion` agree: UP and OVER both raise. -/
theorem ordinalSuccMotion_agree : ordinalSuccMotion.{u}.Agree :=
  ⟨fun x _ h => (Part.mem_some_iff.1 h) ▸ Ordinal.le_nfp _ x,
   fun x _ h => (show _ = Order.succ x from h) ▸ Order.le_succ x⟩

-- Statement: with `ordinalSuccMotion_agree`, `Motion.not_loop_of_agree` re-derives `ordinalSuccMotion_not_loop`.
example : ¬ ordinalSuccMotion.{u}.Loop := Motion.not_loop_of_agree ordinalSuccMotion_agree

/-- `Statement:` `ordinalSuccMotion` has an elbow: UP sends `1` to `nfp (ω^·) 1 ≠ 1`, which steps to
    its successor. -/
theorem ordinalSuccMotion_elbow : ordinalSuccMotion.{u}.Elbow :=
  ⟨1, Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 1,
    Order.succ (Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 1), Part.mem_some _, fun h => by
      have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) (1 : Ordinal.{u})
      rw [h, Ordinal.opow_one] at this
      exact Ordinal.one_lt_omega0.ne' this, rfl⟩

/-- `Statement:` `ordinalSuccMotion` restricted (`Motion.restrict`) to `Set.Ici` of the `n`-th iterate
    of the corner composite from 0; UP and OVER both raise, so the set is closed under both. -/
noncomputable def ordinalView (n : ℕ) : Motion (Set.Ici (ordinalCornerStep^[n] (0 : Ordinal.{u}))) :=
  ordinalSuccMotion.restrict _ (Motion.upClosed_Ici ordinalSuccMotion_agree.1 _)

/-- `Statement:` ⊥ of `Set.Ici` of the `n + 1`-th iterate is a landing of `ordinalView (n + 1)`. -/
theorem ordinalView_bot_isLanding (n : ℕ) : (ordinalView.{u} (n + 1)).IsLanding ⊥ := by
  rw [ordinalView, Motion.restrict_isLanding_iff]
  show _ ∈ Part.some _
  rw [Part.mem_some_iff]
  show ordinalCornerStep^[n + 1] 0 = Ordinal.nfp _ (ordinalCornerStep^[n + 1] 0)
  rw [ordinalCornerStep_iterate]
  exact (Ordinal.nfp_eq_self (Ordinal.omega0_opow_epsilon _)).symm

/-- `Statement:` ⊥ of `Set.Ici 0`, which is 0, ⊥ of `Ordinal`, is not a landing of `ordinalView 0`. -/
theorem ordinalView_zero_bot_not_isLanding : ¬ (ordinalView.{u} 0).IsLanding ⊥ := by
  rw [ordinalView, Motion.restrict_isLanding_iff]
  intro h
  have h' : (0 : Ordinal.{u}) = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 0 := Part.mem_some_iff.1 h
  have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) (0 : Ordinal.{u})
  rw [← h'] at this
  exact bot_is_not_a_step this

/-- `Statement:` every landing of `ordinalView 0` is at or above ε₀. -/
theorem ordinalView_zero_least_landing (y : Set.Ici (ordinalCornerStep^[0] (0 : Ordinal.{u})))
    (hy : (ordinalView.{u} 0).IsLanding y) : Ordinal.epsilon 0 ≤ y.1 := by
  rw [ordinalView, Motion.restrict_isLanding_iff] at hy
  have hy' : y.1 = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) y.1 := Part.mem_some_iff.1 hy
  have hfix : Ordinal.omega0 ^ y.1 = y.1 := by
    have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) y.1
    rwa [← hy'] at this
  rw [Ordinal.epsilon_zero_eq_nfp]
  exact Ordinal.nfp_le_fp
    (Ordinal.isNormal_opow (a := Ordinal.omega0.{u}) Ordinal.one_lt_omega0).strictMono.monotone
    (zero_le _) hfix.le

/-- `Statement:` every step of `ordinalView n` into its ⊥ starts at that ⊥. -/
theorem ordinalView_bot_noEntry (n : ℕ) : ∀ a, (ordinalView.{u} n).step a ⊥ → a = ⊥ :=
  fun a hs => Motion.eq_bot_of_step_to_bot
    (Motion.restrict_stepRaises_Ici ordinalSuccMotion_agree.2 _ _) a hs

/-- `Statement:` the `n + 1`-th iterate, as a point of `ordinalView n`, is not its ⊥, and every step
    into it starts at it (no step reaches it). -/
theorem ordinalView_next_bot_noEntry (n : ℕ) :
    (∀ a, (ordinalView.{u} n).step a
        ⟨ordinalCornerStep^[n + 1] 0, (ordinalCornerStep_iterate_strictMono (Nat.lt_succ_self n)).le⟩ →
      a = ⟨ordinalCornerStep^[n + 1] 0, (ordinalCornerStep_iterate_strictMono (Nat.lt_succ_self n)).le⟩) ∧
    (⟨ordinalCornerStep^[n + 1] 0, (ordinalCornerStep_iterate_strictMono (Nat.lt_succ_self n)).le⟩ :
      Set.Ici (ordinalCornerStep^[n] (0 : Ordinal.{u}))) ≠ ⊥ :=
  ⟨fun a hs => absurd hs (not_step_into_ordinalCornerStep_iterate (n + 1) a.1),
   fun h => (ordinalCornerStep_iterate_strictMono (Nat.lt_succ_self n)).ne'
     (congrArg Subtype.val h)⟩

/-- `Statement:` ⊥ of `ordinalView n` steps elsewhere, to its successor. -/
theorem ordinalView_bot_leavesAt (n : ℕ) : (ordinalView.{u} n).LeavesAt ⊥ :=
  ⟨⟨Order.succ (ordinalCornerStep^[n] 0), Set.mem_Ici.2 (Order.le_succ _)⟩, rfl,
   fun h => (Order.lt_succ (ordinalCornerStep^[n] (0 : Ordinal.{u}))).ne' (congrArg Subtype.val h)⟩

/-- `Statement:` `Set.inclusion` is a relation embedding of `ordinalView (n + 1)`'s steps into
    `ordinalView n`'s (`Motion.restrictInclusion`). -/
noncomputable def ordinalViewInclusion (n : ℕ) :
    (ordinalView.{u} (n + 1)).step ↪r (ordinalView.{u} n).step :=
  ordinalSuccMotion.restrictInclusion _ _
    (Set.Ici_subset_Ici.2 (ordinalCornerStep_iterate_strictMono (Nat.lt_succ_self n)).le)

/-- `Statement:` UP commutes with `ordinalViewInclusion`. -/
theorem ordinalViewInclusion_up (n : ℕ) (x y : Set.Ici (ordinalCornerStep^[n + 1] (0 : Ordinal.{u}))) :
    y ∈ (ordinalView.{u} (n + 1)).up x ↔
      ordinalViewInclusion n y ∈ (ordinalView.{u} n).up (ordinalViewInclusion n x) :=
  Motion.restrictInclusion_up _ _ _ x y

/-- `Statement:` `ordinalViewInclusion n` does not send ⊥ of `ordinalView (n + 1)` to ⊥ of
    `ordinalView n`. -/
theorem ordinalViewInclusion_bot_ne (n : ℕ) : ordinalViewInclusion.{u} n ⊥ ≠ ⊥ :=
  fun h => (ordinalCornerStep_iterate_strictMono (Nat.lt_succ_self n)).ne' (congrArg Subtype.val h)

/-- `Statement:` the carrier of `ordinalView n`, `Set.Ici` of the `n`-th corner iterate from 0, as an
    element of `ordinalSuccMotion`'s lattice of UP- and OVER-closed sets (`Motion.closedSublattice`). -/
noncomputable def ordinalViewClosed (n : ℕ) : Motion.closedSublattice ordinalSuccMotion.{u} :=
  ⟨Set.Ici (ordinalCornerStep^[n] (0 : Ordinal.{u})),
   Motion.upClosed_Ici ordinalSuccMotion_agree.1 _,
   Motion.stepClosed_Ici ordinalSuccMotion_agree.2 _⟩

/-- `Statement:` `ordinalViewClosed` is strictly antitone: `m < n` gives a strictly smaller set at `n`. -/
theorem ordinalViewClosed_strictAnti : StrictAnti ordinalViewClosed.{u} := by
  intro m n hmn
  show Set.Ici _ < Set.Ici _
  exact Set.Ici_ssubset_Ici.2 (ordinalCornerStep_iterate_strictMono hmn)

/-! ### § VI. The climbing kind as a die motion: its corner is a climb, never a loop -/

namespace UpAndOver

variable {α : Type u} [PartialOrder α] (U : UpAndOver α)

/-- `Statement:` the die motion of `U`: UP `U.up`, OVER the covers of `α`. -/
def toMotion : Motion α :=
  Motion.ofTotal U.up U.up.idempotent (· ⋖ ·)

/-- `Statement:` in `α`'s order the legs of `U.toMotion` agree: UP and OVER both raise. -/
theorem toMotion_agree : U.toMotion.Agree :=
  ⟨fun x _ h => (Part.mem_some_iff.1 h) ▸ U.up.le_closure x, fun _ _ h => h.lt.le⟩

/-- `Statement:` `U.toMotion` climbs, from the landing and cover of `corner`. -/
theorem toMotion_climb : U.toMotion.Climb := by
  obtain ⟨y, b, hy, hb, hne⟩ := U.corner
  exact ⟨y, b, U.up b, Part.mem_some_iff.2 hy.closure_eq.symm, hb, Part.mem_some _, hne,
    (hb.lt.trans_le (U.up.le_closure b)).ne'⟩

/-- `Statement:` `U.toMotion` does not loop (`Motion.not_loop_of_agree`). -/
theorem toMotion_not_loop : ¬ U.toMotion.Loop :=
  Motion.not_loop_of_agree U.toMotion_agree

/-- `Statement:` a motion that loops is the die motion of no `UpAndOver`; one way. -/
theorem toMotion_ne_of_loop {M : Motion α} (h : M.Loop) : U.toMotion ≠ M :=
  fun e => U.toMotion_not_loop (e ▸ h)

-- Statement: CONTROL: not looping is the wiring's, not the closure's: with the always-true OVER the
-- same `Fin 3` closure (§ III's, `1 ↦ 2`) loops at 2 (step to `1`, UP back to `2`), and still climbs.
example : (Motion.ofTotal (fun x : Fin 3 => if x = 1 then 2 else x) (by decide)
      (fun _ _ => True)).Loop ∧
    (Motion.ofTotal (fun x : Fin 3 => if x = 1 then 2 else x) (by decide) (fun _ _ => True)).Climb :=
  ⟨⟨2, 1, Part.mem_some_iff.2 (by decide), trivial, by decide, Part.mem_some_iff.2 (by decide)⟩,
    ⟨0, 1, 2, Part.mem_some_iff.2 (by decide), trivial, Part.mem_some_iff.2 (by decide), by decide,
      by decide⟩⟩

end UpAndOver

end ZeroParadox

/-! ## Axiom Purity Check

The named declarations of §§ I-II measure `[propext, Quot.sound]`. § IV inherits
`Classical.choice` from `snapNucleus` and Mathlib's `Ordinal` fixed-point theory, STATEMENT-CARRIED as in
`ZeroParadox/Ordinal/SnapNucleus.lean` (statement control on each, measured 2026-10-08). § V's
footprints are printed below; § VI measures `[propext, Quot.sound]`. -/

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
#print axioms keepAboveKernel
#print axioms nonempty_upAndOver_dual_of_covBy
#print axioms nonempty_upAndOver_dual_of_covBy_classical
#print axioms ordinalUpAndOver
#print axioms ordinalUpAndOver_up
#print axioms deriv_add_one_eq_up_succ
#print axioms limit_rung_no_over_leg
#print axioms ordinalSuccMotion
#print axioms omega0_opow_succ_ne
#print axioms ordinalSuccMotion_corner
#print axioms ordinalSuccMotion_climb
#print axioms ordinalSuccMotion_up_succ_epsilon0
#print axioms ordinalCornerStep
#print axioms lt_ordinalCornerStep
#print axioms ordinalCornerStep_iterate
#print axioms ordinalSuccMotion_not_loop
#print axioms ordinalSuccMotion_agree
#print axioms ordinalSuccMotion_elbow
#print axioms ordinalCornerStep_iterate_strictMono
#print axioms not_step_into_ordinalCornerStep_iterate
#print axioms ordinalView
#print axioms ordinalView_bot_isLanding
#print axioms ordinalView_zero_bot_not_isLanding
#print axioms ordinalView_zero_least_landing
#print axioms ordinalView_bot_noEntry
#print axioms ordinalView_next_bot_noEntry
#print axioms ordinalView_bot_leavesAt
#print axioms ordinalViewInclusion
#print axioms ordinalViewInclusion_up
#print axioms ordinalViewInclusion_bot_ne
#print axioms ordinalViewClosed
#print axioms ordinalViewClosed_strictAnti
#print axioms UpAndOver.toMotion
#print axioms UpAndOver.toMotion_agree
#print axioms UpAndOver.toMotion_climb
#print axioms UpAndOver.toMotion_not_loop
#print axioms UpAndOver.toMotion_ne_of_loop

end PurityCheck
