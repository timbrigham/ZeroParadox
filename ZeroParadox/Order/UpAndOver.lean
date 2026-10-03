import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.SnapSuccession
import ZeroParadox.Reals.OrderedField
import Mathlib.Order.Closure
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The up-and-over shape: a closure operator with a cover at every non-maximal landing

## Engineer's Take

(assembled from Tim's words 2026-10-01/02; pending his edit)

I think it is the same shape, what our "up and over" transform applied. The up and over always felt L
or J shaped. The cell width vs layer height. I think we're seeing it. The fundamental premise being
that that exact shape continues to recur, defining the shape when we can do it. Extrapolated away from
types, into the motions that it takes to get there.

---

## Formal Overview (AI-assisted)
`UpAndOver α` bundles a Mathlib `ClosureOperator` (UP) with a carrier-order cover at each
non-maximal landing (OVER) and two existential non-degeneracy fields, all data. § III refuses the
degenerate carriers; § IV is the ordinal instance. Prior art and fences: `ZeroParadox/Order/UpAndOver.md`.
-/

namespace ZeroParadox

open Order Ordinal

universe u

/-! ### § I. The shape -/

/-- `Statement:` a closure operator `up` on a partial order that moves some point, has two distinct
    closed points, and gives every non-maximal closed point a cover in the carrier order.
    `Reading:` UP is `up`; OVER is the step from a landing to a cover of it. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `ClosureOperator` admits the identity and the
-- constant-top closure and says nothing about covers; this bundles it with existential
-- non-degeneracy and a carrier-order cover at each non-maximal closed point, the field that
-- excludes dense carriers such as ℝ with ceiling.
structure UpAndOver (α : Type u) [PartialOrder α] where
  /-- The UP leg: a closure operator; its closed points are the landings. -/
  up : ClosureOperator α
  /-- Some point is moved by `up`. -/
  moves : ∃ x, up x ≠ x
  /-- Two distinct landings exist. -/
  two_landings : ∃ y z, up.IsClosed y ∧ up.IsClosed z ∧ y ≠ z
  /-- The OVER leg: every landing with something above it has a cover in the carrier order. -/
  cover : ∀ y, up.IsClosed y → ¬ IsMax y → ∃ b, y ⋖ b

namespace UpAndOver

variable {α : Type u} [PartialOrder α] (U : UpAndOver α)

/-! ### § II. Derived facts -/

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

/-- `Statement:` a densely ordered carrier with no maximal element carries no `UpAndOver`: density
    refuses the cover (the corpus form is `axb1_fails_everywhere_iff_dense`). -/
theorem isEmpty_of_denselyOrdered [DenselyOrdered α] [NoMaxOrder α] : IsEmpty (UpAndOver α) :=
  ⟨fun U => by
    obtain ⟨y, -, hy, -, -⟩ := U.two_landings
    obtain ⟨z, hz⟩ := exists_gt y
    obtain ⟨b, hb⟩ := U.cover y hy fun h => not_le_of_gt hz (h hz.le)
    obtain ⟨c, h1, h2⟩ := exists_between hb.1
    exact hb.2 h1 h2⟩

end UpAndOver

/-! ### § III. NO-GO gauge — what fails to be an `UpAndOver`? Each control fails one field. -/

-- `Statement:` the ceiling map on ℝ is a closure operator that moves `1/2`, is not injective, and has
-- the two distinct closed points `0` and `1`; ℝ still carries no `UpAndOver`, so `cover` is the field
-- that refuses it.
example : ∃ c : ClosureOperator ℝ, (∀ x, c x = (⌈x⌉ : ℝ)) ∧ c (1 / 2) ≠ 1 / 2 ∧
    ¬ Function.Injective c ∧ c.IsClosed 0 ∧ c.IsClosed 1 ∧ (0 : ℝ) ≠ 1 := by
  let c : ClosureOperator ℝ := ClosureOperator.mk' (fun x => (⌈x⌉ : ℝ))
    (fun _ _ h => Int.cast_mono (Int.ceil_mono h)) (fun x => Int.le_ceil x) (fun x => by simp)
  refine ⟨c, fun _ => rfl, ?_, ?_, c.isClosed_iff.2 ?_, c.isClosed_iff.2 ?_, by norm_num⟩
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

-- `Statement:` the identity closure moves nothing, so it is the `up` of no `UpAndOver`.
example (α : Type u) [PartialOrder α] : ¬ ∃ U : UpAndOver α, U.up = ClosureOperator.id α := by
  rintro ⟨U, hU⟩
  obtain ⟨x, hx⟩ := U.moves
  exact hx (by rw [hU]; rfl)

-- `Statement:` no `UpAndOver` on `Unit` (nothing moves) or on `Empty` (`moves` is existential).
example : IsEmpty (UpAndOver Unit) :=
  ⟨fun U => by obtain ⟨x, hx⟩ := U.moves; exact hx (Subsingleton.elim _ _)⟩
example : IsEmpty (UpAndOver Empty) :=
  ⟨fun U => by obtain ⟨x, -⟩ := U.moves; exact x.elim⟩

-- `Statement:` a closure sending every point to `⊤` exists on `Bool` and moves `false`; any such
-- closure has at most one closed point, so `two_landings` refuses it.
example : ∃ c : ClosureOperator Bool, (∀ x, c x = ⊤) ∧ c false ≠ false :=
  ⟨ClosureOperator.mk' (fun _ => ⊤) (fun _ _ _ => le_rfl) (fun _ => le_top) (fun _ => le_rfl),
    fun _ => rfl, fun h => Bool.noConfusion h⟩
example {α : Type u} [PartialOrder α] [OrderTop α] (c : ClosureOperator α) (hc : ∀ x, c x = ⊤) :
    ¬ ∃ y z, c.IsClosed y ∧ c.IsClosed z ∧ y ≠ z := by
  rintro ⟨y, z, hy, hz, hne⟩
  exact hne (hy.closure_eq.symm.trans ((hc y).trans ((hc z).symm.trans hz.closure_eq)))

/-! ### § IV. The ordinal instance -/

/-- `Statement:` the ordinals carry the shape with `up` the snap-nucleus `nfp (ω^·)` (`snapNucleus`)
    and covers by `Order.succ`. -/
noncomputable def ordinalUpAndOver : UpAndOver Ordinal.{u} where
  up := snapNucleus.toClosureOperator
  moves := ⟨⊥, snapNucleus_bot_ne_bot⟩
  two_landings := ⟨Ordinal.epsilon 0, Ordinal.epsilon (Order.succ 0),
    snapNucleus.toClosureOperator.isClosed_iff.2 (snapNucleus_fixes_epsilon 0),
    snapNucleus.toClosureOperator.isClosed_iff.2 (snapNucleus_fixes_epsilon _),
    (succession_lt_succ 0).ne⟩
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

-- `Statement:` the cell of `ε_ (o+1)` contains every seed in `(ε_ o, ε_ (o+1)]`
-- (`nfp_seed_successor_cell`, Veblen 1908 Cor. 1 clause B).
example (o s : Ordinal.{u}) (h1 : Ordinal.epsilon o < s) (h2 : s ≤ Ordinal.epsilon (Order.succ o)) :
    ordinalUpAndOver.up s = Ordinal.epsilon (Order.succ o) :=
  nfp_seed_successor_cell o s h1 h2

-- `Statement:` the cell of a limit rung is the rung alone (`seed_eq_of_nfp_eq_epsilon_limit`).
example (o s : Ordinal.{u}) (ho : Order.IsSuccLimit o) (h : ordinalUpAndOver.up s = Ordinal.epsilon o) :
    s = Ordinal.epsilon o :=
  seed_eq_of_nfp_eq_epsilon_limit o s ho h

end ZeroParadox

/-! ## Axiom Purity Check

§§ I-II measure `[propext, Quot.sound]`; Mathlib's `not_isMax` carries `Classical.choice`, so
`isEmpty_of_denselyOrdered` reaches non-maximality through `exists_gt` instead. § IV inherits
`Classical.choice` from `snapNucleus` and Mathlib's `Ordinal` fixed-point theory, UNCLASSIFIED as in
`ZeroParadox/Ordinal/SnapNucleus.lean`. -/

section PurityCheck
open ZeroParadox

#print axioms UpAndOver
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
