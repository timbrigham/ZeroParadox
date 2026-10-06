import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Ordinal.PricedInterface
import ZeroParadox.Order.LeastFixedPoint
import ZeroParadox.Valuation.SemilatticeInstance

/-!
# Machine-checked characterization index of ε₀ — what ε₀ IS and what it IS NOT

An index of established results pinning ε₀, Mathlib `Ordinal.epsilon 0`. Every indexed name is
`#check`ed, so the `import`s recompile each home file. It creates no named declarations; § I-b,
§ I-c, § IV, § V and § VII carry anonymous `example`s, the only things proved here. The `#check`s cannot overclaim; the
glosses can. Long form: `ZeroParadox/Ordinal/Epsilon0CannotBe.md`.

## Engineer's Take

A canonical official representation of what ε₀ can and cannot be. Defined in Lean and referenced by the
proof assistant during development.

---
-/

section Epsilon0CannotBeIndex

/-! ### § I. What ε₀ IS NOT — the invariants (the bedrock guards) -/
#check @ZeroParadox.epsilon0_ne_zero          -- Statement: ε₀ ≠ 0 in `Ordinal`; against ℤ_[2]'s 0 the equation is ill-typed (§ V)
#check @ZeroParadox.epsilon0_ne_bot           -- Statement: ε₀ ≠ ⊥ of `Ordinal`. Reading: seeded at that ⊥ the base is not its closure; seeded at a fixed point it is (§ I-b, the μ schema at ε₀)

/-! ### § I-b. The ε₀ ROLE is never its floor, at any floor in `Ordinal` (the role, not the value) -/
-- Reading: the ε₀ role relative to a floor `f` is the least ε-number strictly greater than `f`, the
-- least fixed point of `α ↦ ω^α` strictly above `f` (Veblen 1908, Corollary 1 to Theorem 4; see
-- `ZeroParadox/Ordinal/Epsilon0LeastFP.md`); `f` is the bottom of the carrier `Set.Ici f`.
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
-- gives ε₀ (the next example) and the strict form gives ε₁ (the role-versus-value example).
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
-- Reading: other chart. In ℤ_[2] read by its norm, ℤ_[2]'s 0 is least and uniquely least (next
-- example); the tower's images tend to that 0 (`mu_construction_correspondence`), and ε₀ gets no
-- image: `cnfToZp2` takes `NONote`, and every notation denotes below ε₀ (`repr_lt_epsilon0`, the
-- example after). `cnf_bridge_type_boundary` pairs ε₀'s least-fixed-point face with that limit;
-- ε₀ is also the tower's supremum, the other face (`epsilon0_min_eq_max`, § III). No identity.
-- Statement: in ℤ_[2], `‖0‖ ≤ ‖x‖`, and `‖x‖ = 0` forces `x = 0`.
example (x : ℤ_[2]) : ‖(0 : ℤ_[2])‖ ≤ ‖x‖ ∧ (‖x‖ = 0 → x = 0) :=
  ⟨norm_zero (E := ℤ_[2]) ▸ norm_nonneg x, norm_eq_zero.1⟩
#check @ZeroParadox.repr_lt_epsilon0          -- Statement: every `ONote`, in normal form or not, denotes strictly below ε₀
-- Statement: so every `NONote`, the domain of `cnfToZp2`, denotes strictly below ε₀.
example (o : NONote) : o.repr < Ordinal.epsilon 0 := ZeroParadox.repr_lt_epsilon0 o.1

/-! ### § I-c. ⊥ and ε₀ as roles relative to a floor: one occupant per carrier, one per seed -/
-- Reading: a role is a position relative to a floor, a Lean object its occupant; the schema is
-- Knaster–Tarski's and Veblen's (`ZeroParadox/Order/LeastFixedPoint.md`). Value versus role: § I-b.
#check @ZeroParadox.da2_bottom_characterization -- Statement: in one `ZPSemilattice`, `(∀ x, join S x = x) ↔ S = bot`
#check @ZeroParadox.IsLeastFixedPointFrom      -- Statement: `mu` is the least fixed point of `f` at or above `seed` under `r`
#check @ZeroParadox.IsLeastFixedPointFrom.unique -- Statement: for antisymmetric `r`, one seed has at most one such `mu`
#check @ZeroParadox.isLeastFixedPointFrom_nfp  -- Statement: for normal `f`, `nfp f a` is that `mu` at the seed `a`
-- Statement: in `Ordinal`, seeded AT an ε-number floor `ε_o` the schema returns `ε_o`; seeded at
-- `succ ε_o` it returns `ε_(o+1)`, a different ordinal.
example (o : Ordinal) :
    ZeroParadox.IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α)
      (Ordinal.epsilon o) (Ordinal.epsilon o) ∧
    ZeroParadox.IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α)
      (Order.succ (Ordinal.epsilon o)) (Ordinal.epsilon (Order.succ o)) ∧
    Ordinal.epsilon o ≠ Ordinal.epsilon (Order.succ o) := by
  refine ⟨⟨le_rfl, Ordinal.omega0_opow_epsilon o, fun _ _ h => h⟩, ?_, ?_⟩
  · rw [Ordinal.epsilon_succ_eq_nfp]
    exact ZeroParadox.isLeastFixedPointFrom_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) _
  · rw [Ordinal.epsilon_succ_eq_nfp]
    exact (lt_of_lt_of_le (Order.lt_succ _) (Ordinal.le_nfp _ _)).ne
-- Statement: at the floor `0`, ⊥ of `Ordinal`, both seeds give ε₀, since `0` is not a fixed point
-- (`bot_is_not_a_step`, § III).
example : Ordinal.nfp (fun α => Ordinal.omega0 ^ α) 0 =
    Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ 0) :=
  (ZeroParadox.nfp_seed_independent_below_epsilon0 _ (Ordinal.epsilon_pos 0).le).trans
    (ZeroParadox.nfp_seed_independent_below_epsilon0 _
      (Order.succ_le_of_lt (Ordinal.epsilon_pos 0))).symm

/-! ### § II. What ε₀ IS — the construction: first fixed point of the ω-tower from ⊥ of `Ordinal` -/
#check @ZeroParadox.epsilon0_eq_nfp_bot       -- Statement: ε₀ = nfp (ω^·) ⊥, seeded at ⊥ of `Ordinal`
#check @ZeroParadox.epsilonZero_eq_nfp        -- Statement: ε₀ = nfp (ω^·) 0, the same seed written as 0
#check @ZeroParadox.epsilon0_is_fixedpoint    -- Statement: ω ^ ε₀ = ε₀
#check @ZeroParadox.epsilon0_isLeastFixedPointFrom  -- Statement: ε₀ is the least fixed point of ω^· at or above ⊥ of `Ordinal` (μ schema)
#check @ZeroParadox.epsilon0_eq_veblen_one_zero     -- Statement: ε₀ = veblen 1 0, Veblen coordinates (1, 0)

/-! ### § III. ε₀ is BOTH min AND max at once — direction/instance-specific, never collapsed -/
#check @ZeroParadox.epsilon0_min_eq_max       -- Statement: ε₀ is the sup of the tower ∧ the least fixed point of ω^· (`IsLeast`)
#check @ZeroParadox.epsilon0_least_fixedpoint -- Statement: the MIN face, lower-bound half only: ε₀ ≤ every fixed point of ω^·
#check @ZeroParadox.epsilonZero_eq_iSup       -- Statement: the MAX face: ε₀ is the supremum of the ω-tower
#check @ZeroParadox.nothing_between_is_a_step -- Statement: no ordinal below ε₀ is fixed by ω^·. Reading: the in-between ordinals are stages of the ascent, not landings
#check @ZeroParadox.bot_is_not_a_step         -- Statement: ω^0 ≠ 0: ⊥ of `Ordinal` is not fixed by ω^·. Reading: with the line above, ε₀ is the first landing in the FIXED-POINT order; ⊥ ⋖ ε₀ is false and is not claimed
-- Reading: ε₀ is the minimum step next to the pole, never the pole: "next to" in the fixed-point order
-- above, the pole ⊥ = 0 = ∞ a chart claim (`ZeroParadox/BottomCannotBe.lean` § INVERSION), "never"
-- `epsilon0_ne_bot` (§ I). Scopes: `ZeroParadox/Ordinal/Epsilon0CannotBe.md`.

/-! ### § IV. ε₀ as the snap threshold ⊥ of `Ordinal` → ε₀, co-witnessed with the 2-adic limit and the machine snap -/
#check @ZeroParadox.epsilonZero_fixedPoint    -- Statement: ω ^ ε₀ = ε₀ (the `epsilonZero` spelling). Reading: the fixed point the snap lands the ascent on
#check @ZeroParadox.snap_exactly_at_epsilon_zero
#check @ZeroParadox.c1_epsilon_zero_identification
#check @ZeroParadox.zpm_triangle              -- Statement: tower stages < ε₀ ∧ the threshold map sends ε₀ to c₁ ∧ the images tend to ℤ_[2]'s 0 ∧ `snapEmbed` sends that c₁ to ℤ_[2]'s 0 (NB no computational conjunct)
#check @ZeroParadox.both_fixed_points_exist   -- Statement: some code `c` has `eval c n = eval c (encode c + n)` for all `n` ∧ a least ordinal fixed by ω^· exists. The first conjunct is trivially inhabited (example below). A conjunction, not a cross-domain identity
-- Statement: `Code.zero` meets the first conjunct with period 0, since `encode Code.zero = 0`.
example : ∃ c : Nat.Partrec.Code, ∀ n, c.eval n = c.eval (Encodable.encode c + n) :=
  ⟨Nat.Partrec.Code.zero, fun n => by simp [Encodable.encode, Nat.Partrec.Code.encodeCode]⟩

/-! ### § V. The 2-adic realization (along the tower: valuation order agrees, norm order reverses from stage 1; ε₀ ≠ 0 preserved, no identity) -/
#check @ZeroParadox.snap_arc_z2_loop          -- Statement: the images start at ℤ_[2]'s 0, are ≠ 0 for every stage n ≥ 1, and tend to that 0 (the loop)
#check @ZeroParadox.mu_construction_correspondence  -- Statement: one tower, two carrier closures: ε₀ in `Ordinal`, ℤ_[2]'s 0 as the images' limit
#check @ZeroParadox.cnf_bridge_type_boundary  -- Statement: ε₀ is the least fixed point at or above ⊥ of `Ordinal` ∧ the images tend to ℤ_[2]'s 0 ∧ each stage's `repr` is its tower stage. Reading: a co-witness; ε₀ = 0 with 0 of ℤ_[2] fails to elaborate, `Ordinal` vs `ℤ_[2]`
#check @ZeroParadox.tower_orders_agree        -- Statement: on the tower stages, ordinal `<` iff `<` on the 2-adic valuations of the images; at the seed this rests on Mathlib's `valuation 0 = 0`
-- Statement: DRIFT. Read by the norm, the order reverses only from stage 1 on: at the seed the norm
-- rises from 0 (first example), and for 1 ≤ m < n it falls (second example).
example : ‖ZeroParadox.cnfToZp2 (ZeroParadox.towerNONote 0)‖ <
    ‖ZeroParadox.cnfToZp2 (ZeroParadox.towerNONote 1)‖ := by
  rw [ZeroParadox.snap_arc_z2_loop.1, norm_zero]
  exact norm_pos_iff.2 (ZeroParadox.snap_arc_z2_loop.2.1 1 le_rfl)
example (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    ‖ZeroParadox.cnfToZp2 (ZeroParadox.towerNONote n)‖ <
      ‖ZeroParadox.cnfToZp2 (ZeroParadox.towerNONote m)‖ := by
  rw [PadicInt.norm_eq_zpow_neg_valuation (ZeroParadox.snap_arc_z2_loop.2.1 n (hm.trans hmn.le)),
    PadicInt.norm_eq_zpow_neg_valuation (ZeroParadox.snap_arc_z2_loop.2.1 m hm),
    ZeroParadox.cnfToZp2_tower_valuation, ZeroParadox.cnfToZp2_tower_valuation]
  exact zpow_lt_zpow_right₀ (by norm_num) (by omega)

/-! ### § VI. The loop returns to a ⊥, never to ε₀ (the *successor* reading is a commitment) -/
#check @ZeroParadox.t_iz_limit_is_new_null    -- Statement: role half only, in any `ZPSemilattice`: (∀ x, join terminal x = x) → terminal = bot. No chain, no limit, no novelty in the statement; "a fresh instance" is the framework's reading, not this theorem

/-! ### § VII. ε₀ as a WIDTH, not a value — the order type and the count of a cell of seeds -/
-- Statement: in the lines below ε₀ occurs only as a LANDING (the least fixed point a seed reaches)
-- and as an ORDER TYPE (a width). None of them places ε₀ at the floor of any carrier; § I stands.
#check @ZeroParadox.first_cell_eq_Iic          -- Statement: the seeds `α` with `nfp (ω^·) α = ε₀` are exactly `Set.Iic ε₀`
#check @ZeroParadox.successor_cell_width       -- Statement: the seeds strictly between `ε_o` and `ε_(o+1)` have order type `ε_(o+1)`, lifted one universe. That the seeds strictly below ε₀ have order type ε₀ is Mathlib's `Ordinal.type_lt_Iio`, true of every ordinal
-- Statement: control, the cell strictly between ε₀ and ε₁ has width ε₁, not ε₀.
open Ordinal in
example : typeLT (Set.Ioo (Ordinal.epsilon 0 : Ordinal.{0}) (Ordinal.epsilon 1)) ≠
    Ordinal.lift.{1, 0} (Ordinal.epsilon 0) := by
  have h := ZeroParadox.successor_cell_width (0 : Ordinal.{0})
  rw [Order.succ_eq_add_one, zero_add] at h
  rw [h, Ne, Ordinal.lift_inj]
  exact (Ordinal.veblen_right_strictMono 1 zero_lt_one).ne'
#check @ZeroParadox.card_epsilon0              -- Statement: COUNTING chart, `ε₀.card = ℵ₀`. A cell indexed past the countable ordinals is not countable (the control in `ZeroParadox/Ordinal/Epsilon0LeastFP.lean`)
#check @ZeroParadox.repr_surj_below_epsilon0   -- Statement: every ordinal below ε₀ is denoted by a normal-form `ONote`, a finite term; ε₀ is denoted by none (`repr_lt_epsilon0`, § I-b)
-- Reading: CARRIER, two charts of one cell, neither denied. Order type: the first cell's seeds below
-- its landing are as wide as ε₀, and each successor cell is as wide as its own landing. Count: the
-- first cell is countable, and each of its addresses is a finite term.

end Epsilon0CannotBeIndex
