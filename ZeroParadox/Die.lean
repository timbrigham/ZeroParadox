import Mathlib.Order.Cover
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Relation
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The die: an order-free motion, its switches, and its premises

## Engineer's Take

The die is the outline of the class that everything should be adhering to. The entire shape of
up and over is what gave rise to the premise of the die to start with. It's the motion that it
represents, the literal up and over. I don't know if that's going to be the exact shape of what
we're representing or an instance of it. Something has to exist inside of the die's parameters,
and there is no necessity that it has to actually be used within a specific context. I could see
one leg or the other not being visible from a given point of view, existing but not usable.
Nothing in this initial set of values should be considered binding. It's just a starting place,
and these forms are meant to be adaptable as we learn.

---

## Formal Overview (AI-assisted)
Meta objects only; imports no face file. The premises are a starting place, in three shapes:
existence, "for all", and "at most one". They are indexed in `ZeroParadox/DieCannotBe.lean`.
-/

namespace ZeroParadox

universe u

/-! ### § I. The motion -/

/-- `Statement:` a partial self-map `up` whose every value is a fixed point of `up`, and a
    relation `step`. `Reading:` UP is `up`, OVER is `step`; a landing is a fixed point of `up`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: pairs an idempotent partial map (Mathlib `PFun`) with a
-- step relation; Mathlib has each part, not the pair.
structure Motion (α : Type u) where
  /-- The UP leg, a partial map; total or partial is the switch of § II. -/
  up : α →. α
  /-- Idempotence in partial form: every value of `up` is a landing. -/
  up_idem : ∀ x y, y ∈ up x → y ∈ up y
  /-- The OVER leg, any relation. -/
  step : α → α → Prop

/-! NO-GO gauge — `Motion` is trivially inhabited: every type carries one (identity UP, empty step;
`ZeroParadox/DieCannotBe.lean` § 0). It is a record; the premises below carry the content. -/

namespace Motion

variable {α : Type u} (M : Motion α)

/-- `Statement:` `y` is a landing: `up` is defined at `y` and returns `y`. -/
def IsLanding (y : α) : Prop := y ∈ M.up y

/-- `Statement:` a total idempotent map and a relation give a motion. -/
def ofTotal (f : α → α) (hf : ∀ x, f (f x) = f x) (s : α → α → Prop) : Motion α where
  up x := Part.some (f x)
  up_idem x y h := by
    rw [Part.mem_some_iff] at h ⊢
    subst h
    exact (hf x).symm
  step := s

/-! ### § II. The switches -/

/-- `Statement:` the UP switch at `total`: `up` is defined everywhere. -/
def UpTotal : Prop := ∀ x, (M.up x).Dom

/-- `Statement:` climb: from a landing `y`, a step to `b`, and `up b` is neither `b` nor `y`. -/
def Climb : Prop := ∃ y b z, M.IsLanding y ∧ M.step y b ∧ z ∈ M.up b ∧ z ≠ b ∧ z ≠ y

/-- `Statement:` loop: from a landing `y`, a step to some `b ≠ y`, and `up b` returns to `y`. -/
def Loop : Prop := ∃ y b, M.IsLanding y ∧ M.step y b ∧ b ≠ y ∧ y ∈ M.up b

/-! ### § III. Premises on a motion -/

/-- `Statement:` some point is a landing. -/
def HasLanding : Prop := ∃ y, M.IsLanding y

/-- `Statement:` OVER exists from some landing. -/
def OverAtLanding : Prop := ∃ y b, M.IsLanding y ∧ M.step y b

/-- `Statement:` the corner: from a landing, a step to `b`, and `up b` is a point other than `b`. -/
def Corner : Prop := ∃ y b z, M.IsLanding y ∧ M.step y b ∧ z ∈ M.up b ∧ z ≠ b

/-- `Statement:` from a landing, a step to a point where `up` is undefined. -/
def OverToUndefined : Prop := ∃ y b, M.IsLanding y ∧ M.step y b ∧ ¬ (M.up b).Dom

/-- `Statement:` `ofTotal` is total. -/
theorem ofTotal_upTotal (f : α → α) (hf : ∀ x, f (f x) = f x) (s : α → α → Prop) :
    (ofTotal f hf s).UpTotal := fun _ => trivial

/-- `Statement:` a total motion has no step into a point where `up` is undefined. -/
theorem not_overToUndefined_of_upTotal (h : M.UpTotal) : ¬ M.OverToUndefined :=
  fun ⟨_, b, _, _, hb⟩ => hb (h b)

/-- `Statement:` a climb is a corner. -/
theorem climb_corner : M.Climb → M.Corner :=
  fun ⟨y, b, z, hy, hs, hz, hzb, _⟩ => ⟨y, b, z, hy, hs, hz, hzb⟩

/-- `Statement:` a loop is a corner. -/
theorem loop_corner : M.Loop → M.Corner :=
  fun ⟨y, b, hy, hs, hby, hyb⟩ => ⟨y, b, y, hy, hs, hyb, Ne.symm hby⟩

/-- `Statement:` a corner gives OVER at a landing. -/
theorem corner_overAtLanding : M.Corner → M.OverAtLanding :=
  fun ⟨y, b, _, hy, hs, _, _⟩ => ⟨y, b, hy, hs⟩

/-- `Statement:` a corner's step leaves its landing. -/
theorem corner_step_moves : M.Corner → ∃ y b, M.step y b ∧ b ≠ y :=
  fun ⟨y, b, _, hy, hs, hz, hzb⟩ =>
    ⟨y, b, hs, fun hb => hzb (by rw [hb] at hz ⊢; exact Part.mem_unique hz hy)⟩

/-- `Statement:` a climb gives three pairwise distinct points. -/
theorem climb_three : M.Climb → ∃ y b z : α, y ≠ b ∧ b ≠ z ∧ z ≠ y :=
  fun ⟨y, b, z, hy, _, hz, hzb, hzy⟩ =>
    ⟨y, b, z, fun hyb => hzy (by rw [← hyb] at hz; exact Part.mem_unique hz hy),
      Ne.symm hzb, hzy⟩

end Motion

/-! ### § IV. The smallest step, derived -/

/-- `Statement:` the reachability preorder of a relation: `a ≤ b` iff `b` is reachable from `a`
    in zero or more steps (`Relation.ReflTransGen`). -/
@[reducible] def reachPreorder {α : Type u} (R : α → α → Prop) : Preorder α where
  le := Relation.ReflTransGen R
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

/-- `Statement:` if `b` is the only `R`-successor of `y` and `b` does not reach `y`, then
    `y ⋖ b` in the reachability preorder. One way: the index records the converse's non-member. -/
theorem unique_succ_covBy {α : Type u} (R : α → α → Prop) {y b : α} (hR : R y b)
    (huniq : ∀ c, R y c → c = b) (hback : ¬ Relation.ReflTransGen R b y) :
    @CovBy α (reachPreorder R).toLT y b := by
  letI := reachPreorder R
  -- the head case of `ReflTransGen`, by induction: Mathlib's `cases_head` carries choice
  have head : ∀ {c}, Relation.ReflTransGen R y c →
      c = y ∨ ∃ d, R y d ∧ Relation.ReflTransGen R d c := by
    intro c h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hbc ih =>
      rcases ih with h | ⟨d, hd, hdb⟩
      · exact Or.inr ⟨_, h ▸ hbc, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨d, hd, hdb.tail hbc⟩
  refine ⟨⟨Relation.ReflTransGen.single hR, hback⟩, fun c hyc hcb => ?_⟩
  rcases head hyc.1 with h | ⟨d, hd, hdc⟩
  · exact hyc.2 (h ▸ Relation.ReflTransGen.refl)
  · exact hcb.2 (huniq d hd ▸ hdc)

/-! ### § V. Order premises -/

section OrderPremises

variable (α : Type u) [PartialOrder α] [OrderBot α]

/-- `Statement:` ⊥ of `α` has a cover. -/
def BotCovered : Prop := ∃ a : α, ⊥ ⋖ a

/-- `Statement:` some `a` above ⊥ of `α` has `[⊥, a] = {⊥, a}`. -/
def BotIntervalTwo : Prop := ∃ a : α, ⊥ < a ∧ ∀ c, c ≤ a → c = ⊥ ∨ c = a

/-- `Statement:` every non-maximal point of `α` has a cover. -/
def EveryStepCovered : Prop := ∀ x : α, ¬ IsMax x → ∃ b, x ⋖ b

/-- `Statement:` ⊥ of `α` has at most one cover. -/
def UniqueBotCover : Prop := ∀ a b : α, ⊥ ⋖ a → ⊥ ⋖ b → a = b

variable {α}

/-- `Statement:` a two-point first interval gives a cover of ⊥ of `α`. -/
theorem botIntervalTwo_botCovered : BotIntervalTwo α → BotCovered α :=
  fun ⟨a, h, h2⟩ => ⟨a, covBy_of_eq_or_eq h fun c _ => h2 c⟩

-- The `DecidableEq` binder is kept in the type on purpose: `botCovered_botIntervalTwo_classical`
-- below is the same direction without it, and the PurityCheck prints both footprints.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, a cover of ⊥ of `α` gives a two-point first interval. -/
theorem botCovered_botIntervalTwo [DecidableEq α] : BotCovered α → BotIntervalTwo α :=
  fun ⟨a, h⟩ => ⟨a, h.lt, fun c hc =>
    if hca : c = a then Or.inr hca else
      if hcb : c = ⊥ then Or.inl hcb else
        absurd (lt_of_le_of_ne hc hca) (h.2 (lt_of_le_of_ne bot_le (Ne.symm hcb)))⟩

/-- `Statement:` the same direction with no `DecidableEq` binder, proved with `classical`. -/
theorem botCovered_botIntervalTwo_classical : BotCovered α → BotIntervalTwo α := by
  classical
  exact botCovered_botIntervalTwo

/-- `Statement:` a cover at every non-maximal point, and a point other than ⊥ of `α`, give a cover
    of ⊥ of `α`. -/
theorem everyStepCovered_botCovered (h : EveryStepCovered α) (hne : ∃ a : α, a ≠ ⊥) :
    BotCovered α :=
  let ⟨_, ha⟩ := hne
  h ⊥ fun hm => ha (le_bot_iff.mp (hm bot_le))

end OrderPremises

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms Motion
#print axioms Motion.IsLanding
#print axioms Motion.UpTotal
#print axioms Motion.Climb
#print axioms Motion.Loop
#print axioms Motion.HasLanding
#print axioms Motion.OverAtLanding
#print axioms Motion.Corner
#print axioms Motion.OverToUndefined
#print axioms reachPreorder
#print axioms BotCovered
#print axioms BotIntervalTwo
#print axioms EveryStepCovered
#print axioms UniqueBotCover
#print axioms Motion.ofTotal
#print axioms Motion.ofTotal_upTotal
#print axioms Motion.not_overToUndefined_of_upTotal
#print axioms Motion.climb_corner
#print axioms Motion.loop_corner
#print axioms Motion.corner_overAtLanding
#print axioms Motion.corner_step_moves
#print axioms Motion.climb_three
#print axioms unique_succ_covBy
#print axioms botIntervalTwo_botCovered
#print axioms botCovered_botIntervalTwo
#print axioms botCovered_botIntervalTwo_classical
#print axioms everyStepCovered_botCovered

end PurityCheck
