import Mathlib.Order.Cover
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Relation
import Mathlib.Computability.Partrec
import Mathlib.Data.ENat.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteSublattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Atoms.Finite
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

The die has evolved, and it is on version two now. I think what we are describing with the die is the uniform shape of what makes a wall a wall and a floor a floor throughout the rest of the corpus. I have a fundamental belief that bottom is equal to zero and infinity at the same time. If we can make the claim about bottom at the end, and bottom at n and n plus one, that sure sounds to me like we can pick the way that we are viewing the object.

---

## Formal Overview (AI-assisted)
Version 2; the index `ZeroParadox/DieCannotBe.lean` numbers its sections differently. Here: MOTION (§ I–IV;
no order); VIEWS (§ XII, § XIV–XV; an order as data); CELLS (§ IX–XI, § XVI; arrival, fan-in); TRAP SETS
(§ XII–XIII, § XVI); the DATUM behind a cell (§ V–VIII, § XIII); MAPS, ORDERS, QUOTIENTS (§ XIII, XVII–XIX).
-/

namespace ZeroParadox

universe u

/-! ### § I. The motion -/

/-- `Statement:` a partial self-map `up` whose every value is a fixed point of `up`, and a
    relation `step`. `Reading:` UP is `up`, OVER is `step`; a landing is a fixed point of `up`. UP
    is an idempotent of the monoid of partial endofunctions (Cockett and Hofstra, APAL 156 (2008),
    p. 187, Example (iii)), inside Par; it need not be a restriction idempotent (`f = f̄`, Cockett
    and Lack, TCS 270 (2002), p. 227), which in Par are the partial identities (Cockett and
    Hofstra, p. 186): the identity UP is one, the `Bool` control below is not. -/
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

-- Statement: the `up_idem` field is idempotence under `PFun.comp`.
example {α : Type u} (u : α →. α) : (∀ x y, y ∈ u x → y ∈ u y) ↔ u.comp u = u := by
  constructor
  · intro h
    funext x
    apply Part.ext
    intro y
    rw [PFun.comp_apply, Part.mem_bind_iff]
    exact ⟨fun ⟨z, hz, hyz⟩ => (Part.mem_unique (h x z hz) hyz) ▸ hz,
      fun hy => ⟨y, hy, h x y hy⟩⟩
  · intro h x y hy
    have hy' : y ∈ (u.comp u) x := by rw [congrFun h x]; exact hy
    rw [PFun.comp_apply, Part.mem_bind_iff] at hy'
    obtain ⟨z, hz, hyz⟩ := hy'
    exact Part.mem_unique hz hy ▸ hyz

-- Statement: the identity UP, `x ↦ Part.some x`, is a partial identity: every value equals its argument.
example {α : Type u} : ∀ x y : α, y ∈ (Part.some x) → y = x := fun _ _ h => Part.mem_some_iff.1 h

-- Statement: control: the constant map `true` on `Bool` meets `up_idem` and is not a partial
-- identity (some value differs from its argument).
example : (∀ x y, y ∈ (fun _ : Bool => Part.some true) x → y ∈ (fun _ : Bool => Part.some true) y) ∧
    ¬ ∀ x y, y ∈ (fun _ : Bool => Part.some true) x → y = x :=
  ⟨fun _ _ h => (Part.mem_some_iff.1 h) ▸ Part.mem_some true,
    fun h => absurd (h false true (Part.mem_some true)) (by decide)⟩

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

/-- `Statement:` the corner, over-then-up: a landing steps to `b`, and `up b` is a point `≠ b`. -/
def Corner : Prop := ∃ y b z, M.IsLanding y ∧ M.step y b ∧ z ∈ M.up b ∧ z ≠ b

/-- `Statement:` the elbow, up-then-over: `up` sends `x` to a point `y ≠ x`, and `y` steps. -/
def Elbow : Prop := ∃ x y b, y ∈ M.up x ∧ y ≠ x ∧ M.step y b

/-- `Statement:` from a landing, a step to a point where `up` is undefined. -/
def OverToUndefined : Prop := ∃ y b, M.IsLanding y ∧ M.step y b ∧ ¬ (M.up b).Dom

/-- `Statement:` `ofTotal` is total. -/
theorem ofTotal_upTotal (f : α → α) (hf : ∀ x, f (f x) = f x) (s : α → α → Prop) :
    (ofTotal f hf s).UpTotal := fun _ => trivial

/-- `Statement:` a total motion has no step into a point where `up` is undefined. -/
theorem not_overToUndefined_of_upTotal (h : M.UpTotal) : ¬ M.OverToUndefined :=
  fun ⟨_, b, _, _, hb⟩ => hb (h b)

/-- `Statement:` if the motion climbs, its corner fires; one way, the converse refuted on `Bool`
    (`ZeroParadox/DieCannotBe.lean` § I: a `Bool` motion whose corner fires and which does not climb). -/
theorem climb_corner : M.Climb → M.Corner :=
  fun ⟨y, b, z, hy, hs, hz, hzb, _⟩ => ⟨y, b, z, hy, hs, hz, hzb⟩

/-- `Statement:` if the motion loops, its corner fires; one way, the converse refuted by
    `ordinalSuccMotion` (`ZeroParadox/DieCannotBe.lean` § XV: a climb, hence a corner, and no loop). -/
theorem loop_corner : M.Loop → M.Corner :=
  fun ⟨y, b, hy, hs, hby, hyb⟩ => ⟨y, b, y, hy, hs, hyb, Ne.symm hby⟩

/-- `Statement:` the corner fires iff a landing `y` steps to some `b` that is not a landing and
    `up b` is defined; both directions. `Reading:` the corner is a crossing of the joint: OVER
    leaves the set of landings and UP sends `b` to a landing (`up_idem`), `y` itself in a loop and
    another landing in a climb. -/
theorem corner_iff_crossing :
    M.Corner ↔ ∃ y b z, M.IsLanding y ∧ M.step y b ∧ ¬ M.IsLanding b ∧ z ∈ M.up b := by
  constructor
  · rintro ⟨y, b, z, hy, hs, hz, hzb⟩
    exact ⟨y, b, z, hy, hs, fun hb => hzb (Part.mem_unique hz hb), hz⟩
  · rintro ⟨y, b, z, hy, hs, hb, hz⟩
    exact ⟨y, b, z, hy, hs, hz, fun e => hb (e ▸ M.up_idem b z hz)⟩

-- The `DecidableEq` binder is kept in the type on purpose: `corner_iff_loop_or_climb_classical`
-- below is the same statement without it, and the PurityCheck prints both footprints.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, the corner fires iff the motion loops or climbs; both
    directions. The two are not exclusive (`ZeroParadox/DieCannotBe.lean` § I, the `Fin 4` example). -/
theorem corner_iff_loop_or_climb [DecidableEq α] : M.Corner ↔ M.Loop ∨ M.Climb := by
  refine ⟨fun ⟨y, b, z, hy, hs, hz, hzb⟩ => ?_, fun h => h.elim M.loop_corner M.climb_corner⟩
  by_cases hzy : z = y
  · subst hzy
    exact Or.inl ⟨z, b, hy, hs, fun e => hzb e.symm, hz⟩
  · exact Or.inr ⟨y, b, z, hy, hs, hz, hzb, hzy⟩

/-- `Statement:` the same with no `DecidableEq` binder, proved with `classical`. -/
theorem corner_iff_loop_or_climb_classical : M.Corner ↔ M.Loop ∨ M.Climb := by
  classical
  exact M.corner_iff_loop_or_climb

/-- `Statement:` if, on every motion on every `β : Type`, a corner gives a loop or a climb, excluded
    middle holds; one way. The reduction runs on `Option Prop`: UP the identity on `some _` and
    `none ↦ some p`, one step `some True → none`; a loop there gives `p`, a climb gives `¬ p`. -/
theorem em_of_corner_loop_or_climb
    (H : ∀ (β : Type) (M : Motion β), M.Corner → M.Loop ∨ M.Climb) : ∀ p : Prop, p ∨ ¬ p := by
  intro p
  let u : Option Prop → Part (Option Prop) := fun x => match x with
    | none => Part.some (some p)
    | some q => Part.some (some q)
  have hu : ∀ x y, y ∈ u x → y ∈ u y := by
    intro x y h
    cases x with
    | none => rw [Part.mem_some_iff.1 h]; exact Part.mem_some _
    | some q => rw [Part.mem_some_iff.1 h]; exact Part.mem_some _
  let N : Motion (Option Prop) := ⟨u, hu, fun a b => a = some True ∧ b = none⟩
  have hc : N.Corner := ⟨some True, none, some p, Part.mem_some _, ⟨rfl, rfl⟩, Part.mem_some _,
    fun h => by cases h⟩
  rcases H _ N hc with ⟨y, b, _, ⟨rfl, rfl⟩, _, hyb⟩ | ⟨y, b, z, _, ⟨rfl, rfl⟩, hz, _, hzy⟩
  · have e : some True = some p := Part.mem_some_iff.1 hyb
    exact Or.inl ((Option.some_inj.1 e) ▸ trivial)
  · have e : z = some p := Part.mem_some_iff.1 hz
    subst e
    exact Or.inr fun hp => hzy (by rw [eq_true hp])

/-- `Statement:` with no binder, if the corner fires, it is not the case that the motion neither
    loops nor climbs. -/
theorem not_not_loop_or_climb_of_corner (h : M.Corner) : ¬¬ (M.Loop ∨ M.Climb) := by
  obtain ⟨y, b, z, hy, hs, hz, hzb⟩ := h
  intro hn
  refine hn (Or.inr ⟨y, b, z, hy, hs, hz, hzb, fun hzy => hn (Or.inl ?_)⟩)
  subst hzy
  exact ⟨z, b, hy, hs, fun e => hzb e.symm, hz⟩

/-- `Statement:` if the corner fires, OVER exists from some landing; one way. -/
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

/-- `Statement:` a run OVER, UP, OVER (a landing `y` steps to `b`, `up b = z ≠ b`, `z` steps to `c`)
    gives a corner and an elbow. -/
theorem corner_elbow_of_over_up_over {y b z c : α} (hy : M.IsLanding y) (hs : M.step y b)
    (hz : z ∈ M.up b) (hzb : z ≠ b) (hc : M.step z c) : M.Corner ∧ M.Elbow :=
  ⟨⟨y, b, z, hy, hs, hz, hzb⟩, ⟨b, z, c, hz, hzb, hc⟩⟩

/-- `Statement:` a run UP, OVER, UP (`up x = y ≠ x`, `y` steps to `b`, `up b = z ≠ b`) gives a
    corner and an elbow; `y` is a landing by `up_idem`. -/
theorem corner_elbow_of_up_over_up {x y b z : α} (hy : y ∈ M.up x) (hyx : y ≠ x)
    (hs : M.step y b) (hz : z ∈ M.up b) (hzb : z ≠ b) : M.Corner ∧ M.Elbow :=
  ⟨⟨y, b, z, M.up_idem x y hy, hs, hz, hzb⟩, ⟨x, y, b, hy, hyx, hs⟩⟩

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

/-- `Statement:` if some first interval of `α` has two points, ⊥ of `α` has a cover; the converse is
    `botCovered_botIntervalTwo`, given `DecidableEq α`. -/
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

/-- `Statement:` if a cover of ⊥ gives a two-point first interval in every partial order with a
    least element on a `Type`, weak excluded middle holds; the reduction runs at `Prop`, below the
    witness `a`, at `p ∧ a`. -/
theorem wem_of_botCovered_botIntervalTwo
    (h : ∀ (β : Type) [PartialOrder β] [OrderBot β], BotCovered β → BotIntervalTwo β) :
    ∀ p : Prop, ¬ p ∨ ¬ ¬ p := by
  intro p
  have hcov : BotCovered Prop :=
    ⟨True, ⟨⟨fun h => h.elim, fun h => h trivial⟩, fun c h1 h2 => h1.2 fun hc => h2.2 fun _ => hc⟩⟩
  obtain ⟨a, hlt, h2⟩ := h Prop hcov
  rcases h2 (p ∧ a) (fun h => h.2) with e | e
  · exact Or.inl fun hp => hlt.2 fun ha => by
      have hpa : p ∧ a := ⟨hp, ha⟩
      rw [e] at hpa
      exact hpa
  · exact Or.inr fun hnp => hlt.2 fun ha => by
      have hpa : p ∧ a := by rw [e]; exact ha
      exact hnp hpa.1

/-- `Statement:` if every non-maximal point of `α` has a cover and some point is not ⊥ of `α`, then
    ⊥ of `α` has a cover; one way. -/
theorem everyStepCovered_botCovered (h : EveryStepCovered α) (hne : ∃ a : α, a ≠ ⊥) :
    BotCovered α :=
  let ⟨_, ha⟩ := hne
  h ⊥ fun hm => ha (le_bot_iff.mp (hm bot_le))

omit [OrderBot α] in
/-- `Statement:` if `α` is finite, every non-maximal point of `α` has a cover; through Mathlib's
    `IsStronglyAtomic` instance for a finite partial order (`Mathlib/Order/Atoms/Finite.lean`). -/
theorem everyStepCovered_of_finite [Finite α] : EveryStepCovered α := fun x hx => by
  obtain ⟨b, hb⟩ := not_isMax_iff.1 hx
  obtain ⟨c, hc, -⟩ := exists_covBy_le_of_lt hb
  exact ⟨c, hc⟩

/-- `Statement:` if `α` is finite and some point is not ⊥ of `α`, then ⊥ of `α` has a cover; one way. -/
theorem botCovered_of_finite [Finite α] (hne : ∃ a : α, a ≠ ⊥) : BotCovered α :=
  everyStepCovered_botCovered everyStepCovered_of_finite hne

end OrderPremises

/-! ### § VI. Stages and their shared closure -/

namespace Motion

variable {α : Type u} (M : Motion α)

/-- `Statement:` UP is unchanged along a step: `step a b` gives `up a = up b`. -/
def UpStepInvariant : Prop := ∀ a b, M.step a b → M.up a = M.up b

/-- `Statement:` `s` is a run: each stage steps to the next. -/
def IsRun (s : ℕ → α) : Prop := ∀ n, M.step (s n) (s (n + 1))

/-- `Statement:` the stage/closure shape: no point of `S` is a landing, and UP sends every point of
    `S` to the one value `c`, which may be undefined. -/
def StageClosure (S : Set α) (c : Part α) : Prop :=
  ∀ s ∈ S, ¬ M.IsLanding s ∧ M.up s = c

variable {M}

/-- `Statement:` with UP unchanged along steps, UP is constant along a run. -/
theorem up_run_const (h : M.UpStepInvariant) {s : ℕ → α} (hs : M.IsRun s) (n : ℕ) :
    M.up (s n) = M.up (s 0) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (h _ _ (hs n)).symm.trans ih

/-- `Statement:` with UP unchanged along steps, a run with no landing among its stages has the
    stage/closure shape, with closure `up (s 0)`. -/
theorem stageClosure_of_run (h : M.UpStepInvariant) {s : ℕ → α} (hs : M.IsRun s)
    (hint : ∀ n, ¬ M.IsLanding (s n)) : M.StageClosure (Set.range s) (M.up (s 0)) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨hint n, up_run_const h hs n⟩

/-- `Statement:` over a nonempty stage set, a defined closure is a landing. -/
theorem StageClosure.isLanding_of_mem {S : Set α} {c : Part α} (h : M.StageClosure S c)
    (hne : S.Nonempty) {y : α} (hy : y ∈ c) : M.IsLanding y := by
  obtain ⟨s, hs⟩ := hne
  have hys : y ∈ M.up s := (h s hs).2 ▸ hy
  exact M.up_idem s y hys

/-- `Statement:` over a nonempty stage set, a defined closure is not one of the stages. -/
theorem StageClosure.not_mem_of_mem {S : Set α} {c : Part α} (h : M.StageClosure S c)
    (hne : S.Nonempty) {y : α} (hy : y ∈ c) : y ∉ S :=
  fun hyS => (h y hyS).1 (h.isLanding_of_mem hne hy)

/-- `Statement:` a nonempty stage set has at most one closure. -/
theorem StageClosure.unique {S : Set α} {c d : Part α} (h₁ : M.StageClosure S c)
    (h₂ : M.StageClosure S d) (hne : S.Nonempty) : c = d := by
  obtain ⟨s, hs⟩ := hne
  exact (h₁ s hs).2.symm.trans (h₂ s hs).2

variable (M)

/-- `Statement:` every run with no landing among its stages closes at `up` of its first stage. -/
def RunsClose : Prop :=
  ∀ s : ℕ → α, M.IsRun s → (∀ n, ¬ M.IsLanding (s n)) → M.StageClosure (Set.range s) (M.up (s 0))

/-- `Statement:` the run form of the shape: `s` is a run, and its stages close at `c`. -/
def RunClosure (s : ℕ → α) (c : Part α) : Prop := M.IsRun s ∧ M.StageClosure (Set.range s) c

variable {M}

/-- `Statement:` UP unchanged along steps gives `RunsClose`; one way. -/
theorem runsClose_of_upStepInvariant (h : M.UpStepInvariant) : M.RunsClose :=
  fun _ hs hint => stageClosure_of_run h hs hint

/-- `Statement:` the run form gives the set form on the run's range; one way. -/
theorem RunClosure.stageClosure {s : ℕ → α} {c : Part α} (h : M.RunClosure s c) :
    M.StageClosure (Set.range s) c := h.2

/-- `Statement:` if no stage of `s` is a landing and `up (s n) ≠ up (s 0)` for some `n`, the carrier
    has three pairwise distinct points: `s n`, `s 0`, and a value of UP at one of them. -/
theorem three_of_not_runClose {s : ℕ → α} (hint : ∀ n, ¬ M.IsLanding (s n)) {n : ℕ}
    (hne : M.up (s n) ≠ M.up (s 0)) : ∃ a b c : α, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  have hab : s n ≠ s 0 := fun e => hne (e ▸ rfl)
  have nl : ∀ {x y : α}, y ∈ M.up x → ¬ M.IsLanding x → y ≠ x :=
    fun hy hx e => hx (e ▸ M.up_idem _ _ hy)
  by_cases h1 : (M.up (s n)).Dom
  · refine ⟨s n, s 0, (M.up (s n)).get h1, hab, fun e => hint 0 (e ▸ M.up_idem _ _ (Part.get_mem h1)),
      (nl (Part.get_mem h1) (hint n)).symm⟩
  · by_cases h0 : (M.up (s 0)).Dom
    · exact ⟨s n, s 0, (M.up (s 0)).get h0, hab, (nl (Part.get_mem h0) (hint 0)).symm,
        fun e => hint n (e ▸ M.up_idem _ _ (Part.get_mem h0))⟩
    · exact absurd ((Part.eq_none_iff'.2 h1).trans (Part.eq_none_iff'.2 h0).symm) hne

/-- `Statement:` with UP total, the same hypotheses give four pairwise distinct points: `s n`, `s 0`,
    and the two UP values. -/
theorem four_of_not_runClose (ht : M.UpTotal) {s : ℕ → α} (hint : ∀ n, ¬ M.IsLanding (s n))
    {n : ℕ} (hne : M.up (s n) ≠ M.up (s 0)) :
    ∃ a b c d : α, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have hy : (M.up (s n)).get (ht _) ∈ M.up (s n) := Part.get_mem _
  have hz : (M.up (s 0)).get (ht _) ∈ M.up (s 0) := Part.get_mem _
  have hyl := M.up_idem _ _ hy
  have hzl := M.up_idem _ _ hz
  refine ⟨s n, s 0, _, _, fun e => hne (e ▸ rfl), fun e => hint n (e ▸ hyl),
    fun e => hint n (e ▸ hzl), fun e => hint 0 (e ▸ hyl), fun e => hint 0 (e ▸ hzl), fun e => hne ?_⟩
  rw [Part.eq_some_iff.2 hy, Part.eq_some_iff.2 hz, e]

/-! ### § VII. The registration switch: is closure-definedness data? -/

variable (M)

/-- `Statement:` some COMPUTABLE `Bool` test decides, at every point, whether `up` is defined. -/
def RegisteredComputable [Primcodable α] : Prop :=
  ∃ d : α → Bool, Computable d ∧ ∀ a, d a = true ↔ (M.up a).Dom

/-- `Statement:` a decision of whether `up` is defined, at every point, exists as data. -/
def RegisteredDecidable : Prop := Nonempty (∀ a, Decidable (M.up a).Dom)

variable {M}

/-- `Statement:` a motion presented by an `Option`-valued UP, through `Part.ofOption`. -/
def ofOption (u : α → Option α) (hu : ∀ x y, y ∈ u x → y ∈ u y) (s : α → α → Prop) : Motion α where
  up x := Part.ofOption (u x)
  up_idem x y h := by
    rw [Part.mem_ofOption] at h ⊢
    exact hu x y h
  step := s

/-- `Statement:` a total motion has a decision of definedness. -/
theorem registeredDecidable_of_upTotal (h : M.UpTotal) : M.RegisteredDecidable :=
  ⟨fun a => isTrue (h a)⟩

/-- `Statement:` an `Option`-presented motion has a decision of definedness. -/
theorem ofOption_registeredDecidable (u : α → Option α) (hu : ∀ x y, y ∈ u x → y ∈ u y)
    (s : α → α → Prop) : (ofOption u hu s).RegisteredDecidable :=
  ⟨fun a => Part.ofOptionDecidable (u a)⟩

/-- `Statement:` a computable test gives a decision of definedness; one way. -/
theorem registeredDecidable_of_registeredComputable [Primcodable α]
    (h : M.RegisteredComputable) : M.RegisteredDecidable := by
  obtain ⟨d, -, hd⟩ := h
  exact ⟨fun a => decidable_of_iff _ (hd a)⟩

/-- `Statement:` classically every motion has a decision of definedness. -/
theorem registeredDecidable_of_classical : M.RegisteredDecidable := by
  classical
  exact ⟨fun _ => inferInstance⟩

/-- `Statement:` if every motion on every `β : Type` has a decision of definedness, excluded middle
    holds; the reduction runs on `Unit`, with UP defined exactly where `p` holds. -/
theorem em_of_registeredDecidable (h : ∀ (β : Type) (M : Motion β), M.RegisteredDecidable) :
    ∀ p : Prop, p ∨ ¬ p := by
  intro p
  obtain ⟨d⟩ := h Unit ⟨fun _ => Part.mk p (fun _ => ()), fun _ _ hy => hy, fun _ _ => False⟩
  exact match d () with
    | isTrue hp => Or.inl hp
    | isFalse hn => Or.inr hn

/-- `Statement:` a total motion on a `Primcodable` carrier has a computable test. -/
theorem registeredComputable_of_upTotal [Primcodable α] (h : M.UpTotal) :
    M.RegisteredComputable :=
  ⟨fun _ => true, Computable.const true, fun a => ⟨fun _ => h a, fun _ => rfl⟩⟩

/-- `Statement:` an `Option`-presented motion with a computable UP has a computable test. -/
theorem ofOption_registeredComputable [Primcodable α] (u : α → Option α) (hu : ∀ x y, y ∈ u x → y ∈ u y)
    (s : α → α → Prop) (hc : Computable u) : (ofOption u hu s).RegisteredComputable :=
  ⟨fun a => (u a).isSome, Primrec.option_isSome.to_comp.comp hc,
    fun _ => (Part.ofOption_dom _).symm⟩

/-! ### § VIII. The OVER leg's WHICH: selection -/

variable (M)

/-- `Statement:` at every point with a successor, a successor is chosen, as data. -/
def SelectedData : Prop := Nonempty (∀ a, (∃ b, M.step a b) → {b // M.step a b})

/-- `Statement:` one map `f` has `step a (f a)` at every point `a` with a successor. -/
def SelectedTotal : Prop := ∃ f : α → α, ∀ a, (∃ b, M.step a b) → M.step a (f a)

variable {M}

/-- `Statement:` a total selector gives a data selector; one way. -/
theorem selectedData_of_selectedTotal (h : M.SelectedTotal) : M.SelectedData :=
  let ⟨f, hf⟩ := h
  ⟨fun a ha => ⟨f a, hf a ha⟩⟩

/-- `Statement:` a data selector, with a decision at every point of whether a successor exists,
    gives a total selector. -/
theorem selectedTotal_of_selectedData (hd : ∀ a, Decidable (∃ b, M.step a b))
    (h : M.SelectedData) : M.SelectedTotal := by
  obtain ⟨g⟩ := h
  refine ⟨fun a => @dite _ (∃ b, M.step a b) (hd a) (fun ha => (g a ha).1) (fun _ => a),
    fun a ha => ?_⟩
  show M.step a (@dite _ _ (hd a) _ _)
  rw [dif_pos ha]
  exact (g a ha).2

/-- `Statement:` classically every motion has a total selector. -/
theorem selectedTotal_of_classical : M.SelectedTotal := by
  classical
  exact selectedTotal_of_selectedData (fun _ => inferInstance)
    ⟨fun _ ha => ⟨Classical.choose ha, Classical.choose_spec ha⟩⟩

/-- `Statement:` if every motion on every `β : Type` has a data selector, excluded middle holds; the
    reduction runs on `(Bool → Prop) × Bool`, with OVER `(S, _) → (S, b)` when `S b`, at the pair
    `b = true ∨ p`, `b = false ∨ p`. -/
theorem em_of_selectedData (h : ∀ (β : Type) (M : Motion β), M.SelectedData) :
    ∀ p : Prop, p ∨ ¬ p := by
  intro p
  obtain ⟨g⟩ := h _ (ofTotal id (fun _ => rfl)
    (fun x y : (Bool → Prop) × Bool => y.1 = x.1 ∧ x.1 y.2))
  let pick : ∀ S : Bool → Prop, (∃ b, S b) → Bool := fun S hS =>
    (g (S, true) (hS.elim fun b hb => ⟨(S, b), rfl, hb⟩)).1.2
  have spec : ∀ (S : Bool → Prop) (hS : ∃ b, S b), S (pick S hS) := fun S hS =>
    (g (S, true) (hS.elim fun b hb => ⟨(S, b), rfl, hb⟩)).2.2
  have cong : ∀ (X Y : Bool → Prop) hX hY, X = Y → pick X hX = pick Y hY := by
    intro X Y hX hY e; subst e; rfl
  rcases spec (fun b => b = true ∨ p) ⟨true, Or.inl rfl⟩ with h1 | h1
  · rcases spec (fun b => b = false ∨ p) ⟨false, Or.inl rfl⟩ with h2 | h2
    · exact Or.inr fun hp => absurd (h1.symm.trans ((cong _ _ ⟨true, Or.inl rfl⟩
        ⟨false, Or.inl rfl⟩ (funext fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩)).trans
        h2)) (by decide)
    · exact Or.inl h2
  · exact Or.inl h1

/-- `Statement:` if every motion on `ℕ` with a `Bool`-valued step (`step a b ↔ r a b = true`) has a total
    selector, then every `r : ℕ → Bool` takes the value `true` somewhere or is `false` everywhere (the
    limited principle of omniscience); one way. The reduction reads the selector at `0` of the step
    `r a b = r b`. -/
theorem lpo_of_selectedTotal_nat_boolStep
    (h : ∀ r : ℕ → ℕ → Bool, (ofTotal id (fun _ => rfl) (fun a b => r a b = true)).SelectedTotal) :
    ∀ r : ℕ → Bool, (∃ n, r n = true) ∨ ∀ n, r n = false := by
  intro r
  obtain ⟨f, hf⟩ := h (fun _ b => r b)
  cases hr : r (f 0)
  · exact Or.inr fun n => by
      cases hn : r n
      · rfl
      · exact absurd (show r (f 0) = true from hf 0 ⟨n, hn⟩) (by rw [hr]; decide)
  · exact Or.inl ⟨f 0, hr⟩

/-- `Statement:` a step given by a function `f` (`step a b ↔ b = f a`) has the total selector `f`. -/
theorem selectedTotal_of_fun (f : α → α) (h : ∀ a b, M.step a b ↔ b = f a) : M.SelectedTotal :=
  ⟨f, fun a _ => (h a (f a)).2 rfl⟩

/-- `Statement:` a step given by an `Option`-valued `f` (`step a b ↔ f a = some b`) has the total
    selector `a ↦ (f a).getD a`. -/
theorem selectedTotal_of_option (f : α → Option α) (h : ∀ a b, M.step a b ↔ f a = some b) :
    M.SelectedTotal := by
  refine ⟨fun a => (f a).getD a, fun a ⟨b, hb⟩ => ?_⟩
  have hb' := (h a b).1 hb
  rw [h]
  show f a = some ((f a).getD a)
  rw [hb']
  rfl

/-! ### § IX. The OVER leg's WHETHER: what OVER does at a point -/

variable (M)

/-- `Statement:` no step leaves `y`. `Reading:` a normal form (irreducible) in the abstract-reduction-system reading (Waldmann, Automated Reasoning lecture notes (2011), p. 2, citing Baader–Nipkow ch. 2). -/
def NoStepAt (y : α) : Prop := ∀ b, ¬ M.step y b

/-- `Statement:` `y` steps to itself and to nothing else. -/
def SelfOnlyAt (y : α) : Prop := M.step y y ∧ ∀ b, M.step y b → b = y

/-- `Statement:` `y` steps to some point other than `y`. -/
def LeavesAt (y : α) : Prop := ∃ b, M.step y b ∧ b ≠ y

/-- `Statement:` at `y`, no step, or a step to itself only, or a step elsewhere. -/
def OverTrichotomy (y : α) : Prop := M.NoStepAt y ∨ M.SelfOnlyAt y ∨ M.LeavesAt y

variable {M}

-- The `DecidableEq` binder is kept in the type on purpose: the proof cases on `decEq`, and the
-- PurityCheck prints the footprint that binder buys.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, a step given by an `Option`-valued `f` meets the
    trichotomy at every point. -/
theorem overTrichotomy_of_option [DecidableEq α] (f : α → Option α)
    (h : ∀ a b, M.step a b ↔ f a = some b) (y : α) : M.OverTrichotomy y := by
  cases hf : f y with
  | none => exact Or.inl fun b hb => by rw [h, hf] at hb; cases hb
  | some b =>
    rcases decEq b y with hne | heq
    · exact Or.inr (Or.inr ⟨b, (h y b).2 hf, hne⟩)
    · subst heq
      exact Or.inr (Or.inl ⟨(h _ _).2 hf,
        fun c hc => (Option.some_injective _ (hf.symm.trans ((h _ c).1 hc))).symm⟩)

/-- `Statement:` if the trichotomy holds at every point of every motion on `ℕ` with a `Bool`-valued
    step (`step a b ↔ r a b = true`), then every `r : ℕ → Bool` takes the value `true` somewhere or is
    `false` everywhere (the limited principle of omniscience); one way. `Reading:` `ℕ` has decidable
    equality, so what the uniform form costs here is the search over the carrier. -/
theorem lpo_of_trichotomy_nat_boolStep
    (H : ∀ r : ℕ → ℕ → Bool, ∀ y,
      (ofTotal id (fun _ => rfl) (fun a b => r a b = true)).OverTrichotomy y) :
    ∀ r : ℕ → Bool, (∃ n, r n = true) ∨ ∀ n, r n = false := by
  intro r
  rcases H (fun _ b => r b) 0 with h | ⟨hs, _⟩ | ⟨b, hb, _⟩
  · exact Or.inr fun n => by
      cases hn : r n
      · rfl
      · exact absurd hn (h n)
  · exact Or.inl ⟨0, hs⟩
  · exact Or.inl ⟨b, hb⟩

/-- `Statement:` if `y` has at most one successor and steps to itself, `y` steps to itself only; no
    order is used. `Reading:` the order-free trap beside § XII's order traps. -/
theorem selfOnlyAt_of_step_self {y : α} (hu : ∀ b c, M.step y b → M.step y c → b = c) (hy : M.step y y) :
    M.SelfOnlyAt y :=
  ⟨hy, fun b hb => hu b y hb hy⟩

/-- `Statement:` if the corner fires, some landing steps elsewhere; one way. -/
theorem corner_leavesAt (h : M.Corner) : ∃ y, M.IsLanding y ∧ M.LeavesAt y :=
  let ⟨y, b, _, hy, hs, hz, hzb⟩ := h
  ⟨y, hy, b, hs, fun hb => hzb (by rw [hb] at hz ⊢; exact Part.mem_unique hz hy)⟩

/-! ### § X. OVER run backwards: fan-in and reversal -/

variable (M)

/-- `Statement:` `y` has two distinct predecessors. -/
def FanIn (y : α) : Prop := ∃ a b, a ≠ b ∧ M.step a y ∧ M.step b y

/-- `Statement:` the reversed motion: the same UP, and OVER flipped. -/
def reverse : Motion α := ⟨M.up, M.up_idem, flip M.step⟩

variable {M}

/-- `Statement:` reversal leaves UP unchanged. -/
theorem reverse_up : M.reverse.up = M.up := rfl

/-- `Statement:` reversing twice returns the motion. -/
theorem reverse_reverse : M.reverse.reverse = M := rfl

/-- `Statement:` fan-in at `y` is two distinct successors of `y` in the reversed motion. -/
theorem fanIn_iff_reverse (y : α) :
    M.FanIn y ↔ ∃ a b, a ≠ b ∧ M.reverse.step y a ∧ M.reverse.step y b := Iff.rfl

/-- `Statement:` a step given by a one-to-one function has no fan-in. -/
theorem not_fanIn_of_injective (f : α → α) (hf : Function.Injective f)
    (h : ∀ a b, M.step a b ↔ b = f a) (y : α) : ¬ M.FanIn y :=
  fun ⟨a, b, hab, ha, hb⟩ => hab (hf (((h a y).1 ha).symm.trans ((h b y).1 hb)))

/-- `Statement:` an involution `σ` with `step a b ↔ step (σ b) (σ a)` maps the points with no
    predecessor (`M.reverse.NoStepAt`) one-to-one onto the points with no successor (`NoStepAt`). -/
theorem bijOn_sources_sinks {σ : α → α} (hσ : Function.Involutive σ)
    (hr : ∀ a b, M.step a b ↔ M.step (σ b) (σ a)) :
    Set.BijOn σ {y | M.reverse.NoStepAt y} {y | M.NoStepAt y} := by
  refine ⟨fun y hy b hb => hy (σ b) ?_, hσ.injective.injOn,
    fun z hz => ⟨σ z, fun a ha => hz (σ a) ?_, hσ z⟩⟩
  · show M.step (σ b) y
    have h := (hr (σ b) y).2
    rw [hσ b] at h
    exact h hb
  · have h := (hr a (σ z)).1 ha
    rw [hσ z] at h
    exact h

/-- `Statement:` if OVER is `<` on a preorder with a least element and no maximal element, no
    involution `σ` has `a < b ↔ σ b < σ a`: ⊥ of `α` is a source and no point is a sink
    (`bijOn_sources_sinks`). Well-foundedness is not assumed. -/
theorem not_exists_involution_reverses_lt [Preorder α] [OrderBot α] [NoMaxOrder α] :
    ¬ ∃ σ : α → α, Function.Involutive σ ∧
      ∀ a b, (ofTotal (id : α → α) (fun _ => rfl) (· < ·)).step a b ↔
        (ofTotal (id : α → α) (fun _ => rfl) (· < ·)).step (σ b) (σ a) := by
  rintro ⟨σ, hσ, hr⟩
  have hb := bijOn_sources_sinks hσ hr
  have src : (ofTotal (id : α → α) (fun _ => rfl) (· < ·)).reverse.NoStepAt (⊥ : α) :=
    fun _ ha => not_lt_bot ha
  obtain ⟨c, hc⟩ := exists_gt (σ ⊥)
  exact hb.mapsTo src c hc

/-- `Statement:` a value `z` of `up` is an `up`-preimage of itself. -/
theorem mem_up_self_of_mem_up {x z : α} (h : z ∈ M.up x) : z ∈ M.up z :=
  M.up_idem x z h

/-! ### § XI. A self-map as input: two encodings, and where the corner fires -/

variable (M) in
/-- `Statement:` a point does not both step to itself only and step elsewhere. -/
theorem not_selfOnlyAt_and_leavesAt (y : α) : ¬ (M.SelfOnlyAt y ∧ M.LeavesAt y) :=
  fun ⟨⟨_, hu⟩, ⟨b, hb, hne⟩⟩ => hne (hu b hb)

/-- `Statement:` if `y` steps to itself, `y` steps to itself only, or steps to itself and elsewhere;
    proved by `by_cases`. -/
theorem selfOnlyAt_or_step_self_and_leavesAt {y : α} (hy : M.step y y) :
    M.SelfOnlyAt y ∨ (M.step y y ∧ M.LeavesAt y) := by
  by_cases h : M.LeavesAt y
  · exact Or.inr ⟨hy, h⟩
  · refine Or.inl ⟨hy, fun b hb => ?_⟩
    by_contra hne
    exact h ⟨b, hb, hne⟩

/-- `Statement:` if `y` has at most one successor, `y` does not both step to itself and step
    elsewhere. -/
theorem not_step_self_and_leavesAt_of_subsingleton {y : α}
    (hu : ∀ b c, M.step y b → M.step y c → b = c) : ¬ (M.step y y ∧ M.LeavesAt y) :=
  fun ⟨hy, hl⟩ => not_selfOnlyAt_and_leavesAt M y ⟨selfOnlyAt_of_step_self hu hy, hl⟩

/-- `Statement:` if `y` steps to itself and steps elsewhere, `y` has two distinct successors. -/
theorem two_successors_of_step_self_and_leavesAt {y : α} (h : M.step y y ∧ M.LeavesAt y) :
    ∃ b c, M.step y b ∧ M.step y c ∧ b ≠ c :=
  let ⟨hp, b, hb, hne⟩ := h
  ⟨y, b, hp, hb, hne.symm⟩

/-- `Statement:` if UP is unchanged along steps, the motion does not climb; one way. -/
theorem not_climb_of_upStepInvariant (h : M.UpStepInvariant) : ¬ M.Climb :=
  fun ⟨y, b, _, hy, hs, hz, _, hzy⟩ => hzy (Part.mem_unique (h y b hs ▸ hz) hy)

/-- `Statement:` the motion of a self-map `g`: UP the identity, OVER the graph of `g`.
    `Reading:` every point is a landing, and OVER carries `g` (encoding 1). -/
def ofFun (g : α → α) : Motion α :=
  ofTotal id (fun _ => rfl) (fun x y => y = g x)

/-- `Statement:` in `ofFun g`, `y` steps to itself only iff `g y = y`; both directions. -/
theorem selfOnlyAt_ofFun_iff (g : α → α) (y : α) : (ofFun g).SelfOnlyAt y ↔ g y = y :=
  ⟨fun h => h.1.symm, fun h => ⟨h.symm, fun _ hb => hb.trans h⟩⟩

/-- `Statement:` in `ofFun g`, `y` steps elsewhere iff `g y ≠ y`; both directions. -/
theorem leavesAt_ofFun_iff (g : α → α) (y : α) : (ofFun g).LeavesAt y ↔ g y ≠ y :=
  ⟨fun ⟨_, hb, hne⟩ h => hne (hb.trans h), fun h => ⟨g y, rfl, h⟩⟩

/-- `Statement:` in `ofFun g` no point both steps to itself and steps elsewhere. -/
theorem not_step_self_and_leavesAt_ofFun (g : α → α) (y : α) :
    ¬ ((ofFun g).step y y ∧ (ofFun g).LeavesAt y) :=
  not_step_self_and_leavesAt_of_subsingleton fun _ _ hb hc => hb.trans hc.symm

/-- `Statement:` in `ofFun Not` every proposition steps elsewhere, since `p ≠ ¬ p`. -/
theorem leavesAt_ofFun_not (p : Prop) : (ofFun Not).LeavesAt p :=
  (leavesAt_ofFun_iff Not p).2 fun h => iff_not_self (iff_of_eq h).symm

/-- `Statement:` UP the partial identity on the fixed points of `g`, OVER the graph of `g`.
    `Reading:` the landings carry `g`'s fixed points (encoding 2). -/
def ofFixedPoints (g : α → α) : Motion α where
  up x := ⟨g x = x, fun _ => x⟩
  up_idem x y h := by
    obtain ⟨hx, rfl⟩ := h
    exact ⟨hx, rfl⟩
  step x y := y = g x

/-- `Statement:` in `ofFixedPoints g`, `y` is a landing iff `g y = y`; both directions. -/
theorem isLanding_ofFixedPoints_iff (g : α → α) (y : α) :
    (ofFixedPoints g).IsLanding y ↔ g y = y :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, rfl⟩⟩

variable (M) in
/-- `Statement:` if OVER is the graph of a function `g` and every landing is a fixed point of `g`,
    the corner does not fire; one way, for any UP. -/
theorem not_corner_of_fun (g : α → α) (hstep : ∀ a b, M.step a b ↔ b = g a)
    (hfix : ∀ y, M.IsLanding y → g y = y) : ¬ M.Corner := by
  rintro ⟨y, b, z, hy, hs, hz, hne⟩
  have hb : b = y := ((hstep y b).1 hs).trans (hfix y hy)
  subst hb
  exact hne (Part.mem_unique hz hy)

/-- `Statement:` the corner of `ofFixedPoints g` does not fire, for every `g`. -/
theorem not_corner_ofFixedPoints (g : α → α) : ¬ (ofFixedPoints g).Corner :=
  not_corner_of_fun _ g (fun _ _ => Iff.rfl) fun y hy => (isLanding_ofFixedPoints_iff g y).1 hy

/-- `Statement:` if `r` is idempotent and `r x = x ↔ g x = x` for every `x`, then the motion with UP
    `r` and OVER the graph of `h` fires the corner iff some fixed point `y` of `g` has `h y` not fixed
    by `g`; both directions. -/
theorem corner_ofTotal_iff (r g h : α → α) (hr : ∀ x, r (r x) = r x)
    (hfix : ∀ x, r x = x ↔ g x = x) :
    (ofTotal r hr (fun a b => b = h a)).Corner ↔ ∃ y, g y = y ∧ g (h y) ≠ h y := by
  constructor
  · rintro ⟨y, b, z, hy, hs, hz, hzb⟩
    have hy' : y = r y := Part.mem_some_iff.1 hy
    have hz' : z = r b := Part.mem_some_iff.1 hz
    have hs' : b = h y := hs
    refine ⟨y, (hfix y).1 hy'.symm, fun hb => hzb ?_⟩
    rw [hz', hs']
    exact (hfix (h y)).2 hb
  · rintro ⟨y, hy, hb⟩
    exact ⟨y, h y, r (h y), Part.mem_some_iff.2 ((hfix y).2 hy).symm, rfl,
      Part.mem_some_iff.2 rfl, fun e => hb ((hfix _).1 e)⟩

/-- `Statement:` the motion of an `Option`-valued map `g`: UP the identity, OVER `g x = some y`. -/
def ofPartialFun (g : α → Option α) : Motion α :=
  ofTotal id (fun _ => rfl) (fun x y => g x = some y)

/-- `Statement:` in `ofPartialFun g`, no step leaves `y` iff `g y = none`; both directions. -/
theorem noStepAt_ofPartialFun_iff (g : α → Option α) (y : α) :
    (ofPartialFun g).NoStepAt y ↔ g y = none := by
  constructor
  · intro h
    cases hy : g y with
    | none => rfl
    | some b => exact absurd hy (h b)
  · intro h b hb
    have hb' : g y = some b := hb
    rw [h] at hb'
    cases hb'

/-- `Statement:` in `ofPartialFun g`, `y` steps to itself only iff `g y = some y`; both directions. -/
theorem selfOnlyAt_ofPartialFun_iff (g : α → Option α) (y : α) :
    (ofPartialFun g).SelfOnlyAt y ↔ g y = some y :=
  ⟨fun h => h.1, fun h => ⟨h, fun b hb => Option.some_injective _ ((hb : g y = some b).symm.trans h)⟩⟩

/-- `Statement:` in `ofPartialFun g`, `y` steps elsewhere iff `g y = some b` with `b ≠ y`; both
    directions. -/
theorem leavesAt_ofPartialFun_iff (g : α → Option α) (y : α) :
    (ofPartialFun g).LeavesAt y ↔ ∃ b, g y = some b ∧ b ≠ y :=
  Iff.rfl

/-- `Statement:` if `g` is one-to-one, the reverse of `ofFun g` has at most one successor at each
    point, and at `y` it has no step iff `y` is not a value of `g`, steps to itself only iff
    `g y = y`, and steps elsewhere iff `g x = y` for some `x ≠ y`. -/
theorem reverse_ofFun_of_injective (g : α → α) (hg : Function.Injective g) (y : α) :
    (∀ a b, (ofFun g).reverse.step y a → (ofFun g).reverse.step y b → a = b) ∧
    ((ofFun g).reverse.NoStepAt y ↔ ∀ x, g x ≠ y) ∧
    ((ofFun g).reverse.SelfOnlyAt y ↔ g y = y) ∧
    ((ofFun g).reverse.LeavesAt y ↔ ∃ x, g x = y ∧ x ≠ y) := by
  refine ⟨fun a b (ha : y = g a) (hb : y = g b) => hg (ha.symm.trans hb), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  · intro h x hx; exact h x hx.symm
  · intro h b (hb : y = g b); exact h b hb.symm
  · intro h; exact h.1.symm
  · intro h; exact ⟨h.symm, fun b (hb : y = g b) => hg (hb.symm.trans h.symm)⟩
  · rintro ⟨b, (hb : y = g b), hne⟩; exact ⟨b, hb.symm, hne⟩
  · rintro ⟨x, hx, hne⟩; exact ⟨x, hx.symm, hne⟩

/-! ### § XII. The pair run backwards, and leg polarity against a carrier order -/

variable (M)

/-- `Statement:` the reversed motion has an elbow iff UP sends some `x` to `y ≠ x` and some step
    ARRIVES at `y`: UP and OVER meet at one point. -/
theorem elbow_reverse_iff :
    M.reverse.Elbow ↔ ∃ x y b, y ∈ M.up x ∧ y ≠ x ∧ M.step b y := Iff.rfl

/-- `Statement:` the reversed motion has a corner iff some `b` steps to a landing `y` and `up b`
    is a point other than `b`: OVER and UP leave one point. -/
theorem corner_reverse_iff :
    M.reverse.Corner ↔ ∃ y b z, M.IsLanding y ∧ M.step b y ∧ z ∈ M.up b ∧ z ≠ b := Iff.rfl

/-- `Statement:` UP raises: every value of `up x` is at or above `x` in the carrier order. -/
def UpRaises [LE α] : Prop := ∀ x y, y ∈ M.up x → x ≤ y

/-- `Statement:` UP lowers: every value of `up x` is at or below `x` in the carrier order. -/
def UpLowers [LE α] : Prop := ∀ x y, y ∈ M.up x → y ≤ x

/-- `Statement:` OVER raises: every step `x → y` has `x ≤ y` in the carrier order. -/
def StepRaises [LE α] : Prop := ∀ x y, M.step x y → x ≤ y

/-- `Statement:` OVER lowers: every step `x → y` has `y ≤ x` in the carrier order. -/
def StepLowers [LE α] : Prop := ∀ x y, M.step x y → y ≤ x

/-- `Statement:` the legs agree: UP raises and OVER raises. -/
def Agree [LE α] : Prop := M.UpRaises ∧ M.StepRaises

/-- `Statement:` the legs oppose: UP lowers and OVER raises. -/
def Oppose [LE α] : Prop := M.UpLowers ∧ M.StepRaises

variable {M}

/-- `Statement:` in the order dual, UP raises iff it lowers in the original order. -/
theorem upRaises_dual [LE α] : @UpRaises αᵒᵈ M _ ↔ M.UpLowers := Iff.rfl

/-- `Statement:` in the order dual, OVER raises iff it lowers in the original order. -/
theorem stepRaises_dual [LE α] : @StepRaises αᵒᵈ M _ ↔ M.StepLowers := Iff.rfl

/-- `Statement:` the order dual flips both legs: agreeing there is both legs lowering here. -/
theorem agree_dual [LE α] : @Agree αᵒᵈ M _ ↔ M.UpLowers ∧ M.StepLowers := Iff.rfl

/-- `Statement:` and opposing there is UP raising and OVER lowering here. -/
theorem oppose_dual [LE α] : @Oppose αᵒᵈ M _ ↔ M.UpRaises ∧ M.StepLowers := Iff.rfl

/-- `Statement:` INVARIANT: reversal leaves whether UP raises unchanged. -/
theorem upRaises_reverse [LE α] : M.reverse.UpRaises ↔ M.UpRaises := Iff.rfl

/-- `Statement:` INVARIANT: reversal leaves whether UP lowers unchanged. -/
theorem upLowers_reverse [LE α] : M.reverse.UpLowers ↔ M.UpLowers := Iff.rfl

/-- `Statement:` reversal flips the OVER leg only: OVER raises in the reverse iff it lowers here. -/
theorem stepRaises_reverse [LE α] : M.reverse.StepRaises ↔ M.StepLowers :=
  ⟨fun h x y hs => h y x hs, fun h x y hs => h y x hs⟩

/-- `Statement:` the reversed motion agrees in the order dual iff the motion opposes. -/
theorem agree_dual_reverse_iff [LE α] : @Agree αᵒᵈ M.reverse _ ↔ M.Oppose :=
  ⟨fun h => ⟨h.1, fun x y hs => h.2 y x hs⟩, fun h => ⟨h.1, fun x y hs => h.2 y x hs⟩⟩

/-- `Statement:` in a partial order, agreeing legs give no loop: from a landing `y`, a step to `b`
    gives `y ≤ b`, UP from `b` back to `y` gives `b ≤ y`, so `b = y` by antisymmetry. -/
theorem not_loop_of_agree [PartialOrder α] (h : M.Agree) : ¬ M.Loop :=
  fun ⟨y, b, _, hs, hby, hyb⟩ => hby (le_antisymm (h.1 b y hyb) (h.2 y b hs))

/-- `Statement:` in a partial order, if OVER raises, a step from `y` to some `x ≤ y` has `x = y`:
    no step goes strictly down. -/
theorem eq_of_step_le_of_stepRaises [PartialOrder α] (h : M.StepRaises) {x y : α}
    (hs : M.step y x) (hxy : x ≤ y) : x = y :=
  le_antisymm hxy (h y x hs)

/-- `Statement:` in a partial order with ⊥, if OVER raises, every step into ⊥ of `α` starts at ⊥ of
    `α`. -/
theorem eq_bot_of_step_to_bot [PartialOrder α] [OrderBot α] (h : M.StepRaises) (a : α)
    (hs : M.step a ⊥) : a = ⊥ :=
  le_bot_iff.mp (h a ⊥ hs)

/-- `Statement:` in a partial order with ⊥, if OVER lowers, every step out of ⊥ of `α` ends at ⊥ of
    `α`. -/
theorem eq_bot_of_step_from_bot [PartialOrder α] [OrderBot α] (h : M.StepLowers) (b : α)
    (hs : M.step ⊥ b) : b = ⊥ :=
  le_bot_iff.mp (h ⊥ b hs)

/-! ### § XIII. Further trap data: emptiness, a rank, accessibility, monotonicity; and maps of motions -/

/-- `Statement:` if every step `a → b` gives a map `E a → E b`, `E y` is empty, and `E a` is
    inhabited for every `a ≠ y`, every step into `y` starts at `y`. No order is used, and the
    step need not be single-valued. -/
theorem eq_of_step_to_isEmpty {E : α → Type*} (hstep : ∀ a b, M.step a b → Nonempty (E a → E b))
    {y : α} (hy : IsEmpty (E y)) (hne : ∀ a, Nonempty (E a) ∨ a = y) (a : α)
    (hs : M.step a y) : a = y := by
  obtain ⟨f⟩ := hstep a y hs
  rcases hne a with hx | h
  · obtain ⟨x⟩ := hx
    exact ((Function.isEmpty f).false x).elim
  · exact h

/-- `Statement:` in `ofFun g`, every step into `y` starts at `y` iff every `x` with `g^[n] x = y` for
    some `n` is `y`; both directions. `Reading:` the seam between "no other start ever reaches `y`"
    (safety) and "orbits eventually reach `y`" (liveness), named as in Alpern and Schneider, IPL 21
    (1985), pp. 181–182; theirs are properties of executions, these of a step relation. The second
    is `Arrives` (§ XVI), and the two meet in `noEntry_ofFun_iff_arrives`. -/
theorem eq_of_step_to_ofFun_iff_iterate (g : α → α) (y : α) :
    (∀ a, (ofFun g).step a y → a = y) ↔ ∀ x n, g^[n] x = y → x = y := by
  constructor
  · intro h x n
    induction n generalizing x with
    | zero => exact fun hx => hx
    | succ n ih =>
      intro hx
      rw [Function.iterate_succ_apply] at hx
      exact h x (show y = g x from (ih (g x) hx).symm)
  · intro h a ha
    exact h a 1 (show y = g a from ha).symm

/-- `Statement:` if a rank `v : α → ℕ∞` drops by at least one along every step, it drops by at least
    one along every run of one or more steps. -/
theorem rank_add_one_le_of_transGen (v : α → ℕ∞) (hv : ∀ a b, M.step a b → v b + 1 ≤ v a)
    {a c : α} (h : Relation.TransGen M.step a c) : v c + 1 ≤ v a := by
  induction h with
  | single hs => exact hv _ _ hs
  | tail _ hbc ih => exact le_trans (le_trans (hv _ _ hbc) le_self_add) ih

/-- `Statement:` with such a rank, every point on a cycle of steps has rank ⊤ of `ℕ∞`. -/
theorem rank_eq_top_of_cycle (v : α → ℕ∞) (hv : ∀ a b, M.step a b → v b + 1 ≤ v a) {y : α}
    (hy : Relation.TransGen M.step y y) : v y = ⊤ := by
  have h := rank_add_one_le_of_transGen v hv hy
  by_contra hne
  exact lt_irrefl _ ((ENat.add_one_le_iff hne).1 h)

/-- `Statement:` with such a rank, if `p` is the only point of rank ⊤ of `ℕ∞`, every point that
    steps to itself is `p`; one way. -/
theorem eq_of_step_self_of_rank (v : α → ℕ∞) (p : α) (hv : ∀ a b, M.step a b → v b + 1 ≤ v a)
    (hu : ∀ x, v x = ⊤ → x = p) {y : α} (hy : M.step y y) : y = p :=
  hu y (rank_eq_top_of_cycle v hv (Relation.TransGen.single hy))

/-- `Statement:` if an `ℕ`-valued rank drops by at least one along every step, no point lies on a
    cycle of steps. -/
theorem not_cycle_of_nat_rank (r : α → ℕ) (hv : ∀ a b, M.step a b → r b + 1 ≤ r a) (y : α) :
    ¬ Relation.TransGen M.step y y := by
  have key : ∀ a c, Relation.TransGen M.step a c → r c + 1 ≤ r a := by
    intro a c h
    induction h with
    | single hs => exact hv _ _ hs
    | tail _ hbc ih => have := hv _ _ hbc; omega
  intro hy
  have := key y y hy
  omega

/-- `Statement:` if `p` steps to itself only, every point reachable from `p` is `p`. -/
theorem eq_of_reflTransGen_of_selfOnlyAt {p x : α} (hp : M.SelfOnlyAt p)
    (h : Relation.ReflTransGen M.step p x) : x = p := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => subst ih; exact hp.2 _ hbc

/-- `Statement:` if `p` steps to itself only, every run starting at `p` stays at `p`. -/
theorem run_const_of_selfOnlyAt {p : α} (hp : M.SelfOnlyAt p) {s : ℕ → α} (hs : M.IsRun s)
    (h0 : s 0 = p) (n : ℕ) : s n = p := by
  induction n with
  | zero => exact h0
  | succ n ih => exact hp.2 _ (ih ▸ hs n)

/-- `Statement:` with a rank `v : α → ℕ∞` dropping by at least one along every step, every point
    reachable from a point that steps to itself only has rank ⊤ of `ℕ∞`. -/
theorem rank_eq_top_of_reflTransGen_selfOnlyAt (v : α → ℕ∞)
    (hv : ∀ a b, M.step a b → v b + 1 ≤ v a) {p x : α} (hp : M.SelfOnlyAt p)
    (h : Relation.ReflTransGen M.step p x) : v x = ⊤ :=
  (eq_of_reflTransGen_of_selfOnlyAt hp h) ▸
    rank_eq_top_of_cycle v hv (Relation.TransGen.single hp.1)

/-- `Statement:` for any relation `r`, a point on a cycle of `r` is not accessible (Mathlib `Acc`). -/
theorem not_acc_of_cycle (r : α → α → Prop) {c : α} (h : Relation.TransGen r c c) :
    ¬ Acc r c := fun hc => by
  induction hc with
  | intro a _ ih =>
    obtain ⟨b, hab, hba⟩ := Relation.TransGen.tail'_iff.1 h
    exact ih b hba (Relation.TransGen.head' hba hab)

/-- `Statement:` for any relation `r`, if `c` reaches `a` by `r`-steps and `a` is accessible, `c` is
    accessible. -/
theorem acc_of_reflTransGen (r : α → α → Prop) {c a : α} (h : Relation.ReflTransGen r c a)
    (ha : Acc r a) : Acc r c := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact ih (ha.inv hbc)

/-- `Statement:` on a finite carrier, `a` is not accessible iff some `c` lies on a cycle of `r` and
    reaches `a` by `r`-steps. -/
theorem not_acc_iff_reaches_cycle (r : α → α → Prop) [Finite α] {a : α} :
    ¬ Acc r a ↔ ∃ c, Relation.ReflTransGen r c a ∧ Relation.TransGen r c c := by
  constructor
  · intro hna
    by_contra hno
    push Not at hno
    let r' : α → α → Prop := fun x y => Relation.TransGen r x y ∧ Relation.ReflTransGen r y a
    haveI : IsTrans α r' := ⟨fun _ _ _ h1 h2 => ⟨h1.1.trans h2.1, h2.2⟩⟩
    haveI : Std.Irrefl r' := ⟨fun x h => hno x h.2 h.1⟩
    have wf : WellFounded r' := Finite.wellFounded_of_trans_of_irrefl r'
    have key : ∀ y, Relation.ReflTransGen r y a → Acc r y := fun y =>
      wf.induction y (C := fun y => Relation.ReflTransGen r y a → Acc r y)
        (fun y ih hy => Acc.intro y fun x hx =>
          ih x ⟨Relation.TransGen.single hx, hy⟩ (Relation.ReflTransGen.head hx hy))
    exact hna (key a Relation.ReflTransGen.refl)
  · rintro ⟨c, hca, hcc⟩ ha
    exact not_acc_of_cycle r hcc (acc_of_reflTransGen r hca ha)

/-- `Statement:` for any relation `r` (`r x a` read as a step from `a` to `x`), if a rank
    `v : α → ℕ∞` drops by at least one along every step and `v a ≠ ⊤`, then `a` is accessible. -/
theorem acc_of_rank_ne_top (r : α → α → Prop) (v : α → ℕ∞) (hv : ∀ a x, r x a → v x + 1 ≤ v a)
    {a : α} (h : v a ≠ ⊤) : Acc r a := by
  have main : ∀ k : ℕ, ∀ a, v a ≤ k → Acc r a := by
    intro k
    induction k with
    | zero =>
      intro a ha
      refine Acc.intro a fun x hx => ?_
      have := le_trans (hv a x hx) ha
      simp at this
    | succ k ih =>
      intro a ha
      refine Acc.intro a fun x hx => ih x ?_
      have h1 := le_trans (hv a x hx) ha
      have hx : v x ≠ ⊤ := by
        intro ht; rw [ht, top_add, top_le_iff] at h1; exact ENat.coe_ne_top _ h1
      obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hx
      rw [← hj] at h1 ⊢
      have : j + 1 ≤ k + 1 := by exact_mod_cast h1
      exact_mod_cast (by omega : j ≤ k)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 h
  exact main k a hk.symm.le

/-- `Statement:` under the same rank hypothesis, if `a` is not accessible, `v a` is ⊤ of `ℕ∞`. -/
theorem rank_eq_top_of_not_acc (r : α → α → Prop) (v : α → ℕ∞)
    (hv : ∀ a x, r x a → v x + 1 ≤ v a) {a : α} (h : ¬ Acc r a) : v a = ⊤ := by
  by_contra hne
  exact h (acc_of_rank_ne_top r v hv hne)

/-- `Statement:` at an accessible `a`, `Set.ncard` of the points `c` with `r`-steps from `a` down to
    `c` (their number on a finite carrier; `Set.ncard` is 0 on an infinite set), and ⊤ of `ℕ∞`
    elsewhere. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `Acc.rank` (`Mathlib/SetTheory/Ordinal/Rank.lean`)
-- is `Ordinal`-valued and takes the `Acc` proof as an argument; this is total, `ℕ∞`-valued, and
-- counts strict descendants, so it is a rank of the die's `ℕ∞` form on a finite carrier.
noncomputable def accHeight (r : α → α → Prop) (a : α) : ℕ∞ := by
  classical
  exact if Acc r a then (Set.ncard {c | Relation.TransGen r c a} : ℕ∞) else ⊤

/-- `Statement:` `accHeight r a ≠ ⊤` iff `a` is accessible. -/
theorem accHeight_ne_top_iff (r : α → α → Prop) {a : α} : accHeight r a ≠ ⊤ ↔ Acc r a := by
  unfold accHeight
  constructor
  · intro h
    by_contra ha
    rw [if_neg ha] at h
    exact h rfl
  · intro ha
    rw [if_pos ha]
    exact ENat.coe_ne_top _

/-- `Statement:` on a finite carrier, `accHeight r` drops by at least one along every step. -/
theorem accHeight_drops (r : α → α → Prop) [Finite α] :
    ∀ a x, r x a → accHeight r x + 1 ≤ accHeight r a := by
  intro a x hx
  unfold accHeight
  by_cases ha : Acc r a
  · have hx' : Acc r x := ha.inv hx
    rw [if_pos hx', if_pos ha]
    have hss : {c | Relation.TransGen r c x} ⊂ {c | Relation.TransGen r c a} :=
      ⟨fun c hc => Relation.TransGen.tail hc hx,
        fun hsub => not_acc_of_cycle r (hsub (Relation.TransGen.single hx)) hx'⟩
    have := Set.ncard_lt_ncard hss (Set.toFinite _)
    exact_mod_cast Nat.succ_le_of_lt this
  · rw [if_neg ha]
    exact le_top

/-- `Statement:` on a finite carrier, every rank dropping by at least one along every step is ⊤ of
    `ℕ∞` at `a` iff `a` is not accessible. -/
theorem forall_rank_eq_top_iff_not_acc (r : α → α → Prop) [Finite α] {a : α} :
    (∀ v : α → ℕ∞, (∀ a x, r x a → v x + 1 ≤ v a) → v a = ⊤) ↔ ¬ Acc r a :=
  ⟨fun h ha => (accHeight_ne_top_iff r).2 ha (h _ (accHeight_drops r)),
    fun hna v hv => rank_eq_top_of_not_acc r v hv hna⟩

/-- `Statement:` on a complete lattice, for a monotone `f`, the least fixed point `OrderHom.lfp f`
    steps to itself only in `ofFun f` (Knaster–Tarski, `OrderHom.map_lfp`). -/
theorem selfOnlyAt_ofFun_lfp {β : Type*} [CompleteLattice β] (f : β →o β) :
    (ofFun f).SelfOnlyAt f.lfp :=
  (selfOnlyAt_ofFun_iff f _).2 (OrderHom.map_lfp f)

/-- `Statement:` on a complete lattice, if `ofFun f` steps elsewhere at every point, `f` is not
    monotone; one way. -/
theorem not_monotone_of_forall_leavesAt {β : Type*} [CompleteLattice β] (f : β → β)
    (h : ∀ y, (ofFun f).LeavesAt y) : ¬ Monotone f := fun hm =>
  not_selfOnlyAt_and_leavesAt _ (OrderHom.lfp ⟨f, hm⟩) ⟨selfOnlyAt_ofFun_lfp ⟨f, hm⟩, h _⟩

/-- `Statement:` `c` semiconjugates `A` to `B` iff it is the map of a relation homomorphism
    (Mathlib `RelHom`) from the step of `ofFun A` to the step of `ofFun B`; both directions. -/
theorem semiconj_iff_exists_relHom {β γ : Type*} (A : β → β) (B : γ → γ) (c : β → γ) :
    Function.Semiconj c A B ↔ ∃ φ : (ofFun A).step →r (ofFun B).step, ⇑φ = c := by
  constructor
  · intro h
    exact ⟨⟨c, fun {a b} (hab : b = A a) => show c b = B (c a) by rw [hab]; exact h a⟩, rfl⟩
  · rintro ⟨φ, rfl⟩ x
    exact φ.map_rel (a := x) (b := A x) rfl

/-- `Statement:` a relation homomorphism carries a self-step to a self-step, so none exists from a
    motion with a self-step into a motion with none. -/
theorem isEmpty_relHom_of_step_self {β γ : Type*} {M : Motion β} {N : Motion γ} {y : β}
    (hy : M.step y y) (hN : ∀ t, ¬ N.step t t) : IsEmpty (M.step →r N.step) :=
  ⟨fun φ => hN (φ y) (φ.map_rel hy)⟩

/-- `Statement:` if `y` steps to itself only and `φ y` has at most one successor, `φ y` steps to
    itself only. -/
theorem selfOnlyAt_relHom {β γ : Type*} {M : Motion β} {N : Motion γ} (φ : M.step →r N.step)
    {y : β} (hy : M.SelfOnlyAt y) (hu : ∀ b c, N.step (φ y) b → N.step (φ y) c → b = c) :
    N.SelfOnlyAt (φ y) :=
  selfOnlyAt_of_step_self hu (φ.map_rel hy.1)

/-- `Statement:` a relation isomorphism (Mathlib `RelIso`) from the steps of `ofFun f` to the steps
    of `ofFun g` carries fixed points of `f` to fixed points of `g`; both directions. -/
theorem fixed_iff_of_relIso {β γ : Type*} {f : β → β} {g : γ → γ}
    (e : (ofFun f).step ≃r (ofFun g).step) (y : β) : f y = y ↔ g (e y) = e y := by
  have := @RelIso.map_rel_iff _ _ _ _ e y y
  exact ⟨fun h => (this.2 h.symm).symm, fun h => (this.1 h.symm).symm⟩

/-! ### § XIV. Views: a carrier order passed as data, and restriction to an up-closed set -/

/-- `Statement:` if `L₂ x y ↔ L₁ y x` for all `x y`, then for every motion OVER raises under `L₂`
    iff it lowers under `L₁`. `stepRaises_dual` is the case where `L₂` is the order dual. -/
theorem stepRaises_iff_of_dual (L₁ L₂ : LE α) (hd : ∀ x y, L₂.le x y ↔ L₁.le y x)
    (N : Motion α) : @StepRaises α N L₂ ↔ @StepLowers α N L₁ :=
  ⟨fun h x y hs => (hd x y).1 (h x y hs), fun h x y hs => (hd x y).2 (h x y hs)⟩

/-- `Statement:` under the same hypothesis, UP raises under `L₂` iff it lowers under `L₁`. -/
theorem upRaises_iff_of_dual (L₁ L₂ : LE α) (hd : ∀ x y, L₂.le x y ↔ L₁.le y x)
    (N : Motion α) : @UpRaises α N L₂ ↔ @UpLowers α N L₁ :=
  ⟨fun h x y hs => (hd x y).1 (h x y hs), fun h x y hs => (hd x y).2 (h x y hs)⟩

/-- `Statement:` under any `≤`, if OVER lowers and `y` is the only point `≤ y`, every step out of
    `y` ends at `y`. No antisymmetry and no `OrderBot` is assumed. -/
theorem eq_of_step_from_of_stepLowers [LE α] (h : M.StepLowers) {y : α}
    (hy : ∀ b, b ≤ y → b = y) (b : α) (hs : M.step y b) : b = y :=
  hy b (h y b hs)

/-- `Statement:` under any `≤`, if OVER raises and `y` is the only point `≥ y`, every step out of
    `y` ends at `y` (`eq_of_step_from_of_stepLowers` in the order dual). -/
theorem eq_of_step_from_of_stepRaises [LE α] (h : M.StepRaises) {y : α}
    (hy : ∀ b, y ≤ b → b = y) (b : α) (hs : M.step y b) : b = y :=
  eq_of_step_from_of_stepLowers (α := αᵒᵈ) (M := M) h hy b hs

variable (M) in
/-- `Statement:` every value of UP at a point of `S` lies in `S`. -/
def UpClosed (S : Set α) : Prop := ∀ x ∈ S, ∀ y ∈ M.up x, y ∈ S

variable (M) in
/-- `Statement:` every step from a point of `S` lands in `S`. -/
def StepClosed (S : Set α) : Prop := ∀ x ∈ S, ∀ b, M.step x b → b ∈ S

variable (M) in
/-- `Statement:` the motion on the subtype of an UP-closed `S`: UP defined where `M`'s is, with the
    same value; OVER Mathlib's `Subrel`, the steps of `M` between points of `S`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `Subrel` restricts the OVER relation; for the
-- partial map UP, `PFun.restrict` shrinks the domain and `Part.restrict` replaces a domain, and a
-- codomain restriction of a `PFun` to a set its values stay in was not located as of 2026-10-21
-- (the search is recorded in `LEAN_CUSTOM_REGISTRY.md`).
def restrict (S : Set α) (hup : M.UpClosed S) : Motion S where
  up x := ⟨(M.up x.1).Dom, fun h => ⟨(M.up x.1).get h, hup x.1 x.2 _ (Part.get_mem h)⟩⟩
  up_idem x y h := by
    obtain ⟨hd, rfl⟩ := h
    obtain ⟨h1, e1⟩ := M.up_idem _ _ (Part.get_mem (o := M.up x.1) hd)
    exact ⟨h1, Subtype.ext e1⟩
  step := Subrel M.step (· ∈ S)

/-- `Statement:` in the restriction, `y` is a value of UP at `x` iff it is so in `M`. -/
theorem mem_restrict_up {S : Set α} (hup : M.UpClosed S) (x y : S) :
    y ∈ (M.restrict S hup).up x ↔ y.1 ∈ M.up x.1 :=
  ⟨fun ⟨h, e⟩ => by subst e; exact Part.get_mem (o := M.up x.1) h, fun ⟨h, e⟩ => ⟨h, Subtype.ext e⟩⟩

/-- `Statement:` a landing of the restriction is a landing of `M` lying in `S`; both directions. -/
theorem restrict_isLanding_iff {S : Set α} (hup : M.UpClosed S) (y : S) :
    (M.restrict S hup).IsLanding y ↔ M.IsLanding y.1 :=
  mem_restrict_up hup y y

/-- `Statement:` a step of the restriction is a step of `M`; both directions. -/
theorem restrict_step_iff {S : Set α} (hup : M.UpClosed S) (x y : S) :
    (M.restrict S hup).step x y ↔ M.step x.1 y.1 := Iff.rfl

/-- `Statement:` if `S` is also OVER-closed, every step of `M` from a point of `S` is a step of the
    restriction. -/
theorem restrict_step_complete {S : Set α} (hup : M.UpClosed S) (hst : M.StepClosed S) (x : S)
    (b : α) (hb : M.step x.1 b) : ∃ b' : S, (M.restrict S hup).step x b' ∧ b'.1 = b :=
  ⟨⟨b, hst x.1 x.2 b hb⟩, hb, rfl⟩

variable (M) in
/-- `Statement:` the inclusion of `S` is a relation embedding (Mathlib `RelEmbedding`) of the
    restriction's steps into `M`'s; with `restrictVal_up`, UP commutes with it. -/
def restrictVal (S : Set α) (hup : M.UpClosed S) : (M.restrict S hup).step ↪r M.step :=
  Subrel.relEmbedding M.step (· ∈ S)

/-- `Statement:` UP commutes with `restrictVal`. -/
theorem restrictVal_up {S : Set α} (hup : M.UpClosed S) (x y : S) :
    y ∈ (M.restrict S hup).up x ↔ M.restrictVal S hup y ∈ M.up (M.restrictVal S hup x) :=
  mem_restrict_up hup x y

variable (M) in
/-- `Statement:` for `T ⊆ S`, `Set.inclusion` is a relation embedding of the restriction to `T`
    into the restriction to `S`. -/
def restrictInclusion {S T : Set α} (hS : M.UpClosed S) (hT : M.UpClosed T) (h : T ⊆ S) :
    (M.restrict T hT).step ↪r (M.restrict S hS).step :=
  Subrel.inclusionEmbedding M.step h

/-- `Statement:` UP commutes with `restrictInclusion`. -/
theorem restrictInclusion_up {S T : Set α} (hS : M.UpClosed S) (hT : M.UpClosed T) (h : T ⊆ S)
    (x y : T) : y ∈ (M.restrict T hT).up x ↔
      M.restrictInclusion hS hT h y ∈ (M.restrict S hS).up (M.restrictInclusion hS hT h x) :=
  (mem_restrict_up hT x y).trans (mem_restrict_up hS (Set.inclusion h x) (Set.inclusion h y)).symm

/-- `Statement:` in a preorder, if UP raises, every `Set.Ici a` is UP-closed. -/
theorem upClosed_Ici [Preorder α] (h : M.UpRaises) (a : α) : M.UpClosed (Set.Ici a) :=
  fun _ hx y hy => le_trans hx (h _ y hy)

/-- `Statement:` in a preorder, if OVER raises, every `Set.Ici a` is OVER-closed. -/
theorem stepClosed_Ici [Preorder α] (h : M.StepRaises) (a : α) : M.StepClosed (Set.Ici a) :=
  fun _ hx b hb => le_trans hx (h _ b hb)

/-- `Statement:` in a preorder, if OVER raises, OVER of the restriction to `Set.Ici a` raises in the
    subtype order. -/
theorem restrict_stepRaises_Ici [Preorder α] (h : M.StepRaises) (a : α)
    (hup : M.UpClosed (Set.Ici a)) : (M.restrict (Set.Ici a) hup).StepRaises :=
  fun x y hs => h x.1 y.1 hs

/-- `Statement:` an empty carrier has at most one motion. One exists on every carrier, the identity UP
    with the empty step (the `example` at `Type` in `ZeroParadox/DieCannotBe.lean` § 0), and on
    `Empty` the `Nonempty` example of § II there. -/
theorem subsingleton_of_isEmpty [IsEmpty α] : Subsingleton (Motion α) :=
  ⟨fun ⟨u, _, s⟩ ⟨u', _, s'⟩ => by
    have hu : u = u' := funext fun x => isEmptyElim x
    have hs : s = s' := funext fun x => isEmptyElim x
    subst hu; subst hs; rfl⟩

end Motion

/-! ### § XV. Views on an adjoined point, the empty carrier, and the ends of a view -/

/-- `Statement:` in a partial order, `x` is both least and greatest iff every point is `x`. -/
theorem isBot_and_isTop_iff {X : Type u} [PartialOrder X] (x : X) :
    (IsBot x ∧ IsTop x) ↔ ∀ y, y = x :=
  ⟨fun ⟨hb, ht⟩ y => le_antisymm (ht y) (hb y),
   fun h => ⟨fun y => (h y).symm ▸ le_rfl, fun y => (h y).symm ▸ le_rfl⟩⟩

/-- `Statement:` on `WithBot σ`, ⊥ is also greatest iff `σ` is empty. -/
theorem withBot_bot_isBot_and_isTop_iff {σ : Type u} [Preorder σ] :
    (IsBot (⊥ : WithBot σ) ∧ IsTop (⊥ : WithBot σ)) ↔ IsEmpty σ := by
  constructor
  · rintro ⟨-, ht⟩
    exact ⟨fun a => WithBot.not_coe_le_bot a (ht a)⟩
  · intro h
    refine ⟨fun _ => bot_le, fun x => ?_⟩
    induction x using WithBot.recBotCoe with
    | bot => exact le_rfl
    | coe a => exact isEmptyElim a

/-- `Statement:` on `WithTop σ`, ⊤ is also least iff `σ` is empty. -/
theorem withTop_top_isBot_and_isTop_iff {σ : Type u} [Preorder σ] :
    (IsBot (⊤ : WithTop σ) ∧ IsTop (⊤ : WithTop σ)) ↔ IsEmpty σ := by
  constructor
  · rintro ⟨hb, -⟩
    exact ⟨fun a => WithTop.not_top_le_coe a (hb a)⟩
  · intro h
    refine ⟨fun x => ?_, fun _ => le_top⟩
    induction x using WithTop.recTopCoe with
    | top => exact le_rfl
    | coe a => exact isEmptyElim a

/-- `Statement:` ⊥ of `WithBot σ` has a cover iff `σ` has a minimal point. -/
theorem botCovered_withBot_iff {σ : Type u} [PartialOrder σ] :
    BotCovered (WithBot σ) ↔ ∃ a : σ, IsMin a := by
  constructor
  · rintro ⟨a, h⟩
    induction a using WithBot.recBotCoe with
    | bot => exact absurd h.lt (lt_irrefl _)
    | coe a => exact ⟨a, WithBot.bot_covBy_coe.1 h⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, WithBot.bot_covBy_coe.2 ha⟩

/-- `Statement:` if `σ` has a least point and no maximal point, ⊥ of `WithTop σ` has a cover iff ⊥
    of `σ` has one. -/
theorem botCovered_withTop_iff {σ : Type u} [PartialOrder σ] [OrderBot σ] [NoMaxOrder σ] :
    BotCovered (WithTop σ) ↔ BotCovered σ := by
  constructor
  · rintro ⟨a, h⟩
    induction a using WithTop.recTopCoe with
    | top =>
      obtain ⟨b, hb⟩ := exists_gt (⊥ : σ)
      exact absurd (WithTop.coe_lt_top b) (h.2 (WithTop.coe_lt_coe.2 hb))
    | coe a => exact ⟨a, WithTop.coe_covBy_coe.1 h⟩
  · rintro ⟨a, h⟩
    exact ⟨a, WithTop.coe_covBy_coe.2 h⟩

/-- `Statement:` under any `≤`, an empty carrier has no least-element and no greatest-element
    structure. -/
theorem isEmpty_orderBot_and_orderTop {α : Type u} [LE α] [IsEmpty α] :
    IsEmpty (OrderBot α) ∧ IsEmpty (OrderTop α) :=
  ⟨⟨fun h => isEmptyElim h.bot⟩, ⟨fun h => isEmptyElim h.top⟩⟩

/-- `Statement:` under the `≤` on `α`, a least point exists iff `b = true`, and a greatest point
    exists iff `t = true`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `OrderBot` and `OrderTop` are data, and
-- `∃ x, IsBot x` is one proposition; this pairs the two existence questions of one `≤` as a cell
-- indexed by two `Bool`s, so that the order dual's exchange of the answers is one lemma
-- (`poleEnds_of_dual`).
def PoleEnds (α : Type u) [LE α] (b t : Bool) : Prop :=
  ((∃ x : α, IsBot x) ↔ b = true) ∧ ((∃ x : α, IsTop x) ↔ t = true)

/-- `Statement:` a `≤` is in at most one cell. -/
theorem poleEnds_unique {α : Type u} [LE α] {b t b' t' : Bool} (h : PoleEnds α b t)
    (h' : PoleEnds α b' t') : b = b' ∧ t = t' :=
  ⟨Bool.eq_iff_iff.2 (h.1.symm.trans h'.1), Bool.eq_iff_iff.2 (h.2.symm.trans h'.2)⟩

/-- `Statement:` if `L₂ x y ↔ L₁ y x` for all `x y`, then `L₂` is in cell `(b, t)` iff `L₁` is in
    cell `(t, b)`. -/
theorem poleEnds_of_dual {α : Type u} (L₁ L₂ : LE α) (hd : ∀ x y, L₂.le x y ↔ L₁.le y x)
    (b t : Bool) : @PoleEnds α L₂ b t ↔ @PoleEnds α L₁ t b := by
  have hb : (∃ x : α, @IsBot α L₂ x) ↔ ∃ x : α, @IsTop α L₁ x :=
    exists_congr fun x => forall_congr' fun y => hd x y
  have ht : (∃ x : α, @IsTop α L₂ x) ↔ ∃ x : α, @IsBot α L₁ x :=
    exists_congr fun x => forall_congr' fun y => hd y x
  unfold PoleEnds
  rw [hb, ht]
  exact And.comm

/-- `Statement:` the order dual `αᵒᵈ` is in cell `(b, t)` iff `α` is in cell `(t, b)`. -/
theorem poleEnds_dual {α : Type u} [LE α] (b t : Bool) : PoleEnds αᵒᵈ b t ↔ PoleEnds α t b :=
  poleEnds_of_dual (α := α) inferInstance (inferInstance : LE αᵒᵈ) (fun _ _ => Iff.rfl) b t

/-- `Statement:` the order dual exchanges the cells `(true, false)` and `(false, true)` and keeps
    the cells `(false, false)` and `(true, true)`. -/
theorem poleEnds_dual_cells {α : Type u} [LE α] :
    (PoleEnds αᵒᵈ true false ↔ PoleEnds α false true) ∧
    (PoleEnds αᵒᵈ false true ↔ PoleEnds α true false) ∧
    (PoleEnds αᵒᵈ false false ↔ PoleEnds α false false) ∧
    (PoleEnds αᵒᵈ true true ↔ PoleEnds α true true) :=
  ⟨poleEnds_dual _ _, poleEnds_dual _ _, poleEnds_dual _ _, poleEnds_dual _ _⟩

/-- `Statement:` in a partial order with a least point `a` and a greatest point `b`, `a ≠ b` iff
    the carrier has two distinct points (`Nontrivial`). -/
theorem ends_ne_iff_nontrivial {α : Type u} [PartialOrder α] {a b : α} (ha : IsBot a)
    (hb : IsTop b) : a ≠ b ↔ Nontrivial α := by
  refine ⟨fun h => ⟨⟨a, b, h⟩⟩, fun hn e => ?_⟩
  subst e
  obtain ⟨x, y, hxy⟩ := hn
  have h := (isBot_and_isTop_iff a).1 ⟨ha, hb⟩
  exact hxy ((h x).trans (h y).symm)

/-- `Statement:` the carrier is inhabited iff `i = true`, and the `≤` is in cell `(b, t)`. -/
-- [ZP-CUSTOM] extends: PoleEnds (ZeroParadox/Die.lean) | reason: `PoleEnds` puts `Empty` and ℤ in one
-- cell; this adds Mathlib's `Nonempty` as a third `Bool` so the two separate, and the order dual
-- keeps it (`poleEndsInhabited_dual`).
def PoleEndsInhabited (α : Type u) [LE α] (i b t : Bool) : Prop :=
  (Nonempty α ↔ i = true) ∧ PoleEnds α b t

/-- `Statement:` a `≤` is in at most one such cell. -/
theorem poleEndsInhabited_unique {α : Type u} [LE α] {i b t i' b' t' : Bool}
    (h : PoleEndsInhabited α i b t) (h' : PoleEndsInhabited α i' b' t') :
    i = i' ∧ b = b' ∧ t = t' :=
  ⟨Bool.eq_iff_iff.2 (h.1.symm.trans h'.1), poleEnds_unique h.2 h'.2⟩

/-- `Statement:` the order dual `αᵒᵈ` is in cell `(i, b, t)` iff `α` is in cell `(i, t, b)`. -/
theorem poleEndsInhabited_dual {α : Type u} [LE α] (i b t : Bool) :
    PoleEndsInhabited αᵒᵈ i b t ↔ PoleEndsInhabited α i t b :=
  and_congr Iff.rfl (poleEnds_dual b t)

/-- `Statement:` if a least or a greatest point exists, the carrier is inhabited. -/
theorem poleEndsInhabited_of_end {α : Type u} [LE α] {i b t : Bool}
    (h : PoleEndsInhabited α i b t) (hbt : b = true ∨ t = true) : i = true := by
  refine h.1.1 ?_
  rcases hbt with hb | ht
  · obtain ⟨x, -⟩ := h.2.1.2 hb; exact ⟨x⟩
  · obtain ⟨x, -⟩ := h.2.2.2 ht; exact ⟨x⟩

namespace Motion

variable {α : Type u} {M : Motion α}

/-! ### § XVI. Arrival and fan-in -/

variable (M) in
/-- `Statement:` `x` arrives at `y`: `x = y`, or `x` has a step and every step from `x` lands at a
    point that arrives at `y`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's `Relation.ReflTransGen` and
-- `StateTransition.Reaches` state that SOME path reaches `y`; this implies that every run passes
-- through `y` (`exists_run_eq_of_arrives`), and the converse holds classically given `[DecidableEq α]`
-- and a step at every point other than `y` (`arrives_of_forall_run`). Mathlib's `Acc` of the step with `y` removed as a
-- source is the nearest form (`acc_of_arrives`, `arrives_of_acc`); the dated search is in
-- `LEAN_CUSTOM_REGISTRY.md`.
inductive Arrives (y : α) : α → Prop
  | here : Arrives y y
  | next {x : α} : (∃ b, M.step x b) → (∀ b, M.step x b → Arrives y b) → Arrives y x

/-- `Statement:` if `x` arrives at `y`, some path of steps leads from `x` to `y`. -/
theorem reflTransGen_of_arrives {y x : α} (h : M.Arrives y x) : Relation.ReflTransGen M.step x y := by
  induction h with
  | here => exact Relation.ReflTransGen.refl
  | next hex _ ih =>
    obtain ⟨b, hb⟩ := hex
    exact Relation.ReflTransGen.head hb (ih b hb)

/-- `Statement:` if `x` arrives at `y`, every run starting at `x` visits `y`. -/
theorem exists_run_eq_of_arrives {y x : α} (h : M.Arrives y x) :
    ∀ s : ℕ → α, M.IsRun s → s 0 = x → ∃ n, s n = y := by
  induction h with
  | here => intro s _ h0; exact ⟨0, h0⟩
  | @next x _ _ ih =>
    intro s hs h0
    have h1 : M.step x (s 1) := by rw [← h0]; exact hs 0
    obtain ⟨n, hn⟩ := ih (s 1) h1 (fun k => s (k + 1)) (fun k => hs (k + 1)) rfl
    exact ⟨n + 1, hn⟩

/-- `Statement:` in `ofFun g`, `x` arrives at `y` iff `g^[n] x = y` for some `n`; both directions. -/
theorem arrives_ofFun_iff (g : α → α) (y x : α) :
    (ofFun g).Arrives y x ↔ ∃ n, g^[n] x = y := by
  constructor
  · intro h
    induction h with
    | here => exact ⟨0, rfl⟩
    | @next x _ _ ih =>
      obtain ⟨n, hn⟩ := ih (g x) rfl
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩
  · rintro ⟨n, hn⟩
    induction n generalizing x with
    | zero =>
      obtain rfl : x = y := hn
      exact Arrives.here
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      exact Arrives.next ⟨g x, rfl⟩ (fun b hb => by
        have hb' : b = g x := hb
        subst hb'
        exact ih (g x) hn)

/-- `Statement:` in `ofFun g`, a path of steps from `x` to `y` gives `g^[n] x = y` for some `n`. -/
theorem iterate_of_reflTransGen_ofFun (g : α → α) {x y : α}
    (h : Relation.ReflTransGen (ofFun g).step x y) : ∃ n, g^[n] x = y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]; exact hbc.symm⟩

/-- `Statement:` in `ofFun g`, `x` arrives at `y` iff some path of steps leads from `x` to `y`; both
    directions. -/
theorem arrives_ofFun_iff_reflTransGen (g : α → α) (y x : α) :
    (ofFun g).Arrives y x ↔ Relation.ReflTransGen (ofFun g).step x y :=
  ⟨reflTransGen_of_arrives, fun h => (arrives_ofFun_iff g y x).2 (iterate_of_reflTransGen_ofFun g h)⟩

/-- `Statement:` if every point has at most one successor, a path of steps from `x` to `y` gives that
    `x` arrives at `y`. -/
theorem arrives_of_reflTransGen_of_det (hdet : ∀ a b c, M.step a b → M.step a c → b = c)
    {x y : α} (h : Relation.ReflTransGen M.step x y) : M.Arrives y x := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Arrives.here
  | head hac _ ih => exact Arrives.next ⟨_, hac⟩ (fun d hd => (hdet _ _ _ hac hd) ▸ ih)

/-- `Statement:` if every step into `y` starts at `y`, every path of steps ending at `y` starts at
    `y`. -/
theorem eq_of_reflTransGen_of_noEntry {y : α} (hF : ∀ a, M.step a y → a = y) {x : α}
    (h : Relation.ReflTransGen M.step x y) : x = y := by
  have key : ∀ c, Relation.ReflTransGen M.step x c → c = y → x = y := by
    intro c hc
    induction hc with
    | refl => exact id
    | tail _ hbc ih => intro hc; subst hc; exact ih (hF _ hbc)
  exact key y h rfl

variable (M) in
/-- `Statement:` every step into `y` starts at `y` iff every path of steps ending at `y` starts at `y`;
    both directions, in any motion. -/
theorem noEntry_iff_noReach (y : α) :
    (∀ a, M.step a y → a = y) ↔ ∀ x, Relation.ReflTransGen M.step x y → x = y :=
  ⟨fun h _ hx => eq_of_reflTransGen_of_noEntry h hx,
   fun h a ha => h a (Relation.ReflTransGen.single ha)⟩

/-- `Statement:` if some `x ≠ y` arrives at `y`, some step into `y` starts elsewhere. -/
theorem not_noEntry_of_arrives {x y : α} (h : M.Arrives y x) (hxy : x ≠ y) :
    ¬ ∀ a, M.step a y → a = y :=
  fun hF => hxy (eq_of_reflTransGen_of_noEntry hF (reflTransGen_of_arrives h))

/-- `Statement:` in `ofFun g`, every step into `y` starts at `y` iff every point arriving at `y` is
    `y`; both directions. -/
theorem noEntry_ofFun_iff_arrives (g : α → α) (y : α) :
    (∀ a, (ofFun g).step a y → a = y) ↔ ∀ x, (ofFun g).Arrives y x → x = y := by
  rw [eq_of_step_to_ofFun_iff_iterate]
  exact ⟨fun h x hx => let ⟨n, hn⟩ := (arrives_ofFun_iff g y x).1 hx; h x n hn,
    fun h x n hn => h x ((arrives_ofFun_iff g y x).2 ⟨n, hn⟩)⟩

/-- `Statement:` in `ofFun g`, if every step into `y` starts at `y` and every point arrives at `y`,
    every point is `y`. -/
theorem eq_of_noEntry_of_forall_arrives (g : α → α) (y : α)
    (hF : ∀ a, (ofFun g).step a y → a = y) (hA : ∀ x, (ofFun g).Arrives y x) : ∀ x, x = y :=
  fun x => (noEntry_ofFun_iff_arrives g y).1 hF x (hA x)

/-- `Statement:` if `x` arrives at `y`, `x` is accessible (Mathlib `Acc`) for the step with `y`
    removed as a source. -/
theorem acc_of_arrives {y x : α} (h : M.Arrives y x) :
    Acc (fun b a => a ≠ y ∧ M.step a b) x := by
  induction h with
  | here => exact Acc.intro _ fun _ hb => absurd rfl hb.1
  | next _ _ ih => exact Acc.intro _ fun b hb => ih b hb.2

-- The `DecidableEq` binder is kept in the type on purpose: the proof cases on it, and the
-- PurityCheck prints the footprint that binder buys.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, if every point other than `y` has a step, accessibility for
    the step with `y` removed as a source gives arrival at `y`. -/
theorem arrives_of_acc [DecidableEq α] {y : α} (hprog : ∀ a, a ≠ y → ∃ b, M.step a b) {x : α}
    (hx : Acc (fun b a => a ≠ y ∧ M.step a b) x) : M.Arrives y x := by
  induction hx with
  | intro x _ ih =>
    by_cases hxy : x = y
    · subst hxy; exact Arrives.here
    · exact Arrives.next (hprog x hxy) (fun b hb => ih b ⟨hxy, hb⟩)

-- The `DecidableEq` binder is kept in the type on purpose, as for `arrives_of_acc`.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, if every point other than `y` has a step and every run
    from `x` visits `y`, then `x` arrives at `y`: the converse of `exists_run_eq_of_arrives` under
    that hypothesis. A run from `x` avoiding `y` is a descending chain of the step with `y` removed
    as a source (Mathlib `not_acc_iff_exists_descending_chain`), so `x` is accessible and
    `arrives_of_acc` applies. `Reading:` the forward half is axiom-free and this proof pays in
    `Classical.choice`, the chain being built by choice; no finite-branching or finite-carrier
    hypothesis is used. -/
theorem arrives_of_forall_run [DecidableEq α] {y : α} (hprog : ∀ a, a ≠ y → ∃ b, M.step a b)
    {x : α} (h : ∀ s : ℕ → α, M.IsRun s → s 0 = x → ∃ n, s n = y) : M.Arrives y x := by
  apply arrives_of_acc hprog
  by_contra hacc
  obtain ⟨f, hf0, hf⟩ := not_acc_iff_exists_descending_chain.mp hacc
  obtain ⟨n, hn⟩ := h f (fun n => (hf n).2) hf0
  exact (hf n).1 hn

-- Statement: CONTROL: without a step at every point other than `y` the converse fails: on `Bool`
-- with the empty step there are no runs, so every run from `true` visits `false`, and `true` does
-- not arrive at `false`.
example : let M := ofTotal (id : Bool → Bool) (fun _ => rfl) (fun _ _ => False)
    (∀ s : ℕ → Bool, M.IsRun s → s 0 = true → ∃ n, s n = false) ∧ ¬ M.Arrives false true := by
  intro M
  refine ⟨fun s hs _ => (hs 0).elim, fun h => ?_⟩
  cases h with
  | next hex _ => exact hex.elim fun _ hb => hb

set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality and a step at every point other than `y`, `x` arrives at `y`
    iff every run from `x` visits `y`; both directions. -/
theorem arrives_iff_forall_run [DecidableEq α] {y : α} (hprog : ∀ a, a ≠ y → ∃ b, M.step a b)
    (x : α) : M.Arrives y x ↔ ∀ s : ℕ → α, M.IsRun s → s 0 = x → ∃ n, s n = y :=
  ⟨exists_run_eq_of_arrives, arrives_of_forall_run hprog⟩

/-- `Statement:` in `ofFun g`, the orbit of `x` is eventually constant at `y` iff `x` arrives at `y`
    and `y` steps to itself only; both directions. -/
theorem reach_and_stay_iff (g : α → α) (x y : α) :
    (∃ N, ∀ k, N ≤ k → g^[k] x = y) ↔ (ofFun g).Arrives y x ∧ (ofFun g).SelfOnlyAt y := by
  rw [arrives_ofFun_iff, selfOnlyAt_ofFun_iff]
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨⟨N, hN N le_rfl⟩, ?_⟩
    have h1 := hN (N + 1) (Nat.le_succ N)
    rw [Function.iterate_succ_apply', hN N le_rfl] at h1
    exact h1
  · rintro ⟨⟨n, hn⟩, hy⟩
    refine ⟨n, fun k hk => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [Function.iterate_add_apply, hn, Function.iterate_fixed hy]

/-- `Statement:` if the stages of a run `s` close at `c` (`StageClosure`), no point of `c` is arrived
    at from `s 0`. -/
theorem not_arrives_of_stageClosure {s : ℕ → α} (hs : M.IsRun s) {c : Part α}
    (hc : M.StageClosure (Set.range s) c) {y : α} (hy : y ∈ c) : ¬ M.Arrives y (s 0) := fun h =>
  let ⟨n, hn⟩ := exists_run_eq_of_arrives h s hs rfl
  hc.not_mem_of_mem ⟨s 0, 0, rfl⟩ hy ⟨n, hn⟩

/-- `Statement:` the reverse of `ofFun g` has at most one successor at every point iff `g` is
    one-to-one; both directions. -/
theorem reverse_ofFun_subsingleton_iff (g : α → α) :
    (∀ y a b, (ofFun g).reverse.step y a → (ofFun g).reverse.step y b → a = b) ↔
      Function.Injective g :=
  ⟨fun h a b hab => h (g b) a b hab.symm rfl,
   fun hg _ a b (ha : _ = g a) (hb : _ = g b) => hg (ha.symm.trans hb)⟩

/-- `Statement:` every point has a step in the reverse of `ofFun g` iff `g` is onto; both
    directions. -/
theorem reverse_ofFun_total_iff (g : α → α) :
    (∀ y, ∃ a, (ofFun g).reverse.step y a) ↔ Function.Surjective g :=
  ⟨fun h y => let ⟨a, ha⟩ := h y; ⟨a, ha.symm⟩, fun h y => let ⟨a, ha⟩ := h y; ⟨a, ha.symm⟩⟩

-- The `DecidableEq` binder is kept in the type on purpose: the proof cases on it, and the
-- PurityCheck prints the footprint that binder buys.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, no point of `ofFun g` has fan-in iff `g` is one-to-one;
    both directions. -/
theorem not_fanIn_ofFun_iff_injective [DecidableEq α] (g : α → α) :
    (∀ y, ¬ (ofFun g).FanIn y) ↔ Function.Injective g := by
  refine ⟨fun h a b hab => ?_, fun hg y => not_fanIn_of_injective g hg (fun _ _ => Iff.rfl) y⟩
  by_cases hne : a = b
  · exact hne
  · exact absurd ⟨a, b, hne, hab.symm ▸ rfl, rfl⟩ (h (g b))

/-- `Statement:` the reverse of `ofFun g` is the step of a function `h` iff `g` is one-to-one and
    onto; both directions. -/
theorem reverse_ofFun_isFun_iff_bijective (g : α → α) :
    (∃ h : α → α, ∀ y a, (ofFun g).reverse.step y a ↔ a = h y) ↔ Function.Bijective g := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨fun a b hab => ?_, fun y => ⟨h y, ((hh y (h y)).2 rfl).symm⟩⟩
    exact ((hh (g a) a).1 rfl).trans ((hh (g a) b).1 hab).symm
  · intro hb
    refine ⟨Function.surjInv hb.2, fun y a => ⟨fun (ha : y = g a) => ?_, fun ha => ?_⟩⟩
    · exact hb.1 (ha ▸ (Function.surjInv_eq hb.2 y).symm)
    · show y = g a
      rw [ha, Function.surjInv_eq hb.2 y]

/-- `Statement:` if `g` is not one-to-one, some point of `ofFun g` has fan-in; proved with
    `classical`. -/
theorem exists_fanIn_ofFun_of_not_injective (g : α → α) (h : ¬ Function.Injective g) :
    ∃ y, (ofFun g).FanIn y := by
  classical
  by_contra hn
  exact h fun a b hab => by
    by_contra hne
    exact hn ⟨g b, a, b, hne, hab.symm, rfl⟩

/-- `Statement:` on `Bool`, if `g` is not one-to-one, some point of `ofFun g` has fan-in; by cases on
    the two values of `g`. -/
theorem exists_fanIn_bool (g : Bool → Bool) (h : ¬ Function.Injective g) :
    ∃ y, (ofFun g).FanIn y := by
  cases h1 : g true <;> cases h2 : g false
  · exact ⟨false, true, false, by decide, h1.symm, h2.symm⟩
  · refine absurd (fun a b hab => ?_) h
    cases a <;> cases b
    · rfl
    · rw [h1, h2] at hab; exact absurd hab (by decide)
    · rw [h1, h2] at hab; exact absurd hab (by decide)
    · rfl
  · refine absurd (fun a b hab => ?_) h
    cases a <;> cases b
    · rfl
    · rw [h1, h2] at hab; exact absurd hab (by decide)
    · rw [h1, h2] at hab; exact absurd hab (by decide)
    · rfl
  · exact ⟨true, true, false, by decide, h1.symm, h2.symm⟩

/-- `Statement:` if, for every `g : ℕ → ℕ`, not one-to-one gives a point of `ofFun g` with fan-in, then
    for every `r : ℕ → Bool`, `¬¬ (∃ n, r n = true)` gives `∃ n, r n = true` (Markov's principle); one
    way. The reduction uses `g n = 0` once `r` has taken the value `true` at or below `n`, and
    `g n = n + 1` before. -/
theorem mp_of_exists_fanIn_nat
    (H : ∀ g : ℕ → ℕ, ¬ Function.Injective g → ∃ y, (ofFun g).FanIn y) :
    ∀ r : ℕ → Bool, ¬ ¬ (∃ n, r n = true) → ∃ n, r n = true := by
  intro r hnn
  obtain ⟨fired, hf0, hfs⟩ : ∃ f : ℕ → Bool, f 0 = r 0 ∧ ∀ m, f (m + 1) = (f m || r (m + 1)) :=
    ⟨fun n => Nat.rec (motive := fun _ => Bool) (r 0) (fun m acc => acc || r (m + 1)) n, rfl,
      fun _ => rfl⟩
  have fired_iff : ∀ n, fired n = true ↔ ∃ k, k ≤ n ∧ r k = true := by
    intro n
    induction n with
    | zero =>
      rw [hf0]
      refine ⟨fun h => ⟨0, le_rfl, h⟩, fun ⟨k, hk, h⟩ => ?_⟩
      obtain rfl : k = 0 := Nat.le_zero.1 hk
      exact h
    | succ m ih =>
      rw [hfs, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨k, hk, hr⟩ := ih.1 h; exact ⟨k, Nat.le_succ_of_le hk, hr⟩
        · exact ⟨m + 1, le_rfl, h⟩
      · rintro ⟨k, hk, hr⟩
        rcases Nat.lt_or_ge k (m + 1) with hlt | hge
        · exact Or.inl (ih.2 ⟨k, Nat.le_of_lt_succ hlt, hr⟩)
        · obtain rfl : k = m + 1 := Nat.le_antisymm hk hge
          exact Or.inr hr
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, ∀ n, g n = bif fired n then 0 else n + 1 := ⟨_, fun _ => rfl⟩
  have hni : ¬ Function.Injective g := by
    intro hinj
    apply hnn
    rintro ⟨k, hk⟩
    have h1 : fired k = true := (fired_iff k).2 ⟨k, le_rfl, hk⟩
    have h2 : fired (k + 1) = true := (fired_iff (k + 1)).2 ⟨k, by omega, hk⟩
    have hgk : g k = g (k + 1) := by rw [hg, hg, h1, h2]; rfl
    have := hinj hgk
    omega
  obtain ⟨y, a, b, hab, ha, hb⟩ := H g hni
  have e : g a = g b := (show y = g a from ha).symm.trans (show y = g b from hb)
  cases hfa : fired a
  · cases hfb : fired b
    · exfalso
      have e' : a + 1 = b + 1 := by
        rw [hg, hg, hfa, hfb] at e
        exact e
      exact hab (by omega)
    · obtain ⟨k, -, hk⟩ := (fired_iff b).1 hfb
      exact ⟨k, hk⟩
  · obtain ⟨k, -, hk⟩ := (fired_iff a).1 hfa
    exact ⟨k, hk⟩

/-- `Statement:` if `y` has fan-in, some step into `y` starts elsewhere. -/
theorem not_noEntry_of_fanIn {y : α} (h : M.FanIn y) : ¬ ∀ a, M.step a y → a = y :=
  fun hF => let ⟨a, b, hab, ha, hb⟩ := h; hab ((hF a ha).trans (hF b hb).symm)

-- The `DecidableEq` binder is kept in the type on purpose, as for `not_fanIn_ofFun_iff_injective`.
set_option linter.unusedDecidableInType false in
/-- `Statement:` with decidable equality, if `g y = y` and some `x ≠ y` arrives at `y` in `ofFun g`,
    `y` has fan-in. -/
theorem fanIn_ofFun_of_arrives [DecidableEq α] (g : α → α) {x y : α} (hy : g y = y)
    (hxy : x ≠ y) (h : (ofFun g).Arrives y x) : (ofFun g).FanIn y := by
  obtain ⟨n, hn⟩ := (arrives_ofFun_iff g y x).1 h
  induction n generalizing x with
  | zero => exact absurd hn hxy
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    by_cases hgx : g x = y
    · exact ⟨x, y, hxy, hgx.symm, hy.symm⟩
    · exact ih hgx ((arrives_ofFun_iff g y (g x)).2 ⟨n, hn⟩) hn

/-- `Statement:` if `g` is one-to-one and `g y = y`, every point arriving at `y` in `ofFun g` is
    `y`. -/
theorem eq_of_arrives_ofFun_of_injective (g : α → α) (hg : Function.Injective g) {x y : α}
    (hy : g y = y) (h : (ofFun g).Arrives y x) : x = y := by
  obtain ⟨n, hn⟩ := (arrives_ofFun_iff g y x).1 h
  exact (hg.iterate n) (hn.trans (Function.iterate_fixed hy n).symm)

/-! ### § XVII. Orders on motions -/

variable (M) in
/-- `Statement:` `S` is UP-closed and OVER-closed. -/
def Closed (S : Set α) : Prop := M.UpClosed S ∧ M.StepClosed S

variable (M) in
/-- `Statement:` the sets closed under UP and OVER, as a complete sublattice of `Set α` (Mathlib
    `CompleteSublattice`): closed under arbitrary unions and intersections. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: built with Mathlib's `CompleteSublattice.mk'` from the two
-- closure conditions of a motion; Mathlib has the constructor, not this family of sets.
def closedSublattice : CompleteSublattice (Set α) :=
  CompleteSublattice.mk' {S | M.Closed S}
    (fun _ hs => ⟨fun x ⟨_, ht, hx⟩ y hy => ⟨_, ht, (hs ht).1 x hx y hy⟩,
                  fun x ⟨_, ht, hx⟩ b hb => ⟨_, ht, (hs ht).2 x hx b hb⟩⟩)
    (fun _ hs => ⟨fun x hx y hy t ht => (hs ht).1 x (hx t ht) y hy,
                  fun x hx b hb t ht => (hs ht).2 x (hx t ht) b hb⟩)

/-- `Statement:` `restrictInclusion` along `S ⊆ S` is the identity. -/
theorem restrictInclusion_refl {S : Set α} (hS : M.UpClosed S) (x : S) :
    M.restrictInclusion hS hS subset_rfl x = x := rfl

/-- `Statement:` `restrictInclusion` along `U ⊆ T` then `T ⊆ S` is `restrictInclusion` along
    `U ⊆ S`. -/
theorem restrictInclusion_trans {S T U : Set α} (hS : M.UpClosed S) (hT : M.UpClosed T)
    (hU : M.UpClosed U) (hTS : T ⊆ S) (hUT : U ⊆ T) (x : U) :
    M.restrictInclusion hS hT hTS (M.restrictInclusion hT hU hUT x) =
      M.restrictInclusion hS hU (hUT.trans hTS) x := rfl

/-- `Statement:` `M ≤ N` when `M` and `N` have the same UP and every step of `M` is a step of `N`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: an order on the die's own record `Motion`: equality of the
-- UP leg and inclusion of the OVER relation; Mathlib orders relations by `≤` on `α → α → Prop`, not
-- this pair.
instance instLE : LE (Motion α) :=
  ⟨fun M N => M.up = N.up ∧ ∀ a b, M.step a b → N.step a b⟩

/-- `Statement:` that `≤` is a partial order on the motions of `α`. -/
instance instPartialOrder : PartialOrder (Motion α) where
  le_refl _ := ⟨rfl, fun _ _ h => h⟩
  le_trans _ _ _ h₁ h₂ := ⟨h₁.1.trans h₂.1, fun a b h => h₂.2 a b (h₁.2 a b h)⟩
  le_antisymm M N h₁ h₂ := by
    obtain ⟨u, hu, s⟩ := M
    obtain ⟨u', hu', s'⟩ := N
    obtain ⟨rfl, h12⟩ := h₁
    have hs : s = s' := funext fun a => funext fun b => propext ⟨h12 a b, h₂.2 a b⟩
    subst hs
    rfl

variable {N : Motion α}

/-- `Statement:` if `M ≤ N`, the identity is a relation homomorphism from `M`'s steps to `N`'s. -/
def leHom (h : M ≤ N) : M.step →r N.step := ⟨id, fun {a b} hab => h.2 a b hab⟩

/-- `Statement:` if `M ≤ N`, `M` and `N` have the same landings. -/
theorem isLanding_iff_of_le (h : M ≤ N) (y : α) : M.IsLanding y ↔ N.IsLanding y := by
  unfold IsLanding
  rw [h.1]

/-- `Statement:` if `M ≤ N` and every step of `N` into `y` starts at `y`, so does every step of `M`. -/
theorem noEntry_anti (h : M ≤ N) (y : α) :
    (∀ a, N.step a y → a = y) → ∀ a, M.step a y → a = y :=
  fun hN a ha => hN a (h.2 a y ha)

/-- `Statement:` if `M ≤ N` and every step of `N` out of `y` ends at `y`, so does every step of `M`. -/
theorem noExit_anti (h : M ≤ N) (y : α) :
    (∀ b, N.step y b → b = y) → ∀ b, M.step y b → b = y :=
  fun hN b hb => hN b (h.2 y b hb)

/-- `Statement:` if `M ≤ N` and no step of `N` leaves `y`, no step of `M` leaves `y`. -/
theorem noStepAt_anti (h : M ≤ N) (y : α) : N.NoStepAt y → M.NoStepAt y :=
  fun hN b hb => hN b (h.2 y b hb)

/-- `Statement:` if `M ≤ N` and `y` steps elsewhere in `M`, it steps elsewhere in `N`. -/
theorem leavesAt_mono (h : M ≤ N) (y : α) : M.LeavesAt y → N.LeavesAt y :=
  fun ⟨b, hb, hne⟩ => ⟨b, h.2 y b hb, hne⟩

/-- `Statement:` if `M ≤ N` and `y` has fan-in in `M`, it has fan-in in `N`. -/
theorem fanIn_mono (h : M ≤ N) (y : α) : M.FanIn y → N.FanIn y :=
  fun ⟨a, b, hab, ha, hb⟩ => ⟨a, b, hab, h.2 a y ha, h.2 b y hb⟩

/-- `Statement:` if `M ≤ N` and the corner of `M` fires, the corner of `N` fires. -/
theorem corner_mono (h : M ≤ N) : M.Corner → N.Corner := by
  rintro ⟨y, b, z, hy, hs, hz, hne⟩
  refine ⟨y, b, z, (isLanding_iff_of_le h y).1 hy, h.2 y b hs, ?_, hne⟩
  rw [← h.1]
  exact hz

/-- `Statement:` if `M ≤ N` and `M` climbs, `N` climbs. -/
theorem climb_mono (h : M ≤ N) : M.Climb → N.Climb := by
  rintro ⟨y, b, z, hy, hs, hz, h1, h2⟩
  refine ⟨y, b, z, (isLanding_iff_of_le h y).1 hy, h.2 y b hs, ?_, h1, h2⟩
  rw [← h.1]
  exact hz

/-- `Statement:` INVARIANT: `M.reverse ≤ N.reverse` iff `M ≤ N`. -/
theorem reverse_le_iff : M.reverse ≤ N.reverse ↔ M ≤ N :=
  ⟨fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩, fun h => ⟨h.1, fun a b hab => h.2 b a hab⟩⟩

/-! ### § XVIII. Quotients of a motion -/

variable (M) in
/-- `Statement:` related starts have related successors: if `s a a'` and `a` steps to `b`, then `a'`
    steps to some `b'` with `s b b'`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: for a setoid, a bisimulation of a relation step (the back
-- clause follows by symmetry; `DieCannotBe.lean` § XXII); Mathlib's `IsBisimulation` is stated for
-- `Stream'`, `Seq` and `Computation`, `StateTransition.Respects` for `Option`-valued steps, and
-- `Quotient.map'` takes a function; the dated search is in `LEAN_CUSTOM_REGISTRY.md`.
def StepCompat (s : Setoid α) : Prop :=
  ∀ a a' b, s.r a a' → M.step a b → ∃ b', M.step a' b' ∧ s.r b b'

variable (M) in
/-- `Statement:` on the classes of `s`, UP the identity and OVER Mathlib's `Relation.Map` of `M`'s
    OVER along the class map. `M`'s UP is not carried to the classes (`quotUp` carries it under
    `UpCompat`). -/
-- [ZP-CUSTOM] no Mathlib analog | reason: pairs the identity UP with Mathlib's `Relation.Map` of the
-- step along `Quotient.mk`; Mathlib has the image relation, not the motion.
def quot (s : Setoid α) : Motion (Quotient s) :=
  ofTotal id (fun _ => rfl) (Relation.Map M.step (Quotient.mk s) (Quotient.mk s))

variable (M) in
/-- `Statement:` the class map is a relation homomorphism (Mathlib `RelHom`) from `M`'s steps to the
    quotient's, for every setoid. -/
def quotHom (s : Setoid α) : M.step →r (M.quot s).step :=
  ⟨Quotient.mk s, fun {a b} h => ⟨a, b, h, rfl, rfl⟩⟩

/-- `Statement:` if `s` is step-compatible, the class of `a` steps to `Y` iff `a` steps to some `b`
    in `Y`; both directions. -/
theorem quot_step_mk_iff {s : Setoid α} (h : M.StepCompat s) (a : α) (Y : Quotient s) :
    (M.quot s).step (Quotient.mk s a) Y ↔ ∃ b, M.step a b ∧ Quotient.mk s b = Y := by
  constructor
  · rintro ⟨a', b, hst, ha', rfl⟩
    obtain ⟨b', hb', hbb'⟩ := h a' a b (Quotient.exact ha') hst
    exact ⟨b', hb', (Quotient.sound hbb').symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨a, b, hb, rfl, rfl⟩

/-- `Statement:` if `s` is step-compatible, the class of `a` steps to itself only iff some successor of
    `a` is related to `a` and every successor of `a` is; both directions. -/
theorem quot_selfOnlyAt_mk_iff {s : Setoid α} (h : M.StepCompat s) (a : α) :
    (M.quot s).SelfOnlyAt (Quotient.mk s a) ↔
      (∃ b, M.step a b ∧ s.r b a) ∧ ∀ b, M.step a b → s.r b a := by
  unfold SelfOnlyAt
  rw [quot_step_mk_iff h]
  constructor
  · rintro ⟨⟨b, hb, he⟩, hall⟩
    exact ⟨⟨b, hb, Quotient.exact he⟩,
      fun c hc => Quotient.exact (hall _ ((quot_step_mk_iff h a _).2 ⟨c, hc, rfl⟩))⟩
  · rintro ⟨⟨b, hb, hba⟩, hall⟩
    refine ⟨⟨b, hb, Quotient.sound hba⟩, fun Y hY => ?_⟩
    obtain ⟨c, hc, rfl⟩ := (quot_step_mk_iff h a Y).1 hY
    exact Quotient.sound (hall c hc)

/-- `Statement:` if `g` sends related points to related points (the hypothesis of Mathlib's
    `Quotient.map'`), `s` is step-compatible for `ofFun g`. -/
theorem stepCompat_ofFun {g : α → α} {s : Setoid α} (hg : ∀ a b, s.r a b → s.r (g a) (g b)) :
    (ofFun g).StepCompat s := fun a a' b h hb =>
  ⟨g a', rfl, show s.r b (g a') from (show b = g a from hb) ▸ hg a a' h⟩

/-- `Statement:` under the same hypothesis, OVER of the quotient of `ofFun g` is OVER of
    `ofFun (Quotient.map' g hg)`; both directions. -/
theorem quot_ofFun_step_iff {g : α → α} {s : Setoid α} (hg : ∀ a b, s.r a b → s.r (g a) (g b))
    (X Y : Quotient s) : ((ofFun g).quot s).step X Y ↔ (ofFun (Quotient.map' g hg)).step X Y := by
  induction X using Quotient.ind with
  | _ a =>
    rw [quot_step_mk_iff (stepCompat_ofFun hg)]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (show b = g a from hb) ▸ rfl
    · intro h
      exact ⟨g a, rfl, h.symm⟩

-- Statement: CONTROL: on `Fin 3` with classes `{0, 1}` and `{2}`, the map `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 2`
-- does not send related points to related points; the quotient steps the class of `0` to itself and
-- elsewhere, and that class, read at its representative `1`, steps to itself while `1` has no
-- successor in it (so `quot_step_mk_iff` fails at `1`).
example : let s : Setoid (Fin 3) := Setoid.ker fun x : Fin 3 => decide (x = 2)
    let g : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else x
    (¬ ∀ a b, s.r a b → s.r (g a) (g b)) ∧
    ((ofFun g).quot s).step (Quotient.mk s 0) (Quotient.mk s 0) ∧
    ((ofFun g).quot s).LeavesAt (Quotient.mk s 0) ∧
    ((ofFun g).quot s).step (Quotient.mk s 1) (Quotient.mk s 0) ∧
    ¬ ∃ b, (ofFun g).step 1 b ∧ Quotient.mk s b = Quotient.mk s 0 := by
  intro s g
  have k0 : ¬ s.r 2 0 := by show ¬ (decide ((2 : Fin 3) = 2) = decide ((0 : Fin 3) = 2)); decide
  have k1 : ¬ s.r 0 2 := by show ¬ (decide ((0 : Fin 3) = 2) = decide ((2 : Fin 3) = 2)); decide
  refine ⟨fun h => k1 (h 0 1 (by show decide _ = decide _; decide)), ⟨0, 0, rfl, rfl, rfl⟩,
    ⟨Quotient.mk s 2, ⟨1, 2, rfl, Quotient.sound (by show decide _ = decide _; decide), rfl⟩,
      fun h => k0 (Quotient.exact h)⟩,
    ⟨0, 0, rfl, Quotient.sound (by show decide _ = decide _; decide), rfl⟩, ?_⟩
  rintro ⟨b, hb, he⟩
  have hb' : b = 2 := hb
  subst hb'
  exact k0 (Quotient.exact he)

variable (M) in
/-- `Statement:` related points have related UP values: if `s a a'` and `y ∈ up a`, then some
    `y' ∈ up a'` has `s y y'`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: the UP-leg twin of `StepCompat`, for a partial map
-- (Mathlib `Part`) and a setoid; the dated search is in `LEAN_CUSTOM_REGISTRY.md`.
def UpCompat (s : Setoid α) : Prop :=
  ∀ a a' y, s.r a a' → y ∈ M.up a → ∃ y', y' ∈ M.up a' ∧ s.r y y'

-- Statement: under `UpCompat`, related points have UP defined at both or at neither.
example {s : Setoid α} (h : M.UpCompat s) {a a' : α} (r : s.r a a') :
    (M.up a).Dom ↔ (M.up a').Dom := by
  rw [Part.dom_iff_mem, Part.dom_iff_mem]
  exact ⟨fun ⟨y, hy⟩ => let ⟨y', hy', _⟩ := h a a' y r hy; ⟨y', hy'⟩,
    fun ⟨y', hy'⟩ => let ⟨y, hy, _⟩ := h a' a y' (s.symm r) hy'; ⟨y, hy⟩⟩

/-- `Statement:` under `UpCompat`, related points have the same UP after the class map. -/
theorem upCompat_map_eq {s : Setoid α} (h : M.UpCompat s) {a a' : α} (r : s.r a a') :
    (M.up a).map (Quotient.mk s) = (M.up a').map (Quotient.mk s) := by
  apply Part.ext
  intro Z
  simp only [Part.mem_map_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', hy', hyy'⟩ := h a a' y r hy
    exact ⟨y', hy', (Quotient.sound hyy').symm⟩
  · rintro ⟨y', hy', rfl⟩
    obtain ⟨y, hy, hyy⟩ := h a' a y' (s.symm r) hy'
    exact ⟨y, hy, (Quotient.sound hyy).symm⟩

variable (M) in
/-- `Statement:` under `UpCompat`, on the classes of `s`: UP the class of `up a` at the class of `a`
    (`up_idem` descends), OVER as in `quot`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: `Quotient.lift` of `Part.map` of the UP leg along
-- `Quotient.mk`, paired with `quot`'s OVER; Mathlib has the lift, not a partial map on the classes.
def quotUp (s : Setoid α) (h : M.UpCompat s) : Motion (Quotient s) where
  up := fun X => Quotient.lift (fun a => (M.up a).map (Quotient.mk s))
    (fun _ _ r => upCompat_map_eq h r) X
  up_idem := by
    intro X Y hY
    induction X using Quotient.ind with
    | _ a =>
      obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).1 hY
      exact (Part.mem_map_iff _).2 ⟨y, M.up_idem a y hy, rfl⟩
  step := Relation.Map M.step (Quotient.mk s) (Quotient.mk s)

/-- `Statement:` UP of `quotUp` at the class of `a` is defined with value `Y` iff some `y ∈ up a` has
    class `Y`; both directions. -/
theorem mem_quotUp_up_mk_iff {s : Setoid α} (h : M.UpCompat s) (a : α) (Y : Quotient s) :
    Y ∈ (M.quotUp s h).up (Quotient.mk s a) ↔ ∃ y, y ∈ M.up a ∧ Quotient.mk s y = Y :=
  Part.mem_map_iff _

/-- `Statement:` the class of `a` is a landing of `quotUp` iff some `y ∈ up a` is related to `a`;
    both directions. -/
theorem isLanding_quotUp_mk_iff {s : Setoid α} (h : M.UpCompat s) (a : α) :
    (M.quotUp s h).IsLanding (Quotient.mk s a) ↔ ∃ y, y ∈ M.up a ∧ s.r y a := by
  unfold IsLanding
  rw [mem_quotUp_up_mk_iff]
  exact ⟨fun ⟨y, hy, he⟩ => ⟨y, hy, Quotient.exact he⟩,
    fun ⟨y, hy, hr⟩ => ⟨y, hy, Quotient.sound hr⟩⟩

/-- `Statement:` if `a` is a landing, its class is a landing of `quotUp`. One way: the converse is
    refuted by the `Fin 3` example below. -/
theorem isLanding_quotUp_mk {s : Setoid α} (h : M.UpCompat s) {a : α} (ha : M.IsLanding a) :
    (M.quotUp s h).IsLanding (Quotient.mk s a) :=
  (isLanding_quotUp_mk_iff h a).2 ⟨a, ha, s.refl a⟩

/-- `Statement:` OVER of `quotUp` is OVER of `quot`. -/
theorem quotUp_step {s : Setoid α} (h : M.UpCompat s) : (M.quotUp s h).step = (M.quot s).step :=
  rfl

/-- `Statement:` if UP is the identity, `UpCompat` holds for every setoid. -/
theorem upCompat_of_up_eq_some (hu : ∀ x, M.up x = Part.some x) (s : Setoid α) : M.UpCompat s :=
  fun _ a' _ r hy => ⟨a', by rw [hu]; exact Part.mem_some a',
    by rw [hu] at hy; rw [Part.mem_some_iff.1 hy]; exact r⟩

/-- `Statement:` if UP is the identity, `quotUp` is `quot`. -/
theorem quotUp_eq_quot (hu : ∀ x, M.up x = Part.some x) (s : Setoid α) :
    M.quotUp s (upCompat_of_up_eq_some hu s) = M.quot s := by
  unfold quotUp quot ofTotal
  congr 1
  funext X
  induction X using Quotient.ind with
  | _ a =>
    show (M.up a).map (Quotient.mk s) = Part.some (Quotient.mk s a)
    rw [hu, Part.map_some]

/-- `Statement:` a total idempotent `r` sending related points to related points gives `UpCompat`
    for `ofTotal r`. -/
theorem upCompat_ofTotal {r : α → α} (hr : ∀ x, r (r x) = r x) (st : α → α → Prop) {s : Setoid α}
    (hs : ∀ a b, s.r a b → s.r (r a) (r b)) : (ofTotal r hr st).UpCompat s :=
  fun a a' _ h hy => ⟨r a', Part.mem_some _, (Part.mem_some_iff.1 hy) ▸ hs a a' h⟩

-- Statement: `ofFun g` has the identity UP, so its `quotUp` is its `quot`.
example (g : α → α) (s : Setoid α) :
    (ofFun g).quotUp s (upCompat_of_up_eq_some (M := ofFun g) (fun _ => rfl) s) =
      (ofFun g).quot s :=
  quotUp_eq_quot (fun _ => rfl) s

-- Statement: MEMBER with a non-identity UP: on `Fin 3` with classes `{0, 1}` and `{2}`, `r` sends `1`
-- to `0` and fixes `0`, `2`; `UpCompat` holds, the class of `1` is a landing of `quotUp`, and `1` is
-- not a landing (the converse of `isLanding_quotUp_mk` fails).
example : let s : Setoid (Fin 3) := Setoid.ker fun x : Fin 3 => decide (x = 2)
    let r : Fin 3 → Fin 3 := fun x => if x = 1 then 0 else x
    ∃ hr : ∀ x, r (r x) = r x, ∃ h : (ofTotal r hr (fun _ _ => False)).UpCompat s,
      ((ofTotal r hr (fun _ _ => False)).quotUp s h).IsLanding (Quotient.mk s 1) ∧
      ¬ (ofTotal r hr (fun _ _ => False)).IsLanding 1 := by
  intro s r
  have hr : ∀ x, r (r x) = r x := by decide
  have hs : ∀ a b : Fin 3, decide (a = 2) = decide (b = 2) →
      decide ((if a = 1 then 0 else a) = 2) = decide ((if b = 1 then 0 else b) = 2) := by decide
  refine ⟨hr, upCompat_ofTotal hr _ (fun a b h => hs a b h), ?_, ?_⟩
  · rw [isLanding_quotUp_mk_iff]
    exact ⟨0, Part.mem_some _, by show decide _ = decide _; decide⟩
  · intro h
    exact absurd (Part.mem_some_iff.1 h) (by decide)

-- Statement: CONTROL: on the same classes, `r` sending `1` to `2` (and fixing `0`, `2`) is idempotent
-- and not `UpCompat`: `0` and `1` are related, their UP values `0` and `2` are not.
example : let s : Setoid (Fin 3) := Setoid.ker fun x : Fin 3 => decide (x = 2)
    let r : Fin 3 → Fin 3 := fun x => if x = 1 then 2 else x
    ∃ hr : ∀ x, r (r x) = r x, ¬ (ofTotal r hr (fun _ _ => False)).UpCompat s := by
  intro s r
  have hr : ∀ x, r (r x) = r x := by decide
  refine ⟨hr, fun h => ?_⟩
  obtain ⟨y', hy', hr'⟩ := h 0 1 0 (by show decide _ = decide _; decide) (Part.mem_some _)
  have : y' = 2 := Part.mem_some_iff.1 hy'
  subst this
  exact absurd hr' (by show ¬ (decide _ = decide _); decide)

end Motion

/-! ### § XIX. Maps of motions with the UP leg: strict, lax, and the back clause -/

namespace Motion

variable {α β γ δ : Type*}

/-- `Statement:` `f` carries every UP value at `x` in `M` to an UP value at `f x` in `N`. `Reading:`
    the lax square of Cockett and Lack, TCS 270 (2002), § 2.1.4, p. 230 (`upLax_iff_le`). -/
def UpLax (M : Motion α) (N : Motion β) (f : α → β) : Prop :=
  ∀ x y, y ∈ M.up x → f y ∈ N.up (f x)

/-- `Statement:` UP at `f x` in `N` is UP at `x` in `M` mapped by `f`, at every `x`. `Reading:` the
    UP square commutes in Par. -/
def UpStrict (M : Motion α) (N : Motion β) (f : α → β) : Prop :=
  ∀ x, N.up (f x) = (M.up x).map f

/-- `Statement:` every step out of `f a` in `N` is the image under `f` of a step out of `a` in `M`.
    `Reading:` with step preservation, Rutten's homomorphism of transition systems, TCS 249 (2000),
    p. 10, conditions 1–2 ("functional bisimulations", p. 13). -/
def StepBack (M : Motion α) (N : Motion β) (f : α → β) : Prop :=
  ∀ a c, N.step (f a) c → ∃ b, M.step a b ∧ f b = c

-- Statement: `StepBack` is `Relation.Fibration` of the reversed steps, by `Iff.rfl`.
example (M : Motion α) (N : Motion β) (f : α → β) :
    StepBack M N f ↔ Relation.Fibration M.reverse.step N.reverse.step f := Iff.rfl

/-- `Statement:` a strict map of motions: a map carrying steps to steps, with `UpStrict`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: a Mathlib `RelHom` on the OVER leg paired with a commuting
-- square on the partial UP leg; Mathlib has the first, not the pair.
structure Hom (M : Motion α) (N : Motion β) where
  /-- The underlying map. -/
  toFun : α → β
  /-- Steps go to steps. -/
  map_step : ∀ {a b}, M.step a b → N.step (toFun a) (toFun b)
  /-- The UP square commutes. -/
  map_up : UpStrict M N toFun

/-- `Statement:` a lax map of motions: a map carrying steps to steps, with `UpLax`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: as `Motion.Hom`, with the UP square lax in the restriction
-- order.
structure LaxHom (M : Motion α) (N : Motion β) where
  /-- The underlying map. -/
  toFun : α → β
  /-- Steps go to steps. -/
  map_step : ∀ {a b}, M.step a b → N.step (toFun a) (toFun b)
  /-- UP values go to UP values. -/
  map_up : UpLax M N toFun

variable {M : Motion α} {N : Motion β} {P : Motion γ}

/-- `Statement:` `UpLax` iff, at every `x`, UP at `x` mapped by `f` is `≤` UP at `f x` in `Part`'s
    order; both directions. -/
theorem upLax_iff_le (f : α → β) : UpLax M N f ↔ ∀ x, (M.up x).map f ≤ N.up (f x) := by
  constructor
  · intro h x z hz
    obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).1 hz
    exact h x y hy
  · intro h x y hy
    exact h x (f y) ((Part.mem_map_iff _).2 ⟨y, hy, rfl⟩)

/-- `Statement:` `UpStrict` gives `UpLax`; one way (`lax_not_strict` example below). -/
theorem upStrict_upLax {f : α → β} (h : UpStrict M N f) : UpLax M N f :=
  fun x y hy => by rw [h x]; exact Part.mem_map f hy

/-- `Statement:` `UpStrict` iff `UpLax` and, at every `x`, UP defined at `f x` in `N` gives UP defined
    at `x` in `M`; both directions. -/
theorem upStrict_iff {f : α → β} :
    UpStrict M N f ↔ UpLax M N f ∧ ∀ x, (N.up (f x)).Dom → (M.up x).Dom := by
  constructor
  · intro h
    refine ⟨upStrict_upLax h, fun x hd => ?_⟩
    rw [h x] at hd
    exact hd
  · rintro ⟨hl, hd⟩ x
    apply Part.ext
    intro z
    constructor
    · intro hz
      have hdom : (M.up x).Dom := hd x (Part.dom_iff_mem.2 ⟨z, hz⟩)
      have hy := Part.get_mem hdom
      rw [Part.mem_unique hz (hl x _ hy)]
      exact Part.mem_map f hy
    · intro hz
      obtain ⟨y, hy, rfl⟩ := (Part.mem_map_iff _).1 hz
      exact hl x y hy

/-- `Statement:` if UP of `M` is total, `UpLax` gives `UpStrict`. -/
theorem upStrict_of_upLax_of_upTotal {f : α → β} (hM : M.UpTotal) (h : UpLax M N f) :
    UpStrict M N f :=
  upStrict_iff.2 ⟨h, fun x _ => hM x⟩

/-- `Statement:` a strict map is a lax map with the same underlying map. -/
def Hom.toLax (φ : Hom M N) : LaxHom M N := ⟨φ.toFun, φ.map_step, upStrict_upLax φ.map_up⟩

/-- `Statement:` if UP of `M` is total, a lax map is a strict map with the same underlying map. -/
def LaxHom.toHomOfUpTotal (hM : M.UpTotal) (φ : LaxHom M N) : Hom M N :=
  ⟨φ.toFun, φ.map_step, upStrict_of_upLax_of_upTotal hM φ.map_up⟩

/-- `Statement:` the identity is a strict map. -/
def Hom.id (M : Motion α) : Hom M M :=
  ⟨fun x => x, fun h => h, fun _ => (Part.map_id' (fun _ => rfl) _).symm⟩

/-- `Statement:` strict maps compose. -/
def Hom.comp (ψ : Hom N P) (φ : Hom M N) : Hom M P :=
  ⟨ψ.toFun ∘ φ.toFun, fun h => ψ.map_step (φ.map_step h), fun x => by
    show P.up (ψ.toFun (φ.toFun x)) = _
    rw [ψ.map_up, φ.map_up, Part.map_map]⟩

/-- `Statement:` the identity is a left unit, by `rfl`. -/
theorem Hom.id_comp (φ : Hom M N) : (Hom.id N).comp φ = φ := rfl

/-- `Statement:` the identity is a right unit, by `rfl`. -/
theorem Hom.comp_id (φ : Hom M N) : φ.comp (Hom.id M) = φ := rfl

/-- `Statement:` composition is associative, by `rfl`. -/
theorem Hom.comp_assoc {Q : Motion δ} (χ : Hom P Q) (ψ : Hom N P) (φ : Hom M N) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := rfl

/-- `Statement:` the identity is a lax map. -/
def LaxHom.id (M : Motion α) : LaxHom M M := ⟨fun x => x, fun h => h, fun _ _ h => h⟩

/-- `Statement:` lax maps compose. -/
def LaxHom.comp (ψ : LaxHom N P) (φ : LaxHom M N) : LaxHom M P :=
  ⟨ψ.toFun ∘ φ.toFun, fun h => ψ.map_step (φ.map_step h),
    fun x y hy => ψ.map_up _ _ (φ.map_up x y hy)⟩

/-- `Statement:` `toLax` preserves composition, by `rfl`. -/
theorem Hom.toLax_comp (ψ : Hom N P) (φ : Hom M N) : (ψ.comp φ).toLax = ψ.toLax.comp φ.toLax := rfl

/-- `Statement:` a strict map is, with the same underlying map, a strict map of the reverses. -/
def Hom.reverse (φ : Hom M N) : Hom M.reverse N.reverse := ⟨φ.toFun, fun h => φ.map_step h, φ.map_up⟩

/-- `Statement:` reversing a strict map twice returns it, by `rfl`. -/
theorem Hom.reverse_reverse (φ : Hom M N) : φ.reverse.reverse = φ := rfl

/-- `Statement:` reversal preserves composition, by `rfl`. -/
theorem Hom.reverse_comp (ψ : Hom N P) (φ : Hom M N) :
    (ψ.comp φ).reverse = ψ.reverse.comp φ.reverse := rfl

/-- `Statement:` if UP is the identity on both motions, a relation homomorphism (Mathlib `RelHom`) of
    the steps is a strict map. -/
def ofRelHomIdUp (hM : ∀ x, M.up x = Part.some x) (hN : ∀ y, N.up y = Part.some y)
    (φ : M.step →r N.step) : Hom M N :=
  ⟨φ, fun h => φ.map_rel h, fun x => by rw [hM, hN, Part.map_some]⟩

/-- `Statement:` `c` semiconjugates `A` to `B` iff some strict map from `ofFun A` to `ofFun B` has
    underlying map `c`; both directions. -/
theorem semiconj_iff_exists_hom (A : α → α) (B : β → β) (c : α → β) :
    Function.Semiconj c A B ↔ ∃ φ : Hom (ofFun A) (ofFun B), φ.toFun = c := by
  rw [semiconj_iff_exists_relHom]
  constructor
  · rintro ⟨φ, rfl⟩; exact ⟨ofRelHomIdUp (fun _ => rfl) (fun _ => rfl) φ, rfl⟩
  · rintro ⟨φ, rfl⟩; exact ⟨⟨φ.toFun, φ.map_step⟩, rfl⟩

/-- `Statement:` every strict map from `ofFun A` to `ofFun B` has the back clause. -/
theorem stepBack_ofFun {A : α → α} {B : β → β} (φ : Hom (ofFun A) (ofFun B)) :
    StepBack (ofFun A) (ofFun B) φ.toFun :=
  fun a c (hc : c = B (φ.toFun a)) =>
    ⟨A a, rfl, (φ.map_step (a := a) (b := A a) rfl).symm ▸ hc.symm⟩

section transfer
variable (φ : LaxHom M N)
include φ

/-- `Statement:` along a lax map, a landing goes to a landing. -/
theorem LaxHom.isLanding {y : α} (hy : M.IsLanding y) : N.IsLanding (φ.toFun y) := φ.map_up y y hy

/-- `Statement:` along a lax map, if `M` has a landing, `N` has one. -/
theorem LaxHom.hasLanding : M.HasLanding → N.HasLanding := fun ⟨_, hy⟩ => ⟨_, φ.isLanding hy⟩

/-- `Statement:` along a lax map, if OVER exists from a landing of `M`, it exists from a landing of `N`. -/
theorem LaxHom.overAtLanding : M.OverAtLanding → N.OverAtLanding :=
  fun ⟨_, _, hy, hs⟩ => ⟨_, _, φ.isLanding hy, φ.map_step hs⟩

/-- `Statement:` along an onto lax map, if UP of `M` is total, UP of `N` is total. -/
theorem LaxHom.upTotal (hs : Function.Surjective φ.toFun) (hM : M.UpTotal) : N.UpTotal := by
  intro y
  obtain ⟨x, rfl⟩ := hs y
  exact Part.dom_iff_mem.2 ⟨_, φ.map_up x _ (Part.get_mem (hM x))⟩

/-- `Statement:` along a one-to-one lax map, if the corner of `M` fires, the corner of `N` fires. -/
theorem LaxHom.corner (hi : Function.Injective φ.toFun) : M.Corner → N.Corner :=
  fun ⟨_, b, z, hy, hs, hz, hzb⟩ =>
    ⟨_, _, _, φ.isLanding hy, φ.map_step hs, φ.map_up b z hz, fun e => hzb (hi e)⟩

/-- `Statement:` along a one-to-one lax map, if `M` loops, `N` loops. -/
theorem LaxHom.loop (hi : Function.Injective φ.toFun) : M.Loop → N.Loop :=
  fun ⟨y, b, hy, hs, hby, hyb⟩ =>
    ⟨_, _, φ.isLanding hy, φ.map_step hs, fun e => hby (hi e), φ.map_up b y hyb⟩

/-- `Statement:` along a one-to-one lax map, if `M` climbs, `N` climbs. -/
theorem LaxHom.climb (hi : Function.Injective φ.toFun) : M.Climb → N.Climb :=
  fun ⟨_, b, z, hy, hs, hz, hzb, hzy⟩ =>
    ⟨_, _, _, φ.isLanding hy, φ.map_step hs, φ.map_up b z hz, fun e => hzb (hi e),
      fun e => hzy (hi e)⟩

/-- `Statement:` along a one-to-one lax map, if `M` has an elbow, `N` has one. -/
theorem LaxHom.elbow (hi : Function.Injective φ.toFun) : M.Elbow → N.Elbow :=
  fun ⟨x, y, _, hy, hyx, hs⟩ => ⟨_, _, _, φ.map_up x y hy, fun e => hyx (hi e), φ.map_step hs⟩

/-- `Statement:` along a one-to-one lax map, if `y` steps elsewhere, its image steps elsewhere. -/
theorem LaxHom.leavesAt (hi : Function.Injective φ.toFun) {y : α} :
    M.LeavesAt y → N.LeavesAt (φ.toFun y) :=
  fun ⟨_, hb, hne⟩ => ⟨_, φ.map_step hb, fun e => hne (hi e)⟩

/-- `Statement:` along a one-to-one lax map, if `y` has fan-in, its image has fan-in. -/
theorem LaxHom.fanIn (hi : Function.Injective φ.toFun) {y : α} : M.FanIn y → N.FanIn (φ.toFun y) :=
  fun ⟨_, _, hab, ha, hb⟩ => ⟨_, _, fun e => hab (hi e), φ.map_step ha, φ.map_step hb⟩

/-- `Statement:` along a lax map, if no step leaves the image of `y`, no step leaves `y`. -/
theorem LaxHom.noStepAt_of_image {y : α} : N.NoStepAt (φ.toFun y) → M.NoStepAt y :=
  fun h _ hb => h _ (φ.map_step hb)

/-- `Statement:` along a lax map with the back clause, if no step leaves `y`, no step leaves its image. -/
theorem LaxHom.noStepAt (hb : StepBack M N φ.toFun) {y : α} :
    M.NoStepAt y → N.NoStepAt (φ.toFun y) :=
  fun h c hc => let ⟨_, hs, _⟩ := hb y c hc; h _ hs

/-- `Statement:` along a lax map with the back clause, if `y` steps to itself only, so does its image. -/
theorem LaxHom.selfOnlyAt (hb : StepBack M N φ.toFun) {y : α} :
    M.SelfOnlyAt y → N.SelfOnlyAt (φ.toFun y) :=
  fun ⟨h1, h2⟩ => ⟨φ.map_step h1, fun c hc => let ⟨b, hs, e⟩ := hb y c hc; e ▸ (h2 b hs) ▸ rfl⟩

/-- `Statement:` along a lax map with the back clause, if the image of `y` steps elsewhere, `y` steps
    elsewhere. -/
theorem LaxHom.leavesAt_of_image (hb : StepBack M N φ.toFun) {y : α} :
    N.LeavesAt (φ.toFun y) → M.LeavesAt y :=
  fun ⟨c, hc, hne⟩ => let ⟨b, hs, e⟩ := hb y c hc; ⟨b, hs, fun h => hne (e ▸ h ▸ rfl)⟩

/-- `Statement:` along a one-to-one lax map with the back clause, if the image of `y` steps to itself
    only, `y` steps to itself only. -/
theorem LaxHom.selfOnlyAt_of_image (hb : StepBack M N φ.toFun) (hi : Function.Injective φ.toFun)
    {y : α} : N.SelfOnlyAt (φ.toFun y) → M.SelfOnlyAt y :=
  fun ⟨h1, h2⟩ =>
    let ⟨_, hs, e⟩ := hb y _ h1
    ⟨(hi e) ▸ hs, fun _ hc => hi (h2 _ (φ.map_step hc))⟩

/-- `Statement:` along a lax map with the back clause, if `x` arrives at `y`, the image of `x` arrives
    at the image of `y`. -/
theorem LaxHom.arrives (hb : StepBack M N φ.toFun) {y x : α} (h : M.Arrives y x) :
    N.Arrives (φ.toFun y) (φ.toFun x) := by
  induction h with
  | here => exact Arrives.here
  | next hex _ ih =>
    obtain ⟨b, hb'⟩ := hex
    exact Arrives.next ⟨_, φ.map_step hb'⟩ fun c hc => by
      obtain ⟨b, hs, rfl⟩ := hb _ c hc
      exact ih b hs

end transfer

/-- `Statement:` along a strict map, if UP of `N` is total, UP of `M` is total. -/
theorem Hom.upTotal_of (φ : Hom M N) (hN : N.UpTotal) : M.UpTotal := fun x => by
  have := hN (φ.toFun x); rw [φ.map_up] at this; exact this

/-- `Statement:` along a one-to-one strict map, if the image of `y` is a landing, `y` is a landing. -/
theorem Hom.isLanding_of_image (φ : Hom M N) (hi : Function.Injective φ.toFun) {y : α}
    (h : N.IsLanding (φ.toFun y)) : M.IsLanding y := by
  unfold IsLanding at h; rw [φ.map_up] at h
  obtain ⟨z, hz, e⟩ := (Part.mem_map_iff _).1 h
  exact hi e ▸ hz

-- Statement: NO-GO, lax is not strict: on `Unit`, UP undefined in the source and the identity in the
-- target; the identity map is lax and not strict, and is one-to-one, and `()` is not a landing of the
-- source while its image is a landing of the target.
example : let M : Motion Unit :=
      ⟨fun _ => Part.none, fun _ _ h => (Part.notMem_none _ h).elim, fun _ _ => False⟩
    UpLax M (ofFun id) id ∧ ¬ UpStrict M (ofFun id) id ∧ ¬ M.IsLanding () ∧
      (ofFun (id : Unit → Unit)).IsLanding () := by
  intro M
  refine ⟨fun _ _ h => (Part.notMem_none _ h).elim, fun h => ?_, Part.notMem_none _, Part.mem_some _⟩
  have hd : ((ofFun (id : Unit → Unit)).up ()).Dom := trivial
  rw [h ()] at hd
  exact hd

-- Statement: NO-GO, the back clause is not carried by reversal: from `Bool` with OVER `_ → false` to
-- `Unit` with every step, the constant map has the back clause, and between the reverses it does not.
example : let M : Motion Bool := ofTotal id (fun _ => rfl) (fun _ b => b = false)
    let N : Motion Unit := ofTotal id (fun _ => rfl) (fun _ _ => True)
    StepBack M N (fun _ => ()) ∧ ¬ StepBack M.reverse N.reverse (fun _ => ()) := by
  intro M N
  refine ⟨fun _ _ _ => ⟨false, rfl, rfl⟩, fun h => ?_⟩
  obtain ⟨b, hb, -⟩ := h true () trivial
  cases (hb : true = false)

-- Statement: NO-GO, the corner and stepping elsewhere are not carried forward without one-to-one: the
-- constant strict map from `Bool` (UP constant `true`, OVER `true → false`) to `Unit` (UP the identity,
-- every step); the source fires the corner and `true` steps elsewhere, the target does neither, and
-- `false`, not a landing of the source, goes to a landing.
example : let M := ofTotal (fun _ : Bool => true) (fun _ => rfl) (fun a b => a = true ∧ b = false)
    let N := ofTotal (id : Unit → Unit) (fun _ => rfl) (fun _ _ => True)
    ∃ φ : Hom M N, M.Corner ∧ ¬ N.Corner ∧ M.LeavesAt true ∧ ¬ N.LeavesAt (φ.toFun true) ∧
      ¬ M.IsLanding false ∧ N.IsLanding (φ.toFun false) := by
  intro M N
  refine ⟨⟨fun _ => (), fun _ => trivial, fun _ => ?_⟩,
    ⟨true, false, true, Part.mem_some _, ⟨rfl, rfl⟩, Part.mem_some _, by decide⟩,
    fun ⟨_, _, _, _, _, _, h⟩ => h rfl, ⟨false, ⟨rfl, rfl⟩, by decide⟩,
    fun h => by obtain ⟨_, _, h⟩ := h; exact h rfl,
    fun h => absurd (Part.mem_some_iff.1 h) (by decide), Part.mem_some _⟩
  show Part.some () = (Part.some true).map _
  rw [Part.map_some]

-- Statement: NO-GO, a climb is not carried forward without one-to-one and a loop is not reflected: the
-- strict map `0, 2 ↦ true`, `1 ↦ false` from `Fin 3` (UP `1 ↦ 2`, else fixed; OVER `0 → 1`), which
-- climbs and does not loop, to `Bool` (UP constant `true`, OVER `true → false`), which loops and, on
-- two points, does not climb (`climb_three`).
example : let M := (ofTotal (fun x : Fin 3 => if x = 1 then 2 else x) (by decide)
      (fun a b => a = 0 ∧ b = 1))
    let N := ofTotal (fun _ : Bool => true) (fun _ => rfl) (fun a b => a = true ∧ b = false)
    ∃ φ : Hom M N, M.Climb ∧ ¬ M.Loop ∧ N.Loop ∧ ¬ N.Climb ∧ φ.toFun 1 = false := by
  intro M N
  refine ⟨⟨fun x => decide (x ≠ 1), ?_, ?_⟩,
    ⟨0, 1, 2, Part.mem_some_iff.2 (by decide), ⟨rfl, rfl⟩, Part.mem_some_iff.2 (by decide),
      by decide, by decide⟩, ?_,
    ⟨true, false, Part.mem_some _, ⟨rfl, rfl⟩, by decide, Part.mem_some _⟩, ?_, rfl⟩
  · rintro a b ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · intro x
    show Part.some true = (Part.some (if x = 1 then 2 else x)).map _
    rw [Part.map_some]; congr 1; revert x; decide
  · rintro ⟨y, b, hy, ⟨rfl, rfl⟩, -, hyb⟩
    exact absurd (Part.mem_some_iff.1 hyb) (by decide)
  · intro h
    obtain ⟨y, b, z, hyb, hbz, hzy⟩ := N.climb_three h
    revert hyb hbz hzy; revert y b z; decide

-- Statement: NO-GO, arrival is not carried forward without the back clause: the identity from the step
-- `true → false` on `Bool` to the steps out of `true`; `true` arrives at `false` in the source, and in
-- the target the run staying at `true` never visits `false`.
example : let M : Motion Bool := ofTotal id (fun _ => rfl) (fun a b => a = true ∧ b = false)
    let N : Motion Bool := ofTotal id (fun _ => rfl) (fun a _ => a = true)
    ∃ φ : Hom M N, M.Arrives false true ∧ ¬ N.Arrives (φ.toFun false) (φ.toFun true) := by
  intro M N
  refine ⟨⟨id, fun h => h.1, fun _ => rfl⟩,
    Arrives.next ⟨false, rfl, rfl⟩ (fun b ⟨_, hb⟩ => hb ▸ Arrives.here), fun h => ?_⟩
  obtain ⟨n, hn⟩ := exists_run_eq_of_arrives h (fun _ => true) (fun _ => rfl) rfl
  exact absurd hn (by decide)

-- Statement: CONTROL, `Unit` with the identity UP and every step: every motion has a lax map into it,
-- and a strict map into it exists iff UP of the source is total; both directions. So a map existing
-- carries no content without one-to-one or the back clause.
example (M : Motion α) :
    Nonempty (LaxHom M (ofTotal (id : Unit → Unit) (fun _ => rfl) (fun _ _ => True))) ∧
      (Nonempty (Hom M (ofTotal (id : Unit → Unit) (fun _ => rfl) (fun _ _ => True))) ↔ M.UpTotal) :=
  let φ : LaxHom M (ofTotal (id : Unit → Unit) (fun _ => rfl) (fun _ _ => True)) :=
    ⟨fun _ => (), fun _ => trivial, fun _ _ _ => Part.mem_some _⟩
  ⟨⟨φ⟩, fun ⟨ψ⟩ => ψ.upTotal_of (fun _ => trivial), fun h => ⟨φ.toHomOfUpTotal h⟩⟩

-- Statement: NO-GO, a landing is not reflected without onto: a strict map from a motion on `Empty`,
-- which has no landing, into `Unit` with the identity UP, which has one.
example : ∃ (M : Motion Empty) (_ : Hom M (ofTotal (id : Unit → Unit) (fun _ => rfl) (fun _ _ => True))),
    ¬ M.HasLanding ∧ (ofTotal (id : Unit → Unit) (fun _ => rfl) (fun _ _ => True)).HasLanding :=
  ⟨ofTotal id (fun _ => rfl) (fun _ _ => False), ⟨Empty.elim, fun {a} _ => a.elim, fun x => x.elim⟩,
    fun ⟨y, _⟩ => y.elim, ⟨(), Part.mem_some _⟩⟩

end Motion

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
#print axioms Motion.corner_iff_crossing
#print axioms Motion.corner_iff_loop_or_climb
#print axioms Motion.corner_iff_loop_or_climb_classical
#print axioms Motion.not_not_loop_or_climb_of_corner
#print axioms Motion.corner_overAtLanding
#print axioms Motion.corner_step_moves
#print axioms Motion.climb_three
#print axioms unique_succ_covBy
#print axioms botIntervalTwo_botCovered
#print axioms botCovered_botIntervalTwo
#print axioms botCovered_botIntervalTwo_classical
#print axioms wem_of_botCovered_botIntervalTwo
#print axioms everyStepCovered_botCovered
#print axioms Motion.UpStepInvariant
#print axioms Motion.IsRun
#print axioms Motion.StageClosure
#print axioms Motion.up_run_const
#print axioms Motion.stageClosure_of_run
#print axioms Motion.StageClosure.isLanding_of_mem
#print axioms Motion.StageClosure.not_mem_of_mem
#print axioms Motion.StageClosure.unique
#print axioms Motion.RunsClose
#print axioms Motion.RunClosure
#print axioms Motion.runsClose_of_upStepInvariant
#print axioms Motion.RunClosure.stageClosure
#print axioms Motion.RegisteredComputable
#print axioms Motion.RegisteredDecidable
#print axioms Motion.ofOption
#print axioms Motion.registeredDecidable_of_upTotal
#print axioms Motion.ofOption_registeredDecidable
#print axioms Motion.registeredDecidable_of_registeredComputable
#print axioms Motion.registeredDecidable_of_classical
#print axioms Motion.em_of_registeredDecidable
#print axioms Motion.registeredComputable_of_upTotal
#print axioms Motion.ofOption_registeredComputable
#print axioms Motion.SelectedData
#print axioms Motion.SelectedTotal
#print axioms Motion.selectedData_of_selectedTotal
#print axioms Motion.selectedTotal_of_selectedData
#print axioms Motion.selectedTotal_of_classical
#print axioms Motion.em_of_selectedData
#print axioms Motion.selectedTotal_of_fun
#print axioms Motion.selectedTotal_of_option
#print axioms Motion.NoStepAt
#print axioms Motion.SelfOnlyAt
#print axioms Motion.LeavesAt
#print axioms Motion.OverTrichotomy
#print axioms Motion.overTrichotomy_of_option
#print axioms Motion.corner_leavesAt
#print axioms Motion.FanIn
#print axioms Motion.reverse
#print axioms Motion.reverse_up
#print axioms Motion.reverse_reverse
#print axioms Motion.fanIn_iff_reverse
#print axioms Motion.not_fanIn_of_injective
#print axioms Motion.bijOn_sources_sinks
#print axioms Motion.mem_up_self_of_mem_up
#print axioms Motion.not_selfOnlyAt_and_leavesAt
#print axioms Motion.not_climb_of_upStepInvariant
#print axioms Motion.ofFun
#print axioms Motion.selfOnlyAt_ofFun_iff
#print axioms Motion.leavesAt_ofFun_iff
#print axioms Motion.leavesAt_ofFun_not
#print axioms Motion.ofFixedPoints
#print axioms Motion.isLanding_ofFixedPoints_iff
#print axioms Motion.not_corner_of_fun
#print axioms Motion.not_corner_ofFixedPoints
#print axioms Motion.corner_ofTotal_iff
#print axioms Motion.ofPartialFun
#print axioms Motion.noStepAt_ofPartialFun_iff
#print axioms Motion.selfOnlyAt_ofPartialFun_iff
#print axioms Motion.leavesAt_ofPartialFun_iff
#print axioms Motion.Elbow
#print axioms Motion.corner_elbow_of_over_up_over
#print axioms Motion.corner_elbow_of_up_over_up
#print axioms Motion.elbow_reverse_iff
#print axioms Motion.corner_reverse_iff
#print axioms Motion.UpRaises
#print axioms Motion.UpLowers
#print axioms Motion.StepRaises
#print axioms Motion.StepLowers
#print axioms Motion.Agree
#print axioms Motion.Oppose
#print axioms Motion.upRaises_dual
#print axioms Motion.stepRaises_dual
#print axioms Motion.agree_dual
#print axioms Motion.oppose_dual
#print axioms Motion.upRaises_reverse
#print axioms Motion.upLowers_reverse
#print axioms Motion.stepRaises_reverse
#print axioms Motion.agree_dual_reverse_iff
#print axioms Motion.not_loop_of_agree
#print axioms Motion.selfOnlyAt_of_step_self
#print axioms Motion.eq_of_step_le_of_stepRaises
#print axioms Motion.eq_bot_of_step_to_bot
#print axioms Motion.eq_bot_of_step_from_bot
#print axioms Motion.not_exists_involution_reverses_lt
#print axioms Motion.reverse_ofFun_of_injective
#print axioms Motion.eq_of_step_to_isEmpty
#print axioms Motion.eq_of_step_to_ofFun_iff_iterate
#print axioms Motion.rank_add_one_le_of_transGen
#print axioms Motion.rank_eq_top_of_cycle
#print axioms Motion.eq_of_step_self_of_rank
#print axioms Motion.not_cycle_of_nat_rank
#print axioms Motion.selfOnlyAt_ofFun_lfp
#print axioms Motion.not_monotone_of_forall_leavesAt
#print axioms Motion.semiconj_iff_exists_relHom
#print axioms Motion.isEmpty_relHom_of_step_self
#print axioms Motion.selfOnlyAt_relHom
#print axioms Motion.stepRaises_iff_of_dual
#print axioms Motion.upRaises_iff_of_dual
#print axioms Motion.eq_of_step_from_of_stepLowers
#print axioms Motion.eq_of_step_from_of_stepRaises
#print axioms Motion.UpClosed
#print axioms Motion.StepClosed
#print axioms Motion.restrict
#print axioms Motion.mem_restrict_up
#print axioms Motion.restrict_isLanding_iff
#print axioms Motion.restrict_step_iff
#print axioms Motion.restrict_step_complete
#print axioms Motion.restrictVal
#print axioms Motion.restrictVal_up
#print axioms Motion.restrictInclusion
#print axioms Motion.restrictInclusion_up
#print axioms Motion.upClosed_Ici
#print axioms Motion.stepClosed_Ici
#print axioms Motion.restrict_stepRaises_Ici
#print axioms Motion.subsingleton_of_isEmpty
#print axioms isBot_and_isTop_iff
#print axioms withBot_bot_isBot_and_isTop_iff
#print axioms withTop_top_isBot_and_isTop_iff
#print axioms botCovered_withBot_iff
#print axioms botCovered_withTop_iff
#print axioms isEmpty_orderBot_and_orderTop
#print axioms Motion.Arrives
#print axioms Motion.reflTransGen_of_arrives
#print axioms Motion.exists_run_eq_of_arrives
#print axioms Motion.arrives_ofFun_iff
#print axioms Motion.iterate_of_reflTransGen_ofFun
#print axioms Motion.arrives_ofFun_iff_reflTransGen
#print axioms Motion.eq_of_reflTransGen_of_noEntry
#print axioms Motion.not_noEntry_of_arrives
#print axioms Motion.noEntry_ofFun_iff_arrives
#print axioms Motion.eq_of_noEntry_of_forall_arrives
#print axioms Motion.acc_of_arrives
#print axioms Motion.arrives_of_acc
#print axioms Motion.arrives_of_forall_run
#print axioms Motion.arrives_iff_forall_run
#print axioms Motion.reach_and_stay_iff
#print axioms Motion.not_arrives_of_stageClosure
#print axioms Motion.reverse_ofFun_subsingleton_iff
#print axioms Motion.reverse_ofFun_total_iff
#print axioms Motion.not_fanIn_ofFun_iff_injective
#print axioms Motion.reverse_ofFun_isFun_iff_bijective
#print axioms Motion.exists_fanIn_ofFun_of_not_injective
#print axioms Motion.not_noEntry_of_fanIn
#print axioms Motion.fanIn_ofFun_of_arrives
#print axioms Motion.eq_of_arrives_ofFun_of_injective
#print axioms Motion.selfOnlyAt_or_step_self_and_leavesAt
#print axioms Motion.not_step_self_and_leavesAt_of_subsingleton
#print axioms Motion.two_successors_of_step_self_and_leavesAt
#print axioms Motion.not_step_self_and_leavesAt_ofFun
#print axioms Motion.eq_of_reflTransGen_of_selfOnlyAt
#print axioms Motion.run_const_of_selfOnlyAt
#print axioms Motion.rank_eq_top_of_reflTransGen_selfOnlyAt
#print axioms Motion.not_acc_of_cycle
#print axioms Motion.acc_of_reflTransGen
#print axioms Motion.not_acc_iff_reaches_cycle
#print axioms Motion.acc_of_rank_ne_top
#print axioms Motion.rank_eq_top_of_not_acc
#print axioms Motion.accHeight
#print axioms Motion.accHeight_ne_top_iff
#print axioms Motion.accHeight_drops
#print axioms Motion.forall_rank_eq_top_iff_not_acc
#print axioms Motion.fixed_iff_of_relIso
#print axioms PoleEnds
#print axioms poleEnds_unique
#print axioms poleEnds_of_dual
#print axioms poleEnds_dual
#print axioms poleEnds_dual_cells
#print axioms ends_ne_iff_nontrivial
#print axioms Motion.Closed
#print axioms Motion.closedSublattice
#print axioms Motion.restrictInclusion_refl
#print axioms Motion.restrictInclusion_trans
#print axioms Motion.instLE
#print axioms Motion.instPartialOrder
#print axioms Motion.leHom
#print axioms Motion.isLanding_iff_of_le
#print axioms Motion.noEntry_anti
#print axioms Motion.noExit_anti
#print axioms Motion.noStepAt_anti
#print axioms Motion.leavesAt_mono
#print axioms Motion.fanIn_mono
#print axioms Motion.corner_mono
#print axioms Motion.climb_mono
#print axioms Motion.reverse_le_iff
#print axioms PoleEndsInhabited
#print axioms poleEndsInhabited_unique
#print axioms poleEndsInhabited_dual
#print axioms poleEndsInhabited_of_end
#print axioms Motion.arrives_of_reflTransGen_of_det
#print axioms Motion.noEntry_iff_noReach
#print axioms Motion.StepCompat
#print axioms Motion.quot
#print axioms Motion.quotHom
#print axioms Motion.quot_step_mk_iff
#print axioms Motion.quot_selfOnlyAt_mk_iff
#print axioms Motion.stepCompat_ofFun
#print axioms Motion.quot_ofFun_step_iff
#print axioms Motion.UpCompat
#print axioms Motion.upCompat_map_eq
#print axioms Motion.quotUp
#print axioms Motion.mem_quotUp_up_mk_iff
#print axioms Motion.isLanding_quotUp_mk_iff
#print axioms Motion.isLanding_quotUp_mk
#print axioms Motion.quotUp_step
#print axioms Motion.upCompat_of_up_eq_some
#print axioms Motion.quotUp_eq_quot
#print axioms Motion.upCompat_ofTotal
#print axioms Motion.em_of_corner_loop_or_climb
#print axioms everyStepCovered_of_finite
#print axioms botCovered_of_finite
#print axioms Motion.three_of_not_runClose
#print axioms Motion.four_of_not_runClose
#print axioms Motion.lpo_of_selectedTotal_nat_boolStep
#print axioms Motion.lpo_of_trichotomy_nat_boolStep
#print axioms Motion.exists_fanIn_bool
#print axioms Motion.mp_of_exists_fanIn_nat
#print axioms Motion.UpLax
#print axioms Motion.UpStrict
#print axioms Motion.StepBack
#print axioms Motion.Hom
#print axioms Motion.LaxHom
#print axioms Motion.upLax_iff_le
#print axioms Motion.upStrict_upLax
#print axioms Motion.upStrict_iff
#print axioms Motion.upStrict_of_upLax_of_upTotal
#print axioms Motion.Hom.toLax
#print axioms Motion.LaxHom.toHomOfUpTotal
#print axioms Motion.Hom.id
#print axioms Motion.Hom.comp
#print axioms Motion.Hom.id_comp
#print axioms Motion.Hom.comp_id
#print axioms Motion.Hom.comp_assoc
#print axioms Motion.LaxHom.id
#print axioms Motion.LaxHom.comp
#print axioms Motion.Hom.toLax_comp
#print axioms Motion.Hom.reverse
#print axioms Motion.Hom.reverse_reverse
#print axioms Motion.Hom.reverse_comp
#print axioms Motion.ofRelHomIdUp
#print axioms Motion.semiconj_iff_exists_hom
#print axioms Motion.stepBack_ofFun
#print axioms Motion.LaxHom.isLanding
#print axioms Motion.LaxHom.hasLanding
#print axioms Motion.LaxHom.overAtLanding
#print axioms Motion.LaxHom.upTotal
#print axioms Motion.LaxHom.corner
#print axioms Motion.LaxHom.loop
#print axioms Motion.LaxHom.climb
#print axioms Motion.LaxHom.elbow
#print axioms Motion.LaxHom.leavesAt
#print axioms Motion.LaxHom.fanIn
#print axioms Motion.LaxHom.noStepAt_of_image
#print axioms Motion.LaxHom.noStepAt
#print axioms Motion.LaxHom.selfOnlyAt
#print axioms Motion.LaxHom.leavesAt_of_image
#print axioms Motion.LaxHom.selfOnlyAt_of_image
#print axioms Motion.LaxHom.arrives
#print axioms Motion.Hom.upTotal_of
#print axioms Motion.Hom.isLanding_of_image

end PurityCheck
