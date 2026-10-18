import Mathlib.Order.Cover
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.PFun
import Mathlib.Logic.Relation
import Mathlib.Computability.Partrec
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
    relation `step`. `Reading:` UP is `up`, OVER is `step`; a landing is a fixed point of `up`. UP
    is an idempotent of the monoid of partial endofunctions (Cockett and Hofstra, APAL 156 (2008),
    p. 187, Example (iii)), inside Par; it need not be a restriction idempotent, which in Par are
    the partial identities (p. 186): the identity UP is one, the `Bool` control below is not. -/
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

/-- `Statement:` a cover at every non-maximal point, and a point other than ⊥ of `α`, give a cover
    of ⊥ of `α`. -/
theorem everyStepCovered_botCovered (h : EveryStepCovered α) (hne : ∃ a : α, a ≠ ⊥) :
    BotCovered α :=
  let ⟨_, ha⟩ := hne
  h ⊥ fun hm => ha (le_bot_iff.mp (hm bot_le))

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

/-- `Statement:` no step leaves `y`. -/
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

/-- `Statement:` a corner leaves its landing. -/
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

/-- `Statement:` a value `z` of `up` is an `up`-preimage of itself. -/
theorem mem_up_self_of_mem_up {x z : α} (h : z ∈ M.up x) : z ∈ M.up z :=
  M.up_idem x z h

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

end PurityCheck
