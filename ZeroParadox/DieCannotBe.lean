import ZeroParadox.Die
import ZeroParadox.Multihomed.BoundaryOrder
import ZeroParadox.Order.Snap
import ZeroParadox.Computability.GroundZero
import ZeroParadox.Valuation.FloorWitness
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Computability.Occurrence
import ZeroParadox.Valuation.PoleRegistration
import ZeroParadox.Valuation.PoleChartSelection
import Mathlib.Data.NNReal.Basic
import Mathlib.CategoryTheory.Category.Bipointed
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.Group.End
import Mathlib.RingTheory.Valuation.PrimeMultiplicity
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Seq.Computation

set_option maxHeartbeats 400000

/-!
# Machine-checked characterization index of the die — its premises, with members and non-members

`#check` lines plus anonymous `example`s; every gloss is `Statement:` or `Reading:`. The premise
set is a starting place: each premise is its own item, no combination is claimed final, and no
carrier is claimed to be the only one meeting them. Definitions: `ZeroParadox/Die.lean`.

## Engineer's Take

We need to collect every premise that we have on the die and test each of them. The premise of
the die is shared unification between different branches of mathematics. Content that could
filter here is more aptly applied in one of the other areas, bottom cannot be, snap cannot be,
and so on. The die should be a unification of the other cannot be files at a meta level, at least
in part. Face level data stays within the other cannot be files, and only the meta objects make
it to the die definition. I think up and over versus the die are the same thing in a real way.
Calling the cannot be under the die just gives us flexibility if other rules turn up.

---
-/

section DieCannotBeIndex

/-! ### § 0. The signature is a record -/
#check @ZeroParadox.Motion                     -- Statement: a partial map `up` whose values are landings, and a relation `step`
-- Statement: every type carries a motion (identity UP, empty step), so membership is uninformative;
-- the premises below carry the content.
example (α : Type) : Nonempty (ZeroParadox.Motion α) :=
  ⟨ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun _ _ => False)⟩
#check @IsIdempotentElem                       -- Statement: Mathlib, `a * a = a`
-- Statement: on `Function.End α` (composition), a total map is an idempotent element iff `f (f x) = f x`.
example {α : Type} (f : α → α) : IsIdempotentElem (show Function.End α from f) ↔ ∀ x, f (f x) = f x :=
  ⟨fun h x => congrFun h x, fun h => funext h⟩
#check @PFun                                    -- Statement: Mathlib, partial functions `α →. β`

/-! ### § I. The switches -/
-- Reading (cited, not claimed): UP beside OVER has the shape of rewriting logic's split of equations
-- from rules. "One step, then UP" from a landing is the canonical transition system (Meseguer,
-- "Generalized Rewrite Theories and Coherence Completion", 2018, Def. 8, p. 10) and the relation of
-- Diaconescu, arXiv:2204.12133, Defs. 11–12, so Loop and Climb are properties of one canonical edge.
-- Delta: in Meseguer UP is total, the normal form of a convergent equation system; in Diaconescu
-- (Def. 11) it is a total homomorphism into a subset it fixes, with equations only in his Examples
-- 8–9. Coherence (Meseguer, Theorem 4, p. 11; a hypothesis of Diaconescu's Props. 5.1 and 5.5) is
-- required there for the canonical system to be faithful to the rules, and is not imposed here; the
-- switches have no located counterpart.
-- Reading: the adjoined-points switch is a CHOICE OF CARRIER: `Option σ` adjoins one point and
-- `Option (Option σ)` two (the `TriStep` example below). `Pointed` and `Bipointed` carry
-- distinguished points, not adjoined ones, and `Bipointed`'s two may coincide.
#check @Pointed                                 -- Statement: Mathlib, a type with one distinguished point
#check @Bipointed                               -- Statement: Mathlib, a type with two distinguished points, possibly equal
#check @Fintype.card_option                     -- Statement: Mathlib, `card (Option α) = card α + 1`
-- Statement: `TriStep σ` is `σ` with two adjoined points.
example (σ : Type) : ZeroParadox.TriStep σ ≃ Option (Option σ) where
  toFun t := match t with
    | .halted => none
    | .idle => some none
    | .step s => some (some s)
  invFun o := match o with
    | none => .halted
    | some none => .idle
    | some (some s) => .step s
  left_inv t := by cases t <;> rfl
  right_inv o := by rcases o with _ | _ | s <;> rfl
#check @ZeroParadox.Motion.UpTotal              -- Statement: UP switch at total: `up` defined everywhere
-- Statement: member and non-member: `ofTotal`; and UP undefined everywhere.
#check @ZeroParadox.Motion.ofTotal_upTotal
example : ∃ M : ZeroParadox.Motion ℕ, (∀ x, M.up x = Part.none) ∧ ¬ M.UpTotal :=
  ⟨⟨fun _ => Part.none, fun _ _ h => absurd h (Part.notMem_none _), fun _ _ => False⟩,
    fun _ => rfl, fun h => h 0⟩
#check @ZeroParadox.Motion.Climb                -- Statement: loop/climb switch at climb
#check @ZeroParadox.Motion.Loop                 -- Statement: loop/climb switch at loop
-- Statement: CLIMB member: on ℕ, UP rounds up to even, OVER adds one; from the landing 0, step to 1, UP to 2.
example : ∃ M : ZeroParadox.Motion ℕ, (∀ n, M.up n = Part.some (n + n % 2)) ∧
    (∀ a b, M.step a b ↔ b = a + 1) ∧ M.UpTotal ∧ M.Climb :=
  ⟨ZeroParadox.Motion.ofTotal (fun n => n + n % 2)
      (fun n => show (n + n % 2) + (n + n % 2) % 2 = n + n % 2 by omega) (fun a b => b = a + 1),
    fun _ => rfl, fun _ _ => Iff.rfl, ZeroParadox.Motion.ofTotal_upTotal _ _ _,
    ⟨0, 1, 2, Part.mem_some_iff.2 (by decide), rfl, Part.mem_some_iff.2 (by decide),
      by decide, by decide⟩⟩
-- Statement: LOOP member, and CLIMB non-member: on `Bool`, UP constant `true`, OVER `≠`; no motion on
-- `Bool` climbs.
example : ∃ M : ZeroParadox.Motion Bool, (∀ x, M.up x = Part.some true) ∧ (∀ a b, M.step a b ↔ a ≠ b) ∧
    M.Loop :=
  ⟨ZeroParadox.Motion.ofTotal (fun _ => true) (fun _ => rfl) (fun a b => a ≠ b), fun _ => rfl,
    fun _ _ => Iff.rfl, ⟨true, false, Part.mem_some_iff.2 rfl, (Bool.false_ne_true).symm,
      Bool.false_ne_true, Part.mem_some_iff.2 rfl⟩⟩
example : ∀ M : ZeroParadox.Motion Bool, ¬ M.Climb := fun M h => by
  obtain ⟨y, b, z, h1, h2, h3⟩ := M.climb_three h
  revert h1 h2 h3; cases y <;> cases b <;> cases z <;> decide
-- Statement: LOOP non-member: the identity UP with any step never loops.
example {α : Type} (s : α → α → Prop) : ¬ (ZeroParadox.Motion.ofTotal id (fun _ => rfl) s).Loop :=
  fun ⟨_, _, _, _, hby, hyb⟩ => hby (Part.mem_some_iff.1 hyb).symm
#check @ZeroParadox.Motion.climb_three          -- Statement: a climb gives three distinct points
-- Statement: the two switch values are not exclusive: on `Fin 4`, UP `1 ↦ 0`, `2 ↦ 3`, OVER `0 → 1`,
-- `0 → 2`; from the landing 0 one step loops back, the other climbs.
example : ∃ M : ZeroParadox.Motion (Fin 4),
    (∀ x, M.up x = Part.some (if x = 1 then 0 else if x = 2 then 3 else x)) ∧
    (∀ a b, M.step a b ↔ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2)) ∧ M.Loop ∧ M.Climb :=
  ⟨ZeroParadox.Motion.ofTotal (fun x : Fin 4 => if x = 1 then 0 else if x = 2 then 3 else x)
      (by decide) (fun a b => (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2)),
    fun _ => rfl, fun _ _ => Iff.rfl,
    ⟨0, 1, Part.mem_some_iff.2 (by decide), Or.inl ⟨rfl, rfl⟩, by decide,
      Part.mem_some_iff.2 (by decide)⟩,
    ⟨0, 2, 3, Part.mem_some_iff.2 (by decide), Or.inr ⟨rfl, rfl⟩, Part.mem_some_iff.2 (by decide),
      by decide, by decide⟩⟩

/-! ### § II. Premises on a motion — existence of a leg, never its use -/
#check @ZeroParadox.Motion.HasLanding           -- Statement: some landing exists
-- Statement: members of `HasLanding`, `OverAtLanding` and `Corner`: on ℕ, UP rounds up to even and
-- OVER adds one; 0 is a landing, OVER goes 0 → 1, and UP sends 1 to 2.
example : ∃ M : ZeroParadox.Motion ℕ, (∀ n, M.up n = Part.some (n + n % 2)) ∧
    (∀ a b, M.step a b ↔ b = a + 1) ∧ M.HasLanding ∧ M.OverAtLanding ∧ M.Corner :=
  ⟨ZeroParadox.Motion.ofTotal (fun n => n + n % 2)
      (fun n => show (n + n % 2) + (n + n % 2) % 2 = n + n % 2 by omega) (fun a b => b = a + 1),
    fun _ => rfl, fun _ _ => Iff.rfl, ⟨0, Part.mem_some_iff.2 (by decide)⟩,
    ⟨0, 1, Part.mem_some_iff.2 (by decide), rfl⟩,
    ⟨0, 1, 2, Part.mem_some_iff.2 (by decide), rfl, Part.mem_some_iff.2 (by decide), by decide⟩⟩
-- Statement: non-member: UP undefined everywhere.
example : ∃ M : ZeroParadox.Motion ℕ, (∀ x, M.up x = Part.none) ∧ ¬ M.HasLanding :=
  ⟨⟨fun _ => Part.none, fun _ _ h => absurd h (Part.notMem_none _), fun _ _ => False⟩,
    fun _ => rfl, fun ⟨_, hy⟩ => Part.notMem_none _ hy⟩
#check @ZeroParadox.Motion.OverAtLanding        -- Statement: OVER exists from some landing
-- Statement: non-member: the empty step relation, any UP.
example {α : Type} (u : α →. α) (h : ∀ x y, y ∈ u x → y ∈ u y) :
    ¬ (⟨u, h, fun _ _ => False⟩ : ZeroParadox.Motion α).OverAtLanding :=
  fun ⟨_, _, _, hs⟩ => hs
#check @ZeroParadox.Motion.Corner               -- Statement: the corner
#check @ZeroParadox.Motion.corner_overAtLanding -- Statement: corner ⇒ OVER at a landing; one way
-- Statement: non-members: `Unit`, and the identity UP with any step.
example : ∀ M : ZeroParadox.Motion Unit, ¬ M.Corner :=
  fun _ ⟨_, _, _, _, _, _, hzb⟩ => hzb (Subsingleton.elim _ _)
example {α : Type} (s : α → α → Prop) : ¬ (ZeroParadox.Motion.ofTotal id (fun _ => rfl) s).Corner :=
  fun ⟨_, _, _, _, _, hz, hzb⟩ => hzb (Part.mem_some_iff.1 hz)
#check @ZeroParadox.Motion.OverToUndefined      -- Statement: from a landing, OVER into a point where UP is undefined
-- Statement: member: on ℕ, UP defined on evens only, OVER adds one; from 0, step to 1, UP undefined.
example : ∃ M : ZeroParadox.Motion ℕ, (∀ n, M.up n = if n % 2 = 0 then Part.some n else Part.none) ∧
    (∀ a b, M.step a b ↔ b = a + 1) ∧ M.OverToUndefined :=
  ⟨⟨fun n => if n % 2 = 0 then Part.some n else Part.none, fun x y h => by
      beta_reduce at h ⊢
      by_cases hx : x % 2 = 0
      · rw [if_pos hx, Part.mem_some_iff] at h
        subst h
        rw [if_pos hx]
        exact Part.mem_some _
      · rw [if_neg hx] at h
        exact absurd h (Part.notMem_none _),
    fun a b => b = a + 1⟩, fun _ => rfl, fun _ _ => Iff.rfl,
    ⟨0, 1, by show 0 ∈ (if 0 % 2 = 0 then Part.some 0 else Part.none); rw [if_pos rfl]; exact Part.mem_some _,
      rfl, by show ¬ (if 1 % 2 = 0 then Part.some 1 else Part.none).Dom; rw [if_neg (by decide)]; exact id⟩⟩
#check @ZeroParadox.Motion.not_overToUndefined_of_upTotal -- Statement: non-members: every total motion
-- Reading: two corpus usages sit beside this name, and neither is claimed here: divergence read as the
-- infinite pole (`ZeroParadox/Computability/Occurrence.lean`'s overview; `wfPart_stepCoalg`'s
-- `Reading:` in `ZeroParadox/Computability/GroundZero.lean`, conjectural), and
-- `ZeroParadox/Computability/Occurrence.lean` § IV-c's two-element pole {halted, loops-in-place}.

/-! ### § III. The smallest step is DERIVED — unique successor, no way back ⇒ cover, one way -/
#check @ZeroParadox.unique_succ_covBy           -- Statement: unique successor, no way back ⇒ a cover of the reachability preorder
-- Reading: the closest classical frame is transitive reduction (Aho, Garey and Ullman, SIAM J. Comput.
-- 1(2):131–137, 1972, doi 10.1137/0201008; cited, not retrieved). On a finite acyclic relation this
-- lemma is the single-successor case of the standard criterion that an edge is in the reduction when
-- it is the only path between its endpoints; the lemma itself assumes neither finiteness nor acyclicity.
-- Statement: on `Fin 3` with steps `0 → 1`, `1 → 2`, `2 → 1` (a cycle), `unique_succ_covBy` gives
-- `0 ⋖ 1` in the reachability preorder.
example : let R : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
    @CovBy (Fin 3) (ZeroParadox.reachPreorder R).toLT 0 1 := by
  intro R
  have back : ∀ a b, Relation.ReflTransGen R a b → b = 0 → a = 0 := by
    intro a b h
    induction h with
    | refl => exact id
    | tail _ hcd _ =>
      intro hd; subst hd
      rcases hcd with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  exact ZeroParadox.unique_succ_covBy R (Or.inl ⟨rfl, rfl⟩)
    (fun c hc => by
      rcases hc with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | exact absurd h (by decide))
    (fun h => absurd (back _ _ h rfl) (by decide))
-- Statement: there `0 ⋖ 2` also holds, with no step `0 → 2`.
example : let R : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)
    @CovBy (Fin 3) (ZeroParadox.reachPreorder R).toLT 0 2 ∧ ¬ R 0 2 := by
  intro R
  have back : ∀ a b, Relation.ReflTransGen R a b → b = 0 → a = 0 := by
    intro a b h
    induction h with
    | refl => exact id
    | tail _ hcd _ =>
      intro hd; subst hd
      rcases hcd with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  have r02 : Relation.ReflTransGen R 0 2 := Relation.ReflTransGen.head (Or.inl ⟨rfl, rfl⟩)
    (Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine ⟨⟨⟨r02, fun h => absurd (back _ _ h rfl) (by decide)⟩, fun c h0c hc2 => ?_⟩, ?_⟩
  · fin_cases c
    · exact h0c.2 Relation.ReflTransGen.refl
    · exact hc2.2 (Relation.ReflTransGen.single (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    · exact hc2.2 Relation.ReflTransGen.refl
  · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)
-- Statement: the converse fails: on `Fin 3` with `0 → 1` and `0 → 2`, `0 ⋖ 1` in the reachability
-- preorder while `0` has two successors.
example : let R : Fin 3 → Fin 3 → Prop := fun a b => (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2)
    @CovBy (Fin 3) (ZeroParadox.reachPreorder R).toLT 0 1 ∧ R 0 1 ∧ R 0 2 := by
  intro R
  have key : ∀ a b, Relation.ReflTransGen R a b → a = b ∨ a = 0 := by
    intro a b h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hcd ih =>
      obtain ⟨hc, -⟩ | ⟨hc, -⟩ := hcd <;> rcases ih with h | h <;>
        first | exact Or.inr (h.trans hc) | exact Or.inr h
  refine ⟨⟨⟨Relation.ReflTransGen.single (Or.inl ⟨rfl, rfl⟩), fun h => ?_⟩, fun c h0c hc1 => ?_⟩,
    Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · rcases key _ _ h with h | h <;> exact absurd h (by decide)
  · rcases key _ _ hc1.1 with h | h
    · subst h; exact hc1.2 Relation.ReflTransGen.refl
    · subst h; exact h0c.2 Relation.ReflTransGen.refl
-- Statement: and two routes `0 → 1 → 2`, `0 → 2` do not make `0 ⋖ 2`.
example : ¬ @CovBy (Fin 3) (ZeroParadox.reachPreorder (fun a b : Fin 3 =>
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 2))).toLT 0 2 := by
  intro h
  let R := fun a b : Fin 3 => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 0 ∧ b = 2)
  have mono : ∀ a b, Relation.ReflTransGen R a b → a ≤ b := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | tail _ hst ih =>
      rename_i c d
      refine ih.trans ?_
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  refine h.2 (c := 1) ⟨Relation.ReflTransGen.single (Or.inl ⟨rfl, rfl⟩), fun h' => ?_⟩
    ⟨Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩)), fun h' => ?_⟩
  · exact absurd (mono _ _ h') (by decide)
  · exact absurd (mono _ _ h') (by decide)
#check @le_iff_reflTransGen_covBy               -- Statement: Mathlib, in a locally finite partial order `≤` is the reflexive transitive closure of `⋖`
#check @SimpleGraph.hasse                       -- Statement: Mathlib, the Hasse diagram as an undirected graph: `a`, `b` adjacent iff `a ⋖ b ∨ b ⋖ a`
#check @ZeroParadox.deterministic_has_no_fanout -- Statement: a step function has at most one successor

/-! ### § IV. Order premises — general `[PartialOrder α] [OrderBot α]`, then ZP-A's induced order -/
#check @ZeroParadox.BotCovered                  -- Statement: ⊥ of `α` has a cover. Reading: AX-B1's cut
example {α : Type} [PartialOrder α] [OrderBot α] :
    ZeroParadox.BotCovered α ↔ ZeroParadox.HasFirstStep (⊥ : α) := Iff.rfl
#check @bot_covBy_iff                           -- Statement: Mathlib, `⊥ ⋖ a ↔ IsAtom a`
-- Statement: so `BotCovered α` says an atom of `α` exists.
example {α : Type} [PartialOrder α] [OrderBot α] : ZeroParadox.BotCovered α ↔ ∃ a : α, IsAtom a :=
  ⟨fun ⟨a, h⟩ => ⟨a, bot_covBy_iff.1 h⟩, fun ⟨a, h⟩ => ⟨a, bot_covBy_iff.2 h⟩⟩
-- Statement: members `Bool`, ℕ; non-members `Unit`, `NNReal`.
example : ZeroParadox.BotCovered Bool ∧ ZeroParadox.BotCovered ℕ :=
  ⟨⟨true, covBy_of_eq_or_eq (by decide) fun c _ _ => by cases c <;> decide⟩,
    ⟨_, Order.covBy_succ (⊥ : ℕ)⟩⟩
example : ¬ ZeroParadox.BotCovered Unit ∧ ¬ ZeroParadox.BotCovered NNReal :=
  ⟨fun ⟨_, h⟩ => h.lt.ne (Subsingleton.elim _ _), fun ⟨_, h⟩ => not_covBy h⟩
#check @ZeroParadox.BotIntervalTwo              -- Statement: some `a` above ⊥ of `α` has `[⊥, a] = {⊥, a}`. Reading: AX-B1's piece
-- Statement: members `Bool`, `Fin 3`; non-members `Unit`, `NNReal`.
example : ZeroParadox.BotIntervalTwo Bool ∧ ZeroParadox.BotIntervalTwo (Fin 3) :=
  ⟨⟨true, by decide, fun c _ => by cases c <;> decide⟩, ⟨1, by decide, by decide⟩⟩
example : ¬ ZeroParadox.BotIntervalTwo Unit ∧ ¬ ZeroParadox.BotIntervalTwo NNReal :=
  ⟨fun ⟨_, h, _⟩ => h.ne (Subsingleton.elim _ _),
    fun h => let ⟨_, hc⟩ := ZeroParadox.botIntervalTwo_botCovered h; not_covBy hc⟩
#check @ZeroParadox.botIntervalTwo_botCovered   -- Statement: piece ⇒ cut, no hypothesis
#check @ZeroParadox.botCovered_botIntervalTwo   -- Statement: cut ⇒ piece, given `DecidableEq`
#check @ZeroParadox.botCovered_botIntervalTwo_classical -- Statement: cut ⇒ piece with no binder, proved with `classical`
-- Reading: decidable equality is the cost of this direction: the `DecidableEq` form depends on no
-- axioms and the `classical` form on `Classical.choice` (both printed in `ZeroParadox/Die.lean`'s
-- PurityCheck).
#check @CovBy.eq_or_eq                          -- Statement: Mathlib, `a ⋖ b → a ≤ c → c ≤ b → c = a ∨ c = b`; its footprint is printed next
#print axioms CovBy.eq_or_eq
#check @CovBy.Icc_eq                            -- Statement: Mathlib, `a ⋖ b → Set.Icc a b = {a, b}`
#check @ZeroParadox.EveryStepCovered            -- Statement: every non-maximal point of `α` has a cover. Reading: AX-B1's scope form
-- Statement: Mathlib's `IsStronglyAtomic` (every `a < b` has `a ⋖ x ≤ b`) gives it; one way, and the
-- converse is not tested here.
example {α : Type} [PartialOrder α] [IsStronglyAtomic α] : ZeroParadox.EveryStepCovered α :=
  fun x hx => by
    obtain ⟨b, hb⟩ := not_isMax_iff.1 hx
    obtain ⟨c, hc, -⟩ := exists_covBy_le_of_lt hb
    exact ⟨c, hc⟩
-- Statement: member ℕ; non-member `WithBot (WithBot ℚ)`, which has the cut at ⊥ of
-- `WithBot (WithBot ℚ)`.
example : ZeroParadox.EveryStepCovered ℕ := fun x _ => ⟨_, Order.covBy_succ x⟩
example : ZeroParadox.BotCovered (WithBot (WithBot ℚ)) ∧
    ¬ ZeroParadox.EveryStepCovered (WithBot (WithBot ℚ)) := by
  refine ⟨⟨((⊥ : WithBot ℚ) : WithBot (WithBot ℚ)), covBy_of_eq_or_eq (WithBot.bot_lt_coe _)
    fun c _ hc => ?_⟩, fun h => ?_⟩
  · induction c using WithBot.recBotCoe with
    | bot => exact Or.inl rfl
    | coe c => exact Or.inr (congrArg _ (le_bot_iff.mp (WithBot.coe_le_coe.mp hc)))
  · obtain ⟨b, hb⟩ := h ((⊥ : WithBot ℚ) : WithBot (WithBot ℚ))
      (not_isMax_of_lt (WithBot.coe_lt_coe.2 (WithBot.bot_lt_coe (0 : ℚ))))
    induction b using WithBot.recBotCoe with
    | bot => exact not_lt_bot hb.lt
    | coe b =>
      have hb' := WithBot.coe_covBy_coe.mp hb
      induction b using WithBot.recBotCoe with
      | bot => exact lt_irrefl _ hb'.lt
      | coe q =>
        exact hb'.2 (WithBot.bot_lt_coe (q - 1)) (WithBot.coe_lt_coe.2 (by linarith))
#check @ZeroParadox.everyStepCovered_botCovered -- Statement: scope form, plus a point other than ⊥ of `α`, ⇒ cut; one way
#check @ZeroParadox.UniqueBotCover              -- Statement: ⊥ of `α` has at most one cover
-- Statement: members `Bool`, `Fin 3`; non-member `Set Bool` (`∅` is covered by `{true}` and `{false}`).
example : ZeroParadox.UniqueBotCover Bool ∧ ZeroParadox.UniqueBotCover (Fin 3) := by
  refine ⟨fun a b ha hb => ?_, fun a b ha hb => ?_⟩
  · have key : ∀ x : Bool, (⊥ : Bool) ⋖ x → x = true := fun x hx => by
      cases x
      · exact absurd hx.lt (by decide)
      · rfl
    rw [key a ha, key b hb]
  · have key : ∀ x : Fin 3, (⊥ : Fin 3) ⋖ x → x = 1 := fun x hx => by
      fin_cases x
      · exact absurd hx.lt (by decide)
      · rfl
      · exact absurd (hx.2 (show (⊥ : Fin 3) < 1 by decide) (show (1 : Fin 3) < 2 by decide)) id
    rw [key a ha, key b hb]
example : ¬ ZeroParadox.UniqueBotCover (Set Bool) := fun h =>
  absurd (h _ _ (Set.empty_covBy_singleton true) (Set.empty_covBy_singleton false))
    (fun h' => absurd (h' ▸ Set.mem_singleton true) (by simp))
#check @NoMaxOrder                              -- Statement: Mathlib, no maximal point (the no-top premise)
-- Statement: member ℕ; non-members `Fin 3`, `Bool`.
example : NoMaxOrder ℕ := inferInstance
example : ¬ NoMaxOrder (Fin 3) ∧ ¬ NoMaxOrder Bool := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨b, hb⟩ := @exists_gt _ _ h (2 : Fin 3)
    revert hb; revert b; decide
  · obtain ⟨b, hb⟩ := @exists_gt _ _ h true
    revert hb; revert b; decide
-- Statement: ZP-A's induced order on `MachinePhase`: ⊥ of `MachinePhase` is `c₀` and is covered,
-- `c₁` is maximal, and `NoMaxOrder` fails.
example : letI := ZeroParadox.zpSemilatticeSup ZeroParadox.MachinePhase
    letI := ZeroParadox.zpOrderBot ZeroParadox.MachinePhase
    (⊥ : ZeroParadox.MachinePhase) = ZeroParadox.c₀ ∧ ZeroParadox.BotCovered ZeroParadox.MachinePhase ∧
      IsMax ZeroParadox.c₁ ∧ ¬ NoMaxOrder ZeroParadox.MachinePhase := by
  letI := ZeroParadox.zpSemilatticeSup ZeroParadox.MachinePhase
  letI := ZeroParadox.zpOrderBot ZeroParadox.MachinePhase
  refine ⟨rfl, ⟨ZeroParadox.c₁, ⟨rfl, by decide⟩, fun c h1 h2 => ?_⟩, fun b _ => ?_, fun h => ?_⟩
  · cases c
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h2
  · cases b
    · show ZeroParadox.ZPSemilattice.join ZeroParadox.c₀ ZeroParadox.c₁ = ZeroParadox.c₁; rfl
    · exact le_rfl
  · obtain ⟨b, hb⟩ := @exists_gt _ _ h ZeroParadox.c₁
    cases b
    · exact absurd hb.1 (by decide)
    · exact lt_irrefl _ hb
-- Reading: CARRIER, one boundary model, two orders: below, the floor has a cover; above, the floor
-- is the top and covers nothing.
#check @ZeroParadox.phase_floor_covBy_snap      -- Statement: floor-below order: the floor is covered by the snap
#check @ZeroParadox.phaseEquivWithTop_floor_covers_nothing -- Statement: floor-above order: the floor is top, and covers nothing

/-! ### § V. The up-and-over shape, an order-theoretic presentation -/
#check @ZeroParadox.UpAndOver                   -- Statement: closure, corner, a cover at every non-maximal landing
#check @ZeroParadox.ordinalUpAndOver            -- Statement: member `Ordinal`
-- Statement: non-member `Bool`.
example : IsEmpty (ZeroParadox.UpAndOver Bool) := ⟨fun U => by
  obtain ⟨y, b, -, hb, hne⟩ := U.corner
  have hbt : b = true := by
    cases b
    · exact absurd hb.lt (by cases y <;> decide)
    · rfl
  subst hbt
  exact hne U.up.isClosed_top.closure_eq⟩

/-! ### § VI. ℤ_[2]'s 0, two coordinates, both indexed -/
#check @PadicInt.valuation_zero                 -- Statement: Mathlib, `PadicInt.valuation 0 = 0`
-- Reading: a totalization convention.
-- Statement: under that convention ℤ_[2]'s 0 and its unit 1 both read 0.
example : PadicInt.valuation (0 : ℤ_[2]) = 0 ∧ PadicInt.valuation (1 : ℤ_[2]) = 0 :=
  ⟨PadicInt.valuation_zero, PadicInt.valuation_one⟩
#check @ZeroParadox.addVal_bot                  -- Statement: an additive valuation sends 0 to ⊤
-- Statement: at ℤ_[2]'s 0 the ℕ-valued valuation reads 0 and the additive valuation reads ⊤.
-- Reading: the additive valuation presents that 0 as the adjoined top; the natural-number reading 0 is
-- Mathlib's totalization value, shared with every unit.
example : PadicInt.valuation (0 : ℤ_[2]) = 0 ∧
    multiplicity_addValuation PadicInt.prime_p (0 : ℤ_[2]) = ⊤ :=
  ⟨PadicInt.valuation_zero, ZeroParadox.addVal_bot _⟩
-- Statement: every unit of ℤ_[2] reads 0 under the ℕ-valued valuation.
example (u : ℤ_[2]ˣ) : PadicInt.valuation (u : ℤ_[2]) = 0 := by
  have h := PadicInt.valuation_mul u.ne_zero (u⁻¹).ne_zero
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

/-! ### § VII. Runs, beside the die — commitments as hypotheses -/
#check @ZeroParadox.t_snap_given                -- Statement: CC-1 `hcc1` and occurrence `hocc` as hypotheses
#check @ZeroParadox.t_snap_given_cover          -- Statement: and the cover `hcov` as a third
#check @ZeroParadox.tsnap_holds_but_nothing_moves -- Statement: the shape holds where nothing moves

/-! ### § VIII. Stages and one shared closure — two faces, co-witnesses -/
#check @ZeroParadox.Motion.StageClosure         -- Statement: no stage is a landing, and UP sends every stage to one value `c`, possibly undefined
#check @ZeroParadox.Motion.UpStepInvariant      -- Statement: the premise form: UP unchanged along every step
#check @ZeroParadox.Motion.up_run_const         -- Statement: UP unchanged along steps ⇒ UP constant along a run; one way
#check @ZeroParadox.Motion.stageClosure_of_run  -- Statement: and a run with no landing among its stages has the shape
#check @ZeroParadox.Motion.StageClosure.isLanding_of_mem -- Statement: over a nonempty stage set, a defined closure is a landing
#check @ZeroParadox.Motion.StageClosure.not_mem_of_mem -- Statement: over a nonempty stage set, a defined closure is not a stage
-- Statement: the premise is needed: over the empty stage set every value is a closure, here a
-- non-landing.
example : ∃ M : ZeroParadox.Motion ℕ, M.StageClosure ∅ (Part.some 1) ∧ ¬ M.IsLanding 1 :=
  ⟨⟨fun _ => Part.some 0, fun _ _ h => by rw [Part.mem_some_iff] at h ⊢; exact h, fun _ _ => False⟩,
    fun _ hs => absurd hs (Set.notMem_empty _), fun h => by simp [ZeroParadox.Motion.IsLanding] at h⟩
#check @ZeroParadox.Motion.StageClosure.unique  -- Statement: a nonempty stage set has at most one closure
#check @ZeroParadox.Motion.RunsClose            -- Statement: the derived form: every landing-free run has the shape, closure `up (s 0)`
#check @ZeroParadox.Motion.runsClose_of_upStepInvariant -- Statement: premise form ⇒ derived form; one way
-- Statement: the converse fails: on ℕ, UP rounds up to even and OVER adds one; no run is
-- landing-free (of two consecutive stages one is even), so `RunsClose` holds, while UP changes
-- along the step `2 → 3`.
example :
    (ZeroParadox.Motion.ofTotal (fun n : ℕ => n + n % 2)
      (fun n => show (n + n % 2) + (n + n % 2) % 2 = n + n % 2 by omega)
      (fun a b => b = a + 1)).RunsClose ∧
    ¬ (ZeroParadox.Motion.ofTotal (fun n : ℕ => n + n % 2)
      (fun n => show (n + n % 2) + (n + n % 2) % 2 = n + n % 2 by omega)
      (fun a b => b = a + 1)).UpStepInvariant := by
  refine ⟨fun s hs hint => ?_, fun h => absurd (Part.some_inj.1 (h 2 3 rfl)) (by decide)⟩
  exfalso
  have h0 : ¬ s 0 = s 0 + s 0 % 2 := fun h => hint 0 (Part.mem_some_iff.2 h)
  have h1 : ¬ s 1 = s 1 + s 1 % 2 := fun h => hint 1 (Part.mem_some_iff.2 h)
  have e : s 1 = s 0 + 1 := hs 0
  rw [e] at h1
  omega
#check @ZeroParadox.Motion.RunClosure           -- Statement: the run form: `s` is a run and its range has the shape
#check @ZeroParadox.Motion.RunClosure.stageClosure -- Statement: run form ⇒ set form; one way
-- Reading: the two faces below are co-witnesses of one shape; no identity between `Ordinal` and a
-- machine's configurations is claimed, and no claim that an undefined closure is the corpus's pole.
#check @ZeroParadox.ordinalTowerMotion          -- Statement: on `Ordinal`, UP `nfp (ω^·)`, OVER `a ↦ ω^a`
#check @ZeroParadox.ordinalTowerMotion_upStepInvariant -- Statement: member of the premise form
#check @ZeroParadox.ordinalTowerMotion_stageClosure -- Statement: the tower stages `(ω^·)^[n] 0` close at ε₀
#check @ZeroParadox.ordinalTowerMotion_runClosure -- Statement: and the tower is a member of the run form too
-- Statement: those stages are `fundamentalSeq`.
example (n : ℕ) : ZeroParadox.fundamentalSeq n = (fun a : Ordinal => Ordinal.omega0 ^ a)^[n] 0 := rfl
-- Statement: ε₀ is a landing of the ordinal motion: the closure lies in the carrier.
example : ZeroParadox.ordinalTowerMotion.IsLanding (Ordinal.epsilon 0) :=
  (ZeroParadox.ordinalTowerMotion_isLanding_iff _).2 (Ordinal.omega0_opow_epsilon 0)
#check @ZeroParadox.nothing_between_is_a_step   -- Statement: no ordinal below ε₀ is fixed by `α ↦ ω^α`
#check @ZeroParadox.nfp_seed_independent_below_epsilon0 -- Statement: every seed at or below ε₀ closes at ε₀
#check @ZeroParadox.runMotion                   -- Statement: on configurations of `f : σ → Option σ`, UP `StateTransition.eval f`, OVER one step
#check @ZeroParadox.runMotion_upStepInvariant   -- Statement: member of the premise form
#check @ZeroParadox.runMotion_stageClosure      -- Statement: the not-yet-halted configurations reachable from `a` close at `eval f a`
#check @StateTransition.reaches_eval            -- Statement: Mathlib, `Reaches f a b → eval f a = eval f b`
#check @PFun.fix_fwd_eq                         -- Statement: Mathlib, `Sum.inr a' ∈ f a → f.fix a = f.fix a'`; `eval` is a `PFun.fix`
-- Reading: Mathlib's docstring calls `PFun.fix` the "first return map"; `fix_fwd_eq` is the `Part`
-- case of the Elgot fixpoint law (Goncharov, Jakob, Neves, arXiv:1807.01053, Def. 5, p. 22:7; cited).
-- Reading: for a step RELATION that iteration lands in the powerset, a set of results (ibid.,
-- Example 6.1, p. 22:7), not one landing; here `UpStepInvariant` supplies the single closure, one
-- way: premise ⇒ one closure (`stageClosure_of_run`); the converse control above fails.
-- Statement: HALTING member: `n ↦ n + 1` below 3, halted at 3; the stages `0, 1, 2` close at 3.
example : (ZeroParadox.runMotion (fun n : ℕ => if n < 3 then some (n + 1) else none)).StageClosure
    {0, 1, 2} (Part.some 3) := by
  let g : ℕ → Option ℕ := fun n => if n < 3 then some (n + 1) else none
  have r2 : StateTransition.Reaches g 2 3 := Relation.ReflTransGen.single rfl
  have r1 : StateTransition.Reaches g 1 3 := Relation.ReflTransGen.head rfl r2
  have r0 : StateTransition.Reaches g 0 3 := Relation.ReflTransGen.head rfl r1
  have h3 : g 3 = none := rfl
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  refine ⟨fun hl => ?_, ?_⟩
  · have := (ZeroParadox.runMotion_isLanding_iff g s).1 hl
    rcases hs with rfl | rfl | rfl <;> simp [g] at this
  · show StateTransition.eval g s = Part.some 3
    rcases hs with rfl | rfl | rfl
    · exact Part.eq_some_iff.2 (StateTransition.mem_eval.2 ⟨r0, h3⟩)
    · exact Part.eq_some_iff.2 (StateTransition.mem_eval.2 ⟨r1, h3⟩)
    · exact Part.eq_some_iff.2 (StateTransition.mem_eval.2 ⟨r2, h3⟩)
-- Statement: and that machine has no run, so it is a member of the set form and of no run form.
example : ¬ ∃ s : ℕ → ℕ,
    (ZeroParadox.runMotion (fun n : ℕ => if n < 3 then some (n + 1) else none)).IsRun s := by
  rintro ⟨s, hs⟩
  have step : ∀ n, s n < 3 ∧ s (n + 1) = s n + 1 := fun n => by
    have h : s (n + 1) ∈ (if s n < 3 then some (s n + 1) else none) := hs n
    by_cases hlt : s n < 3
    · rw [if_pos hlt] at h
      exact ⟨hlt, (Option.mem_some_iff.1 h).symm⟩
    · rw [if_neg hlt] at h
      simp at h
  have grow : ∀ n, n ≤ s n := fun n => by
    induction n with
    | zero => omega
    | succ n ih => have := (step n).2; omega
  have := (step 3).1
  have := grow 3
  omega
-- Statement: DIVERGENT member: `n ↦ n + 1` forever; every `n` is a stage and the closure is undefined.
example : (ZeroParadox.runMotion (fun n : ℕ => some (n + 1))).StageClosure Set.univ
    (StateTransition.eval (fun n : ℕ => some (n + 1)) 0) ∧
    ¬ (StateTransition.eval (fun n : ℕ => some (n + 1)) 0).Dom := by
  have reach : ∀ n, StateTransition.Reaches (fun n : ℕ => some (n + 1)) 0 n := fun n => by
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih => exact ih.tail rfl
  refine ⟨fun s _ => ⟨fun hl => ?_, (StateTransition.reaches_eval (reach s)).symm⟩, ?_⟩
  · have := (ZeroParadox.runMotion_isLanding_iff _ s).1 hl
    simp at this
  · exact (ZeroParadox.runMotion_run_diverges (fun n : ℕ => some (n + 1)) (s := id)
      (fun _ => rfl)).2
#check @ZeroParadox.runMotion_run_diverges      -- Statement: along a run of the motion no stage is a landing and the closure is undefined
-- Statement: the delay face: for `f a = some b`, the delayed runs from `a` and from `b` are weakly
-- bisimilar (Mathlib `Computation.Equiv`); one step adds one `think`.
example {σ : Type} (f : σ → Option σ) {a b : σ} (h : f a = some b) :
    Computation.Equiv (Computation.corec (fun s => (f s).elim (Sum.inl s) Sum.inr) a)
      (Computation.corec (fun s => (f s).elim (Sum.inl s) Sum.inr) b) := by
  have e : Computation.destruct (Computation.corec (fun s => (f s).elim (Sum.inl s) Sum.inr) a) =
      Sum.inr (Computation.corec (fun s => (f s).elim (Sum.inl s) Sum.inr) b) := by
    rw [Computation.corec_eq, h]; rfl
  rw [Computation.destruct_eq_think e]
  exact Computation.think_equiv _
-- Statement: NON-MEMBER, stages closing at different values: on ℕ, UP rounds up to even and OVER adds
-- one; `1` closes at 2 and `3` at 4.
example :
    ¬ ∃ c, (ZeroParadox.Motion.ofTotal (fun n : ℕ => n + n % 2)
      (fun n => show (n + n % 2) + (n + n % 2) % 2 = n + n % 2 by omega)
      (fun a b => b = a + 1)).StageClosure {1, 3} c := fun ⟨_, hc⟩ =>
  absurd (Part.some_inj.1 ((hc 1 (by simp)).2.trans (hc 3 (by simp)).2.symm)) (by decide)
-- Statement: NON-MEMBER, a stage that is a landing: the tower stages together with ε₀.
example : ¬ ∃ c, ZeroParadox.ordinalTowerMotion.StageClosure
    (insert (Ordinal.epsilon 0) (Set.range fun n => (fun a : Ordinal => Ordinal.omega0 ^ a)^[n] 0)) c :=
  fun ⟨_, hc⟩ => (hc _ (Set.mem_insert _ _)).1
    ((ZeroParadox.ordinalTowerMotion_isLanding_iff _).2 (Ordinal.omega0_opow_epsilon 0))

/-! ### § IX. The registration switch — is closure-definedness data? -/
#check @ZeroParadox.Motion.RegisteredComputable -- Statement: (a) a computable `Bool` test decides where UP is defined
#check @ZeroParadox.Motion.RegisteredDecidable  -- Statement: (b) a `Decidable` family on where UP is defined
#check @ZeroParadox.Motion.registeredDecidable_of_registeredComputable -- Statement: (a) ⇒ (b); one way
#check @ZeroParadox.Motion.registeredDecidable_of_classical -- Statement: under `classical` every motion is in (b), so (b) has no non-member there
#check @ZeroParadox.Motion.ofOption             -- Statement: a motion from an `Option`-valued UP, via `Part.ofOption`
#check @ZeroParadox.Motion.ofOption_registeredDecidable -- Statement: an `Option` presentation is in (b), with no axiom of choice
#check @ZeroParadox.Motion.ofOption_registeredComputable -- Statement: and in (a) when its `Option` map is computable
#check @ZeroParadox.Motion.registeredComputable_of_upTotal -- Statement: members of (a): every total motion on a `[Primcodable α]` carrier; the total ordinal tower is not one (below)
#check @ZeroParadox.Motion.registeredDecidable_of_upTotal -- Statement: members of (b): every total motion
-- Statement: the ordinal tower is a member of (b).
example : ZeroParadox.ordinalTowerMotion.RegisteredDecidable :=
  ZeroParadox.Motion.registeredDecidable_of_upTotal (ZeroParadox.Motion.ofTotal_upTotal _ _ _)
-- Statement: (a) takes `[Primcodable α]`, and `Ordinal` has no `Primcodable` structure (it is uncountable).
example : IsEmpty (Primcodable Ordinal) :=
  ⟨fun h => (Uncountable.not_countable : ¬ Countable Ordinal) (@Encodable.countable _ h.toEncodable)⟩
#check @ZeroParadox.no_computable_registration_at_kleene_floor -- Statement: no computable test decides self-halting on `Nat.Partrec.Code`
-- Statement: NON-MEMBER of (a): on `Nat.Partrec.Code`, UP defined (and fixing `c`) where `c` halts on
-- its own code.
example : ∃ M : ZeroParadox.Motion Nat.Partrec.Code,
    (∀ c, M.up c = (Nat.Partrec.Code.eval c (Encodable.encode c)).map (fun _ => c)) ∧
    ¬ M.RegisteredComputable := by
  refine ⟨⟨fun c => (Nat.Partrec.Code.eval c (Encodable.encode c)).map (fun _ => c),
    fun x y h => ?_, fun _ _ => False⟩, fun _ => rfl, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Part.mem_map_iff _).1 h
    exact Part.mem_map _ ha
  · rintro ⟨d, hdc, hd⟩
    exact ZeroParadox.no_computable_registration_at_kleene_floor ⟨d, hdc, fun c => hd c⟩
-- Reading: three presentations of UP: `Option` (definedness decided), the delay type (Capretta, LMCS
-- 1(2) 2005, Def. 3.1, p. 8; Mathlib `Computation`; p. 9: "A^ν is not isomorphic to A + 1 ...
-- because divergence is undecidable"), and `Part` (definedness a proposition).
#check @Part.ofOption                           -- Statement: Mathlib, `Option α → Part α`; free
#check @Part.toOption                           -- Statement: Mathlib, `Part α → Option α`, given `[Decidable o.Dom]`
#check @Part.equivOption                        -- Statement: Mathlib, `Part α ≃ Option α`, noncomputable
#check @ZeroParadox.registeredDecider           -- Statement: an `Option` decides its own `none`, with `propext` only, no `Classical.choice`
#check @ZeroParadox.em_of_poleDiscriminator     -- Statement: a total test of definedness on `Part Unit` gives excluded middle
#check @ZeroParadox.em_of_choiceFragment        -- Statement: the two-element choice fragment gives excluded middle
#check @ZeroParadox.select_of_decidable         -- Statement: a decidable inhabited predicate on `Bool` has a witness computed by `if`
-- Statement: registering every motion ⇒ excluded middle (no axioms).
example (h : ∀ (α : Type) (M : ZeroParadox.Motion α), M.RegisteredDecidable) :
    ZeroParadox.ExcludedMiddle := by
  intro p
  let M : ZeroParadox.Motion Unit :=
    ⟨fun _ => Part.mk p (fun _ => ()), fun _ _ hy => hy, fun _ _ => False⟩
  obtain ⟨d⟩ := h Unit M
  exact match d () with
    | isTrue hp => Or.inl hp
    | isFalse hn => Or.inr hn
-- Statement: the two-element choice fragment ⇒ every motion registered (`[propext, Quot.sound]`).
example (h : ZeroParadox.ChoiceFragment) {α : Type} (M : ZeroParadox.Motion α) :
    M.RegisteredDecidable := by
  obtain ⟨ch, hch⟩ := h
  refine ⟨fun a => ?_⟩
  let p := (M.up a).Dom
  let A : Bool → Prop := fun b => b = true ∨ p
  let B : Bool → Prop := fun b => b = false ∨ p
  have hA := hch A ⟨true, Or.inl rfl⟩
  have hB := hch B ⟨false, Or.inl rfl⟩
  refine decidable_of_iff (ch A = ch B) ⟨fun e => ?_, fun hp => ?_⟩
  · rcases hA with h1 | h1
    · rcases hB with h2 | h2
      · exact absurd (e ▸ h1 : ch B = true) (by rw [h2]; decide)
      · exact h2
    · exact h1
  · have : A = B := funext fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    rw [this]
-- Reading: so registering everywhere implies excluded middle, and the two-element choice fragment
-- suffices for it; neither arrow uses `Classical.choice`. On `Part Unit` the test is inter-derivable
-- with the fragment, both legs choice-free (`ZeroParadox/Valuation/PoleRegistration.lean` § II).

end DieCannotBeIndex
