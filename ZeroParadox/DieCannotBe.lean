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
import Mathlib.Order.Interval.Finset.DenselyOrdered
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Seq.Computation
import Mathlib.CategoryTheory.Idempotents.Basic
import ZeroParadox.Ordinal.PricedInterface
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Category.BottomUndecidable
import ZeroParadox.Computability.Rice
import ZeroParadox.Settheory.Loeb
import ZeroParadox.Settheory.Curry
import ZeroParadox.Settheory.Tarski
import ZeroParadox.Settheory.FixedPointFork
import ZeroParadox.Category.LawvereTwoAdic
import ZeroParadox.Multihomed.HilbertDiagonal
import ZeroParadox.Order.UpAndOver
import ZeroParadox.Settheory.QuineHost
import ZeroParadox.Settheory.HypersetOrder

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
-- "Generalized Rewrite Theories and Coherence Completion", Rewriting Logic and Its Applications, LNCS,
-- 2018, pp. 164–183, doi 10.1007/978-3-319-99840-4_10, record checked at Crossref 2026-10-18; Def. 8,
-- p. 10 of the 28-page copy read, which prints no venue and is not the LNCS pagination) and the relation of
-- R. Diaconescu, "Non-Deterministic Algebraic Rewriting as Adjunction", arXiv:2204.12133, Defs.
-- 11–12, so Loop and Climb are properties of one canonical edge. Delta: in Meseguer UP is total, the
-- normal form modulo the axioms B of a convergent equation system; in R. Diaconescu (Def. 11) it is a
-- total homomorphism into a subset it fixes, with equations only in his Examples 8–9. Meseguer requires
-- coherence (p. 11, with Theorem 4) for the canonical system to be faithful to the rules; the
-- counterpart condition in R. Diaconescu is β-coherence (Def. 12, a hypothesis of his Props. 5.1 and 5.5), to which he says
-- the Maude literature's coherence conditions bear "some similarity" while playing "a different role"
-- (p. 26). Neither is imposed here. No counterpart of the switches was located in these two sources
-- as of 2026-10-18 (UP is total in both; their text, searched for "partial", "loop" and "cycle", has
-- no hit bearing on a switch); the dated search for the pair is in `LEAN_CUSTOM_REGISTRY.md`.
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
-- Statement: so the converse of `climb_corner` fails: that `Bool` motion fires the corner and does
-- not climb.
example : ∃ M : ZeroParadox.Motion Bool, M.Corner ∧ ¬ M.Climb :=
  ⟨ZeroParadox.Motion.ofTotal (fun _ => true) (fun _ => rfl) (fun a b => a ≠ b),
    ZeroParadox.Motion.loop_corner _ ⟨true, false, Part.mem_some_iff.2 rfl, Bool.false_ne_true.symm,
      Bool.false_ne_true, Part.mem_some_iff.2 rfl⟩,
    fun h => by
      obtain ⟨y, b, z, h1, h2, h3⟩ := ZeroParadox.Motion.climb_three _ h
      revert h1 h2 h3; cases y <;> cases b <;> cases z <;> decide⟩
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
#check @ZeroParadox.unique_succ_covBy           -- Statement: if `b` is `y`'s only successor and `b` does not reach `y`, then `y ⋖ b` in the reachability preorder; one way, the converse refuted on `Fin 3` below
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
-- Statement: no hypotheses: ℕ is a member; `WithBot (WithBot ℚ)` has the cut at its ⊥, is not a
-- member, and is not densely ordered.
example : ZeroParadox.EveryStepCovered ℕ := fun x _ => ⟨_, Order.covBy_succ x⟩
example : ZeroParadox.BotCovered (WithBot (WithBot ℚ)) ∧
    ¬ ZeroParadox.EveryStepCovered (WithBot (WithBot ℚ)) ∧ ¬ DenselyOrdered (WithBot (WithBot ℚ)) := by
  have hcut : ZeroParadox.BotCovered (WithBot (WithBot ℚ)) :=
    ⟨((⊥ : WithBot ℚ) : WithBot (WithBot ℚ)), covBy_of_eq_or_eq (WithBot.bot_lt_coe _)
      fun c _ hc => by
        induction c using WithBot.recBotCoe with
        | bot => exact Or.inl rfl
        | coe c => exact Or.inr (congrArg _ (le_bot_iff.mp (WithBot.coe_le_coe.mp hc)))⟩
  refine ⟨hcut, fun h => ?_, fun hd => ZeroParadox.axb1_fails_everywhere_iff_dense.mp hd ⊥ hcut⟩
  obtain ⟨b, hb⟩ := h ((⊥ : WithBot ℚ) : WithBot (WithBot ℚ))
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
#check @ZeroParadox.axb1_fails_everywhere_iff_dense -- Statement: if `α` is a preorder, then `α` is densely ordered iff no point of `α` has a first step (`∀ bot, ¬ HasFirstStep bot`); both directions. ZP-F's restatement (`ZeroParadox/Reals/OrderedField.lean`) of Mathlib's `denselyOrdered_iff_forall_not_covBy`
-- Statement: if `α` is a partial order with ⊥ and has the cut, then `α` is not densely ordered; the
-- converse is refuted at the `WithTop (WithTop NNReal)` example below.
example {α : Type} [PartialOrder α] [OrderBot α] (h : ZeroParadox.BotCovered α) :
    ¬ DenselyOrdered α := fun hd => ZeroParadox.axb1_fails_everywhere_iff_dense.mp hd ⊥ h
-- Statement: if `α` is a partial order, is a member of the scope form, and has a non-maximal point,
-- then `α` is not densely ordered; the converse fails at the `WithBot (WithBot ℚ)` example above.
example {α : Type} [PartialOrder α] (h : ZeroParadox.EveryStepCovered α)
    (hx : ∃ x : α, ¬ IsMax x) : ¬ DenselyOrdered α := fun hd =>
  let ⟨x, hx⟩ := hx
  ZeroParadox.axb1_fails_everywhere_iff_dense.mp hd x (h x hx)
-- Statement: no hypotheses: `Unit` is densely ordered, has no cut, and is a member, so the example
-- above is false without its non-maximal-point hypothesis.
example : DenselyOrdered Unit ∧ ¬ ZeroParadox.BotCovered Unit ∧ ZeroParadox.EveryStepCovered Unit :=
  ⟨⟨fun a b h => (lt_irrefl a (Subsingleton.elim b a ▸ h)).elim⟩,
    fun ⟨_, h⟩ => h.lt.ne (Subsingleton.elim _ _), fun _ hx => absurd (fun _ _ => le_rfl) hx⟩
-- Statement: if `α` is a partial order with ⊥, then (1) no cut, (2) the cut without the scope form, or
-- (3) the scope form with ⊥ of `α` not maximal holds, and (1) and (3) do not both hold.
example {α : Type} [PartialOrder α] [OrderBot α] :
    (¬ ZeroParadox.BotCovered α ∨ (ZeroParadox.BotCovered α ∧ ¬ ZeroParadox.EveryStepCovered α) ∨
      (ZeroParadox.EveryStepCovered α ∧ ¬ IsMax (⊥ : α))) ∧
    ¬ (¬ ZeroParadox.BotCovered α ∧ ZeroParadox.EveryStepCovered α ∧ ¬ IsMax (⊥ : α)) := by
  refine ⟨?_, fun ⟨hn, h, hb⟩ => hn (h ⊥ hb)⟩
  by_cases hc : ZeroParadox.BotCovered α
  · by_cases he : ZeroParadox.EveryStepCovered α
    · obtain ⟨a, ha⟩ := hc
      exact Or.inr (Or.inr ⟨he, fun hm => absurd (hm ha.lt.le) (not_le_of_gt ha.lt)⟩)
    · exact Or.inr (Or.inl ⟨hc, he⟩)
  · exact Or.inl hc
-- Statement: if `α` is a partial order with ⊥, then `α` is a member of the scope form with no cut iff
-- every point of `α` is ⊥ of `α`; both directions.
example {α : Type} [PartialOrder α] [OrderBot α] :
    ZeroParadox.EveryStepCovered α ∧ ¬ ZeroParadox.BotCovered α ↔ ∀ a : α, a = ⊥ :=
  ⟨fun ⟨h, hb⟩ a => by_contra fun ha => hb (ZeroParadox.everyStepCovered_botCovered h ⟨a, ha⟩),
    fun h => ⟨fun x hx => absurd (fun y _ => by rw [h y, h x]) hx, fun ⟨a, ha⟩ => ha.lt.ne (h a).symm⟩⟩
-- Statement: no hypotheses: `WithTop (WithTop NNReal)` has no cut and is not densely ordered, so the
-- converse of the cut ⇒ not-densely-ordered example fails.
example : ¬ ZeroParadox.BotCovered (WithTop (WithTop NNReal)) ∧
    ¬ DenselyOrdered (WithTop (WithTop NNReal)) := by
  refine ⟨fun ⟨a, h⟩ => ?_, fun hd => ?_⟩
  · induction a using WithTop.recTopCoe with
    | top =>
      exact h.2 (c := (((1 : NNReal) : WithTop NNReal) : WithTop (WithTop NNReal)))
        (WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 one_pos)) (WithTop.coe_lt_top _)
    | coe b =>
      induction b using WithTop.recTopCoe with
      | top =>
        exact h.2 (c := (((1 : NNReal) : WithTop NNReal) : WithTop (WithTop NNReal)))
          (WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 one_pos))
          (WithTop.coe_lt_coe.2 (WithTop.coe_lt_top _))
      | coe r =>
        have hr : (0 : NNReal) < r := WithTop.coe_lt_coe.1 (WithTop.coe_lt_coe.1 h.lt)
        exact h.2 (c := (((r / 2 : NNReal) : WithTop NNReal) : WithTop (WithTop NNReal)))
          (WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (by positivity)))
          (WithTop.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (NNReal.half_lt_self hr.ne')))
  · refine ZeroParadox.axb1_fails_everywhere_iff_dense.mp hd ((⊤ : WithTop NNReal) : WithTop (WithTop NNReal))
      ⟨⊤, WithTop.coe_lt_top _, fun c h1 h2 => ?_⟩
    induction c using WithTop.recTopCoe with
    | top => exact lt_irrefl _ h2
    | coe b => exact not_top_lt (WithTop.coe_lt_coe.1 h1)
#check @LocallyFiniteOrder.denselyOrdered_iff_subsingleton -- Statement: Mathlib, if `X` is a linear order and locally finite, then `X` is densely ordered iff it is a subsingleton; both directions
#check @Dyadic                                  -- Statement: Lean core, the dyadic rationals: zero or `n * 2 ^ (-k)`, `n` odd, `k : ℤ`; the grids below are subsets of ℚ and do not use it
-- Statement: for each `N : ℕ`, the `N`-place grid `{k / 2 ^ N | k : ℕ}` ⊆ ℚ, with 0 as its ⊥, is a
-- member of the scope form and has the cut.
example (N : ℕ) :
    letI : OrderBot {q : ℚ // ∃ k : ℕ, q = k / 2 ^ N} :=
      { bot := ⟨0, 0, by simp⟩
        bot_le := fun ⟨_, k, hk⟩ => show (0 : ℚ) ≤ _ from hk ▸ by positivity }
    ZeroParadox.EveryStepCovered {q : ℚ // ∃ k : ℕ, q = k / 2 ^ N} ∧
      ZeroParadox.BotCovered {q : ℚ // ∃ k : ℕ, q = k / 2 ^ N} := by
  have hp : (0 : ℚ) < 2 ^ N := by positivity
  have cov : ∀ k : ℕ, (⟨k / 2 ^ N, k, rfl⟩ : {q : ℚ // ∃ k : ℕ, q = k / 2 ^ N}) ⋖
      ⟨((k + 1 : ℕ) : ℚ) / 2 ^ N, k + 1, rfl⟩ := fun k => by
    refine ⟨show (k : ℚ) / 2 ^ N < ((k + 1 : ℕ) : ℚ) / 2 ^ N by
      rw [div_lt_div_iff_of_pos_right hp]; exact_mod_cast Nat.lt_succ_self k, ?_⟩
    rintro ⟨_, j, rfl⟩ h0 h1
    change (k : ℚ) / 2 ^ N < j / 2 ^ N at h0
    change (j : ℚ) / 2 ^ N < ((k + 1 : ℕ) : ℚ) / 2 ^ N at h1
    rw [div_lt_div_iff_of_pos_right hp] at h0 h1
    have a : k < j := by exact_mod_cast h0
    have b : j < k + 1 := by exact_mod_cast h1
    omega
  have hE : ZeroParadox.EveryStepCovered {q : ℚ // ∃ k : ℕ, q = k / 2 ^ N} :=
    fun ⟨_, k, hk⟩ _ => by subst hk; exact ⟨_, cov k⟩
  letI : OrderBot {q : ℚ // ∃ k : ℕ, q = k / 2 ^ N} :=
    { bot := ⟨0, 0, by simp⟩
      bot_le := fun ⟨_, k, hk⟩ => show (0 : ℚ) ≤ _ from hk ▸ by positivity }
  exact ⟨hE, ZeroParadox.everyStepCovered_botCovered hE ⟨⟨((1 : ℕ) : ℚ) / 2 ^ N, 1, rfl⟩,
    fun h => absurd (congrArg Subtype.val h) (show ((1 : ℕ) : ℚ) / 2 ^ N ≠ 0 by positivity)⟩⟩
-- Statement: no hypotheses: the union of the grids over all `N : ℕ`, with 0 as its ⊥, is densely
-- ordered and has no cut.
example :
    letI : OrderBot {q : ℚ // ∃ N k : ℕ, q = k / 2 ^ N} :=
      { bot := ⟨0, 0, 0, by simp⟩
        bot_le := fun ⟨_, _, k, hk⟩ => show (0 : ℚ) ≤ _ from hk ▸ by positivity }
    DenselyOrdered {q : ℚ // ∃ N k : ℕ, q = k / 2 ^ N} ∧
      ¬ ZeroParadox.BotCovered {q : ℚ // ∃ N k : ℕ, q = k / 2 ^ N} := by
  have hd : DenselyOrdered {q : ℚ // ∃ N k : ℕ, q = k / 2 ^ N} := by
    refine ⟨fun ⟨a, N, k, ha⟩ ⟨b, M, j, hb⟩ hab => ?_⟩
    subst ha hb
    refine ⟨⟨((k * 2 ^ M + j * 2 ^ N : ℕ) : ℚ) / 2 ^ (N + M + 1), N + M + 1, _, rfl⟩, ?_, ?_⟩ <;>
    · rw [Subtype.mk_lt_mk] at hab ⊢
      have e : ((k * 2 ^ M + j * 2 ^ N : ℕ) : ℚ) / 2 ^ (N + M + 1)
          = ((k : ℚ) / 2 ^ N + j / 2 ^ M) / 2 := by
        push_cast; field_simp; ring
      rw [e]; linarith
  exact ⟨hd, fun ⟨_, h⟩ => not_covBy h⟩
-- Statement: if `S` is a finite set of precisions and `q` lies in the `n`-place grid for some `n ∈ S`,
-- then `q` lies in the grid of precision `S.sup id`, the largest in `S`; one way; the converse is
-- not claimed.
example (S : Finset ℕ) (q : ℚ) (h : ∃ n ∈ S, ∃ k : ℕ, q = k / 2 ^ n) :
    ∃ k : ℕ, q = k / 2 ^ S.sup id := by
  obtain ⟨n, hn, k, rfl⟩ := h
  have hle : n ≤ S.sup id := Finset.le_sup (f := id) hn
  refine ⟨k * 2 ^ (S.sup id - n), ?_⟩
  have e : (2 : ℚ) ^ S.sup id = 2 ^ n * 2 ^ (S.sup id - n) := by rw [← pow_add]; congr 1; omega
  rw [e]; push_cast; field_simp
-- Reading (Tim's): precision `N` is reading `N` binary digits after the point; see the three grid
-- examples above (the fixed-`N` grid, the union, the finite-set nesting).
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
-- Statement: `not_mem_of_mem`'s nonempty premise is redundant: `y ∈ S` supplies it.
example {α : Type} {M : ZeroParadox.Motion α} {S : Set α} {c : Part α} (h : M.StageClosure S c)
    {y : α} (hy : y ∈ c) : y ∉ S :=
  fun hyS => h.not_mem_of_mem ⟨y, hyS⟩ hy hyS
#check @ZeroParadox.Motion.StageClosure.unique  -- Statement: a nonempty stage set has at most one closure
-- Statement: over the empty stage set every value is a closure of every motion.
example {α : Type} (M : ZeroParadox.Motion α) (c : Part α) : M.StageClosure ∅ c :=
  fun _ hs => absurd hs (Set.notMem_empty _)
-- Statement: so `unique` needs its nonempty premise: on any inhabited carrier, `Part.none` and
-- `Part.some default` are two different closures of the empty stage set.
example {α : Type} [Inhabited α] (M : ZeroParadox.Motion α) :
    M.StageClosure ∅ Part.none ∧ M.StageClosure ∅ (Part.some default) ∧
      (Part.none : Part α) ≠ Part.some default :=
  ⟨fun _ hs => absurd hs (Set.notMem_empty _), fun _ hs => absurd hs (Set.notMem_empty _),
    fun h => Part.notMem_none (default : α) (h ▸ Part.mem_some default)⟩
-- Statement: and `isLanding_of_mem` needs it: on ℕ, a defined closure of the empty stage set that is
-- not a landing.
example : ∃ M : ZeroParadox.Motion ℕ, M.StageClosure ∅ (Part.some 1) ∧ ¬ M.IsLanding 1 :=
  ⟨⟨fun _ => Part.some 0, fun _ _ h => by rw [Part.mem_some_iff] at h ⊢; exact h, fun _ _ => False⟩,
    fun _ hs => absurd hs (Set.notMem_empty _), fun h => by simp [ZeroParadox.Motion.IsLanding] at h⟩
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
#check @ZeroParadox.Motion.em_of_registeredDecidable -- Statement: if every motion on every `α : Type` is registered, excluded middle holds; one way (the converse, given unique choice into `Bool`, is the `example` below)
-- Statement: the two-element choice fragment ⇒ every motion on every `α : Type` registered
-- (`[propext, Quot.sound]`).
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
-- Statement: registering every motion on every `α : Type` ⇒ the two-element choice fragment (no axioms).
example (h : ∀ (α : Type) (M : ZeroParadox.Motion α), M.RegisteredDecidable) :
    ZeroParadox.ChoiceFragment := by
  let M : ZeroParadox.Motion (Bool → Prop) :=
    ⟨fun S => Part.mk (S true) (fun _ => S), fun _ _ hy => by
      obtain ⟨hd, rfl⟩ := hy; exact ⟨hd, rfl⟩, fun _ _ => False⟩
  obtain ⟨d⟩ := h _ M
  refine ⟨fun S => @decide (S true) (d S), fun S ⟨b, hb⟩ => ?_⟩
  show S (@decide (S true) (d S))
  cases hS : @decide (S true) (d S)
  · have : ¬ S true := @of_decide_eq_false _ (d S) hS
    cases b
    · exact hb
    · exact absurd hb this
  · exact @of_decide_eq_true _ (d S) hS
-- Statement: by `Motion.em_of_registeredDecidable`, the `example`s after it and `em_of_choiceFragment`,
-- registration on every `α : Type` and the fragment are inter-derivable and each gives excluded
-- middle, none of them using `Classical.choice` (footprints: the glosses above; the PurityChecks of
-- `ZeroParadox/Die.lean` and `ZeroParadox/Category/ExcludedMiddleBridge.lean`); `Part Unit` form:
-- `ZeroParadox/Valuation/PoleRegistration.lean` § II.
-- Statement: given unique choice into `Bool` as a hypothesis, registration on every `α : Type` and
-- excluded middle are inter-derivable (no axioms).
example (uc : ∀ P : Bool → Prop, (∃! b, P b) → {b : Bool // P b}) :
    (∀ (α : Type) (M : ZeroParadox.Motion α), M.RegisteredDecidable) ↔ ZeroParadox.ExcludedMiddle := by
  refine ⟨fun h p => ?_, fun hem α M => ⟨fun a => ?_⟩⟩
  · let M : ZeroParadox.Motion Unit :=
      ⟨fun _ => Part.mk p (fun _ => ()), fun _ _ hy => hy, fun _ _ => False⟩
    obtain ⟨d⟩ := h Unit M
    exact match d () with
      | isTrue hp => Or.inl hp
      | isFalse hn => Or.inr hn
  · have hu : ∃! b : Bool, (b = true ∧ (M.up a).Dom) ∨ (b = false ∧ ¬ (M.up a).Dom) := by
      rcases hem (M.up a).Dom with hp | hn
      · exact ⟨true, Or.inl ⟨rfl, hp⟩, fun _ hy => hy.elim And.left (fun h => absurd hp h.2)⟩
      · exact ⟨false, Or.inr ⟨rfl, hn⟩, fun _ hy => hy.elim (fun h => absurd h.2 hn) And.left⟩
    obtain ⟨b, hb⟩ := uc _ hu
    exact match b, hb with
      | true, hb => isTrue (hb.elim And.right (fun h => absurd h.1 (by decide)))
      | false, hb => isFalse (hb.elim (fun h => absurd h.1 (by decide)) And.right)
-- Reading (cited, not claimed): Escardó and Knapp, "Partial Elements and Recursion via Dominances in
-- Univalent Type Theory", CSL 2017, LIPIcs 82: § 2.2, p. 21:4, "The assertion that every partial
-- element is defined or else undefined is equivalent to the principle of excluded middle (every
-- proposition is inhabited or empty)", and § 2.7, p. 21:6, "L X ≃ X + 1 iff the canonical map 2 → Ω
-- is an equivalence iff excluded middle holds"; T. de Jong, arXiv:2407.06952, Prop. 5.7, p. 13, credits
-- the equivalence to their § 2.2. In Lean's `Prop`/`Type` split their excluded middle sits on the data
-- side, `∀ p, Decidable p`, equivalently the `Bool` choice fragment, and the PROVED legs above are
-- instances of their equivalence on that side: registration on every `α : Type` ⇔ the fragment. The
-- `Prop`-valued `ZeroParadox.ExcludedMiddle` is reached one way, and back with the unique-choice
-- hypothesis of the previous `example`; without it the converse is not established in Lean
-- (`ZeroParadox/Category/ChoiceCannotBe.md`). An instance of theirs, not a generalization.

/-! ### § X. The OVER leg's WHICH — selection, in two variants -/
#check @ZeroParadox.Motion.SelectedData         -- Statement: (a) at every point with a successor, a successor chosen as data
#check @ZeroParadox.Motion.SelectedTotal        -- Statement: (b) one map choosing a successor at every point that has one
#check @ZeroParadox.Motion.selectedData_of_selectedTotal -- Statement: (b) ⇒ (a); one way
#check @ZeroParadox.Motion.selectedTotal_of_selectedData -- Statement: (a) ⇒ (b), given a decision at every point of whether a successor exists
#check @ZeroParadox.Motion.selectedTotal_of_classical -- Statement: under `classical` every motion is in (b), so neither variant has a non-member there
#check @ZeroParadox.Motion.selectedTotal_of_fun -- Statement: a step given by a function is in (b)
#check @ZeroParadox.Motion.selectedTotal_of_option -- Statement: a step given by an `Option`-valued function is in (b)
-- Statement: members: the run motion of any `f : σ → Option σ`, and the ordinal tower motion.
example {σ : Type} (f : σ → Option σ) : (ZeroParadox.runMotion f).SelectedTotal :=
  ZeroParadox.Motion.selectedTotal_of_option f (fun _ _ => Iff.rfl)
example : ZeroParadox.ordinalTowerMotion.{0}.SelectedTotal :=
  ZeroParadox.Motion.selectedTotal_of_fun _ (fun _ _ => Iff.rfl)
-- Statement: (a) on every motion on every `α : Type` ⇒ the two-element choice fragment. The carrier is
-- `(Bool → Prop) × Bool` with OVER `(S, _) → (S, b)` when `S b`; both predicates of
-- `em_of_choiceFragment`'s pair are inhabited, so the selector decides `S true` as data
-- (`[propext, Quot.sound]`).
example (h : ∀ (α : Type) (M : ZeroParadox.Motion α), M.SelectedData) :
    ZeroParadox.ChoiceFragment := by
  obtain ⟨g⟩ := h _ (ZeroParadox.Motion.ofTotal id (fun _ => rfl)
    (fun x y : (Bool → Prop) × Bool => y.1 = x.1 ∧ x.1 y.2))
  let pick : ∀ S : Bool → Prop, (∃ b, S b) → Bool := fun S hS =>
    (g (S, true) (hS.elim fun b hb => ⟨(S, b), rfl, hb⟩)).1.2
  have spec : ∀ (S : Bool → Prop) (hS : ∃ b, S b), S (pick S hS) := fun S hS =>
    (g (S, true) (hS.elim fun b hb => ⟨(S, b), rfl, hb⟩)).2.2
  have cong : ∀ (X Y : Bool → Prop) hX hY, X = Y → pick X hX = pick Y hY := by
    intro X Y hX hY e; subst e; rfl
  have key : ∀ S : Bool → Prop, pick (fun b => b = true ∨ S true) ⟨true, Or.inl rfl⟩ =
      pick (fun b => b = false ∨ S true) ⟨false, Or.inl rfl⟩ ↔ S true := by
    intro S
    refine ⟨fun e => ?_, fun hp => cong _ _ ⟨true, Or.inl rfl⟩ ⟨false, Or.inl rfl⟩
      (funext fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩)⟩
    rcases spec (fun b => b = true ∨ S true) ⟨true, Or.inl rfl⟩ with h1 | h1
    · rcases spec (fun b => b = false ∨ S true) ⟨false, Or.inl rfl⟩ with h2 | h2
      · exact absurd (h1.symm.trans (e.trans h2)) (by decide)
      · exact h2
    · exact h1
  refine ⟨fun S => decide (pick (fun b => b = true ∨ S true) ⟨true, Or.inl rfl⟩ =
    pick (fun b => b = false ∨ S true) ⟨false, Or.inl rfl⟩), fun S ⟨b, hb⟩ => ?_⟩
  show S (decide (pick (fun b => b = true ∨ S true) ⟨true, Or.inl rfl⟩ =
    pick (fun b => b = false ∨ S true) ⟨false, Or.inl rfl⟩))
  cases hd : decide (pick (fun b => b = true ∨ S true) ⟨true, Or.inl rfl⟩ =
    pick (fun b => b = false ∨ S true) ⟨false, Or.inl rfl⟩)
  · have hn : ¬ S true := fun hp => absurd ((key S).2 hp) (of_decide_eq_false hd)
    cases b
    · exact hb
    · exact absurd hb hn
  · exact (key S).1 (of_decide_eq_true hd)
-- Reading (cited, not claimed): Diaconescu's argument as in the Rocq standard library,
-- `theories/Logic/Diaconescu.v` Part A (`pred_ext_and_rel_choice_imp_EM`, through
-- `AC_bool_subset_to_bool`, a functional relation choosing in every inhabited subset of `bool`), which
-- credits Diaconescu 1975 and Lacas and Werner 1999, run on the data side: there relational choice, a
-- `Prop`, gives excluded middle; here a selector given as data gives the fragment (the `example`
-- above) and excluded middle directly (`Motion.em_of_selectedData`, next line), the latter on Part A's
-- own two classes `b = true ∨ p`, `b = false ∨ p`; an instance of theirs, not a generalization.
#check @ZeroParadox.Motion.em_of_selectedData -- Statement: (a) on every motion on every `α : Type` ⇒ excluded middle, directly
-- Statement: with the fragment, (a) at any motion gives (b); so (a) on every motion on every
-- `α : Type` gives (b) on every such motion, with the previous `example`, and (b) gives (a) by
-- `selectedData_of_selectedTotal` (`[propext, Quot.sound]`).
example (hf : ZeroParadox.ChoiceFragment) {α : Type} (M : ZeroParadox.Motion α)
    (h : M.SelectedData) : M.SelectedTotal := by
  obtain ⟨ch, hch⟩ := hf
  refine ZeroParadox.Motion.selectedTotal_of_selectedData (fun a => ?_) h
  have hA := hch (fun b => b = true ∨ ∃ c, M.step a c) ⟨true, Or.inl rfl⟩
  have hB := hch (fun b => b = false ∨ ∃ c, M.step a c) ⟨false, Or.inl rfl⟩
  refine decidable_of_iff (ch (fun b => b = true ∨ ∃ c, M.step a c) =
    ch (fun b => b = false ∨ ∃ c, M.step a c)) ⟨fun e => ?_, fun hp => ?_⟩
  · rcases hA with h1 | h1
    · rcases hB with h2 | h2
      · exact absurd (h1.symm.trans (e.trans h2)) (by decide)
      · exact h2
    · exact h1
  · have : (fun b => b = true ∨ ∃ c, M.step a c) = (fun b => b = false ∨ ∃ c, M.step a c) :=
      funext fun b => propext ⟨fun _ => Or.inr hp, fun _ => Or.inr hp⟩
    rw [this]
-- Reading: the converse, the fragment ⇒ a selector on every motion, is not established here: the
-- fragment chooses in `Bool`, a selector in an arbitrary carrier.

/-! ### § XI. The OVER leg's WHETHER — what OVER does at a point -/
#check @ZeroParadox.Motion.NoStepAt              -- Statement: no step leaves `y`
#check @ZeroParadox.Motion.SelfOnlyAt            -- Statement: `y` steps to itself and to nothing else
#check @ZeroParadox.Motion.LeavesAt              -- Statement: `y` steps to some point other than `y`
#check @ZeroParadox.Motion.OverTrichotomy        -- Statement: one of the three holds at `y`
-- Statement: the three are pairwise exclusive.
example {α : Type} (M : ZeroParadox.Motion α) (y : α) :
    ¬ (M.NoStepAt y ∧ M.SelfOnlyAt y) ∧ ¬ (M.NoStepAt y ∧ M.LeavesAt y) ∧
      ¬ (M.SelfOnlyAt y ∧ M.LeavesAt y) :=
  ⟨fun ⟨h1, h2⟩ => h1 y h2.1, fun ⟨h1, ⟨b, hb, _⟩⟩ => h1 b hb,
    fun ⟨⟨_, h2⟩, ⟨b, hb, hne⟩⟩ => hne (h2 b hb)⟩
#check @ZeroParadox.Motion.overTrichotomy_of_option -- Statement: with `DecidableEq`, an `Option`-valued step meets the trichotomy at every point
-- Statement: the trichotomy at every point of every motion on every `α : Type` ⇒ excluded middle
-- (`[propext]`).
example (H : ∀ (α : Type) (M : ZeroParadox.Motion α) (y : α), M.OverTrichotomy y) :
    ZeroParadox.ExcludedMiddle := by
  intro p
  rcases H Unit (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun _ _ => p)) () with
    h | ⟨hp, _⟩ | ⟨b, _, hb⟩
  · exact Or.inr (h ())
  · exact Or.inl hp
  · exact absurd (Subsingleton.elim b ()) hb
-- Reading: the OVER-leg counterpart of § IX's Escardó–Knapp § 2.2 form ("every partial element is
-- defined or else undefined"), there quoted; cited, not claimed.
#check @ZeroParadox.machine_trichotomy           -- Statement: the machine face: a configuration of `f : σ → Option σ` is halted, loops in place, or steps to some `s' ≠ s`
-- Reading: under a function the first two values share a fate, as `machine_trichotomy`'s docstring
-- states for the machine face (`loop_is_a_trap`); the obstruction is single-valuedness
-- (`deterministic_has_no_fanout`, § III), not the fixed point.
-- Statement: under a relation a point can step to itself and elsewhere, which is `LeavesAt`: the
-- always-true relation on `Bool`, at `true`.
example : let M := ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun _ _ => True)
    M.step true true ∧ M.LeavesAt true ∧ ¬ M.SelfOnlyAt true :=
  ⟨trivial, ⟨false, trivial, by decide⟩, fun ⟨_, h⟩ => absurd (h false trivial) (by decide)⟩
-- Statement: `NoStepAt` members: every landing of the run motion.
example {σ : Type} (f : σ → Option σ) (s : σ) (hs : (ZeroParadox.runMotion f).IsLanding s) :
    (ZeroParadox.runMotion f).NoStepAt s := fun b hb => by
  have h := (ZeroParadox.runMotion_isLanding_iff f s).1 hs
  change b ∈ f s at hb
  rw [h] at hb
  cases hb
-- Statement: `SelfOnlyAt` members: every landing of the ordinal tower motion.
example (y : Ordinal.{0}) (hy : ZeroParadox.ordinalTowerMotion.IsLanding y) :
    ZeroParadox.ordinalTowerMotion.SelfOnlyAt y := by
  have h := (ZeroParadox.ordinalTowerMotion_isLanding_iff y).1 hy
  exact ⟨h.symm, fun b hb => hb.trans h⟩
-- Statement: `LeavesAt` member, `NoStepAt` and `SelfOnlyAt` non-member: on `Bool` with OVER `≠`, at
-- `true`.
example : let M := ZeroParadox.Motion.ofTotal (fun _ : Bool => true) (fun _ => rfl) (fun a b => a ≠ b)
    M.LeavesAt true ∧ ¬ M.NoStepAt true ∧ ¬ M.SelfOnlyAt true :=
  ⟨⟨false, fun e => Bool.noConfusion e, fun e => Bool.noConfusion e⟩,
    fun h => h false (fun e => Bool.noConfusion e), fun ⟨h, _⟩ => h rfl⟩
#check @ZeroParadox.Motion.corner_leavesAt       -- Statement: a corner leaves its landing; with `loop_corner` and `climb_corner`, loop and climb sit at `LeavesAt`

/-! ### § XII. OVER run backwards — fan-in, reversal, predecessor selection -/
#check @ZeroParadox.Motion.FanIn                 -- Statement: `y` has two distinct predecessors
-- Statement: member: on `Bool` with OVER constant `true`, `true` has predecessors `false` and `true`.
example : (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun _ b => b = true)).FanIn
    true :=
  ⟨false, true, by decide, rfl, rfl⟩
#check @ZeroParadox.Motion.not_fanIn_of_injective -- Statement: non-members: every point of a step given by a one-to-one function
-- Statement: non-member: every motion on `Unit`.
example (M : ZeroParadox.Motion Unit) (y : Unit) : ¬ M.FanIn y :=
  fun ⟨a, b, h, _, _⟩ => h (Subsingleton.elim a b)
-- Reading: the forward twin is `deterministic_has_no_fanout` (§ III): a step function has no
-- fan-out, and fan-in only where it is not one-to-one.
#check @ZeroParadox.Motion.reverse               -- Statement: the reversed motion: the same UP, OVER flipped
#check @ZeroParadox.Motion.reverse_up            -- Statement: INVARIANT: reversal leaves UP, and with it `up_idem`, unchanged
#check @ZeroParadox.Motion.reverse_reverse       -- Statement: reversing twice returns the motion
#check @ZeroParadox.Motion.fanIn_iff_reverse     -- Statement: fan-in at `y` is two distinct successors of `y` in the reversed motion
-- Statement: selecting predecessors on every motion on every `α : Type` and selecting successors there
-- are inter-derivable, since reversal is an involution (no axioms).
example : (∀ (α : Type) (M : ZeroParadox.Motion α), M.reverse.SelectedData) ↔
    ∀ (α : Type) (M : ZeroParadox.Motion α), M.SelectedData :=
  ⟨fun h α M => h α M.reverse, fun h α M => h α M.reverse⟩
#check @ZeroParadox.Motion.mem_up_self_of_mem_up -- Statement: a value of UP is its own UP-preimage, so on UP's image the identity selects a UP-preimage
#check @CategoryTheory.IsIdempotentComplete      -- Statement: Mathlib, a category in which every idempotent splits. Reading: the general frame for the line above; not claimed of partial maps
#check @ZeroParadox.first_cell_eq_Iic            -- Statement: the seeds `α` with `nfp (ω^·) α = ε₀` are exactly `Set.Iic ε₀`. Reading: these are UP's preimages of ε₀, whose least is ⊥ of `Ordinal`, not its only one; OVER there is one-to-one, so no point has `FanIn` (next `example`)
-- Statement: OVER of the ordinal tower motion, `a ↦ ω ^ a`, is one-to-one, so no ordinal has fan-in.
example (y : Ordinal.{0}) : ¬ ZeroParadox.ordinalTowerMotion.FanIn y :=
  ZeroParadox.Motion.not_fanIn_of_injective _
    (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono.injective (fun _ _ => Iff.rfl) y
#check @Function.Surjective.hasRightInverse      -- Statement: Mathlib, a surjection has a right inverse; its footprint is printed next. Reading: prior art; the governing source is Diaconescu, "Axiom of Choice and Complementation", Proc. AMS 51 (1975), p. 176, "AC: Every epimorphism has a section"; cited, not re-proved
#print axioms Function.Surjective.hasRightInverse
-- Statement: choosing, on the image of every step function on every `α : Type`, a predecessor (a total
-- selector of the reversed motion) ⇒ the two-element choice fragment (`[propext]`).
example (h : ∀ (α : Type) (f : α → α),
    (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b => b = f a)).reverse.SelectedTotal) :
    ZeroParadox.ChoiceFragment := by
  let X := {x : (Bool → Prop) × Bool // x.1 x.2} ⊕ (Bool → Prop)
  let f : Option X → Option X := fun o => match o with
    | some (Sum.inl x) => some (Sum.inr x.1.1)
    | _ => none
  obtain ⟨g, hg⟩ := h (Option X) f
  refine ⟨fun S => match g (some (Sum.inr S)) with
    | some (Sum.inl x) => x.1.2
    | _ => true, fun S ⟨b, hb⟩ => ?_⟩
  have e : some (Sum.inr S) = f (g (some (Sum.inr S))) :=
    hg (some (Sum.inr S)) ⟨some (Sum.inl ⟨(S, b), hb⟩), rfl⟩
  show S (match g (some (Sum.inr S)) with
    | some (Sum.inl x) => x.1.2
    | _ => true)
  revert e
  generalize g (some (Sum.inr S)) = o
  rcases o with _ | (⟨⟨T, c⟩, hc⟩ | T)
  · intro e; cases e
  · intro e
    have hT : S = T := Sum.inr.inj (Option.some.inj e)
    subst hT
    exact hc
  · intro e; cases e
-- Reading: ε₀'s two faces in die terms: the tower's stages close at ε₀
-- (`ordinalTowerMotion_stageClosure`, § VIII), the supremum; UP at a seed is the least fixed point at
-- or above it (`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § I-b), the least fixed point; one point in
-- one order (`epsilon0_min_eq_max`). `Motion` carries no order, and reversal leaves UP unchanged.
#check @ZeroParadox.epsilon0_min_eq_max          -- Statement: ε₀ is the sup of the tower ∧ the least fixed point of ω^· (`IsLeast`)

/-! ### § XIII. Per face — which legs come as data, and what the others cost -/
-- Reading: three costs are kept apart: a taboo (excluded middle, the weak limited principle of
-- omniscience, the fragment); non-computability (`no_computable_registration_at_kleene_floor`, § IX);
-- and STATEMENT-CARRIED choice (`ZeroParadox/Category/ChoiceCannotBe.md`): `runMotion` and
-- `ordinalTowerMotion` each carry `[propext, Classical.choice, Quot.sound]`, and a statement that only
-- assumes a premise of either reports it (statement control, measured 2026-10-18).
-- Statement: `Motion.ofOption`: UP is data, so registration is free on every carrier
-- (`ofOption_registeredDecidable`, § IX); OVER is any relation, and a data selector on every such
-- motion gives one on every motion (`[propext]`), hence the fragment by § X's first `example`.
example (h : ∀ (α : Type) (u : α → Option α) (hu : ∀ x y, y ∈ u x → y ∈ u y) (s : α → α → Prop),
    (ZeroParadox.Motion.ofOption u hu s).SelectedData) :
    ∀ (α : Type) (M : ZeroParadox.Motion α), M.SelectedData :=
  fun α M => h α some (fun _ _ _ => rfl) M.step
-- Statement: `Bool`, UP constant `true`, OVER `≠`: registered, selected, the trichotomy at every point,
-- and no fan-in (`[propext]`).
example : let M := ZeroParadox.Motion.ofTotal (fun _ : Bool => true) (fun _ => rfl) (fun a b => a ≠ b)
    M.RegisteredDecidable ∧ M.SelectedTotal ∧ (∀ y, M.OverTrichotomy y) ∧ ∀ y, ¬ M.FanIn y :=
  ⟨ZeroParadox.Motion.registeredDecidable_of_upTotal (ZeroParadox.Motion.ofTotal_upTotal _ _ _),
   ZeroParadox.Motion.selectedTotal_of_fun (fun b => !b) (fun a b => show a ≠ b ↔ b = !a by
     cases a <;> cases b <;> decide),
   fun y => Or.inr (Or.inr ⟨!y, show y ≠ !y by cases y <;> decide, by cases y <;> decide⟩),
   fun y ⟨a, b, hab, ha, hb⟩ => by
     change a ≠ y at ha; change b ≠ y at hb
     revert hab ha hb; cases a <;> cases b <;> cases y <;> decide⟩
-- Statement: the ordinal face on `E0Note` (`ZeroParadox/Ordinal/PricedInterface.lean`), UP constant ⊤,
-- the only fixed point of OVER `e0OmegaPow` (`e0OmegaPow_fixedpoint_iff`, below): registered, selected,
-- the trichotomy at every point (`e0DecidableEq`), no fan-in, and the notation tower's stages close at
-- ⊤ (`[propext]`).
example : let M := (ZeroParadox.Motion.ofTotal (fun _ : ZeroParadox.E0Note => ⊤) (fun _ => rfl)
      (fun a b => b = ZeroParadox.e0OmegaPow a))
    M.RegisteredDecidable ∧ M.SelectedTotal ∧ (∀ y, M.OverTrichotomy y) ∧ (∀ y, ¬ M.FanIn y) ∧
      M.StageClosure (Set.range fun n => ZeroParadox.e0Coe (ZeroParadox.tower n)) (Part.some ⊤) := by
  intro M
  have inj : Function.Injective ZeroParadox.e0OmegaPow := by
    intro a b h
    induction a using WithTop.recTopCoe with
    | top =>
      induction b using WithTop.recTopCoe with
      | top => rfl
      | coe y => exact absurd h.symm WithTop.coe_ne_top
    | coe x =>
      induction b using WithTop.recTopCoe with
      | top => exact absurd h WithTop.coe_ne_top
      | coe y =>
        have h' : ZeroParadox.omegaPow (ZeroParadox.ofSyn x) =
            ZeroParadox.omegaPow (ZeroParadox.ofSyn y) :=
          congrArg ZeroParadox.ofSyn (WithTop.coe_injective h)
        unfold ZeroParadox.omegaPow at h'
        cases h'
        rfl
  exact ⟨ZeroParadox.Motion.registeredDecidable_of_upTotal (ZeroParadox.Motion.ofTotal_upTotal _ _ _),
    ZeroParadox.Motion.selectedTotal_of_fun _ (fun _ _ => Iff.rfl),
    fun y => @ZeroParadox.Motion.overTrichotomy_of_option _ M ZeroParadox.e0DecidableEq
      (fun a => some (ZeroParadox.e0OmegaPow a))
      (fun _ _ => ⟨fun h => h ▸ rfl, fun h => (Option.some_inj.1 h).symm⟩) y,
    fun y => ZeroParadox.Motion.not_fanIn_of_injective _ inj (fun _ _ => Iff.rfl) y,
    by rintro _ ⟨n, rfl⟩; exact ⟨fun h => WithTop.coe_ne_top (Part.mem_some_iff.1 h), rfl⟩⟩
-- Reading: ⊤ is adjoined by definition (`e0OmegaPow_top` is `rfl`) and `E0Note`'s order is not
-- well-founded; naming ⊤ as ε₀ crosses into `Ordinal` by `e0Repr`, whose footprint carries choice, so
-- on this face the cost moved to that map and did not vanish. Against it, `ordinalTowerMotion` meets
-- the same four cells (§§ IX–XII) with statement-carried footprints.
#check @ZeroParadox.e0Repr_eq_epsilon0_iff        -- Statement: `e0Repr a = ε₀ ↔ a = ⊤`
#check @ZeroParadox.e0OmegaPow_top                -- Statement: `e0OmegaPow ⊤ = ⊤`, by `rfl`
#check @ZeroParadox.e0OmegaPow_fixedpoint_iff     -- Statement: `e0OmegaPow a = a ↔ a = ⊤`
-- Statement: the machine face's OVER, an `Option`-valued function: the trichotomy at every point of
-- every carrier `σ : Type` gives excluded middle (`[propext]`). At `Prop`, `_ ↦ some True` returns to
-- `p` exactly when `p` holds; with `DecidableEq` it is free (`overTrichotomy_of_option`, § XI).
example (H : ∀ (σ : Type) (f : σ → Option σ) (y : σ),
    (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b => f a = some b)).OverTrichotomy y) :
    ZeroParadox.ExcludedMiddle := by
  intro p
  rcases H Prop (fun _ => some True) p with h | ⟨_, h⟩ | ⟨b, hb, hne⟩
  · exact absurd rfl (h True)
  · exact Or.inl ((h True rfl) ▸ trivial)
  · have hb' : b = True := (Option.some_inj.1 hb).symm
    subst hb'
    exact Or.inr fun hp => hne (propext ⟨fun _ => hp, fun _ => trivial⟩)
-- Statement: bit tapes `ℕ → Bool`, UP constant ⊥ (the all-false tape), OVER prepending `false`: both
-- legs are functions, registered and selected, with no fan-in (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (fun _ : ℕ → Bool => ⊥) (fun _ => rfl)
      (fun a b => b = fun n => match n with | 0 => false | k + 1 => a k))
    M.RegisteredDecidable ∧ M.SelectedTotal ∧ ∀ y, ¬ M.FanIn y :=
  ⟨ZeroParadox.Motion.registeredDecidable_of_upTotal (ZeroParadox.Motion.ofTotal_upTotal _ _ _),
   ZeroParadox.Motion.selectedTotal_of_fun _ (fun _ _ => Iff.rfl),
   fun y => ZeroParadox.Motion.not_fanIn_of_injective
     (fun a : ℕ → Bool => fun n => match n with | 0 => false | k + 1 => a k)
     (fun _ _ h => funext fun k => congrFun h (k + 1)) (fun _ _ => Iff.rfl) y⟩
-- Statement: and there the trichotomy at every point is equivalent to the weak limited principle of
-- omniscience at ⊥ of `ℕ → Bool` (`ZeroParadox/Category/ChoiceCannotBe.lean` § II), since the step
-- returns to `x` exactly when `x = ⊥` (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (fun _ : ℕ → Bool => ⊥) (fun _ => rfl)
      (fun a b => b = fun n => match n with | 0 => false | k + 1 => a k))
    (∀ y, M.OverTrichotomy y) ↔ ∀ x : ℕ → Bool, x = ⊥ ∨ x ≠ ⊥ := by
  intro M
  have fix : ∀ x : ℕ → Bool, ((fun n => match n with | 0 => false | k + 1 => x k) = x) ↔ x = ⊥ := by
    intro x
    constructor
    · intro h
      funext n
      induction n with
      | zero => exact (congrFun h 0).symm
      | succ k ih => rw [← congrFun h (k + 1)]; exact ih
    · rintro rfl; funext n; cases n <;> rfl
  constructor
  · intro H x
    rcases H x with h | ⟨h, _⟩ | ⟨b, hb, hne⟩
    · exact absurd rfl (h _)
    · exact Or.inl ((fix x).1 h.symm)
    · refine Or.inr fun hx => hne ?_
      rw [hb]; exact (fix x).2 hx
  · intro W y
    rcases W y with h | h
    · refine Or.inr (Or.inl ⟨((fix y).2 h).symm, fun b hb => ?_⟩)
      rw [hb]; exact (fix y).2 h
    · exact Or.inr (Or.inr ⟨_, rfl, fun e => h ((fix y).1 e)⟩)
-- Reading: the prediction that a face pays a taboo exactly on the legs it does not present as data
-- holds on `Motion.ofOption` (over every carrier) and on `Bool` and `E0Note` (per instance), and fails
-- on the OVER leg of the last two faces, over every carrier for the machine face and on the one carrier
-- `ℕ → Bool` for bit tapes: OVER is a function, and the trichotomy still reaches a taboo through the
-- carrier's equality, which the leg does not supply. The machine face's own UP,
-- `StateTransition.eval`, is partial and is not the leg measured here.

/-! ### § XIV. Reversing OVER by an involution of the carrier -/
-- Statement: an involution `σ` with `step a b ↔ step (σ b) (σ a)` sends each source (a point with no
-- predecessor, `M.reverse.NoStepAt`) to a sink (a point with no successor, `NoStepAt`) (`[propext]`).
-- Reading (cited, not claimed): the shape is Devaney's reversing involution, `R² = identity`, under which
-- a vector field or a diffeomorphism is R-reversible (Devaney, "Reversible diffeomorphisms and flows",
-- Trans. AMS 218 (1976) 89–113, pp. 89–90), here for a step relation and without his condition
-- `dim Fix(R) = ½ dim M`; an instance of that shape, not a generalization of his results.
example {α : Type} (M : ZeroParadox.Motion α) (σ : α → α) (hσ : Function.Involutive σ)
    (hr : ∀ a b, M.step a b ↔ M.step (σ b) (σ a)) (y : α) :
    (∀ a, ¬ M.step a y) ↔ M.NoStepAt (σ y) :=
  ⟨fun h b hb => h _ (by rw [hr, hσ] at hb; exact hb), fun h a ha => h (σ a) ((hr _ _).1 ha)⟩
#check @ZeroParadox.Motion.bijOn_sources_sinks   -- Statement: and the sources map one-to-one onto the sinks
-- Reading (cited, not claimed): folklore, of which the theorem is an instance. A digraph isomorphic to
-- its converse is self-converse (Harary and Palmer, "Enumeration of self-converse digraphs",
-- Mathematika 13 (1966); bibliographic record only, not read), and the theorem says an involutive such
-- isomorphism sends the sources onto the sinks; the poset form is Chajda and Länger, arXiv:2502.01266v1, Lemma 3.6, p. 5: for an antitone
-- involution `'` and `A ⊆ P`, "(Max A)' = Min A' and (Min A)' = Max A'". The dynamical analogue is in
-- Devaney's § IX (PDF page 26 of the copy read): for a symmetric hyperbolic critical point `p`, "by
-- R-reversibility, we have R(W^s(p)) = W^u(p)", the stable manifold sent onto the unstable one.
-- Statement: and the sinks onto the sources: the same theorem at the reversed motion (no axioms).
example {α : Type} {M : ZeroParadox.Motion α} {σ : α → α} (hσ : Function.Involutive σ)
    (hr : ∀ a b, M.step a b ↔ M.step (σ b) (σ a)) :
    Set.BijOn σ {y | M.NoStepAt y} {y | M.reverse.NoStepAt y} :=
  ZeroParadox.Motion.bijOn_sources_sinks (M := M.reverse) hσ (fun a b => hr b a)
-- Statement: the trichotomy of § XI is carried across: at `y` no step, a step to itself only, or a
-- step elsewhere holds exactly when its counterpart for predecessors holds at `σ y` (no axioms).
example {α : Type} {M : ZeroParadox.Motion α} {σ : α → α} (hσ : Function.Involutive σ)
    (hr : ∀ a b, M.step a b ↔ M.step (σ b) (σ a)) (y : α) :
    (M.NoStepAt y ↔ M.reverse.NoStepAt (σ y)) ∧ (M.SelfOnlyAt y ↔ M.reverse.SelfOnlyAt (σ y)) ∧
      (M.LeavesAt y ↔ M.reverse.LeavesAt (σ y)) := by
  have key : ∀ b, M.step y b ↔ M.reverse.step (σ y) (σ b) := fun b => hr y b
  refine ⟨⟨fun h a ha => h (σ a) ?_, fun h b hb => h (σ b) ((key b).1 hb)⟩,
    ⟨fun ⟨h1, h2⟩ => ⟨(key y).1 h1, fun a ha => ?_⟩, fun ⟨h1, h2⟩ => ⟨(key y).2 h1, fun b hb => ?_⟩⟩,
    ⟨fun ⟨b, hb, hne⟩ => ⟨σ b, (key b).1 hb, fun e => hne (hσ.injective e)⟩,
     fun ⟨a, ha, hne⟩ => ⟨σ a, (key (σ a)).2 (by rw [hσ a]; exact ha),
       fun e => hne (by rw [← e, hσ a])⟩⟩⟩
  · exact (key (σ a)).2 (by rw [hσ a]; exact ha)
  · have h := h2 (σ a) ((key (σ a)).2 (by rw [hσ a]; exact ha))
    rw [← hσ a, h]
  · exact hσ.injective (h2 (σ b) ((key b).1 hb))
-- Statement: non-member: on `OnePoint ℕ`, which is `Option ℕ`, OVER `Option.map Nat.succ` steps `∞` to
-- itself and has the source `0` and no sink; no involution reverses it (`[propext]`).
example : ¬ ∃ σ : OnePoint ℕ → OnePoint ℕ, Function.Involutive σ ∧
    ∀ a b : OnePoint ℕ, (b = Option.map Nat.succ a ↔ σ a = Option.map Nat.succ (σ b)) := by
  rintro ⟨σ, hσ, hr⟩
  have h0 : ∀ a : OnePoint ℕ, ¬ (OnePoint.some 0 = Option.map Nat.succ a) := fun a ha =>
    match a, ha with
    | none, (ha : some 0 = none) => nomatch ha
    | some n, (ha : some 0 = some (n + 1)) => Nat.succ_ne_zero n (Option.some.inj ha).symm
  refine h0 (σ (Option.map Nat.succ (σ (OnePoint.some 0)))) ?_
  have := (hr (σ (OnePoint.some 0)) (Option.map Nat.succ (σ (OnePoint.some 0)))).1 rfl
  rw [hσ] at this
  exact this
-- Statement: member on the same carrier: OVER `0 → ∞` alone, reversed by the involution exchanging `0`
-- and `∞`.
example : let σ : OnePoint ℕ → OnePoint ℕ := fun o => match o with
      | none => some 0
      | some 0 => none
      | some (n + 1) => some (n + 1)
    Function.Involutive σ ∧ ∀ a b : OnePoint ℕ,
      (a = some 0 ∧ b = none) ↔ (σ b = some 0 ∧ σ a = none) := by
  intro σ
  have l1 : ∀ b, σ b = some 0 ↔ b = none := by
    intro b
    rcases b with _ | _ | m
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    · exact ⟨fun h => absurd (Option.some.inj h) (Nat.succ_ne_zero m), fun h => (nomatch h)⟩
  have l2 : ∀ a, σ a = none ↔ a = some 0 := by
    intro a
    rcases a with _ | _ | n
    · exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun h => (nomatch h), fun h => absurd (Option.some.inj h) (Nat.succ_ne_zero n)⟩
  refine ⟨fun o => ?_, fun a b => ⟨fun ⟨ha, hb⟩ => ⟨(l1 b).2 hb, (l2 a).2 ha⟩,
    fun ⟨hb, ha⟩ => ⟨(l2 a).1 ha, (l1 b).1 hb⟩⟩⟩
  rcases o with _ | _ | n <;> rfl
-- Statement: members: `Fin 3` with OVER `0 → 1 → 2` and `Fin.rev`; `Bool` with OVER `false → true` and
-- `not`, the two-state step off ⊥ of `Bool`.
example : ∀ a b : Fin 3, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)) ↔
    ((Fin.rev b = 0 ∧ Fin.rev a = 1) ∨ (Fin.rev b = 1 ∧ Fin.rev a = 2)) := by decide
example : ∀ a b : Bool, (a = false ∧ b = true) ↔ ((!b) = false ∧ (!a) = true) := by decide
-- Statement: member: ℤ with OVER `a ↦ a + 1`, and negation (`[propext, Quot.sound]`).
example : ∀ a b : ℤ, (b = a + 1 ↔ -a = -b + 1) := fun a b => by constructor <;> intro h <;> omega
-- Statement: the ends of those motions. `Fin 3`, OVER `0 → 1 → 2`: the source is `0` and the sink `2`
-- (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : Fin 3 → Fin 3) (fun _ => rfl)
      (fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)))
    {y | M.reverse.NoStepAt y} = {0} ∧ {y | M.NoStepAt y} = {2} := by
  intro M
  refine ⟨Set.ext fun y => ?_, Set.ext fun y => ?_⟩ <;>
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, ZeroParadox.Motion.NoStepAt,
      ZeroParadox.Motion.reverse, flip, M, ZeroParadox.Motion.ofTotal] <;> revert y <;> decide
-- Statement: `Bool`, OVER `false → true`: the source is `false` and the sink `true`
-- (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl)
      (fun a b => a = false ∧ b = true))
    {y | M.reverse.NoStepAt y} = {false} ∧ {y | M.NoStepAt y} = {true} := by
  intro M
  refine ⟨Set.ext fun y => ?_, Set.ext fun y => ?_⟩ <;>
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, ZeroParadox.Motion.NoStepAt,
      ZeroParadox.Motion.reverse, flip, M, ZeroParadox.Motion.ofTotal] <;> revert y <;> decide
-- Statement: ℤ, OVER `a ↦ a + 1`: no source, no sink, and no point steps only to itself
-- (`[propext, Quot.sound]`).
example : let M := ZeroParadox.Motion.ofTotal (id : ℤ → ℤ) (fun _ => rfl) (fun a b => b = a + 1)
    (∀ y, ¬ M.reverse.NoStepAt y) ∧ (∀ y, ¬ M.NoStepAt y) ∧ ∀ y, ¬ M.SelfOnlyAt y := by
  intro M
  exact ⟨fun y h => h (y - 1) (show y = y - 1 + 1 by omega), fun y h => h (y + 1) rfl,
    fun y ⟨h, _⟩ => by change y = y + 1 at h; omega⟩
-- Statement: `OnePoint ℕ`, OVER `Option.map Nat.succ`: the only source is `0`, there is no sink, and `∞`
-- steps only to itself and is stepped into only from itself (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : OnePoint ℕ → OnePoint ℕ) (fun _ => rfl)
      (fun a b => b = Option.map Nat.succ a))
    {y | M.reverse.NoStepAt y} = {OnePoint.some 0} ∧ (∀ y, ¬ M.NoStepAt y) ∧
      M.SelfOnlyAt OnePoint.infty ∧ M.reverse.SelfOnlyAt OnePoint.infty := by
  intro M
  refine ⟨Set.ext fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y h => h _ rfl,
    ⟨rfl, fun b hb => hb⟩, ⟨rfl, fun a ha => ?_⟩⟩
  · rcases y with _ | _ | n
    · exact absurd (show M.reverse.step OnePoint.infty OnePoint.infty from rfl) (h OnePoint.infty)
    · rfl
    · exact absurd (show M.reverse.step (OnePoint.some (n + 1)) (OnePoint.some n) from rfl)
        (h (OnePoint.some n))
  · rw [Set.mem_singleton_iff] at h
    subst h
    intro a ha
    change OnePoint.some 0 = Option.map Nat.succ a at ha
    rcases a with _ | n
    · exact nomatch ha
    · exact Nat.succ_ne_zero n (Option.some.inj ha).symm
  · change OnePoint.infty = Option.map Nat.succ a at ha
    rcases a with _ | n
    · rfl
    · exact nomatch ha
-- Statement: the same carrier, OVER `0 → ∞` alone: the source that steps is `0` and the sink stepped
-- into is `∞`; a point that does neither, such as `1`, is a source and a sink at once
-- (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : OnePoint ℕ → OnePoint ℕ) (fun _ => rfl)
      (fun a b => a = OnePoint.some 0 ∧ b = OnePoint.infty))
    {y | M.reverse.NoStepAt y ∧ ∃ b, M.step y b} = {OnePoint.some 0} ∧
      {y | M.NoStepAt y ∧ ∃ a, M.step a y} = {OnePoint.infty} ∧
      M.reverse.NoStepAt (OnePoint.some 1) ∧ M.NoStepAt (OnePoint.some 1) := by
  intro M
  refine ⟨Set.ext fun y => ⟨fun ⟨_, b, hb⟩ => hb.1, fun h => ?_⟩,
    Set.ext fun y => ⟨fun ⟨_, a, ha⟩ => ha.2, fun h => ?_⟩, fun a ha => ?_, fun b hb => ?_⟩
  · rw [Set.mem_singleton_iff] at h; subst h
    exact ⟨fun a ha => (nomatch ha.2), OnePoint.infty, rfl, rfl⟩
  · rw [Set.mem_singleton_iff] at h; subst h
    exact ⟨fun b hb => (nomatch hb.1), OnePoint.some 0, rfl, rfl⟩
  · exact nomatch ha.2
  · exact absurd (Option.some.inj hb.1) (by decide)
-- Statement: the run motion: the sinks are exactly the halted configurations, and a self-looping
-- configuration steps only to itself and is no sink (`[propext, Classical.choice, Quot.sound]`, which
-- `runMotion` carries, § XIII).
example {σ : Type} (f : σ → Option σ) (s : σ) :
    (ZeroParadox.runMotion f).NoStepAt s ↔ f s = none := by
  constructor
  · intro h
    cases hf : f s with
    | none => rfl
    | some b => exact absurd (show b ∈ f s by rw [hf]; rfl) (h b)
  · intro h b hb
    change b ∈ f s at hb
    rw [h] at hb
    cases hb
example {σ : Type} (f : σ → Option σ) (s : σ) (h : ZeroParadox.LoopsInPlace f s) :
    (ZeroParadox.runMotion f).SelfOnlyAt s ∧ ¬ (ZeroParadox.runMotion f).NoStepAt s :=
  ⟨⟨show s ∈ f s by rw [h]; rfl, fun b hb => by
      change b ∈ f s at hb; rw [h] at hb; exact (Option.mem_some_iff.1 hb).symm⟩,
    fun hn => hn s (show s ∈ f s by rw [h]; rfl)⟩
-- Statement: NON-MEMBER by `bijOn_sources_sinks`: the machine `0 ↦ 2`, `1 ↦ 2`, `2` halted, on `Fin 3`
-- has the sources `0` and `1` and the one sink `2`, so no involution reverses it
-- (`[propext, Classical.choice, Quot.sound]`).
example : ¬ ∃ σ : Fin 3 → Fin 3, Function.Involutive σ ∧ ∀ a b,
    (ZeroParadox.runMotion (fun a : Fin 3 => if a = 2 then none else some 2)).step a b ↔
      (ZeroParadox.runMotion (fun a : Fin 3 => if a = 2 then none else some 2)).step (σ b) (σ a) := by
  rintro ⟨σ, hσ, hr⟩
  have hb := ZeroParadox.Motion.bijOn_sources_sinks hσ hr
  have src : ∀ y : Fin 3, y ≠ 2 →
      (ZeroParadox.runMotion (fun a : Fin 3 => if a = 2 then none else some 2)).reverse.NoStepAt y := by
    intro y hy a ha
    change y ∈ (if a = 2 then none else some 2) at ha
    revert ha hy; revert a y; decide
  have snk : ∀ y : Fin 3,
      (ZeroParadox.runMotion (fun a : Fin 3 => if a = 2 then none else some 2)).NoStepAt y → y = 2 := by
    intro y hy
    by_contra hne
    fin_cases y
    · exact hy 2 (show (if (0 : Fin 3) = 2 then none else some 2) = some 2 from rfl)
    · exact hy 2 (show (if (1 : Fin 3) = 2 then none else some 2) = some 2 from rfl)
    · exact hne rfl
  have h0 := snk _ (hb.mapsTo (src 0 (by decide)))
  have h1 := snk _ (hb.mapsTo (src 1 (by decide)))
  exact absurd (hσ.injective (h0.trans h1.symm)) (by decide)
-- Statement: the converse fails: on `Fin 4` with OVER `0 → 1 → 2 → 3` and `0 → 2`, the one source is `0`
-- and the one sink `3`, and no involution reverses it (`[propext]`).
example : ¬ ∃ σ : Fin 4 → Fin 4, Function.Involutive σ ∧
    ∀ a b : Fin 4, ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 0 ∧ b = 2)) ↔
      ((σ b = 0 ∧ σ a = 1) ∨ (σ b = 1 ∧ σ a = 2) ∨ (σ b = 2 ∧ σ a = 3) ∨ (σ b = 0 ∧ σ a = 2)) := by
  rintro ⟨σ, hσ, hr⟩
  have noPred0 : ∀ a : Fin 4, ¬ ((a = 0 ∧ (0 : Fin 4) = 1) ∨ (a = 1 ∧ (0 : Fin 4) = 2) ∨
      (a = 2 ∧ (0 : Fin 4) = 3) ∨ (a = 0 ∧ (0 : Fin 4) = 2)) := by decide
  have s0 : ∀ b : Fin 4, ¬ ((σ 0 = 0 ∧ b = 1) ∨ (σ 0 = 1 ∧ b = 2) ∨ (σ 0 = 2 ∧ b = 3) ∨
      (σ 0 = 0 ∧ b = 2)) := by
    intro b hb
    apply noPred0 (σ b)
    have := (hr (σ b) 0).2
    rw [hσ b] at this
    exact this hb
  have e0 : σ 0 = 3 := by
    revert s0; generalize σ 0 = x; revert x; decide
  have e1 : σ 1 = 2 := by
    have h := (hr 0 1).1 (Or.inl ⟨rfl, rfl⟩)
    rw [e0] at h
    revert h; generalize σ 1 = x; revert x; decide
  have e2 : σ 2 = 2 := by
    have h := (hr 0 2).1 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    rw [e0] at h
    revert h; generalize σ 2 = x; revert x; decide
  exact absurd (hσ.injective (e1.trans e2.symm)) (by decide)
-- Statement: and there the source is `0` and the sink `3` (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : Fin 4 → Fin 4) (fun _ => rfl)
      (fun a b => (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 0 ∧ b = 2)))
    {y | M.reverse.NoStepAt y} = {0} ∧ {y | M.NoStepAt y} = {3} := by
  intro M
  refine ⟨Set.ext fun y => ?_, Set.ext fun y => ?_⟩ <;>
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, ZeroParadox.Motion.NoStepAt,
      ZeroParadox.Motion.reverse, flip, M, ZeroParadox.Motion.ofTotal] <;> revert y <;> decide
-- Statement: counting a self-loop as an end: the points stepped into only from themselves or from
-- nothing map one-to-one onto the points stepping only to themselves or nowhere (no axioms) ...
example {α : Type} {M : ZeroParadox.Motion α} {σ : α → α} (hσ : Function.Involutive σ)
    (hr : ∀ a b, M.step a b ↔ M.step (σ b) (σ a)) :
    Set.BijOn σ {y | ∀ a, M.step a y → a = y} {y | ∀ b, M.step y b → b = y} := by
  refine ⟨fun y hy b hb => ?_, hσ.injective.injOn, fun z hz => ⟨σ z, fun a ha => ?_, hσ z⟩⟩
  · have h := (hr (σ b) y).2 (by rw [hσ b]; exact hb)
    rw [← hσ b, hy _ h]
  · have h := (hr a (σ z)).1 ha
    rw [hσ z] at h
    rw [← hσ a, hz _ h]
-- Statement: ... and on `OnePoint ℕ` under `Option.map Nat.succ` the first set is `{0, ∞}` and the
-- second `{∞}`, so that count refuses a reversal too (`[propext, Quot.sound]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : OnePoint ℕ → OnePoint ℕ) (fun _ => rfl)
      (fun a b => b = Option.map Nat.succ a))
    {y | ∀ a, M.step a y → a = y} = {OnePoint.some 0, OnePoint.infty} ∧
      {y | ∀ b, M.step y b → b = y} = {OnePoint.infty} := by
  intro M
  refine ⟨Set.ext fun y => ⟨fun h => ?_, fun h => ?_⟩, Set.ext fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases y with _ | _ | n
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact absurd (h (OnePoint.some n) rfl) (fun e => by have := Option.some.inj e; omega)
  · rcases h with rfl | rfl
    · intro a ha
      change OnePoint.some 0 = Option.map Nat.succ a at ha
      rcases a with _ | n
      · exact nomatch ha
      · exact absurd (Option.some.inj ha).symm (Nat.succ_ne_zero n)
    · intro a ha
      change OnePoint.infty = Option.map Nat.succ a at ha
      rcases a with _ | n
      · rfl
      · exact nomatch ha
  · rcases y with _ | n
    · rfl
    · exact absurd (h _ rfl) (fun e => by have := Option.some.inj e; omega)
  · rw [Set.mem_singleton_iff] at h; subst h
    intro b hb; exact hb
-- Statement: the adjoined points. `Option σ` under `Option.map f`: `none` steps only to itself and is
-- stepped into only from itself, so it is neither a source nor a sink (`[propext]`).
example {σ : Type} (f : σ → σ) : let M := (ZeroParadox.Motion.ofTotal (id : Option σ → Option σ)
      (fun _ => rfl) (fun a b => b = Option.map f a))
    M.SelfOnlyAt none ∧ M.reverse.SelfOnlyAt none ∧ ¬ M.NoStepAt none ∧ ¬ M.reverse.NoStepAt none := by
  intro M
  refine ⟨⟨rfl, fun b hb => hb⟩, ⟨rfl, fun a ha => ?_⟩, fun h => h none rfl, fun h => h none rfl⟩
  change none = Option.map f a at ha
  rcases a with _ | x
  · rfl
  · exact nomatch ha
-- Statement: `TriStep σ` as the codomain of a step `g`: on `σ` with OVER `g a = step b`, a configuration
-- at either adjoined value, `halted` or `idle`, has no step (`[propext]`).
example {σ : Type} (g : σ → ZeroParadox.TriStep σ) (s : σ)
    (h : g s = ZeroParadox.TriStep.halted ∨ g s = ZeroParadox.TriStep.idle) :
    (ZeroParadox.Motion.ofTotal (id : σ → σ) (fun _ => rfl)
      (fun a b => g a = ZeroParadox.TriStep.step b)).NoStepAt s := by
  intro b hb
  change g s = ZeroParadox.TriStep.step b at hb
  rcases h with h | h <;> rw [h] at hb <;> exact nomatch hb
-- Statement: `E0Note` under `e0OmegaPow`: ⊤ of `E0Note`, the adjoined point, steps only to itself and
-- is stepped into only from itself, and `e0Coe 0` is a source (`[propext]`).
example : let M := (ZeroParadox.Motion.ofTotal (id : ZeroParadox.E0Note → ZeroParadox.E0Note)
      (fun _ => rfl) (fun a b => b = ZeroParadox.e0OmegaPow a))
    M.SelfOnlyAt ⊤ ∧ M.reverse.SelfOnlyAt ⊤ ∧ M.reverse.NoStepAt (ZeroParadox.e0Coe 0) := by
  intro M
  refine ⟨⟨rfl, fun b hb => hb⟩, ⟨rfl, fun a ha => ?_⟩, fun a ha => ?_⟩
  · change ⊤ = ZeroParadox.e0OmegaPow a at ha
    induction a using WithTop.recTopCoe with
    | top => rfl
    | coe x => exact absurd ha.symm WithTop.coe_ne_top
  · change ZeroParadox.e0Coe 0 = ZeroParadox.e0OmegaPow a at ha
    induction a using WithTop.recTopCoe with
    | top => exact absurd ha WithTop.coe_ne_top
    | coe x =>
      have h' := WithTop.coe_injective ha
      unfold ZeroParadox.omegaPow at h'
      exact nomatch congrArg ZeroParadox.ofSyn h'
#check @ZeroParadox.rInv_conj_rScale             -- Statement: on `OnePoint ℚ_[2]`, `rInv ∘ rScale n ∘ rInv = rScale (-n)`
-- Statement: `OnePoint ℚ_[2]` under `rScale n`: `rInv` reverses the motion, `0` and `∞` each step only
-- to themselves, and there is no source and no sink (`[propext, Classical.choice, Quot.sound]`).
example (n : ℤ) : let M := (ZeroParadox.Motion.ofTotal (id : ZeroParadox.Sphere → ZeroParadox.Sphere)
      (fun _ => rfl) (fun a b => b = ZeroParadox.rScale n a))
    (∀ a b, M.step a b ↔ M.step (ZeroParadox.rInv b) (ZeroParadox.rInv a)) ∧
      M.SelfOnlyAt (OnePoint.some 0) ∧ M.SelfOnlyAt OnePoint.infty ∧
      (∀ y, ¬ M.reverse.NoStepAt y) ∧ (∀ y, ¬ M.NoStepAt y) := by
  intro M
  have inv : ∀ z, ZeroParadox.rScale n (ZeroParadox.rScale (-n) z) = z := fun z => by
    rw [ZeroParadox.rScale_add, add_neg_cancel, ZeroParadox.rScale_zero]; rfl
  have inv' : ∀ z, ZeroParadox.rScale (-n) (ZeroParadox.rScale n z) = z := fun z => by
    rw [ZeroParadox.rScale_add, neg_add_cancel, ZeroParadox.rScale_zero]; rfl
  have conj : ∀ z, ZeroParadox.rScale n (ZeroParadox.rInv z) =
      ZeroParadox.rInv (ZeroParadox.rScale (-n) z) := fun z => by
    rw [← ZeroParadox.rInv_conj_rScale n z, ZeroParadox.rInv_involutive]
  refine ⟨fun a b => ?_, ⟨(ZeroParadox.rScale_fixes_poles n).1.symm,
      fun b hb => hb.trans (ZeroParadox.rScale_fixes_poles n).1⟩,
    ⟨rfl, fun b hb => hb⟩, fun y h => h (ZeroParadox.rScale (-n) y) (inv y).symm, fun y h => h _ rfl⟩
  change b = ZeroParadox.rScale n a ↔ ZeroParadox.rInv a = ZeroParadox.rScale n (ZeroParadox.rInv b)
  rw [conj]
  constructor
  · rintro rfl; rw [inv']
  · intro h
    rw [ZeroParadox.rInv_involutive.injective h, inv]
#check @ZeroParadox.rInv_swaps                    -- Statement: `rInvHomeo` sends `0` to `∞` and `∞` to `0` on `OnePoint ℚ_[2]`: the INVERSION witness, two distinct points exchanged, not the coincidence
-- Reading: Tim's reading of the two ends, measured. A source (nothing steps in) and a sink (nothing
-- steps out) are roles of the MOTION, not points of its carrier, and a reversal maps the first
-- one-for-one onto the second (`bijOn_sources_sinks`), as `0` and `∞` under `0 → ∞` on `OnePoint ℕ`.
-- Read as the motion's local 0 and local ∞ they pair with the pole ⊥ = 0 = ∞, a chart claim
-- (`ZeroParadox/BottomCannotBe.lean` § INVERSION), as a reading, not an identity. The implication runs
-- one way: a reversal matches the ends, matched ends force no reversal (`Fin 4`), and a reversal needs
-- no ends (ℤ). An adjoined point that the motion maps to itself is not an end in the no-step sense (in
-- the self-loop count above it falls in both sets): it steps only to itself and is stepped into only
-- from itself, INVARIANT under reversal (`Option.map`; ⊤ of `E0Note`; `∞` of `OnePoint ℚ_[2]` under
-- `rScale n`, where `0`, not adjoined, behaves the same, `rInv` reverses the motion, and `rInv_swaps`
-- exchanges the two). ⊤ of `E0Note` is the point `e0Repr` sends to ε₀, and ε₀ is the minimum step
-- next to the pole, never the pole (`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § III); it sits
-- in that list beside `∞` as a self-loop, not as the pole's infinity. An
-- adjoined value in the step's codomain gives a sink instead (`runMotion`; both `TriStep` values, which
-- the relation does not tell apart). Under a function a halted and a self-looping configuration share
-- a fate (§ XI); under reversal the first goes to a source and the second to a point stepped into only
-- from itself. The adjoined-points switch (§ I) counts points of the carrier, not ends of a motion, and
-- stands as stated in § I.

/-! ### § XV. Diagonal faces as inputs to the die's motion: carrier, map, witness, quotient -/
-- Reading: each face below enters as INPUTS: a carrier `β` and a self-map `g` (or a relation); the
-- Lawvere and Cantor entries and the computability witness also take a class of admissible maps with
-- a witness (`HasWitnessRel`); Rice, Löb and the biproduct entries take a quotient, where the face's
-- fixed point holds only up to an equivalence. No classification of the faces is claimed. Reading
-- (cited, not claimed): the sources treat Cantor, Russell and Tarski (Lawvere 1969, TAC reprint p. 3,
-- "a fixed-point theorem ... which seems to play this role" for Cantor, Russell, Gödel and Tarski),
-- and, extending Lawvere, the halting problem (Yanofsky 2003, pp. 11–12), the diagonal lemma
-- (Theorem 4, pp. 15–16) and Löb's paradox (p. 18), the recursion theorem (pp. 18–19) and Rice (p. 19).
#check @ZeroParadox.Motion.ofFun                 -- Statement: encoding 1: UP the identity, OVER the graph of `g`
#check @ZeroParadox.Motion.selfOnlyAt_ofFun_iff  -- Statement: there `y` steps to itself only iff `g y = y`; both directions
#check @ZeroParadox.Motion.leavesAt_ofFun_iff    -- Statement: and `y` steps elsewhere iff `g y ≠ y`; both directions
#check @ZeroParadox.Motion.not_selfOnlyAt_and_leavesAt -- Statement: no point does both, in any motion
#check @ZeroParadox.Motion.ofFixedPoints         -- Statement: encoding 2: UP the partial identity on the fixed points of `g`, OVER the graph of `g`
#check @ZeroParadox.Motion.isLanding_ofFixedPoints_iff -- Statement: there `y` is a landing iff `g y = y`; both directions
-- Statement: in encoding 2, UP is total iff `g` is the identity; both directions.
example {β : Type} (g : β → β) : (ZeroParadox.Motion.ofFixedPoints g).UpTotal ↔ ∀ x, g x = x := Iff.rfl
#check @ZeroParadox.Motion.not_corner_of_fun     -- Statement: if OVER is the graph of a function `g` and every landing is fixed by `g`, no corner; one way, any UP
#check @ZeroParadox.Motion.not_corner_ofFixedPoints -- Statement: so encoding 2 never fires the corner
#check @ZeroParadox.Motion.corner_ofTotal_iff    -- Statement: if UP `r` is idempotent with the fixed points of `g`, and OVER is the graph of `h`, the corner fires iff some fixed point `y` of `g` has `h y` not fixed by `g`; both directions
-- Statement: CONTROL: with `h = g` the corner does not fire: the ordinal tower motion (UP `nfp (ω^·)`,
-- OVER `ω^·`).
example : ¬ ZeroParadox.ordinalTowerMotion.{0}.Corner := fun hc => by
  have hn := Ordinal.isNormal_opow Ordinal.one_lt_omega0
  obtain ⟨y, hy, hn'⟩ := (ZeroParadox.Motion.corner_ofTotal_iff
    (Ordinal.nfp fun a => Ordinal.omega0 ^ a) (fun a => Ordinal.omega0 ^ a)
    (fun a => Ordinal.omega0 ^ a) (fun x => Ordinal.nfp_eq_self (Ordinal.nfp_fp hn x))
    (fun x => ⟨fun h => h ▸ Ordinal.nfp_fp hn x, Ordinal.nfp_eq_self⟩)).1 hc
  exact hn' (by rw [hy, hy])
#check @ZeroParadox.ordinalSuccMotion_corner     -- Statement: with OVER `Order.succ` instead (`ordinalSuccMotion`), the corner fires at ε₀
#check @ZeroParadox.selfOnlyAt_of_witnessRel     -- Statement: Lawvere: if `β` has a witness relative to `M` and `M g`, some point steps to itself only in `ofFun g`; one way
#check @ZeroParadox.hasLanding_ofFixedPoints_of_witnessRel -- Statement: and encoding 2 then has a landing; one way
#check @ZeroParadox.no_witnessRel_of_leavesAt    -- Statement: Cantor: if `M g` and `ofFun g` steps elsewhere everywhere, no witness relative to `M`; one way
-- Statement: CONTROL: `Bool` negation steps elsewhere everywhere, so `Bool` has no witness relative to
-- the class of all maps.
example : ¬ ZeroParadox.HasWitnessRel Bool (fun _ => True) :=
  ZeroParadox.no_witnessRel_of_leavesAt (g := fun b => !b) trivial
    fun b => (ZeroParadox.Motion.leavesAt_ofFun_iff _ b).2 (by cases b <;> decide)
-- Statement: Cantor, Russell, Tarski (`cantor_via_engine`, `russell_via_engine`,
-- `tarski_no_internal_truth`): no `e : A → (A → Prop)` is onto, since `ofFun Not` steps elsewhere at
-- every proposition.
example {A : Type} (e : A → (A → Prop)) : ¬ Function.Surjective e := fun he =>
  let ⟨b, hb⟩ := Function.exists_fixed_point_of_surjective e he Not
  ZeroParadox.Motion.not_selfOnlyAt_and_leavesAt _ b
    ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff Not b).2 hb, ZeroParadox.Motion.leavesAt_ofFun_not b⟩
-- Statement: Turing (`no_self_decider`): the same with `Bool` and `not`.
example {A : Type} (e : A → (A → Bool)) : ¬ Function.Surjective e := fun he =>
  let ⟨b, hb⟩ := Function.exists_fixed_point_of_surjective e he (fun b => !b)
  ZeroParadox.Motion.not_selfOnlyAt_and_leavesAt _ b
    ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ b).2 hb,
      (ZeroParadox.Motion.leavesAt_ofFun_iff _ b).2 (ZeroParadox.bool_not_no_fixedpoint b)⟩
-- Statement: Curry: some proposition steps to itself only in `ofFun (· → P)` iff `P`; both directions
-- (`curry_paradox` one way, `True` the other).
example (P : Prop) : (∃ y, (ZeroParadox.Motion.ofFun (fun q : Prop => q → P)).SelfOnlyAt y) ↔ P := by
  constructor
  · rintro ⟨y, hy⟩
    exact ZeroParadox.curry_paradox
      (iff_of_eq ((ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ y).1 hy)).symm
  · intro hP
    exact ⟨True, (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2
      (propext ⟨fun _ => trivial, fun _ _ => hP⟩)⟩
-- Statement: self-application (`AbstractSelfApp`): `y` steps to itself only in `ofFun selfApp` iff `y`
-- is ⊥ of the `ZPSemilattice`; both directions, from the class fields `fixed_bot` and `unique_fp`.
example {L : Type} [ZeroParadox.ZPSemilattice L] [ZeroParadox.AbstractSelfApp L] (y : L) :
    (ZeroParadox.Motion.ofFun (ZeroParadox.AbstractSelfApp.selfApp (L := L))).SelfOnlyAt y ↔
      y = ZeroParadox.ZPSemilattice.bot :=
  (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ y).trans
    ⟨ZeroParadox.AbstractSelfApp.unique_fp y, fun h => h ▸ ZeroParadox.AbstractSelfApp.fixed_bot⟩
-- Statement: the Knaster–Tarski fork: exactly one point steps to itself only in `ofFun f` iff
-- `f.lfp = f.gfp`; both directions (`fork_collapse_iff`).
example {α : Type} [CompleteLattice α] (f : α →o α) :
    (∃! y, (ZeroParadox.Motion.ofFun f).SelfOnlyAt y) ↔ f.lfp = f.gfp :=
  (existsUnique_congr fun y => ZeroParadox.Motion.selfOnlyAt_ofFun_iff f y).trans
    (ZeroParadox.fork_collapse_iff f).symm
-- Statement: OVER a relation `r` with UP the identity: if `r` is well-founded, no point steps to itself
-- only (`wf_no_selfloop`); one way.
example {α : Type} {r : α → α → Prop} (h : WellFounded r) (y : α) :
    ¬ (ZeroParadox.Motion.ofTotal id (fun _ => rfl) r).SelfOnlyAt y :=
  fun hy => ZeroParadox.wf_no_selfloop h y hy.1
-- Statement: `ZFSet` with OVER `a → b` when `b ∈ a`: `x` steps to itself only iff `x = {x}`; both
-- directions. No `ZFSet` does (`no_quine_atom`).
example (x : ZFSet) :
    ((ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b : ZFSet => b ∈ a)).SelfOnlyAt x ↔ x = {x}) ∧
      ¬ (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b : ZFSet => b ∈ a)).SelfOnlyAt x := by
  refine ⟨⟨fun ⟨hx, hu⟩ => ZFSet.ext fun z => ?_, fun h => ⟨?_, fun b hb => ?_⟩⟩,
    fun h => ZeroParadox.no_quine_atom x h.1⟩
  · rw [ZFSet.mem_singleton]; exact ⟨hu z, fun h => h ▸ hx⟩
  · have hs : x ∈ ({x} : ZFSet) := ZFSet.mem_singleton.2 rfl
    rw [← h] at hs; exact hs
  · rw [h] at hb; exact ZFSet.mem_singleton.1 hb
-- Statement: `QuineHost`'s two fields give a self-step at ⊥ of the host and do not give `SelfOnlyAt`:
-- on `Bool` with `mem x y := y = false` (the control in `ZeroParadox/Settheory/QuineHost.lean`), OVER
-- `a → b` when `b` is a member of `a` steps `false` to itself and to `true`.
example : let M := ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a _ => a = false)
    M.step false false ∧ M.LeavesAt false ∧ ¬ M.SelfOnlyAt false :=
  ⟨rfl, ⟨true, rfl, by decide⟩, fun ⟨_, h⟩ => absurd (h true rfl) (by decide)⟩
-- Statement: ℤ_[2]: add one steps elsewhere at every point (`succ_ne_self`); doubling steps to itself
-- only exactly at 0; both directions.
example (x : ℤ_[2]) : (ZeroParadox.Motion.ofFun (· + (1 : ℤ_[2]))).LeavesAt x ∧
    ((ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).SelfOnlyAt x ↔ x = 0) :=
  ⟨(ZeroParadox.Motion.leavesAt_ofFun_iff _ x).2 (succ_ne_self x)
,
    (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ x).trans
      ⟨fun h => by linear_combination h, fun h => by rw [h, mul_zero]⟩⟩
-- Statement: partial digit streams (`ZeroParadox/Category/LawvereTwoAdic.lean`): `partialAddOne` steps
-- to itself only exactly at `[]`; `partialDouble` steps elsewhere at every stream.
example (w : List Bool) : ((ZeroParadox.Motion.ofFun ZeroParadox.partialAddOne).SelfOnlyAt w ↔ w = []) ∧
    (ZeroParadox.Motion.ofFun ZeroParadox.partialDouble).LeavesAt w :=
  ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ w).trans (ZeroParadox.partialAddOne_fixed_iff w),
    (ZeroParadox.Motion.leavesAt_ofFun_iff _ w).2 (ZeroParadox.partialDouble_ne_self w)⟩
-- Statement: `QuineAtomHost`'s (Y') does give it: with OVER `a → b` when `b` is a member of `a`, ⊥ steps
-- to itself only.
example {L : Type} [ZeroParadox.QuineAtomHost L] :
    (ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => ZeroParadox.QuineAtomHost.mem b a)).SelfOnlyAt ZeroParadox.QuineAtomHost.bot :=
  ⟨(ZeroParadox.QuineAtomHost.bot_mem_iff _).2 rfl,
    fun b hb => (ZeroParadox.QuineAtomHost.bot_mem_iff b).1 hb⟩
#check @ZeroParadox.Motion.ofPartialFun          -- Statement: a partial self-map `g : β → Option β`: UP the identity, OVER `g x = some y`
#check @ZeroParadox.Motion.noStepAt_ofPartialFun_iff -- Statement: no step at `y` iff `g y = none`; both directions
#check @ZeroParadox.Motion.selfOnlyAt_ofPartialFun_iff -- Statement: a step to itself only iff `g y = some y`; both directions
#check @ZeroParadox.Motion.leavesAt_ofPartialFun_iff -- Statement: a step elsewhere iff `g y = some b`, `b ≠ y`; both directions
-- Statement: the nowhere-defined partial map on `Bool` has no step at any point: the third value of
-- the trichotomy, which a total map never takes.
example (y : Bool) : (ZeroParadox.Motion.ofPartialFun (fun _ : Bool => (none : Option Bool))).NoStepAt y :=
  (ZeroParadox.Motion.noStepAt_ofPartialFun_iff _ y).2 rfl
-- Statement: adjoin one point: if every admissible map on `Option β` is a lift `x ↦ x.bind g`, no
-- admissible map is fixed-point-free, since each fixes `none`; so the Cantor route
-- (`no_witnessRel_of_admissible_fpf`) has no admissible input there; one way.
example {β : Type} (M : (Option β → Option β) → Prop)
    (hM : ∀ f, M f → ∃ g : β → Option β, f = fun x => x.bind g) :
    ¬ ∃ f, M f ∧ ∀ x, f x ≠ x := by
  rintro ⟨f, hf, hfpf⟩
  obtain ⟨g, rfl⟩ := hM f hf
  exact hfpf none rfl
-- Statement: CONTROL: `Bool` negation fixes no `Bool`, and its lift fixes `none`.
example : (∀ b : Bool, (!b) ≠ b) ∧ (none : Option Bool).bind (fun b => some (!b)) = none :=
  ⟨by decide, rfl⟩
-- Statement: biproduct diagonal on isomorphism classes of `ModuleCat ℂ` (the quotient by `≅`): a
-- finite-dimensional `X` whose class steps to itself only under `Y ↦ Y ⊞ Y` is zero
-- (`biprod_diagonal_only_zero`); one way. `freeNat`, not finite, has a class that does and is not zero.
open CategoryTheory CategoryTheory.Limits in
example (X : ModuleCat.{0} ℂ) [Module.Finite ℂ X] :
    let D : Quotient (isIsomorphicSetoid (ModuleCat.{0} ℂ)) → Quotient (isIsomorphicSetoid _) :=
      Quotient.map (fun Y : ModuleCat.{0} ℂ => Y ⊞ Y) (fun _ _ ⟨i⟩ => ⟨biprod.mapIso i i⟩)
    ((ZeroParadox.Motion.ofFun D).SelfOnlyAt ⟦X⟧ → IsZero X) ∧
      (ZeroParadox.Motion.ofFun D).SelfOnlyAt ⟦ZeroParadox.freeNat⟧ ∧ ¬ IsZero ZeroParadox.freeNat := by
  intro D
  refine ⟨fun h => ?_, (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2
    (Quotient.sound ⟨ZeroParadox.freeNat_biprod_self.symm⟩), ZeroParadox.freeNat_not_isZero⟩
  obtain ⟨i⟩ := (Quotient.exact ((ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).1 h) :
    IsIsomorphic (X ⊞ X) X)
  exact ZeroParadox.biprod_diagonal_only_zero X ⟨i.symm⟩
#check @ZeroParadox.ProvabilityLogic.loebMapQuot -- Statement: Löb's `p ↦ (□p → A)` on the Lindenbaum quotient (provable equivalence)
#check @ZeroParadox.ProvabilityLogic.selfOnlyAt_loebMapQuot_iff -- Statement: a class steps to itself only iff it is a Löb diagonal for `A`; both directions
#check @ZeroParadox.ProvabilityLogic.loeb_of_selfOnlyAt -- Statement: if such a class exists and `⊢ □A → A`, then `⊢ A`; one way
-- Statement: Gödel's second theorem in the same form (`godel_two`): if a class steps to itself only
-- under `p ↦ (□p → falsum)` and `⊬ falsum`, then `⊬ □falsum → falsum`. The diagonal is a hypothesis.
example {S : Type} [ZeroParadox.ProvabilityLogic S] {falsum : S} (psi : S)
    (hy : (ZeroParadox.Motion.ofFun (ZeroParadox.ProvabilityLogic.loebMapQuot falsum)).SelfOnlyAt
      (⟦psi⟧ : ZeroParadox.ProvabilityLogic.Lindenbaum S))
    (hcon : ¬ ZeroParadox.ProvabilityLogic.Thm falsum) :
    ¬ ZeroParadox.ProvabilityLogic.Thm
      (ZeroParadox.ProvabilityLogic.imp (ZeroParadox.ProvabilityLogic.box falsum) falsum) :=
  fun h => hcon (ZeroParadox.ProvabilityLogic.loeb_of_selfOnlyAt psi hy h)
#check @ZeroParadox.hasWitnessRel_evalClass      -- Statement: codes up to equal `eval` carry a witness relative to the maps induced by computable `eval`-respecting maps
#check @ZeroParadox.no_witnessRel_evalClass_top  -- Statement: CONTROL: relative to the class of all maps on that quotient, none
-- Statement: so every such induced map has a class that steps to itself only in `ofFun`.
example (G : ZeroParadox.EvalClass → ZeroParadox.EvalClass) (hG : ZeroParadox.ComputableOnEval G) :
    ∃ y, (ZeroParadox.Motion.ofFun G).SelfOnlyAt y :=
  ZeroParadox.selfOnlyAt_of_witnessRel ZeroParadox.hasWitnessRel_evalClass hG
#check @ZeroParadox.rice_of_evalClassWitness     -- Statement: Rice's theorem (`rice_face` cites Mathlib), proved through that witness
#check @ZeroParadox.occurrence_undecidable       -- Statement: occurrence at `n` is not a `ComputablePred`
-- Statement: occurrence at `n` respects `eval` and is not a `ComputablePred`, through the witness.
example (n : ℕ) : ¬ ComputablePred (fun c : Nat.Partrec.Code => ZeroParadox.Occurs c n) := by
  obtain ⟨cn, hcn⟩ := Nat.Partrec.Code.exists_code.1 Nat.Partrec.none
  refine ZeroParadox.rice_of_evalClassWitness {c | ZeroParadox.Occurs c n}
    (fun x y e => by simp only [Set.mem_setOf_eq, ZeroParadox.occurs_iff_halts, e])
    (a := Nat.Partrec.Code.zero) (b := cn) ?_ ?_
  · show ZeroParadox.Occurs _ n
    rw [ZeroParadox.occurs_iff_halts]; exact (trivial : (Part.some 0).Dom)
  · show ¬ ZeroParadox.Occurs cn n
    rw [ZeroParadox.occurs_iff_halts, hcn]; exact Part.not_none_dom
#check @ZeroParadox.evalStepMotion_not_selfOnlyAt -- Statement: with OVER `eval b = F a` on codes, no code steps to itself only (padding)
#check @ZeroParadox.universalStepMotion_leavesAt_of_step -- Statement: CONTROL: on universal codes, a self-step still leaves
#check @ZeroParadox.selfPrintsStepMotion_selfOnlyAt_of_step -- Statement: on self-printing codes, a self-step is a step to itself only; one way
#check @ZeroParadox.exists_selfPrintsStepMotion_selfOnlyAt -- Statement: and a self-printing universal code does so
#check @ZeroParadox.selfref_universal_infinite   -- Statement: infinitely many codes are self-printing and universal
#check @ZeroParadox.shiftMotion                  -- Statement: on inputs, OVER `n ↦ ⌜c⌝ + n` (`quine_period_is_goedel`), UP `n ↦ n % ⌜c⌝` (a choice of encoding)
#check @ZeroParadox.isComputationalQuine_iff_eval_mod -- Statement: `c` is a computational quine iff `eval c` is constant on the fibres of that UP; both directions
#check @ZeroParadox.shiftMotion_corner_iff       -- Statement: the corner fires iff `⌜c⌝ ≠ 0`; both directions
-- Statement: ZP-M's two sides, two conjuncts with no `Code`/`Ordinal` equation: some computational
-- quine's `shiftMotion` loops and does not climb; `ordinalSuccMotion` climbs and does not loop.
example :
    (∃ c : Nat.Partrec.Code, ZeroParadox.IsComputationalQuine c ∧ (ZeroParadox.shiftMotion c).Loop ∧
      ¬ (ZeroParadox.shiftMotion c).Climb) ∧
    (ZeroParadox.ordinalSuccMotion.{0}.Climb ∧ ¬ ZeroParadox.ordinalSuccMotion.{0}.Loop) := by
  refine ⟨?_, ZeroParadox.ordinalSuccMotion_climb, ZeroParadox.ordinalSuccMotion_not_loop⟩
  obtain ⟨c, hc, hk⟩ := ZeroParadox.infinite_quine_family 0
  exact ⟨c, hc, ZeroParadox.shiftMotion_loop c (by omega),
    ZeroParadox.Motion.not_climb_of_upStepInvariant (ZeroParadox.shiftMotion_upStepInvariant c)⟩
-- Statement: CONTROL: `Code.zero` is a computational quine with Gödel number 0, and its `shiftMotion`
-- has no corner.
example : ZeroParadox.IsComputationalQuine Nat.Partrec.Code.zero ∧
    ¬ (ZeroParadox.shiftMotion Nat.Partrec.Code.zero).Corner := by
  have hz : Encodable.encode Nat.Partrec.Code.zero = 0 := by decide
  refine ⟨?_, fun h => (ZeroParadox.shiftMotion_corner_iff _).1 h hz⟩
  show Nat.Partrec.Code.eval Nat.Partrec.Code.zero = ZeroParadox.selfApply Nat.Partrec.Code.zero
  funext n; simp [ZeroParadox.selfApply, hz]
#check @ZeroParadox.ordinalSuccMotion_up_succ_epsilon0 -- Statement: there UP sends `succ ε₀` to ε₁
#check @ZeroParadox.selfOnlyAt_ofFun_app_iff     -- Statement: for `S : SelfContained C`, `x` steps to itself only in `ofFun S.app` iff `x = S.bot`; both directions
#check @ZeroParadox.wem_of_decidable_selfOnlyAt_glue -- Statement: deciding that at the glued point, uniformly in `p`, gives weak excluded middle; one way

/-! ### § XVI. The over-then-up / up-then-over pair, and leg polarity against a carrier order -/
#check @ZeroParadox.Motion.Elbow                 -- Statement: up-then-over: `up x = y ≠ x`, and `y` steps, possibly to itself
-- Reading: `Corner` (over-then-up) and `Elbow` (up-then-over) are a pair; neither is the preferred member.
#check @ZeroParadox.Motion.corner_elbow_of_over_up_over -- Statement: a run OVER, UP, OVER from a landing gives a corner and an elbow
#check @ZeroParadox.Motion.corner_elbow_of_up_over_up -- Statement: a run UP, OVER, UP gives a corner and an elbow
#check @ZeroParadox.Motion.elbow_reverse_iff     -- Statement: reversed, an elbow is UP and OVER arriving at one point
#check @ZeroParadox.Motion.corner_reverse_iff    -- Statement: reversed, a corner is OVER and UP leaving one point
-- Statement: CONTROL: a corner without an elbow, on `Fin 3`: UP `1 ↦ 2`, OVER only `0 → 1`.
example : let M := (ZeroParadox.Motion.ofTotal (fun x : Fin 3 => if x = 1 then 2 else x) (by decide)
      (fun a b => a = 0 ∧ b = 1))
    M.Corner ∧ ¬ M.Elbow := by
  refine ⟨⟨0, 1, 2, Part.mem_some_iff.2 (by decide), ⟨rfl, rfl⟩, Part.mem_some_iff.2 (by decide),
    by decide⟩, ?_⟩
  rintro ⟨x, y, b, hy, hyx, hs, -⟩
  have hy' : y = (if x = 1 then 2 else x) := Part.mem_some_iff.1 hy
  subst hs
  clear hy
  revert hy' hyx; revert x; decide
-- Statement: CONTROL: an elbow without a corner, on `Fin 2`: UP constant `0`, OVER only `0 → 0`;
-- the elbow's step does not leave `0` (`¬ LeavesAt 0`), where a corner's step always leaves its
-- landing (the `example` after this one).
example : let M := (ZeroParadox.Motion.ofTotal (fun _ : Fin 2 => (0 : Fin 2)) (fun _ => rfl)
      (fun a b => a = 0 ∧ b = 0))
    M.Elbow ∧ ¬ M.Corner ∧ ¬ M.LeavesAt 0 := by
  refine ⟨⟨1, 0, 0, Part.mem_some_iff.2 rfl, by decide, ⟨rfl, rfl⟩⟩, ?_, ?_⟩
  · rintro ⟨y, b, z, -, ⟨-, rfl⟩, hz, hzb⟩
    exact hzb (Part.mem_some_iff.1 hz)
  · rintro ⟨b, ⟨-, hb⟩, hne⟩
    exact hne hb
-- Statement: from a landing `y`, `step y b`, `z ∈ up b` and `z ≠ b` give `b ≠ y`, in every motion.
example {α : Type*} (M : ZeroParadox.Motion α) :
    ∀ y b z, M.IsLanding y → M.step y b → z ∈ M.up b → z ≠ b → b ≠ y := by
  intro y b z hy _ hz hzb hb
  subst hb
  exact hzb (Part.mem_unique hz hy)
#check @ZeroParadox.ordinalSuccMotion_elbow      -- Statement: `ordinalSuccMotion` has an elbow; with `ordinalSuccMotion_corner`, both members
#check @ZeroParadox.shiftMotion_elbow_iff        -- Statement: `shiftMotion c` has an elbow iff `⌜c⌝ ≠ 0`, as with the corner (`shiftMotion_corner_iff`)
#check @ZeroParadox.Motion.UpRaises              -- Statement: every value of `up x` is `≥ x`
#check @ZeroParadox.Motion.UpLowers              -- Statement: every value of `up x` is `≤ x`
#check @ZeroParadox.Motion.StepRaises            -- Statement: every step `x → y` has `x ≤ y`
#check @ZeroParadox.Motion.StepLowers            -- Statement: every step `x → y` has `y ≤ x`
#check @ZeroParadox.Motion.Agree                 -- Statement: UP raises and OVER raises
#check @ZeroParadox.Motion.Oppose                -- Statement: UP lowers and OVER raises
-- Statement: CONTROL: `Agree` and `Oppose` overlap, and `Oppose` does not force a loop: on ℕ, the
-- identity UP both raises and lowers, OVER `n ↦ n + 1` raises, and the motion does not loop.
example : let M := ZeroParadox.Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl) (fun a b => b = a + 1)
    M.Agree ∧ M.Oppose ∧ ¬ M.Loop := by
  have hu : ∀ x y : ℕ, y ∈ Part.some (id x) → y = x := fun _ _ h => Part.mem_some_iff.1 h
  have hs : ∀ x y : ℕ, y = x + 1 → x ≤ y := fun _ _ h => h ▸ Nat.le_succ _
  exact ⟨⟨fun x y h => (hu x y h).ge, hs⟩, ⟨fun x y h => (hu x y h).le, hs⟩,
    fun ⟨_, _, _, _, hby, hyb⟩ => hby (Part.mem_some_iff.1 hyb).symm⟩
-- Statement: CONTROL: they do not cover every motion: on `Fin 4`, UP `1 ↦ 0` lowers and `2 ↦ 3`
-- raises, so UP neither raises nor lowers, and the motion neither agrees nor opposes.
example : let M := (ZeroParadox.Motion.ofTotal
      (fun x : Fin 4 => if x = 1 then 0 else if x = 2 then 3 else x) (by decide)
      (fun a b => (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2)))
    ¬ M.Agree ∧ ¬ M.Oppose :=
  ⟨fun h => absurd (h.1 1 0 (Part.mem_some_iff.2 (by decide))) (by decide),
    fun h => absurd (h.1 2 3 (Part.mem_some_iff.2 (by decide))) (by decide)⟩
#check @ZeroParadox.MemGraph.pruneMotion_upLowers -- Statement: under `Sub`, pruning's UP lowers, at every node count
#check @ZeroParadox.MemGraph.pruneMotion_not_stepRaises -- Statement: on two nodes its OVER, edge inclusion, does not raise
#check @ZeroParadox.MemGraph.pruneMotion_two_neither -- Statement: on two nodes the legs neither agree nor oppose
#check @ZeroParadox.MemGraph.pruneMotion_one_oppose -- Statement: on one node the legs oppose (UP lowers; OVER raises, `pruneMotion_one_stepRaises`)
#check @ZeroParadox.MemGraph.pruneMotion_one_loop -- Statement: and on one node the motion loops
#check @ZeroParadox.Motion.upRaises_dual         -- Statement: in the order dual, UP raises iff it lowers here
#check @ZeroParadox.Motion.stepRaises_dual       -- Statement: and OVER raises iff it lowers here
#check @ZeroParadox.Motion.agree_dual            -- Statement: the order dual flips both legs: agree there is both lowering here
#check @ZeroParadox.Motion.oppose_dual           -- Statement: oppose there is UP raising and OVER lowering here
#check @ZeroParadox.Motion.upRaises_reverse      -- Statement: INVARIANT: reversal leaves whether UP raises unchanged
#check @ZeroParadox.Motion.upLowers_reverse      -- Statement: INVARIANT: and whether UP lowers
#check @ZeroParadox.Motion.stepRaises_reverse    -- Statement: reversal flips OVER's polarity only
#check @ZeroParadox.Motion.agree_dual_reverse_iff -- Statement: reversed, in the order dual, the motion agrees iff it opposes here
#check @ZeroParadox.Motion.not_loop_of_agree     -- Statement: in a partial order, agreeing legs give no loop, by antisymmetry; one way
-- Statement: in a partial order, both legs lowering gives no loop (`not_loop_of_agree` in the
-- order dual).
example {α : Type} [PartialOrder α] (M : ZeroParadox.Motion α) (hu : M.UpLowers)
    (hs : M.StepLowers) : ¬ M.Loop :=
  ZeroParadox.Motion.not_loop_of_agree (α := αᵒᵈ) (M := M) ⟨hu, hs⟩
#check @ZeroParadox.ordinalSuccMotion_agree      -- Statement: `ordinalSuccMotion`'s legs agree in `Ordinal`'s order
#check @ZeroParadox.shiftMotion_oppose           -- Statement: `shiftMotion c`'s legs oppose in ℕ's order
-- Statement: polarity beside ZP-M's two sides: `ordinalSuccMotion` agrees and does not loop; for
-- `⌜c⌝ ≠ 0`, `shiftMotion c` opposes and loops.
example (c : Nat.Partrec.Code) (hk : Encodable.encode c ≠ 0) :
    (ZeroParadox.ordinalSuccMotion.{0}.Agree ∧ ¬ ZeroParadox.ordinalSuccMotion.{0}.Loop) ∧
      ((ZeroParadox.shiftMotion c).Oppose ∧ (ZeroParadox.shiftMotion c).Loop) :=
  ⟨⟨ZeroParadox.ordinalSuccMotion_agree,
      ZeroParadox.Motion.not_loop_of_agree ZeroParadox.ordinalSuccMotion_agree⟩,
    ZeroParadox.shiftMotion_oppose c, ZeroParadox.shiftMotion_loop c hk⟩

end DieCannotBeIndex
