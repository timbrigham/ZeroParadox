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
import ZeroParadox.Computability.SelfCopyReference
import ZeroParadox.Algebra.Wheel
import ZeroParadox.Category.WellFoundedCoalgebra
import ZeroParadox.Category.ExcludedMiddleBridge
import ZeroParadox.Category.IgnoranceSeam
import ZeroParadox.Multihomed.InfoFunctor
import Mathlib.CategoryTheory.Category.Preorder
import ZeroParadox.Miniature
import ZeroParadox.Valuation.PoleCorners
import ZeroParadox.Reals.MarkovSpectralGap
import ZeroParadox.Order.WellFoundedObstruct
import ZeroParadox.Valuation.PoleCornersBridge
import ZeroParadox.Category.DieNucleus
import ZeroParadox.Order.LeastFixedPoint
import ZeroParadox.Valuation.SemilatticeInstance
import ZeroParadox.Settheory.OntBridge
import ZeroParadox.Settheory.Model

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

universe u

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
-- no hit bearing on a switch); the dated search for the pair is in `LEAN_CUSTOM_REGISTRY.md`. The
-- loop/climb split as a named pair, not located closer than Meseguer and R. Diaconescu as of
-- 2026-10-22, searched by theoremsearch alone (its null is uninformative on its own) in three
-- phrasings: "rewrite step from a normal form followed by normalization returns to the same or a
-- different normal form"; "stuttering step ... quotient transition system"; "closing a cover of a
-- closed element yields the next closed element"; and by one web search the same day in rewriting,
-- normal-form, stutter and closure-cover vocabulary.
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
#check @WithBot.none_eq_bot                      -- Statement: Mathlib, `none` is ⊥ of `WithBot σ`
#check @WithTop.none_eq_top                      -- Statement: Mathlib, `none` is ⊤ of `WithTop σ`
-- Reading: one adjoined point, ⊥ in the `WithBot` order on `Option σ` and ⊤ in the `WithTop` order, by
-- definition and for every motion on `Option σ`; what depends on the order chosen is polarity and the
-- order route to a trap set (§ XVIII).
#check @ZeroParadox.isBot_and_isTop_iff          -- Statement: in a partial order, `x` is least and greatest iff every point is `x`
#check @ZeroParadox.withBot_bot_isBot_and_isTop_iff -- Statement: ⊥ of `WithBot σ` is also greatest iff `σ` is empty
#check @ZeroParadox.withTop_top_isBot_and_isTop_iff -- Statement: ⊤ of `WithTop σ` is also least iff `σ` is empty
-- Statement: two adjoined points give, on any `σ`, a ⊥ and a ⊤ that differ: in `WithBot (WithTop σ)`
-- the outer `none` and `some none`.
example (σ : Type) [LE σ] :
    IsBot (⊥ : WithBot (WithTop σ)) ∧ IsTop (⊤ : WithBot (WithTop σ)) ∧
      (⊥ : WithBot (WithTop σ)) ≠ ⊤ ∧
      (⊥ : WithBot (WithTop σ)) = (none : Option (Option σ)) ∧
      (⊤ : WithBot (WithTop σ)) = (some none : Option (Option σ)) :=
  ⟨fun _ => bot_le, fun _ => le_top, WithBot.bot_ne_coe, rfl, rfl⟩
-- Statement: CONTROL: one adjoined point to ℤ gives one end only: `WithBot ℤ` has no greatest point.
example : ¬ ∃ t : WithBot ℤ, IsTop t := by
  rintro ⟨t, ht⟩
  induction t using WithBot.recBotCoe with
  | bot => exact WithBot.not_coe_le_bot 0 (ht 0)
  | coe a => exact absurd (WithBot.coe_le_coe.1 (ht ((a + 1 : ℤ) : WithBot ℤ))) (by omega)
#check @ZeroParadox.Motion.UpTotal             -- Statement: UP switch at total: `up` defined everywhere
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
#check @ZeroParadox.Motion.corner_iff_crossing  -- Statement: the corner fires iff a landing steps to a non-landing `b` with `up b` defined; both directions
#check @ZeroParadox.Motion.corner_iff_loop_or_climb -- Statement: with decidable equality, the corner fires iff the motion loops or climbs; both directions
#check @ZeroParadox.Motion.corner_iff_loop_or_climb_classical -- Statement: the same with no binder, proved with `classical`
#check @ZeroParadox.Motion.not_not_loop_or_climb_of_corner -- Statement: with no binder, a corner gives `¬¬ (Loop ∨ Climb)`
#check @ZeroParadox.Motion.em_of_corner_loop_or_climb -- Statement: if a corner gives a loop or a climb on every motion on every `β : Type`, excluded middle holds (`[propext]`); so a choice-free proof of the binder-free twin's forward direction at `Type` would be a choice-free proof of excluded middle (ESSENTIAL on the premise of `ZeroParadox/Category/ChoiceCannotBe.lean` § IV)
#check @ZeroParadox.UpAndOver.toMotion_climb    -- Statement: the die motion of an `UpAndOver` (UP its closure, OVER the covers) climbs
#check @ZeroParadox.UpAndOver.toMotion_not_loop -- Statement: and does not loop, its legs agreeing (`toMotion_agree`, `not_loop_of_agree`)
#check @ZeroParadox.UpAndOver.toMotion_ne_of_loop -- Statement: so a motion that loops is the die motion of no `UpAndOver`
-- Reading (Tim, 2026-10-22, verbatim): "I do think that that shape can represent a self loop which by
-- definition isn't landing somewhere new correct? That we have a "joint/L/J/boundary/etc" being crossed
-- is what makes it important I think. If that's the case, that needs to be a legal way of representing it."
-- Statement: the corner fires iff a landing steps to a non-landing at which UP is defined
-- (`corner_iff_crossing`); with decidable equality, iff the motion loops or climbs
-- (`corner_iff_loop_or_climb`), not exclusively (`Fin 4` above). In a partial order agreeing legs give
-- no loop (`not_loop_of_agree`), and the legs of `UpAndOver.toMotion`, whose OVER is every cover of the
-- carrier (one chosen wiring, § XIX `cover_overs_differ`), agree (`toMotion_agree`), so that motion climbs
-- and never loops (`toMotion_climb`, `toMotion_not_loop`). `phaseBelowCoverMotion` climbs (§ XXIII); the ℕ∞
-- model's join and scale loop, in both wirings below, and in each wiring, in ℕ∞'s own order and in
-- ZP-A's induced order alike, one leg raises and the other lowers (the `example` after them).
-- Reading: by the ruling above both kinds are legal up-and-over shapes, and the crossing of the joint
-- is OVER leaving the set of landings and UP returning to a landing (the `Statement:` above). Tim's
-- read, 2026-10-22, verbatim: "My gut reaction is that the joint might fill both of those rolls.. you
-- have plenty of cases where we have overlap". Both ℕ∞ wirings also switch order between the legs, with
-- opposite assignments: in wiring one UP raises in ZP-A's induced order and OVER in ℕ∞'s own, in wiring
-- two UP raises in ℕ∞'s own and OVER in the induced order (the `example` after the wirings). On ℕ∞,
-- legs that oppose in one order switch order, since the induced order is ℕ∞'s own order reversed (the
-- `example` after that one, per leg: raising in the induced order iff lowering in ℕ∞'s own). A switch
-- occurs with no corner (the `CONTROL` after that one), so these examples do not show the switch BEING
-- the crossing; that the
-- joint fills both roles stays Tim's read. Not claimed here: that the two roles coincide in general, or
-- that every crossing is a switch of order.
-- Reading: Q1: in the second wiring the loop's landing is the pole, ⊤ of `ℕ∞` (⊥ of the ZP order), which
-- steps off the landings and is sent back to itself. Q2: run backwards (`reverse`, which keeps UP), a
-- loop is a point `b ≠ y` from which OVER and UP both reach the landing `y`, and a climb one from which
-- they reach two different points (the two examples after the ℕ∞ ones).
-- Statement: LOOP, wiring one, on the ℕ∞ model (`ZeroParadox/Settheory/Model.lean`: join `min`, scale
-- `+ 1`): UP join with `c`, OVER the scale step. If `c ≠ ⊤` of `ℕ∞`, the motion loops at `c`, does not
-- climb, and is the die motion of no `UpAndOver ℕ∞`.
example (c : ℕ∞) (hc : c ≠ ⊤) :
    let M := ZeroParadox.Motion.ofTotal (fun x : ℕ∞ => ZeroParadox.ZPSemilattice.join x c)
      (fun x => show min (min x c) c = min x c by rw [min_assoc, min_self])
      (fun a b => b = ZeroParadox.ValuationStructure.scale a)
    M.Loop ∧ ¬ M.Climb ∧ ∀ U : ZeroParadox.UpAndOver ℕ∞, U.toMotion ≠ M := by
  intro M
  have hl : M.Loop := by
    refine ⟨c, c + 1, Part.mem_some_iff.2 (min_self c).symm, rfl,
      ((ENat.lt_add_one_iff hc).2 le_rfl).ne', ?_⟩
    show c ∈ Part.some (min (c + 1) c)
    rw [Part.mem_some_iff, min_eq_right le_self_add]
  refine ⟨hl, ?_, fun U => U.toMotion_ne_of_loop hl⟩
  rintro ⟨y, b, z, hy, hs, hz, hzb, hzy⟩
  have hy' : y ≤ c := min_eq_left_iff.1 (Part.mem_some_iff.1 hy).symm
  have hs' : b = y + 1 := hs
  have hz' : z = min b c := Part.mem_some_iff.1 hz
  rw [hs'] at hz' hzb
  rcases min_choice (y + 1) c with h | h
  · exact hzb (hz'.trans h)
  · rw [h] at hz'
    rw [hz'] at hzb hzy
    have hle : c ≤ y + 1 := h ▸ min_le_left _ _
    by_cases hyt : y = ⊤
    · exact hzy ((top_le_iff.1 (hyt ▸ hy')).trans hyt.symm)
    · exact hzy (le_antisymm ((ENat.lt_add_one_iff hyt).1 (lt_of_le_of_ne hle hzb)) hy')
-- Statement: LOOP, wiring two: UP the constant map to ⊤ of `ℕ∞` (the scale's unique fixed point,
-- `natInf_scale_unique_fp`), OVER the join step `a → join a z`; the motion loops at ⊤ of `ℕ∞` and does
-- not climb.
example :
    let M := ZeroParadox.Motion.ofTotal (fun _ : ℕ∞ => (⊤ : ℕ∞)) (fun _ => rfl)
      (fun a b => ∃ z, b = ZeroParadox.ZPSemilattice.join a z)
    M.Loop ∧ ¬ M.Climb := by
  intro M
  refine ⟨⟨⊤, 0, Part.mem_some _, ⟨0, (ZeroParadox.ZPSemilattice.bot_join (0 : ℕ∞)).symm⟩, by simp,
    Part.mem_some _⟩, ?_⟩
  rintro ⟨y, b, z, hy, -, hz, -, hzy⟩
  exact hzy ((Part.mem_some_iff.1 hz).trans (Part.mem_some_iff.1 hy).symm)
-- Statement: the legs of the two wirings in ℕ∞'s own order and in ZP-A's induced order (the reverse of
-- it, `ZeroParadox/Settheory/Model.lean`): wiring one opposes in ℕ∞'s own order (UP lowers, OVER
-- raises), and in the induced order UP raises and OVER lowers; wiring two has UP raising and OVER
-- lowering in ℕ∞'s own order, and opposes in the induced order.
example (c : ℕ∞) :
    let M := ZeroParadox.Motion.ofTotal (fun x : ℕ∞ => ZeroParadox.ZPSemilattice.join x c)
      (fun x => show min (min x c) c = min x c by rw [min_assoc, min_self])
      (fun a b => b = ZeroParadox.ValuationStructure.scale a)
    let N := ZeroParadox.Motion.ofTotal (fun _ : ℕ∞ => (⊤ : ℕ∞)) (fun _ => rfl)
      (fun a b => ∃ z, b = ZeroParadox.ZPSemilattice.join a z)
    (M.Oppose ∧ @ZeroParadox.Motion.UpRaises ℕ∞ M (ZeroParadox.zpSemilatticeSup ℕ∞).toLE ∧
      @ZeroParadox.Motion.StepLowers ℕ∞ M (ZeroParadox.zpSemilatticeSup ℕ∞).toLE) ∧
    (N.UpRaises ∧ N.StepLowers ∧ @ZeroParadox.Motion.Oppose ℕ∞ N (ZeroParadox.zpSemilatticeSup ℕ∞).toLE) := by
  intro M N
  refine ⟨⟨⟨fun x y h => ?_, fun a b h => ?_⟩, fun x y h => ?_, fun a b h => ?_⟩,
    fun x y h => ?_, fun a b ⟨z, h⟩ => ?_, fun x y h => ?_, fun a b ⟨z, h⟩ => ?_⟩
  · rw [Part.mem_some_iff.1 h]; exact min_le_left x c
  · rw [(h : b = a + 1)]; exact le_self_add
  · rw [Part.mem_some_iff.1 h]
    show min x (min x c) = min x c
    rw [← min_assoc, min_self]
  · rw [(h : b = a + 1)]
    show min (a + 1) a = a
    exact min_eq_right le_self_add
  · rw [Part.mem_some_iff.1 h]; exact le_top
  · rw [h]; exact min_le_left a z
  · rw [Part.mem_some_iff.1 h]
    show min ⊤ x = x
    exact min_eq_right le_top
  · rw [h]
    show min a (min a z) = min a z
    rw [← min_assoc, min_self]
-- Statement: on `ℕ∞`, for every motion, UP raises in ZP-A's induced order iff it lowers in ℕ∞'s own, and
-- likewise OVER; both directions.
example (M : ZeroParadox.Motion ℕ∞) :
    (@ZeroParadox.Motion.UpRaises ℕ∞ M (ZeroParadox.zpSemilatticeSup ℕ∞).toLE ↔ M.UpLowers) ∧
    (@ZeroParadox.Motion.StepRaises ℕ∞ M (ZeroParadox.zpSemilatticeSup ℕ∞).toLE ↔ M.StepLowers) :=
  have h : ∀ x y : ℕ∞, (ZeroParadox.zpSemilatticeSup ℕ∞).toLE.le x y ↔ y ≤ x :=
    fun x y => show min x y = y ↔ y ≤ x from min_eq_right_iff
  ⟨forall_congr' fun x => forall_congr' fun y => imp_congr_right fun _ => h x y,
    forall_congr' fun x => forall_congr' fun y => imp_congr_right fun _ => h x y⟩
-- Statement: CONTROL: on `ℕ∞`, UP the join with 0 of `ℕ∞` (every point sent to 0, which is ⊥ of ℕ∞'s
-- own order and ⊤ of ZP-A's induced order), OVER the scale step only from points other than 0: UP
-- moves 1 to 0, the legs oppose in ℕ∞'s own order (UP lowers, OVER raises), UP does not raise there and
-- raises in the induced order, and the corner does not fire (the one landing, 0, has no step).
example :
    let M := ZeroParadox.Motion.ofTotal (fun x : ℕ∞ => ZeroParadox.ZPSemilattice.join x 0)
      (fun x => show min (min x 0) 0 = min x 0 by rw [min_assoc, min_self])
      (fun a b => a ≠ 0 ∧ b = ZeroParadox.ValuationStructure.scale a)
    (0 : ℕ∞) ∈ M.up 1 ∧ M.Oppose ∧ ¬ M.UpRaises ∧
      @ZeroParadox.Motion.UpRaises ℕ∞ M (ZeroParadox.zpSemilatticeSup ℕ∞).toLE ∧ ¬ M.Corner := by
  intro M
  refine ⟨Part.mem_some_iff.2 (by simp [ZeroParadox.ZPSemilattice.join]),
    ⟨fun x y h => ?_, fun a b ⟨_, h⟩ => ?_⟩, fun h => ?_, fun x y h => ?_, ?_⟩
  · rw [Part.mem_some_iff.1 h]; exact min_le_left x 0
  · rw [(h : b = a + 1)]; exact le_self_add
  · exact absurd (h 1 (min 1 0) (Part.mem_some _)) (by simp)
  · rw [Part.mem_some_iff.1 h]
    show min x (min x 0) = min x 0
    rw [← min_assoc, min_self]
  · rintro ⟨y, b, z, hy, ⟨hy0, -⟩, -, -⟩
    have : y = min y 0 := Part.mem_some_iff.1 hy
    exact hy0 (this.trans (min_eq_right (zero_le y)))
-- Statement: CONTROL: with UP constant ⊤ of `ℕ∞`, the always-true step loops too, so the loop kind
-- there says nothing specific about the join.
example : (ZeroParadox.Motion.ofTotal (fun _ : ℕ∞ => (⊤ : ℕ∞)) (fun _ => rfl) (fun _ _ => True)).Loop :=
  ⟨⊤, 0, Part.mem_some _, trivial, by simp, Part.mem_some _⟩
-- Statement: Q2: a loop is a landing `y` and a point `b ≠ y` with `b` stepping to `y` in the reversed
-- motion and `y ∈ up b`; both directions.
example {α : Type} (M : ZeroParadox.Motion α) :
    M.Loop ↔ ∃ y b, M.IsLanding y ∧ M.reverse.step b y ∧ b ≠ y ∧ y ∈ M.reverse.up b := Iff.rfl
-- Statement: Q2: a climb is a landing `y` and a point `b` stepping to `y` in the reversed motion, with
-- some `z ∈ up b` other than `b` and `y`; both directions.
example {α : Type} (M : ZeroParadox.Motion α) :
    M.Climb ↔ ∃ y b z, M.IsLanding y ∧ M.reverse.step b y ∧ z ∈ M.reverse.up b ∧ z ≠ b ∧ z ≠ y :=
  Iff.rfl

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
-- Statement: on an empty carrier every existence premise fails ...
example {α : Type} [IsEmpty α] (M : ZeroParadox.Motion α) :
    ¬ M.HasLanding ∧ ¬ M.OverAtLanding ∧ ¬ M.Corner ∧ ¬ M.Elbow ∧ ¬ M.Climb ∧ ¬ M.Loop ∧
      ¬ M.OverToUndefined :=
  ⟨fun ⟨y, _⟩ => isEmptyElim y, fun ⟨y, _⟩ => isEmptyElim y, fun ⟨y, _⟩ => isEmptyElim y,
   fun ⟨x, _⟩ => isEmptyElim x, fun ⟨y, _⟩ => isEmptyElim y, fun ⟨y, _⟩ => isEmptyElim y,
   fun ⟨y, _⟩ => isEmptyElim y⟩
-- Statement: ... and every "for all" premise holds with nothing to test.
example {α : Type} [IsEmpty α] [LE α] (M : ZeroParadox.Motion α) :
    M.UpTotal ∧ M.UpStepInvariant ∧ M.RunsClose ∧ M.Agree ∧ M.Oppose ∧ M.SelectedTotal ∧
      M.RegisteredDecidable ∧ ∀ y, M.OverTrichotomy y :=
  ⟨fun x => isEmptyElim x, fun a => isEmptyElim a, fun s => isEmptyElim (s 0),
   ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩, ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩,
   ⟨id, fun a => isEmptyElim a⟩, ⟨fun a => isEmptyElim a⟩, fun y => isEmptyElim y⟩
#check @ZeroParadox.Motion.subsingleton_of_isEmpty -- Statement: an empty carrier has at most one motion
-- Statement: and `Empty` has one, so it has exactly one (with `subsingleton_of_isEmpty`).
example : Nonempty (ZeroParadox.Motion Empty) := ⟨⟨fun x => x.elim, fun x => x.elim, fun x => x.elim⟩⟩
#check @ZeroParadox.isEmpty_orderBot_and_orderTop -- Statement: under any `≤`, an empty carrier has no `OrderBot` and no `OrderTop` structure
-- Reading: so the premises naming ⊥ (`BotCovered`, `BotIntervalTwo`, `UniqueBotCover`, the trap
-- theorems at ⊥) cannot be instantiated on an empty carrier, which is neither a member nor a
-- non-member of them.

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
#check @ZeroParadox.botCovered_withBot_iff        -- Statement: ⊥ of `WithBot σ` has a cover iff `σ` has a minimal point (`[propext, Classical.choice, Quot.sound]`, through Mathlib's `WithBot.bot_covBy_coe`)
#check @ZeroParadox.botCovered_withTop_iff        -- Statement: with ⊥ of `σ` and no maximal point, ⊥ of `WithTop σ` has a cover iff ⊥ of `σ` has one
-- Statement: the two adjoined-point orders can disagree: `NNReal` has the cut in `WithBot` and not in
-- `WithTop`; ℕ has it in both.
example : ZeroParadox.BotCovered (WithBot NNReal) ∧ ¬ ZeroParadox.BotCovered (WithTop NNReal) :=
  ⟨ZeroParadox.botCovered_withBot_iff.2 ⟨⊥, isMin_bot⟩,
   fun h => let ⟨_, ha⟩ := ZeroParadox.botCovered_withTop_iff.1 h; not_covBy ha⟩
example : ZeroParadox.BotCovered (WithBot ℕ) ∧ ZeroParadox.BotCovered (WithTop ℕ) :=
  ⟨ZeroParadox.botCovered_withBot_iff.2 ⟨⊥, isMin_bot⟩,
   ZeroParadox.botCovered_withTop_iff.2 ⟨_, Order.covBy_succ (⊥ : ℕ)⟩⟩
-- Statement: CONTROL for `NoMaxOrder`: `WithTop PUnit` has the cut and `PUnit` does not.
example : ZeroParadox.BotCovered (WithTop PUnit) ∧ ¬ ZeroParadox.BotCovered PUnit :=
  ⟨⟨⊤, WithTop.coe_covBy_top.2 (fun _ _ => le_rfl)⟩, fun ⟨_, h⟩ => h.lt.ne (Subsingleton.elim _ _)⟩
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
#check @ZeroParadox.everyStepCovered_of_finite  -- Statement: if `α` is a finite partial order, the scope form holds
#check @ZeroParadox.botCovered_of_finite        -- Statement: if `α` is a finite partial order with ⊥ and a point other than ⊥ of `α`, the cut holds
-- Reading: both measure `[propext, Classical.choice, Quot.sound]`. Not statement-carried (statement
-- control axiom-free, measured 2026-10-28); the choice enters through Mathlib's well-foundedness of a
-- finite order (`Finite.wellFounded_of_trans_of_irrefl` measures the same); no choice-free proof was
-- found, and no reduction to a taboo was attempted, so the class is open between accidental and
-- essential.
-- Statement: CONTROL, infinite: `NNReal` has a point other than its ⊥ and no cut, so finiteness in
-- `botCovered_of_finite` is not removable; `Unit` (finite, no cut, above) is the control for the
-- point other than ⊥.
example : (∃ a : NNReal, a ≠ ⊥) ∧ ¬ ZeroParadox.BotCovered NNReal :=
  ⟨⟨1, one_ne_zero⟩, fun ⟨_, h⟩ => not_covBy h⟩
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

/-! ### § V. The up-and-over shape's climbing kind, an order-theoretic presentation -/
#check @ZeroParadox.UpAndOver                   -- Statement: closure, corner, a cover at every non-maximal landing; `UpAndOver.toMotion` (OVER every cover) climbs and never loops (§ I, `toMotion_climb`, `toMotion_not_loop`). Reading: the loop kind is presented by `Motion.Loop`
#check @ZeroParadox.ordinalUpAndOver            -- Statement: member `Ordinal`
#check @ZeroParadox.nonempty_upAndOver_dual_of_covBy -- Statement: with decidable `≤`, a least point `e` and a cover `b ⋖ a` with `b ≠ e` give a member `αᵒᵈ`
#check @ZeroParadox.MemGraph.nonempty_upAndOver_hset2 -- Statement: member `(HSet 2)ᵒᵈ`; by `no_upAndOver_prune` no member there has pruning as UP
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
#check @ZeroParadox.Motion.three_of_not_runClose -- Statement: if no stage of `s` is a landing and `up (s n) ≠ up (s 0)` for some `n`, the carrier has three distinct points (`[propext, Classical.choice, Quot.sound]`, the choice in a case split on definedness; not statement-carried, control measured 2026-10-28)
#check @ZeroParadox.Motion.four_of_not_runClose -- Statement: with UP total, four distinct points (`[propext, Quot.sound]`)
-- Statement: the bounds are met: on `Fin 3`, UP `0, 2 ↦ 2`, undefined at `1`, OVER `0 ↔ 1`, the run
-- `0, 1, 0, …` is landing-free and its stages differ in UP, so `RunsClose` fails.
example : ∃ M : ZeroParadox.Motion (Fin 3), ¬ M.RunsClose := by
  let u : Fin 3 → Option (Fin 3) := fun x => if x = 1 then none else some 2
  have hu : ∀ x y, y ∈ u x → y ∈ u y := by decide
  refine ⟨ZeroParadox.Motion.ofOption u hu (fun a b => a ≠ b ∧ a ≠ 2 ∧ b ≠ 2), fun h => ?_⟩
  let s : ℕ → Fin 3 := fun n => if n % 2 = 0 then 0 else 1
  have hs : (ZeroParadox.Motion.ofOption u hu (fun a b => a ≠ b ∧ a ≠ 2 ∧ b ≠ 2)).IsRun s :=
    fun n => by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have : (n + 1) % 2 = 1 := by omega
        simp only [s, h, this]
        show (0 : Fin 3) ≠ 1 ∧ (0 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 2
        decide
      · have : (n + 1) % 2 = 0 := by omega
        simp only [s, h, this]
        show (1 : Fin 3) ≠ 0 ∧ (1 : Fin 3) ≠ 2 ∧ (0 : Fin 3) ≠ 2
        decide
  have hint : ∀ n, ¬ (ZeroParadox.Motion.ofOption u hu
      (fun a b => a ≠ b ∧ a ≠ 2 ∧ b ≠ 2)).IsLanding (s n) := fun n hl => by
    change s n ∈ Part.ofOption (u (s n)) at hl
    rw [Part.mem_ofOption] at hl
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [s, u, h] at hl
  have hc := (h s hs hint) 1 ⟨1, rfl⟩
  have e : Part.ofOption (u 1) = Part.ofOption (u 0) := hc.2
  have : (2 : Fin 3) ∈ Part.ofOption (u 0) := Part.mem_ofOption.2 rfl
  rw [← e, Part.mem_ofOption] at this
  exact absurd this (by decide)
-- Statement: with UP total: on `Fin 4`, UP `0 ↦ 2`, `1 ↦ 3`, `2`, `3` fixed, OVER `0 ↔ 1`; `RunsClose`
-- fails.
example : ∃ M : ZeroParadox.Motion (Fin 4), M.UpTotal ∧ ¬ M.RunsClose := by
  let r : Fin 4 → Fin 4 := fun x => if x = 0 then 2 else if x = 1 then 3 else x
  have hr : ∀ x, r (r x) = r x := by decide
  refine ⟨ZeroParadox.Motion.ofTotal r hr (fun a b => a ≠ b ∧ a.val < 2 ∧ b.val < 2),
    ZeroParadox.Motion.ofTotal_upTotal _ _ _, fun h => ?_⟩
  let s : ℕ → Fin 4 := fun n => if n % 2 = 0 then 0 else 1
  have hs : (ZeroParadox.Motion.ofTotal r hr (fun a b => a ≠ b ∧ a.val < 2 ∧ b.val < 2)).IsRun s :=
    fun n => by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have : (n + 1) % 2 = 1 := by omega
        simp only [s, h, this]
        show (0 : Fin 4) ≠ 1 ∧ (0 : Fin 4).val < 2 ∧ (1 : Fin 4).val < 2
        decide
      · have : (n + 1) % 2 = 0 := by omega
        simp only [s, h, this]
        show (1 : Fin 4) ≠ 0 ∧ (1 : Fin 4).val < 2 ∧ (0 : Fin 4).val < 2
        decide
  have hint : ∀ n, ¬ (ZeroParadox.Motion.ofTotal r hr
      (fun a b => a ≠ b ∧ a.val < 2 ∧ b.val < 2)).IsLanding (s n) := fun n hl => by
    have := Part.mem_some_iff.1 hl
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [s, r, h] at this
  have hc := (h s hs hint) 1 ⟨1, rfl⟩
  have e : Part.some (r 1) = Part.some (r 0) := hc.2
  exact absurd (Part.some_inj.1 e) (by decide)
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
-- Statement: ⊥ < ε₀ in `Ordinal`, through the die: ⊥ of `Ordinal` is stage 0 of the tower, and a
-- defined closure is not a stage (`StageClosure.not_mem_of_mem`). The direct proofs are
-- `epsilon0_ne_bot` and `epsilon0_ne_zero`; this re-derives them at every universe, not a stronger fact.
example : (⊥ : Ordinal.{u}) < Ordinal.epsilon 0 := by
  refine bot_lt_iff_ne_bot.2 fun h => ?_
  have hne : (Set.range fun n => (fun a : Ordinal.{u} => Ordinal.omega0 ^ a)^[n] 0).Nonempty :=
    ⟨_, 0, rfl⟩
  apply ZeroParadox.ordinalTowerMotion_stageClosure.{u}.not_mem_of_mem hne (Part.mem_some _)
  exact ⟨0, by simp [h]⟩
#check @Ordinal.iterate_omega0_opow_lt_epsilon_zero -- Statement: Mathlib: every tower stage `(ω^·)^[n] 0` is `< ε₀`; at `n = 0` the stage is 0, ⊥ of `Ordinal`
-- Statement: on `E0Note` the zero notation is below ⊤ of `E0Note` in the carrier's own order, decided
-- by evaluation (`e0Coe_lt_top` for every notation), and `e0Repr` sends ⊤ to ε₀ and the zero
-- notation to 0. `<` on `E0Note` does not track `<` on `Ordinal` in general (the comparator `example`
-- after `e0Repr_not_injective` in `ZeroParadox/Ordinal/PricedInterface.lean`), and `e0Repr` is
-- `noncomputable`.
example : ZeroParadox.e0Coe 0 < (⊤ : ZeroParadox.E0Note) ∧
    ZeroParadox.e0Repr ⊤ = Ordinal.epsilon 0 ∧ ZeroParadox.e0Repr (ZeroParadox.e0Coe 0) = 0 :=
  ⟨by decide, rfl, by simp⟩
#check @ZeroParadox.nothing_between_is_a_step   -- Statement: no ordinal below ε₀ is fixed by `α ↦ ω^α`
#check @ZeroParadox.nfp_seed_independent_below_epsilon0 -- Statement: every seed at or below ε₀ closes at ε₀
#check @ZeroParadox.ordinalCornerStep            -- Statement: OVER `succ` then UP `nfp (ω^·)`, as one map on `Ordinal`
-- Statement: it is the corner composite of `ordinalSuccMotion`: `a` steps to `succ a`, and UP sends
-- `succ a` to `ordinalCornerStep a`.
example (a : Ordinal.{u}) : ZeroParadox.ordinalSuccMotion.{u}.step a (Order.succ a) ∧
    ZeroParadox.ordinalCornerStep a ∈ ZeroParadox.ordinalSuccMotion.{u}.up (Order.succ a) :=
  ⟨rfl, Part.mem_some _⟩
#check @ZeroParadox.lt_ordinalCornerStep         -- Statement: it moves every ordinal strictly up
-- Statement: CONTROL, finite: on a nonempty finite preorder no map moves every point strictly up (its
-- iterates from a point would be strictly increasing, hence one-to-one on ℕ).
example {α : Type} [Preorder α] [Finite α] [Nonempty α] (f : α → α) : ¬ ∀ x, x < f x := by
  intro h
  obtain ⟨x⟩ := ‹Nonempty α›
  have hm : StrictMono (fun n => f^[n] x) := strictMono_nat_of_lt_succ fun n => by
    rw [Function.iterate_succ_apply']; exact h _
  exact not_finite_iff_infinite.2 (Infinite.of_injective _ hm.injective) ‹_›
#check @ZeroParadox.ordinalCornerStep_iterate    -- Statement: iterated `n + 1` times from 0, ⊥ of `Ordinal`, it gives `ε_n`
-- Statement: the `n`-th iterate from 0 is ⊥ of its own `Set.Ici`, and the `n + 1`-th is strictly
-- above it.
example (n : ℕ) :
    ((⊥ : Set.Ici (ZeroParadox.ordinalCornerStep^[n] (0 : Ordinal.{u}))) : Ordinal.{u}) =
        ZeroParadox.ordinalCornerStep^[n] 0 ∧
      ZeroParadox.ordinalCornerStep^[n] (0 : Ordinal.{u}) < ZeroParadox.ordinalCornerStep^[n + 1] 0 :=
  ⟨rfl, by rw [Function.iterate_succ_apply']; exact ZeroParadox.lt_ordinalCornerStep _⟩
-- Reading: the die supplies an index, the number `n` of corner steps from ⊥ of `Ordinal`, and a
-- direction, strictly up. That the `n`-th iterate is a bottom is stated of the carrier `Set.Ici`;
-- the motion restricted there is `ordinalView n` (`Motion.restrict`, § XVIII). At `n = 1` the value is ε₀,
-- ⊥ of `Set.Ici ε₀` and not ⊥ of `Ordinal` (`epsilon0_ne_bot`). The iterates are distinct values
-- (strictly increasing); reading each as the bottom the snap-arc returns to is a commitment, not shown
-- here, and `t_iz_limit_is_new_null` is the role half only.
#check @ZeroParadox.runMotion                   -- Statement: on configurations of `f : σ → Option σ`, UP `StateTransition.eval f`, OVER one step
#check @ZeroParadox.runMotion_upStepInvariant   -- Statement: member of the premise form
#check @ZeroParadox.runMotion_stageClosure      -- Statement: the not-yet-halted configurations reachable from `a` close at `eval f a`
#check @StateTransition.reaches_eval            -- Statement: Mathlib, `Reaches f a b → eval f a = eval f b`
#check @PFun.fix_fwd_eq                         -- Statement: Mathlib, `Sum.inr a' ∈ f a → f.fix a = f.fix a'`; `eval` is a `PFun.fix`
-- Reading: Mathlib's docstring calls `PFun.fix` the "first return map"; `fix_fwd_eq` is the `Part`
-- case of the Elgot fixpoint law (Goncharov, Jakob, Neves, arXiv:1807.01053, Def. 5, p. 22:7; cited).
-- Reading: for a step RELATION that iteration lands in the powerset, a set of results (ibid.,
-- Example 6, item 1, p. 22:7), not one landing; here `UpStepInvariant` supplies the single closure, one
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
-- Statement: under `ordinalSuccMotion`, 0, ⊥ of `Ordinal.{0}`, does not step to itself, steps
-- elsewhere (to `succ 0`), and is not a landing (UP sends it to `nfp (ω^·) 0 ≠ 0`).
example : ¬ ZeroParadox.ordinalSuccMotion.{0}.step 0 0 ∧ ZeroParadox.ordinalSuccMotion.{0}.LeavesAt 0 ∧
    ¬ ZeroParadox.ordinalSuccMotion.{0}.IsLanding 0 := by
  refine ⟨fun h => ?_, ⟨Order.succ 0, rfl, (Order.lt_succ 0).ne'⟩, fun h => ?_⟩
  · have h' : (0 : Ordinal) = Order.succ 0 := h
    exact (Order.lt_succ (0 : Ordinal)).ne h'
  · have h' : (0 : Ordinal) = Ordinal.nfp (fun a => Ordinal.omega0 ^ a) 0 := Part.mem_some_iff.1 h
    have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) (0 : Ordinal)
    rw [← h', Ordinal.opow_zero] at this
    exact one_ne_zero this

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
#check @ZeroParadox.Motion.lpo_of_selectedTotal_nat_boolStep -- Statement: (b) on every motion on `ℕ` with a `Bool`-valued step ⇒ the limited principle of omniscience (`[propext]`)
-- Statement: CONTROL: (a) there is free: a `Bool`-valued step on `ℕ` has a data selector, `Nat.find`.
example (r : ℕ → ℕ → Bool) :
    (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b => r a b = true)).SelectedData :=
  ⟨fun a h => ⟨Nat.find (p := fun b => r a b = true) h, Nat.find_spec (p := fun b => r a b = true) h⟩⟩
-- Statement: the same reduction lands on `ZeroParadox.LPO` (`ZeroParadox/Category/LawvereTaboo.lean`
-- § V).
example (h : ∀ r : ℕ → ℕ → Bool,
    (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b => r a b = true)).SelectedTotal) :
    ZeroParadox.LPO :=
  ZeroParadox.Motion.lpo_of_selectedTotal_nat_boolStep h
-- Reading: on `ℕ` with a `Bool`-valued step, a data selector is free and a total one costs the
-- limited principle of omniscience: the gap is deciding at each point whether a successor exists,
-- which is the search over the carrier.
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
#check @ZeroParadox.Motion.lpo_of_trichotomy_nat_boolStep -- Statement: the trichotomy at every point of every motion on `ℕ` with a `Bool`-valued step ⇒ the limited principle of omniscience (`[propext]`)
-- Statement: CONTROL: on `Bool` with a `Bool`-valued step the trichotomy holds at every point, with no
-- hypothesis. Reading: so the cost on `ℕ` is the carrier's search, not the step's values.
example (r : Bool → Bool → Bool) (y : Bool) :
    (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b => r a b = true)).OverTrichotomy y := by
  have two : ∀ b : Bool, b = y ∨ b = !y := fun b => by cases b <;> cases y <;> decide
  cases ho : r y (!y)
  · cases hs : r y y
    · refine Or.inl fun b hb => ?_
      have hb' : r y b = true := hb
      rcases two b with rfl | rfl
      · rw [hs] at hb'; exact absurd hb' (by decide)
      · rw [ho] at hb'; exact absurd hb' (by decide)
    · refine Or.inr (Or.inl ⟨hs, fun b hb => ?_⟩)
      have hb' : r y b = true := hb
      rcases two b with rfl | rfl
      · rfl
      · rw [ho] at hb'; exact absurd hb' (by decide)
  · exact Or.inr (Or.inr ⟨!y, ho, by cases y <;> decide⟩)
-- Statement: the `ℕ` reduction lands on `ZeroParadox.LPO`.
example (H : ∀ r : ℕ → ℕ → Bool, ∀ y,
    (ZeroParadox.Motion.ofTotal id (fun _ => rfl) (fun a b => r a b = true)).OverTrichotomy y) :
    ZeroParadox.LPO :=
  ZeroParadox.Motion.lpo_of_trichotomy_nat_boolStep H
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
-- Statement: the three OVER cells (`SelfOnlyAt`, `NoStepAt`, `LeavesAt`) crossed with {a landing
-- (`IsLanding`), UP undefined}: each of the six pairs has a member, in the six `example`s below. So "a
-- point that steps to itself only has no UP value" fails, at ε₀ in the ordinal tower.
example : ZeroParadox.ordinalTowerMotion.{0}.SelfOnlyAt (Ordinal.epsilon 0) ∧
    ZeroParadox.ordinalTowerMotion.{0}.IsLanding (Ordinal.epsilon 0) := by
  have h := Ordinal.omega0_opow_epsilon 0
  exact ⟨⟨h.symm, fun b hb => hb.trans h⟩, (ZeroParadox.ordinalTowerMotion_isLanding_iff _).2 h⟩
example : (ZeroParadox.runMotion (fun _ : Unit => some ())).SelfOnlyAt () ∧
    ¬ ((ZeroParadox.runMotion (fun _ : Unit => some ())).up ()).Dom :=
  ⟨⟨rfl, fun _ _ => rfl⟩,
    (ZeroParadox.runMotion_run_diverges (fun _ : Unit => some ()) (s := fun _ => ()) (fun _ => rfl)).2⟩
example : (ZeroParadox.runMotion (fun _ : Unit => (none : Option Unit))).NoStepAt () ∧
    (ZeroParadox.runMotion (fun _ : Unit => (none : Option Unit))).IsLanding () :=
  ⟨fun b hb => (by change b ∈ (none : Option Unit) at hb; cases hb),
    (ZeroParadox.runMotion_isLanding_iff (fun _ : Unit => (none : Option Unit)) ()).2 rfl⟩
example : let M : ZeroParadox.Motion ℕ :=
      ⟨fun _ => Part.none, fun _ _ h => absurd h (Part.notMem_none _), fun _ _ => False⟩
    M.NoStepAt 0 ∧ ¬ (M.up 0).Dom :=
  ⟨fun _ h => h, Part.not_none_dom⟩
example : let M := ZeroParadox.Motion.ofTotal (fun _ : Bool => true) (fun _ => rfl) (fun a b => a ≠ b)
    M.LeavesAt true ∧ M.IsLanding true :=
  ⟨⟨false, fun e => Bool.noConfusion e, fun e => Bool.noConfusion e⟩, Part.mem_some _⟩
example : let M : ZeroParadox.Motion ℕ :=
      ⟨fun _ => Part.none, fun _ _ h => absurd h (Part.notMem_none _), fun a b => b = a + 1⟩
    M.LeavesAt 0 ∧ ¬ (M.up 0).Dom :=
  ⟨⟨1, rfl, by decide⟩, Part.not_none_dom⟩
#check @ZeroParadox.Motion.corner_leavesAt       -- Statement: a corner leaves its landing; with `loop_corner` and `climb_corner`, loop and climb sit at `LeavesAt`
-- Statement: a coalgebra `α : X → P.Obj X` with OVER its child relation (UP the identity): `x` is in
-- the next time of `∅` (`nextTime`, `ZeroParadox/Category/WellFoundedCoalgebra.lean`) iff no step
-- leaves `x` (`[propext]`).
example {X : Type} {P : PFunctor.{0, 0}} (α : X → P.Obj X) (x : X) :
    x ∈ ZeroParadox.nextTime α ∅ ↔
      (ZeroParadox.Motion.ofTotal (id : X → X) (fun _ => rfl)
        (fun x y => ∃ b, (α x).2 b = y)).NoStepAt x :=
  ⟨fun h _ ⟨b, _⟩ => absurd (h b) (Set.notMem_empty _), fun h b => (h _ ⟨b, rfl⟩).elim⟩
-- Statement: so if the coalgebra is well-founded (`IsWellFoundedCoalg`) and no point is without a step,
-- the carrier is empty (`[propext, Quot.sound]`). Reading (cited): the argument of Adámek, Milius and
-- Moss 2020, arXiv:1910.09401v2, Examples 4.5(3), p. 15 ("the empty coalgebra is a fixed point of"
-- next time), here per coalgebra, with no point lacking a step in place of their `F∅ = ∅`.
example {X : Type} {P : PFunctor.{0, 0}} (α : X → P.Obj X) (hwf : ZeroParadox.IsWellFoundedCoalg α)
    (hns : ∀ x, ¬ (ZeroParadox.Motion.ofTotal (id : X → X) (fun _ => rfl)
        (fun x y => ∃ b, (α x).2 b = y)).NoStepAt x) : IsEmpty X := by
  have h : ZeroParadox.nextTime α ∅ = ∅ := Set.ext fun x =>
    ⟨fun hx => hns x fun _ ⟨b, _⟩ => absurd (hx b) (Set.notMem_empty _), fun hx => hx.elim⟩
  have hu := hwf ∅ h
  exact ⟨fun x => by
    have hx : x ∈ (∅ : Set X) := by rw [hu]; trivial
    exact hx⟩
-- Statement: on the leaf-free M-type (`idPF_Coalgebra`, not well-founded: `idPF_M_not_wellFounded`)
-- every point steps to itself only, since any two points are equal (`PFunctor.M.bisim`)
-- (`[propext, Classical.choice, Quot.sound]`). Reading: the root cut's two sides sit at two trichotomy
-- values, no step (which an inhabited well-founded carrier cannot lack, previous `example`) and a step
-- to itself only (this one); the root cut's seam half is not derived from them.
example (x : PFunctor.M ZeroParadox.idPF_Coalgebra) :
    (ZeroParadox.Motion.ofTotal (id : PFunctor.M ZeroParadox.idPF_Coalgebra → _) (fun _ => rfl)
      (fun x y => ∃ b, (PFunctor.M.dest x).2 b = y)).SelfOnlyAt x := by
  have heq : ∀ a b : PFunctor.M ZeroParadox.idPF_Coalgebra, a = b := fun a b => by
    refine PFunctor.M.bisim (fun _ _ => True) ?_ a b trivial
    intro a b _
    rcases ha : PFunctor.M.dest a with ⟨i, f⟩
    rcases hb : PFunctor.M.dest b with ⟨j, g⟩
    cases i; cases j
    exact ⟨PUnit.unit, f, g, rfl, rfl, fun _ => trivial⟩
  exact ⟨⟨PUnit.unit, heq _ _⟩, fun b _ => heq _ _⟩

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
#check @ZeroParadox.DieSelfCopyRef               -- Statement: in `ofFun g`, no fan-in, some point with no predecessor, and exactly one point stepping to itself only
#check @ZeroParadox.selfCopyRef_of_dieSelfCopyRef -- Statement: with `DecidableEq`, the die form gives `SelfCopyRef` (one-to-one, not onto, one fixed point) (`[propext]`)
#check @ZeroParadox.fanIn_selfOnlyAt_of_selfCopyRef -- Statement: `SelfCopyRef` gives no fan-in and exactly one point stepping to itself only (`[propext]`)
#check @ZeroParadox.dieSelfCopyRef_of_selfCopyRef -- Statement: and the die form, the point with no predecessor obtained by contradiction from not-onto (`[propext, Classical.choice, Quot.sound]`)
#check @ZeroParadox.Motion.reverse               -- Statement: the reversed motion: the same UP, OVER flipped
#check @ZeroParadox.Motion.reverse_up            -- Statement: INVARIANT: reversal leaves UP, and with it `up_idem`, unchanged
#check @ZeroParadox.Motion.reverse_reverse       -- Statement: reversing twice returns the motion
#check @ZeroParadox.Motion.fanIn_iff_reverse     -- Statement: fan-in at `y` is two distinct successors of `y` in the reversed motion
#check @ZeroParadox.Motion.reverse_ofFun_of_injective -- Statement: if `g` is one-to-one, the reverse of `ofFun g` has at most one successor per point, and no step / a step to itself only / a step elsewhere at `y` iff `y` is not a value of `g` / `g y = y` / `g x = y` for some `x ≠ y`
-- Statement: that reverse is Mathlib's partial inverse: with `g` one-to-one, `y` steps to `x` in it iff
-- `Function.partialInv g y = some x` (`Function.Injective.isPartialInv`).
example {α : Type} (g : α → α) (hg : Function.Injective g) (y x : α) :
    (ZeroParadox.Motion.ofFun g).reverse.step y x ↔ Function.partialInv g y = some x :=
  ⟨fun h => (hg.isPartialInv x y).2 h.symm, fun h => ((hg.isPartialInv x y).1 h).symm⟩
#check @ZeroParadox.Motion.reverse_ofFun_subsingleton_iff -- Statement: the reverse of `ofFun g` has at most one successor everywhere iff `g` is one-to-one
#check @ZeroParadox.Motion.reverse_ofFun_total_iff -- Statement: every point has a step in that reverse iff `g` is onto
#check @ZeroParadox.Motion.not_fanIn_ofFun_iff_injective -- Statement: with `DecidableEq`, no point of `ofFun g` has fan-in iff `g` is one-to-one (`[propext]`)
#check @ZeroParadox.Motion.reverse_ofFun_isFun_iff_bijective -- Statement: the reverse is the step of a function iff `g` is one-to-one and onto (`[propext, Classical.choice]`, the choice in `Function.surjInv`)
-- Statement: CONTROL: one-to-one is not enough for that: `· + 1` on ℕ is one-to-one, and in its
-- reverse 0 has no step.
example : Function.Injective (fun n : ℕ => n + 1) ∧
    ¬ ∃ a, (ZeroParadox.Motion.ofFun (fun n : ℕ => n + 1)).reverse.step 0 a :=
  ⟨fun _ _ h => Nat.succ_injective h, fun ⟨a, (ha : 0 = a + 1)⟩ => Nat.succ_ne_zero a ha.symm⟩
-- Statement: on a finite carrier it is: if `g` is one-to-one, every point has a step in the reverse of
-- `ofFun g`, and that reverse is the step of a function (`Finite.injective_iff_surjective`, then
-- `reverse_ofFun_total_iff` and `reverse_ofFun_isFun_iff_bijective`); the converse partner of the
-- finite `example` below on points entered from no other point.
example {α : Type} [Finite α] (g : α → α) (hg : Function.Injective g) :
    (∀ y, ∃ a, (ZeroParadox.Motion.ofFun g).reverse.step y a) ∧
      ∃ h : α → α, ∀ y a, (ZeroParadox.Motion.ofFun g).reverse.step y a ↔ a = h y :=
  ⟨(ZeroParadox.Motion.reverse_ofFun_total_iff g).2 (Finite.injective_iff_surjective.1 hg),
    (ZeroParadox.Motion.reverse_ofFun_isFun_iff_bijective g).2
      ⟨hg, Finite.injective_iff_surjective.1 hg⟩⟩
-- Statement: CONTROL, infinite and total: `· + 1` on ℤ is one-to-one and every point has a reverse
-- step, so finiteness is sufficient, not necessary.
example : Function.Injective (fun n : ℤ => n + 1) ∧
    ∀ y : ℤ, ∃ a, (ZeroParadox.Motion.ofFun (fun n : ℤ => n + 1)).reverse.step y a :=
  ⟨fun _ _ h => by simpa using h, fun y => ⟨y - 1, show y = y - 1 + 1 by omega⟩⟩
#check @ZeroParadox.Motion.exists_fanIn_ofFun_of_not_injective -- Statement: if `g` is not one-to-one, some point has fan-in; proved with `classical`
#check @ZeroParadox.Motion.exists_fanIn_bool     -- Statement: on `Bool` the same, by cases (`[propext]`)
#check @ZeroParadox.Motion.mp_of_exists_fanIn_nat -- Statement: the same for every `g : ℕ → ℕ` ⇒ Markov's principle (`[propext, Quot.sound]`); `ℕ` has decidable equality, and a choice-free proof of `exists_fanIn_ofFun_of_not_injective` on `ℕ` would be a choice-free proof of Markov's principle (ESSENTIAL in the sense of `ZeroParadox/Category/ChoiceCannotBe.md` given that Markov's principle is not derivable in the choice-free fragment; that premise is not one of `ZeroParadox/Category/ChoiceCannotBe.lean` § IV's cases and is not proved here)
-- Statement: that reduction lands on `ZeroParadox.MarkovPrinciple`
-- (`ZeroParadox/Category/LawvereTaboo.lean` § V).
example (H : ∀ g : ℕ → ℕ, ¬ Function.Injective g → ∃ y, (ZeroParadox.Motion.ofFun g).FanIn y) :
    ZeroParadox.MarkovPrinciple :=
  ZeroParadox.Motion.mp_of_exists_fanIn_nat H
-- Statement: CONTROL: with a pair `a ≠ b`, `g a = g b` in hand, the fan-in is immediate; the taboo is
-- the passage from "not one-to-one" to the pair.
example {α : Type} (g : α → α) {a b : α} (hab : a ≠ b) (h : g a = g b) :
    (ZeroParadox.Motion.ofFun g).FanIn (g a) :=
  ⟨a, b, hab, rfl, h⟩
#check @ZeroParadox.Motion.not_noEntry_of_fanIn  -- Statement: in any motion, if `y` has fan-in, some step into `y` starts elsewhere
-- Statement: members, each with its fan-in exhibited: `cZero` (`ZeroParadox/Miniature.lean`) and
-- `Pole.cornerZero` (`ZeroParadox/Valuation/PoleCorners.lean`) at their zero; `T fullMix`
-- (`ZeroParadox/Reals/MarkovSpectralGap.lean`) at 0, where `v0` and 0 both step to 0.
example : (ZeroParadox.Motion.ofFun ZeroParadox.Miniature.Pole.cZero).FanIn
    ZeroParadox.Miniature.Pole.zero :=
  ⟨ZeroParadox.Miniature.Pole.zero, ZeroParadox.Miniature.Pole.infty, by decide, rfl, rfl⟩
example : (ZeroParadox.Motion.ofFun ZeroParadox.Pole.cornerZero).FanIn ZeroParadox.Pole.zero :=
  ⟨ZeroParadox.Pole.zero, ZeroParadox.Pole.infty, by decide, rfl, rfl⟩
example : (ZeroParadox.Motion.ofFun ⇑(ZeroParadox.T ZeroParadox.fullMix)).FanIn 0 :=
  ⟨ZeroParadox.v0, 0, ZeroParadox.v0_ne_zero,
    (show ZeroParadox.T ZeroParadox.fullMix ZeroParadox.v0 = 0 by
      rw [ZeroParadox.fullMix_eigen_zero, zero_smul]).symm, (map_zero _).symm⟩
-- Statement: each of the four cells {one-to-one or not} × {both trap sets (§ XVI) nonempty, both
-- empty} has a function-step member; the mixed cells are not shown. Not one-to-one, both nonempty:
-- `cZero` (zero steps to itself only; no step enters infty).
example : (ZeroParadox.Motion.ofFun ZeroParadox.Miniature.Pole.cZero).FanIn
      ZeroParadox.Miniature.Pole.zero ∧
    (∀ a, (ZeroParadox.Motion.ofFun ZeroParadox.Miniature.Pole.cZero).step a
      ZeroParadox.Miniature.Pole.infty → a = ZeroParadox.Miniature.Pole.infty) ∧
    (∀ b, (ZeroParadox.Motion.ofFun ZeroParadox.Miniature.Pole.cZero).step
      ZeroParadox.Miniature.Pole.zero b → b = ZeroParadox.Miniature.Pole.zero) :=
  ⟨⟨ZeroParadox.Miniature.Pole.zero, ZeroParadox.Miniature.Pole.infty, by decide, rfl, rfl⟩,
    fun _ (ha : ZeroParadox.Miniature.Pole.infty = ZeroParadox.Miniature.Pole.zero) => (nomatch ha),
    fun _ hb => hb⟩
-- Statement: not one-to-one, both empty: on ℕ, `0 ↦ 1`, `1 ↦ 0`, `n + 2 ↦ n`; this cell needs an
-- infinite carrier (the `example` after this one).
example : let g : ℕ → ℕ := fun n => match n with | 0 => 1 | 1 => 0 | n + 2 => n
    (ZeroParadox.Motion.ofFun g).FanIn 0 ∧
    (∀ y, ¬ ∀ a, (ZeroParadox.Motion.ofFun g).step a y → a = y) ∧
    (∀ y, ¬ ∀ b, (ZeroParadox.Motion.ofFun g).step y b → b = y) := by
  intro g
  refine ⟨⟨1, 2, by decide, rfl, rfl⟩, fun y h => ?_, fun y h => ?_⟩
  · have := h (y + 2) rfl; omega
  · have h' := h (g y) rfl
    match y, h' with
    | 0, h' => exact absurd h' (by decide)
    | 1, h' => exact absurd h' (by decide)
    | n + 2, h' => exact absurd (show n = n + 2 from h') (by omega)
-- Statement: on a finite carrier, if `g` is not one-to-one, some point is entered from no other point
-- in `ofFun g` (`g` is not onto, `Finite.injective_iff_surjective`).
example {α : Type*} [Finite α] (g : α → α) (h : ¬ Function.Injective g) :
    ∃ y, ∀ a, (ZeroParadox.Motion.ofFun g).step a y → a = y := by
  have hns : ¬ Function.Surjective g := fun hs => h (Finite.injective_iff_surjective.2 hs)
  simp only [Function.Surjective, not_forall, not_exists] at hns
  obtain ⟨y, hy⟩ := hns
  exact ⟨y, fun a (ha : y = g a) => absurd ha.symm (hy a)⟩
-- Statement: one-to-one, both nonempty: `Pole.cornerId`; one-to-one, both empty: `Pole.swap`.
example : Function.Injective ZeroParadox.Pole.cornerId ∧
    (∀ a, (ZeroParadox.Motion.ofFun ZeroParadox.Pole.cornerId).step a ZeroParadox.Pole.zero →
      a = ZeroParadox.Pole.zero) ∧
    (∀ b, (ZeroParadox.Motion.ofFun ZeroParadox.Pole.cornerId).step ZeroParadox.Pole.zero b →
      b = ZeroParadox.Pole.zero) :=
  ⟨ZeroParadox.Pole.cornerId_bijective.1, fun _ ha => ha.symm, fun _ hb => hb⟩
example : Function.Injective ZeroParadox.Pole.swap ∧
    (∀ y, ¬ ∀ a, (ZeroParadox.Motion.ofFun ZeroParadox.Pole.swap).step a y → a = y) ∧
    (∀ y, ¬ ∀ b, (ZeroParadox.Motion.ofFun ZeroParadox.Pole.swap).step y b → b = y) := by
  refine ⟨ZeroParadox.Pole.swap_bijective.1, fun y h => ?_, fun y h => ?_⟩
  · cases y
    · exact absurd (h ZeroParadox.Pole.infty rfl) (by decide)
    · exact absurd (h ZeroParadox.Pole.zero rfl) (by decide)
  · cases y
    · exact absurd (h _ rfl) (by decide)
    · exact absurd (h _ rfl) (by decide)
-- Statement: bit tapes, OVER prepending `false` (§ XIII): in the reverse, the tapes with no step are
-- the tapes whose first bit is `true`.
example (y : ℕ → Bool) : (ZeroParadox.Motion.ofFun
      (fun a : ℕ → Bool => fun n => match n with | 0 => false | k + 1 => a k)).reverse.NoStepAt y ↔
    y 0 = true := by
  rw [(ZeroParadox.Motion.reverse_ofFun_of_injective _
    (fun _ _ h => funext fun k => congrFun h (k + 1)) y).2.1]
  constructor
  · intro h
    cases h0 : y 0
    · exact absurd (funext fun n => by cases n with
        | zero => exact h0.symm
        | succ k => rfl) (h (fun k => y (k + 1)))
    · rfl
  · intro h x hx
    have := congrFun hx 0
    rw [h] at this
    exact Bool.false_ne_true this
-- Statement: CONTROL: the shift `x ↦ (n ↦ x (n + 1))` is not one-to-one, and in its reverse ⊥ of
-- `ℕ → Bool` has two distinct successors. Reading: deciding the reverse trichotomy at every tape is
-- not measured here; the forward one is the weak limited principle of omniscience (§ XIII).
example : let M := ZeroParadox.Motion.ofFun (fun x : ℕ → Bool => fun n => x (n + 1))
    ∃ a b, a ≠ b ∧ M.reverse.step ⊥ a ∧ M.reverse.step ⊥ b :=
  ⟨⊥, fun n => decide (n = 0), fun h => by simpa using congrFun h 0, rfl, rfl⟩
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
-- Statement: where the uniform die statements land among the omniscience principles
-- (`ZeroParadox/Category/LawvereTaboo.lean` § V): excluded middle from the corner split
-- (`em_of_corner_loop_or_climb`, § I); weak excluded middle from the cut (`wem_of_botCovered_botIntervalTwo`,
-- § IV); LPO from the trichotomy and from a total selector over a `Bool`-valued step on `ℕ` (§§ X, XI);
-- Markov's principle from fan-in on `ℕ` (§ XII). Each lands on its principle and on the weaker ones
-- the arrows there reach; here the cut's.
example (h : ∀ (β : Type) [PartialOrder β] [OrderBot β], ZeroParadox.BotCovered β →
    ZeroParadox.BotIntervalTwo β) : ZeroParadox.WLPO ∧ ZeroParadox.LLPO :=
  have w := ZeroParadox.wlpo_of_weakExcludedMiddle (ZeroParadox.wem_of_botCovered_botIntervalTwo h)
  ⟨w, ZeroParadox.llpo_of_wlpo w⟩
-- Reading (cited, not claimed): the reductions to LPO and to Markov's principle are Brouwerian
-- counterexamples in the "stable" form, a statement implying a principle quantified over all binary
-- sequences (Diener, arXiv:1804.05495v3, § 0.3, p. 5); the excluded-middle and weak-excluded-middle
-- reductions quantify over `Prop` instead. The die-shaped statements themselves were not located in the
-- sources read, as of 2026-10-28. What moves the landing point is the carrier. Decidable equality frees
-- the corner split (`Motion.corner_iff_loop_or_climb`) and the cut (`botCovered_botIntervalTwo`); it
-- does not free registration, whose taboo comes from a `Prop`-valued UP-definedness and is reached on
-- `Unit` (`Motion.em_of_registeredDecidable`). On `ℕ`, the quantifier in the trichotomy, the selector
-- and fan-in returns as LPO or Markov's principle; this is measured for `ℕ` only. Escardó (preprint of
-- JSL 78(3) (2013), p. 1) grades the same principle by the set searched, "For X finite this is
-- trivial, and for X = ℕ, this is LPO", and exhibits infinite sets on which it holds, the first being
-- ℕ∞. LPO and weak excluded middle are not shown comparable here: the model over ℝ shows that LPO does
-- not imply weak excluded middle (`LawvereTaboo.lean` § V, last Reading), and the converse was not
-- settled from the sources read.
-- Statement: `Prop`, UP double negation `p ↦ ¬¬p` (total, so registration is free,
-- `registeredDecidable_of_upTotal`), OVER negation `p → ¬p`: a decidable proposition is a landing.
example (p : Prop) [Decidable p] :
    (ZeroParadox.Motion.ofTotal (fun q : Prop => ¬¬q)
      (fun _ => propext ⟨fun h hn => h fun hnn => hnn hn, fun h hnnn => hnnn h⟩)
      (fun a b => b = ¬a)).IsLanding p :=
  Part.mem_some_iff.2 (propext ⟨fun h hn => hn h, Decidable.of_not_not⟩)
-- Statement: and every proposition is a landing iff excluded middle (`em_iff_all_props_regular`).
example : (∀ p, (ZeroParadox.Motion.ofTotal (fun q : Prop => ¬¬q)
      (fun _ => propext ⟨fun h hn => h fun hnn => hnn hn, fun h hnnn => hnnn h⟩)
      (fun a b => b = ¬a)).IsLanding p) ↔ ZeroParadox.ExcludedMiddle := by
  constructor
  · intro h
    refine ZeroParadox.em_iff_all_props_regular.2 fun p => ?_
    exact (ZeroParadox.prop_isRegular_iff p).2 (Part.mem_some_iff.1 (h p)).symm
  · intro hem p
    exact Part.mem_some_iff.2
      ((ZeroParadox.prop_isRegular_iff p).1 (ZeroParadox.em_iff_all_props_regular.1 hem p)).symm
-- Statement: CONTROL: on `Fin 3` with UP `x ↦ xᶜᶜ`, the middle point is not a landing
-- (`fin3_middle_not_regular`).
example : ¬ (ZeroParadox.Motion.ofTotal (fun x : Fin 3 => xᶜᶜ)
    (fun x => congrArg compl (compl_compl_compl x)) (fun _ _ => False)).IsLanding 1 :=
  fun h => ZeroParadox.fin3_middle_not_regular (Part.mem_some_iff.1 h).symm
-- Statement: with OVER negation the corner does not fire, since `¬¬¬a = ¬a`: every step lands on a
-- landing. No proposition is a fixed point of negation (`leavesAt_ofFun_not`), so the premise of
-- `not_corner_of_fun` fails here.
example : ¬ (ZeroParadox.Motion.ofTotal (fun q : Prop => ¬¬q)
      (fun _ => propext ⟨fun h hn => h fun hnn => hnn hn, fun h hnnn => hnnn h⟩)
      (fun a b => b = ¬a)).Corner := by
  rintro ⟨y, b, z, -, hs, hz, hzb⟩
  have hb : b = ¬y := hs
  have hz' : z = ¬¬b := Part.mem_some_iff.1 hz
  apply hzb
  rw [hz', hb]
  exact propext ⟨fun h hy => h fun hny => hny hy, fun h hnny => hnny h⟩

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
#check @ZeroParadox.Motion.not_exists_involution_reverses_lt -- Statement: if OVER is `<` on a preorder with a least element and no maximal element, no involution reverses it
-- Statement: its hypotheses already make the carrier infinite (Mathlib `NoMaxOrder.infinite`, the
-- least element supplying `Nonempty`).
example {α : Type} [Preorder α] [OrderBot α] [NoMaxOrder α] : Infinite α := NoMaxOrder.infinite
-- Statement: CONTROL: infinitude alone does not block the reversal: `WithBot (WithTop ℤ)` is infinite,
-- has ⊥ and ⊤, and `z ↦ -z` with ⊥ and ⊤ exchanged is an involution reversing `<` (`[propext,
-- Classical.choice, Quot.sound]`). Reading: both hypotheses are operative. Dropping the absence of a
-- maximal element gives this example; dropping the least element gives ℤ under negation (the CONTROLS
-- below); `Fin 3` with `Fin.rev` (below) is the finite member.
example : Infinite (WithBot (WithTop ℤ)) ∧ ∃ σ : WithBot (WithTop ℤ) → WithBot (WithTop ℤ),
    Function.Involutive σ ∧ ∀ a b, a < b ↔ σ b < σ a := by
  obtain ⟨σ, e1, e2, e3⟩ : ∃ σ : WithBot (WithTop ℤ) → WithBot (WithTop ℤ),
      σ ⊥ = ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) ∧
      σ ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) = ⊥ ∧
      ∀ z : ℤ, σ (((z : WithTop ℤ)) : WithBot (WithTop ℤ)) =
        (((-z : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) :=
    ⟨fun x => match x with
      | none => some none
      | some none => none
      | some (some z) => some (some (-z)), rfl, rfl, fun _ => rfl⟩
  refine ⟨Infinite.of_injective (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ)))
      (fun _ _ h => WithTop.coe_injective (WithBot.coe_injective h)), σ, fun x => ?_, fun a b => ?_⟩
  · induction x using WithBot.recBotCoe with
    | bot => rw [e1, e2]
    | coe x =>
      induction x using WithTop.recTopCoe with
      | top => rw [e2, e1]
      | coe z => rw [e3, e3, neg_neg]
  · induction a using WithBot.recBotCoe with
    | bot =>
      induction b using WithBot.recBotCoe with
      | bot => simp
      | coe b =>
        induction b using WithTop.recTopCoe with
        | top => rw [e1, e2]
        | coe b =>
          rw [e1, e3]
          exact ⟨fun _ => WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _), fun _ => WithBot.bot_lt_coe _⟩
    | coe a =>
      induction a using WithTop.recTopCoe with
      | top =>
        induction b using WithBot.recBotCoe with
        | bot => rw [e1, e2]
        | coe b =>
          induction b using WithTop.recTopCoe with
          | top => simp
          | coe b => rw [e2, e3]; simp
      | coe a =>
        induction b using WithBot.recBotCoe with
        | bot => rw [e1, e3]; simp
        | coe b =>
          induction b using WithTop.recTopCoe with
          | top =>
            rw [e2, e3]
            exact ⟨fun _ => WithBot.bot_lt_coe _,
              fun _ => WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)⟩
          | coe b =>
            rw [e3, e3, WithBot.coe_lt_coe, WithBot.coe_lt_coe, WithTop.coe_lt_coe, WithTop.coe_lt_coe]
            exact neg_lt_neg_iff.symm
-- Statement: it applies to `NNReal`, `Ordinal`, and `WithBot ℤ`, so no involution reverses `<` on
-- any of them; `WithBot ℤ`'s `<` is not well-founded (next `example`), so the hypotheses hold there
-- without well-foundedness.
example : ¬ ∃ σ : NNReal → NNReal, Function.Involutive σ ∧
    ∀ a b, (ZeroParadox.Motion.ofTotal (id : NNReal → NNReal) (fun _ => rfl) (· < ·)).step a b ↔
      (ZeroParadox.Motion.ofTotal (id : NNReal → NNReal) (fun _ => rfl) (· < ·)).step (σ b) (σ a) :=
  ZeroParadox.Motion.not_exists_involution_reverses_lt
example : ¬ ∃ σ : Ordinal.{0} → Ordinal.{0}, Function.Involutive σ ∧
    ∀ a b, (ZeroParadox.Motion.ofTotal (id : Ordinal.{0} → Ordinal.{0}) (fun _ => rfl) (· < ·)).step a b ↔
      (ZeroParadox.Motion.ofTotal (id : Ordinal.{0} → Ordinal.{0}) (fun _ => rfl) (· < ·)).step
        (σ b) (σ a) :=
  ZeroParadox.Motion.not_exists_involution_reverses_lt
example : ¬ ∃ σ : WithBot ℤ → WithBot ℤ, Function.Involutive σ ∧
    ∀ a b, (ZeroParadox.Motion.ofTotal (id : WithBot ℤ → WithBot ℤ) (fun _ => rfl) (· < ·)).step a b ↔
      (ZeroParadox.Motion.ofTotal (id : WithBot ℤ → WithBot ℤ) (fun _ => rfl) (· < ·)).step
        (σ b) (σ a) :=
  ZeroParadox.Motion.not_exists_involution_reverses_lt
example : ¬ WellFounded ((· < ·) : WithBot ℤ → WithBot ℤ → Prop) :=
  ZeroParadox.not_wf_of_descent (fun n : ℕ => ((-(n : ℤ) : ℤ) : WithBot ℤ))
    (fun n => WithBot.coe_lt_coe.2 (by omega))
-- Statement: CONTROLS: `<` is reversed by negation on ℤ (no least element) and by `Fin.rev` on `Fin 3`
-- (a maximal element).
example : ∀ a b : ℤ, a < b ↔ -b < -a := fun _ _ => neg_lt_neg_iff.symm
example : ∀ a b : Fin 3, a < b ↔ Fin.rev b < Fin.rev a := by decide
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
#check @ZeroParadox.runMotion_noStepAt_iff      -- Statement: in the run motion, no step at `s` iff `f s = none`
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
-- Statement: the wheel carrier `ZPWheelElem` is ℚ with two adjoined points.
example : ZeroParadox.ZPWheelElem ≃ Option (Option ℚ) where
  toFun x := match x with
    | .bot => none
    | .inf => some none
    | .fin q => some (some q)
  invFun o := match o with
    | none => .bot
    | some none => .inf
    | some (some q) => .fin q
  left_inv x := by cases x <;> rfl
  right_inv o := by rcases o with _ | _ | q <;> rfl
-- Statement: there, OVER the wheel inversion `/` (an involution, `winv_winv`): `0·/0` steps only to
-- itself, and `0` and `∞` are exchanged, each stepping elsewhere. The exchange is the INVERSION kind,
-- two distinct points swapped, never the coincidence of the pole ⊥ = 0 = ∞, which is a chart claim
-- (`ZeroParadox/BottomCannotBe.lean` § INVERSION).
example : (ZeroParadox.Motion.ofFun ZeroParadox.zpwInv).SelfOnlyAt ZeroParadox.ZPWheelElem.bot ∧
    ZeroParadox.zpwInv (.fin 0) = .inf ∧ ZeroParadox.zpwInv .inf = .fin 0 ∧
    (ZeroParadox.Motion.ofFun ZeroParadox.zpwInv).LeavesAt (.fin 0) ∧
    (ZeroParadox.Motion.ofFun ZeroParadox.zpwInv).LeavesAt .inf :=
  ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 rfl, ZeroParadox.zpw_inv_zero_eq_inf,
    ZeroParadox.zpw_inv_inf_eq_zero,
    (ZeroParadox.Motion.leavesAt_ofFun_iff _ _).2 (by rw [ZeroParadox.zpw_inv_zero_eq_inf]; simp),
    (ZeroParadox.Motion.leavesAt_ofFun_iff _ _).2 (by rw [ZeroParadox.zpw_inv_inf_eq_zero]; simp)⟩
#check @ZeroParadox.wheelBot_selfOnlyAt_winv     -- Statement: in every wheel, `0·/0` steps only to itself under `/`
-- Statement: CONTROL, no adjoined point: in a group with zero (ℚ), inversion fixes `0` (`inv_zero`), so
-- `0` steps only to itself.
example : (ZeroParadox.Motion.ofFun (Inv.inv : ℚ → ℚ)).SelfOnlyAt 0 :=
  (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 inv_zero
-- Reading: with two adjoined points, `∞` is exchanged with `0` and `0·/0` is the involution's fixed
-- centre, not an end; with none, `0` is fixed and nothing is exchanged with it. The one-point case
-- between them is not measured here.
#check @ZeroParadox.rInv_conj_rScale            -- Statement: on `OnePoint ℚ_[2]`, `rInv ∘ rScale n ∘ rInv = rScale (-n)`
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
-- (cited, not claimed): Lawvere 1969 (TAC reprint p. 3) says the similarity of "the famous arguments
-- of Cantor, Russell, Gödel and Tarski ... suggests that these arguments should all be special cases
-- of a single theorem" and offers "a fixed-point theorem in cartesian closed categories which seems
-- to play this role"; extending Lawvere, Yanofsky 2003 treats the
-- halting problem (pp. 11–12), the diagonal lemma (Theorem 4, pp. 15–16), Löb's paradox (p. 18), the
-- recursion theorem (pp. 18–19) and Rice (p. 19). No shared mechanism among the faces below is claimed.
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
#check @ZeroParadox.Motion.selfOnlyAt_ofFun_lfp  -- Statement: the existence half: on a complete lattice, for a monotone `f`, `f.lfp` steps to itself only in `ofFun f` (`OrderHom.map_lfp`)
#check @ZeroParadox.Motion.not_monotone_of_forall_leavesAt -- Statement: so if `ofFun f` steps elsewhere at every point of a complete lattice, `f` is not monotone; one way
-- Statement: `Bool` negation, which steps elsewhere at every point, is not monotone, through it.
example : ¬ Monotone (fun b : Bool => !b) :=
  ZeroParadox.Motion.not_monotone_of_forall_leavesAt _ fun y =>
    (ZeroParadox.Motion.leavesAt_ofFun_iff _ y).2 (by cases y <;> decide)
-- Statement: CONTROL: on ℕ, not a complete lattice, `Nat.succ` is monotone and steps elsewhere at every
-- point.
example : Monotone Nat.succ ∧ ∀ y, (ZeroParadox.Motion.ofFun Nat.succ).LeavesAt y :=
  ⟨fun _ _ h => Nat.succ_le_succ h,
    fun y => (ZeroParadox.Motion.leavesAt_ofFun_iff _ y).2 (Nat.succ_ne_self y)⟩
-- Statement: the converse fails: on ℕ∞ the map exchanging `0` and `1` and fixing the rest is not
-- monotone, and `2` steps to itself only.
example : let f : ℕ∞ → ℕ∞ := fun x => if x = 0 then 1 else if x = 1 then 0 else x
    ¬ Monotone f ∧ (ZeroParadox.Motion.ofFun f).SelfOnlyAt 2 := by
  intro f
  refine ⟨fun hm => absurd (hm (show (0 : ℕ∞) ≤ 1 from zero_le_one)) (by simp [f]),
    (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 (by simp [f])⟩
-- Statement: Curry's `q ↦ (q → P)` is antitone. Reading: with the Curry entry above (a point stepping
-- to itself only iff `P`), an antitone map decides nothing either.
example (P : Prop) : Antitone (fun q : Prop => q → P) := fun _ _ hab h ha => h (hab ha)
-- Statement: OVER a relation `r` with UP the identity: if `r` is well-founded, no point steps to itself
-- only (`wf_no_selfloop`); one way.
example {α : Type} {r : α → α → Prop} (h : WellFounded r) (y : α) :
    ¬ (ZeroParadox.Motion.ofTotal id (fun _ => rfl) r).SelfOnlyAt y :=
  fun hy => ZeroParadox.wf_no_selfloop h y hy.1
#check @ZeroParadox.Motion.rank_add_one_le_of_transGen -- Statement: if a rank into ℕ∞ drops by at least one along each step, it drops by at least one along every run of one or more steps
#check @ZeroParadox.Motion.rank_eq_top_of_cycle  -- Statement: so every point on a cycle of steps has rank ⊤ of ℕ∞
#check @ZeroParadox.Motion.eq_of_step_self_of_rank -- Statement: and if `p` is the only point of rank ⊤ of ℕ∞, every point that steps to itself is `p`; one way
#check @ZeroParadox.Motion.not_cycle_of_nat_rank -- Statement: if such a rank is ℕ-valued, no point lies on a cycle
-- Statement: member, the carrier ℕ∞ of `ZeroParadox/Settheory/Model.lean`: the reverse of `ofFun (· + 1)`
-- has the rank `id`, so a point on a cycle of it is ⊤ of ℕ∞.
example (y : ℕ∞)
    (hy : Relation.TransGen (ZeroParadox.Motion.ofFun (fun x : ℕ∞ => x + 1)).reverse.step y y) :
    y = ⊤ :=
  ZeroParadox.Motion.rank_eq_top_of_cycle id (fun a b h => by
    change a = b + 1 at h
    subst h; exact le_rfl) hy
-- Statement: CONTROL, `eq_of_step_self_of_rank`'s converse fails: on `Fin 3` with OVER `0 → 0`,
-- `1 → 2`, `2 → 1`, `0` is the only point that steps to itself, and no such rank has all its points of
-- rank ⊤ of ℕ∞ equal to one point.
example : let M := (ZeroParadox.Motion.ofTotal (id : Fin 3 → Fin 3) (fun _ => rfl)
      (fun a b => (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1)))
    M.step 0 0 ∧ (∀ y, M.step y y → y = 0) ∧
      ¬ ∃ (v : Fin 3 → ℕ∞) (p : Fin 3), (∀ a b, M.step a b → v b + 1 ≤ v a) ∧ ∀ x, v x = ⊤ → x = p := by
  intro M
  refine ⟨Or.inl ⟨rfl, rfl⟩, fun y hy => by
    rcases hy with ⟨h, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h
    · exact absurd (h1.symm.trans h2) (by decide)
    · exact absurd (h1.symm.trans h2) (by decide), ?_⟩
  rintro ⟨v, p, hv, hu⟩
  have c1 : Relation.TransGen M.step 1 1 :=
    Relation.TransGen.tail (Relation.TransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      (Or.inr (Or.inr ⟨rfl, rfl⟩))
  have c2 : Relation.TransGen M.step 2 2 :=
    Relation.TransGen.tail (Relation.TransGen.single (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have e1 := hu 1 (ZeroParadox.Motion.rank_eq_top_of_cycle v hv c1)
  have e2 := hu 2 (ZeroParadox.Motion.rank_eq_top_of_cycle v hv c2)
  exact absurd (e1.trans e2.symm) (by decide)
-- Reading: the three ℕ∞-valued rank theorems print `[propext, Classical.choice, Quot.sound]`, as does
-- the bare statement `(∀ x : ℕ∞, x + 1 ≤ x → x = ⊤) → True` (statement control, measured 2026-10-21):
-- their footprint is carried by ℕ∞ in the statement. `not_cycle_of_nat_rank` states no ℕ∞ and is
-- proved directly over ℕ: `[propext, Quot.sound]`. It covers ℕ-valued ranks only; an ordinal-valued
-- form, for well-founded relations in general, is not built here. A rank dropping along every step is
-- a well-foundedness argument, the kind a liveness proof rests on (Alpern and Schneider, IPL 21 (1985),
-- p. 181).
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

/-! ### § XVI. The over-then-up / up-then-over pair; leg polarity against a carrier order, the causes
of the trap sets, arrival and fan-in, the clock machine -/
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
example {α : Type*} [PartialOrder α] (M : ZeroParadox.Motion α) (hu : M.UpLowers)
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
-- Reading: one-way "cannot be" as membership in two trap sets, `{y | ∀ a, step a y → a = y}`
-- (the points stepped into only from themselves or from nothing) and `{y | ∀ b, step y b → b = y}`
-- (the points stepping only to themselves or nowhere). Each trap theorem below uses one datum, named in
-- its premises, and the data are kept apart: the next three use the carrier order
-- (antisymmetry, ⊥ least), and of them the second and third state membership; the first states that
-- no step goes strictly down, and at ⊥ it gives membership in the first set, as
-- `eq_bot_of_step_to_bot` states; the fourth uses at most one
-- successor and no order. After the controls: emptiness of a carrier, a thin category's order,
-- absorption, at most one predecessor, and reachability under a function step.
#check @ZeroParadox.Motion.eq_of_step_le_of_stepRaises -- Statement: in a partial order, if OVER raises, no step goes strictly down
#check @ZeroParadox.Motion.eq_bot_of_step_to_bot -- Statement: with ⊥ of `α`, if OVER raises, every step into ⊥ starts at ⊥: ⊥ is in the first set
#check @ZeroParadox.Motion.eq_bot_of_step_from_bot -- Statement: if OVER lowers, every step out of ⊥ ends at ⊥: ⊥ is in the second set
#check @ZeroParadox.Motion.selfOnlyAt_of_step_self -- Statement: if `y` has at most one successor and steps to itself, it steps to itself only: `y` is in the second set
-- Statement: read in the order dual, the lowering fact at ⊥ (`eq_bot_of_step_from_bot` in `αᵒᵈ`)
-- becomes a raising fact at ⊤: if OVER raises, every step out of ⊤ of `α` ends at ⊤.
example {α : Type*} [PartialOrder α] [OrderTop α] (M : ZeroParadox.Motion α) (h : M.StepRaises)
    (b : α) (hs : M.step ⊤ b) : b = ⊤ :=
  ZeroParadox.Motion.eq_bot_of_step_from_bot (α := αᵒᵈ) (M := M) h b hs
-- Statement: reversing the step (`Motion.reverse`) swaps the two sets ...
example {α : Type*} (M : ZeroParadox.Motion α) :
    {y | ∀ a, M.reverse.step a y → a = y} = {y | ∀ b, M.step y b → b = y} := rfl
example {α : Type*} (M : ZeroParadox.Motion α) :
    {y | ∀ b, M.reverse.step y b → b = y} = {y | ∀ a, M.step a y → a = y} := rfl
-- Statement: ... so the fact that, if OVER lowers, every step out of ⊥ ends at ⊥, is
-- `eq_bot_of_step_to_bot` applied to the reversed motion (`stepRaises_reverse`).
example {α : Type*} [PartialOrder α] [OrderBot α] (M : ZeroParadox.Motion α) (h : M.StepLowers)
    (b : α) (hs : M.step ⊥ b) : b = ⊥ :=
  ZeroParadox.Motion.eq_bot_of_step_to_bot (M := M.reverse)
    (ZeroParadox.Motion.stepRaises_reverse.2 h) b hs
-- Statement: raising trap at ⊥ (the first set), a member with nothing to test: the ordinal tower
-- motion's OVER raises (`Ordinal.right_le_opow`) and nothing steps into ⊥ of `Ordinal` (`ω ^ a ≠ 0`),
-- so `eq_bot_of_step_to_bot` holds there with no step into ⊥ to check.
example : ZeroParadox.ordinalTowerMotion.{0}.StepRaises ∧
    ∀ a, ¬ ZeroParadox.ordinalTowerMotion.{0}.step a ⊥ := by
  refine ⟨?_, fun a h => ?_⟩
  · rintro a b rfl
    exact Ordinal.right_le_opow a Ordinal.one_lt_omega0
  · exact (Ordinal.opow_ne_zero a Ordinal.omega0_ne_zero) h.symm
-- Statement: raising trap at ⊥, a member with a step into ⊥ to test: `ofFun id` on ℕ raises, steps
-- 0, ⊥ of ℕ, to 0, and every step into 0 starts at 0.
example : (ZeroParadox.Motion.ofFun (id : ℕ → ℕ)).StepRaises ∧
    (ZeroParadox.Motion.ofFun (id : ℕ → ℕ)).step 0 0 ∧
    ∀ a, (ZeroParadox.Motion.ofFun (id : ℕ → ℕ)).step a 0 → a = 0 :=
  have h : (ZeroParadox.Motion.ofFun (id : ℕ → ℕ)).StepRaises := by rintro a b rfl; exact le_rfl
  ⟨h, rfl, ZeroParadox.Motion.eq_bot_of_step_to_bot h⟩
-- Statement: lowering trap at ⊥ (the second set), a member with steps out of ⊥ to test: `Nat.pred`
-- lowers, so every step out of 0, ⊥ of ℕ, lands on 0 (the order route). Separately, `SelfOnlyAt 0`
-- in `ofFun Nat.pred` comes from the function route, `selfOnlyAt_ofFun_iff` with `Nat.pred 0 = 0`.
example : ∀ b, (ZeroParadox.Motion.ofFun Nat.pred).step 0 b → b = 0 :=
  ZeroParadox.Motion.eq_bot_of_step_from_bot (by rintro a b rfl; exact Nat.pred_le a)
example : (ZeroParadox.Motion.ofFun Nat.pred).SelfOnlyAt 0 :=
  (ZeroParadox.Motion.selfOnlyAt_ofFun_iff Nat.pred 0).2 rfl
-- Reading (cited): a point that steps to itself only is what Markov-chain texts call an absorbing
-- state (Levin–Peres, Markov Chains and Mixing Times, 2nd ed., § 1.7, p. 15: "the chain never leaves
-- x once it first visits x; such states are called absorbing"); the corpus uses the term at
-- `blockKernel_pure0_stationary` (`ZeroParadox/Computability/MarkovNuUniversal.lean`). A transition
-- matrix gives every state a step, so the second set's points with no step have no counterpart there.
-- Statement: ZP-A's join step `a → a ⊔ z` raises in the induced order, so
-- `eq_of_step_le_of_stepRaises` re-derives `t_snap_irreversible`.
example {L : Type*} [ZeroParadox.ZPSemilattice L] {x y : L} (hle : ZeroParadox.ZPSemilattice.le x y)
    (hne : x ≠ y) : ¬ ∃ z, ZeroParadox.ZPSemilattice.join y z = x := by
  letI := ZeroParadox.zpSemilatticeSup L
  let M := ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
    (fun a b => ∃ z, b = ZeroParadox.ZPSemilattice.join a z)
  have hr : M.StepRaises := by
    rintro a b ⟨z, rfl⟩
    exact (le_sup_left : a ≤ a ⊔ z)
  rintro ⟨z, hz⟩
  exact hne (ZeroParadox.Motion.eq_of_step_le_of_stepRaises hr ⟨z, hz.symm⟩ hle)
-- Statement: the machine face: a configuration that loops in place steps only to itself, with at most
-- one successor from `deterministic_has_no_fanout`.
example {σ : Type} (f : σ → Option σ) (s : σ) (h : ZeroParadox.LoopsInPlace f s) :
    (ZeroParadox.runMotion f).SelfOnlyAt s :=
  ZeroParadox.Motion.selfOnlyAt_of_step_self
    (fun b c hb hc => ZeroParadox.deterministic_has_no_fanout f s b c hb hc) h
-- Statement: CONTROL for the order traps: on `Bool`, OVER `≠` neither raises nor lowers, and ⊥ of
-- `Bool`, `false`, is entered from `true`. For the fourth: § XI's always-true relation on `Bool` steps
-- `true` to itself and elsewhere.
example : let M := ZeroParadox.Motion.ofTotal (fun _ : Bool => true) (fun _ => rfl) (fun a b => a ≠ b)
    M.step true ⊥ ∧ ¬ M.StepRaises ∧ ¬ M.StepLowers :=
  ⟨show true ≠ false by decide,
    fun h => absurd (h true false (show true ≠ false by decide)) (by decide),
    fun h => absurd (h false true (show false ≠ true by decide)) (by decide)⟩
#check @ZeroParadox.Motion.eq_of_step_to_isEmpty -- Statement: emptiness: if each step `a → b` gives a map `E a → E b`, `E y` is empty and every other `E a` is inhabited, then `y` is in the first set; no order, and the step need not be single-valued
-- Statement: member: on ℕ with OVER "a map `Fin m → Fin n` exists", `0` is in the first set, and the
-- step has two successors at `0`, does not raise (`3 → 1`) and does not lower (`0 → 1`) in ℕ's order.
example : let M := (ZeroParadox.Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl)
      (fun m n => Nonempty (Fin m → Fin n)))
    M.step 0 1 ∧ M.step 0 2 ∧ ¬ M.StepRaises ∧ ¬ M.StepLowers ∧ ∀ a, M.step a 0 → a = 0 := by
  intro M
  refine ⟨⟨Fin.elim0⟩, ⟨Fin.elim0⟩, fun h => absurd (h 3 1 ⟨fun _ => 0⟩) (by decide),
    fun h => absurd (h 0 1 ⟨Fin.elim0⟩) (by decide),
    ZeroParadox.Motion.eq_of_step_to_isEmpty (M := M) (E := fun n => Fin n) (fun _ _ h => h)
      ⟨fun i => i.elim0⟩ (fun a => ?_)⟩
  cases a with
  | zero => exact Or.inr rfl
  | succ k => exact Or.inl ⟨0⟩
-- Statement: member: the same with morphisms of `KleisliCat PMF` between `fC_functor`'s objects, where
-- `0` is in the first set by `fC_no_return` (`ZeroParadox/Multihomed/InfoFunctor.lean`).
open CategoryTheory in
example : let M := (ZeroParadox.Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl)
      (fun m n => Nonempty (ZeroParadox.fC_functor.obj m ⟶ ZeroParadox.fC_functor.obj n)))
    ¬ M.StepRaises ∧ ¬ M.StepLowers ∧ ∀ a, M.step a 0 → a = 0 := by
  intro M
  have s01 : M.step 0 1 := ⟨ZeroParadox.fC_zero_isInitial.to _⟩
  have s31 : M.step 3 1 := ⟨fun _ => PMF.pure (0 : Fin 1)⟩
  refine ⟨fun h => absurd (h 3 1 s31) (by decide),
    fun h => absurd (h 0 1 s01) (by decide), fun a ⟨f⟩ => ?_⟩
  rcases Nat.eq_zero_or_pos a with h | h
  · exact h
  · exact ((ZeroParadox.fC_no_return h).false f).elim
-- Statement: in the step's own reachability preorder (`reachPreorder`, § III) every step raises.
-- Reading: so "OVER raises" informs about a trap only against an order given apart from the step.
example : let M := (ZeroParadox.Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl)
      (fun m n => Nonempty (Fin m → Fin n)))
    @ZeroParadox.Motion.StepRaises ℕ M (ZeroParadox.reachPreorder M.step).toLE :=
  fun _ _ h => Relation.ReflTransGen.single h
-- Statement: a thin category's order: in a partial order viewed as a category, OVER "a morphism
-- exists" raises, and `eq_bot_of_step_to_bot` puts ⊥ in the first set.
open CategoryTheory in
example (α : Type) [PartialOrder α] [OrderBot α] :
    let M := ZeroParadox.Motion.ofTotal (id : α → α) (fun _ => rfl) (fun X Y => Nonempty (X ⟶ Y))
    M.StepRaises ∧ ∀ X, M.step X ⊥ → X = ⊥ := by
  intro M
  have h : M.StepRaises := fun _ _ ⟨f⟩ => leOfHom f
  exact ⟨h, ZeroParadox.Motion.eq_bot_of_step_to_bot h⟩
-- Statement: and in any category, that motion on `Cᵒᵖ` is the reversed motion on `C`.
open CategoryTheory in
example {C : Type} [Category C] (X Y : C) :
    (ZeroParadox.Motion.ofTotal (id : Cᵒᵖ → Cᵒᵖ) (fun _ => rfl) (fun X Y => Nonempty (X ⟶ Y))).step
        (Opposite.op X) (Opposite.op Y) ↔
      (ZeroParadox.Motion.ofTotal (id : C → C) (fun _ => rfl)
        (fun X Y => Nonempty (X ⟶ Y))).reverse.step X Y :=
  ⟨fun ⟨f⟩ => ⟨f.unop⟩, fun ⟨f⟩ => ⟨f.op⟩⟩
-- Reading: outside thin categories "a morphism exists" is a preorder that need not be antisymmetric,
-- and a strict initial object is entered only from objects isomorphic to it
-- (`ax_g2_from_strict_initial`, `ZeroParadox/Category/AxG2Reduce.lean`), a trap up to isomorphism;
-- that cause is not stated as a die premise here.
#check @ZeroParadox.wheelBot_absorbs             -- Statement: absorption: in every wheel, with OVER `a → a + z` for some `z`, `0·/0` steps only to itself (the second set) and every point steps to it
#check @ZeroParadox.zpw_addStep_no_polarity      -- Statement: on `ZPWheelElem` no partial order makes that step raise, nor lower
-- Statement: and there `0` has two successors, `0` and `1`, so the step is not single-valued: neither
-- the order datum nor the at-most-one-successor datum is available on this face.
example : let M := (ZeroParadox.Motion.ofTotal (id : ZeroParadox.ZPWheelElem → _) (fun _ => rfl)
      (fun a b => ∃ z, b = ZeroParadox.Wheel.wadd a z))
    M.step (.fin 0) (.fin 0) ∧ M.step (.fin 0) (.fin 1) ∧
      ZeroParadox.ZPWheelElem.fin 0 ≠ .fin 1 :=
  ⟨⟨.fin 0, show ZeroParadox.ZPWheelElem.fin 0 = ZeroParadox.zpwAdd (.fin 0) (.fin 0) by
      simp [ZeroParadox.zpwAdd]⟩,
    ⟨.fin 1, show ZeroParadox.ZPWheelElem.fin 1 = ZeroParadox.zpwAdd (.fin 0) (.fin 1) by
      simp [ZeroParadox.zpwAdd]⟩, by simp⟩
-- Statement: CAVEAT: where addition is idempotent, a join, the step raises and the absorber is ⊤, which
-- the order dual already puts in the second set (`eq_bot_of_step_from_bot` in `αᵒᵈ`).
example {α : Type} [SemilatticeSup α] [OrderTop α] (b : α)
    (hs : (ZeroParadox.Motion.ofTotal (id : α → α) (fun _ => rfl)
      (fun a b => ∃ z, b = a ⊔ z)).step ⊤ b) : b = ⊤ :=
  ZeroParadox.Motion.eq_bot_of_step_from_bot (α := αᵒᵈ)
    (by rintro a b ⟨z, rfl⟩; exact le_sup_left) b hs
-- Statement: CONTROL: ⊥ of a `ZPSemilattice` under its own join step is no absorber: it steps to every
-- point.
example {L : Type} [ZeroParadox.ZPSemilattice L] (a : L) :
    (ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun x y => ∃ z, y = ZeroParadox.ZPSemilattice.join x z)).step ZeroParadox.ZPSemilattice.bot a :=
  ⟨a, (ZeroParadox.ZPSemilattice.bot_join a).symm⟩
-- Statement: at most one predecessor, on the reversed motion: ⊤ of ℕ∞ steps only to itself in the
-- reverse of `ofFun (· + 1)` (`selfOnlyAt_of_step_self` there, since `x + 1 = ⊤` only at `x = ⊤`), so ⊤
-- of ℕ∞ is in the first set of `ofFun (· + 1)`. In ℕ∞'s own order the step raises, and that datum puts
-- `0`, ⊥ of ℕ∞, in the first set, not ⊤.
example : (ZeroParadox.Motion.ofFun (fun x : ℕ∞ => x + 1)).reverse.SelfOnlyAt ⊤ :=
  ZeroParadox.Motion.selfOnlyAt_of_step_self
    (fun b c (hb : ⊤ = b + 1) (hc : ⊤ = c + 1) => by
      have hb' := (WithTop.add_eq_top.1 hb.symm).resolve_right (by decide)
      have hc' := (WithTop.add_eq_top.1 hc.symm).resolve_right (by decide)
      rw [hb', hc'])
    (show (⊤ : ℕ∞) = ⊤ + 1 from rfl)
#check @ZeroParadox.Motion.eq_of_step_to_ofFun_iff_iterate -- Statement: for a function step, `y` is in the first set iff no start other than `y` reaches `y` by iterating; both directions
-- Statement: member: doubling on ℚ_[2] puts `0` in the first set and steps `0` to itself only.
example : (∀ a, (ZeroParadox.Motion.ofFun (fun x : ℚ_[2] => 2 * x)).step a 0 → a = 0) ∧
    (ZeroParadox.Motion.ofFun (fun x : ℚ_[2] => 2 * x)).SelfOnlyAt 0 :=
  ⟨fun a (ha : (0 : ℚ_[2]) = 2 * a) => (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero,
   (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 (mul_zero 2)⟩
-- Statement: CONTROL: `Nat.pred` steps `1` to `0` and steps `0` to itself only, so `0` is reached
-- from another start and is not in the first set.
example : ¬ (∀ a, (ZeroParadox.Motion.ofFun Nat.pred).step a 0 → a = 0) ∧
    (ZeroParadox.Motion.ofFun Nat.pred).SelfOnlyAt 0 :=
  ⟨fun h => absurd (h 1 rfl) (by decide), (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 rfl⟩
-- Reading: the first trap set says no other start ever gets in, the second that no step leaves to
-- elsewhere; read on runs, each forbids a "bad thing" (safety, Alpern and Schneider, "Defining
-- Liveness", IPL 21 (1985), p. 181). `Arrives` implies that every run passes through `y`
-- (`exists_run_eq_of_arrives`; the converse holds given a step at every point other than `y`,
-- `arrives_of_forall_run`), a "good thing" eventually happening (liveness, p. 182, termination among
-- their examples); theirs are properties of executions, these of a step relation. Arrival is a die
-- notion; approach in a metric (`Tendsto`) is not, since a motion carries no topology.
#check @ZeroParadox.Motion.Arrives              -- Statement: `x = y`, or `x` has a step and every step from `x` lands at a point arriving at `y`
-- Reading (cited, not claimed): `Arrives y` is CTL's inevitability `AF` at the proposition "is `y`"
-- (Clarke and Emerson, "Design and Synthesis of Synchronization Skeletons Using Branching Time
-- Temporal Logic", Logics of Programs, LNCS 131 (1981), p. 55: `AFf₁ ≡ A[true U f₁]`, "for every
-- path, there exists a state on the path at which f₁ holds", a path being an infinite sequence of
-- states), in Emerson's least-fixpoint form `AFP = μZ.P ∨ AXZ` ("Temporal and Modal Logic", Handbook
-- of Theoretical Computer Science vol. B (1990); § 8.4 "Fixpoint Logics" in the author's preprint, the
-- published chapter's numbering not checked); the `next` clause's `∃ b, M.step x b` is the source's
-- totality requirement ("we require that A be total", p. 55) carried inside the predicate, since a
-- motion's step need not be total; with a step at every point other than `y` and `DecidableEq`,
-- arrival is the path form, every run from `x` visits `y` (`arrives_iff_forall_run`). Delta: theirs
-- are properties of executions, these of a step relation. Neighbour: Stefanescu, Ciobaca, Mereuta,
-- Moore, Rosu and Serbanuta, "All-Path Reachability Logic", LMCS 15(2) 2019, Lemma 8.6, stated one
-- way (`→`) at p. 5:17 and used as the iff at p. 5:19, `coreach(φ) ↔ φ ∨ (∃c' step(c, c') ∧
-- ∀c' (step(c, c') → coreach(φ)[c'/□]))`, the `next` clause's unfolding stated for a step that need
-- not be total; delta: their `coreach` (Fig. 5, p. 5:15) ranges over complete paths, each ending at a
-- configuration with no step, so a diverging run does not obstruct it, where `Arrives` is the least
-- fixed point of that unfolding and every run from `x` visits `y` (`exists_run_eq_of_arrives`); that
-- split is named in Buruiana and Ciobaca, "Reducing Total Correctness to Partial Correctness by a
-- Transformation of the Language Semantics", WPTE 2018, EPTCS 289 (2019), Def. 2.6 (complete paths,
-- p. 7) against Def. 3.2 (complete or diverging executions, p. 8).
#check @ZeroParadox.Motion.reflTransGen_of_arrives -- Statement: arrival gives a path of steps (Mathlib `ReflTransGen`)
#check @ZeroParadox.Motion.exists_run_eq_of_arrives -- Statement: arrival from `x` gives that every run starting at `x` visits `y`
#check @ZeroParadox.Motion.arrives_ofFun_iff    -- Statement: in `ofFun g`, arrival is `g^[n] x = y` for some `n`
#check @ZeroParadox.Motion.arrives_ofFun_iff_reflTransGen -- Statement: in `ofFun g`, arrival iff a path of steps
-- Statement: CONTROL, off function steps a path does not give arrival: on `Bool` with the always-true
-- step, `true` reaches `false` in one step, and `true` does not arrive at `false` (the run staying at
-- `true` never visits it).
example : let M := ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun _ _ => True)
    Relation.ReflTransGen M.step true false ∧ ¬ M.Arrives false true := by
  intro M
  refine ⟨Relation.ReflTransGen.single trivial, fun h => ?_⟩
  have key : ∀ x, M.Arrives false x → x = false := by
    intro x hx
    induction hx with
    | here => rfl
    | next _ _ ih => exact ih _ trivial
  exact absurd (key true h) (by decide)
#check @ZeroParadox.Motion.eq_of_reflTransGen_of_noEntry -- Statement: if every step into `y` starts at `y`, every path ending at `y` starts at `y`
#check @ZeroParadox.Motion.not_noEntry_of_arrives -- Statement: in any motion, if some `x ≠ y` arrives at `y`, some step into `y` starts elsewhere
#check @ZeroParadox.Motion.noEntry_ofFun_iff_arrives -- Statement: in `ofFun g`, every step into `y` starts at `y` iff every point arriving at `y` is `y`
-- Statement: CONTROL, the `←` direction fails off function steps: on `Bool` with the always-true
-- step, every point arriving at `false` is `false`, and `true` steps into `false`.
example : let M := ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun _ _ => True)
    (∀ x, M.Arrives false x → x = false) ∧ ¬ ∀ a, M.step a false → a = false := by
  intro M
  refine ⟨fun x hx => ?_, fun h => absurd (h true trivial) (by decide)⟩
  induction hx with
  | here => rfl
  | next _ _ ih => exact ih _ trivial
#check @ZeroParadox.Motion.eq_of_noEntry_of_forall_arrives -- Statement: in `ofFun g`, if every step into `y` starts at `y` and every point arrives at `y`, every point is `y`
#check @ZeroParadox.Motion.acc_of_arrives       -- Statement: arrival at `y` gives Mathlib's `Acc` for the step with `y` removed as a source
#check @ZeroParadox.Motion.arrives_of_acc       -- Statement: and back, with `DecidableEq` and a step at every point other than `y`
#check @ZeroParadox.Motion.arrives_of_forall_run -- Statement: with `DecidableEq` and a step at every point other than `y`, if every run from `x` visits `y` then `x` arrives at `y`; `[propext, Classical.choice, Quot.sound]`, through Mathlib's `not_acc_iff_exists_descending_chain`, where the forward half `exists_run_eq_of_arrives` is axiom-free; the control in `ZeroParadox/Die.lean` § XVI drops the step hypothesis
#check @ZeroParadox.Motion.arrives_iff_forall_run -- Statement: both directions under that hypothesis
#check @ZeroParadox.Motion.reach_and_stay_iff   -- Statement: in `ofFun g`, an orbit eventually constant at `y` iff arrival at `y` and `SelfOnlyAt y`
#check @ZeroParadox.Motion.not_arrives_of_stageClosure -- Statement: no point of a run's stage closure is arrived at from the run's first stage
-- Statement: members: `Nat.pred` (`pred_orbit_reaches_floor`) and every self-map of ℕ strictly
-- lowering off 0 (`descent_with_strict_steps_reaches_floor`) arrive at 0 from every start
-- (`ZeroParadox/Order/WellFoundedObstruct.lean`).
example (n : ℕ) : (ZeroParadox.Motion.ofFun Nat.pred).Arrives 0 n := by
  obtain ⟨N, hN⟩ := ZeroParadox.pred_orbit_reaches_floor n
  exact (ZeroParadox.Motion.arrives_ofFun_iff _ _ _).2 ⟨N, hN N le_rfl⟩
example (g : ℕ → ℕ) (hg : ∀ k, k ≠ 0 → g k < k) (x : ℕ) :
    (ZeroParadox.Motion.ofFun g).Arrives 0 x := by
  obtain ⟨N, hN⟩ := ZeroParadox.descent_with_strict_steps_reaches_floor (fun k => g^[k] x)
    (fun k hk => by
      show g^[k + 1] x < g^[k] x
      rw [Function.iterate_succ_apply']
      exact hg _ hk)
  exact (ZeroParadox.Motion.arrives_ofFun_iff _ _ _).2 ⟨N, hN⟩
-- Statement: a relation member with many successors: OVER "to any smaller number" on ℕ arrives at 0
-- from every start, through `Acc` of `<` (`arrives_of_acc`).
example (x : ℕ) :
    (ZeroParadox.Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl) (fun a b => b < a)).Arrives 0 x :=
  ZeroParadox.Motion.arrives_of_acc (fun _ ha => ⟨0, Nat.pos_of_ne_zero ha⟩)
    (Subrelation.accessible (fun {_ _} h => h.2) (wellFounded_lt.apply x))
-- Statement: approach is not arrival: on ℚ_[2], for `x ≠ 0` the doubling orbit tends to 0
-- (`doubling_orbit_tendsto_zero`), `x` does not arrive at 0 (`padic_orbit_never_reaches_zero`), and
-- every step into 0 starts at 0.
example (x : ℚ_[2]) (hx : x ≠ 0) :
    Filter.Tendsto (fun n : ℕ => (2 : ℚ_[2]) ^ n * x) Filter.atTop (nhds 0) ∧
    ¬ (ZeroParadox.Motion.ofFun (fun z : ℚ_[2] => 2 * z)).Arrives 0 x ∧
    (∀ a, (ZeroParadox.Motion.ofFun (fun z : ℚ_[2] => 2 * z)).step a 0 → a = 0) := by
  have hit : ∀ n : ℕ, (fun z : ℚ_[2] => 2 * z)^[n] x = (2 : ℚ_[2]) ^ n * x := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_assoc]
  refine ⟨ZeroParadox.doubling_orbit_tendsto_zero x, fun h => ?_,
    fun a (ha : (0 : ℚ_[2]) = 2 * a) => (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero⟩
  obtain ⟨n, hn⟩ := (ZeroParadox.Motion.arrives_ofFun_iff _ _ _).1 h
  rw [hit] at hn
  exact ZeroParadox.padic_orbit_never_reaches_zero x hx n hn
-- Statement: the tower seeded at 0, ⊥ of `Ordinal`, closes at ε₀ (`ordinalTowerMotion_stageClosure`),
-- and 0 does not arrive at ε₀.
example : ¬ ZeroParadox.ordinalTowerMotion.{0}.Arrives (Ordinal.epsilon 0) 0 :=
  ZeroParadox.Motion.not_arrives_of_stageClosure
    (s := fun n => (fun a : Ordinal.{0} => Ordinal.omega0 ^ a)^[n] 0)
    ZeroParadox.ordinalTowerMotion_isRun ZeroParadox.ordinalTowerMotion_stageClosure (Part.mem_some _)
-- Reading: three cells kept apart: finite arrival (`Nat.pred`), stage closure (the tower), and metric
-- approach (doubling on ℚ_[2]); the third is stated with `Tendsto` beside the die.
#check @ZeroParadox.Motion.fanIn_ofFun_of_arrives -- Statement: with `DecidableEq`, if `g y = y` and some `x ≠ y` arrives at `y`, `y` has fan-in
#check @ZeroParadox.Motion.eq_of_arrives_ofFun_of_injective -- Statement: if `g` is one-to-one and `g y = y`, every point arriving at `y` is `y`
#check @ZeroParadox.Motion.arrives_of_reflTransGen_of_det -- Statement: if every point has at most one successor, a path of steps gives arrival
-- Reading: `zeroStar_reaches_not_arrives` (§ XX) is the CONTROL: node 0 of `zeroStar` also steps to
-- itself, so a path to node 1 does not give arrival there.
#check @ZeroParadox.Motion.noEntry_iff_noReach   -- Statement: in any motion, every step into `y` starts at `y` iff every path ending at `y` starts at `y`
-- Reading: halting as arrival, in `ZeroParadox/Computability/Occurrence.lean` § VIII and § VIII-b.
#check @ZeroParadox.runMotion_arrives_iff_reaches -- Statement: in the run motion, arrival iff reachability (`StateTransition.Reaches`)
#check @ZeroParadox.mem_eval_iff_arrives_noStepAt -- Statement: `b` is a value of the run from `a` iff `a` arrives at `b` and `b` has no step
#check @ZeroParadox.eval_dom_iff_arrives_noStepAt -- Statement: the run from `a` halts iff `a` arrives at a configuration with no step
#check @ZeroParadox.runMotion_noEntry_iff_arrives -- Statement: in the run motion, every step into `y` starts at `y` iff every configuration arriving at `y` is `y`
#check @ZeroParadox.runMotion_selfOnlyAt_of_step_self -- Statement: a configuration stepping to itself steps to itself only
#check @ZeroParadox.runMotion_not_step_self_and_leavesAt -- Statement: no configuration steps to itself and elsewhere
-- Reading: both rest on `runMotion_det`, at most one successor: the step is a function, and a
-- self-loop alone gives neither (§ XX's `Fin 3` relation).
#check @ZeroParadox.clockStep_primrec            -- Statement: the clock machine's step on `(code, input, budget)` is primitive recursive
#check @ZeroParadox.clock_arrival_iff            -- Statement: `(c, n, 0)` arrives at a configuration with no step iff `Occurs c n`
#check @ZeroParadox.clock_arrival_undecidable    -- Statement: as a predicate of the code, that arrival is not a `ComputablePred`
#check @ZeroParadox.clock_arrival_re_not_coRe    -- Statement: it is an `REPred`, and its negation is not
#check @ZeroParadox.clock_start_noEntry          -- Statement: no step enters `(c, n, 0)`, for every code
-- Reading: on the clock machine the arrival (liveness) cell at `(c, n, 0)` is undecidable over codes,
-- and the "no entry from elsewhere" (safety) cell at the same configurations holds for every code.
-- Whether the safety cell is decidable on other machines or configurations is not stated.

/-! ### § XVII. Maps of motions: Mathlib's `RelHom` on the steps -/
#check @RelHom                                   -- Statement: Mathlib, a map `f` with `r a b → s (f a) (f b)`; on two motions' steps, a step-preserving map
#check @ZeroParadox.Motion.semiconj_iff_exists_relHom -- Statement: `c` semiconjugates `A` to `B` iff it is such a map from `ofFun A` to `ofFun B`; both directions
#check @ZeroParadox.Motion.isEmpty_relHom_of_step_self -- Statement: a self-step goes to a self-step, so there is no such map from a motion with one into a motion with none
#check @ZeroParadox.Motion.selfOnlyAt_relHom     -- Statement: if `y` steps to itself only and its image has at most one successor, the image steps to itself only
-- Reading: the last transfer rests on the target's single-valuedness (its premise), not on the
-- self-loop: § XI's always-true relation on `Bool` has a self-step at `true` that is no `SelfOnlyAt`.
-- Statement: `partialAddOne_no_semiconj` re-derived: `partialAddOne` fixes `[]`, add one on ℤ_[2]
-- fixes nothing, so no `c` semiconjugates the first to the second.
example : ¬ ∃ c : List Bool → ℤ_[2], Function.Semiconj c ZeroParadox.partialAddOne (· + 1) := by
  rintro ⟨c, hc⟩
  obtain ⟨φ, -⟩ := (ZeroParadox.Motion.semiconj_iff_exists_relHom _ _ c).1 hc
  exact (ZeroParadox.Motion.isEmpty_relHom_of_step_self
    (M := ZeroParadox.Motion.ofFun ZeroParadox.partialAddOne)
    (N := ZeroParadox.Motion.ofFun (· + (1 : ℤ_[2]))) (y := [])
    ((ZeroParadox.partialAddOne_fixed_iff []).2 rfl).symm
    (fun t (ht : t = t + 1) => succ_ne_self t ht.symm)).false φ
-- Statement: CONTROL, stepping elsewhere is not carried: the constant map from `ofFun not` on `Bool`
-- to `ofFun id` on `Unit` preserves steps, `true` steps elsewhere, and its image steps to itself only.
example : ∃ φ : (ZeroParadox.Motion.ofFun (fun b : Bool => !b)).step →r
      (ZeroParadox.Motion.ofFun (id : Unit → Unit)).step,
    (ZeroParadox.Motion.ofFun (fun b : Bool => !b)).LeavesAt true ∧
      (ZeroParadox.Motion.ofFun (id : Unit → Unit)).SelfOnlyAt (φ true) :=
  ⟨⟨fun _ => (), fun _ => rfl⟩, ⟨false, rfl, by decide⟩, ⟨rfl, fun _ _ => rfl⟩⟩
-- Statement: complement on bit tapes (`compl_semiconj_tapeCons`) is such a map from prepending
-- `false` to prepending `true`; it sends ⊥ of `ℕ → Bool`, which steps to itself only in the first,
-- to ⊤, which steps to itself only in the second.
example : ∃ φ : (ZeroParadox.Motion.ofFun (ZeroParadox.tapeCons false)).step →r
      (ZeroParadox.Motion.ofFun (ZeroParadox.tapeCons true)).step,
    ⇑φ = compl ∧ (ZeroParadox.Motion.ofFun (ZeroParadox.tapeCons false)).SelfOnlyAt ⊥ ∧
      (ZeroParadox.Motion.ofFun (ZeroParadox.tapeCons true)).SelfOnlyAt (φ ⊥) ∧ φ ⊥ = ⊤ := by
  obtain ⟨φ, hφ⟩ := (ZeroParadox.Motion.semiconj_iff_exists_relHom _ _ _).1
    ZeroParadox.compl_semiconj_tapeCons
  refine ⟨φ, hφ, (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 (ZeroParadox.tapeCons_const false),
    (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 ?_, by rw [hφ]; exact compl_bot⟩
  rw [hφ]
  show ZeroParadox.tapeCons true (⊥ : ℕ → Bool)ᶜ = (⊥ : ℕ → Bool)ᶜ
  rw [compl_bot]
  exact ZeroParadox.tapeCons_const true
-- Reading: a `RelHom` carries OVER only. Adding UP gives two notions, strict (the square commutes in
-- Par) and lax (it commutes up to the restriction order, Cockett and Lack, TCS 270 (2002), § 2.1.4,
-- p. 230); adding the back clause on OVER gives Rutten's homomorphism of transition systems (TCS 249
-- (2000), p. 10). Each premise below needs its own combination; none of the three is the map of
-- motions.
#check @ZeroParadox.Motion.UpLax                  -- Statement: every UP value goes to an UP value
#check @ZeroParadox.Motion.UpStrict               -- Statement: UP at `f x` is UP at `x` mapped by `f`
#check @ZeroParadox.Motion.StepBack               -- Statement: every step out of `f a` is the image of a step out of `a`; Mathlib's `Relation.Fibration` of the reversed steps
#check @ZeroParadox.Motion.Hom                    -- Statement: steps to steps, with `UpStrict`
#check @ZeroParadox.Motion.LaxHom                 -- Statement: steps to steps, with `UpLax`
#check @ZeroParadox.Motion.upLax_iff_le           -- Statement: `UpLax` iff `(M.up x).map f ≤ N.up (f x)` in `Part`'s order, at every `x`
#check @ZeroParadox.Motion.upStrict_iff           -- Statement: strict iff lax and UP-definedness reflected
#check @ZeroParadox.Motion.upStrict_of_upLax_of_upTotal -- Statement: lax ⇒ strict when the source UP is total
#check @ZeroParadox.Motion.Hom.comp_assoc         -- Statement: strict maps compose associatively, with `Hom.id` as unit (`Hom.id_comp`, `Hom.comp_id`), by `rfl`
#check @ZeroParadox.Motion.Hom.reverse            -- Statement: a strict map is a strict map of the reverses; involutive (`Hom.reverse_reverse`)
#check @ZeroParadox.Motion.semiconj_iff_exists_hom -- Statement: on `ofFun` motions, strict maps are the semiconjugacies
#check @ZeroParadox.Motion.stepBack_ofFun         -- Statement: and they have the back clause
-- Statement: transfers, each with the hypothesis it needs: forward along any lax map, landings
-- (`LaxHom.isLanding`, `hasLanding`, `overAtLanding`); forward, one-to-one, the corner, loop, climb,
-- elbow, stepping elsewhere and fan-in (`LaxHom.corner`, `loop`, `climb`, `elbow`, `leavesAt`,
-- `fanIn`); forward, onto, UP totality (`LaxHom.upTotal`); forward, back clause, no step, a step to
-- itself only, arrival (`LaxHom.noStepAt`, `selfOnlyAt`, `arrives`); backward, no hypothesis, no step
-- (`LaxHom.noStepAt_of_image`); backward, back clause, stepping elsewhere (`LaxHom.leavesAt_of_image`),
-- and with one-to-one a step to itself only (`LaxHom.selfOnlyAt_of_image`); backward, strict, UP
-- totality (`Hom.upTotal_of`), and with one-to-one landings (`Hom.isLanding_of_image`). The NO-GO
-- `example`s after them in `ZeroParadox/Die.lean` § XIX refute the forward corner, climb and arrival
-- and the backward landing without their hypotheses.
#check @ZeroParadox.Motion.LaxHom.corner         -- Statement: along a one-to-one lax map the corner is carried forward
#check @ZeroParadox.Motion.LaxHom.selfOnlyAt     -- Statement: along a lax map with the back clause a step to itself only is carried forward
#check @ZeroParadox.Motion.Hom.isLanding_of_image -- Statement: along a one-to-one strict map landings are reflected
-- Statement: a cross-face strict map: `towerToZp2Hom` on the steps, with identity UP on both sides,
-- is a strict map from `ofFun omegaPowNote` on `NONote` to `ofFun towerImageStep` on ℤ_[2], and
-- `towerToOrdHom` one into `ofFun (ω^·)` on `Ordinal`. Reading: with identity UP the UP square holds for
-- any map, so these carry content on OVER only.
example : ∃ φ : ZeroParadox.Motion.Hom (ZeroParadox.Motion.ofFun ZeroParadox.omegaPowNote)
    (ZeroParadox.Motion.ofFun ZeroParadox.towerImageStep), φ.toFun = ZeroParadox.towerToZp2Hom :=
  ⟨ZeroParadox.Motion.ofRelHomIdUp (fun _ => rfl) (fun _ => rfl) ZeroParadox.towerToZp2Hom, rfl⟩
example : ∃ φ : ZeroParadox.Motion.Hom (ZeroParadox.Motion.ofFun ZeroParadox.omegaPowNote)
    (ZeroParadox.Motion.ofFun (fun a : Ordinal => Ordinal.omega0 ^ a)),
    φ.toFun = ZeroParadox.towerToOrdHom :=
  ⟨ZeroParadox.Motion.ofRelHomIdUp (fun _ => rfl) (fun _ => rfl) ZeroParadox.towerToOrdHom, rfl⟩
-- Statement: a cross-face map with a non-identity UP: from the run motion of `f : σ → Option σ` to
-- `MachinePhase` (UP constant `c₀`, OVER from `c₁` to every phase), halted configurations to `c₀` and
-- the others to `c₁`, is a lax map; and it is strict iff UP of the run motion is total, that is, iff
-- every configuration's run halts; both directions. Reading: sending halted configurations to `c₀` is
-- a choice of labelling.
example {σ : Type} (f : σ → Option σ) :
    let ph : σ → ZeroParadox.MachinePhase := fun c => match f c with
      | none => ZeroParadox.c₀
      | some _ => ZeroParadox.c₁
    let T := ZeroParadox.Motion.ofTotal (fun _ : ZeroParadox.MachinePhase => ZeroParadox.c₀)
      (fun _ => rfl) (fun a _ => a = ZeroParadox.c₁)
    (∃ φ : ZeroParadox.Motion.LaxHom (ZeroParadox.runMotion f) T, φ.toFun = ph) ∧
      (ZeroParadox.Motion.UpStrict (ZeroParadox.runMotion f) T ph ↔
        (ZeroParadox.runMotion f).UpTotal) := by
  intro ph T
  have h1 : ∀ {c d : σ}, d ∈ f c → ph c = ZeroParadox.c₁ := fun {c d} h => by
    show (match f c with | none => _ | some _ => _) = _
    rw [Option.mem_def.1 h]
  have hlax : ZeroParadox.Motion.UpLax (ZeroParadox.runMotion f) T ph := fun x y hy => by
    show ph y ∈ Part.some ZeroParadox.c₀
    have h0 : f y = none := (StateTransition.mem_eval.1 hy).2
    show (match f y with | none => _ | some _ => _) ∈ _
    rw [h0]; exact Part.mem_some _
  refine ⟨⟨⟨ph, fun h => h1 h, hlax⟩, rfl⟩,
    ⟨fun h x => (ZeroParadox.Motion.upStrict_iff.1 h).2 x trivial,
     fun h => ZeroParadox.Motion.upStrict_iff.2 ⟨hlax, fun x _ => h x⟩⟩⟩
-- Statement: CONTROL: on `Unit` with `() ↦ some ()` the run diverges, so that map is not strict.
example : ¬ ZeroParadox.Motion.UpStrict (ZeroParadox.runMotion (fun _ : Unit => some ()))
    (ZeroParadox.Motion.ofTotal (fun _ : ZeroParadox.MachinePhase => ZeroParadox.c₀) (fun _ => rfl)
      (fun a _ => a = ZeroParadox.c₁)) (fun _ => ZeroParadox.c₁) := fun h => by
  have hd := (ZeroParadox.Motion.upStrict_iff.1 h).2 () trivial
  exact (ZeroParadox.runMotion_run_diverges (fun _ : Unit => some ()) (s := fun _ => ())
    (fun _ => rfl)).2 hd
-- Reading: occurrence (every run halts) appears here as strictness of a map into the two-state face.
-- Not claimed: that this map is canonical, or an identity between the machine face and `MachinePhase`.
-- Not stated in this section: maps through ℕ∞ to ℤ_[2] and `Ordinal` with UP constant at an orbit's
-- limit; that UP is a choice the corpus does not make.

/-! ### § XVIII. Views: a carrier order passed as data, and restriction -/
-- Reading: a view is an order on the carrier given as an argument, never a field of `Motion`. The
-- motion and its two trap sets mention no order; polarity, ⊥ and ⊤, and the cut depend on the view.
-- Statement: the two trap sets are the same set under any two `≤`. Reading: a typing fact, not a
-- finding: the sets take no order argument.
example {α : Type} (M : ZeroParadox.Motion α) (L₁ L₂ : LE α) :
    (letI := L₁; {y : α | ∀ a, M.step a y → a = y}) = (letI := L₂; {y : α | ∀ a, M.step a y → a = y}) ∧
    (letI := L₁; {y : α | ∀ b, M.step y b → b = y}) = (letI := L₂; {y : α | ∀ b, M.step y b → b = y}) :=
  ⟨rfl, rfl⟩
#check @ZeroParadox.Motion.stepRaises_iff_of_dual -- Statement: if `L₂` is `L₁` reversed pointwise, OVER raises under `L₂` iff it lowers under `L₁`
#check @ZeroParadox.Motion.upRaises_iff_of_dual  -- Statement: and the same for UP
#check @ZeroParadox.Motion.eq_of_step_from_of_stepLowers -- Statement: under any `≤`, if OVER lowers and `y` is the only point `≤ y`, every step out of `y` ends at `y`
#check @ZeroParadox.Motion.eq_of_step_from_of_stepRaises -- Statement: if OVER raises and `y` is the only point `≥ y`, every step out of `y` ends at `y`
#check @ZeroParadox.q2Val_le_iff_norm_le          -- Statement: on ℤ_[2], ℤ_[2]'s 0 included, `q2Val x ≤ q2Val y ↔ ‖y‖ ≤ ‖x‖`
#check @ZeroParadox.z2_two_views                  -- Statement: ℤ_[2]'s 0 is least by norm and greatest by `q2Val`; doubling lowers by norm, raises by `q2Val`, does not raise by norm; 0 is in both trap sets
-- Reading: one point at opposite ends of two mutually reverse orders, each defined on ℤ_[2] apart from
-- the other. Reading the valuation's ⊤ as the pole's ∞ is interpretation; the coincidence witness of
-- the pole stays `infinitude_forces_infinite_complexity` (`ZeroParadox/BottomCannotBe.lean` § INVERSION).
-- Statement: the same membership, every step out of 0 ends at 0, reached by two order routes: 0 the
-- only point `≤ 0` by norm with doubling lowering, and 0 the only point `≥ 0` by `q2Val` with doubling
-- raising.
example : (∀ b, (ZeroParadox.Motion.ofFun (fun x : ℤ_[2] => 2 * x)).step 0 b → b = 0) ∧
    (∀ b, (ZeroParadox.Motion.ofFun (fun x : ℤ_[2] => 2 * x)).step 0 b → b = 0) :=
  ⟨@ZeroParadox.Motion.eq_of_step_from_of_stepLowers _ _ (Preorder.lift (‖·‖ : ℤ_[2] → ℝ)).toLE
      ZeroParadox.z2_two_views.2.2.2.1 0
      (fun b (h : ‖b‖ ≤ ‖(0 : ℤ_[2])‖) => norm_le_zero_iff.mp (by simpa using h)),
   @ZeroParadox.Motion.eq_of_step_from_of_stepRaises _ _ (Preorder.lift ZeroParadox.q2Val).toLE
      ZeroParadox.z2_two_views.2.2.2.2.1 0
      (fun b (h : ZeroParadox.q2Val 0 ≤ ZeroParadox.q2Val b) =>
        ZeroParadox.q2Val_unique b (top_le_iff.mp (ZeroParadox.q2Val_bot ▸ h)))⟩
-- Statement: CONTROL: least in one order and greatest in another is had by any carrier with a least
-- point, through the order dual: `false` on `Bool`.
example : IsBot false ∧ @IsTop Bool (OrderDual.instLE Bool) false :=
  ⟨fun b => Bool.false_le b, fun b => Bool.false_le b⟩
-- Statement: CONTROL: on `Unit` one point is least and greatest in one order.
example : IsBot () ∧ IsTop () := ⟨fun _ => le_rfl, fun _ => le_rfl⟩
-- Statement: CONTROL: on ℝ doubling raises by norm, and 0 is still in both trap sets.
example : @ZeroParadox.Motion.StepRaises ℝ (ZeroParadox.Motion.ofFun (fun x : ℝ => 2 * x))
      (Preorder.lift (‖·‖ : ℝ → ℝ)).toLE ∧
    (∀ a, (ZeroParadox.Motion.ofFun (fun x : ℝ => 2 * x)).step a 0 → a = 0) ∧
    (ZeroParadox.Motion.ofFun (fun x : ℝ => 2 * x)).SelfOnlyAt 0 := by
  refine ⟨?_, fun a (ha : (0 : ℝ) = 2 * a) => (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero,
    (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 (mul_zero 2)⟩
  rintro x y rfl
  show ‖x‖ ≤ ‖(2 : ℝ) * x‖
  rw [norm_mul, Real.norm_two]; nlinarith [norm_nonneg x]
#check @ZeroParadox.sNorm                         -- Statement: the extended norm on `OnePoint ℚ_[2]`, ⊤ of `ℝ≥0∞` at `∞`
#check @ZeroParadox.sNorm_rInv                    -- Statement: `sNorm (rInv s) = (sNorm s)⁻¹` at every point
#check @ZeroParadox.rInv_reverses                 -- Statement: `rInv` reverses the order lifted along `sNorm`
#check @ZeroParadox.rInvRelIso                    -- Statement: `rInvHomeo` as a `RelIso` from that order to its reverse
#check @ZeroParadox.sphere_exchange               -- Statement: EXCHANGE: in that order 0 is least and `∞` greatest, `0 ≠ ∞`, and `rInv` swaps them; two distinct points, not the coincidence witness
#check @ZeroParadox.sphere_polarity_swap          -- Statement: for every motion on the sphere, OVER raises in the order lifted along `sNorm ∘ rInv` iff it lowers in the order lifted along `sNorm`
-- Reading: two ways to change view: read the same point in the reverse order (ℤ_[2], `z2_two_views`),
-- or move the point by an order-reversing involution (the sphere, `rInv_reverses`).
#check @ZeroParadox.Motion.UpClosed               -- Statement: every value of UP at a point of `S` lies in `S`
#check @ZeroParadox.Motion.StepClosed             -- Statement: every step from a point of `S` lands in `S`
#check @ZeroParadox.Motion.restrict               -- Statement: the motion on the subtype of an UP-closed `S`; OVER is Mathlib's `Subrel`
#check @ZeroParadox.Motion.mem_restrict_up        -- Statement: UP of the restriction is UP of the motion
#check @ZeroParadox.Motion.restrict_isLanding_iff -- Statement: a landing of the restriction is a landing lying in `S`
#check @ZeroParadox.Motion.restrict_step_iff      -- Statement: a step of the restriction is a step of the motion
#check @ZeroParadox.Motion.restrict_step_complete -- Statement: if `S` is also OVER-closed, every step from a point of `S` is a step of the restriction
#check @ZeroParadox.Motion.restrictVal            -- Statement: the inclusion of `S` is a relation embedding of steps
#check @ZeroParadox.Motion.restrictVal_up         -- Statement: and UP commutes with it
#check @ZeroParadox.Motion.restrictInclusion      -- Statement: for `T ⊆ S`, `Set.inclusion` is a relation embedding of the restricted steps
#check @ZeroParadox.Motion.restrictInclusion_up   -- Statement: and UP commutes with it
#check @ZeroParadox.Motion.upClosed_Ici           -- Statement: in a preorder, if UP raises, `Set.Ici a` is UP-closed
#check @ZeroParadox.Motion.stepClosed_Ici         -- Statement: if OVER raises, `Set.Ici a` is OVER-closed
#check @ZeroParadox.Motion.restrict_stepRaises_Ici -- Statement: if OVER raises, OVER of the restriction to `Set.Ici a` raises
-- Statement: CONTROL: on ℕ, UP constant 0 is not UP-closed on `Set.Ici 1`.
example : ¬ (ZeroParadox.Motion.ofTotal (fun _ : ℕ => 0) (fun _ => rfl) (fun _ _ => False)).UpClosed
    (Set.Ici 1) :=
  fun h => absurd (h 1 (Set.mem_Ici.2 le_rfl) 0 (Part.mem_some _)) (by simp)
-- Statement: CONTROL: `∅` is UP-closed for every motion, so being a restriction is uninformative.
example {α : Type} (M : ZeroParadox.Motion α) : M.UpClosed ∅ := fun _ hx => hx.elim
-- Statement: CONTROL: the order trap at a least point needs OVER raising: `ofFun Nat.pred` restricted
-- to `Set.Ici 3` steps 4 into 3, the least point there.
example : ∃ h : (ZeroParadox.Motion.ofFun Nat.pred).UpClosed (Set.Ici 3),
    ((ZeroParadox.Motion.ofFun Nat.pred).restrict (Set.Ici 3) h).step ⟨4, by decide⟩
      ⟨3, Set.mem_Ici.2 le_rfl⟩ ∧ IsBot (⟨3, Set.mem_Ici.2 le_rfl⟩ : Set.Ici 3) ∧
      (⟨4, by decide⟩ : Set.Ici 3) ≠ ⟨3, Set.mem_Ici.2 le_rfl⟩ :=
  ⟨fun x hx y hy => (Part.mem_some_iff.1 hy) ▸ hx, show (3 : ℕ) = Nat.pred 4 from rfl,
   fun x => x.2, fun h => absurd (congrArg Subtype.val h) (show (4 : ℕ) ≠ 3 by decide)⟩
#check @ZeroParadox.ordinalView                   -- Statement: `ordinalSuccMotion` restricted to `Set.Ici` of the `n`-th corner iterate from 0
#check @ZeroParadox.ordinalView_bot_isLanding     -- Statement: ⊥ of view `n + 1` is a landing there
#check @ZeroParadox.ordinalView_zero_bot_not_isLanding -- Statement: ⊥ of view 0, which is 0, ⊥ of `Ordinal`, is not a landing there
#check @ZeroParadox.ordinalView_zero_least_landing -- Statement: every landing of view 0 is at or above ε₀
-- Statement: and ε₀ is a landing of view 0, so it is the least landing there.
example : (ZeroParadox.ordinalView.{0} 0).IsLanding ⟨Ordinal.epsilon 0, by simp⟩ := by
  rw [ZeroParadox.ordinalView, ZeroParadox.Motion.restrict_isLanding_iff]
  show _ ∈ Part.some _
  rw [Part.mem_some_iff]
  exact (Ordinal.nfp_eq_self (Ordinal.omega0_opow_epsilon 0)).symm
-- Statement: the corner composite sends ⊥ of view `n` to ⊥ of view `n + 1`.
example (n : ℕ) : ZeroParadox.ordinalCornerStep
      ((⊥ : Set.Ici (ZeroParadox.ordinalCornerStep^[n] (0 : Ordinal.{u}))) : Ordinal.{u}) =
    ((⊥ : Set.Ici (ZeroParadox.ordinalCornerStep^[n + 1] (0 : Ordinal.{u}))) : Ordinal.{u}) :=
  (Function.iterate_succ_apply' _ _ _).symm
-- Reading: ε₀ is ⊥ of view 1, `Set.Ici ε₀`, and in view 0 it is the least landing, not ⊥ (⊥ of view 0
-- is 0, `epsilon0_ne_bot`). That view `n + 1`'s ⊥ is the bottom the snap-arc returns to is a commitment;
-- `t_iz_limit_is_new_null` is the role half only.
#check @ZeroParadox.ordinalView_bot_noEntry       -- Statement: every step of view `n` into its ⊥ starts at its ⊥
#check @ZeroParadox.ordinalView_next_bot_noEntry  -- Statement: the `n + 1`-th iterate, as an element of `ordinalView n`'s carrier, is not its ⊥, and every step into it starts at it
-- Reading: so membership in the first trap set does not pick out ⊥ of a view: no ordinal steps to 0 or
-- to an ε-number (`not_step_into_ordinalCornerStep_iterate` and the `example` after it), and the set
-- holds them all.
#check @ZeroParadox.not_step_into_ordinalCornerStep_iterate -- Statement: no ordinal steps under `ordinalSuccMotion` to a corner iterate from 0
-- Statement: nor to any ε-number `Ordinal.epsilon o`.
example (o a : Ordinal.{u}) : ¬ ZeroParadox.ordinalSuccMotion.step a (Ordinal.epsilon o) := by
  intro h
  have h' : Ordinal.epsilon o = Order.succ a := h
  have hf := Ordinal.omega0_opow_epsilon o
  rw [h'] at hf
  exact ZeroParadox.omega0_opow_succ_ne a hf
#check @ZeroParadox.ordinalView_bot_leavesAt      -- Statement: ⊥ of view `n` steps elsewhere, to its successor
#check @ZeroParadox.ordinalViewInclusion          -- Statement: view `n + 1`'s steps embed in view `n`'s by `Set.inclusion`
#check @ZeroParadox.ordinalViewInclusion_up       -- Statement: and UP commutes with that embedding
#check @ZeroParadox.ordinalViewInclusion_bot_ne   -- Statement: the embedding does not send ⊥ of view `n + 1` to ⊥ of view `n`
-- Statement: on `Option σ` with OVER `Option.map g` (UP the identity), `none` is in both trap sets with
-- no order used; for `g` with `x ≤ g x`, OVER raises in the `WithBot` order and in the `WithTop` order,
-- and the `WithBot` order gives the first set's membership of `none`, the `WithTop` order the second's.
example {σ : Type} [PartialOrder σ] (g : σ → σ) (hg : ∀ x, x ≤ g x) :
    let M := ZeroParadox.Motion.ofTotal (id : Option σ → Option σ) (fun _ => rfl)
                (fun a b => b = Option.map g a)
    ((∀ a, M.step a none → a = none) ∧ (∀ b, M.step none b → b = none)) ∧
    (∀ a : WithBot σ, M.step a (⊥ : WithBot σ) → a = ⊥) ∧
      (∀ b : WithTop σ, M.step (⊤ : WithTop σ) b → b = ⊤) := by
  intro M
  have hb : @ZeroParadox.Motion.StepRaises (WithBot σ) M _ := by
    rintro a b rfl
    rcases a with _ | x
    · exact le_rfl
    · exact WithBot.coe_le_coe.2 (hg x)
  have ht : @ZeroParadox.Motion.StepRaises (WithTop σ) M _ := by
    rintro a b rfl
    rcases a with _ | x
    · exact le_rfl
    · exact WithTop.coe_le_coe.2 (hg x)
  refine ⟨⟨fun a ha => ?_, fun _ hb => hb⟩, ZeroParadox.Motion.eq_bot_of_step_to_bot hb,
    ZeroParadox.Motion.eq_bot_of_step_from_bot (α := (WithTop σ)ᵒᵈ) (M := M) ht⟩
  change none = Option.map g a at ha
  rcases a with _ | x
  · rfl
  · exact nomatch ha
-- Statement: CONTROL: with `g = succ` on ℕ, OVER lowers in neither order, so neither order's route
-- reaches the other membership.
example : let M := ZeroParadox.Motion.ofTotal (id : Option ℕ → Option ℕ) (fun _ => rfl)
                (fun a b => b = Option.map Nat.succ a)
    ¬ @ZeroParadox.Motion.StepLowers (WithBot ℕ) M _ ∧ ¬ @ZeroParadox.Motion.StepLowers (WithTop ℕ) M _ :=
  ⟨fun h => absurd (h (some 0) (some 1) rfl) (by decide),
   fun h => absurd (h (some 0) (some 1) rfl) (by decide)⟩
-- Statement: CONTROL, a motion moving `none`: OVER `none ↦ some 0`, `some n ↦ some (n + 1)` raises in
-- the `WithBot` order and neither raises nor lowers in the `WithTop` order; `none` is in the first set
-- and not in the second.
example : let M := ZeroParadox.Motion.ofTotal (id : Option ℕ → Option ℕ) (fun _ => rfl)
                (fun a b => b = some (a.elim 0 Nat.succ))
    @ZeroParadox.Motion.StepRaises (WithBot ℕ) M _ ∧ ¬ @ZeroParadox.Motion.StepRaises (WithTop ℕ) M _ ∧
      ¬ @ZeroParadox.Motion.StepLowers (WithTop ℕ) M _ ∧
      (∀ a, M.step a none → a = none) ∧ ¬ (∀ b, M.step none b → b = none) := by
  intro M
  refine ⟨?_, fun h => absurd (h none (some 0) rfl) (by decide),
    fun h => absurd (h (some 0) (some 1) rfl) (by decide), fun a ha => ?_,
    fun h => absurd (h (some 0) rfl) (by decide)⟩
  · rintro a b rfl
    rcases a with _ | n
    · exact bot_le
    · exact WithBot.coe_le_coe.2 (Nat.le_succ n)
  · change none = some _ at ha; exact nomatch ha

/-! ### § XIX. Two points and their views: the four corners, the tower span, the ends of a view -/
#check @ZeroParadox.Pole.cornerZero_cells        -- Statement: the cells of `ofFun cornerZero` at `zero` and `infty`: trap sets, fan-in, arrival
#check @ZeroParadox.Pole.cornerInfty_cells       -- Statement: the same cells with `zero` and `infty` exchanged
#check @ZeroParadox.Pole.cornerId_cells          -- Statement: in `ofFun cornerId` every point steps to itself only and is in both trap sets
#check @ZeroParadox.Pole.swap_cells              -- Statement: in `ofFun swap` every point steps elsewhere and neither trap set has a member
#check @ZeroParadox.Pole.eq_of_selfOnlyAt_iff    -- Statement: on `Pole`, two self-maps with the same points stepping to themselves only are equal
#check @ZeroParadox.Pole.corner_of_selfOnlyAt    -- Statement: that set names the corner
-- Statement: CONTROL, the classification is a two-point fact: on `Fin 3`, `i ↦ i + 1` and `i ↦ i + 2`
-- differ, and in both motions every point steps elsewhere, no point has fan-in, and every point
-- arrives at every point.
example : (fun i : Fin 3 => i + 1) ≠ (fun i => i + 2) ∧
    (∀ y : Fin 3, (ZeroParadox.Motion.ofFun (fun i : Fin 3 => i + 1)).LeavesAt y ∧
      (ZeroParadox.Motion.ofFun (fun i : Fin 3 => i + 2)).LeavesAt y) ∧
    (∀ y : Fin 3, ¬ (ZeroParadox.Motion.ofFun (fun i : Fin 3 => i + 1)).FanIn y ∧
      ¬ (ZeroParadox.Motion.ofFun (fun i : Fin 3 => i + 2)).FanIn y) ∧
    (∀ x y : Fin 3, (ZeroParadox.Motion.ofFun (fun i : Fin 3 => i + 1)).Arrives y x ∧
      (ZeroParadox.Motion.ofFun (fun i : Fin 3 => i + 2)).Arrives y x) := by
  have i1 : Function.Injective (fun i : Fin 3 => i + 1) := fun a b h => by simpa using h
  have i2 : Function.Injective (fun i : Fin 3 => i + 2) := fun a b h => by simpa using h
  refine ⟨fun h => absurd (congrFun h 0) (by decide), fun y => ⟨?_, ?_⟩,
    fun y => ⟨ZeroParadox.Motion.not_fanIn_of_injective _ i1 (fun _ _ => Iff.rfl) y,
      ZeroParadox.Motion.not_fanIn_of_injective _ i2 (fun _ _ => Iff.rfl) y⟩, fun x y => ⟨?_, ?_⟩⟩
  · rw [ZeroParadox.Motion.leavesAt_ofFun_iff]; revert y; decide
  · rw [ZeroParadox.Motion.leavesAt_ofFun_iff]; revert y; decide
  · rw [ZeroParadox.Motion.arrives_ofFun_iff]
    have : ∀ x y : Fin 3, ∃ n : Fin 3, (fun i : Fin 3 => i + 1)^[n] x = y := by decide
    obtain ⟨n, hn⟩ := this x y
    exact ⟨n, hn⟩
  · rw [ZeroParadox.Motion.arrives_ofFun_iff]
    have : ∀ x y : Fin 3, ∃ n : Fin 3, (fun i : Fin 3 => i + 2)^[n] x = y := by decide
    obtain ⟨n, hn⟩ := this x y
    exact ⟨n, hn⟩
#check @ZeroParadox.Pole.swap_conj               -- Statement: conjugating by `swap` exchanges the two collapses and keeps `cornerId` and `swap`
#check @ZeroParadox.Pole.zeroInftyIso            -- Statement: `swap` is a relation isomorphism from the steps of `ofFun cornerZero` to those of `ofFun cornerInfty`
#check @ZeroParadox.Motion.fixed_iff_of_relIso   -- Statement: a relation isomorphism of function motions carries fixed points to fixed points, both directions
#check @ZeroParadox.Pole.three_classes           -- Statement: the motions `ofFun f` on `Pole` fall in three isomorphism classes, `cornerId`, `swap`, `cornerZero`
-- Reading: EXCHANGE, not coincidence: `zeroInftyIso` carries the distinct collapse targets `zero` and
-- `infty` onto each other, as `rInv_swaps` exchanges 0 and ∞; the coincidence witness of the pole
-- stays `infinitude_forces_infinite_complexity` (`ZeroParadox/BottomCannotBe.lean` § INVERSION).
#check @ZeroParadox.Pole.corner_polarity         -- Statement: under `poleView`, `cornerZero` lowers, `cornerInfty` raises, `cornerId` does both, `swap` neither
#check @ZeroParadox.Pole.pole_polarity_swap      -- Statement: for every motion on `Pole`, raising under `poleViewSwap` is lowering under `poleView`
#check @ZeroParadox.towerToZp2Hom                -- Statement: `cnfToZp2` maps the steps of `ofFun omegaPowNote` on `NONote` to those of `ofFun towerImageStep` on ℤ_[2]
#check @ZeroParadox.towerToOrdHom                -- Statement: `NONote.repr` maps the same steps to those of `ofFun (ω^·)` on `Ordinal`
#check @ZeroParadox.towerNONote_orbits           -- Statement: the `n`-th stage maps to `towerImageStep^[n] 0` and to `fundamentalSeq n`
#check @ZeroParadox.isEmpty_relHom_omegaPow_towerImageStep -- Statement: no relation homomorphism from the steps of `ofFun (ω^·)` on `Ordinal` to those of `ofFun towerImageStep`
-- Reading: a span `Ordinal ← NONote → ℤ_[2]`, two maps out of one motion; no map of motions runs from
-- `ofFun (ω^·)` on `Ordinal` to the image motion `ofFun towerImageStep`, and no equation between ε₀ and
-- ℤ_[2]'s 0 is stated.
#check @ZeroParadox.tower_polarity               -- Statement: stage to stage, the ordinal value and the image's valuation rise; the image's norm rises and its `q2Val` falls at stage 0, the reverse from stage 1
#check @ZeroParadox.towerImageStep_no_polarity_norm_q2Val -- Statement: under the norm view and under the `q2Val` view the image step neither raises nor lowers
#check @ZeroParadox.towerImageStep_nonzero_polarity -- Statement: on the nonzero points it lowers by norm and raises by `q2Val`
-- Reading: DRIFT. Mathlib's valuation view raises at every stage, as the ordinal does; the norm and
-- `q2Val` views, each the other reversed, change polarity at the seed.
-- Statement: CONTROL: the valuation view is not the norm view reversed: it fails at `0`, `1`.
example : ¬ ∀ x y : ℤ_[2], (x.valuation ≤ y.valuation ↔ ‖y‖ ≤ ‖x‖) := by
  intro h
  have := (h 0 1).1 (by simp)
  norm_num at this
-- Statement: CONTROL: doubling fixes ℤ_[2]'s 0 and the image step does not.
example : (2 : ℤ_[2]) * 0 = 0 ∧ ZeroParadox.towerImageStep 0 ≠ 0 :=
  ⟨mul_zero 2, ZeroParadox.towerImageStep_ne_zero 0⟩
#check @ZeroParadox.PoleEnds                     -- Statement: under a `≤`, a least point exists iff `b`, a greatest iff `t`
#check @ZeroParadox.poleEnds_unique              -- Statement: a `≤` is in at most one cell
#check @ZeroParadox.poleEnds_of_dual             -- Statement: reversing the `≤` exchanges the two answers
#check @ZeroParadox.poleEnds_dual_cells          -- Statement: the order dual exchanges `(true, false)` and `(false, true)` and keeps the other two cells
#check @ZeroParadox.ends_ne_iff_nontrivial       -- Statement: in a partial order, a least and a greatest point differ iff the carrier is `Nontrivial`
-- Statement: members: ℕ is in `(true, false)`, its order dual in `(false, true)`, ℤ in
-- `(false, false)`, `WithTop ℕ` in `(true, true)`.
example : ZeroParadox.PoleEnds ℕ true false ∧ ZeroParadox.PoleEnds ℕᵒᵈ false true ∧
    ZeroParadox.PoleEnds ℤ false false ∧ ZeroParadox.PoleEnds (WithTop ℕ) true true := by
  have hn : ZeroParadox.PoleEnds ℕ true false :=
    ⟨⟨fun _ => rfl, fun _ => ⟨0, fun _ => Nat.zero_le _⟩⟩,
      ⟨fun ⟨x, h⟩ => absurd h (not_isTop x), fun h => absurd h Bool.false_ne_true⟩⟩
  exact ⟨hn, (ZeroParadox.poleEnds_dual _ _).2 hn,
    ⟨⟨fun ⟨x, h⟩ => absurd h (not_isBot x), fun h => absurd h Bool.false_ne_true⟩,
      ⟨fun ⟨x, h⟩ => absurd h (not_isTop x), fun h => absurd h Bool.false_ne_true⟩⟩,
    ⟨⟨fun _ => rfl, fun _ => ⟨⊥, isBot_bot⟩⟩, ⟨fun _ => rfl, fun _ => ⟨⊤, isTop_top⟩⟩⟩⟩
-- Statement: CONTROLS: `PUnit` is in `(true, true)` with one point least and greatest; `Empty` is in
-- `(false, false)`, ℤ's cell; `Fin 3` is in `(true, true)` with three points.
example : ZeroParadox.PoleEnds PUnit true true ∧ (IsBot PUnit.unit ∧ IsTop PUnit.unit) ∧
    ZeroParadox.PoleEnds Empty false false ∧ ZeroParadox.PoleEnds (Fin 3) true true :=
  ⟨⟨⟨fun _ => rfl, fun _ => ⟨PUnit.unit, fun _ => le_rfl⟩⟩,
      ⟨fun _ => rfl, fun _ => ⟨PUnit.unit, fun _ => le_rfl⟩⟩⟩,
    ⟨fun _ => le_rfl, fun _ => le_rfl⟩,
    ⟨⟨fun ⟨x, _⟩ => x.elim, fun h => absurd h Bool.false_ne_true⟩,
      ⟨fun ⟨x, _⟩ => x.elim, fun h => absurd h Bool.false_ne_true⟩⟩,
    ⟨⟨fun _ => rfl, fun _ => ⟨⊥, isBot_bot⟩⟩, ⟨fun _ => rfl, fun _ => ⟨⊤, isTop_top⟩⟩⟩⟩
-- Reading: a cell counts the ends of a view, an `≤` passed as data. `(true, true)` gives two distinct
-- ends only on a `Nontrivial` carrier (`PUnit`), and identification with `Pole` needs exactly two
-- points (`Fin 3`); `Empty` and ℤ share a cell, so the cell does not see emptiness.
#check @ZeroParadox.PoleEndsInhabited            -- Statement: the carrier is inhabited iff `i`, and the `≤` is in `PoleEnds` cell `(b, t)`
#check @ZeroParadox.poleEndsInhabited_unique     -- Statement: a `≤` is in at most one such cell
#check @ZeroParadox.poleEndsInhabited_dual       -- Statement: the order dual keeps `i` and exchanges `b` and `t`
#check @ZeroParadox.poleEndsInhabited_of_end     -- Statement: a least or a greatest point gives `i = true`
-- Statement: members: `Empty` is in `(false, false, false)`, ℤ in `(true, false, false)`, `PUnit` in
-- `(true, true, true)`; `Empty` and ℤ, one `PoleEnds` cell, are in different cells here
-- (`poleEndsInhabited_unique`).
example : ZeroParadox.PoleEndsInhabited Empty false false false ∧
    ZeroParadox.PoleEndsInhabited ℤ true false false ∧
    ZeroParadox.PoleEndsInhabited PUnit true true true := by
  refine ⟨⟨⟨fun ⟨x⟩ => x.elim, fun h => absurd h Bool.false_ne_true⟩,
      ⟨fun ⟨x, _⟩ => x.elim, fun h => absurd h Bool.false_ne_true⟩,
      ⟨fun ⟨x, _⟩ => x.elim, fun h => absurd h Bool.false_ne_true⟩⟩,
    ⟨⟨fun _ => rfl, fun _ => ⟨0⟩⟩,
      ⟨fun ⟨x, h⟩ => absurd h (not_isBot x), fun h => absurd h Bool.false_ne_true⟩,
      ⟨fun ⟨x, h⟩ => absurd h (not_isTop x), fun h => absurd h Bool.false_ne_true⟩⟩,
    ⟨⟨fun _ => rfl, fun _ => ⟨PUnit.unit⟩⟩,
      ⟨fun _ => rfl, fun _ => ⟨PUnit.unit, fun _ => le_rfl⟩⟩,
      ⟨fun _ => rfl, fun _ => ⟨PUnit.unit, fun _ => le_rfl⟩⟩⟩⟩
-- Reading: `PoleEnds` alone cannot tell the empty carrier from ℤ (both in `(false, false)`); the added
-- datum `Nonempty` separates them at the level of a view's cell, and it records whether a point exists
-- and does not count points.
#check @ZeroParadox.Pole.poleView_ends           -- Statement: under `poleView`, `Pole` is in `(true, true)`, `zero` least, `infty` greatest, `zero ≠ infty`
#check @ZeroParadox.Pole.poleView_swap_ends      -- Statement: under `poleViewSwap`, `infty` least and `zero` greatest
#check @ZeroParadox.Pole.two_point_both_ends_is_poleView -- Statement: a two-point partial order with `DecidableEq`, a least and a greatest point is `Pole` under `poleView`, by an order-preserving and -reflecting equivalence
-- Statement: the order ZP-A's join induces on `MachinePhase` (`machinePhaseZPS`) is order-isomorphic
-- to `poleView` on `Pole`: `initial ↦ zero`, `running ↦ infty`, `≤` preserved and reflected.
-- Reading: the two-point order shape only, not computation; what `MachinePhase` carries
-- computationally is in `ZeroParadox/Computability/ComputationCannotBe.lean` § IV.
example : ∃ e : ZeroParadox.MachinePhase ≃ ZeroParadox.Pole,
    e ZeroParadox.MachinePhase.initial = ZeroParadox.Pole.zero ∧
    e ZeroParadox.MachinePhase.running = ZeroParadox.Pole.infty ∧
    ∀ x y, @ZeroParadox.ZPSemilattice.le ZeroParadox.MachinePhase ZeroParadox.machinePhaseZPS x y ↔
      ZeroParadox.Pole.poleView.le (e x) (e y) :=
  ⟨⟨fun x => match x with | .initial => ZeroParadox.Pole.zero | .running => ZeroParadox.Pole.infty,
    fun p => match p with | .zero => .initial | .infty => .running,
    fun x => by cases x <;> rfl, fun p => by cases p <;> rfl⟩,
   rfl, rfl, fun x y => by
    show ZeroParadox.machinePhaseZPS.join x y = y ↔ ZeroParadox.Pole.poleRank _ ≤ ZeroParadox.Pole.poleRank _
    cases x <;> cases y <;> decide⟩
-- Statement: the sphere `OnePoint ℚ_[2]` in the order lifted along `sNorm` is in `(true, true)`;
-- in the order lifted along `sNorm ∘ rInv`, ∞ is least and 0 greatest.
example : @ZeroParadox.PoleEnds ZeroParadox.Sphere (Preorder.lift ZeroParadox.sNorm).toLE true true ∧
    @IsBot ZeroParadox.Sphere (Preorder.lift (ZeroParadox.sNorm ∘ ZeroParadox.rInv)).toLE OnePoint.infty ∧
    @IsTop ZeroParadox.Sphere (Preorder.lift (ZeroParadox.sNorm ∘ ZeroParadox.rInv)).toLE
      (OnePoint.some 0) := by
  have hd : ∀ x y : ZeroParadox.Sphere, (Preorder.lift (ZeroParadox.sNorm ∘ ZeroParadox.rInv)).toLE.le x y ↔
      (Preorder.lift ZeroParadox.sNorm).toLE.le y x := fun x y => ZeroParadox.rInv_reverses x y
  exact ⟨⟨⟨fun _ => rfl, fun _ => ⟨_, ZeroParadox.sphere_exchange.1⟩⟩,
      ⟨fun _ => rfl, fun _ => ⟨_, ZeroParadox.sphere_exchange.2.1⟩⟩⟩,
    fun y => (hd _ y).2 (ZeroParadox.sphere_exchange.2.1 y),
    fun y => (hd y _).2 (ZeroParadox.sphere_exchange.1 y)⟩
-- Reading: INVERSION, an exchange: two provably distinct points trade the least and greatest roles, as
-- `sphere_exchange`; not the coincidence witness.
-- Statement: `Bool`: the `&&` view is the `||` view reversed (each `x ≤ y :↔ join x y = y`, ZP-A's
-- D1); OVER of `ofFun (fun _ => true)` raises under `||`, lowers and does not raise under `&&`;
-- `true` steps to itself only and no step enters `false`, with no order used.
example :
    let Lor : LE Bool := ⟨fun x y => (x || y) = y⟩
    let Land : LE Bool := ⟨fun x y => (x && y) = y⟩
    (∀ x y, Land.le x y ↔ Lor.le y x) ∧
      @ZeroParadox.Motion.StepRaises Bool (ZeroParadox.Motion.ofFun (fun _ => true)) Lor ∧
      @ZeroParadox.Motion.StepLowers Bool (ZeroParadox.Motion.ofFun (fun _ => true)) Land ∧
      ¬ @ZeroParadox.Motion.StepRaises Bool (ZeroParadox.Motion.ofFun (fun _ => true)) Land ∧
      (ZeroParadox.Motion.ofFun (fun _ : Bool => true)).SelfOnlyAt true ∧
      (∀ a, ¬ (ZeroParadox.Motion.ofFun (fun _ : Bool => true)).step a false) := by
  intro Lor Land
  have hd : ∀ x y, Land.le x y ↔ Lor.le y x := by
    intro x y
    show (x && y) = y ↔ (y || x) = x
    cases x <;> cases y <;> decide
  have hr : @ZeroParadox.Motion.StepRaises Bool (ZeroParadox.Motion.ofFun (fun _ => true)) Lor := by
    rintro x y rfl
    show (x || true) = true
    cases x <;> rfl
  refine ⟨hd, hr, (ZeroParadox.Motion.stepRaises_iff_of_dual Land Lor (fun x y => (hd y x).symm) _).1 hr,
    fun h => ?_, (ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ _).2 rfl, fun a h => Bool.false_ne_true h⟩
  exact absurd (show (false && true) = true from h false true rfl) (by decide)
#check @ZeroParadox.phase_views_shape            -- Statement: on `Phase`, the floor-below and floor-above views agree on `up a`, `up b`; the floor is least in one, greatest in the other
#check @ZeroParadox.phase_views_not_dual         -- Statement: the floor-above view is not the floor-below view reversed
#check @ZeroParadox.phase_cover_three_views      -- Statement: one motion raises under the floor-below view, lowers under its reverse, neither under the floor-above view; nothing steps into the floor
#check @ZeroParadox.phase_trap_route             -- Statement: under the floor-below view, a raising OVER has every step into the floor start at the floor
#check @ZeroParadox.poleEnds_phase               -- Statement: the floor-below view is in `(true, false)`, the floor-above view in `(true, true)`
-- Reading: unlike `||` and `&&` on `Bool`, the two placements are not each other's reverse: moving the
-- floor changes the cell from `(true, false)` to `(true, true)`, where a reversal gives `(false, true)`.
#check @ZeroParadox.three_overs_one_up           -- Statement: three motions on `Phase` with one UP; at the floor OVER steps to itself only, steps elsewhere, or has no step
#check @ZeroParadox.cover_overs_differ           -- Statement: the two cover relations, as OVER, differ
-- Reading: carrier, UP and view do not fix OVER; the die keeps OVER as its own field `Motion.step`.

/-! ### § XX. The drawing and the set: self-steps, ranks, accessibility -/
#check @ZeroParadox.Motion.selfOnlyAt_or_step_self_and_leavesAt -- Statement: a point stepping to itself steps to itself only, or to itself and elsewhere
#check @ZeroParadox.Motion.not_step_self_and_leavesAt_of_subsingleton -- Statement: with at most one successor at `y`, not both
#check @ZeroParadox.Motion.two_successors_of_step_self_and_leavesAt -- Statement: stepping to itself and elsewhere gives two distinct successors
#check @ZeroParadox.Motion.not_step_self_and_leavesAt_ofFun -- Statement: in `ofFun g` no point steps to itself and elsewhere
-- Reading: the obstruction is that the step is a FUNCTION (at most one successor), never the self-loop,
-- which both cells have; a relation gives the possibility of leaving, not its occurrence
-- (`zeroStar_reaches_not_arrives`). Tim's Engineer's Take in `ZeroParadox/Settheory/GraphBisim.lean`
-- says: "The quines here, and the up and over, decide whether it is a dead perfect zero or an imperfect
-- zero allowing local movement in the other direction." Our reading, not his, from these definitions:
-- stepping to itself only matches the dead perfect zero, stepping to itself and elsewhere the imperfect
-- zero.
-- Statement: CONTROLS: `ofFun id` on `Bool`: every point steps to itself only and none steps to
-- itself and elsewhere; `≠` on `Bool`: no point steps to itself and every point steps elsewhere; on
-- `Fin 3`, one relation with `0` stepping to itself only and `1` stepping to itself and to `2`.
example (x : Bool) : (ZeroParadox.Motion.ofFun (id : Bool → Bool)).SelfOnlyAt x ∧
    ¬ ((ZeroParadox.Motion.ofFun (id : Bool → Bool)).step x x ∧
      (ZeroParadox.Motion.ofFun (id : Bool → Bool)).LeavesAt x) :=
  ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ x).2 rfl,
    ZeroParadox.Motion.not_step_self_and_leavesAt_ofFun _ x⟩
example (x : Bool) :
    ¬ (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a b => a ≠ b)).step x x ∧
      (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a b => a ≠ b)).LeavesAt x :=
  ⟨fun h => h rfl, ⟨!x, show x ≠ !x from Bool.self_ne_not x, show (!x) ≠ x from Bool.not_ne_self x⟩⟩
example :
    let M := ZeroParadox.Motion.ofTotal (id : Fin 3 → Fin 3) (fun _ => rfl)
      (fun a b => (a = 0 ∧ b = 0) ∨ (a = 1 ∧ (b = 1 ∨ b = 2)))
    M.SelfOnlyAt 0 ∧ (M.step 1 1 ∧ M.LeavesAt 1) := by
  refine ⟨⟨Or.inl ⟨rfl, rfl⟩, fun b hb => ?_⟩,
    ⟨Or.inr ⟨rfl, Or.inl rfl⟩, 2, Or.inr ⟨rfl, Or.inr rfl⟩, by decide⟩⟩
  rcases hb with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h (by decide)
#check @ZeroParadox.MemGraph.memberMotion        -- Statement: UP the identity, OVER from a node to each of its members
#check @ZeroParadox.MemGraph.omegaLoop_selfOnlyAt -- Statement: in `omegaLoop` node 0 steps to itself only
#check @ZeroParadox.MemGraph.zeroStar_cells      -- Statement: in `zeroStar` node 0 steps to itself and elsewhere, node 1 has no step
#check @ZeroParadox.MemGraph.omegaPair_no_step_self -- Statement: in `omegaPair` no node steps to itself
#check @ZeroParadox.MemGraph.selfOnlyAt_root_not_same_invariant -- Statement: `Same omegaLoop omegaPair`, and only the first root steps to itself
-- Reading: so stepping to itself is a property of the DRAWING of Ω, not of Ω.
#check @ZeroParadox.MemGraph.zeroStar_reaches_not_arrives -- Statement: in `zeroStar` node 0 reaches node 1 and does not arrive at it
#check @ZeroParadox.Motion.eq_of_reflTransGen_of_selfOnlyAt -- Statement: everything reachable from a point stepping to itself only is that point
#check @ZeroParadox.Motion.run_const_of_selfOnlyAt -- Statement: a run starting at such a point stays there
#check @ZeroParadox.Motion.rank_eq_top_of_reflTransGen_selfOnlyAt -- Statement: a rank dropping by at least one per step is ⊤ of `ℕ∞` on everything reachable from such a point
#check @ZeroParadox.Motion.not_acc_of_cycle      -- Statement: a point on a cycle is not accessible (Mathlib `Acc`)
#check @ZeroParadox.Motion.acc_of_reflTransGen   -- Statement: accessibility passes down along steps
#check @ZeroParadox.Motion.not_acc_iff_reaches_cycle -- Statement: on a finite carrier, not accessible iff a cycle lies below
-- Statement: so, on a finite carrier, if the motion has a run, some point lies on a cycle of OVER: the
-- run's first stage is not accessible for the reversed step. The cycle is of OVER, not a loop of the
-- die (the `Bool` motion with identity UP never loops, § I).
example {α : Type} [Finite α] (M : ZeroParadox.Motion α) {s : ℕ → α} (hs : M.IsRun s) :
    ∃ c, Relation.TransGen M.step c c := by
  have key : ∀ a, Acc (fun x a => M.step a x) a → ∀ n, s n = a → False := by
    intro a ha
    induction ha with
    | intro a _ ih => intro n hn; subst hn; exact ih (s (n + 1)) (hs n) (n + 1) rfl
  obtain ⟨c, -, hc⟩ := (ZeroParadox.Motion.not_acc_iff_reaches_cycle (fun x a => M.step a x)).1
    (fun h => key _ h 0 rfl)
  exact ⟨c, hc.swap⟩
-- Statement: and a run whose stages are pairwise distinct needs an infinite carrier
-- (Mathlib `Infinite.of_injective`).
example {α : Type} (s : ℕ → α) (hinj : Function.Injective s) : Infinite α :=
  Infinite.of_injective s hinj
#check @ZeroParadox.Motion.acc_of_rank_ne_top    -- Statement: a dropping `ℕ∞` rank finite at `a` makes `a` accessible
#check @ZeroParadox.Motion.rank_eq_top_of_not_acc -- Statement: at a point that is not accessible, every dropping rank is ⊤ of `ℕ∞`
#check @ZeroParadox.Motion.accHeight             -- Statement: `Set.ncard` of the strict descendants at accessible points (their count on a finite carrier), ⊤ elsewhere
#check @ZeroParadox.Motion.accHeight_drops       -- Statement: on a finite carrier it drops by at least one per step
#check @ZeroParadox.Motion.forall_rank_eq_top_iff_not_acc -- Statement: on a finite carrier, every dropping rank is ⊤ at `a` iff `a` is not accessible
#check @ZeroParadox.MemGraph.acc_root_iff_of_same -- Statement: `Same A B` gives: the root of `A` accessible iff the root of `B` is
#check @ZeroParadox.MemGraph.ForcedTop           -- Statement: every rank dropping by at least one along the member motion is ⊤ of `ℕ∞` at `a`
#check @ZeroParadox.MemGraph.forcedTop_iff_not_acc -- Statement: iff `a` is not accessible
#check @ZeroParadox.MemGraph.forcedTop_iff_reaches_cycle -- Statement: iff a node on a cycle is reachable from `a`
#check @ZeroParadox.MemGraph.forcedTop_bisim     -- Statement: bisimilar nodes agree on it
#check @ZeroParadox.MemGraph.forcedTop_same      -- Statement: `Same A B` gives it at one root iff at the other
#check @ZeroParadox.MemGraph.omega_forcedTop     -- Statement: it holds at the roots of `omegaLoop` and `omegaPair`
#check @ZeroParadox.MemGraph.zeroStar_empty_forcedTop -- Statement: it holds at node 0 of `zeroStar`, fails at its node 1 and at the root of `empty`
#check @ZeroParadox.MemGraph.junkLoop_control    -- Statement: CONTROL: `Same junkLoop empty`, a node of `junkLoop` has it, its root does not
-- Reading: on finite membership graphs a forced ⊤ rank at the root is a property of the set (invariant
-- under `Same`), stepping to itself is not. It is a termination fact (not accessible); it is not a
-- complexity measure, not Tim's maximally-complex commitment (`ZeroParadox/BottomCannotBe.lean`,
-- last Reading), and no implication with `infinitude_forces_infinite_complexity` is proved either way.
-- Statement: CONTROL, finiteness in `not_acc_iff_reaches_cycle`: on ℕ with `x` a member of `y` iff
-- `x = y + 1`, 0 is not accessible and no point lies on a cycle.
example : ¬ Acc (fun x y : ℕ => x = y + 1) 0 ∧
    ∀ c, ¬ Relation.TransGen (fun x y : ℕ => x = y + 1) c c := by
  refine ⟨fun h => ?_, fun c hc => ?_⟩
  · have : ∀ a, Acc (fun x y : ℕ => x = y + 1) a → False := by
      intro a ha
      induction ha with
      | intro a _ ih => exact ih (a + 1) rfl
    exact this 0 h
  · have : ∀ x y, Relation.TransGen (fun x y : ℕ => x = y + 1) x y → y < x := by
      intro x y h
      induction h with
      | single h => omega
      | tail _ h ih => omega
    exact lt_irrefl _ (this c c hc)
-- Statement: CONTROL, finiteness in `forall_rank_eq_top_iff_not_acc`: on `Option ℕ`, with every
-- `some n` a member of `none` and `some n` a member of `some (n + 1)`, `none` is accessible and every
-- dropping rank is ⊤ of `ℕ∞` at `none`.
example :
    let fan : Option ℕ → Option ℕ → Prop :=
      fun x a => (a = none ∧ x ≠ none) ∨ ∃ n, a = some (n + 1) ∧ x = some n
    Acc fan none ∧ ∀ v : Option ℕ → ℕ∞, (∀ a x, fan x a → v x + 1 ≤ v a) → v none = ⊤ := by
  intro fan
  have hs : ∀ n, Acc fan (some n) := by
    intro n
    induction n with
    | zero =>
      refine Acc.intro _ fun x hx => ?_
      rcases hx with ⟨h, _⟩ | ⟨n, h, _⟩
      · exact absurd h (by simp)
      · simp at h
    | succ n ih =>
      refine Acc.intro _ fun x hx => ?_
      rcases hx with ⟨h, _⟩ | ⟨m, h, hx⟩
      · exact absurd h (by simp)
      · have hm : m = n := by have := Option.some.inj h; omega
        subst hm
        subst hx
        exact ih
  refine ⟨Acc.intro _ fun x hx => ?_, fun v hv => ?_⟩
  · rcases hx with ⟨_, hx⟩ | ⟨n, h, _⟩
    · obtain ⟨n, rfl⟩ := Option.ne_none_iff_exists'.1 hx
      exact hs n
    · simp at h
  · have hge : ∀ n : ℕ, (n : ℕ∞) ≤ v (some n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have := hv (some (n + 1)) (some n) (Or.inr ⟨n, rfl, rfl⟩)
        calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
          _ ≤ v (some n) + 1 := by gcongr
          _ ≤ v (some (n + 1)) := this
    refine ENat.eq_top_iff_forall_ge.2 fun n => ?_
    exact le_trans (hge n) (le_trans le_self_add (hv none (some n) (Or.inl ⟨rfl, by simp⟩)))
-- Statement: under doubling on ℤ_[2], ℤ_[2]'s 0 steps to itself only, every step into it starts at
-- it, and every path of steps ending at it starts at it.
example : (ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).SelfOnlyAt 0 ∧
    (∀ a, (ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).step a 0 → a = 0) ∧
    ∀ x, Relation.ReflTransGen (ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).step x 0 → x = 0 := by
  have hF : ∀ a, (ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).step a 0 → a = 0 := by
    intro a h
    have h' : (0 : ℤ_[2]) = 2 * a := h
    rcases mul_eq_zero.1 h'.symm with h2 | h2
    · exact absurd h2 two_ne_zero
    · exact h2
  exact ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff _ 0).2 (mul_zero 2), hF,
    fun x hx => ZeroParadox.Motion.eq_of_reflTransGen_of_noEntry hF hx⟩
-- Statement: the 2-adic order `emultiplicity 2` drops by at least one along every step of REVERSED doubling, so
-- it is ⊤ of `ℕ∞` at ℤ_[2]'s 0, which steps to itself (`rank_eq_top_of_cycle`).
example : (∀ a b, (ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).reverse.step a b →
      emultiplicity (2 : ℤ_[2]) b + 1 ≤ emultiplicity (2 : ℤ_[2]) a) ∧
    emultiplicity (2 : ℤ_[2]) 0 = ⊤ := by
  have hp : Prime (2 : ℤ_[2]) := by
    have := PadicInt.irreducible_p (p := 2)
    exact_mod_cast this.prime
  have hd : ∀ a b, (ZeroParadox.Motion.ofFun (fun y : ℤ_[2] => 2 * y)).reverse.step a b →
      emultiplicity (2 : ℤ_[2]) b + 1 ≤ emultiplicity (2 : ℤ_[2]) a := by
    intro a b h
    have h' : a = 2 * b := h
    subst h'
    rw [emultiplicity_mul hp,
      (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self, add_comm]
  exact ⟨hd, ZeroParadox.Motion.rank_eq_top_of_cycle _ hd
    (Relation.TransGen.single (show (0 : ℤ_[2]) = 2 * 0 by rw [mul_zero]))⟩
-- Reading: the 2-adic order ranks the REVERSED motion; along doubling itself it rises.

/-! ### § XXI. Orders on motions, one least-fixed-point shape, UP legs as nuclei -/
#check @ZeroParadox.Motion.Closed                -- Statement: `S` is UP-closed and OVER-closed
#check @ZeroParadox.Motion.closedSublattice      -- Statement: those sets form a complete sublattice of `Set α`
-- Statement: ⊥ of `closedSublattice M` is `∅` and ⊤ is `Set.univ`.
example {α : Type} (M : ZeroParadox.Motion α) :
    ((⊥ : M.closedSublattice) : Set α) = ∅ ∧ ((⊤ : M.closedSublattice) : Set α) = Set.univ :=
  ⟨rfl, rfl⟩
-- Statement: CONTROL: on `Bool`, identity UP and the single step `false → true`, `{false}` is
-- UP-closed and not OVER-closed.
example :
    (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl)
        (fun a b => a = false ∧ b = true)).UpClosed {false} ∧
      ¬ (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl)
        (fun a b => a = false ∧ b = true)).Closed {false} :=
  ⟨fun x hx y hy => by
      have : y = id x := Part.mem_some_iff.1 hy
      subst this
      exact hx,
   fun h => by
      have := h.2 false rfl true ⟨rfl, rfl⟩
      simp at this⟩
#check @ZeroParadox.Motion.restrictInclusion_refl -- Statement: restriction inclusion along `S ⊆ S` is the identity
#check @ZeroParadox.Motion.restrictInclusion_trans -- Statement: and along `U ⊆ T ⊆ S` it composes
#check @ZeroParadox.ordinalViewClosed            -- Statement: the carrier of `ordinalView n` as a closed set of `ordinalSuccMotion`
#check @ZeroParadox.ordinalViewClosed_strictAnti -- Statement: strictly antitone in `n`
#check @ZeroParadox.Motion.instPartialOrder      -- Statement: `M ≤ N` when UP is the same and every step of `M` is a step of `N`; a partial order
#check @ZeroParadox.Motion.leHom                 -- Statement: `M ≤ N` gives the identity as a map of motions
#check @ZeroParadox.Motion.isLanding_iff_of_le   -- Statement: `M ≤ N` gives the same landings
#check @ZeroParadox.Motion.noEntry_anti          -- Statement: the "no entry from elsewhere" set of `N` lies in that of `M`
#check @ZeroParadox.Motion.noExit_anti           -- Statement: the "no exit elsewhere" set of `N` lies in that of `M`
#check @ZeroParadox.Motion.noStepAt_anti         -- Statement: a point with no step in `N` has none in `M`
#check @ZeroParadox.Motion.leavesAt_mono         -- Statement: stepping elsewhere passes from `M` to `N`
#check @ZeroParadox.Motion.fanIn_mono            -- Statement: fan-in passes from `M` to `N`
#check @ZeroParadox.Motion.corner_mono           -- Statement: the corner passes from `M` to `N`
#check @ZeroParadox.Motion.climb_mono            -- Statement: the climb passes from `M` to `N`
#check @ZeroParadox.Motion.reverse_le_iff        -- Statement: INVARIANT: reversing both keeps `≤`
-- Statement: CONTROL, arrival is not monotone: on `Bool` with identity UP, the step `false → true` is
-- below "every step from `false`"; `false` arrives at `true` in the first and not in the second.
example :
    (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a b => a = false ∧ b = true)) ≤
      ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl) (fun a _ => a = false) ∧
    (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl)
      (fun a b => a = false ∧ b = true)).Arrives true false ∧
    ¬ (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl)
      (fun a _ => a = false)).Arrives true false := by
  refine ⟨⟨rfl, fun _ _ h => h.1⟩, .next ⟨true, rfl, rfl⟩ fun b hb => ?_, fun h => ?_⟩
  · obtain ⟨-, rfl⟩ := hb
    exact .here
  have key : ∀ x, (ZeroParadox.Motion.ofTotal (id : Bool → Bool) (fun _ => rfl)
      (fun a _ => a = false)).Arrives true x → x = true := by
    intro x hx
    induction hx with
    | here => rfl
    | next hex _ ih =>
      obtain ⟨_, hb⟩ := hex
      exact ih _ hb
  exact absurd (key false h) (by decide)
#check @ZeroParadox.IsLeastFixedPointUpTo        -- Statement: the least-fixed-point schema with the equation `f mu = mu` passed as a relation `e`
#check @ZeroParadox.upTo_eq_iff                  -- Statement: with `e = Eq` it is `IsLeastFixedPointFrom`
#check @ZeroParadox.nat_isLeastFixedPointUpTo    -- Statement: on `Type`, with injections and equivalences, ℕ is the least fixed point of `Option` from `Empty`
#check @ZeroParadox.aleph0_isLeastFixedPointFrom -- Statement: on `Cardinal`, `ℵ₀` is the least fixed point of `· + 1` from 0
#check @ZeroParadox.fin_not_fixed                -- Statement: no `Option (Fin n) ≃ Fin n`
#check @ZeroParadox.optIter_lt_nat               -- Statement: each stage of adjoining points to `Empty` injects into ℕ and is not equivalent to it
#check @ZeroParadox.epsilonZero_tower_lt         -- Statement: each ω-tower stage is below ε₀
#check @ZeroParadox.nothing_between_is_a_step    -- Statement: no ordinal below ε₀ is fixed by `ω^·`
-- Reading: one shape, two implementations: adjoining a point from `Empty` and the ω-tower from 0, ⊥
-- of `Ordinal`, have no fixed stage and close at the first fixed point, ℕ up to `≃` and ε₀ up to `=`.
-- No map between ℕ and ε₀ is stated, and the count of adjoined points is not linked to the corner
-- index `ordinalCornerStep^[n]`.
#check @ZeroParadox.Motion.toNucleus             -- Statement: on a meet-semilattice, a total, raising, `⊓`-preserving UP is a Mathlib `Nucleus`
#check @ZeroParadox.Motion.ofNucleus             -- Statement: a nucleus with any OVER is a motion
#check @ZeroParadox.Motion.toNucleus_ofNucleus   -- Statement: the round trip nucleus → motion → nucleus returns the nucleus
#check @ZeroParadox.Motion.isLanding_ofNucleus_iff -- Statement: landings are the fixed points of the nucleus
#check @ZeroParadox.Motion.isLanding_ofNucleus_anti -- Statement: `n ≤ m` gives every landing of `ofNucleus m s` as a landing of `ofNucleus n s`; one way
#check @ZeroParadox.Motion.isLanding_ofNucleus_subset_iff -- Statement: and both directions, on a meet-semilattice; on a frame the same iff is Mathlib's `Nucleus.range_subset_range`
-- Reading: the order on UP legs is Mathlib's order on nuclei, on any meet-semilattice; when the
--   carrier is a frame it is the frame of nuclei, the corpus's lattice of systems
--   (`ZeroParadox/Category/DifferenceGeneratesSystem.lean`; on `WithTop Ordinal`,
--   `ZeroParadox/Ordinal/SnapMetaLattice.lean` § II). `⊓`-preservation is a hypothesis no die premise
--   supplies. The binder is a meet-semilattice, so § I of `ZeroParadox/Category/DieNucleus.lean`
--   reaches bare `Ordinal`:
#check @ZeroParadox.toNucleus_ordinalTowerMotion -- Statement: MEMBER: `toNucleus` of `ordinalTowerMotion` is `snapNucleus`, by `rfl`; UP at `a` is `Part.some (snapNucleus a)` (the `example` after it in `ZeroParadox/Category/DieNucleus.lean` § III)
-- Reading: what bare `Ordinal` lacks is a top over its order (`IsEmpty (OrderTop Ordinal)`,
--   `ZeroParadox/Category/DieNucleus.lean` § IV), hence Mathlib's `⊤ : Nucleus Ordinal` is not stated
--   (`instTop`, like `ofNucleus_top_up`, takes `[OrderTop X]`), nor the frame of nuclei, so
--   `ofNucleus_top_up` and the two-ended lattice of DieNucleus § II do not reach it; adjoining ⊤
--   gives the frame where the lift is a member:
#check @ZeroParadox.snapNucleusTop_isLanding_iff -- Statement: MEMBER: on the frame `WithTop Ordinal`, for any OVER `s`, the landings of `ofNucleus snapNucleusTop s` are `⊤` and the lifted ε-numbers `↑(ε_ o)`; UP at `↑a` is `ordinalTowerMotion`'s UP at `a` pushed through `↑`, and the round trip returns `snapNucleusTop` (the `example`s after it in `ZeroParadox/Category/DieNucleus.lean` § III)
-- `Statement:` `↑⊥`, the ordinals' ⊥ lifted, is not a landing there: UP sends it to `↑ε₀`
-- (`snapNucleusTop_coe_bot`), and `ε₀ ≠ ⊥` in `Ordinal` (`epsilon0_ne_bot`).
example (s : WithTop Ordinal → WithTop Ordinal → Prop) :
    ¬ (ZeroParadox.Motion.ofNucleus ZeroParadox.snapNucleusTop s).IsLanding
      ((⊥ : Ordinal) : WithTop Ordinal) := by
  rw [ZeroParadox.Motion.isLanding_ofNucleus_iff, ZeroParadox.snapNucleusTop_coe_bot]
  exact fun h => ZeroParadox.epsilon0_ne_bot (WithTop.coe_injective h)
#check @ZeroParadox.em_iff_ofNucleus_dneg_isLanding -- Statement: MEMBER: excluded middle iff every proposition is a landing of `ofNucleus (dnegNucleus Prop) s` (`em_iff_dnegNucleus_trivial` through `isLanding_ofNucleus_iff`); `[propext]`: the statement's `SemilatticeInf Prop` instance is read off the pinned `Prop.instHeytingAlgebra` and is choice-free, where the `SemilatticeInf Prop` instance synthesized under that file's imports carries `Classical.choice` through `Prop.instCompleteLinearOrder` (the parent instances `Prop.instHeytingAlgebra` and `Prop.instCompleteLinearOrder`, and the forced form `dnegLandingForcedInstance`, are printed in `ZeroParadox/Category/DieNucleus.lean`)
#check @ZeroParadox.no_snap_nucleus              -- Statement: NON-MEMBER: for every nucleus `j` on `SynONote`, not every closed point of `j` is fixed by `omegaPow`; so no `ofTotal j _ s` has only `omegaPow`-fixed landings (the die form in `ZeroParadox/Category/DieNucleus.lean` § IV, whose next `example` gives the landings as the closed points). The `Nucleus`-typed corollary of `no_snap_closure`; `SynONote` has no ⊤ over its order (`tower_no_upper_bound`), so `ofNucleus_top_up` is not stated there
#check @ZeroParadox.no_snap_closure              -- Statement: the order-free form: no idempotent endomap of `ONote` has only `omegaPow`-fixed fixed points; no order, no monotonicity, no inflation assumed

/-! ### § XXII. Quotients of a motion: the drawing and the set; carrier-changing steps -/
#check @ZeroParadox.Motion.StepCompat            -- Statement: related starts have related successors
-- Statement: for a setoid, step-compatibility is both transfer clauses, forward and back. Reading: the
-- bisimulation condition of `MemGraph.IsBisim` (Aczel's `R⁺`, 1988, p. 20; Park's, credited p. 92),
-- cited in `ZeroParadox/Settheory/GraphBisim.lean`, here for one relation on one carrier; with it `quot`
-- is the quotient by a bisimulation equivalence.
example {α : Type} (M : ZeroParadox.Motion α) (s : Setoid α) :
    M.StepCompat s ↔ ∀ a a', s.r a a' →
      (∀ b, M.step a b → ∃ b', M.step a' b' ∧ s.r b b') ∧
      (∀ b', M.step a' b' → ∃ b, M.step a b ∧ s.r b b') :=
  ⟨fun h a a' r => ⟨fun b hb => h a a' b r hb, fun b' hb' =>
      let ⟨b, hb, hbb⟩ := h a' a b' (s.symm r) hb'
      ⟨b, hb, s.symm hbb⟩⟩,
    fun h a a' b r hb => (h a a' r).1 b hb⟩
#check @ZeroParadox.Motion.quot                 -- Statement: on the classes, UP the identity and OVER Mathlib's `Relation.Map` of OVER
#check @ZeroParadox.Motion.quotHom               -- Statement: the class map is a map of motions on the steps, for every setoid
#check @ZeroParadox.Motion.quot_step_mk_iff      -- Statement: with step-compatibility, a class steps to `Y` iff a representative steps into `Y`
#check @ZeroParadox.Motion.quot_selfOnlyAt_mk_iff -- Statement: with step-compatibility, a class steps to itself only iff some successor and every successor of a representative is related to it
#check @ZeroParadox.Motion.stepCompat_ofFun      -- Statement: a map sending related points to related points gives step-compatibility for `ofFun`
#check @ZeroParadox.Motion.quot_ofFun_step_iff   -- Statement: and the quotient's OVER is the graph of `Quotient.map'`
#check @ZeroParadox.Motion.UpCompat              -- Statement: related points have related UP values
#check @ZeroParadox.Motion.upCompat_map_eq       -- Statement: with it, related points have the same UP after the class map
#check @ZeroParadox.Motion.quotUp                -- Statement: with it, UP on the classes is the class of UP; OVER as in `quot`
#check @ZeroParadox.Motion.mem_quotUp_up_mk_iff  -- Statement: UP of a class is read off any representative
#check @ZeroParadox.Motion.isLanding_quotUp_mk_iff -- Statement: a class is a landing iff some UP value of a representative is related to it
#check @ZeroParadox.Motion.isLanding_quotUp_mk   -- Statement: if `a` is a landing, its class is; one way (`Die.lean` § XVIII's `Fin 3` member refutes the converse)
#check @ZeroParadox.Motion.quotUp_step           -- Statement: OVER of `quotUp` is OVER of `quot`
#check @ZeroParadox.Motion.upCompat_of_up_eq_some -- Statement: if UP is the identity, every setoid is UP-compatible
#check @ZeroParadox.Motion.quotUp_eq_quot        -- Statement: and then `quotUp` is `quot`
#check @ZeroParadox.Motion.upCompat_ofTotal      -- Statement: a total idempotent sending related points to related points is UP-compatible
-- Statement: `graphMotion n` and `evalStepMotion F` have the identity UP, so `quotUp` is `quot` there.
example (n : ℕ) (s : Setoid (ZeroParadox.MemGraph n)) :
    (ZeroParadox.MemGraph.graphMotion n).quotUp s
        (ZeroParadox.Motion.upCompat_of_up_eq_some (fun _ => rfl) s) =
      (ZeroParadox.MemGraph.graphMotion n).quot s :=
  ZeroParadox.Motion.quotUp_eq_quot (fun _ => rfl) s
example (F : Nat.Partrec.Code → ℕ →. ℕ) :
    (ZeroParadox.evalStepMotion F).quotUp ZeroParadox.evalSetoid
        (ZeroParadox.Motion.upCompat_of_up_eq_some (fun _ => rfl) _) =
      (ZeroParadox.evalStepMotion F).quot ZeroParadox.evalSetoid :=
  ZeroParadox.Motion.quotUp_eq_quot (fun _ => rfl) _
-- Statement: a hyperset member with a non-identity UP: `pruneMotion n` (UP `wfPart`) is UP-compatible
-- with mutual `Sub`, since `wfPart` is monotone (`wfPart_sub_mono`).
example (n : ℕ) :
    (ZeroParadox.MemGraph.pruneMotion n).UpCompat (AntisymmRel.setoid (ZeroParadox.MemGraph n) (· ≤ ·)) :=
  ZeroParadox.Motion.upCompat_ofTotal _ _ fun _ _ h =>
    ⟨ZeroParadox.MemGraph.wfPart_sub_mono h.1, ZeroParadox.MemGraph.wfPart_sub_mono h.2⟩
-- Statement: a `Fin 3` member with a non-identity UP, and the `Fin 3` control where UP does not
-- respect the classes: `Die.lean` § XVIII's two examples after `upCompat_ofTotal`.
-- Statement: members, a self-step of the class with none of a representative: hypersets
-- (`HSet 2`) and codes up to `eval`.
#check @ZeroParadox.MemGraph.drawing_vs_set      -- Statement: `omegaPair` has no self-step in `graphMotion 2`; its class steps to itself only
#check @ZeroParadox.MemGraph.graphMotion_omegaLoop_step_self -- Statement: `omegaLoop` steps to itself in `graphMotion 1`
#check @ZeroParadox.padId_drawing_vs_set         -- Statement: no code steps to itself in `ofFun padId`; every class up to `eval` steps to itself only
#check @ZeroParadox.codes_vs_classes             -- Statement: for computable `eval`-respecting `F`, no code steps to itself only, some class does
#check @ZeroParadox.quot_evalStep_step_iff       -- Statement: that quotient is `ofFun (liftEval F hF)`, step for step
-- Reading: for hypersets SOME representative of Ω's class has no self-step (`omegaPair`) and another
-- has one (`omegaLoop`); for `padId` NO code has one. "Codes are drawings, behaviours are sets" is a
-- shared SHAPE, proved separately in each member; `Code` and `MemGraph` are not related by any map
-- here, and no ⊥ is named on `HSet 2` or `EvalClass` (no view is given).
-- Statement: CONTROLS: `Die.lean` § XVIII's `Fin 3` example (without step-compatibility the class
-- steps to itself and elsewhere, and `quot_step_mk_iff` fails); `constEnc` on codes.
#check @ZeroParadox.constEnc_not_respects        -- Statement: CONTROL: `constEnc` is computable and not `eval`-respecting
#check @ZeroParadox.constEnc_two_successors      -- Statement: CONTROL: its quotient steps some class to two distinct classes
-- Statement: carrier-changing steps, as one motion on a larger carrier: `wrap` on `Σ n, MemGraph n`.
#check @ZeroParadox.MemGraph.wrapMotion          -- Statement: `ofFun` of `(n, A) ↦ (n + 1, wrap A)`
#check @ZeroParadox.MemGraph.wrapMotion_stepCompat -- Statement: `Same` on graphs of every size is step-compatible with it
#check @ZeroParadox.MemGraph.wrapMotion_omegaLoop_selfOnlyAt -- Statement: the class of `omegaLoop` steps to itself only
#check @ZeroParadox.MemGraph.eq_omegaLoop_of_wrapMotion_step_self -- Statement: every class stepping to itself is the class of `omegaLoop`
-- Statement: `Option` on `Type`.
#check @ZeroParadox.optionMotion                 -- Statement: `ofFun Option` on `Type`; the stages `optIter n` form a run
#check @ZeroParadox.quot_optionMotion_step_iff   -- Statement: up to an equivalence, on `Cardinal.{0}`, the class `X` steps to `Y` iff `Y = X + 1`
#check @ZeroParadox.quot_optionMotion_selfOnlyAt_nat -- Statement: the class of ℕ steps to itself only
#check @ZeroParadox.quot_optionMotion_not_selfOnlyAt_fin -- Statement: the class of `Fin n` does not
-- Reading: the change of carrier disappears into a larger carrier (`Σ n, MemGraph n`, `Type`). On the
-- graphs no point steps to itself (`HypersetOrder.lean` § VII's `example`); on `Type` no equation
-- between types is stated. The fixed classes are read off the quotient, the shape of `drawing_vs_set`.

/-! ### § XXIII. T-SNAP as the die's first case study: a run's motion, both directions, the gaps -/
-- Reading (cited, not claimed): each part of the die has a standard home, and this index catalogues
-- them. UP is an idempotent of the category of sets and partial functions (Cockett and Lack, TCS 270
-- (2002), Example 1, p. 228; named Par in Cockett and Hofstra 2008, p. 186), not in general a
-- restriction idempotent (Cockett and Lack, p. 227; Cockett and Hofstra, pp. 186–187, as at
-- `ZeroParadox/Die.lean` § I); OVER is an abstract reduction system, with `NoStepAt` its normal form
-- (Waldmann, Automated Reasoning lecture notes, 2011, p. 2, citing Baader and Nipkow 1998, ch. 2);
-- `quot` under `StepCompat` is the quotient by a bisimulation equivalence (Rutten, TCS 249 (2000),
-- p. 26 for labelled transition systems, generalized as Prop. 5.8, p. 34), of the OVER leg only, since
-- `quot` replaces UP by the identity; a premise free per face and a taboo over all carriers is a
-- Brouwerian counterexample (Diener, arXiv:1804.05495v3, pp. 6, 11). The pair itself, a partial idempotent beside
-- a relation with per-leg premises tabulated across carriers, was not located as a named structure as
-- of 2026-10-22, searched in 13 theoremsearch queries varied by vocabulary, a text grep of 38 papers on
-- restriction categories, rewriting, coalgebra and constructive reverse mathematics, and nLab.
-- Reading: T-SNAP is the die's first case study, read in the converse of the direction the die was
-- built in: "The entire shape of up and over is what gave rise to the premise of the die to start
-- with" (`ZeroParadox/Die.lean`'s Engineer's Take), and these examples render the snap in the die.
-- "Instance" is too strong: the OVER used is CHOSEN, the run motion of `S` (UP the identity, OVER from
-- each stage `S n` to the next), and carrier, UP and view do not fix OVER (§ XIX,
-- `cover_overs_differ`); that choice is the first step these examples do not justify.
-- Statement: each clause is an `example` below. If a run `S` on a `ZPSemilattice L` has `S 0 = ⊥`
-- (CC-1, `hcc1`) and `S 1 ≠ S 0` (`hocc`), then in its run motion ⊥ of `L` steps elsewhere, and the
-- first step strictly raises in ZP-A's induced order (`t_snap_given`'s triple is `S 0 < S 1` there);
-- ⊥ of `L` is also a landing, but UP is the identity there, so every point is one and that conjunct
-- is free. If moreover `S` is a state sequence (ZP-A's D3, which is `StepRaises` of the run motion),
-- then ⊥ of `L` is in the first trap set and no later stage is ⊥ of `L`. From `hcc1` and `hcov` alone,
-- `BotCovered L`; the converse fails on ℕ. UP is the identity in the run motion, so the corner does
-- not fire (§ II); with UP `phaseClosure` on the boundary model `Phase` and OVER the covers of its
-- floor-below order (`WithBot Ordinal`), the corner fires and the motion climbs. In the other
-- direction, if some motion on `L` steps elsewhere at ⊥ of `L`, some step elsewhere out of ⊥ of `L`
-- carries T-SNAP's triple, and that premise gives neither `hocc` nor a run.
-- Statement: if `S 0 = ⊥` and `S 1 ≠ S 0`, then in the run motion of `S` the point `S 0`, ⊥ of `L`, is a
-- landing (free: UP is the identity), steps to `S 1`, steps elsewhere, and `S 0 < S 1` in ZP-A's
-- induced order.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (S : ℕ → L)
    (hcc1 : S 0 = ZeroParadox.ZPSemilattice.bot) (hocc : S 1 ≠ S 0) :
    let M := ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => ∃ n, a = S n ∧ b = S (n + 1))
    M.IsLanding (S 0) ∧ M.step (S 0) (S 1) ∧ M.LeavesAt (S 0) ∧
      (letI := ZeroParadox.zpSemilatticeSup L; S 0 < S 1) := by
  intro M
  letI := ZeroParadox.zpSemilatticeSup L
  obtain ⟨hab, -, hj⟩ := ZeroParadox.t_snap_given S hcc1 hocc
  exact ⟨Part.mem_some_iff.2 rfl, ⟨0, rfl, rfl⟩, ⟨S 1, ⟨0, rfl, rfl⟩, hocc⟩,
    hj, fun h => hab (h.symm.trans ((ZeroParadox.ZPSemilattice.join_comm _ _).trans hj))⟩
-- Statement: INVARIANT, no motion in it: T-SNAP's triple at `(a, b)` is `a < b` in ZP-A's induced order;
-- both directions.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (a b : L) :
    (a ≠ b ∧ b ≠ a ∧ ZeroParadox.ZPSemilattice.join a b = b) ↔
      (letI := ZeroParadox.zpSemilatticeSup L; a < b) := by
  letI := ZeroParadox.zpSemilatticeSup L
  constructor
  · rintro ⟨hab, -, hj⟩
    exact ⟨hj, fun h => hab (h.symm.trans ((ZeroParadox.ZPSemilattice.join_comm b a).trans hj))⟩
  · intro h
    obtain ⟨hj, hn⟩ := lt_iff_le_not_ge.1 h
    refine ⟨fun h => hn ?_, fun h => hn ?_, hj⟩
    · subst h; exact ZeroParadox.ZPSemilattice.join_idem a
    · subst h; exact ZeroParadox.ZPSemilattice.join_idem _
-- Statement: ZP-A's D3, `IsStateSequence S`, is `StepRaises` of the run motion of `S` in ZP-A's induced
-- order; both directions.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (S : ℕ → L) :
    ZeroParadox.ZPSemilattice.IsStateSequence S ↔ @ZeroParadox.Motion.StepRaises L
      (ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
        (fun a b => ∃ n, a = S n ∧ b = S (n + 1))) (ZeroParadox.zpSemilatticeSup L).toLE := by
  constructor
  · intro hS
    rintro a b ⟨n, rfl, rfl⟩
    exact ZeroParadox.ZPSemilattice.state_sequence_monotone S hS n
  · intro h
    exact ⟨fun n => S (n + 1), fun n => (h (S n) (S (n + 1)) ⟨n, rfl, rfl⟩).symm⟩
-- Statement: if moreover `S` is a state sequence, every step of the run motion into ⊥ of `L` starts at
-- ⊥ of `L` (the first trap set, by `eq_bot_of_step_to_bot`) and no later stage is ⊥ of `L`. Under the
-- extra hypothesis `IsStateSequence S`, it adds these trap-set and no-return conclusions to
-- `t_snap_given`'s.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (S : ℕ → L) (hS : ZeroParadox.ZPSemilattice.IsStateSequence S)
    (hcc1 : S 0 = ZeroParadox.ZPSemilattice.bot) (hocc : S 1 ≠ S 0) :
    let M := ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => ∃ n, a = S n ∧ b = S (n + 1))
    (∀ a, M.step a ZeroParadox.ZPSemilattice.bot → a = ZeroParadox.ZPSemilattice.bot) ∧
      ∀ n, S (n + 1) ≠ ZeroParadox.ZPSemilattice.bot := by
  intro M
  letI := ZeroParadox.zpSemilatticeSup L
  letI := ZeroParadox.zpOrderBot L
  have hr : M.StepRaises := by
    rintro a b ⟨n, rfl, rfl⟩
    exact ZeroParadox.ZPSemilattice.state_sequence_monotone S hS n
  have trap : ∀ a, M.step a ⊥ → a = ⊥ := ZeroParadox.Motion.eq_bot_of_step_to_bot hr
  refine ⟨trap, fun n => ?_⟩
  induction n with
  | zero => exact fun h => hocc (h.trans hcc1.symm)
  | succ n ih => exact fun h => ih (trap _ ⟨n + 1, rfl, h.symm⟩)
-- Statement: Q2, OVER run backwards: for a state sequence, in the reversed run motion every step out of
-- ⊥ of `L` ends at ⊥ of `L` (the second trap set, by `eq_bot_of_step_from_bot`).
example {L : Type*} [ZeroParadox.ZPSemilattice L] (S : ℕ → L) (hS : ZeroParadox.ZPSemilattice.IsStateSequence S) :
    letI := ZeroParadox.zpSemilatticeSup L; letI := ZeroParadox.zpOrderBot L;
    ∀ b, (ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => ∃ n, a = S n ∧ b = S (n + 1))).reverse.step (⊥ : L) b → b = ⊥ := by
  letI := ZeroParadox.zpSemilatticeSup L
  letI := ZeroParadox.zpOrderBot L
  intro b hb
  refine ZeroParadox.Motion.eq_bot_of_step_from_bot (M := (ZeroParadox.Motion.ofTotal (id : L → L)
    (fun _ => rfl) (fun a b => ∃ n, a = S n ∧ b = S (n + 1))).reverse) ?_ b hb
  rintro x y ⟨n, rfl, rfl⟩
  exact ZeroParadox.ZPSemilattice.state_sequence_monotone S hS n
-- Statement: from `hcc1` and `hcov` alone (`t_snap_given_cover`), ⊥ of `L` has a cover in ZP-A's
-- induced order: `BotCovered L`; one way.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (S : ℕ → L)
    (hcc1 : S 0 = ZeroParadox.ZPSemilattice.bot)
    (hcov : letI := ZeroParadox.zpSemilatticeSup L; S 0 ⋖ S 1) :
    letI := ZeroParadox.zpSemilatticeSup L; letI := ZeroParadox.zpOrderBot L;
      ZeroParadox.BotCovered L :=
  ⟨S 1, (ZeroParadox.t_snap_given_cover S hcc1
    (by letI := ZeroParadox.zpSemilatticeSup L; exact hcov.1.ne') hcov).2⟩
-- Statement: GAP, carrier cover against run cover: on ℕ (join `max`, ⊥ = 0), `BotCovered ℕ` holds in
-- ZP-A's induced order while the run `0, 2, 2, …` meets `hcc1` and `hocc` and not `hcov`.
example :
    let S : ℕ → ℕ := fun n => match n with | 0 => 0 | _ + 1 => 2
    @ZeroParadox.BotCovered ℕ (ZeroParadox.zpSemilatticeSup ℕ).toPartialOrder
        (ZeroParadox.zpOrderBot ℕ) ∧
      S 0 = ZeroParadox.ZPSemilattice.bot ∧ S 1 ≠ S 0 ∧
      ¬ @CovBy ℕ (ZeroParadox.zpSemilatticeSup ℕ).toLT (S 0) (S 1) := by
  intro S
  have key : ∀ a b : ℕ, @LT.lt ℕ (ZeroParadox.zpSemilatticeSup ℕ).toLT a b ↔ a < b := by
    intro a b
    show (max a b = b ∧ ¬ max b a = a) ↔ a < b
    omega
  refine ⟨⟨1, (key 0 1).2 (by decide), fun c h1 h2 => ?_⟩, rfl, by decide, fun h => ?_⟩
  · have h1' := (key 0 c).1 h1
    have h2' := (key c 1).1 h2
    clear h1 h2
    omega
  · exact h.2 (c := 1) ((key 0 1).2 (by decide)) ((key 1 2).2 (by decide))
-- Statement: the other direction: if a motion on `L` steps elsewhere at ⊥ of `L`, some step `⊥ → b`
-- carries T-SNAP's triple at `(⊥, b)`. No landing hypothesis is used, so the UP leg plays no part.
example {L : Type*} [ZeroParadox.ZPSemilattice L] (M : ZeroParadox.Motion L)
    (hl : M.LeavesAt (ZeroParadox.ZPSemilattice.bot : L)) :
    ∃ b, M.step ZeroParadox.ZPSemilattice.bot b ∧
      (ZeroParadox.ZPSemilattice.bot ≠ b ∧ b ≠ ZeroParadox.ZPSemilattice.bot ∧
        ZeroParadox.ZPSemilattice.join ZeroParadox.ZPSemilattice.bot b = b) :=
  let ⟨b, hs, hne⟩ := hl
  ⟨b, hs, ZeroParadox.t_snap_given
    (fun n => match n with | 0 => ZeroParadox.ZPSemilattice.bot | _ + 1 => b) rfl hne⟩
-- Statement: GAP, a point fact against an index fact: stepping elsewhere at `S 0` does not give `hocc`.
-- The run `c₀, c₀, c₁, c₁, …` on `MachinePhase` starts at ⊥ of `MachinePhase`, steps elsewhere at `S 0`
-- in its run motion, and has `S 1 = S 0`.
example :
    let S : ℕ → ZeroParadox.MachinePhase := fun n => match n with
      | 0 => ZeroParadox.c₀ | 1 => ZeroParadox.c₀ | _ + 2 => ZeroParadox.c₁
    S 0 = ZeroParadox.ZPSemilattice.bot ∧
      (ZeroParadox.Motion.ofTotal (id : ZeroParadox.MachinePhase → ZeroParadox.MachinePhase)
        (fun _ => rfl) (fun a b => ∃ n, a = S n ∧ b = S (n + 1))).LeavesAt (S 0) ∧ S 1 = S 0 := by
  intro S
  exact ⟨rfl, ⟨ZeroParadox.c₁, ⟨1, rfl, rfl⟩, (by decide : ZeroParadox.c₁ ≠ ZeroParadox.c₀)⟩, rfl⟩
-- Statement: GAP, no run: on `MachinePhase` with UP the identity and OVER the single step `c₀ → c₁`, ⊥
-- of `MachinePhase` steps elsewhere and no sequence is a run.
example :
    let M := ZeroParadox.Motion.ofTotal (id : ZeroParadox.MachinePhase → ZeroParadox.MachinePhase)
      (fun _ => rfl) (fun a b => a = ZeroParadox.c₀ ∧ b = ZeroParadox.c₁)
    M.LeavesAt ZeroParadox.c₀ ∧ ¬ ∃ S : ℕ → ZeroParadox.MachinePhase, M.IsRun S := by
  intro M
  refine ⟨⟨ZeroParadox.c₁, ⟨rfl, rfl⟩, by decide⟩, ?_⟩
  rintro ⟨S, hS⟩
  exact absurd ((hS 1).1.symm.trans (hS 0).2) (by decide)
-- Statement: the face on `MachinePhase`, the run `c₀, c₁, c₁, …` (`t_snap_derived`'s): a state
-- sequence; in its run motion ⊥ of `MachinePhase` (`c₀`) is a landing that steps elsewhere, `c₁` steps to
-- itself only, the corner does not fire, no later stage is `c₀`, and `BotCovered` holds.
example :
    let S : ℕ → ZeroParadox.MachinePhase := fun n => match n with
      | 0 => ZeroParadox.c₀ | _ + 1 => ZeroParadox.c₁
    let M := ZeroParadox.Motion.ofTotal (id : ZeroParadox.MachinePhase → ZeroParadox.MachinePhase)
      (fun _ => rfl) (fun a b => ∃ n, a = S n ∧ b = S (n + 1))
    ZeroParadox.ZPSemilattice.IsStateSequence S ∧ M.IsLanding ZeroParadox.c₀ ∧ M.LeavesAt ZeroParadox.c₀ ∧
      M.SelfOnlyAt ZeroParadox.c₁ ∧ ¬ M.Corner ∧ (∀ n, S (n + 1) ≠ ZeroParadox.ZPSemilattice.bot) ∧
      (letI := ZeroParadox.zpSemilatticeSup ZeroParadox.MachinePhase;
        letI := ZeroParadox.zpOrderBot ZeroParadox.MachinePhase;
        ZeroParadox.BotCovered ZeroParadox.MachinePhase) := by
  intro S M
  refine ⟨⟨fun _ => ZeroParadox.c₁, fun n => by cases n <;> rfl⟩, Part.mem_some_iff.2 rfl,
    ⟨ZeroParadox.c₁, ⟨0, rfl, rfl⟩, by decide⟩, ⟨⟨1, rfl, rfl⟩, ?_⟩,
    fun ⟨_, _, _, _, _, hz, hzb⟩ => hzb (Part.mem_some_iff.1 hz),
    fun n h => (by decide : ZeroParadox.c₁ ≠ ZeroParadox.c₀) h, ?_⟩
  · rintro b ⟨n, hn, hb⟩
    cases n with
    | zero => exact absurd hn (by decide : ZeroParadox.c₁ ≠ ZeroParadox.c₀)
    | succ k => exact hb
  · letI := ZeroParadox.zpSemilatticeSup ZeroParadox.MachinePhase
    letI := ZeroParadox.zpOrderBot ZeroParadox.MachinePhase
    refine ⟨ZeroParadox.c₁, ⟨rfl, by decide⟩, fun c h1 h2 => ?_⟩
    cases c
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h2
-- Statement: the same cells on `OntologicalStates` (⊥ of `OntologicalStates` is `null`), run
-- `null, exist, exist, …`.
example :
    let S : ℕ → ZeroParadox.OntologicalStates := fun n => match n with
      | 0 => .null | _ + 1 => .exist
    let M := ZeroParadox.Motion.ofTotal
      (id : ZeroParadox.OntologicalStates → ZeroParadox.OntologicalStates)
      (fun _ => rfl) (fun a b => ∃ n, a = S n ∧ b = S (n + 1))
    ZeroParadox.ZPSemilattice.IsStateSequence S ∧ S 0 = ZeroParadox.ZPSemilattice.bot ∧
      M.IsLanding .null ∧ M.LeavesAt .null ∧ M.SelfOnlyAt .exist ∧ ¬ M.Corner ∧
      (∀ n, S (n + 1) ≠ ZeroParadox.ZPSemilattice.bot) ∧
      (letI := ZeroParadox.zpSemilatticeSup ZeroParadox.OntologicalStates;
        letI := ZeroParadox.zpOrderBot ZeroParadox.OntologicalStates;
        ZeroParadox.BotCovered ZeroParadox.OntologicalStates) := by
  intro S M
  refine ⟨⟨fun _ => .exist, fun n => by cases n <;> rfl⟩, rfl, Part.mem_some_iff.2 rfl,
    ⟨.exist, ⟨0, rfl, rfl⟩, by decide⟩, ⟨⟨1, rfl, rfl⟩, ?_⟩,
    fun ⟨_, _, _, _, _, hz, hzb⟩ => hzb (Part.mem_some_iff.1 hz),
    fun n h => (by decide : ZeroParadox.OntologicalStates.exist ≠ .null) h, ?_⟩
  · rintro b ⟨n, hn, hb⟩
    cases n with
    | zero => exact absurd hn (by decide : ZeroParadox.OntologicalStates.exist ≠ .null)
    | succ k => exact hb
  · letI := ZeroParadox.zpSemilatticeSup ZeroParadox.OntologicalStates
    letI := ZeroParadox.zpOrderBot ZeroParadox.OntologicalStates
    refine ⟨.exist, ⟨rfl, by decide⟩, fun c h1 h2 => ?_⟩
    cases c
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h2
-- Statement: the snap's UP leg at the boundary model: `phaseBelowCoverMotion` (UP `phaseClosure`, OVER
-- the covers of `WithBot Ordinal`) climbs from the landing `floor`, the point sent to ⊥ of
-- `WithBot Ordinal`, over the cover to the snap `up 0`, then UP to `up ε₀`, which is neither the snap
-- (`epsilon0_ne_zero`) nor `floor`; so its corner fires (`climb_corner`). The statement names
-- `phaseBelowCoverMotion`, which measures `[propext, Classical.choice, Quot.sound]`, and its UP
-- `phaseClosure` measures the same, through Mathlib's `Ordinal` order and fixed-point theory, while
-- `phaseEquivWithBot` measures `[propext, Quot.sound]` (`ZeroParadox/Multihomed/BoundaryOrder.lean`'s
-- PurityCheck); the type `Ordinal` itself measures `[propext, Quot.sound]`
-- (`ZeroParadox/Ordinal/OrdinalChoiceEssential.lean`'s PurityCheck).
example : ZeroParadox.phaseBelowCoverMotion.Climb ∧ ZeroParadox.phaseBelowCoverMotion.Corner := by
  have h : ZeroParadox.phaseBelowCoverMotion.Climb := by
    refine ⟨ZeroParadox.Phase.floor, ZeroParadox.snap, ZeroParadox.Phase.up ZeroParadox.epsilonZero,
      Part.mem_some_iff.2 rfl, ZeroParadox.phase_floor_covBy_snap, ?_, ?_, ?_⟩
    · exact Part.mem_some_iff.2 (congrArg ZeroParadox.Phase.up
        (ZeroParadox.epsilon0_eq_nfp_bot.trans (congrArg _ Ordinal.bot_eq_zero)))
    · exact fun e => ZeroParadox.epsilon0_ne_zero (ZeroParadox.Phase.up.inj e)
    · exact fun e => ZeroParadox.Phase.noConfusion e
  exact ⟨h, ZeroParadox.Motion.climb_corner _ h⟩
-- Reading: Q1: if `hcc1` and `hocc`, ⊥ of `L` is the source the run leaves (the constant run at ⊥ of
-- `L`, a CONTROL below, never leaves); if moreover `S` is a state sequence, it never re-enters, and in
-- the two-state runs above (`c₀, c₁, c₁, …` and `null, exist, exist, …`) the other end (`c₁`, `exist`)
-- is where the run stays, stepping to itself only.
-- Q2: if `S` is a state sequence, then run backwards (`reverse`), ⊥ of `L` is in the second trap set:
-- every step from it stays at it (CONTROL below: without that premise, on ℕ it fails).
-- INVARIANT: UP (`reverse` keeps it) and the equivalence of T-SNAP's triple with `<`.
-- Statement: CONTROL for Q2's premise: on ℕ (join `max`, ⊥ = 0) the run `0, 1, 0, 1, …` is not a
-- state sequence, and its reversed run motion steps from 0 to 1.
example :
    (ZeroParadox.Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl)
      (fun a b => ∃ n, a = n % 2 ∧ b = (n + 1) % 2)).reverse.step 0 1 ∧
    ¬ ZeroParadox.ZPSemilattice.IsStateSequence (fun n : ℕ => n % 2) :=
  ⟨⟨1, rfl, rfl⟩, fun ⟨e, he⟩ => by have := he 1; simp [ZeroParadox.ZPSemilattice.join] at this; omega⟩
-- Statement: CONTROL, `tsnap_holds_but_nothing_moves`: T-SNAP's triple holds on `MachinePhase` while in
-- `ofFun stuckPhase` every phase steps to itself only, so ⊥ of `MachinePhase` does not step elsewhere.
example : (ZeroParadox.c₀ ≠ ZeroParadox.c₁ ∧ ZeroParadox.c₁ ≠ ZeroParadox.c₀ ∧
      ZeroParadox.ZPSemilattice.join ZeroParadox.c₀ ZeroParadox.c₁ = ZeroParadox.c₁) ∧
    (∀ p, (ZeroParadox.Motion.ofFun ZeroParadox.stuckPhase).SelfOnlyAt p) ∧
    ¬ (ZeroParadox.Motion.ofFun ZeroParadox.stuckPhase).LeavesAt ZeroParadox.c₀ :=
  ⟨ZeroParadox.tsnap_holds_but_nothing_moves.1,
    fun p => (ZeroParadox.Motion.selfOnlyAt_ofFun_iff ZeroParadox.stuckPhase p).2 rfl,
    fun h => ZeroParadox.Motion.not_selfOnlyAt_and_leavesAt _ ZeroParadox.c₀
      ⟨(ZeroParadox.Motion.selfOnlyAt_ofFun_iff ZeroParadox.stuckPhase ZeroParadox.c₀).2 rfl, h⟩⟩
-- Statement: CONTROL: the constant run at ⊥ of any `L`: in its run motion ⊥ of `L` steps to itself only
-- and does not step elsewhere.
example {L : Type*} [ZeroParadox.ZPSemilattice L] :
    let M := ZeroParadox.Motion.ofTotal (id : L → L) (fun _ => rfl)
      (fun a b => ∃ _ : ℕ, a = ZeroParadox.ZPSemilattice.bot ∧ b = ZeroParadox.ZPSemilattice.bot)
    M.SelfOnlyAt ZeroParadox.ZPSemilattice.bot ∧ ¬ M.LeavesAt ZeroParadox.ZPSemilattice.bot := by
  intro M
  have hs : M.SelfOnlyAt ZeroParadox.ZPSemilattice.bot := ⟨⟨0, rfl, rfl⟩, fun _ ⟨_, _, hb⟩ => hb⟩
  exact ⟨hs, fun h => ZeroParadox.Motion.not_selfOnlyAt_and_leavesAt _ _ ⟨hs, h⟩⟩
-- Statement: CONTROL, an ordered field (ℝ is one), in the field's OWN linear order: it has no
-- `OrderBot`, so `BotCovered` is not stated in that order (neither member nor non-member); no pair is
-- a cover (`not_covBy`); and the field's 0 has no first step (`axb1_fails_in_ordered_field`). `hcov`
-- is typed in the order a `ZPSemilattice` induces, not this one, so this control is silent on `hcov`.
example {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (S : ℕ → F) :
    IsEmpty (OrderBot F) ∧ ¬ (S 0 ⋖ S 1) ∧ ¬ ZeroParadox.HasFirstStep (0 : F) :=
  ⟨⟨fun h => by letI := h; exact not_lt.2 (bot_le : (⊥ : F) ≤ ⊥ - 1) (sub_one_lt ⊥)⟩,
    not_covBy, ZeroParadox.axb1_fails_in_ordered_field⟩
-- Statement: CONTROL, `Unit`: `hocc` has no member and no motion on `Unit` steps elsewhere.
example : (¬ ∃ S : ℕ → Unit, S 1 ≠ S 0) ∧ ∀ M : ZeroParadox.Motion Unit, ¬ M.LeavesAt () :=
  ⟨fun ⟨_, h⟩ => h rfl, fun _ ⟨_, _, h⟩ => h rfl⟩
-- Statement: CONTROL, `Fin 3` in its own order (⊥ = 0): the run `0, 2, 2, …` has `hocc` and steps
-- elsewhere at `S 0` in its run motion, and `S 1` does not cover `S 0` (1 lies between).
example :
    let S : ℕ → Fin 3 := fun n => match n with | 0 => 0 | _ + 1 => 2
    S 1 ≠ S 0 ∧ (ZeroParadox.Motion.ofTotal (id : Fin 3 → Fin 3) (fun _ => rfl)
      (fun a b => ∃ n, a = S n ∧ b = S (n + 1))).LeavesAt (S 0) ∧ ¬ (S 0 ⋖ S 1) := by
  intro S
  exact ⟨by decide, ⟨2, ⟨0, rfl, rfl⟩, by decide⟩, fun h => h.2 (c := 1) (by decide) (by decide)⟩

end DieCannotBeIndex
