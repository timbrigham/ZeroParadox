-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): `snap_of_firstStep_MLRandom` instantiated on two carriers, the corner on `WithBot Ordinal` and the cover at ε₀ on `{0} ∪ {fixed points of ω^·}`, with an order isomorphism relating them. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Information.TwoRequirements
import ZeroParadox.Multihomed.BoundaryOrder
import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Reals.OrderedField
import Mathlib.Tactic

/-!
# The snap at ε₀: the corner on one carrier, the cover on another

## Engineer's Take

There was something about epsilon zero we hadn't quite wrapped up. What we needed was two specific things: an instantiation, and a very specific place in the die. These are two separate zoom levels, a maximum of one and a minimum of the other.

---

## Formal Overview (AI-assisted)
§ I: `max` on a linear order with least element. § II: the corner, `WithBot Ordinal`. § III: the
cover, `EpsilonOrZero`. § IV: the iso between them. Each snap is one way, from hypotheses.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. A linear order with a least element, join `max` -/

/-- `Statement:` join `max`, ⊥ the given least element `b`; a definition, not an instance. -/
abbrev linearMaxZPS (α : Type*) [LinearOrder α] (b : α) (hb : ∀ x, b ≤ x) : ZPSemilattice α where
  join := max
  bot := b
  join_assoc := max_assoc
  join_comm := max_comm
  join_idem := max_self
  bot_join := fun x => max_eq_right (hb x)

/-- `Statement:` under `linearMaxZPS`, ZP-A's induced `<` is `α`'s own `<`. -/
theorem linearMaxZPS_lt_iff {α : Type*} [LinearOrder α] (b : α) (hb : ∀ x, b ≤ x) (x y : α) :
    @LT.lt α (@zpSemilatticeSup α (linearMaxZPS α b hb)).toLT x y ↔ x < y := by
  show (max x y = y ∧ ¬ max y x = x) ↔ x < y
  rw [max_eq_right_iff, max_eq_right_iff, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- `Statement:` so its covers are `α`'s own covers; both directions. -/
theorem linearMaxZPS_covBy_iff {α : Type*} [LinearOrder α] (b : α) (hb : ∀ x, b ≤ x) (x y : α) :
    @CovBy α (@zpSemilatticeSup α (linearMaxZPS α b hb)).toLT x y ↔ x ⋖ y := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(linearMaxZPS_lt_iff b hb _ _).1 h1, fun c hc1 hc2 =>
      h2 ((linearMaxZPS_lt_iff b hb _ _).2 hc1) ((linearMaxZPS_lt_iff b hb _ _).2 hc2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(linearMaxZPS_lt_iff b hb _ _).2 h1, fun c hc1 hc2 =>
      h2 ((linearMaxZPS_lt_iff b hb _ _).1 hc1) ((linearMaxZPS_lt_iff b hb _ _).1 hc2)⟩

/-- `Statement:` `BotHasFirstStep` under `linearMaxZPS` iff `HasFirstStep b` in `α`'s order. -/
theorem linearMaxZPS_botHasFirstStep_iff {α : Type*} [LinearOrder α] (b : α) (hb : ∀ x, b ≤ x) :
    @BotHasFirstStep α (linearMaxZPS α b hb) ↔ HasFirstStep b :=
  ⟨fun ⟨a, ha⟩ => ⟨a, (linearMaxZPS_covBy_iff b hb _ _).1 ha⟩,
   fun ⟨a, ha⟩ => ⟨a, (linearMaxZPS_covBy_iff b hb _ _).2 ha⟩⟩

/-- `Statement:` if `b ⋖ a` and `w` is Martin-Löf random for `trials p hp` with `0 < p`, then
`snap_of_firstStep_MLRandom`'s conclusion holds under `linearMaxZPS`, and the run's `S 1` covers
`b` in `α`'s order and equals `a` (`axb1_gives_unique_target`). One way. -/
theorem linearMaxZPS_snap_target {α : Type*} [LinearOrder α] (b : α) (hb : ∀ x, b ≤ x)
    (a : α) (ha : b ⋖ a)
    (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (w : ℕ → Bool) (hML : MLRandom (trials p hp) w) :
    ∃ (φ : Bool → α) (hw : ∃ k, w k = true),
      ((φ ∘ firedRun w hw) 0 = b ∧ (φ ∘ firedRun w hw) 1 ≠ (φ ∘ firedRun w hw) 0 ∧
        @IsStateSequence α (linearMaxZPS α b hb) (φ ∘ firedRun w hw)) ∧
      b ⋖ (φ ∘ firedRun w hw) 1 ∧ (φ ∘ firedRun w hw) 1 = a := by
  obtain ⟨φ, hw, h⟩ := @snap_of_firstStep_MLRandom α (linearMaxZPS α b hb)
    ((linearMaxZPS_botHasFirstStep_iff b hb).2 ⟨a, ha⟩) p hp hp0 w hML
  have hcov : b ⋖ (φ ∘ firedRun w hw) 1 := (linearMaxZPS_covBy_iff b hb _ _).1 h.2.2
  exact ⟨φ, hw, h.1, hcov, (axb1_gives_unique_target b ⟨a, ha⟩).unique hcov ha⟩

/-! ## § II. The corner: `WithBot Ordinal`, the floor-below order of `BoundaryOrder.lean` -/

/-- `Statement:` `linearMaxZPS` on `WithBot Ordinal`, ⊥ of `WithBot Ordinal` as its ⊥. -/
noncomputable abbrev phaseMaxZPS : ZPSemilattice (WithBot Ordinal.{0}) :=
  linearMaxZPS (WithBot Ordinal.{0}) ⊥ (fun _ => bot_le)

/-- `Statement:` ⊥ of `WithBot Ordinal` has a first step under `phaseMaxZPS`. -/
theorem phaseMaxZPS_botHasFirstStep : @BotHasFirstStep (WithBot Ordinal.{0}) phaseMaxZPS :=
  (linearMaxZPS_botHasFirstStep_iff _ _).2 ⟨_, phase_floor_covBy_snap⟩

/-- `Statement:` under `phaseMaxZPS`, if `w` is Martin-Löf random for `trials p hp` with `0 < p`,
some run `S` from the tape has `⊥ ⋖ S 1`, `S 1 = ↑0 ≠ ↑ε₀`, and `phaseUpAndOver.up (S 1) = ↑ε₀`.
One way. -/
theorem phase_snap_of_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (w : ℕ → Bool)
    (hML : MLRandom (trials p hp) w) :
    ∃ (φ : Bool → WithBot Ordinal.{0}) (hw : ∃ k, w k = true),
      (⊥ : WithBot Ordinal.{0}) ⋖ (φ ∘ firedRun w hw) 1 ∧
      (φ ∘ firedRun w hw) 1 = ((0 : Ordinal) : WithBot Ordinal) ∧
      (φ ∘ firedRun w hw) 1 ≠ ((epsilonZero : Ordinal) : WithBot Ordinal) ∧
      phaseUpAndOver.up ((φ ∘ firedRun w hw) 1) = ((epsilonZero : Ordinal) : WithBot Ordinal) := by
  obtain ⟨φ, hw, -, hcov, h1⟩ := linearMaxZPS_snap_target (⊥ : WithBot Ordinal.{0})
    (fun _ => bot_le) _ phase_floor_covBy_snap p hp hp0 w hML
  refine ⟨φ, hw, hcov, h1, ?_, ?_⟩
  · rw [h1]; exact phase_floor_snap_epsilon0_ne.1
  · rw [h1]; exact phaseUp_snap

-- `Statement:` CONTROL: in `WithBot Ordinal`, `↑ε₀` does not cover ⊥ of `WithBot Ordinal` (`↑0` lies
-- between), so no run's first step lands there.
example : ¬ (⊥ : WithBot Ordinal.{0}) ⋖ ((epsilonZero : Ordinal) : WithBot Ordinal) := fun h =>
  h.2 (c := ((0 : Ordinal) : WithBot Ordinal)) (WithBot.bot_lt_coe _)
    (WithBot.coe_lt_coe.2 (Ordinal.epsilon_pos 0))

/-! ## § III. The cover: `{o | o = 0 ∨ ω^o = o}`, join `max`, ⊥ = 0 of `Ordinal` -/

/-- `Statement:` the ordinals that are 0 or fixed by `α ↦ ω^α`, in `Ordinal`'s order. -/
abbrev EpsilonOrZero : Type 1 := {o : Ordinal.{0} // o = 0 ∨ Ordinal.omega0 ^ o = o}

/-- `Statement:` the point 0 of `Ordinal`, adjoined by the left disjunct. -/
def epsilonOrZero_bot : EpsilonOrZero := ⟨0, Or.inl rfl⟩

/-- `Statement:` the point ε₀. -/
noncomputable def epsilonOrZero_eps0 : EpsilonOrZero := ⟨Ordinal.epsilon 0, Or.inr epsilon0_is_fixedpoint⟩

/-- `Statement:` the point ε₁. -/
noncomputable def epsilonOrZero_eps1 : EpsilonOrZero :=
  ⟨Ordinal.epsilon 1, Or.inr (Ordinal.omega0_opow_epsilon 1)⟩

/-- `Statement:` `epsilonOrZero_bot` is least. -/
theorem epsilonOrZero_bot_le (x : EpsilonOrZero) : epsilonOrZero_bot ≤ x :=
  show (0 : Ordinal) ≤ x.1 from zero_le (a := x.1)

/-- `Statement:` `linearMaxZPS` on `EpsilonOrZero`, with `epsilonOrZero_bot` as its ⊥. -/
noncomputable abbrev epsilonOrZeroMaxZPS : ZPSemilattice EpsilonOrZero :=
  linearMaxZPS EpsilonOrZero epsilonOrZero_bot epsilonOrZero_bot_le

/-- `Statement:` ε₀ covers 0 in `EpsilonOrZero`; the `SnapCannotBe.lean` § II example, named. -/
theorem epsilonOrZero_bot_covBy_eps0 : epsilonOrZero_bot ⋖ epsilonOrZero_eps0 := by
  refine ⟨Ordinal.epsilon_pos 0, ?_⟩
  rintro ⟨c, hc | hc⟩ h0 hε
  · exact (ne_of_gt (show (0 : Ordinal) < c from h0)) hc
  · exact nothing_between_is_a_step c hε hc

/-- `Statement:` ⊥ of `EpsilonOrZero` has a first step under `epsilonOrZeroMaxZPS`. -/
theorem epsilonOrZeroMaxZPS_botHasFirstStep : @BotHasFirstStep EpsilonOrZero epsilonOrZeroMaxZPS :=
  (linearMaxZPS_botHasFirstStep_iff _ _).2 ⟨_, epsilonOrZero_bot_covBy_eps0⟩

/-- `Statement:` under `epsilonOrZeroMaxZPS`, if `w` is Martin-Löf random for `trials p hp` with
`0 < p`, some run `S` from the tape has `S 1` covering 0 with value ε₀ ≠ 0. One way. -/
theorem epsilonOrZero_snap_of_MLRandom (p : NNReal) (hp : p ≤ 1) (hp0 : 0 < p) (w : ℕ → Bool)
    (hML : MLRandom (trials p hp) w) :
    ∃ (φ : Bool → EpsilonOrZero) (hw : ∃ k, w k = true),
      epsilonOrZero_bot ⋖ (φ ∘ firedRun w hw) 1 ∧
      ((φ ∘ firedRun w hw) 1).1 = Ordinal.epsilon 0 ∧ ((φ ∘ firedRun w hw) 1).1 ≠ (0 : Ordinal) := by
  obtain ⟨φ, hw, -, hcov, h1⟩ := linearMaxZPS_snap_target epsilonOrZero_bot epsilonOrZero_bot_le _
    epsilonOrZero_bot_covBy_eps0 p hp hp0 w hML
  exact ⟨φ, hw, hcov, congrArg Subtype.val h1, by rw [h1]; exact epsilon0_ne_zero⟩

-- `Statement:` CONTROL, non-vacuity: `EpsilonOrZero` holds ε₁, distinct from 0 and ε₀ and above ε₀;
-- ε₁ does not cover 0, and 0 has exactly one cover.
example : epsilonOrZero_eps1 ≠ epsilonOrZero_bot ∧ epsilonOrZero_eps0 < epsilonOrZero_eps1 ∧
    ¬ epsilonOrZero_bot ⋖ epsilonOrZero_eps1 ∧ ∃! a : EpsilonOrZero, epsilonOrZero_bot ⋖ a := by
  have h01 : Ordinal.epsilon.{0} 0 < Ordinal.epsilon 1 :=
    Ordinal.veblen_right_strictMono 1 zero_lt_one
  refine ⟨fun h => (Ordinal.epsilon_pos 1).ne' (congrArg Subtype.val h), h01,
    fun h => h.2 epsilonOrZero_bot_covBy_eps0.1 h01, ?_⟩
  exact axb1_gives_unique_target epsilonOrZero_bot ⟨_, epsilonOrZero_bot_covBy_eps0⟩

/-! ## § IV. The relation: `EpsilonOrZero` ≃o the landings of `phaseUpAndOver.up` -/

/-- `Statement:` the closed points (landings) of `phaseUpAndOver.up` in `WithBot Ordinal`. -/
abbrev PhaseLanding : Type 1 := {x : WithBot Ordinal.{0} // phaseUpAndOver.up x = x}

/-- `Statement:` on `↑o`, `phaseUpAndOver.up` is `↑(nfp (ω^·) o)`. -/
theorem phaseUp_coe (o : Ordinal.{0}) : phaseUpAndOver.up (o : WithBot Ordinal) =
    ((Ordinal.nfp (fun a => Ordinal.omega0 ^ a) o : Ordinal) : WithBot Ordinal) := rfl

/-- `Statement:` `phaseUpAndOver.up` fixes ⊥ of `WithBot Ordinal`. -/
theorem phaseUp_bot : phaseUpAndOver.up (⊥ : WithBot Ordinal.{0}) = ⊥ := rfl

open Classical in
/-- `Statement:` 0 of `Ordinal` to ⊥ of `WithBot Ordinal`, each fixed point `o` to `↑o`. -/
noncomputable def epsilonOrZeroToLanding : EpsilonOrZero → PhaseLanding := fun x =>
  if h : x.1 = 0 then ⟨⊥, phaseUp_bot⟩
  else ⟨(x.1 : WithBot Ordinal), by rw [phaseUp_coe, Ordinal.nfp_eq_self (x.2.resolve_left h)]⟩

/-- `Statement:` `epsilonOrZeroToLanding` is strictly monotone. -/
theorem epsilonOrZeroToLanding_strictMono : StrictMono epsilonOrZeroToLanding := by
  intro a b hab
  have hb : b.1 ≠ 0 := (lt_of_le_of_lt (zero_le (a := a.1)) hab).ne'
  by_cases ha : a.1 = 0
  · simp only [epsilonOrZeroToLanding, ha, hb, ↓reduceDIte]
    exact WithBot.bot_lt_coe _
  · simp only [epsilonOrZeroToLanding, ha, hb, ↓reduceDIte]
    exact WithBot.coe_lt_coe.2 hab

/-- `Statement:` `epsilonOrZeroToLanding` is onto. -/
theorem epsilonOrZeroToLanding_surjective : Function.Surjective epsilonOrZeroToLanding := by
  rintro ⟨x, hx⟩
  induction x using WithBot.recBotCoe with
  | bot => exact ⟨epsilonOrZero_bot, by simp [epsilonOrZeroToLanding, epsilonOrZero_bot]⟩
  | coe o =>
    rw [phaseUp_coe] at hx
    have ha : Ordinal.nfp (fun a => Ordinal.omega0 ^ a) o = o := WithBot.coe_injective hx
    have hfp : Ordinal.omega0 ^ o = o := by
      have := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) o
      rwa [ha] at this
    have ho : o ≠ 0 := fun h => bot_is_not_a_step (h ▸ hfp)
    exact ⟨⟨o, Or.inr hfp⟩, by simp [epsilonOrZeroToLanding, ho]⟩

/-- `Statement:` the order isomorphism `EpsilonOrZero ≃o PhaseLanding`. -/
noncomputable def epsilonOrZeroIsoLanding : EpsilonOrZero ≃o PhaseLanding :=
  StrictMono.orderIsoOfSurjective epsilonOrZeroToLanding epsilonOrZeroToLanding_strictMono
    epsilonOrZeroToLanding_surjective

/-- `Statement:` the iso sends 0 of `Ordinal` to ⊥ of `WithBot Ordinal` (not to `↑0`) and ε₀ to
`↑ε₀`, and carries the cover `0 ⋖ ε₀` to a cover among the landings. -/
theorem epsilonOrZeroIsoLanding_spec :
    (epsilonOrZeroIsoLanding epsilonOrZero_bot).1 = ⊥ ∧
    (epsilonOrZeroIsoLanding epsilonOrZero_eps0).1 =
      ((Ordinal.epsilon 0 : Ordinal) : WithBot Ordinal) ∧
    epsilonOrZeroIsoLanding epsilonOrZero_bot ⋖ epsilonOrZeroIsoLanding epsilonOrZero_eps0 := by
  refine ⟨?_, ?_, (apply_covBy_apply_iff epsilonOrZeroIsoLanding).2 epsilonOrZero_bot_covBy_eps0⟩
  · show (epsilonOrZeroToLanding epsilonOrZero_bot).1 = ⊥
    simp [epsilonOrZeroToLanding, epsilonOrZero_bot]
  · show (epsilonOrZeroToLanding epsilonOrZero_eps0).1 = _
    have h : (epsilonOrZero_eps0.1 : Ordinal) ≠ 0 := (Ordinal.epsilon_pos 0).ne'
    simp only [epsilonOrZeroToLanding, h, ↓reduceDIte]
    rfl

-- `Statement:` CONTROL: the inclusion `o ↦ ↑o` sends 0 of `Ordinal` to `↑0`, not to ⊥ of
-- `WithBot Ordinal`, and does not preserve the cover: `↑1` lies between `↑0` and `↑ε₀`.
example : ¬ ((0 : Ordinal.{0}) : WithBot Ordinal) ⋖ ((Ordinal.epsilon 0 : Ordinal) : WithBot Ordinal) :=
  fun h => h.2 (c := ((1 : Ordinal) : WithBot Ordinal)) (WithBot.coe_lt_coe.2 zero_lt_one)
    (WithBot.coe_lt_coe.2 (lt_trans Ordinal.one_lt_omega0 (Ordinal.omega0_lt_epsilon 0)))

/-- `Statement:` (i) `up` sends the snap `↑0` to `↑ε₀`, and ε₀ is the tower's supremum; (ii) ε₀,
the cover of 0 in `EpsilonOrZero`, is the least fixed point of `ω^·`; (iii) the iso sends that
cover to `up`'s landing from the snap. `Reading:` the supremum face and the least-fixed-point face
of `epsilon0_min_eq_max`, one per carrier, related by the iso; neither face replaces the other. -/
theorem snap_epsilon0_two_faces :
    (phaseUpAndOver.up (phaseEquivWithBot snap) = ((epsilonZero : Ordinal.{0}) : WithBot Ordinal) ∧
      epsilonZero = ⨆ n : ℕ, fundamentalSeq.{0} n) ∧
    (epsilonOrZero_bot ⋖ epsilonOrZero_eps0 ∧ epsilonOrZero_eps0.1 = epsilonZero ∧
      IsLeast {o : Ordinal.{0} | Ordinal.omega0 ^ o = o} epsilonZero.{0}) ∧
    (epsilonOrZeroIsoLanding epsilonOrZero_eps0).1 = phaseUpAndOver.up (phaseEquivWithBot snap) :=
  ⟨⟨phaseUp_snap, epsilon0_min_eq_max.{0, 0}.1⟩,
    ⟨epsilonOrZero_bot_covBy_eps0, rfl, epsilon0_min_eq_max.{0, 0}.2⟩,
    epsilonOrZeroIsoLanding_spec.2.1.trans phaseUp_snap.symm⟩

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms linearMaxZPS
#print axioms linearMaxZPS_lt_iff
#print axioms linearMaxZPS_covBy_iff
#print axioms linearMaxZPS_botHasFirstStep_iff
#print axioms linearMaxZPS_snap_target
#print axioms phaseMaxZPS
#print axioms phaseMaxZPS_botHasFirstStep
#print axioms phase_snap_of_MLRandom
#print axioms EpsilonOrZero
#print axioms epsilonOrZero_bot
#print axioms epsilonOrZero_eps0
#print axioms epsilonOrZero_eps1
#print axioms epsilonOrZero_bot_le
#print axioms epsilonOrZeroMaxZPS
#print axioms epsilonOrZero_bot_covBy_eps0
#print axioms epsilonOrZeroMaxZPS_botHasFirstStep
#print axioms epsilonOrZero_snap_of_MLRandom
#print axioms PhaseLanding
#print axioms phaseUp_coe
#print axioms phaseUp_bot
#print axioms epsilonOrZeroToLanding
#print axioms epsilonOrZeroToLanding_strictMono
#print axioms epsilonOrZeroToLanding_surjective
#print axioms epsilonOrZeroIsoLanding
#print axioms epsilonOrZeroIsoLanding_spec
#print axioms snap_epsilon0_two_faces

end PurityCheck
