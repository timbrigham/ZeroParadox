-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): each of the four conjuncts of T-H3 (`th3_snap_all_functors`) read as a fact about a die `Motion` on its own carrier, each fit beside a failing control and a second chart (a reversed motion for (A), (B), (C); an order dual for (A); a swap of summands for (C); a swap of basis vectors for (D)), and two obstructions (not identities) relating conjunct (A) to (B) and (A) to (D) through maps of carriers. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.CategoricalBridge
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Valuation.BranchingSnapChain
import ZeroParadox.Die
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Tactic

/-!
# T-H3 in the die: four conjuncts as facts about motions, with controls and two obstructions

Experimental probe, not a finalized layer; results are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

I never used the term face of the snap, and I wanted to know what it was trying to represent. My read was that it's basically a prototype of the die, so we ran a probe to see if that holds up.

---

Formal Overview (AI-assisted) and prior art: the ride-along `TH3Die.md`.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open ZPSemilattice

/-! ## § I. (A) `MachinePhase`: `join c₀ c₁ = c₁` -/

/-- `Statement:` UP `a ↦ join a c₁`, OVER its graph `b = join a c₁`. -/
def th3JoinUpMotion : Motion MachinePhase :=
  Motion.ofTotal (fun a => join a c₁) (by intro x; cases x <;> rfl) (fun a b => b = join a c₁)

/-- `Statement:` `c₁` is an UP value at `c₀` in `th3JoinUpMotion` iff `join c₀ c₁ = c₁`; both
    directions, so conjunct (A) is equivalent to this membership. -/
theorem th3_A_iff : c₁ ∈ th3JoinUpMotion.up c₀ ↔ join c₀ c₁ = c₁ :=
  Part.mem_some_iff.trans eq_comm

/-- `Statement:` in `th3JoinUpMotion`, `c₀` goes UP to `c₁`, `c₁` is the only landing, `c₀` steps
    to a point other than itself, and `c₁` steps to itself only. -/
theorem th3_A_fit : c₁ ∈ th3JoinUpMotion.up c₀ ∧ (∀ y, th3JoinUpMotion.IsLanding y ↔ y = c₁) ∧
    th3JoinUpMotion.LeavesAt c₀ ∧ th3JoinUpMotion.SelfOnlyAt c₁ := by
  refine ⟨th3_A_iff.2 t_snap_machine, ?_, ⟨c₁, t_snap_machine.symm, by decide⟩, ⟨rfl, ?_⟩⟩
  · intro y
    show y ∈ Part.some (join y c₁) ↔ _
    rw [Part.mem_some_iff]
    cases y <;> decide
  · intro b hb
    exact hb

/-- `Statement:` `c₀` steps to `c₁` in `machineJoinMotion` (OVER `a → join a z`). -/
theorem th3_A_step_machineJoin : machineJoinMotion.step c₀ c₁ :=
  ⟨c₁, t_snap_machine.symm⟩

/-- `Statement:` CONTROL, same carrier: with UP the identity, or UP constant at `c₀`, `c₁` is not an
    UP value at `c₀`. -/
theorem th3_A_control :
    c₁ ∉ (Motion.ofTotal (id : MachinePhase → MachinePhase) (fun _ => rfl) (fun _ _ => False)).up c₀ ∧
    c₁ ∉ (Motion.ofTotal (fun _ : MachinePhase => c₀) (fun _ => rfl) (fun _ _ => False)).up c₀ := by
  constructor <;> (intro h; rw [Motion.ofTotal, Part.mem_some_iff] at h; exact absurd h (by decide))

/-- `Statement:` CONTROL for the step reading: in `Motion.ofFun id`, `c₀` does not step to `c₁`. -/
theorem th3_A_step_control : ¬ (Motion.ofFun (id : MachinePhase → MachinePhase)).step c₀ c₁ := by
  intro h; exact absurd (show c₁ = c₀ from h) (by decide)

/-- `Statement:` the reversed motion: `c₀` has no step (nothing steps into `c₀` forwards), and `c₁`
    steps to both `c₀` and `c₁` (fan-in run backwards). -/
theorem th3_A_reverse : th3JoinUpMotion.reverse.NoStepAt c₀ ∧
    th3JoinUpMotion.reverse.step c₁ c₀ ∧ th3JoinUpMotion.reverse.step c₁ c₁ := by
  refine ⟨?_, rfl, rfl⟩
  intro b h
  change c₀ = join b c₁ at h
  cases b <;> exact absurd h (by decide)

/-- `Statement:` the order-dual chart, supplied by hand (`ZPSemilattice` carries no meet): UP
    constant at `c₀`, OVER its graph. -/
def th3MeetUpMotion : Motion MachinePhase :=
  Motion.ofTotal (fun _ => c₀) (fun _ => rfl) (fun _ b => b = c₀)

/-- `Statement:` in `th3MeetUpMotion`, `c₀` is an UP value at `c₁` and `c₀` is the only landing. -/
theorem th3_A_dual : c₀ ∈ th3MeetUpMotion.up c₁ ∧ (∀ y, th3MeetUpMotion.IsLanding y ↔ y = c₀) := by
  refine ⟨Part.mem_some _, fun y => ?_⟩
  show y ∈ Part.some c₀ ↔ _
  exact Part.mem_some_iff

/-! ## § II. (B) `Q₂`: no continuous path from `x ≠ 0` to `0` -/

/-- `Statement:` the path motion on a space `X`: UP the identity, OVER Mathlib's `Joined` (a
    continuous path on the unit interval from `x` to `y`). -/
def th3PathMotion (X : Type*) [TopologicalSpace X] : Motion X :=
  Motion.ofTotal id (fun _ => rfl) Joined

/-- `Statement:` CARRIER — in a totally disconnected space, joined points are equal; from
    `disconnectedness_forbids_path`. -/
theorem th3_joined_eq {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X] {x y : X}
    (h : Joined x y) : x = y := by
  by_contra hxy
  obtain ⟨γ⟩ := h
  exact disconnectedness_forbids_path hxy ⟨γ.toContinuousMap, γ.source, γ.target⟩

/-- `Statement:` conjunct (B) as a die fact, from `c3_irreversible`: in the path motion on `Q₂`,
    every step into `0` starts at `0`. -/
theorem th3_B_fit : ∀ x : Q₂, (th3PathMotion Q₂).step x 0 → x = 0 := by
  intro x h
  by_contra hx
  obtain ⟨γ⟩ := (h : Joined x 0)
  exact c3_irreversible x hx ⟨γ.toContinuousMap, γ.source, γ.target⟩

/-- `Statement:` in the path motion on `Q₂`, EVERY point steps to itself only. `Reading:` the role
    `SelfOnlyAt` is occupied at every point of `Q₂`, so (B) does not single out `0`. -/
theorem th3_B_every_point_selfOnly (y : Q₂) : (th3PathMotion Q₂).SelfOnlyAt y :=
  ⟨Joined.refl y, fun _ hb => (th3_joined_eq hb).symm⟩

/-- `Statement:` INVARIANT under reversal: in the reversed path motion on `Q₂`, every step into `0`
    starts at `0`; it agrees with `th3_B_fit` because `Joined` is symmetric (`Joined.symm`). -/
theorem th3_B_reverse : ∀ x : Q₂, (th3PathMotion Q₂).reverse.step x 0 → x = 0 :=
  fun _ h => (th3_joined_eq h).symm

/-- `Statement:` CONTROL (ℝ): in the path motion on ℝ, `1` steps to `0`, so `th3_B_fit`'s shape
    fails there. -/
theorem th3_B_control_real : ¬ ∀ x : ℝ, (th3PathMotion ℝ).step x 0 → x = 0 :=
  fun h => one_ne_zero (h 1 (PathConnectedSpace.joined 1 0))

/-- `Statement:` CONTROL, same carrier `Q₂`: with the always-true OVER the shape fails. -/
theorem th3_B_control_Q2 :
    ¬ ∀ x : Q₂, (Motion.ofTotal (id : Q₂ → Q₂) (fun _ => rfl) (fun _ _ => True)).step x 0 → x = 0 :=
  fun h => one_ne_zero (h 1 trivial)

/-! ## § III. (C) `JSD(P, Q) = log 2` — a fit as DATA -/

/-- `Statement:` UP constant at the mixture `mixtureM`, OVER the single step `P_real → Q_real`. -/
noncomputable def th3MixMotion : Motion (BinaryState → ℝ) :=
  Motion.ofTotal (fun _ => mixtureM) (fun _ => rfl) (fun p q => p = P_real ∧ q = Q_real)

/-- `Statement:` a property defined HERE, not die vocabulary: the mean KL divergence from `P_real`
    and `Q_real` to their UP values is `log 2`. -/
def Th3JsdAlong (M : Motion (BinaryState → ℝ)) : Prop :=
  ∀ mp ∈ M.up P_real, ∀ mq ∈ M.up Q_real,
    (1 / 2) * klDiv P_real mp + (1 / 2) * klDiv Q_real mq = Real.log 2

/-- `Statement:` `P_real` steps to `Q_real`, both go UP to `mixtureM`, and `Th3JsdAlong` holds.
    `Reading:` this fits only as DATA: the mixture is supplied as UP by hand and the quantity is a
    property defined in this file; no die premise computes either. -/
theorem th3_C_fit : th3MixMotion.step P_real Q_real ∧ mixtureM ∈ th3MixMotion.up P_real ∧
    mixtureM ∈ th3MixMotion.up Q_real ∧ Th3JsdAlong th3MixMotion := by
  refine ⟨⟨rfl, rfl⟩, Part.mem_some _, Part.mem_some _, ?_⟩
  intro mp hp mq hq
  simp only [th3MixMotion, Motion.ofTotal, Part.mem_some_iff] at hp hq
  subst hp hq
  exact t1b_jsd

/-- `Statement:` CONTROL, same carrier and step: with UP the identity, `Th3JsdAlong` fails. -/
theorem th3_C_control :
    ¬ Th3JsdAlong (Motion.ofTotal id (fun _ => rfl) (fun p q => p = P_real ∧ q = Q_real)) := by
  intro h
  have := h P_real (Part.mem_some _) Q_real (Part.mem_some _)
  have hP : klDiv P_real P_real = 0 := by simp [klDiv, P_real, nullSt]
  have hQ : klDiv Q_real Q_real = 0 := by simp [klDiv, Q_real, firstSt]
  rw [hP, hQ] at this
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- `Statement:` INVARIANT under swapping `P` and `Q` in the sum: summed in the order `Q`, then `P`,
    the value is the same. -/
theorem th3_C_reverse : ∀ mq ∈ th3MixMotion.up Q_real, ∀ mp ∈ th3MixMotion.up P_real,
    (1 / 2) * klDiv Q_real mq + (1 / 2) * klDiv P_real mp = Real.log 2 :=
  fun mq hq mp hp => by rw [add_comm]; exact th3_C_fit.2.2.2 mp hp mq hq

/-- `Statement:` INVARIANT under reversal: `Th3JsdAlong` holds for the reversed motion
    `th3MixMotion.reverse`, which keeps UP. -/
theorem th3_C_reverse_motion : Th3JsdAlong th3MixMotion.reverse :=
  th3_C_fit.2.2.2

/-! ## § IV. (D) `StateSpace n`: `⟪T 0, T 1⟫ = 0` -/

section D
variable (n : ℕ) (hn : 2 ≤ n)

/-- `Statement:` `transitionOp n` at index `0`. -/
noncomputable def th3E0 : StateSpace n := transitionOp n ⟨0, by omega⟩

/-- `Statement:` `transitionOp n` at index `1`. -/
noncomputable def th3E1 : StateSpace n := transitionOp n ⟨1, by omega⟩

/-- `Statement:` UP the orthogonal projection onto the complex line `ℂ ∙ u`, OVER `s`. -/
noncomputable def th3ProjMotion (u : StateSpace n) (s : StateSpace n → StateSpace n → Prop) :
    Motion (StateSpace n) :=
  Motion.ofTotal (ℂ ∙ u).starProjection
    (fun x => congrArg (fun f : StateSpace n →L[ℂ] StateSpace n => f x)
      (ℂ ∙ u).isIdempotentElem_starProjection) s

/-- `Statement:` `th3E0 n hn` is not the zero vector. -/
theorem th3_e0_ne_zero : th3E0 n hn ≠ 0 := by
  intro h
  have := t2_norm_eq_one n ⟨0, by omega⟩
  rw [show transitionOp n ⟨0, by omega⟩ = th3E0 n hn from rfl, h, norm_zero] at this
  exact zero_ne_one this

/-- `Statement:` `th3E1 n hn` is not the zero vector. -/
theorem th3_e1_ne_zero : th3E1 n hn ≠ 0 := by
  intro h
  have := t2_norm_eq_one n ⟨1, by omega⟩
  rw [show transitionOp n ⟨1, by omega⟩ = th3E1 n hn from rfl, h, norm_zero] at this
  exact zero_ne_one this

/-- `Statement:` in the projection motion onto `ℂ ∙ th3E0`, `v` goes UP to the zero vector iff
    `⟪th3E0, v⟫ = 0`; both directions. -/
theorem th3_D_up_zero_iff (s : StateSpace n → StateSpace n → Prop) (v : StateSpace n) :
    (0 : StateSpace n) ∈ (th3ProjMotion n (th3E0 n hn) s).up v ↔
      @inner ℂ (StateSpace n) _ (th3E0 n hn) v = 0 := by
  show (0 : StateSpace n) ∈ Part.some ((ℂ ∙ th3E0 n hn).starProjection v) ↔ _
  rw [Part.mem_some_iff, Submodule.starProjection_singleton,
    show ‖th3E0 n hn‖ = 1 from t2_norm_eq_one n _]
  simp [th3_e0_ne_zero n hn, eq_comm]

/-- `Statement:` conjunct (D) as a die fact, from `t4_snap_orthogonal`: `th3E0` is a landing and
    `th3E1` goes UP to the zero vector. -/
theorem th3_D_fit (s : StateSpace n → StateSpace n → Prop) :
    (th3ProjMotion n (th3E0 n hn) s).IsLanding (th3E0 n hn) ∧
      (0 : StateSpace n) ∈ (th3ProjMotion n (th3E0 n hn) s).up (th3E1 n hn) := by
  refine ⟨?_, (th3_D_up_zero_iff n hn s _).2 (t4_snap_orthogonal n hn)⟩
  show th3E0 n hn ∈ Part.some ((ℂ ∙ th3E0 n hn).starProjection (th3E0 n hn))
  rw [Part.mem_some_iff,
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _)]

/-- `Statement:` with OVER the single step `th3E0 → th3E1`, the projection motion climbs: `th3E1`
    goes UP to the zero vector, which is neither `th3E1` nor `th3E0`. -/
theorem th3_D_climb :
    (th3ProjMotion n (th3E0 n hn) (fun a b => a = th3E0 n hn ∧ b = th3E1 n hn)).Climb :=
  ⟨th3E0 n hn, th3E1 n hn, 0, (th3_D_fit n hn _).1, ⟨rfl, rfl⟩, (th3_D_fit n hn _).2,
    (th3_e1_ne_zero n hn).symm, (th3_e0_ne_zero n hn).symm⟩

/-- `Statement:` the projection onto `ℂ ∙ th3E0` fixes `th3E0`. -/
theorem th3_proj_e0_e0 : (ℂ ∙ th3E0 n hn).starProjection (th3E0 n hn) = th3E0 n hn :=
  Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_span_singleton_self _)

/-- `Statement:` the projection onto `ℂ ∙ th3E0` sends `th3E1` to the zero vector. -/
theorem th3_proj_e0_e1 : (ℂ ∙ th3E0 n hn).starProjection (th3E1 n hn) = 0 := by
  have := (th3_D_up_zero_iff n hn (fun _ _ => False) (th3E1 n hn)).2 (t4_snap_orthogonal n hn)
  exact (Part.mem_some_iff.1 this).symm

/-- `Statement:` CONTROL, same carrier: with the non-orthogonal `th3E0 + th3E1` in place of
    `th3E1`, the step loops (UP returns to `th3E0`) and does not climb. -/
theorem th3_D_control :
    let w := th3E0 n hn + th3E1 n hn
    let M := th3ProjMotion n (th3E0 n hn) (fun a b => a = th3E0 n hn ∧ b = w)
    M.Loop ∧ ¬ M.Climb := by
  intro w M
  have hw : (ℂ ∙ th3E0 n hn).starProjection w = th3E0 n hn := by
    simp only [w, map_add, th3_proj_e0_e0, th3_proj_e0_e1, add_zero]
  have hwne : w ≠ th3E0 n hn := by
    intro h; apply th3_e1_ne_zero n hn
    have : th3E0 n hn + th3E1 n hn = th3E0 n hn + 0 := by rw [add_zero]; exact h
    exact add_left_cancel this
  refine ⟨⟨th3E0 n hn, w, (th3_D_fit n hn _).1, ⟨rfl, rfl⟩, hwne, ?_⟩, ?_⟩
  · show th3E0 n hn ∈ Part.some ((ℂ ∙ th3E0 n hn).starProjection w)
    rw [hw]; exact Part.mem_some _
  · rintro ⟨y, b, z, -, ⟨rfl, rfl⟩, hz, -, hzy⟩
    apply hzy
    have : z = (ℂ ∙ th3E0 n hn).starProjection w := Part.mem_some_iff.1 hz
    rw [this, hw]

/-- `Statement:` CONTROL (UP the identity): `th3E1` does not go UP to the zero vector. -/
theorem th3_D_control_id :
    (0 : StateSpace n) ∉ (Motion.ofTotal (id : StateSpace n → StateSpace n) (fun _ => rfl)
      (fun _ _ => False)).up (th3E1 n hn) := by
  intro h
  exact th3_e1_ne_zero n hn (Part.mem_some_iff.1 h).symm

/-- `Statement:` INVARIANT under swapping the indices: projecting onto `ℂ ∙ th3E1`, `th3E0` goes UP
    to the zero vector (conjugate symmetry of the inner product). -/
theorem th3_D_swap (s : StateSpace n → StateSpace n → Prop) :
    (0 : StateSpace n) ∈ (th3ProjMotion n (th3E1 n hn) s).up (th3E0 n hn) := by
  show (0 : StateSpace n) ∈ Part.some ((ℂ ∙ th3E1 n hn).starProjection (th3E0 n hn))
  have h : @inner ℂ (StateSpace n) _ (th3E1 n hn) (th3E0 n hn) = 0 :=
    inner_eq_zero_symm.mp (t4_snap_orthogonal n hn)
  rw [Part.mem_some_iff, Submodule.starProjection_singleton, h]
  simp

end D

/-! ## § V. Obstructions: (A) with (B), (A) with (D). No cross-carrier equation is stated. -/

/-- `Statement:` CARRIER — in any totally disconnected space `X`, a map `MachinePhase → X` carrying each step of
    `machineJoinMotion` to a step of the path motion sends `c₀` and `c₁` to the same point. (A)
    supplies the step `c₀ → c₁` (`t_snap_machine`); joined points are equal (`th3_joined_eq`). -/
theorem th3_AB_collapse_any {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X]
    (f : MachinePhase → X)
    (hf : ∀ a b, machineJoinMotion.step a b → (th3PathMotion X).step (f a) (f b)) :
    f c₀ = f c₁ :=
  th3_joined_eq (hf c₀ c₁ ⟨c₁, t_snap_machine.symm⟩)

/-- `Statement:` a map `MachinePhase → Q₂` carrying each step of `machineJoinMotion` to a path step
    and putting `c₁` at `0` also puts `c₀` at `0`. It is the instance at `0` of
    `th3_AB_collapse_any`; the `0` is not used. (A) supplies the step `c₀ → c₁`
    (`t_snap_machine`); (B) forbids its image (`c3_irreversible`, via `th3_B_fit`). -/
theorem th3_AB_collapse (f : MachinePhase → Q₂)
    (hf : ∀ a b, machineJoinMotion.step a b → (th3PathMotion Q₂).step (f a) (f b))
    (h1 : f c₁ = 0) : f c₀ = 0 := by
  have hs := hf c₀ c₁ ⟨c₁, t_snap_machine.symm⟩
  rw [h1] at hs
  exact th3_B_fit (f c₀) hs

/-- `Statement:` the `snapEmbed` assignment (`c₀ ↦ 1`, `c₁ ↦ 0`), read in `Q₂`, does not carry the
    join steps to path steps. -/
theorem th3_AB_snapEmbed_not_path :
    ¬ ∀ a b, machineJoinMotion.step a b →
      (th3PathMotion Q₂).step ((snapEmbed a : ℤ_[2]) : Q₂) ((snapEmbed b : ℤ_[2]) : Q₂) := by
  intro hf
  have := th3_AB_collapse (fun a => ((snapEmbed a : ℤ_[2]) : Q₂)) hf (by simp)
  simp at this

/-- `Statement:` CARRIER — CONTROL (ℝ): the assignment `c₀ ↦ 1`, `c₁ ↦ 0` into ℝ carries every join step to a
    path step. What `th3_AB_collapse` consumes beyond (A) is that joined points are equal
    (`th3_joined_eq`, total disconnectedness), which ℝ lacks. -/
theorem th3_AB_control_real :
    ∀ a b, machineJoinMotion.step a b →
      (th3PathMotion ℝ).step
        ((fun p : MachinePhase => match p with | .initial => (1 : ℝ) | .running => 0) a)
        ((fun p : MachinePhase => match p with | .initial => (1 : ℝ) | .running => 0) b) :=
  fun _ _ _ => PathConnectedSpace.joined _ _

/-- `Statement:` CONTROL, same carrier `Q₂`: with the always-true OVER in place of `Joined`, the
    `snapEmbed` assignment (`c₀ ↦ 1`, `c₁ ↦ 0`) carries every join step. -/
theorem th3_AB_control_Q2 :
    ∀ a b, machineJoinMotion.step a b →
      (Motion.ofTotal (id : Q₂ → Q₂) (fun _ => rfl) (fun _ _ => True)).step
        ((snapEmbed a : ℤ_[2]) : Q₂) ((snapEmbed b : ℤ_[2]) : Q₂) :=
  fun _ _ _ => trivial

/-- `Statement:` no map `MachinePhase → StateSpace n` with `c₀ ↦ th3E1`, `c₁ ↦ th3E0` satisfies the
    lax UP square from `th3JoinUpMotion` to the projection motion onto `ℂ ∙ th3E0`. -/
theorem th3_AD_no_upLax (n : ℕ) (hn : 2 ≤ n) (s : StateSpace n → StateSpace n → Prop) :
    ¬ ∃ f : MachinePhase → StateSpace n, f c₀ = th3E1 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  rintro ⟨f, h0, h1, hf⟩
  have h := hf c₀ c₁ (th3_A_iff.2 t_snap_machine)
  rw [h0, h1] at h
  have h' : th3E0 n hn = (ℂ ∙ th3E0 n hn).starProjection (th3E1 n hn) := Part.mem_some_iff.1 h
  rw [th3_proj_e0_e1] at h'
  exact th3_e0_ne_zero n hn h'

/-- `Statement:` for any `v` whose projection onto `ℂ ∙ th3E0` is not `th3E0`, no map
    `MachinePhase → StateSpace n` with `c₀ ↦ v`, `c₁ ↦ th3E0` satisfies the lax UP square from
    `th3JoinUpMotion` to the projection motion onto `ℂ ∙ th3E0`. -/
theorem th3_AD_no_upLax_of_proj_ne (n : ℕ) (hn : 2 ≤ n) (s : StateSpace n → StateSpace n → Prop)
    (v : StateSpace n) (hv : (ℂ ∙ th3E0 n hn).starProjection v ≠ th3E0 n hn) :
    ¬ ∃ f : MachinePhase → StateSpace n, f c₀ = v ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  rintro ⟨f, h0, h1, hf⟩
  have h := hf c₀ c₁ (th3_A_iff.2 t_snap_machine)
  rw [h0, h1] at h
  have h' : th3E0 n hn = (ℂ ∙ th3E0 n hn).starProjection v := Part.mem_some_iff.1 h
  exact hv h'.symm

/-- `Statement:` CONTROL: with `th3E0 + th3E1` in place of `th3E1` such a map exists. What
    `th3_AD_no_upLax` consumes is the hypothesis of `th3_AD_no_upLax_of_proj_ne`: the projection
    of `f c₀` onto `ℂ ∙ th3E0` is not `th3E0`. (D) supplies it for `th3E1` and the proof routes
    through `t4_snap_orthogonal`; the hypothesis is weaker than orthogonality (next `example`). -/
theorem th3_AD_control (n : ℕ) (hn : 2 ≤ n) (s : StateSpace n → StateSpace n → Prop) :
    ∃ f : MachinePhase → StateSpace n, f c₀ = th3E0 n hn + th3E1 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  refine ⟨fun p => match p with | .initial => th3E0 n hn + th3E1 n hn | .running => th3E0 n hn,
    rfl, rfl, ?_⟩
  intro x y hy
  have hy' : y = join x c₁ := Part.mem_some_iff.1 hy
  subst hy'
  show _ ∈ Part.some ((ℂ ∙ th3E0 n hn).starProjection _)
  rw [Part.mem_some_iff]
  cases x
  · show th3E0 n hn = (ℂ ∙ th3E0 n hn).starProjection (th3E0 n hn + th3E1 n hn)
    rw [map_add, th3_proj_e0_e0, th3_proj_e0_e1, add_zero]
  · show th3E0 n hn = (ℂ ∙ th3E0 n hn).starProjection (th3E0 n hn)
    rw [th3_proj_e0_e0]

/-- `Statement:` `2 • th3E0` is not orthogonal to `th3E0`, and no map with `c₀ ↦ 2 • th3E0`,
    `c₁ ↦ th3E0` satisfies the lax UP square. -/
example (n : ℕ) (hn : 2 ≤ n) (s : StateSpace n → StateSpace n → Prop) :
    @inner ℂ (StateSpace n) _ (th3E0 n hn) ((2 : ℂ) • th3E0 n hn) ≠ 0 ∧
    ¬ ∃ f : MachinePhase → StateSpace n, f c₀ = (2 : ℂ) • th3E0 n hn ∧ f c₁ = th3E0 n hn ∧
      Motion.UpLax th3JoinUpMotion (th3ProjMotion n (th3E0 n hn) s) f := by
  refine ⟨?_, th3_AD_no_upLax_of_proj_ne n hn s _ ?_⟩
  · rw [inner_smul_right, inner_self_eq_norm_sq_to_K, show ‖th3E0 n hn‖ = 1 from t2_norm_eq_one n _]
    norm_num
  · rw [map_smul, th3_proj_e0_e0]
    intro h
    have h' : (2 : ℂ) • th3E0 n hn = (1 : ℂ) • th3E0 n hn := by rw [one_smul]; exact h
    have h12 := smul_left_injective ℂ (th3_e0_ne_zero n hn) h'
    norm_num at h12

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms th3JoinUpMotion
#print axioms th3_A_iff
#print axioms th3_A_fit
#print axioms th3_A_step_machineJoin
#print axioms th3_A_control
#print axioms th3_A_step_control
#print axioms th3_A_reverse
#print axioms th3MeetUpMotion
#print axioms th3_A_dual
#print axioms th3PathMotion
#print axioms th3_joined_eq
#print axioms th3_B_fit
#print axioms th3_B_every_point_selfOnly
#print axioms th3_B_reverse
#print axioms th3_B_control_real
#print axioms th3_B_control_Q2
#print axioms th3MixMotion
#print axioms Th3JsdAlong
#print axioms th3_C_fit
#print axioms th3_C_control
#print axioms th3_C_reverse
#print axioms th3_C_reverse_motion
#print axioms th3E0
#print axioms th3E1
#print axioms th3ProjMotion
#print axioms th3_e0_ne_zero
#print axioms th3_e1_ne_zero
#print axioms th3_D_up_zero_iff
#print axioms th3_D_fit
#print axioms th3_D_climb
#print axioms th3_proj_e0_e0
#print axioms th3_proj_e0_e1
#print axioms th3_D_control
#print axioms th3_D_control_id
#print axioms th3_D_swap
#print axioms th3_AB_collapse_any
#print axioms th3_AB_collapse
#print axioms th3_AB_snapEmbed_not_path
#print axioms th3_AB_control_real
#print axioms th3_AB_control_Q2
#print axioms th3_AD_no_upLax
#print axioms th3_AD_no_upLax_of_proj_ne
#print axioms th3_AD_control
end PurityCheck
