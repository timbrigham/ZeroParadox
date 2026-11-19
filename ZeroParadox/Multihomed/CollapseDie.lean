-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): one collapse lemma in two forms (a step-carrying map into a target with no other entry, or at most one successor, at the image point is constant) and the loop obstruction, with six legacy results as instances, each beside a failing control. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Multihomed.OrbitDie
import ZeroParadox.Valuation.ScaleRealization
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Category.Category
import ZeroParadox.Miniature
import Mathlib.Tactic

/-!
# The collapse family in the die: one lemma, six instances, with controls

Experimental probe, not a finalized layer; results are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

I could easily see there being an entire mid-level tier with a reasonable chance of still needing to be further reviewed. So we ranked the results, landed them, and kept going.

---

Formal Overview (AI-assisted) and prior art: the ride-along `CollapseDie.md`.
-/

set_option maxHeartbeats 400000

universe u

namespace ZeroParadox

/-! ## § 0. The collapse, in two forms, and the loop obstruction -/

/-- `Statement:` IN form: if every point has a path of steps to `y`, and every step of `N` into
    `f y` starts at `f y`, a step-carrying map is constant at `f y`. Pointwise, `od_collapse`. -/
theorem cd_collapse_in {α β : Type*} {M : Motion α} {N : Motion β} (f : α → β)
    (hf : ∀ a b, M.step a b → N.step (f a) (f b)) {y : α}
    (hy : ∀ x, Relation.ReflTransGen M.step x y) (hN : ∀ a, N.step a (f y) → a = f y) (x : α) :
    f x = f y :=
  od_collapse f hf hN (hy x)

/-- `Statement:` OUT form, local: if `f t` has at most one successor in `N`, a step-carrying map
    identifies any two successors of `t`. -/
theorem cd_fan_collapse {α β : Type*} {M : Motion α} {N : Motion β} (f : α → β)
    (hf : ∀ a b, M.step a b → N.step (f a) (f b)) {t a b : α} (ha : M.step t a) (hb : M.step t b)
    (hN : ∀ c d, N.step (f t) c → N.step (f t) d → c = d) : f a = f b :=
  hN _ _ (hf t a ha) (hf t b hb)

/-- `Statement:` OUT form: if `t` steps to every point and `f t` has at most one successor in `N`,
    a step-carrying map is constant. -/
theorem cd_collapse_out {α β : Type*} {M : Motion α} {N : Motion β} (f : α → β)
    (hf : ∀ a b, M.step a b → N.step (f a) (f b)) {t : α} (ht : ∀ b, M.step t b)
    (hN : ∀ c d, N.step (f t) c → N.step (f t) d → c = d) (a b : α) : f a = f b :=
  cd_fan_collapse f hf (ht a) (ht b) hN

/-- `Statement:` the one-step case of `cd_collapse_in`: every point steps to `t`. -/
example {α β : Type*} {M : Motion α} {N : Motion β} (f : α → β)
    (hf : ∀ a b, M.step a b → N.step (f a) (f b)) {t : α} (ht : ∀ a, M.step a t)
    (hN : ∀ b, N.step b (f t) → b = f t) (x : α) : f x = f t :=
  cd_collapse_in f hf (fun x => Relation.ReflTransGen.single (ht x)) hN x

/-- `Statement:` into a function motion the OUT form needs no hypothesis on the target. -/
example {α β : Type*} {M : Motion α} (g : β → β) (f : α → β)
    (hf : ∀ a b, M.step a b → (Motion.ofFun g).step (f a) (f b)) {t : α} (ht : ∀ b, M.step t b)
    (a b : α) : f a = f b :=
  cd_collapse_out f hf ht (fun c d (hc : c = g (f t)) (hd : d = g (f t)) => hc.trans hd.symm) a b

/-- `Statement:` the first half of the loop obstruction is `Motion.isEmpty_relHom_of_step_self`
    (`ZeroParadox/Die.lean`): no step-carrying map from a self-step into a step with none. -/
example {α β : Type*} {M : Motion α} {N : Motion β} {y : α} (hy : M.step y y)
    (hN : ∀ t, ¬ N.step t t) : IsEmpty (M.step →r N.step) :=
  Motion.isEmpty_relHom_of_step_self hy hN

/-- `Statement:` if `M` loops and every landing of `N` steps only to itself, no lax map `M → N` is
    one-to-one. -/
theorem cd_not_injective_of_loop {α β : Type*} {M : Motion α} {N : Motion β} (hM : M.Loop)
    (hN : ∀ y b, N.IsLanding y → N.step y b → b = y) (φ : Motion.LaxHom M N) :
    ¬ Function.Injective φ.toFun := fun hi => by
  obtain ⟨y, b, hy, hs, hby, _⟩ := φ.loop hi hM
  exact hby (hN y b hy hs)

/-! ## § I. T-IZ (`t_iz_complete`): the join step into doubling -/

/-- `Statement:` the join-step motion on a `ZPSemilattice`: UP the identity, OVER `a → join a z`. -/
def cdJoinStep (L : Type*) [ZPSemilattice L] : Motion L :=
  Motion.ofTotal id (fun _ => rfl) (fun a b => ∃ z, b = ZPSemilattice.join a z)

/-- `Statement:` at `MachinePhase` it is `machineJoinMotion` (`ZeroParadox/Ordinal/Incompleteness.lean`). -/
example : cdJoinStep MachinePhase = machineJoinMotion := rfl

/-- `Statement:` the bottom of a `ZPSemilattice` steps to every point of `cdJoinStep` (A4,
    `bot_join`). -/
theorem cd_bot_steps_everywhere {L : Type*} [ZPSemilattice L] (e : L) :
    (cdJoinStep L).step ZPSemilattice.bot e :=
  ⟨e, (ZPSemilattice.bot_join e).symm⟩

/-- `Statement:` every map carrying join steps to doubling steps on `Q₂` is `0`: the OUT form at the
    bottom of `L`. -/
theorem cd_tiz_doubling_collapse {L : Type*} [ZPSemilattice L] (f : L → Q₂)
    (hf : ∀ a b, (cdJoinStep L).step a b → (Motion.ofFun (fun x : Q₂ => 2 * x)).step (f a) (f b))
    (x : L) : f x = 0 := by
  have hc := cd_collapse_out f hf (t := ZPSemilattice.bot) cd_bot_steps_everywhere
    (fun c d (hc : c = 2 * f ZPSemilattice.bot) (hd : d = 2 * f ZPSemilattice.bot) =>
      hc.trans hd.symm)
  have hself : f ZPSemilattice.bot = 2 * f ZPSemilattice.bot := hf _ _ (cd_bot_steps_everywhere _)
  rw [hc x ZPSemilattice.bot]
  linear_combination -hself

/-- `Statement:` INVARIANT under reversal: every map carrying REVERSED join steps to doubling steps
    on `Q₂` is `0`: the IN form at the bottom of `L`. -/
theorem cd_tiz_reverse_doubling_collapse {L : Type*} [ZPSemilattice L] (f : L → Q₂)
    (hf : ∀ a b, (cdJoinStep L).reverse.step a b →
      (Motion.ofFun (fun x : Q₂ => 2 * x)).step (f a) (f b)) (x : L) : f x = 0 := by
  have hself : f ZPSemilattice.bot = 2 * f ZPSemilattice.bot := hf _ _ (cd_bot_steps_everywhere _)
  have h0 : f ZPSemilattice.bot = 0 := by linear_combination -hself
  rw [cd_collapse_in f hf (y := ZPSemilattice.bot)
    (fun x => Relation.ReflTransGen.single (cd_bot_steps_everywhere x))
    (fun a (ha : f ZPSemilattice.bot = 2 * a) => by
      rw [h0] at ha ⊢; exact (mul_eq_zero.mp ha.symm).resolve_left two_ne_zero) x, h0]

/-- `Statement:` CONTROL (target not single-valued): `c₀ ↦ 1`, `c₁ ↦ 0` carries every join step of
    `MachinePhase` to the always-true OVER on `Q₂` and is not constant. -/
theorem cd_tiz_control_target :
    let f : MachinePhase → Q₂ := fun p => match p with | .initial => 1 | .running => 0
    (∀ a b, (cdJoinStep MachinePhase).step a b →
      (Motion.ofTotal (id : Q₂ → Q₂) (fun _ => rfl) (fun _ _ => True)).step (f a) (f b)) ∧
      f c₀ ≠ f c₁ := by
  intro f
  exact ⟨fun _ _ _ => trivial, by simp [f, c₀, c₁]⟩

/-- `Statement:` CONTROL (no point steps everywhere): with OVER only `c₀ → c₁`, `c₀ ↦ 1`, `c₁ ↦ 2`
    carries every step to a doubling step and is not constant. -/
theorem cd_tiz_control_source :
    let f : MachinePhase → Q₂ := fun p => match p with | .initial => 1 | .running => 2
    (∀ a b, (Motion.ofTotal (id : MachinePhase → MachinePhase) (fun _ => rfl)
        (fun a b => a = c₀ ∧ b = c₁)).step a b →
      (Motion.ofFun (fun x : Q₂ => 2 * x)).step (f a) (f b)) ∧ f c₀ ≠ f c₁ := by
  intro f
  refine ⟨?_, by simp [f, c₀, c₁]⟩
  rintro a b ⟨rfl, rfl⟩
  show f c₁ = 2 * f c₀
  simp [f, c₀, c₁]

/-- `Statement:` CONTROL (single-valued target, another fixed point): the constant map `1` carries
    every join step into `ofFun (fun _ => 1)`; the collapse holds and the value `0` does not. -/
theorem cd_tiz_control_value :
    ∀ a b, (cdJoinStep MachinePhase).step a b →
      (Motion.ofFun (fun _ : Q₂ => (1 : Q₂))).step ((fun _ => (1 : Q₂)) a) ((fun _ => (1 : Q₂)) b) :=
  fun _ _ _ => rfl

/-! ## § II. Floors (`floor_reach_separates_mu_nu`): `Nat.pred` against doubling -/

/-- `Statement:` if every point of `ofFun A` arrives at a fixed point `y` of `A`, and no fixed point
    of `B` is entered from another point, every semiconjugacy from `A` to `B` is constant at `c y`.
    The IN form for function motions. -/
theorem cd_semiconj_const {α β : Type*} (A : α → α) (B : β → β) (y : α) (hy : A y = y)
    (harr : ∀ x, (Motion.ofFun A).Arrives y x) (hB : ∀ z a, B z = z → B a = z → a = z)
    (c : α → β) (hc : Function.Semiconj c A B) (x : α) : c x = c y := by
  have hfix : B (c y) = c y := by rw [← hc y, hy]
  exact cd_collapse_in (M := Motion.ofFun A) (N := Motion.ofFun B) c
    (fun a b (h : b = A a) => show c b = B (c a) by rw [h]; exact hc a)
    (fun x => (Motion.arrives_ofFun_iff_reflTransGen A y x).1 (harr x))
    (fun a (ha : c y = B a) => hB _ a hfix ha.symm) x

/-- `Statement:` every semiconjugacy from `Nat.pred` on ℕ to doubling on `Q₂` is `0`. -/
theorem cd_pred_to_doubling_const (c : ℕ → Q₂)
    (hc : Function.Semiconj c Nat.pred (fun z => 2 * z)) (n : ℕ) : c n = 0 := by
  have h0 : c 0 = 0 := by
    have h : c 0 = 2 * c 0 := hc 0
    linear_combination -h
  rw [cd_semiconj_const Nat.pred _ 0 rfl
    (fun x => (Motion.arrives_ofFun_iff _ _ _).2 ⟨x, by rw [Nat.pred_iterate, Nat.sub_self]⟩)
    (fun z a hz ha => mul_left_cancel₀ two_ne_zero (ha.trans hz.symm)) c hc n, h0]

/-- `Statement:` CONTROL, same target carrier: a step on `Q₂` that is not one-to-one at its fixed
    point (`0 ↦ 0`, `z ↦ z - 1` elsewhere) receives the nonconstant semiconjugacy `Nat.cast`. -/
theorem cd_floor_control_target :
    letI := Classical.decEq Q₂
    Function.Semiconj (Nat.cast : ℕ → Q₂) Nat.pred (fun z => if z = 0 then 0 else z - 1) ∧
      ((1 : ℕ) : Q₂) ≠ ((0 : ℕ) : Q₂) := by
  refine ⟨fun n => ?_, by norm_num⟩
  cases n with
  | zero => simp
  | succ k =>
    simp only [Nat.pred_succ]
    split_ifs with h
    · exact absurd h (by exact_mod_cast Nat.succ_ne_zero k)
    · push_cast; ring

/-- `Statement:` CONTROL, same source carrier: with `Nat.succ` (nothing arrives at a fixed point),
    `n ↦ 2 ^ n` is a nonconstant semiconjugacy into doubling on `Q₂`. -/
theorem cd_floor_control_source :
    Function.Semiconj (fun n : ℕ => (2 : Q₂) ^ n) Nat.succ (fun z => 2 * z) ∧
      (2 : Q₂) ^ 1 ≠ (2 : Q₂) ^ 0 :=
  ⟨fun n => by simp [pow_succ, mul_comm], by norm_num⟩

/-- `Statement:` the other direction is not obstructed: `z ↦ toNat (-(valuation z))` is a
    nonconstant semiconjugacy from doubling on `Q₂` to `Nat.pred` on ℕ. -/
theorem cd_doubling_to_pred :
    Function.Semiconj (fun z : Q₂ => (-(Padic.valuation z)).toNat) (fun z => 2 * z) Nat.pred ∧
      (-(Padic.valuation (2⁻¹ : Q₂))).toNat ≠ (-(Padic.valuation (0 : Q₂))).toNat := by
  have hv2 : Padic.valuation (2 : Q₂) = 1 := by
    have := Padic.valuation_p (p := 2); exact_mod_cast this
  refine ⟨fun z => ?_, ?_⟩
  · by_cases hz : z = 0
    · subst hz; simp
    · simp only
      rw [Padic.valuation_mul two_ne_zero hz, hv2, Nat.pred_eq_sub_one]
      omega
  · have h : Padic.valuation ((2 : Q₂) * 2⁻¹) = 1 + Padic.valuation (2⁻¹ : Q₂) := by
      rw [Padic.valuation_mul two_ne_zero (inv_ne_zero two_ne_zero), hv2]
    rw [mul_inv_cancel₀ two_ne_zero, Padic.valuation_one] at h
    rw [Padic.valuation_zero]
    omega

/-! ## § III. The valuation bridge (`realization_bridges_both_valuations`) -/

/-- `Statement:` a realization sends ⊥ of `L` to `0` of `Q₂`: the self-step of `ofFun scale` at ⊥
    goes to the only fixed point of doubling (`od_selfstep_image`). -/
theorem cd_realization_bot {L : Type*} [ValBridge L] (ρ : L → Q₂)
    (hsemi : Function.Semiconj ρ ValBridge.scale (fun q => 2 * q)) : ρ ValBridge.bot = 0 :=
  od_selfstep_image (M := Motion.ofFun (ValBridge.scale (L := L)))
    (N := Motion.ofFun (fun q : Q₂ => 2 * q)) ρ
    (fun a b (h : b = ValBridge.scale a) => show ρ b = 2 * ρ a by rw [h]; exact hsemi a)
    (show ValBridge.bot = ValBridge.scale ValBridge.bot from (ValBridge.scale_bot (L := L)).symm)
    (fun z (hz : z = 2 * z) => by linear_combination -hz)

/-- `Statement:` so `ρ x ≠ 0` gives `x ≠ ⊥` of `L`. -/
theorem cd_realization_ne_bot {L : Type*} [ValBridge L] (ρ : L → Q₂)
    (hsemi : Function.Semiconj ρ ValBridge.scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0) :
    x ≠ ValBridge.bot := by
  rintro rfl
  exact hx (cd_realization_bot ρ hsemi)

/-- `Statement:` `realization_bridges_both_valuations` without its hypothesis `hxb`. -/
theorem cd_realization_bridges {L : Type*} [ValBridge L] (ρ : L → Q₂)
    (hsemi : Function.Semiconj ρ ValBridge.scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0) (n : ℕ) :
    ValBridge.val (ValBridge.scale^[n] x) = ValBridge.val x + n ∧
    (ρ (ValBridge.scale^[n] x)).valuation = (ρ x).valuation + n :=
  realization_bridges_both_valuations ρ hsemi x (cd_realization_ne_bot ρ hsemi x hx) hx n

/-- `Statement:` CONTROL: without `hsemi`, `ρ x ≠ 0` does not give `x ≠ ⊥` (constant `1` at ⊥). -/
example {L : Type*} [ValBridge L] :
    (fun _ : L => (1 : Q₂)) ValBridge.bot ≠ 0 ∧ ¬ (ValBridge.bot : L) ≠ ValBridge.bot :=
  ⟨one_ne_zero, fun h => h rfl⟩

/-- `Statement:` INVARIANT along the orbit: the offset between the two valuations is constant. -/
theorem cd_banks_offset {L : Type*} [ValBridge L] (ρ : L → Q₂)
    (hsemi : Function.Semiconj ρ ValBridge.scale (fun q => 2 * q)) (x : L) (hx : ρ x ≠ 0)
    (n : ℕ) :
    ((ValBridge.val (ValBridge.scale^[n] x)).toNat : ℤ) - (ρ (ValBridge.scale^[n] x)).valuation
      = ((ValBridge.val x).toNat : ℤ) - (ρ x).valuation := by
  have hxb := cd_realization_ne_bot ρ hsemi x hx
  obtain ⟨h1, h2⟩ := realization_bridges_both_valuations ρ hsemi x hxb hx n
  rw [h1, h2, ENat.toNat_add (val_finite_free x hxb) (ENat.natCast_ne_top n), ENat.toNat_natCast]
  push_cast
  ring

/-- `Statement:` CONTROL: with the constant realization `1` the offset moves at the first step. -/
theorem cd_banks_offset_control {L : Type*} [ValBridge L] (x : L) (hxb : x ≠ ValBridge.bot) :
    ((ValBridge.val (ValBridge.scale x)).toNat : ℤ) -
        ((fun _ : L => (1 : Q₂)) (ValBridge.scale x)).valuation
      ≠ ((ValBridge.val x).toNat : ℤ) - ((fun _ : L => (1 : Q₂)) x).valuation := by
  simp only [Padic.valuation_one]
  rw [ValBridge.val_scale x hxb, ENat.toNat_add (val_finite_free x hxb) ENat.one_ne_top]
  simp

/-- `Statement:` forward chart: every realization satisfies the back clause `Motion.StepBack`. -/
theorem cd_forward_stepBack {L : Type*} (scale : L → L) (ρ : L → Q₂)
    (hsemi : Function.Semiconj ρ scale (fun q => 2 * q)) :
    Motion.StepBack (Motion.ofFun scale) (Motion.ofFun (fun q : Q₂ => 2 * q)) ρ :=
  fun a c hc => ⟨scale a, rfl, by rw [hsemi a]; exact hc.symm⟩

/-- `Statement:` reversed chart: if `x` has no `scale`-predecessor, no map `ρ : L → Q₂` satisfies
    the back clause between the reversed motions. -/
theorem cd_reverse_no_stepBack {L : Type*} (scale : L → L) (ρ : L → Q₂) (x : L)
    (hx : ∀ y, scale y ≠ x) :
    ¬ Motion.StepBack (Motion.ofFun scale).reverse (Motion.ofFun (fun q : Q₂ => 2 * q)).reverse ρ := by
  intro h
  obtain ⟨b, hb, -⟩ := h x (ρ x / 2) (show ρ x = 2 * (ρ x / 2) by ring)
  exact hx b hb.symm

/-- `Statement:` the reversed chart on the corpus instance `ℤ_[2]`, at `1`. -/
theorem cd_reverse_no_stepBack_z2 :
    ¬ Motion.StepBack (Motion.ofFun (ValBridge.scale (L := ℤ_[2]))).reverse
      (Motion.ofFun (fun q : Q₂ => 2 * q)).reverse (fun z : ℤ_[2] => (z : Q₂)) :=
  cd_reverse_no_stepBack _ _ 1
    (no_scale_predecessor_at_val_zero (1 : ℤ_[2]) (by show q2Val (1 : ℤ_[2]) = 0; simp [q2Val]))

/-- `Statement:` CONTROL, target `ℤ_[2]` (where `1` has no half): the identity satisfies the back
    clause between the reversed motions. -/
theorem cd_reverse_control :
    Motion.StepBack (Motion.ofFun (ValBridge.scale (L := ℤ_[2]))).reverse
      (Motion.ofFun (ValBridge.scale (L := ℤ_[2]))).reverse id :=
  fun _ c hc => ⟨c, hc, rfl⟩

/-! ## § IV. T-H2 (`th2_singularity_compatibility`): the hom motion -/

section TH2
open CategoryTheory

/-- `Statement:` the hom motion of a category: UP the identity, OVER "a morphism exists". -/
def cdHomMotion (C : Type*) [Category C] : Motion C :=
  Motion.ofTotal id (fun _ => rfl) (fun X Y => Nonempty (X ⟶ Y))

/-- `Statement:` under AX-G2's shape at `I`, a run of the hom motion at `I` at time `k` was at an
    object not isomorphism-free with `I` at every time `m ≤ k`. -/
theorem cd_run_into {C : Type*} [Category C] (I : C)
    (hI : ∀ X : C, IsEmpty (X ≅ I) → IsEmpty (X ⟶ I)) {s : ℕ → C}
    (hs : (cdHomMotion C).IsRun s) {k : ℕ} (hk : s k = I) (m : ℕ) (hm : m ≤ k) :
    ¬ IsEmpty (s m ≅ I) := by
  have key : ∀ d m, m + d = k → Nonempty (s m ⟶ I) := by
    intro d
    induction d with
    | zero =>
        intro m hm
        have e : m = k := by omega
        subst e
        exact ⟨eqToHom hk⟩
    | succ d ih =>
        intro m hm
        obtain ⟨g⟩ := ih (m + 1) (by omega)
        obtain ⟨f⟩ : Nonempty (s m ⟶ s (m + 1)) := hs m
        exact ⟨f ≫ g⟩
  intro hne
  obtain ⟨f⟩ := key (k - m) m (by omega)
  exact (hI _ hne).false f

/-- `Statement:` the `ZPCategory` case, from the field `ax_g2`. -/
example {C : Type*} [Category C] [zpcat : ZPCategory C] {s : ℕ → C}
    (hs : (cdHomMotion C).IsRun s) {k : ℕ} (hk : s k = zpcat.zpInitial) (m : ℕ) (hm : m ≤ k) :
    ¬ IsEmpty (s m ≅ zpcat.zpInitial) :=
  cd_run_into _ (fun X hne => zpcat.ax_g2 X hne) hs hk m hm

/-- `Statement:` CONTROL, carrier ℕ: with the always-true OVER the run `1, 0, 0, …` reaches `0`
    from `1`, and `1` is not isomorphic to `0` in ℕ's order category. -/
theorem cd_run_into_control :
    (Motion.ofTotal (id : ℕ → ℕ) (fun _ => rfl) (fun _ _ => True)).IsRun
        (fun n => if n = 0 then 1 else 0) ∧
      IsEmpty ((1 : ℕ) ≅ 0) :=
  ⟨fun _ => trivial, ⟨fun i => by have := i.hom.down.down; omega⟩⟩

/-- `Statement:` no step-carrying map from the hom motion of an inhabited category into `ofFun succ`
    on ℕ: an identity morphism is a self-step, and `succ` has no fixed point. -/
theorem cd_no_map_to_accumulation {C : Type*} [Category C] (X : C) :
    IsEmpty ((cdHomMotion C).step →r (Motion.ofFun Nat.succ).step) :=
  Motion.isEmpty_relHom_of_step_self (y := X) ⟨𝟙 X⟩
    (fun t (h : t = Nat.succ t) => Nat.succ_ne_self t h.symm)

/-- `Statement:` including ℤ, which carries no `ZPCategory` (`no_zpcat_int`). -/
example : IsEmpty (ZPCategory ℤ) ∧ IsEmpty ((cdHomMotion ℤ).step →r (Motion.ofFun Nat.succ).step) :=
  ⟨no_zpcat_int, cd_no_map_to_accumulation (0 : ℤ)⟩

/-- `Statement:` CONTROL: into `ofFun id` the constant map is step-carrying. -/
example {C : Type*} [Category C] :
    Nonempty ((cdHomMotion C).step →r (Motion.ofFun (id : ℕ → ℕ)).step) :=
  ⟨⟨fun _ => 0, fun _ => rfl⟩⟩

end TH2

/-! ## § V. The miniature (`Miniature.shape`): arity, and the floor into the tower -/

/-- `Statement:` in the reverse of `ofFun cZero` on `Miniature.Pole`, `zero` has two distinct
    successors, one of them `zero` itself: two-way branching fits on the two-point pole. -/
theorem cd_pole_fans_two : ∃ a b : Miniature.Pole, a ≠ b ∧
    (Motion.ofFun Miniature.Pole.cZero).reverse.step .zero a ∧
    (Motion.ofFun Miniature.Pole.cZero).reverse.step .zero b :=
  ⟨.zero, .infty, by decide, rfl, rfl⟩

/-- `Statement:` `Miniature.Pole` has no three pairwise distinct points, so no three-way branching. -/
theorem cd_pole_no_three : ¬ ∃ a b c : Miniature.Pole, a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  rintro ⟨a, b, c, h1, h2, h3⟩
  cases a <;> cases b <;> cases c <;> simp_all

/-- `Statement:` every step-carrying map from `ofFun cZero` on `Miniature.Pole` into `ofFun (· + 1)`
    on `ℕ∞` is constant `⊤`: the IN form at `zero`. -/
theorem cd_floor_to_tower (φ : (Motion.ofFun Miniature.Pole.cZero).step →r
    (Motion.ofFun (fun x : ℕ∞ => x + 1)).step) (p : Miniature.Pole) : φ p = ⊤ := by
  have h0 : φ .zero = ⊤ := (Miniature.enat_fp_iff _).1
    (φ.map_rel (show (Motion.ofFun Miniature.Pole.cZero).step .zero .zero from rfl)).symm
  rw [cd_collapse_in (⇑φ) (fun a b h => φ.map_rel h) (y := Miniature.Pole.zero)
    (fun x => Relation.ReflTransGen.single
      (show (Motion.ofFun Miniature.Pole.cZero).step x .zero from rfl))
    (fun a (ha : φ .zero = a + 1) => by
      rw [h0] at ha ⊢; exact (WithTop.add_eq_top.mp ha.symm).resolve_right ENat.one_ne_top) p, h0]

/-- `Statement:` CONTROL: into `ofFun Nat.succ` on ℕ (no fixed point) there is no step-carrying map
    from `ofFun cZero`. -/
example : IsEmpty ((Motion.ofFun Miniature.Pole.cZero).step →r (Motion.ofFun Nat.succ).step) :=
  Motion.isEmpty_relHom_of_step_self (y := Miniature.Pole.zero) rfl
    (fun t (h : t = Nat.succ t) => Nat.succ_ne_self t h.symm)

/-- `Statement:` CONTROL: into `ofFun id` on `ℕ∞` the constant `0` is step-carrying, so the value `⊤`
    consumes the target's `+ 1`. -/
example : ∃ φ : (Motion.ofFun Miniature.Pole.cZero).step →r (Motion.ofFun (id : ℕ∞ → ℕ∞)).step,
    φ .zero = 0 :=
  ⟨⟨fun _ => 0, fun _ => rfl⟩, rfl⟩

/-! ## § VI. Fixed points (`both_fixed_points_exist`): the shift motion against the ordinal tower -/

section FixedPoints
open Nat.Partrec

/-- `Statement:` in `ordinalTowerMotion` a landing steps only to itself. -/
theorem cd_tower_landing_selfOnly (y b : Ordinal.{u}) (hy : ordinalTowerMotion.IsLanding y)
    (hs : ordinalTowerMotion.step y b) : b = y := by
  have h1 := (ordinalTowerMotion_isLanding_iff y).1 hy
  have h2 : b = Ordinal.omega0 ^ y := hs
  rw [h2, h1]

/-- `Statement:` for `⌜c⌝ ≠ 0` no lax map from `shiftMotion c` to `ordinalTowerMotion` is
    one-to-one (`cd_not_injective_of_loop`). -/
theorem cd_shift_tower_not_injective (c : Code) (hk : Encodable.encode c ≠ 0)
    (φ : Motion.LaxHom (shiftMotion c) ordinalTowerMotion.{u}) : ¬ Function.Injective φ.toFun :=
  cd_not_injective_of_loop (shiftMotion_loop c hk) cd_tower_landing_selfOnly φ

/-- `Statement:` every lax map from `shiftMotion c` to `ordinalTowerMotion` takes only fixed points
    of `α ↦ ω^α` and has period `⌜c⌝`, for every code `c`. -/
theorem cd_shift_tower_periodic (c : Code)
    (φ : Motion.LaxHom (shiftMotion c) ordinalTowerMotion.{u}) (n : ℕ) :
    ordinalTowerMotion.IsLanding (φ.toFun n) ∧ φ.toFun (Encodable.encode c + n) = φ.toFun n := by
  have hland : ∀ n, ordinalTowerMotion.IsLanding (φ.toFun n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < Encodable.encode c ∨ Encodable.encode c = 0
      · have hmod : n % Encodable.encode c = n := by
          rcases hn with h | h
          · exact Nat.mod_eq_of_lt h
          · rw [h, Nat.mod_zero]
        have := φ.map_up n (n % Encodable.encode c) (Part.mem_some_iff.2 rfl)
        rw [hmod] at this
        exact this
      · simp only [not_or, not_lt] at hn
        obtain ⟨m, rfl⟩ : ∃ m, n = Encodable.encode c + m := ⟨n - Encodable.encode c, by omega⟩
        have hm := ih m (by omega)
        have hs : φ.toFun (Encodable.encode c + m) = Ordinal.omega0 ^ φ.toFun m :=
          φ.map_step (a := m) (b := Encodable.encode c + m) rfl
        rw [hs, (ordinalTowerMotion_isLanding_iff _).1 hm]
        exact hm
  refine ⟨hland n, ?_⟩
  have hs : φ.toFun (Encodable.encode c + n) = Ordinal.omega0 ^ φ.toFun n :=
    φ.map_step (a := n) (b := Encodable.encode c + n) rfl
  rw [hs, (ordinalTowerMotion_isLanding_iff _).1 (hland n)]

/-- `Statement:` CONTROL for injectivity: the constant map at ε₀ (`Ordinal.epsilon 0`) is a strict
    map from `shiftMotion c` to `ordinalTowerMotion`, for every `c`. -/
noncomputable def cdConstTowerHom (c : Code) : Motion.Hom (shiftMotion c) ordinalTowerMotion.{u} where
  toFun := fun _ => Ordinal.epsilon 0
  map_step := fun _ => (Ordinal.omega0_opow_epsilon 0).symm
  map_up := fun x => by
    show Part.some (Ordinal.nfp (fun a => Ordinal.omega0 ^ a) (Ordinal.epsilon 0)) =
      (Part.some (x % Encodable.encode c)).map (fun _ => Ordinal.epsilon 0)
    rw [Part.map_some, Ordinal.nfp_eq_self (Ordinal.omega0_opow_epsilon 0)]

/-- `Statement:` CONTROL for the target hypothesis: for `⌜c⌝ ≠ 0` the identity is a one-to-one lax
    map from `shiftMotion c` to itself, and there the landing `0` steps elsewhere. -/
example (c : Code) (hk : Encodable.encode c ≠ 0) :
    Function.Injective (Motion.LaxHom.id (shiftMotion c)).toFun ∧
    ¬ ∀ y b, (shiftMotion c).IsLanding y → (shiftMotion c).step y b → b = y :=
  ⟨fun _ _ h => h, fun h => hk (by
    have := h 0 (Encodable.encode c) (Part.mem_some_iff.2 (Nat.zero_mod _).symm)
      (show Encodable.encode c = Encodable.encode c + 0 by rfl)
    exact this)⟩

/-- `Statement:` for `⌜c⌝ ≠ 0` there is no lax map from `ordinalTowerMotion` to `shiftMotion c`: a
    fixed point of `α ↦ ω^α` is a self-step, and the shift has none. -/
theorem cd_no_laxHom_tower_shift (c : Code) (hk : Encodable.encode c ≠ 0) :
    IsEmpty (Motion.LaxHom ordinalTowerMotion.{u} (shiftMotion c)) :=
  ⟨fun φ => (Motion.isEmpty_relHom_of_step_self (M := ordinalTowerMotion.{u}) (N := shiftMotion c)
    (y := Ordinal.epsilon 0) (Ordinal.omega0_opow_epsilon 0).symm
    (fun t ht => hk (by have : t = Encodable.encode c + t := ht; omega))).false
    ⟨φ.toFun, φ.map_step⟩⟩

/-- `Statement:` CONTROL, `Code.zero` (Gödel number `0`): the constant map `0` is a lax map from
    `ordinalTowerMotion` to `shiftMotion Code.zero`. -/
example : Nonempty (Motion.LaxHom ordinalTowerMotion.{u} (shiftMotion Code.zero)) :=
  ⟨⟨fun _ => 0, fun _ => by show (0 : ℕ) = Encodable.encode Code.zero + 0; decide,
    fun _ _ _ => Part.mem_some_iff.2 (Nat.zero_mod (Encodable.encode Code.zero))⟩⟩

end FixedPoints

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms cd_collapse_in
#print axioms cd_fan_collapse
#print axioms cd_collapse_out
#print axioms cd_not_injective_of_loop
#print axioms cdJoinStep
#print axioms cd_bot_steps_everywhere
#print axioms cd_tiz_doubling_collapse
#print axioms cd_tiz_reverse_doubling_collapse
#print axioms cd_tiz_control_target
#print axioms cd_tiz_control_source
#print axioms cd_tiz_control_value
#print axioms cd_semiconj_const
#print axioms cd_pred_to_doubling_const
#print axioms cd_floor_control_target
#print axioms cd_floor_control_source
#print axioms cd_doubling_to_pred
#print axioms cd_realization_bot
#print axioms cd_realization_ne_bot
#print axioms cd_realization_bridges
#print axioms cd_banks_offset
#print axioms cd_banks_offset_control
#print axioms cd_forward_stepBack
#print axioms cd_reverse_no_stepBack
#print axioms cd_reverse_no_stepBack_z2
#print axioms cd_reverse_control
#print axioms cdHomMotion
#print axioms cd_run_into
#print axioms cd_run_into_control
#print axioms cd_no_map_to_accumulation
#print axioms cd_pole_fans_two
#print axioms cd_pole_no_three
#print axioms cd_floor_to_tower
#print axioms cd_tower_landing_selfOnly
#print axioms cd_shift_tower_not_injective
#print axioms cd_shift_tower_periodic
#print axioms cdConstTowerHom
#print axioms cd_no_laxHom_tower_shift
end PurityCheck
