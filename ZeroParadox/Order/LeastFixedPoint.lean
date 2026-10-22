import ZeroParadox.Ordinal.Epsilon0MinMax
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Computability.Kleene
import Mathlib.Order.FixedPoints
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Fin.Embedding

set_option maxHeartbeats 400000

/-!
# The μ abstraction: least fixed point reached from a seed (the ceiling analogue of `AbstractSelfApp`)

## Engineer's Take

Define epsilon 0 as a minimum fixed point in an abstract class, instead of a fixed class for a given
framework. Denotes a common placement relative to zero.

---

## Formal Overview
`IsLeastFixedPointFrom r f seed mu` — the Knaster–Tarski least fixed point at or above a seed, over a
bare relation so it spans carriers. Three faces — ε₀ (genuine ascent), `selfApp` (degenerate), Kleene
(FENCED) — share a **SHAPE**, never one object. Schema, faces and the type-boundary fence: `ZeroParadox/Order/LeastFixedPoint.md`.
-/

namespace ZeroParadox

open Ordinal

/-! ## § I. The μ schema: least fixed point reached from a seed -/

/-- `mu` is the **least fixed point of `f` at or above `seed`**, with respect to the relation `r`.
    The order-generic Knaster–Tarski / μ characterization: `mu` is a fixed point, and any fixed
    point at or above the seed dominates it. Stated over a bare relation `r : α → α → Prop` (not a
    lattice typeclass) so the framework's distinct carriers — `Ordinal` (via `≤`) and the ZP
    semilattice `L` (via `ZPSemilattice.le`) — instantiate the same schema. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: Mathlib's least-fixed-point API (OrderHom.lfp, isLeast_lfp)
-- is fixed to a CompleteLattice carrier. This predicate states the SAME μ characterization
-- (least fixed point at/above a seed) over a bare relation so it applies to the framework's
-- non-lattice carriers (the axiom-clean ZPSemilattice L, and Ordinal which is not a complete
-- lattice). It is the order-generic placement schema, grounded back to OrderHom.lfp in § II.
structure IsLeastFixedPointFrom {α : Type*} (r : α → α → Prop) (f : α → α) (seed mu : α) : Prop where
  /-- The seed lies at or below the μ closure. -/
  seed_le : r seed mu
  /-- `mu` is a fixed point of `f`. -/
  fixed   : f mu = mu
  /-- `mu` is least among fixed points at or above the seed. -/
  least   : ∀ b : α, f b = b → r seed b → r mu b

/-- The schema pins a **unique** object within one carrier: given antisymmetry of `r`, any two least
    fixed points of `f` from the same seed coincide. (This is a within-carrier statement only — it
    says nothing across the distinct carriers of the faces; that identity is the ill-typed
    type-boundary fence.) -/
theorem IsLeastFixedPointFrom.unique {α : Type*} {r : α → α → Prop} {f : α → α} {seed mu mu' : α}
    (antisymm : ∀ x y : α, r x y → r y x → x = y)
    (h : IsLeastFixedPointFrom r f seed mu) (h' : IsLeastFixedPointFrom r f seed mu') :
    mu = mu' :=
  antisymm mu mu' (h.least mu' h'.fixed h'.seed_le) (h'.least mu h.fixed h.seed_le)

/-! ## § II. Grounding: the schema IS Mathlib's `OrderHom.lfp` (Knaster–Tarski)

On a complete lattice, the standard least fixed point `f.lfp` witnesses the schema from ⊥. This
anchors `IsLeastFixedPointFrom` to recognized order theory — it is not ZP-invented structure. -/

/-- On a complete lattice, Mathlib's `OrderHom.lfp` is the least fixed point from ⊥ in the sense of
    the schema. Wraps `OrderHom.map_lfp` (fixed) and `OrderHom.lfp_le_fixed` (least). -/
theorem lfp_isLeastFixedPointFrom {α : Type*} [CompleteLattice α] (f : α →o α) :
    IsLeastFixedPointFrom (· ≤ ·) (⇑f) (⊥ : α) f.lfp where
  seed_le := bot_le
  fixed := f.map_lfp
  least := fun _ hb _ => f.lfp_le_fixed hb

/-! ## § III. The general ordinal μ: `nfp` of a normal function

For any normal ordinal function, its next fixed point `nfp f a` (the supremum of the finite iterates
from `a`) is the least fixed point from `a` — the Kleene ascent μ on ordinals. Reuses Mathlib's
`le_nfp`, `nfp_fp`, `nfp_le_fp`. -/

/-- For a normal `f : Ordinal → Ordinal`, `nfp f a` is the least fixed point from the seed `a`. -/
theorem isLeastFixedPointFrom_nfp {f : Ordinal → Ordinal} (H : Order.IsNormal f) (a : Ordinal) :
    IsLeastFixedPointFrom (· ≤ ·) f a (Ordinal.nfp f a) where
  seed_le := Ordinal.le_nfp f a
  fixed := Ordinal.nfp_fp H a
  least := fun _b hb hab => Ordinal.nfp_le_fp H.strictMono.monotone hab (le_of_eq hb)

-- `Statement:` for a normal `f`, the supremum of the finite iterates from `a` is that least fixed point.
example {f : Ordinal → Ordinal} (H : Order.IsNormal f) (a : Ordinal) :
    IsLeastFixedPointFrom (· ≤ ·) f a (⨆ n, f^[n] a) := by
  rw [Ordinal.iSup_iterate_eq_nfp]
  exact isLeastFixedPointFrom_nfp H a

/-! ## § IV. The ε₀ face — genuine ascent μ (seed ⊥ ≠ closure ε₀)

⚠ **THE ASCENT IS GENUINE; THE SEED IS NOT DISTINGUISHED WITHIN `[0, ε₀]`.**
`nfp_seed_independent_below_epsilon0` (`ZeroParadox/Ordinal/Epsilon0LeastFP.lean`) proves
`∀ a ≤ ε₀, nfp (ω^·) a = ε₀`. ⚠ Scope is at or below ε₀, and normality is load-bearing. Veblen's
classical form, the seed-as-role reading, and the SHAPE-never-instance-of fence: `ZeroParadox/Order/LeastFixedPoint.md`. -/

/-- **ε₀ face.** ε₀ is the least fixed point of `α ↦ ω^α` from the ordinal bottom ⊥. The seed ⊥ and
    the closure ε₀ are distinct — this is the genuine ascent μ. Reuses `epsilonZero_fixedPoint`
    and `epsilonZero_le_fixedPoint` (`Ordinal/Gentzen.lean`); nothing reproved. -/
theorem epsilon0_isLeastFixedPointFrom :
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal) epsilonZero where
  seed_le := bot_le
  fixed := epsilonZero_fixedPoint
  least := fun _ hb _ => epsilonZero_le_fixedPoint hb

/-- The ε₀ face is literally the general ordinal `nfp` μ at `f = ω^·`, seed ⊥ (via
    `isLeastFixedPointFrom_nfp` on the normal function `ω^·`). With `epsilon0_eq_nfp_bot`
    (`ε₀ = nfp (ω^·) ⊥`), this identifies the two presentations of the same μ. -/
theorem epsilon0_isLeastFixedPointFrom_via_nfp :
    IsLeastFixedPointFrom (· ≤ ·) (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal)
      (Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (⊥ : Ordinal)) :=
  isLeastFixedPointFrom_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) ⊥

/-- The closure = supremum of the ascending iterates, for the ε₀ face: ε₀ is the supremum of the
    ω-tower stages. Re-exposes `epsilonZero_eq_iSup` (`Ordinal/Gentzen.lean`) as the Kleene-ascent
    content of the ε₀ μ. -/
theorem epsilon0_mu_eq_iSup : epsilonZero = ⨆ n : ℕ, fundamentalSeq n :=
  epsilonZero_eq_iSup

/-! ## § V. The self-reference face — degenerate/floor μ (seed = closure = ⊥) -/

/-- **Self-reference face.** In any `AbstractSelfApp` semilattice, ⊥ is the least fixed point of
    `selfApp` from the seed ⊥ (w.r.t. `ZPSemilattice.le`). Here seed = closure = ⊥: the μ
    construction collapses onto the seed. This is the floor μ — the Gödel-inversion fact that
    self-reference sits *at* the floor, the ceiling analogue's degenerate case. Uses `fixed_bot`
    and the semilattice bottom law `bot_join`. -/
theorem selfApp_isLeastFixedPointFrom {L : Type*} [ZPSemilattice L] [AbstractSelfApp L] :
    IsLeastFixedPointFrom (ZPSemilattice.le) (AbstractSelfApp.selfApp)
      (ZPSemilattice.bot : L) (ZPSemilattice.bot : L) where
  seed_le := ZPSemilattice.le_refl _
  fixed := AbstractSelfApp.fixed_bot
  least := fun b _ _ => ZPSemilattice.bot_join b

/-- On the self-reference face the schema's uniqueness collapses to the AFA uniqueness: ⊥ is the
    only least fixed point of `selfApp` from ⊥ (via `IsLeastFixedPointFrom.unique` with
    `ZPSemilattice.le_antisymm`). -/
theorem selfApp_mu_unique {L : Type*} [ZPSemilattice L] [AbstractSelfApp L]
    {mu : L} (h : IsLeastFixedPointFrom (ZPSemilattice.le) (AbstractSelfApp.selfApp)
      (ZPSemilattice.bot : L) mu) : mu = ZPSemilattice.bot :=
  IsLeastFixedPointFrom.unique (fun _ _ => ZPSemilattice.le_antisymm)
    h selfApp_isLeastFixedPointFrom

/-! ## § VI. The Kleene face — FENCED (same shape, different setting)

Rogers'/Kleene's recursion theorem gives a fixed point of any computable self-map of `Code`. This is
the same μ-*shape* (a self-map has a fixed point) in a different *setting*: `Code` carries no
complete-lattice order, so there is no `lfp`; its fixed points are NOT unique
(`infinite_quine_family`); and there is no seed→closure ascent. Hence it does **not** instantiate
`IsLeastFixedPointFrom` — recorded as an existence statement with the fence in prose. The
cross-face identity (Ordinal μ = `L` μ = `Code` μ) is a type boundary, not a proposition. -/

open Nat.Partrec Nat.Partrec.Code in
/-- **Kleene face (fenced).** For any computable `f : Code → Code` a behavioral fixed point exists
    (`eval (f c) = eval c`). Wraps `roger_fixed_point_exists`. NOT an `IsLeastFixedPointFrom`: no
    lattice order on `Code`, fixed points non-unique, no seed→closure — same shape, different
    setting. -/
theorem kleene_fixed_point_from_exists (f : Code → Code) (hf : Computable f) :
    ∃ c : Code, eval (f c) = eval c :=
  roger_fixed_point_exists f hf

/-! ## § VII. The schema with the fixed-point equation relaxed to a relation

On `Type` the type face is not stated as an `IsLeastFixedPointFrom`: its `fixed` field would be the
equation `Option ℕ = ℕ`, which is well-typed and neither proved nor refuted here. The relaxed schema
takes the equation as a parameter `e`; the type face uses `≃`, and the `Cardinal` quotient recovers
the schema itself. A shared SHAPE: no map between ℕ and ε₀ is stated. Reading: the `least` field of
`nat_isLeastFixedPointUpTo` (`Option B ≃ B` gives `ℕ ↪ B`) is one direction of the Dedekind-infinite
characterisation; ℕ as the colimit of the `Fin`-chain and Lambek's lemma are indexed in
`ZeroParadox/BottomCannotBe.lean` § GENERATION. -/

/-- `Statement:` `mu` is `r`-above `seed`, `e (f mu) mu`, and `mu` is `r`-below every `b` with
    `e (f b) b` that is `r`-above `seed`. -/
-- [ZP-CUSTOM] extends: IsLeastFixedPointFrom (ZeroParadox/Order/LeastFixedPoint.lean) | reason: the
-- same three fields with the equation `f mu = mu` passed as a relation `e`, so a carrier whose
-- fixed points hold only up to `≃` (types) meets it; `upTo_eq_iff` recovers the original at `e = Eq`.
structure IsLeastFixedPointUpTo {α : Type*} (r e : α → α → Prop) (f : α → α) (seed mu : α) :
    Prop where
  /-- The seed lies `r`-below the closure. -/
  seed_le : r seed mu
  /-- `mu` is a fixed point of `f` up to `e`. -/
  fixed : e (f mu) mu
  /-- `mu` is `r`-least among such fixed points `r`-above the seed. -/
  least : ∀ b, e (f b) b → r seed b → r mu b

/-! NO-GO gauge — what fails to be an `IsLeastFixedPointUpTo`? ℕ, for `Option` from `Empty` with `e`
always true (the CONTROL below); members: `nat_isLeastFixedPointUpTo`, and ε₀ at `e = Eq`. -/

/-- `Statement:` with `e = Eq` the relaxed schema is `IsLeastFixedPointFrom`; both directions. -/
theorem upTo_eq_iff {α : Type*} (r : α → α → Prop) (f : α → α) (seed mu : α) :
    IsLeastFixedPointUpTo r Eq f seed mu ↔ IsLeastFixedPointFrom r f seed mu :=
  ⟨fun h => ⟨h.seed_le, h.fixed, h.least⟩, fun h => ⟨h.seed_le, h.fixed, h.least⟩⟩

-- Statement: ε₀ in the relaxed schema with `e = Eq`, from `epsilon0_isLeastFixedPointFrom` (§ IV).
example : IsLeastFixedPointUpTo (· ≤ ·) Eq (fun α : Ordinal => Ordinal.omega0 ^ α) (⊥ : Ordinal)
    epsilonZero :=
  (upTo_eq_iff _ _ _ _).2 epsilon0_isLeastFixedPointFrom

/-- `Statement:` from `e : Option B ≃ B`, the injection `ℕ ↪ B` with `0 ↦ e none` and
    `k + 1 ↦ e (some (image of k))`. -/
def natEmbOfOptEquiv {B : Type} (e : Option B ≃ B) : ℕ ↪ B where
  toFun := fun n => Nat.rec (e none) (fun _ b => e (some b)) n
  inj' := by
    intro m n h
    induction m generalizing n with
    | zero =>
      cases n with
      | zero => rfl
      | succ n => exact absurd (e.injective h) (by simp)
    | succ m ih =>
      cases n with
      | zero => exact absurd (e.injective h) (by simp)
      | succ n =>
        have h' := Option.some_injective _ (e.injective h)
        exact congrArg Nat.succ (ih h')

/-- `Statement:` on `Type`, with `r` = "an injection exists" and `e` = "an equivalence exists", ℕ is
    the least fixed point of `Option` from `Empty` in the relaxed schema. -/
theorem nat_isLeastFixedPointUpTo :
    IsLeastFixedPointUpTo (fun A B : Type => Nonempty (A ↪ B)) (fun A B => Nonempty (A ≃ B))
      Option Empty ℕ where
  seed_le := ⟨⟨Empty.elim, fun a => a.elim⟩⟩
  fixed := ⟨(Equiv.optionEquivSumPUnit ℕ : Option ℕ ≃ ℕ ⊕ PUnit.{1}).trans Equiv.natSumPUnitEquivNat⟩
  least := fun _ ⟨e⟩ _ => ⟨natEmbOfOptEquiv e⟩

-- Statement: CONTROL, the relation `e` carries the schema: with `e` always true, ℕ is not least.
example : ¬ IsLeastFixedPointUpTo (fun A B : Type => Nonempty (A ↪ B)) (fun _ _ => True)
    Option Empty ℕ := fun h => by
  obtain ⟨g⟩ := h.least Empty trivial ⟨⟨Empty.elim, fun a => a.elim⟩⟩
  exact (g 0).elim

/-- `Statement:` on `Cardinal`, with `≤`, `c ↦ c + 1` and seed 0, `ℵ₀` is the least fixed point
    (`IsLeastFixedPointFrom`). -/
theorem aleph0_isLeastFixedPointFrom :
    IsLeastFixedPointFrom (· ≤ ·) (fun c : Cardinal.{0} => c + 1) 0 Cardinal.aleph0 where
  seed_le := zero_le _
  fixed := Cardinal.add_one_eq le_rfl
  least := fun b hb _ => by
    by_contra hlt
    obtain ⟨n, rfl⟩ := Cardinal.lt_aleph0.1 (not_le.1 hlt)
    have : ((n + 1 : ℕ) : Cardinal) = (n : Cardinal) := by push_cast; exact hb
    exact absurd (Nat.cast_injective this) (by omega)

-- Statement: Mathlib's `Cardinal.mk_option`, `#(Option α) = #α + 1`, links the type face to the
-- cardinal one.
#check @Cardinal.mk_option

/-- `Statement:` the `n`-th stage of adjoining a point to `Empty`. -/
def optIter : ℕ → Type
  | 0 => Empty
  | n + 1 => Option (optIter n)

/-- `Statement:` the `n`-th stage is equivalent to `Fin n`. -/
def optIterEquiv : (n : ℕ) → optIter n ≃ Fin n
  | 0 => show Empty ≃ Fin 0 from
      { toFun := fun e => e.elim, invFun := fun i => i.elim0,
        left_inv := fun e => e.elim, right_inv := fun i => i.elim0 }
  | n + 1 => (Equiv.optionCongr (optIterEquiv n)).trans (finSuccEquiv n).symm

/-- `Statement:` no equivalence `Option (Fin n) ≃ Fin n`: no finite stage is a fixed point up to `≃`. -/
theorem fin_not_fixed (n : ℕ) : IsEmpty (Option (Fin n) ≃ Fin n) :=
  ⟨fun e => by
    have := Fin.equiv_iff_eq.1 ⟨(finSuccEquiv n).trans e⟩
    omega⟩

/-- `Statement:` each stage injects into ℕ and is not equivalent to ℕ. -/
theorem optIter_lt_nat (n : ℕ) : Nonempty (optIter n ↪ ℕ) ∧ IsEmpty (optIter n ≃ ℕ) :=
  ⟨⟨(optIterEquiv n).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩⟩,
   ⟨fun e => by
      haveI := Finite.of_equiv _ ((optIterEquiv n).symm.trans e)
      exact not_finite ℕ⟩⟩

/-! Adjoining a point as a motion on `Type` (`ZeroParadox/Die.lean` § XVIII). Each stage `optIter n`
is a type of its own; on the carrier `Type` the step is one self-map. Quotiented by "an equivalence exists"
(Mathlib's `Cardinal.isEquivalent`, whose classes are `Cardinal`), the step is `c ↦ c + 1`. -/

/-- `Statement:` the motion `ofFun Option` on `Type`. -/
-- [ZP-CUSTOM] no Mathlib analog | reason: `Option` as a self-map of `Type`, so that the stages
-- `optIter n` form a run of one motion.
def optionMotion : Motion Type := Motion.ofFun Option

/-- `Statement:` the stages `optIter n` form a run of `optionMotion`. -/
theorem optionMotion_isRun_optIter : optionMotion.IsRun optIter := fun _ => rfl

/-- `Statement:` "an equivalence exists" is step-compatible with `optionMotion`
    (`Equiv.optionCongr`). -/
theorem optionMotion_stepCompat : optionMotion.StepCompat Cardinal.isEquivalent :=
  Motion.stepCompat_ofFun fun _ _ ⟨e⟩ => ⟨Equiv.optionCongr e⟩

/-- `Statement:` in the quotient, on `Cardinal.{0}`, the class `X` steps to `Y` iff `Y = X + 1`
    (`Cardinal.mk_option`); both directions. `Reading:` from 0 the least fixed point of `c ↦ c + 1`
    is `ℵ₀` (`aleph0_isLeastFixedPointFrom`). -/
theorem quot_optionMotion_step_iff (X Y : Cardinal.{0}) :
    (optionMotion.quot Cardinal.isEquivalent).step X Y ↔ Y = X + 1 := by
  induction X using Quotient.ind with
  | _ a =>
    rw [Motion.quot_step_mk_iff optionMotion_stepCompat]
    constructor
    · rintro ⟨b, hb, rfl⟩
      have hb' : b = Option a := hb
      subst hb'
      exact Cardinal.mk_option
    · rintro rfl
      exact ⟨Option a, rfl, Cardinal.mk_option⟩

/-- `Statement:` the class of ℕ steps to itself only (`nat_isLeastFixedPointUpTo`'s `fixed`). -/
theorem quot_optionMotion_selfOnlyAt_nat :
    (optionMotion.quot Cardinal.isEquivalent).SelfOnlyAt (Quotient.mk _ ℕ) := by
  rw [Motion.quot_selfOnlyAt_mk_iff optionMotion_stepCompat]
  exact ⟨⟨Option ℕ, rfl, nat_isLeastFixedPointUpTo.fixed⟩,
    fun b hb => (show b = Option ℕ from hb) ▸ nat_isLeastFixedPointUpTo.fixed⟩

/-- `Statement:` the class of `Fin n` does not step to itself only (`fin_not_fixed`). -/
theorem quot_optionMotion_not_selfOnlyAt_fin (n : ℕ) :
    ¬ (optionMotion.quot Cardinal.isEquivalent).SelfOnlyAt (Quotient.mk _ (Fin n)) := by
  rw [Motion.quot_selfOnlyAt_mk_iff optionMotion_stepCompat]
  rintro ⟨⟨b, hb, ⟨e⟩⟩, -⟩
  have hb' : b = Option (Fin n) := hb
  subst hb'
  exact (fin_not_fixed n).false e

end ZeroParadox

/-! ## Axiom Purity Check

The schema's `selfApp_*` instances and `IsLeastFixedPointFrom.unique` are axiom-free (no axioms at
all); the Mathlib-`lfp` grounding `lfp_isLeastFixedPointFrom` is choice-free `[propext, Quot.sound]`.
The ordinal faces (`isLeastFixedPointFrom_nfp`, `epsilon0_*`) and the Kleene face are
STATEMENT-CARRIED (`ZeroParadox/Category/ChoiceCannotBe.md`): each statement, only assumed, already
reports `Classical.choice` (statement control, measured 2026-10-08), from Mathlib's `Ordinal`/`nfp` and
`Code`/`Partrec` machinery. The open question is a restatement on a choice-free carrier; ZP-N proves the
snap-from-below (the ascent) choice-free on `ONote`, which is evidence for that question, not a
restatement of these faces. -/

section PurityCheck
open ZeroParadox

#print axioms IsLeastFixedPointFrom.unique
#print axioms lfp_isLeastFixedPointFrom
#print axioms isLeastFixedPointFrom_nfp
#print axioms epsilon0_isLeastFixedPointFrom
#print axioms epsilon0_isLeastFixedPointFrom_via_nfp
#print axioms epsilon0_mu_eq_iSup
#print axioms selfApp_isLeastFixedPointFrom
#print axioms selfApp_mu_unique
#print axioms kleene_fixed_point_from_exists
#print axioms IsLeastFixedPointUpTo
#print axioms upTo_eq_iff
#print axioms natEmbOfOptEquiv
#print axioms nat_isLeastFixedPointUpTo
#print axioms aleph0_isLeastFixedPointFrom
#print axioms optIter
#print axioms optIterEquiv
#print axioms fin_not_fixed
#print axioms optIter_lt_nat
#print axioms optionMotion
#print axioms optionMotion_isRun_optIter
#print axioms optionMotion_stepCompat
#print axioms quot_optionMotion_step_iff
#print axioms quot_optionMotion_selfOnlyAt_nat
#print axioms quot_optionMotion_not_selfOnlyAt_fin

end PurityCheck
