import ZeroParadox.Die
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Rat.Denumerable
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
# Homeomorphic and bi-Lipschitz isomorphisms of die motions, the levels above `Motion.StrictIso`

## Engineer's Take

Whether two motions are the same is a switch passed to one of the attributes we're already building the die with, and it's mandatory. The constructors reference each other and pass the fixed default along, to avoid drift. There are three of them instead of two, specifically so that we can note exactly where choice gets introduced, and that's the right way to address the nesting behavior.

---

`Motion.StrictIso` lives in `ZeroParadox/Die.lean`; this file adds `Motion.HomeoIso` (a topological
conjugacy) and `Motion.LipIso` (a bi-Lipschitz conjugacy; a lipeomorphism in Jenkins and Spallone,
arXiv:1011.2451v1, Definition 1.1, p. 1, cited, not claimed: there of germs, here of die motions).
§§ III and IV separate the two steps; § V measures where `Classical.choice` appears.
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

namespace Motion

universe u

variable {α β : Type u}

/-! ## § I. The levels -/

/-- `Statement:` a strict isomorphism of motions (`StrictIso`) whose forward and backward maps are
    continuous, so its underlying bijection is a homeomorphism; the topologies are the ambient
    instances. -/
structure HomeoIso [TopologicalSpace α] [TopologicalSpace β] (M : Motion α) (N : Motion β)
    extends StrictIso M N where
  /-- The forward map is continuous. -/
  continuous_hom : Continuous hom.toFun
  /-- The backward map is continuous. -/
  continuous_inv : Continuous inv.toFun

/-- `Statement:` a `HomeoIso` whose forward and backward maps are Lipschitz, so its underlying
    bijection is bi-Lipschitz. The continuity fields default to the continuity of a Lipschitz map
    (`LipschitzWith.continuous`), so in structure-instance notation a user supplies only the
    Lipschitz fields; `LipIso.mk` still takes a full `HomeoIso`. Mathlib states bi-Lipschitz
    conditions unbundled, as `AntilipschitzWith` and `LipschitzWith` hypotheses on a map
    (`Mathlib/Topology/MetricSpace/Bilipschitz.lean`); this is a structure because it extends
    `HomeoIso` on motions. -/
structure LipIso [PseudoEMetricSpace α] [PseudoEMetricSpace β] (M : Motion α) (N : Motion β)
    extends HomeoIso M N where
  /-- The forward map is Lipschitz for some constant. -/
  lipschitz_hom : ∃ K, LipschitzWith K hom.toFun
  /-- The backward map is Lipschitz for some constant. -/
  lipschitz_inv : ∃ K, LipschitzWith K inv.toFun
  continuous_hom := lipschitz_hom.elim fun _ h => h.continuous
  continuous_inv := lipschitz_inv.elim fun _ h => h.continuous

-- Statement: on ℝ, `LipIso.toHomeoIso` lands at ℝ's ambient topology.
example {M N : Motion ℝ} (e : LipIso M N) : HomeoIso M N := e.toHomeoIso

/-! ## § II. The identity at each level -/

/-- `Statement:` the identity is a strict isomorphism of a motion with itself. -/
def StrictIso.refl (M : Motion α) : StrictIso M M where
  hom := Hom.id M
  inv := Hom.id M
  left_inv _ := rfl
  right_inv _ := rfl

/-- `Statement:` the identity is a `HomeoIso` of a motion with itself, at any topology. -/
def HomeoIso.refl [TopologicalSpace α] (M : Motion α) : HomeoIso M M :=
  { StrictIso.refl M with
    continuous_hom := continuous_id'
    continuous_inv := continuous_id' }

/-- `Statement:` the identity is a `LipIso` of a motion with itself, at any pseudo-extended metric;
    the continuity fields are left to their defaults. -/
def LipIso.refl [PseudoEMetricSpace α] (M : Motion α) : LipIso M M :=
  { StrictIso.refl M with
    lipschitz_hom := ⟨1, LipschitzWith.id⟩
    lipschitz_inv := ⟨1, LipschitzWith.id⟩ }

-- Statement: each level forgets to the identity of the level below, by `rfl`.
example [PseudoEMetricSpace α] (M : Motion α) : (LipIso.refl M).toHomeoIso = HomeoIso.refl M := rfl
example [TopologicalSpace α] (M : Motion α) : (HomeoIso.refl M).toStrictIso = StrictIso.refl M := rfl

/-- `Statement:` the topology on `Bool` in which every set is open, built field by field rather than
    taken from Mathlib's instance; used in § V. -/
abbrev handTopBool : TopologicalSpace Bool where
  IsOpen _ := True
  isOpen_univ := trivial
  isOpen_inter _ _ _ _ := trivial
  isOpen_sUnion _ _ := trivial

/-! ## § III. CONTROL: a strict isomorphism with no homeomorphic one -/

/-- `Statement:` the motion on `α` with identity UP and no step. -/
def stillMotion (α : Type u) : Motion α := ofTotal id (fun _ => rfl) (fun _ _ => False)

/-- `Statement:` every bijection `α ≃ β` is a strict isomorphism of the motions with identity UP
    and no step. -/
def stillIso (e : α ≃ β) : StrictIso (stillMotion α) (stillMotion β) where
  hom := ⟨e, fun h => h.elim, fun x => by simp [stillMotion, ofTotal]⟩
  inv := ⟨e.symm, fun h => h.elim, fun x => by simp [stillMotion, ofTotal]⟩
  left_inv := e.symm_apply_apply
  right_inv := e.apply_symm_apply

/-- `Statement:` `{0}` is not open in `ℚ`; Mathlib's `not_isOpen_singleton` at `0`. -/
theorem rat_singleton_zero_not_isOpen : ¬ IsOpen ({0} : Set ℚ) := not_isOpen_singleton 0

/-- `Statement:` CONTROL. With identity UP and no step on `ℕ` and on `ℚ`, standard topologies, a
    strict isomorphism exists and no `HomeoIso` exists. -/
theorem stillMotion_nat_rat_strict_not_homeo :
    Nonempty (StrictIso (stillMotion ℕ) (stillMotion ℚ)) ∧
      IsEmpty (HomeoIso (stillMotion ℕ) (stillMotion ℚ)) := by
  refine ⟨⟨stillIso (Denumerable.eqv ℚ).symm⟩, ⟨fun e => ?_⟩⟩
  -- the preimage of `{e⁻¹ 0}` under the continuous backward map is open in `ℚ` and equals `{0}`
  have hopen : IsOpen (e.inv.toFun ⁻¹' {e.inv.toFun 0}) :=
    (isOpen_discrete _).preimage e.continuous_inv
  have heq : e.inv.toFun ⁻¹' {e.inv.toFun 0} = ({0} : Set ℚ) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      have := congrArg e.hom.toFun hq
      rwa [e.right_inv, e.right_inv] at this
    · rintro rfl; rfl
  exact rat_singleton_zero_not_isOpen (heq ▸ hopen)

-- Statement: CONTROL at the top level: the same pair has no `LipIso`.
example : IsEmpty (LipIso (stillMotion ℕ) (stillMotion ℚ)) :=
  ⟨fun e => stillMotion_nat_rat_strict_not_homeo.2.false e.toHomeoIso⟩

-- Statement: NO-GO gauge. Neither `HomeoIso` nor `LipIso` is degenerate: the identity is a member
-- at every level (`HomeoIso.refl`, `LipIso.refl`, § II), and the pair above is a non-member of both
-- (`stillMotion_nat_rat_strict_not_homeo` and the `example` after it).

/-! ## § IV. CONTROL: a homeomorphic isomorphism with no bi-Lipschitz one -/

/-- `Statement:` the open interval `(-1, 1)` of `ℝ`, as a type. -/
abbrev NegOneOneIoo : Type := Set.Ioo (-1 : ℝ) 1

/-- `Statement:` with identity UP and no step, `ℝ` and `(-1, 1)` are isomorphic as motions by a
    homeomorphism, Mathlib's `orderIsoIooNegOneOne`. -/
noncomputable def lineIntervalHomeo : HomeoIso (stillMotion ℝ) (stillMotion NegOneOneIoo) :=
  { stillIso (orderIsoIooNegOneOne ℝ).toEquiv with
    continuous_hom := (orderIsoIooNegOneOne ℝ).continuous
    continuous_inv := (orderIsoIooNegOneOne ℝ).symm.continuous }

/-- `Statement:` no Lipschitz map from `(-1, 1)` onto `ℝ` exists. -/
theorem no_lipschitz_surj (g : NegOneOneIoo → ℝ) (hg : Function.Surjective g) (K : NNReal)
    (hK : LipschitzWith K g) : False := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  set x0 : NegOneOneIoo := ⟨0, h0⟩
  obtain ⟨x, hx⟩ := hg (g x0 + K + 1)
  have hd : dist (g x) (g x0) ≤ K * dist x x0 := hK.dist_le_mul x x0
  have hxx : dist x x0 < 1 := by
    rw [Subtype.dist_eq, Real.dist_eq]
    obtain ⟨hx1, hx2⟩ := x.2
    simp only [x0, sub_zero]
    exact abs_lt.2 ⟨hx1, hx2⟩
  rw [hx, Real.dist_eq] at hd
  have hK0 : (0 : ℝ) ≤ K := K.2
  have : (K : ℝ) * dist x x0 ≤ K := by nlinarith [dist_nonneg (x := x) (y := x0)]
  have habs : |g x0 + K + 1 - g x0| = K + 1 := by
    rw [show g x0 + K + 1 - g x0 = (K : ℝ) + 1 by ring, abs_of_pos (by linarith)]
  linarith

/-- `Statement:` CONTROL, metric only. With identity UP and no step on `ℝ` and on `(-1, 1)`, a
    `HomeoIso` exists and no `LipIso` exists. -/
theorem stillMotion_line_interval_homeo_not_lip :
    Nonempty (HomeoIso (stillMotion ℝ) (stillMotion NegOneOneIoo)) ∧
      IsEmpty (LipIso (stillMotion ℝ) (stillMotion NegOneOneIoo)) := by
  refine ⟨⟨lineIntervalHomeo⟩, ⟨fun e => ?_⟩⟩
  obtain ⟨K, hK⟩ := e.lipschitz_inv
  exact no_lipschitz_surj e.inv.toFun
    (fun y => ⟨e.hom.toFun y, e.left_inv y⟩) K hK

/-- `Statement:` the motion on `ℝ` with identity UP and step `x ↦ c * x`. -/
def scaleMotion (c : ℝ) : Motion ℝ := ofTotal id (fun _ => rfl) (fun x y => y = c * x)

/-- `Statement:` the signed square `x ↦ x * |x|`. -/
noncomputable def signedSq (x : ℝ) : ℝ := x * |x|

/-- `Statement:` the signed square is strictly increasing. -/
theorem signedSq_strictMono : StrictMono signedSq := by
  intro a b hab
  unfold signedSq
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]; nlinarith
  · linarith
  · rw [abs_of_neg ha, abs_of_nonneg hb]; nlinarith
  · rw [abs_of_neg ha, abs_of_neg hb]; nlinarith

/-- `Statement:` the signed square is onto `ℝ`. -/
theorem signedSq_surjective : Function.Surjective signedSq := by
  intro y
  rcases le_or_gt 0 y with hy | hy
  · refine ⟨Real.sqrt y, ?_⟩
    unfold signedSq
    rw [abs_of_nonneg (Real.sqrt_nonneg y), Real.mul_self_sqrt hy]
  · refine ⟨-Real.sqrt (-y), ?_⟩
    unfold signedSq
    rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _), neg_mul, Real.mul_self_sqrt (by linarith)]
    ring

/-- `Statement:` the signed square sends `2 * x` to `4` times its value at `x`. -/
theorem signedSq_two_mul (x : ℝ) : signedSq (2 * x) = 4 * signedSq x := by
  unfold signedSq
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; ring

/-- `Statement:` the signed square as an order isomorphism of `ℝ`. -/
noncomputable def signedSqIso : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective signedSq signedSq_strictMono signedSq_surjective

/-- `Statement:` the signed square is a `HomeoIso` from `scaleMotion 2` to `scaleMotion 4`. -/
noncomputable def scale24Homeo : HomeoIso (scaleMotion 2) (scaleMotion 4) where
  hom := ⟨signedSqIso, fun {a b} h => by
      show signedSqIso b = 4 * signedSqIso a
      change b = 2 * a at h
      subst h
      exact signedSq_two_mul a,
    fun x => by simp [scaleMotion, ofTotal]⟩
  inv := ⟨signedSqIso.symm, fun {a b} h => by
      show signedSqIso.symm b = 2 * signedSqIso.symm a
      change b = 4 * a at h
      apply signedSqIso.injective
      rw [OrderIso.apply_symm_apply, h]
      show 4 * a = signedSq (2 * signedSqIso.symm a)
      rw [signedSq_two_mul]
      show 4 * a = 4 * signedSqIso (signedSqIso.symm a)
      rw [OrderIso.apply_symm_apply],
    fun x => by simp [scaleMotion, ofTotal]⟩
  left_inv := signedSqIso.symm_apply_apply
  right_inv := signedSqIso.apply_symm_apply
  continuous_hom := signedSqIso.continuous
  continuous_inv := signedSqIso.symm.continuous

/-- `Statement:` CONTROL, dynamical. From `scaleMotion 2` to `scaleMotion 4` a `HomeoIso` exists and
    no `LipIso` exists. `Reading:` the p-adic counterpart, dilations with different multipliers
    conjugate by a homeomorphism whose Hölder exponent at 0 cannot be improved, is Jenkins and
    Spallone, arXiv:1011.2451v1, Proposition 7.1, p. 26 (cited, not claimed). -/
theorem scale24_not_lip :
    Nonempty (HomeoIso (scaleMotion 2) (scaleMotion 4)) ∧
      IsEmpty (LipIso (scaleMotion 2) (scaleMotion 4)) := by
  refine ⟨⟨scale24Homeo⟩, ⟨fun e => ?_⟩⟩
  obtain ⟨K, hK⟩ := e.lipschitz_hom
  set f := e.hom.toFun with hf
  have hstep : ∀ x, f (2 * x) = 4 * f x := fun x => e.hom.map_step (a := x) (b := 2 * x) rfl
  have h0 : f 0 = 0 := by
    have := hstep 0
    rw [mul_zero] at this
    linarith
  have hpow : ∀ n : ℕ, f (2 ^ n) = 4 ^ n * f 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_comm _ (2:ℝ), hstep, ih, pow_succ]; ring
  have hbound : ∀ n : ℕ, (2:ℝ) ^ n * |f 1| ≤ K := by
    intro n
    have hd := hK.dist_le_mul (2 ^ n : ℝ) 0
    rw [Real.dist_eq, Real.dist_eq, hpow, h0, sub_zero, sub_zero, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 4 ^ n), abs_of_pos (by positivity : (0:ℝ) < 2 ^ n)] at hd
    have h4 : (4:ℝ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
    rw [h4] at hd
    have h2 : (0:ℝ) < 2 ^ n := by positivity
    nlinarith [abs_nonneg (f 1)]
  have hf1 : f 1 = 0 := by
    by_contra hne
    have hpos : 0 < |f 1| := abs_pos.2 hne
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((K : ℝ) / |f 1|) (by norm_num : (1:ℝ) < 2)
    have := hbound n
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have : (1:ℝ) = 0 := by
    have := congrArg e.inv.toFun (hf1.trans h0.symm)
    rwa [e.left_inv, e.left_inv] at this
  norm_num at this

-- Statement: both steps of the chain are strict. As collections of isomorphisms, every `LipIso`
-- gives a `HomeoIso` and every `HomeoIso` a `StrictIso` (the `extends` projections); the pair in
-- § III has a `StrictIso` and no `HomeoIso`, and the pairs above have a `HomeoIso` and no `LipIso`.

/-! ## § V. Where `Classical.choice` appears, measured

The footprints are printed in `PurityCheck` below. Measured: the structure types `StrictIso` and
`HomeoIso` depend on no axioms, and `LipIso` carries `Classical.choice`, as do Mathlib's
`PseudoEMetricSpace` and `LipschitzWith`. At the first two levels a member carries `Classical.choice`
when built on Mathlib's topology instance (`homeoIsoReflBool`, `homeoIsoReflNat`; the instances on
`ℕ`, `Bool` and `Empty` carry it) and does not on the hand-built `handTopBool`
(`homeoIsoReflHandBool`, `[propext, Quot.sound]`). -/

/-- `Statement:` the identity `HomeoIso` of the motion with identity UP and no step on `Bool`, at the
    hand-built topology `handTopBool`. -/
def homeoIsoReflHandBool :
    @HomeoIso Bool Bool handTopBool handTopBool (stillMotion Bool) (stillMotion Bool) :=
  @HomeoIso.refl Bool handTopBool (stillMotion Bool)

/-- `Statement:` the same identity on `Bool` at Mathlib's topology instance. -/
def homeoIsoReflBool : HomeoIso (stillMotion Bool) (stillMotion Bool) := HomeoIso.refl _

/-- `Statement:` the same identity on `ℕ` at Mathlib's topology instance. -/
def homeoIsoReflNat : HomeoIso (stillMotion ℕ) (stillMotion ℕ) := HomeoIso.refl _

end Motion

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms Motion.StrictIso
#print axioms Motion.HomeoIso
#print axioms Motion.LipIso
#print axioms Motion.StrictIso.refl
#print axioms Motion.HomeoIso.refl
#print axioms Motion.LipIso.refl
#print axioms Motion.handTopBool
#print axioms Motion.stillMotion
#print axioms Motion.stillIso
#print axioms Motion.rat_singleton_zero_not_isOpen
#print axioms Motion.stillMotion_nat_rat_strict_not_homeo
#print axioms Motion.NegOneOneIoo
#print axioms Motion.lineIntervalHomeo
#print axioms Motion.no_lipschitz_surj
#print axioms Motion.stillMotion_line_interval_homeo_not_lip
#print axioms Motion.scaleMotion
#print axioms Motion.signedSq
#print axioms Motion.signedSq_strictMono
#print axioms Motion.signedSq_surjective
#print axioms Motion.signedSq_two_mul
#print axioms Motion.signedSqIso
#print axioms Motion.scale24Homeo
#print axioms Motion.scale24_not_lip
#print axioms Motion.homeoIsoReflHandBool
#print axioms Motion.homeoIsoReflBool
#print axioms Motion.homeoIsoReflNat
-- Measured beside the levels: Mathlib's topologies on `ℕ`, `Bool` and `Empty`, and the types the two
-- upper levels name.
#print axioms instTopologicalSpaceNat
#print axioms instTopologicalSpaceBool
#print axioms instTopologicalSpaceEmpty
#print axioms TopologicalSpace
#print axioms Continuous
#print axioms PseudoEMetricSpace
#print axioms LipschitzWith
#print axioms ENNReal
#print axioms NNReal
end PurityCheck
