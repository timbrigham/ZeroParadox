import ZeroParadox.Die
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Rat.Denumerable
import Mathlib.Tactic

/-!
# Levels of "same motion": strict, homeomorphic and bi-Lipschitz isomorphisms of die motions

## Engineer's Take

Whether two motions are the same is a switch passed to one of the attributes we're already building the die with, and it's mandatory. The constructors reference each other and pass the fixed default along, to avoid drift. There are three of them instead of two, specifically so that we can note exactly where choice gets introduced, and that's the right way to address the nesting behavior.

---

`Motion.StrictIso` (`ZeroParadox/Die.lean`) asks nothing of the carriers; `Motion.HomeoIso` extends
it with continuity (a homeomorphism) and `Motion.LipIso` extends that with Lipschitz bounds (a
bi-Lipschitz map). § III is the control: a `StrictIso` with no `HomeoIso` and no `LipIso`.
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
    (`LipschitzWith.continuous`), so a user supplies only the Lipschitz fields. -/
structure LipIso [PseudoEMetricSpace α] [PseudoEMetricSpace β] (M : Motion α) (N : Motion β)
    extends HomeoIso M N where
  /-- The forward map is Lipschitz for some constant. -/
  lipschitz_hom : ∃ K, LipschitzWith K hom.toFun
  /-- The backward map is Lipschitz for some constant. -/
  lipschitz_inv : ∃ K, LipschitzWith K inv.toFun
  continuous_hom := lipschitz_hom.elim fun _ h => h.continuous
  continuous_inv := lipschitz_inv.elim fun _ h => h.continuous

-- Statement: the forgetful maps are the `extends` projections.
example [TopologicalSpace α] [TopologicalSpace β] {M : Motion α} {N : Motion β}
    (e : HomeoIso M N) : StrictIso M N := e.toStrictIso
example [PseudoEMetricSpace α] [PseudoEMetricSpace β] {M : Motion α} {N : Motion β}
    (e : LipIso M N) : HomeoIso M N := e.toHomeoIso

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
    taken from Mathlib's instance. -/
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

/-- `Statement:` `{0}` is not open in `ℚ`. -/
theorem rat_singleton_zero_not_isOpen : ¬ IsOpen ({0} : Set ℚ) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 h 0 rfl
  obtain ⟨q, hq0, hqε⟩ := exists_pos_rat_lt hε
  have hq : q ∈ Metric.ball (0 : ℚ) ε := by
    rw [Metric.mem_ball, Rat.dist_eq]
    push_cast
    rw [sub_zero, abs_of_pos (by exact_mod_cast hq0)]
    exact hqε
  exact hq0.ne' (hball hq)

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

-- Reading: NO-GO gauge. Neither `HomeoIso` nor `LipIso` is degenerate: the identity is a member at
-- every level (§ II), and the pair above is a non-member of both. This file exhibits no `HomeoIso`
-- lacking a `LipIso`.

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
-- Measured beside the levels: Mathlib's topology on `ℕ`, and the types the two upper levels name.
#print axioms instTopologicalSpaceNat
#print axioms TopologicalSpace
#print axioms Continuous
#print axioms PseudoEMetricSpace
#print axioms LipschitzWith
#print axioms ENNReal
#print axioms NNReal
end PurityCheck
