-- EXPERIMENTAL (branch scaffolding): bottom-diagram probe campaign, not a finalized layer. Curated/load-bearing results are indexed in ZeroParadox/ZPH_BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.ZPB
import ZeroParadox.ZPH_TopFunctor
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# ZP-H MC-1 TC10: the p-adic floor `{0}` is a genuine categorical limit cone

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`ZPH_TopFunctor.fB_bottom_is_limit` proves the *set* equation `⋂ n, q2Ball n = {0}`: the
intersection of the shrinking clopen balls `B(0, 2⁻ⁿ) ⊆ Q₂` is exactly the snap floor `{0}`.
That is a statement in `Set Q₂`, not in `TopCat`. The campaign question (TH10) was whether the
node #3 is a *genuine* ν / categorical limit, i.e. whether the snap floor is the **limit object**
of the inverse system `fB_functor : ℕᵒᵖ ⥤ TopCat` with an honest `IsLimit` cone — not merely a
set intersection that happens to coincide.

This file builds that cone and proves it.

- `floorCone : Cone fB_functor` — point `TopCat.of ↥({0} : Set Q₂)` (the snap floor as a
  one-point topological space), legs the continuous inclusions `{0} ↪ q2Ball n`.
- `floorConeIsLimit : IsLimit floorCone` — the load-bearing result. Any cone over the inverse
  system factors *uniquely* through the snap floor. The `fac` leg is where the real content lives:
  a compatible family of ball-points has a single underlying `Q₂` value lying in *every* ball, so
  by `fB_bottom_is_limit` it is `0`. Uniqueness is automatic (the apex is a subsingleton), but
  existence of the factoring map is exactly the intersection theorem promoted to a universal
  property.
- `fB_limit_iso_floor : limit fB_functor ≅ TopCat.of ↥({0} : Set Q₂)` — the canonical Mathlib
  limit object is homeomorphic to the snap floor, the categorical upgrade of `fB_bottom_is_limit`.

**What is witnessed vs interpreted.** The `IsLimit` and the iso are the witnesses: `{0}` is a true
limit object of the real `TopCat` diagram, not a set coincidence. The *interpretation* (this is the
"ν / limit face" of the cross-framework diagonal fixed point) is framework prose, not a Lean claim.
-/

namespace ZeroParadox.ZPH_MC1_TC10

open ZeroParadox.ZPB
open ZeroParadox.ZPH_TopFunctor
open CategoryTheory CategoryTheory.Limits

/-- `0` lies in every clopen ball of the snap chain. -/
theorem zero_mem_q2Ball (n : ℕ) : (0 : Q₂) ∈ q2Ball n := by
  simp only [q2Ball, Metric.mem_closedBall, dist_self]
  positivity

/-- The snap floor `{0}` includes into each ball `q2Ball n`. -/
theorem floor_subset_q2Ball (n : ℕ) : ({(0 : Q₂)} : Set Q₂) ⊆ q2Ball n := by
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact zero_mem_q2Ball n

/-- The snap floor `{0}` as a topological space, the candidate limit object. -/
noncomputable def floorPt : TopCat := TopCat.of ↥({(0 : Q₂)} : Set Q₂)

/-- A leg of the candidate cone: the continuous inclusion `{0} ↪ q2Ball n`. -/
noncomputable def floorLeg (n : ℕ) : C(↥({(0 : Q₂)} : Set Q₂), ↥(q2Ball n)) :=
  ⟨Set.inclusion (floor_subset_q2Ball n), continuous_inclusion (floor_subset_q2Ball n)⟩

/-- The candidate limit cone: the snap floor `{0}` with the inclusion legs into each ball. -/
noncomputable def floorCone : Cone fB_functor where
  pt := floorPt
  π :=
    { app := fun n => TopCat.ofHom (floorLeg n.unop)
      naturality := by
        intro m n f
        ext x
        rfl }

/-- The underlying `Q₂` value of `floorLeg n` applied to the unique floor point is `0`. -/
@[simp] theorem floorLeg_val (n : ℕ) (x : ↥({(0 : Q₂)} : Set Q₂)) :
    (floorLeg n x).val = (0 : Q₂) := by
  have : x.val = (0 : Q₂) := x.2
  simpa [floorLeg, Set.inclusion] using this

/-- The underlying `Q₂` value of a cone leg at index `n`, applied to `x : S.pt`. We name it
explicitly to force the carrier `fB_functor.obj (op n)` to reduce to the subtype `↥(q2Ball n)`
so that the `Subtype.val` coercion to `Q₂` is available. -/
noncomputable def legVal (S : Cone fB_functor) (x : S.pt) (n : ℕ) : Q₂ :=
  (show ↥(q2Ball n) from S.π.app (Opposite.op n) x).val

/-- `legVal` lands in its own ball. -/
theorem legVal_mem (S : Cone fB_functor) (x : S.pt) (n : ℕ) :
    legVal S x n ∈ q2Ball n :=
  (show ↥(q2Ball n) from S.π.app (Opposite.op n) x).2

/-- Compatibility: the inclusions are value-preserving, so for `m ≤ n` the `Q₂` value of the
`m`-leg equals that of the `n`-leg at any point `x : S.pt`. -/
theorem cone_val_const (S : Cone fB_functor) (x : S.pt) {m n : ℕ} (h : m ≤ n) :
    legVal S x n = legVal S x m := by
  -- the morphism `op n ⟶ op m` in `ℕᵒᵖ` induced by `m ≤ n`
  have hnat := S.π.naturality (Quiver.Hom.op (homOfLE h))
  -- evaluate the naturality square at `x`, then take underlying `Q₂` values
  have hx := congrArg Subtype.val (ConcreteCategory.congr_hom hnat x)
  -- `fB_functor.map` is a value-preserving inclusion; `legVal` is already the `.val`
  simp only [legVal]
  simpa [fB_functor, fBIncl, fBObj, Set.coe_inclusion, Function.comp,
    TopCat.hom_comp, ContinuousMap.comp] using hx.symm

/-- The underlying `Q₂` value of any cone leg `legVal S x n` is `0`: it lies in every ball
(by `cone_val_const` collapsing all legs to one value) and hence in `⋂ q2Ball n = {0}`. -/
theorem cone_val_eq_zero (S : Cone fB_functor) (x : S.pt) (n : ℕ) :
    legVal S x n = 0 := by
  -- the value at leg `n` lies in `q2Ball k` for every `k`
  have hmem : legVal S x n ∈ ⋂ k, q2Ball k := by
    rw [Set.mem_iInter]
    intro k
    rcases le_total n k with hnk | hkn
    · -- k ≥ n : value at leg k equals val at leg n, and lives in q2Ball k
      have hk := cone_val_const S x hnk
      have hmemk := legVal_mem S x k
      rwa [hk] at hmemk
    · -- k ≤ n : value at leg n lands in q2Ball k via antitonicity
      exact q2Ball_antitone hkn (legVal_mem S x n)
  rw [fB_bottom_is_limit, Set.mem_singleton_iff] at hmem
  exact hmem

/-- **The payload.** The snap floor `{0}` with its inclusion cone is a genuine categorical limit
of the inverse system `fB_functor : ℕᵒᵖ ⥤ TopCat`. Existence of the factoring map is exactly the
intersection theorem `fB_bottom_is_limit` promoted to a universal property; uniqueness is automatic
(the apex `{0}` is a subsingleton). -/
noncomputable def floorConeIsLimit : IsLimit floorCone where
  lift S := TopCat.ofHom
    { toFun := fun _ => ⟨(0 : Q₂), rfl⟩
      continuous_toFun := continuous_const }
  fac S n := by
    ext x
    -- both sides are points of `q2Ball n.unop`; compare underlying `Q₂` values
    apply Subtype.ext
    -- LHS value is the floor point's value = 0; RHS value is `legVal S x n.unop = 0`
    show ((floorLeg n.unop ⟨(0 : Q₂), rfl⟩ : ↥(q2Ball n.unop)) : Q₂)
        = (show ↥(q2Ball n.unop) from S.π.app n x).val
    rw [floorLeg_val]
    exact (cone_val_eq_zero S x n.unop).symm
  uniq S m _ := by
    ext x
    -- apex `{0}` is a subsingleton, so any two maps into it agree
    apply Subtype.ext
    have h1 : (show ↥({(0 : Q₂)} : Set Q₂) from m x).val = 0 :=
      (show ↥({(0 : Q₂)} : Set Q₂) from m x).2
    rw [h1]
    rfl

/-- The canonical Mathlib limit object of the snap chain is homeomorphic to the snap floor `{0}`:
the categorical upgrade of the set equation `fB_bottom_is_limit`. -/
noncomputable def fB_limit_iso_floor : limit fB_functor ≅ floorPt :=
  (limit.isLimit fB_functor).conePointUniqueUpToIso floorConeIsLimit

end ZeroParadox.ZPH_MC1_TC10

/-! ## Axiom Purity Check

`Classical.choice` is expected: it enters through Mathlib's `TopCat` / limits / metric library,
the same dependency carried by `ZPH_TopFunctor` and the ZP-B topology layer. It is a library
dependency, not a new commitment of this construction. -/

section PurityCheck
open ZeroParadox.ZPH_MC1_TC10

#print axioms zero_mem_q2Ball
#print axioms floorCone
#print axioms cone_val_eq_zero
#print axioms floorConeIsLimit
#print axioms fB_limit_iso_floor

end PurityCheck
