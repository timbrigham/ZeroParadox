-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): in an ultrametric space, dist x c < dist y c implies dist x y = dist y c; on ℤ_[2], doubling halves distances with image the closed ball of radius 1/2 about 0; for any two points, some isometry of ℤ_[2] sends the first to the second, and likewise some involutive homeomorphism of ℕ → Bool. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.Padic
import ZeroParadox.Valuation.PadicStillPoint
import ZeroParadox.Valuation.PadicErgodic
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# In an ultrametric space, dist x c < dist y c implies dist x y = dist y c; on ℤ_[2], doubling halves distance and has image the closed ball of radius 1/2 about 0; ℤ_[2] and ℕ → Bool are homogeneous: for any two points, some isometry of ℤ_[2], likewise some involutive homeomorphism of ℕ → Bool, sends the first to the second

## Engineer's Take

When I was visualizing the tree I was orbiting around and zooming in. The outside of my view distorted
like a fish bowl before dissolving the more distant points. When you zoom in and out, you see more detail
on the edges, kind of like lifting a fog around tree branches. It's ironic. It looks like a fluid version
of Yggdrasil in my mind, and the branches pop to the forefront as you spin the controls. The wave that
doesn't wave sounds like the orbit of zero.

---

## Formal Overview (AI-assisted)
`Statement:` CARRIER — the ultrametric isosceles property from a centre (any ultrametric space, then
`ℤ_[2]` with centre `0`), the doubling map on `ℤ_[2]`, and point-homogeneity of `ℤ_[2]` and, separately,
of `ℕ → Bool`; no map between those two carriers is stated.
-/

namespace ZeroParadox

open Metric

/-! ### § I. Isosceles from a centre -/

/-- `Statement:` in an ultrametric pseudometric space, `dist x c < dist y c` implies
`dist x y = dist y c`; one way. The case, with one strict inequality, of Mathlib's
`IsUltrametricDist.dist_eq_max_of_dist_ne_dist`; `c1_isosceles` is that lemma on `Q₂` (`example` below). -/
theorem fishbowl {X : Type*} [PseudoMetricSpace X] [IsUltrametricDist X] {x y c : X}
    (h : dist x c < dist y c) : dist x y = dist y c := by
  have hne : dist x c ≠ dist c y := by rw [dist_comm c y]; exact h.ne
  rw [IsUltrametricDist.dist_eq_max_of_dist_ne_dist x c y hne, dist_comm c y,
    max_eq_right h.le]

-- Statement: `c1_isosceles` (`ZeroParadox/Valuation/Padic.lean`) is Mathlib's ultrametric lemma on `Q₂`.
example (x y z : Q₂) (h : dist x y ≠ dist y z) : dist x z = max (dist x y) (dist y z) :=
  IsUltrametricDist.dist_eq_max_of_dist_ne_dist x y z h

/-- `Statement:` on `ℤ_[2]`, `‖x‖ < ‖y‖` implies `‖x - y‖ = ‖y‖`. -/
theorem fishbowl_Z2_norm {x y : ℤ_[2]} (h : ‖x‖ < ‖y‖) : ‖x - y‖ = ‖y‖ := by
  have := fishbowl (c := (0 : ℤ_[2])) (x := x) (y := y) (by simpa [dist_zero_right] using h)
  simpa [dist_eq_norm] using this

/-- `Statement:` on `ℤ_[2]`, if `y` lies in `shellSet m` (norm exactly `2^(-m)`) and
`‖x‖ < 2^(-m)`, then `dist x y = 2^(-m)`. -/
theorem fishbowl_Z2_shell (m : ℕ) {x y : ℤ_[2]} (hy : y ∈ shellSet (p := 2) m)
    (hx : ‖x‖ < (2 : ℝ) ^ (-(m : ℤ))) : dist x y = (2 : ℝ) ^ (-(m : ℤ)) := by
  have hny : ‖y‖ = ((2 : ℕ) : ℝ) ^ (-(m : ℤ)) := norm_eq_of_mem_shell m hy
  push_cast at hny
  rw [dist_eq_norm, fishbowl_Z2_norm (by rw [hny]; exact hx), hny]

-- Statement: CONTROL, the conclusion of `fishbowl` fails in ℝ: x = 1, y = 2, c = 0.
example : ∃ x y c : ℝ, dist x c < dist y c ∧ dist x y ≠ dist y c :=
  ⟨1, 2, 0, by norm_num [Real.dist_eq], by norm_num [Real.dist_eq]⟩

/-! ### § II. Doubling on ℤ_[2] -/

/-- `Statement:` `‖(2 : ℤ_[2])‖ = 1/2`. -/
theorem norm_two_Z2 : ‖(2 : ℤ_[2])‖ = 1 / 2 := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_cast, PadicInt.norm_p]; norm_num

/-- `Statement:` on `ℤ_[2]`, `dist (2 * x) (2 * y) = dist x y / 2`. -/
theorem zoom_dist (x y : ℤ_[2]) : dist (2 * x) (2 * y) = dist x y / 2 := by
  rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, norm_two_Z2]; ring

/-- `Statement:` the image of `x ↦ 2 * x` on `ℤ_[2]` is exactly `{z | ‖z‖ ≤ 1/2}`. -/
theorem zoom_range : Set.range (fun x : ℤ_[2] => 2 * x) = {z : ℤ_[2] | ‖z‖ ≤ 1 / 2} := by
  ext z
  have key := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) z 1
  rw [Ideal.mem_span_singleton, pow_one] at key
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  have h2 : ((2 : ℕ) : ℝ) ^ (-((1 : ℕ) : ℤ)) = 1 / 2 := by norm_num
  rw [h2] at key
  rw [key]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨x, by push_cast; ring⟩
  · rintro ⟨x, hx⟩; exact ⟨x, by rw [hx]; push_cast; ring⟩

/-! ### § III. Homogeneity -/

/-- `Statement:` for any `x y : ℤ_[2]`, some isometric bijection of `ℤ_[2]` sends `x` to `y`; the
proof's witness is translation by `y - x`. -/
theorem homog_Z2 (x y : ℤ_[2]) : ∃ e : ℤ_[2] ≃ᵢ ℤ_[2], e x = y :=
  ⟨IsometryEquiv.addLeft (y - x), by simp⟩

/-- `Statement:` for any `x y : ℤ_[2]`, some involutive isometric bijection of `ℤ_[2]` swaps `x` and
`y`; the proof's witness is `z ↦ x + y - z`. -/
theorem homog_Z2_swap (x y : ℤ_[2]) :
    ∃ e : ℤ_[2] ≃ᵢ ℤ_[2], e x = y ∧ e y = x ∧ Function.Involutive e :=
  ⟨IsometryEquiv.subLeft (x + y), by simp, by simp, fun z => by simp⟩

-- Statement: on `Q₂`, translation is an isometry: the `example` `dist (x - a) (y - a) = dist x y`
-- after `c3_irreversible` (`ZeroParadox/Valuation/Padic.lean`).

/-- `Statement:` pointwise xor with a fixed sequence `m`. -/
def xorWith (m : ℕ → Bool) (z : ℕ → Bool) : ℕ → Bool := fun n => xor (m n) (z n)

/-- `Statement:` `xorWith m` is its own inverse. -/
theorem xorWith_involutive (m : ℕ → Bool) : Function.Involutive (xorWith m) := by
  intro z; funext n; simp [xorWith]

/-- `Statement:` `xorWith m` is continuous for the product topology. -/
theorem xorWith_continuous (m : ℕ → Bool) : Continuous (xorWith m) :=
  continuous_pi fun n => continuous_of_discreteTopology.comp (continuous_apply n)

/-- `Statement:` `xorWith m` as a homeomorphism of `ℕ → Bool`. -/
def xorHomeo (m : ℕ → Bool) : (ℕ → Bool) ≃ₜ (ℕ → Bool) where
  toEquiv := (xorWith_involutive m).toPerm
  continuous_toFun := xorWith_continuous m
  continuous_invFun := xorWith_continuous m

/-- `Statement:` `xorHomeo m` is its own inverse. -/
theorem xorHomeo_symm (m : ℕ → Bool) : (xorHomeo m).symm = xorHomeo m := rfl

/-- `Statement:` for any `x y : ℕ → Bool`, some involutive homeomorphism of `ℕ → Bool` sends `x` to `y`. -/
theorem homog_cantor (x y : ℕ → Bool) :
    ∃ e : (ℕ → Bool) ≃ₜ (ℕ → Bool), e x = y ∧ Function.Involutive e :=
  ⟨xorHomeo (xorWith x y), by
      funext n; show xor (xor (x n) (y n)) (x n) = y n
      cases x n <;> cases y n <;> rfl,
    xorWith_involutive _⟩

/-! ### § IV. The orbit of `0` of ℤ_[2] and the trivial character, stated separately -/

-- Statement: the forward orbit of `0` of `ℤ_[2]` under `x ↦ x + 1` is dense: the `x = 0`, `p = 2`
-- case of `denseRange_odometer_orbit`.
example : DenseRange (fun n : ℕ => (0 : ℤ_[2]) + (n : ℤ_[2])) := denseRange_odometer_orbit 0
-- Statement: `paChar n 0`, the zero character `0` of `AddChar (ZMod (p ^ n)) ℂ` composed with
-- reduction mod `p ^ n`, which is the constant function `1` on `ℤ_[p]` (`paChar_trivial`), takes the
-- same value at `c + x` as at `x`. Reading: CARRIER — `0` of `ℤ_[2]` moves and its orbit is dense;
-- the function `paChar n 0` on `ℤ_[p]` is fixed by every translation; no equation between the two is stated.
#check @stillPoint_koopman_fixed

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms fishbowl
#print axioms fishbowl_Z2_norm
#print axioms fishbowl_Z2_shell
#print axioms norm_two_Z2
#print axioms zoom_dist
#print axioms zoom_range
#print axioms homog_Z2
#print axioms homog_Z2_swap
#print axioms xorWith
#print axioms xorWith_involutive
#print axioms xorWith_continuous
#print axioms xorHomeo
#print axioms xorHomeo_symm
#print axioms homog_cantor
end PurityCheck
