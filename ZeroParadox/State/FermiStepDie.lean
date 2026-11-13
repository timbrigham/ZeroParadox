import ZeroParadox.Die
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic

/-!
# The cold logistic step as a die: the zero-temperature limit of the sigmoid is the UP of a three-landing die, and the sigmoid's point symmetry is a strict isomorphism of that die, onto the reversed die when OVER is ordered

## Engineer's Take

I get the weird feeling that if we were to mirror our up and over motion dead through the middle
of that sigmoid, it is the same thing, or maybe an echo is a better word. It's worth publishing if
it's the same shape as something regularly described.

---
## Formal Overview (AI-assisted)
`Real.sign` is idempotent, so it is the UP of a die on ℝ whose landings are `-1`, `0`, `1` (§ I).
`Real.sigmoid (β * x)` tends to `(Real.sign x + 1) / 2` as `β → ∞`, at every `x` (§ II). Negation
commutes with that UP: a strict self-isomorphism under a symmetric OVER, a strict isomorphism onto
`Motion.reverse` under OVER `<`, and not a strict self-map under `<` (§ III).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Filter Topology

/-! ### § I. The sign map as a total UP -/

/-- `Statement:` `Real.sign` is idempotent. -/
theorem real_sign_idem (x : ℝ) : Real.sign (Real.sign x) = Real.sign x := by
  rcases Real.sign_apply_eq x with h | h | h <;> rw [h]
  · exact Real.sign_of_neg (by norm_num)
  · exact Real.sign_zero
  · exact Real.sign_one

/-- `Statement:` the die on ℝ with UP `Real.sign` and OVER the relation `st`. -/
noncomputable def signDie (st : ℝ → ℝ → Prop) : Motion ℝ :=
  Motion.ofTotal Real.sign real_sign_idem st

/-- `Statement:` the landings of `signDie st` are exactly `-1`, `0` and `1`; both directions. -/
theorem isLanding_signDie_iff (st : ℝ → ℝ → Prop) (y : ℝ) :
    (signDie st).IsLanding y ↔ y = -1 ∨ y = 0 ∨ y = 1 := by
  show y ∈ Part.some (Real.sign y) ↔ _
  rw [Part.mem_some_iff]
  constructor
  · intro h; rw [h]; exact Real.sign_apply_eq y
  · rintro (rfl | rfl | rfl)
    · exact (Real.sign_of_neg (by norm_num)).symm
    · exact Real.sign_zero.symm
    · exact Real.sign_one.symm

/-! ### § II. The zero-temperature limit of the sigmoid
`Reading:` with `x = µ - E`, `Real.sigmoid (β * x)` is the Fermi–Dirac occupation (D. Tong, *Statistical
Physics* (Cambridge Part II lecture notes), § 3.6, eq. (3.37), p. 91); Tong's `T → 0` step (§ 3.6.2,
p. 92) is for `E ≠ µ` only, and the `1 / 2` at `E = µ` is `Real.sigmoid_zero`. The heat-bath use of
the same sigmoid is `ZeroParadox/Information/PoleWithinEnsemble.lean` § VIII. -/

/-- `Statement:` `Real.sigmoid (β * x) → (Real.sign x + 1) / 2` as `β → ∞`, at every `x`, `x = 0`
    included. -/
theorem sigmoid_cold_limit_is_sign (x : ℝ) :
    Tendsto (fun β : ℝ => Real.sigmoid (β * x)) atTop (𝓝 ((Real.sign x + 1) / 2)) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx]; norm_num
    exact Real.tendsto_sigmoid_atBot.comp (tendsto_id.atTop_mul_const_of_neg hx)
  · simp only [mul_zero, Real.sigmoid_zero, Real.sign_zero]; norm_num
  · rw [Real.sign_of_pos hx]; norm_num
    exact Real.tendsto_sigmoid_atTop.comp (tendsto_id.atTop_mul_const hx)

/-- `Statement:` `(-s + 1) / 2 = 1 - (s + 1) / 2`. `Reading:` under `y ↦ (y + 1) / 2`, negating `Real.sign x` is `y ↦ 1 - y`, the mirror law `Real.sigmoid_neg` (`unitInterval.sigmoid_neg`). -/
theorem signDie_mirrors_agree (s : ℝ) : (-s + 1) / 2 = 1 - (s + 1) / 2 := by ring

/-! ### § III. The mirror `x ↦ -x` as a symmetry of the die
`Reading:` `Real.sigmoid_neg` is the Fermi–Dirac symmetry around the chemical potential,
f(µ + δ) = 1 − f(µ − δ), usually interpreted as particle–hole symmetry (Grabsch, Majumdar, Schehr,
Texier, arXiv:1711.07770v2, § 3, eq. (59), p. 14). `Real.sign` is an odd (Z/2-equivariant)
idempotent (`Real.sign_neg`). -/

/-- `Statement:` negation as a strict map `signDie st → signDie st'`, for any `st` it carries into
    `st'`. -/
noncomputable def signDieMirrorHom (st st' : ℝ → ℝ → Prop) (h : ∀ {a b}, st a b → st' (-a) (-b)) :
    Motion.Hom (signDie st) (signDie st') :=
  ⟨fun x => -x, h, fun x => by
    show Part.some (Real.sign (-x)) = (Part.some (Real.sign x)).map (fun x => -x)
    rw [Part.map_some, Real.sign_neg]⟩

/-- `Statement:` with OVER `≠`, negation is a strict self-isomorphism of the die. -/
noncomputable def signDieMirrorAuto : Motion.StrictIso (signDie (· ≠ ·)) (signDie (· ≠ ·)) where
  hom := signDieMirrorHom _ _ (fun h => fun e => h (neg_inj.1 e))
  inv := signDieMirrorHom _ _ (fun h => fun e => h (neg_inj.1 e))
  left_inv := neg_neg
  right_inv := neg_neg

/-- `Statement:` with OVER `<`, negation is a strict isomorphism onto the reversed die.
    `Reading:` `Motion.not_exists_involution_reverses_lt` excludes such an involution under `OrderBot`
    and `NoMaxOrder`; ℝ has no least element, as ℤ, the negation control in `DieCannotBe.lean` § XIV. -/
noncomputable def signDieMirrorReverse :
    Motion.StrictIso (signDie (· < ·)) (signDie (· < ·)).reverse where
  hom := ⟨fun x => -x, fun h => neg_lt_neg h, fun x => by
    show Part.some (Real.sign (-x)) = (Part.some (Real.sign x)).map (fun x => -x)
    rw [Part.map_some, Real.sign_neg]⟩
  inv := ⟨fun x => -x, fun {a b} (h : b < a) => (neg_lt_neg h : -a < -b), fun x => by
    show Part.some (Real.sign (-x)) = (Part.some (Real.sign x)).map (fun x => -x)
    rw [Part.map_some, Real.sign_neg]⟩
  left_inv := neg_neg
  right_inv := neg_neg

/-- `Statement:` CONTROL, with OVER `<` no strict map of the die to itself has negation as its map. -/
theorem signDie_mirror_not_self_hom :
    ¬ ∃ φ : Motion.Hom (signDie (· < ·)) (signDie (· < ·)), ∀ x, φ.toFun x = -x := by
  rintro ⟨φ, hφ⟩
  have h := @Motion.Hom.map_step _ _ _ _ φ 0 1 (by norm_num : (0 : ℝ) < 1)
  simp only [signDie, Motion.ofTotal, hφ] at h
  norm_num at h

/-- `Statement:` negation fixes `0`, sends `1` to `-1` and `-1` to `1`, and fixes no other real. -/
theorem signDie_mirror_on_landings :
    (-(0 : ℝ) = 0) ∧ (-(1 : ℝ) = -1) ∧ (-(-1 : ℝ) = 1) ∧ ∀ y : ℝ, -y = y ↔ y = 0 :=
  ⟨neg_zero, rfl, neg_neg 1, fun y => ⟨fun h => by linarith, fun h => by rw [h, neg_zero]⟩⟩

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms real_sign_idem
#print axioms signDie
#print axioms isLanding_signDie_iff
#print axioms sigmoid_cold_limit_is_sign
#print axioms signDie_mirrors_agree
#print axioms signDieMirrorHom
#print axioms signDieMirrorAuto
#print axioms signDieMirrorReverse
#print axioms signDie_mirror_not_self_hom
#print axioms signDie_mirror_on_landings

end PurityCheck
