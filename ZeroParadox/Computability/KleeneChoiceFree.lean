import Mathlib.Computability.PartrecCode
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Kleene's second recursion theorem for transformations given as codes, choice-free

## Engineer's Take

Self reference is execution. Copying yourself inside is self reference, with the data being
passed to an internal "copy" endpoint. That's an execution by replication, and it sounds like
a computer worm. The only difference you see between the copies is the address, and that
address of an otherwise identical copy of the infinity data is what stops it from being
incompressible compared to the next instance. Selecting one instance of bottom out of the
infinitude introduces choice. Building the address does not. A version of this choice free
recursion theorem has cropped up several times in our old discussions, and it should be a
priority item if it keeps repeating itself.

---

`Statement:` for every code `cψ`, `eval (fpCF cψ) x = eval cψ (Nat.pair (encodeCode (fpCF cψ)) x)`
(`kleene_cf`), with `fpCF` an explicit term; a fixed point up to `eval`, never a literal one. Not
proved here: the `Partrec₂` form (Mathlib's `fixed_point₂`), a universal code, or that selecting a
code by its behaviour needs `Classical.choice`. Footprints: `PurityCheck` at the end of this file.
-/

namespace ZeroParadox

open Nat.Partrec Nat.Partrec.Code

/-! ## § I. Integer square root and pairing -/

/-- `Statement:` `4ab ≤ (a + b)²` on `ℕ`, choice-free proof. -/
theorem cf_amgm (a b : ℕ) : 4 * (a * b) ≤ (a + b) * (a + b) := by
  rcases Nat.le_total a b with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e1 : (a + (a + d)) * (a + (a + d)) = 4 * (a * a) + 4 * (a * d) + d * d := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm d a]; omega
    have e2 : a * (a + d) = a * a + a * d := Nat.mul_add a a d
    omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e1 : (b + d + b) * (b + d + b) = 4 * (b * b) + 4 * (b * d) + d * d := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_comm d b]; omega
    have e2 : (b + d) * b = b * b + b * d := by rw [Nat.mul_comm, Nat.mul_add]
    omega

/-- `Statement:` `(s + 1)² = s² + 2s + 1` on `ℕ`, choice-free proof. -/
theorem cf_sq_succ (s : ℕ) : (s + 1) * (s + 1) = s * s + s + s + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

/-- `Statement:` same type as Mathlib's `Nat.sqrt.iter_sq_le`, choice-free proof. -/
theorem cf_sqrt_iter_sq_le (n : ℕ) : ∀ g, Nat.sqrt.iter n g * Nat.sqrt.iter n g ≤ n := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    rw [Nat.sqrt.iter]
    split
    · next h => exact ih _ h
    · next h =>
      rcases Nat.eq_zero_or_pos g with hg | hg
      · subst hg; exact Nat.zero_le _
      · have h1 : g ≤ (g + n / g) / 2 := Nat.le_of_not_lt h
        have h2 : g * 2 ≤ g + n / g := (Nat.le_div_iff_mul_le (by decide)).1 h1
        have h3 : g ≤ n / g := by
          generalize n / g = q at h2 ⊢
          omega
        exact (Nat.le_div_iff_mul_le hg).1 h3

/-- `Statement:` same type as Mathlib's `Nat.sqrt.lt_iter_succ_sq`, choice-free proof. -/
theorem cf_sqrt_lt_iter_succ_sq (n : ℕ) : ∀ g, n < (g + 1) * (g + 1) →
    n < (Nat.sqrt.iter n g + 1) * (Nat.sqrt.iter n g + 1) := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro hn
    rw [Nat.sqrt.iter]
    split
    · next h =>
      apply ih _ h
      have hg : 0 < g := Nat.lt_of_le_of_lt (Nat.zero_le _) h
      have hdm : g * (n / g) + n % g = n := Nat.div_add_mod n g
      have hr : n % g < g := Nat.mod_lt _ hg
      generalize n / g = q at h hdm ⊢
      generalize n % g = r at hr hdm
      have hm2 : 2 * ((g + q) / 2) + (g + q) % 2 = g + q := Nat.div_add_mod (g + q) 2
      have hm3 : (g + q) % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize (g + q) / 2 = m at h hm2 ⊢
      generalize (g + q) % 2 = t at hm2 hm3
      have am : 4 * (g * (q + 1)) ≤ (g + (q + 1)) * (g + (q + 1)) := cf_amgm g (q + 1)
      have hsq : (g + (q + 1)) * (g + (q + 1)) ≤ (2 * m + 2) * (2 * m + 2) :=
        Nat.mul_self_le_mul_self (by omega)
      have e1 : (2 * m + 2) * (2 * m + 2) = 4 * ((m + 1) * (m + 1)) := by
        simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
        rw [Nat.mul_comm 2 m, Nat.mul_assoc, Nat.mul_left_comm 2 m 2, ← Nat.mul_assoc m m]
        omega
      have e2 : g * (q + 1) = g * q + g := Nat.mul_succ g q
      omega
    · exact hn

/-- `Statement:` Mathlib's `Nat.sqrt_le` and `Nat.lt_succ_sqrt` as one conjunction, choice-free. -/
theorem cf_sqrt_isSqrt (n : ℕ) :
    Nat.sqrt n * Nat.sqrt n ≤ n ∧ n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
  unfold Nat.sqrt
  split
  · next h =>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl
    · exact ⟨Nat.le_refl _, by decide⟩
    · exact ⟨Nat.le_refl _, by decide⟩
  · next h =>
    refine ⟨cf_sqrt_iter_sq_le _ _, cf_sqrt_lt_iter_succ_sq _ _ ?_⟩
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    have hl : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    have hj : 2 * (n.log2 / 2) + n.log2 % 2 = n.log2 := Nat.div_add_mod _ 2
    have hj2 : n.log2 % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize n.log2 / 2 = j at hj ⊢
    generalize n.log2 = k at hl hj hj2
    generalize n.log2 % 2 = t at hj hj2
    have hp : 2 ^ (k + 1) ≤ 2 ^ (j + 1) * 2 ^ (j + 1) := by
      rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : 2 ^ (j + 1) * 2 ^ (j + 1) < (2 ^ (j + 1) + 1) * (2 ^ (j + 1) + 1) :=
      Nat.mul_self_lt_mul_self (Nat.lt_succ_self _)
    omega

/-- `Statement:` `q² ≤ n < (q + 1)²` forces `Nat.sqrt n = q`, choice-free proof. -/
theorem cf_sqrt_eq_of {n q : ℕ} (h1 : q * q ≤ n) (h2 : n < (q + 1) * (q + 1)) :
    Nat.sqrt n = q := by
  obtain ⟨s1, s2⟩ := cf_sqrt_isSqrt n
  generalize Nat.sqrt n = s at s1 s2
  rcases Nat.lt_trichotomy s q with h | h | h
  · have : (s + 1) * (s + 1) ≤ q * q := Nat.mul_self_le_mul_self h
    omega
  · exact h
  · have : (q + 1) * (q + 1) ≤ s * s := Nat.mul_self_le_mul_self h
    omega

/-- `Statement:` same type as Mathlib's `Nat.sqrt_le_self`, choice-free proof. -/
theorem cf_sqrt_le_self (n : ℕ) : Nat.sqrt n ≤ n := by
  have h := (cf_sqrt_isSqrt n).1
  rcases Nat.eq_zero_or_pos (Nat.sqrt n) with h0 | h0
  · omega
  · exact Nat.le_trans (Nat.le_mul_of_pos_left _ h0) h

/-- `Statement:` same type as Mathlib's `Nat.pair_unpair`, choice-free proof. -/
theorem cf_pair_unpair (n : ℕ) : Nat.pair (Nat.unpair n).1 (Nat.unpair n).2 = n := by
  obtain ⟨h1, h2⟩ := cf_sqrt_isSqrt n
  have e := cf_sq_succ (Nat.sqrt n)
  unfold Nat.unpair
  dsimp only
  generalize Nat.sqrt n = s at h1 h2 e
  split
  · next h =>
    show Nat.pair (n - s * s) s = n
    unfold Nat.pair
    rw [if_pos h]
    omega
  · next h =>
    show Nat.pair s (n - s * s - s) = n
    unfold Nat.pair
    have hn : ¬ s < n - s * s - s := by omega
    rw [if_neg hn]
    omega

/-- `Statement:` same type as Mathlib's `Nat.unpair_pair`, choice-free proof. -/
theorem cf_unpair_pair (a b : ℕ) : Nat.unpair (Nat.pair a b) = (a, b) := by
  unfold Nat.pair
  split
  · next h =>
    have hs : Nat.sqrt (b * b + a) = b :=
      cf_sqrt_eq_of (Nat.le_add_right _ _) (by rw [cf_sq_succ]; omega)
    unfold Nat.unpair
    dsimp only
    rw [hs, if_pos (by omega), show b * b + a - b * b = a by omega]
  · next h =>
    have hs : Nat.sqrt (a * a + a + b) = a :=
      cf_sqrt_eq_of (by omega) (by rw [cf_sq_succ]; omega)
    unfold Nat.unpair
    dsimp only
    rw [hs, if_neg (by omega), show a * a + a + b - a * a - a = b by omega]

/-- `Statement:` same type as Mathlib's `Nat.unpair_left_le`, choice-free proof. -/
theorem cf_unpair_left_le (n : ℕ) : (Nat.unpair n).1 ≤ n := by
  have hs := cf_sqrt_le_self n
  unfold Nat.unpair
  dsimp only
  generalize Nat.sqrt n = s at hs
  split
  · show n - s * s ≤ n; omega
  · show s ≤ n; exact hs

/-- `Statement:` same type as Mathlib's `Nat.unpair_right_le`, choice-free proof. -/
theorem cf_unpair_right_le (n : ℕ) : (Nat.unpair n).2 ≤ n := by
  have hs := cf_sqrt_le_self n
  unfold Nat.unpair
  dsimp only
  generalize Nat.sqrt n = s at hs
  split
  · show s ≤ n; exact hs
  · show n - s * s - s ≤ n; omega

/-- `Statement:` the low bit plus twice `Nat.div2 n` is `n`, choice-free proof. -/
theorem cf_bodd_add_div2 : ∀ n, (Nat.bodd n).toNat + 2 * Nat.div2 n = n
  | 0 => rfl
  | n + 1 => by
    have ih := cf_bodd_add_div2 n
    rw [Nat.bodd_succ, Nat.div2_succ]
    cases hb : Nat.bodd n <;> rw [hb] at ih
    · show 1 + 2 * Nat.div2 n = n + 1
      have : (false : Bool).toNat = 0 := rfl
      rw [this] at ih; omega
    · show 0 + 2 * (Nat.div2 n + 1) = n + 1
      have : (true : Bool).toNat = 1 := rfl
      rw [this] at ih; omega

/-- `Statement:` same type as Mathlib's `Nat.div2_val`, choice-free proof. -/
theorem cf_div2_val (n : ℕ) : Nat.div2 n = n / 2 := by
  have h1 := cf_bodd_add_div2 n
  have h2 := Nat.div_add_mod n 2
  have h3 : n % 2 < 2 := Nat.mod_lt _ (by decide)
  have h4 : (Nat.bodd n).toNat < 2 := by cases Nat.bodd n <;> decide
  generalize n / 2 = q at h2 ⊢
  generalize n % 2 = r at h2 h3
  generalize (Nat.bodd n).toNat = b at h1 h4
  omega

/-! ## § II. Evaluation on Mathlib's `Code` -/

/-- `Statement:` `succ` adds one, by `rfl`. -/
theorem cf_eval_succ (n : ℕ) : eval succ n = Part.some (n + 1) := rfl

/-- `Statement:` `left` returns the first component of a pair. -/
theorem cf_eval_left (a b : ℕ) : eval left (Nat.pair a b) = Part.some a := by
  show Part.some (Nat.unpair (Nat.pair a b)).1 = _
  rw [cf_unpair_pair]

/-- `Statement:` `right` returns the second component of a pair. -/
theorem cf_eval_right (a b : ℕ) : eval right (Nat.pair a b) = Part.some b := by
  show Part.some (Nat.unpair (Nat.pair a b)).2 = _
  rw [cf_unpair_pair]

/-- `Statement:` `pair cf cg` on total arguments returns the pair of their values. -/
theorem cf_eval_pair {cf cg : Code} {n a b : ℕ} (h1 : eval cf n = Part.some a)
    (h2 : eval cg n = Part.some b) : eval (pair cf cg) n = Part.some (Nat.pair a b) := by
  show Nat.pair <$> eval cf n <*> eval cg n = _
  rw [h1, h2, Part.map_eq_map, Part.map_some]
  show Part.bind (Part.some (Nat.pair a)) (fun f => f <$> Part.some b) = _
  rw [Part.bind_some, Part.map_eq_map, Part.map_some]

/-- `Statement:` `comp cf cg` runs `cf` on the value of `cg`. -/
theorem cf_eval_comp {cf cg : Code} {n a : ℕ} (h : eval cg n = Part.some a) :
    eval (comp cf cg) n = eval cf a := by
  show eval cg n >>= eval cf = _
  rw [h, Part.bind_eq_bind, Part.bind_some]

/-- `Statement:` `comp cf cg` on two total stages returns the second stage's value. -/
theorem cf_eval_comp_some {cf cg : Code} {n a b : ℕ} (h : eval cg n = Part.some a)
    (h' : eval cf a = Part.some b) : eval (comp cf cg) n = Part.some b :=
  (cf_eval_comp h).trans h'

/-- `Statement:` same type as Mathlib's `Nat.Partrec.Code.eval_id`, choice-free proof. -/
theorem cf_eval_id (n : ℕ) : eval Code.id n = Part.some n := by
  have h := cf_eval_pair (cf := left) (cg := right) (n := n) rfl rfl
  rw [cf_pair_unpair] at h
  exact h

/-- `Statement:` same type as Mathlib's `Nat.Partrec.Code.eval_curry`, choice-free proof. -/
theorem cf_eval_curry (c : Code) (m x : ℕ) : eval (curry c m) x = eval c (Nat.pair m x) :=
  cf_eval_comp (cf_eval_pair (eval_const m x) (cf_eval_id x))

/-- `Statement:` same type as Mathlib's `Nat.Partrec.Code.eval_prec_zero`, choice-free proof. -/
theorem cf_eval_prec_zero (cf cg : Code) (a : ℕ) :
    eval (prec cf cg) (Nat.pair a 0) = eval cf a := by
  rw [eval]
  simp only [Nat.unpaired, cf_unpair_pair]
  rfl

/-- `Statement:` same type as Mathlib's `Nat.Partrec.Code.eval_prec_succ`, choice-free proof. -/
theorem cf_eval_prec_succ (cf cg : Code) (a k : ℕ) :
    eval (prec cf cg) (Nat.pair a (k + 1)) =
      eval (prec cf cg) (Nat.pair a k) >>= fun i => eval cg (Nat.pair a (Nat.pair k i)) := by
  rw [eval]
  simp only [Nat.unpaired, cf_unpair_pair]

/-- `Statement:` `prec cf cg` with total base and step computes the recursion `f`. -/
theorem cf_eval_prec_total {cf cg : Code} {a : ℕ} (f : ℕ → ℕ) (h0 : eval cf a = Part.some (f 0))
    (hs : ∀ k, eval cg (Nat.pair a (Nat.pair k (f k))) = Part.some (f (k + 1))) :
    ∀ k, eval (prec cf cg) (Nat.pair a k) = Part.some (f k) := by
  intro k
  induction k with
  | zero => rw [cf_eval_prec_zero, h0]
  | succ k ih => rw [cf_eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some, hs]

/-! ## § III. The address arithmetic as codes -/

/-- `Statement:` the code running `P` on `Nat.pair 0 y` at input `y`. -/
def cfUnary (P : Code) : Code := comp P (pair zero Code.id)

/-- `Statement:` `cfUnary P` on `y` is `P` on `Nat.pair 0 y`. -/
theorem cf_eval_unary (P : Code) (y : ℕ) : eval (cfUnary P) y = eval P (Nat.pair 0 y) :=
  cf_eval_comp (cf_eval_pair rfl (cf_eval_id y))

/-- `Statement:` the code `x ↦ x + 4`. -/
def cfAdd4 : Code := comp succ (comp succ (comp succ succ))

/-- `Statement:` `cfAdd4` adds four. -/
theorem cf_eval_add4 (x : ℕ) : eval cfAdd4 x = Part.some (x + 4) :=
  cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some rfl rfl) rfl) rfl

/-- `Statement:` the doubling step `(a, (k, i)) ↦ i + 2`. -/
def cfAdd2Step : Code := comp succ (comp succ (comp right right))

/-- `Statement:` the code `y ↦ 2 * y`. -/
def cfDouble : Code := cfUnary (prec zero cfAdd2Step)

/-- `Statement:` `cfDouble` doubles. -/
theorem cf_eval_double (y : ℕ) : eval cfDouble y = Part.some (2 * y) := by
  unfold cfDouble
  rw [cf_eval_unary]
  refine cf_eval_prec_total (fun k => 2 * k) rfl (fun k => ?_) y
  show eval cfAdd2Step (Nat.pair 0 (Nat.pair k (2 * k))) = Part.some (2 * (k + 1))
  exact cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some (cf_eval_right _ _)
    (cf_eval_right _ _)) rfl) rfl

/-- `Statement:` the step of `k ↦ encodeCode (Code.const k)`. -/
def cfEncConstStep : Code :=
  comp cfAdd4 (comp cfDouble (comp succ (comp cfDouble (pair (Code.const 1) (comp right right)))))

/-- `Statement:` the code `y ↦ encodeCode (Code.const y)`. -/
def cfEncConst : Code := cfUnary (prec zero cfEncConstStep)

/-- `Statement:` the Gödel number of `Code.const (k + 1)` from that of `Code.const k`, by `rfl`. -/
theorem cf_encodeCode_const_succ (k : ℕ) :
    encodeCode (Code.const (k + 1)) = 2 * (2 * Nat.pair 1 (encodeCode (Code.const k)) + 1) + 4 :=
  rfl

/-- `Statement:` `cfEncConst` computes `y ↦ encodeCode (Code.const y)`. -/
theorem cf_eval_encConst (y : ℕ) : eval cfEncConst y = Part.some (encodeCode (Code.const y)) := by
  unfold cfEncConst
  rw [cf_eval_unary]
  refine cf_eval_prec_total (fun k => encodeCode (Code.const k)) rfl (fun k => ?_) y
  show eval cfEncConstStep (Nat.pair 0 (Nat.pair k (encodeCode (Code.const k)))) =
    Part.some (encodeCode (Code.const (k + 1)))
  rw [cf_encodeCode_const_succ]
  have hr : eval (comp right right) (Nat.pair 0 (Nat.pair k (encodeCode (Code.const k)))) =
      Part.some (encodeCode (Code.const k)) :=
    cf_eval_comp_some (cf_eval_right _ _) (cf_eval_right _ _)
  exact cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some
    (cf_eval_pair (eval_const 1 _) hr) (cf_eval_double _)) rfl) (cf_eval_double _))
    (cf_eval_add4 _)

/-- `Statement:` the Gödel number of `curry d n`, as a function of `y = encodeCode d` and `n`. -/
def cfCurryIndex (y n : ℕ) : ℕ :=
  2 * (2 * Nat.pair y (2 * (2 * Nat.pair (encodeCode (Code.const n)) (encodeCode Code.id)) + 4)
    + 1) + 4

/-- `Statement:` `encodeCode (curry d n) = cfCurryIndex (encodeCode d) n`, by `rfl`. -/
theorem cf_encodeCode_curry (d : Code) (n : ℕ) :
    encodeCode (curry d n) = cfCurryIndex (encodeCode d) n :=
  rfl

/-- `Statement:` the code `y ↦ cfCurryIndex y y`. -/
def cfDiagIndex : Code :=
  comp cfAdd4 (comp cfDouble (comp succ (comp cfDouble (pair Code.id
    (comp cfAdd4 (comp cfDouble (comp cfDouble (pair cfEncConst (Code.const (encodeCode Code.id))))))))))

/-- `Statement:` `cfDiagIndex` computes `y ↦ cfCurryIndex y y`. -/
theorem cf_eval_diagIndex (y : ℕ) : eval cfDiagIndex y = Part.some (cfCurryIndex y y) := by
  have hq := cf_eval_pair (cf_eval_encConst y) (eval_const (encodeCode Code.id) y)
  have hE := cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some hq (cf_eval_double _))
    (cf_eval_double _)) (cf_eval_add4 _)
  exact cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some (cf_eval_comp_some
    (cf_eval_pair (cf_eval_id y) hE) (cf_eval_double _)) rfl) (cf_eval_double _)) (cf_eval_add4 _)

/-! ## § IV. The recursion theorem in code form -/

/-- `Statement:` on `Nat.pair y x`, run `cψ` on `Nat.pair (cfCurryIndex y y) x`. -/
def cfDiag (cψ : Code) : Code := comp cψ (pair (comp cfDiagIndex left) right)

/-- `Statement:` `cfDiag cψ` on `Nat.pair y x` is `cψ` on `Nat.pair (cfCurryIndex y y) x`. -/
theorem cf_eval_diag (cψ : Code) (y x : ℕ) :
    eval (cfDiag cψ) (Nat.pair y x) = eval cψ (Nat.pair (cfCurryIndex y y) x) :=
  cf_eval_comp (cf_eval_pair (cf_eval_comp_some (cf_eval_left y x) (cf_eval_diagIndex y))
    (cf_eval_right y x))

/-- `Statement:` the fixed-point address of `cψ`, `curry (cfDiag cψ) (encodeCode (cfDiag cψ))`. -/
def fpCF (cψ : Code) : Code := curry (cfDiag cψ) (encodeCode (cfDiag cψ))

/-- `Statement:` Kleene's second recursion theorem for a transformation given as a code `cψ`:
`fpCF cψ` computes `x ↦ eval cψ (Nat.pair (encodeCode (fpCF cψ)) x)`. -/
theorem kleene_cf (cψ : Code) (x : ℕ) :
    eval (fpCF cψ) x = eval cψ (Nat.pair (encodeCode (fpCF cψ)) x) := by
  unfold fpCF
  rw [cf_eval_curry, cf_eval_diag, cf_encodeCode_curry]

/-- `Statement:` the same, in the shape of Mathlib's `fixed_point₂`, up to `eval`. -/
theorem kleene_cf_fixed₂ (cψ : Code) :
    ∃ c : Code, eval c = (fun d x => eval cψ (Nat.pair (encodeCode d) x)) c :=
  ⟨fpCF cψ, funext (kleene_cf cψ)⟩

/-- `Statement:` a code returning its own `encodeCode` plus one on every input. -/
theorem quine_succ_cf : ∃ c : Code, ∀ x, eval c x = Part.some (encodeCode c + 1) :=
  ⟨fpCF (comp succ left), fun x =>
    (kleene_cf _ x).trans (cf_eval_comp_some (cf_eval_left _ _) (cf_eval_succ _))⟩

/-- `Statement:` `k ≤ encodeCode (Code.const k)`. -/
theorem cf_le_encodeCode_const (k : ℕ) : k ≤ encodeCode (Code.const k) := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [cf_encodeCode_const_succ]
    have := Nat.right_le_pair 1 (encodeCode (Code.const k))
    omega

/-- `Statement:` CONTROL: no constant code returns its own `encodeCode` plus one on every input. -/
theorem const_not_quine_succ (k : ℕ) :
    ¬ ∀ x, eval (Code.const k) x = Part.some (encodeCode (Code.const k) + 1) := by
  intro h
  have h1 := Part.some_inj.1 ((eval_const k 0).symm.trans (h 0))
  have h2 := cf_le_encodeCode_const k
  omega

-- Statement: CONTROL: without the `+ 1`, a constant meets the condition: `Code.zero` returns its own
-- `encodeCode`, which is `0`.
example : ∀ x, eval Code.zero x = Part.some (encodeCode Code.zero) := fun _ => rfl

/-! ## § V. The statements, measured as `Prop`s -/

/-- `Statement:` Mathlib's `fixed_point₂`, as a `Prop`. -/
def stmtFixedPoint₂ : Prop := ∀ {f : Code → ℕ →. ℕ}, Partrec₂ f → ∃ c : Code, eval c = f c

/-- `Statement:` Mathlib's `fixed_point`, as a `Prop`. -/
def stmtFixedPoint : Prop := ∀ {f : Code → Code}, Computable f → ∃ c : Code, eval (f c) = eval c

/-- `Statement:` `kleene_cf_fixed₂`'s statement, as a `Prop`. -/
def stmtKleeneCF : Prop :=
  ∀ cψ : Code, ∃ c : Code, eval c = (fun d x => eval cψ (Nat.pair (encodeCode d) x)) c

-- Statement: `kleene_cf_fixed₂` proves `stmtKleeneCF`.
example : stmtKleeneCF := kleene_cf_fixed₂

/-- `Statement:` a statement whose only content is a `Partrec₂` hypothesis at `ℕ → ℕ →. ℕ`, as a `Prop`. -/
def stmtPartrec₂Hyp : Prop := ∀ f : ℕ → ℕ →. ℕ, Partrec₂ f → True

/-- `Statement:` CONTROL: the same with a unary `Partrec` hypothesis at `ℕ →. ℕ`, as a `Prop`. -/
def stmtPartrecHyp : Prop := ∀ f : ℕ →. ℕ, Partrec f → True

/-- `Statement:` CONTROL: a unary `Partrec` hypothesis at the pair carrier `ℕ × ℕ →. ℕ`, as a `Prop`. -/
def stmtPartrecProdHyp : Prop := ∀ f : ℕ × ℕ →. ℕ, Partrec f → True

-- Statement: `stmtPartrec₂Hyp` carries `Classical.choice`, with no `Code` in it, and `stmtPartrecHyp`
-- measures `[propext, Quot.sound]` (`PurityCheck`): the choice enters with the pair, through
-- `Primcodable.prod`, before any recursion theorem is stated.
-- Statement: `stmtPartrecProdHyp` carries `Classical.choice` too (`PurityCheck`), so the choice comes
-- with the pair instance `Primcodable.prod`, not with having two arguments.

-- Statement: each `cf_` lemma of § I and § II named after a Mathlib constant has exactly its type.
example : type_of% @Nat.unpair_pair := @cf_unpair_pair
example : type_of% @Nat.pair_unpair := @cf_pair_unpair
example : type_of% @Nat.sqrt_le := fun n => (cf_sqrt_isSqrt n).1
example : type_of% @Nat.lt_succ_sqrt := fun n => (cf_sqrt_isSqrt n).2
example : type_of% @Nat.sqrt.iter_sq_le := @cf_sqrt_iter_sq_le
example : type_of% @Nat.sqrt.lt_iter_succ_sq := @cf_sqrt_lt_iter_succ_sq
example : type_of% @Nat.sqrt_le_self := @cf_sqrt_le_self
example : type_of% @Nat.unpair_left_le := @cf_unpair_left_le
example : type_of% @Nat.unpair_right_le := @cf_unpair_right_le
example : type_of% @Nat.div2_val := @cf_div2_val
example : type_of% @Nat.Partrec.Code.eval_id := @cf_eval_id
example : type_of% @Nat.Partrec.Code.eval_curry := @cf_eval_curry
example : type_of% @Nat.Partrec.Code.eval_prec_zero := @cf_eval_prec_zero
example : type_of% @Nat.Partrec.Code.eval_prec_succ := @cf_eval_prec_succ

-- Statement: the Mathlib constants named above, and `stmtFixedPoint₂` / `stmtFixedPoint`, carry
-- `Classical.choice`; the `cf_` lemmas, `fpCF`, `kleene_cf`, `kleene_cf_fixed₂` and `stmtKleeneCF` do
-- not (the `#print axioms` lines in `PurityCheck`).
-- Reading: in the bins of `ZeroParadox/Category/ChoiceCannotBe.md`, those Mathlib lemmas are
-- ACCIDENTAL (a choice-free proof of the same type is exhibited above) and `fixed_point₂` /
-- `fixed_point` are STATEMENT-CARRIED; the self-referential address is constructed, not selected.
-- Reading (cited, not claimed): the construction is Kleene's, "On notation for ordinal numbers", J.
-- Symbolic Logic 3(4) (1938), p. 153: "Let e define ψ(S¹ₙ(y, y), 𝔵) recursively, and set
-- f = S¹ₙ(e, e)"; `cfDiag cψ` plays e and `fpCF cψ` plays S¹ₙ(e, e). Constructive machine-checked
-- versions exist: Forster and Smolka, "Call-by-value lambda calculus as a model of computation in
-- Coq", J. Automated Reasoning, doi 10.1007/s10817-018-9484-2, Fact 18 (§ 7), for the λ-calculus L; Forster, "Computability in
-- Constructive Type Theory", PhD thesis, Saarland University (2021), Theorem 6.16, p. 61, Rogers' form
-- under the axiom EPF. In Lean 4, the closest located: L. J. Close, `witness-asymmetry` v1.0.1,
-- Zenodo software (2026), version doi 10.5281/zenodo.18915696 for v1.0.1 (concept doi
-- 10.5281/zenodo.18915083, all versions), `FixedPoint/ChurchTuring/ConstructiveRecursionTheorem.lean`: `recursion_theorem` by the same
-- construction, `fixedPointIndex e_f := smn (diag_closure e_f) (diag_closure e_f)`, with no imports and
-- no axioms (`#print axioms` re-run on the filed source, 2026-10-22), over a class `NamingSystem` whose
-- fields assume s-m-n (`smn_spec`) and the diagonal program (`diag_closure_spec`). So a choice-free
-- construction is expected. This file proves the counterpart of `smn_spec` (`cf_eval_curry`) and the
-- diagonal step of Kleene's ψ-form (`cf_eval_diag`, which hands the index `cfCurryIndex y y` to `cψ` as
-- data); the counterpart of `diag_closure_spec`, which evaluates the code `e_f` returns, needs a
-- universal code and is not built here. It builds no `NamingSystem` instance, and adds the measurement
-- on `Code`, where the choice sits in the statements' packaging (`Partrec₂`, `Denumerable Code`) and in
-- the proofs of the arithmetic lemmas above, not in the construction.
-- Reading: whether selecting a code by its behaviour needs choice was not attempted as of 2026-10-22.
-- Bauer's behaviour-level recursion theorems use choice at that step and do not show it necessary:
-- "First steps in synthetic computability theory", Electronic Notes in Theoretical Computer Science
-- (MFPS XXI), Theorem 4.24, p. 34 of the preliminary version, by Number Choice; "On fixed-point theorems in synthetic
-- computability", Tbilisi Math. J. 10(3) (2017), Theorem 5.2, p. 177, by Countable Choice.

/-! ## § VI. Decoding: the inverse of `encodeCode`

Reading (cited, not claimed): the encoding is Carneiro's, "Formalizing computability theory via
partial recursive functions", ITP 2019, LIPIcs 141, paper 12 (arXiv 1810.08380v2, § 5.1, p. 11),
chosen there because "it is a bijection to N". The decoder below is Mathlib's
`Nat.Partrec.Code.ofNatCode` with its termination proof redone by `cf_` lemmas, and the proofs of the
two inverse laws follow Mathlib's private `encode_ofNatCode` and the `left_inv` of `instDenumerable`. -/

/-- `Statement:` `Nat.div2 (Nat.div2 n) < n + 4`, choice-free proof. -/
theorem cf_div2_div2_lt (n : ℕ) : n.div2.div2 < n + 4 := by
  rw [cf_div2_val, cf_div2_val]
  exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
    (Nat.succ_le_succ (Nat.le_add_right _ _))

/-- `Statement:` a decoder `ℕ → Code` by the case split of Mathlib's `Nat.Partrec.Code.ofNatCode`,
terminating by `cf_div2_div2_lt`, `cf_unpair_left_le` and `cf_unpair_right_le`. -/
def ofNatCodeCF : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | n + 4 =>
    match n.bodd, n.div2.bodd with
    | false, false =>
      pair (ofNatCodeCF (Nat.unpair n.div2.div2).1) (ofNatCodeCF (Nat.unpair n.div2.div2).2)
    | false, true =>
      comp (ofNatCodeCF (Nat.unpair n.div2.div2).1) (ofNatCodeCF (Nat.unpair n.div2.div2).2)
    | true, false =>
      prec (ofNatCodeCF (Nat.unpair n.div2.div2).1) (ofNatCodeCF (Nat.unpair n.div2.div2).2)
    | true, true => rfind' (ofNatCodeCF n.div2.div2)
termination_by n => n
decreasing_by
  all_goals first
    | exact Nat.lt_of_le_of_lt (cf_unpair_left_le _) (cf_div2_div2_lt _)
    | exact Nat.lt_of_le_of_lt (cf_unpair_right_le _) (cf_div2_div2_lt _)
    | exact cf_div2_div2_lt _

/-- `Statement:` `encodeCode (ofNatCodeCF n) = n`. -/
theorem cf_encodeCode_ofNatCodeCF : ∀ n, encodeCode (ofNatCodeCF n) = n
  | 0 => by rw [ofNatCodeCF]; rfl
  | 1 => by rw [ofNatCodeCF]; rfl
  | 2 => by rw [ofNatCodeCF]; rfl
  | 3 => by rw [ofNatCodeCF]; rfl
  | n + 4 => by
    have IH := cf_encodeCode_ofNatCodeCF n.div2.div2
    have IH1 := cf_encodeCode_ofNatCodeCF (Nat.unpair n.div2.div2).1
    have IH2 := cf_encodeCode_ofNatCodeCF (Nat.unpair n.div2.div2).2
    have hpu := cf_pair_unpair n.div2.div2
    have h1 := cf_bodd_add_div2 n
    have h2 := cf_bodd_add_div2 n.div2
    have hf : (false : Bool).toNat = 0 := rfl
    have ht : (true : Bool).toNat = 1 := rfl
    rw [ofNatCodeCF]
    cases ha : n.bodd <;> cases hb : n.div2.bodd <;> rw [ha] at h1 <;> rw [hb] at h2
    · show 2 * (2 * Nat.pair (encodeCode (ofNatCodeCF _)) (encodeCode (ofNatCodeCF _))) + 4 = n + 4
      rw [IH1, IH2, hpu]
      rw [hf] at h1 h2; omega
    · show 2 * (2 * Nat.pair (encodeCode (ofNatCodeCF _)) (encodeCode (ofNatCodeCF _)) + 1) + 4 =
        n + 4
      rw [IH1, IH2, hpu]
      rw [hf] at h1; rw [ht] at h2; omega
    · show (2 * (2 * Nat.pair (encodeCode (ofNatCodeCF _)) (encodeCode (ofNatCodeCF _))) + 1) + 4 =
        n + 4
      rw [IH1, IH2, hpu]
      rw [ht] at h1; rw [hf] at h2; omega
    · show (2 * (2 * encodeCode (ofNatCodeCF _) + 1) + 1) + 4 = n + 4
      rw [IH]
      rw [ht] at h1 h2; omega
termination_by n => n
decreasing_by
  all_goals first
    | exact Nat.lt_of_le_of_lt (cf_unpair_left_le _) (cf_div2_div2_lt _)
    | exact Nat.lt_of_le_of_lt (cf_unpair_right_le _) (cf_div2_div2_lt _)
    | exact cf_div2_div2_lt _

/-- `Statement:` `n = x.toNat + 2 * (y.toNat + 2 * m)` gives `n.bodd = x`, `n.div2.bodd = y` and
`n.div2.div2 = m`. -/
theorem cf_bodd_div2_eq {n m : ℕ} {x y : Bool} (h : n = x.toNat + 2 * (y.toNat + 2 * m)) :
    n.bodd = x ∧ n.div2.bodd = y ∧ n.div2.div2 = m := by
  have h1 := cf_bodd_add_div2 n
  have h2 := cf_bodd_add_div2 n.div2
  have h3 := cf_div2_val n
  have h4 := cf_div2_val n.div2
  have hx : x.toNat < 2 := by cases x <;> decide
  have hy : y.toNat < 2 := by cases y <;> decide
  have hbx : (n.bodd).toNat < 2 := by cases n.bodd <;> decide
  have hby : (n.div2.bodd).toNat < 2 := by cases n.div2.bodd <;> decide
  have ex : n.bodd.toNat = x.toNat := by omega
  have ey : n.div2.bodd.toNat = y.toNat := by omega
  refine ⟨?_, ?_, by omega⟩
  · cases hb : n.bodd <;> cases x <;> rw [hb] at ex <;> first | rfl | exact absurd ex (by decide)
  · cases hb : n.div2.bodd <;> cases y <;> rw [hb] at ey <;> first | rfl | exact absurd ey (by decide)

/-- `Statement:` for `n = x.toNat + 2 * (y.toNat + 2 * m)`, `ofNatCodeCF (n + 4)` is the four-way
match on `x, y`: `pair`, `comp` or `prec` of `ofNatCodeCF` at the two halves of `Nat.unpair m`, or
`rfind' (ofNatCodeCF m)`. -/
theorem cf_ofNatCodeCF_step {n m : ℕ} (x y : Bool) (h : n = x.toNat + 2 * (y.toNat + 2 * m)) :
    ofNatCodeCF (n + 4) =
      match x, y with
      | false, false => pair (ofNatCodeCF (Nat.unpair m).1) (ofNatCodeCF (Nat.unpair m).2)
      | false, true => comp (ofNatCodeCF (Nat.unpair m).1) (ofNatCodeCF (Nat.unpair m).2)
      | true, false => prec (ofNatCodeCF (Nat.unpair m).1) (ofNatCodeCF (Nat.unpair m).2)
      | true, true => rfind' (ofNatCodeCF m) := by
  obtain ⟨hx, hy, hm⟩ := cf_bodd_div2_eq h
  rw [ofNatCodeCF, hx, hy, hm]
  cases x <;> cases y <;> rfl

/-- `Statement:` `ofNatCodeCF (encodeCode c) = c`. -/
theorem cf_ofNatCodeCF_encodeCode : ∀ c, ofNatCodeCF (encodeCode c) = c
  | .zero => by rw [encodeCode, ofNatCodeCF]
  | .succ => by rw [encodeCode, ofNatCodeCF]
  | .left => by rw [encodeCode, ofNatCodeCF]
  | .right => by rw [encodeCode, ofNatCodeCF]
  | .pair a b => by
    rw [encodeCode, cf_ofNatCodeCF_step (m := Nat.pair (encodeCode a) (encodeCode b)) false false
      (by show _ = 0 + 2 * (0 + 2 * _); omega)]
    dsimp only
    rw [cf_unpair_pair, cf_ofNatCodeCF_encodeCode a, cf_ofNatCodeCF_encodeCode b]
  | .comp a b => by
    rw [encodeCode, cf_ofNatCodeCF_step (m := Nat.pair (encodeCode a) (encodeCode b)) false true
      (by show _ = 0 + 2 * (1 + 2 * _); omega)]
    dsimp only
    rw [cf_unpair_pair, cf_ofNatCodeCF_encodeCode a, cf_ofNatCodeCF_encodeCode b]
  | .prec a b => by
    rw [encodeCode, cf_ofNatCodeCF_step (m := Nat.pair (encodeCode a) (encodeCode b)) true false
      (by show _ = 1 + 2 * (0 + 2 * _); omega)]
    dsimp only
    rw [cf_unpair_pair, cf_ofNatCodeCF_encodeCode a, cf_ofNatCodeCF_encodeCode b]
  | .rfind' a => by
    rw [encodeCode, cf_ofNatCodeCF_step (m := encodeCode a) true true
      (by show _ = 1 + 2 * (1 + 2 * _); omega)]
    dsimp only
    rw [cf_ofNatCodeCF_encodeCode a]

/-- `Statement:` `ofNatCodeCF` is Mathlib's `Nat.Partrec.Code.ofNatCode`. -/
theorem ofNatCodeCF_eq_ofNatCode : ofNatCodeCF = ofNatCode := funext fun n => by
  conv_rhs => rw [← cf_encodeCode_ofNatCodeCF n]
  rw [← ofNatCode_eq, ← encodeCode_eq, Denumerable.ofNat_encode]

-- Statement: `ofNatCodeCF` and its two inverse laws do not carry `Classical.choice`; `ofNatCode` and
-- `ofNatCodeCF_eq_ofNatCode` do (the `#print axioms` lines in `PurityCheck`).
-- Reading: in the bins of `ZeroParadox/Category/ChoiceCannotBe.md`, `ofNatCodeCF_eq_ofNatCode` is
-- STATEMENT-CARRIED, measured 2026-10-25 (the bare statement `ofNatCodeCF = ofNatCode` reports
-- `Classical.choice`); the choice enters through the constant `ofNatCode`, whose own footprint is
-- not classed here.

end ZeroParadox

section PurityCheck
open ZeroParadox

#print axioms cf_amgm
#print axioms cf_sq_succ
#print axioms cf_sqrt_iter_sq_le
#print axioms cf_sqrt_lt_iter_succ_sq
#print axioms cf_sqrt_isSqrt
#print axioms cf_sqrt_eq_of
#print axioms cf_sqrt_le_self
#print axioms cf_pair_unpair
#print axioms cf_unpair_pair
#print axioms cf_unpair_left_le
#print axioms cf_unpair_right_le
#print axioms cf_bodd_add_div2
#print axioms cf_div2_val
#print axioms cf_eval_succ
#print axioms cf_eval_left
#print axioms cf_eval_right
#print axioms cf_eval_pair
#print axioms cf_eval_comp
#print axioms cf_eval_comp_some
#print axioms cf_eval_id
#print axioms cf_eval_curry
#print axioms cf_eval_prec_zero
#print axioms cf_eval_prec_succ
#print axioms cf_eval_prec_total
#print axioms cfUnary
#print axioms cf_eval_unary
#print axioms cfAdd4
#print axioms cf_eval_add4
#print axioms cfAdd2Step
#print axioms cfDouble
#print axioms cf_eval_double
#print axioms cfEncConstStep
#print axioms cfEncConst
#print axioms cf_encodeCode_const_succ
#print axioms cf_eval_encConst
#print axioms cfCurryIndex
#print axioms cf_encodeCode_curry
#print axioms cfDiagIndex
#print axioms cf_eval_diagIndex
#print axioms cfDiag
#print axioms cf_eval_diag
#print axioms fpCF
#print axioms kleene_cf
#print axioms kleene_cf_fixed₂
#print axioms quine_succ_cf
#print axioms cf_le_encodeCode_const
#print axioms const_not_quine_succ
#print axioms stmtFixedPoint₂
#print axioms stmtFixedPoint
#print axioms stmtKleeneCF
#print axioms stmtPartrec₂Hyp
#print axioms stmtPartrecHyp
#print axioms stmtPartrecProdHyp
#print axioms Partrec₂
#print axioms Primcodable.prod
#print axioms Encodable.Prod.encodable
#print axioms cf_div2_div2_lt
#print axioms ofNatCodeCF
#print axioms cf_encodeCode_ofNatCodeCF
#print axioms cf_bodd_div2_eq
#print axioms cf_ofNatCodeCF_step
#print axioms cf_ofNatCodeCF_encodeCode
#print axioms ofNatCodeCF_eq_ofNatCode
-- The Mathlib constants the `cf_` lemmas share a type with, the two recursion theorems, and
-- `ofNatCode`.
#print axioms Nat.unpair_pair
#print axioms Nat.pair_unpair
#print axioms Nat.sqrt_le
#print axioms Nat.lt_succ_sqrt
#print axioms Nat.sqrt.iter_sq_le
#print axioms Nat.sqrt.lt_iter_succ_sq
#print axioms Nat.sqrt_le_self
#print axioms Nat.unpair_left_le
#print axioms Nat.unpair_right_le
#print axioms Nat.div2_val
#print axioms Nat.Partrec.Code.eval_id
#print axioms Nat.Partrec.Code.eval_curry
#print axioms Nat.Partrec.Code.eval_prec_zero
#print axioms Nat.Partrec.Code.eval_prec_succ
#print axioms Nat.Partrec.Code.fixed_point₂
#print axioms Nat.Partrec.Code.fixed_point
#print axioms Nat.Partrec.Code.ofNatCode

end PurityCheck
