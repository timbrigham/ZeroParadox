import ZeroParadox.Valuation.PoleCompletion
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Self-copying self-reference: infinite ⟺ a one-to-one, not-onto self-map with exactly one fixed point

## Engineer's Take

The question here is whether infinite complexity at the bottom denotes a mandatory ability for self reference, whether by definition it needs at some point to include it. The self reference is an action, and if you make an exact copy it is by definition a duplicate. Guaranteeing one thing and forbidding another is the exact direction I would have expected here. Where choice enters needed to be measured first.

---
## Formal Overview (AI-assisted)
`SelfCopyRef f`: `f` is one-to-one, not onto, with exactly one fixed point. Central result:
`infinite_iff_exists_selfCopyRef`. Prior art: Dedekind (1888), *Was sind und was sollen die Zahlen?*,
Erklärung 64; Sätze 159, 160 — infinite ⟺ a proper self-embedding; the unique-fixed-point refinement is
this file's packaging. Fences: § IV. Choice footprints, and the set-theory status of ⟹: `PurityCheck`.
-/

namespace ZeroParadox

/-! ## § I. The predicate and the iff -/

/-- `Statement:` `f` is one-to-one, not onto, and has exactly one fixed point. -/
def SelfCopyRef {α : Type*} (f : α → α) : Prop :=
  Function.Injective f ∧ ¬ Function.Surjective f ∧ ∃! b, f b = b

/-- `Statement:` a finite carrier has no `SelfCopyRef` map (a one-to-one self-map of a finite type
is onto, Mathlib `Finite.injective_iff_surjective`). -/
theorem no_selfCopyRef_of_finite {α : Type} [Finite α] (f : α → α) : ¬ SelfCopyRef f :=
  fun ⟨hi, hns, _⟩ => hns (Finite.injective_iff_surjective.mp hi)

/-- `Statement:` every infinite carrier has a `SelfCopyRef` map: fix `none` and shift each ℕ-column
of `Option (α × ℕ)` up by one, transported along an equivalence `α ≃ Option (α × ℕ)` obtained from
cardinal arithmetic. -/
theorem exists_selfCopyRef_of_infinite {α : Type} [Infinite α] : ∃ f : α → α, SelfCopyRef f := by
  have hc : Cardinal.mk (Option (α × ℕ)) = Cardinal.mk α := by
    rw [Cardinal.mk_option, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_nat,
      Cardinal.mul_aleph0_eq (Cardinal.aleph0_le_mk α),
      Cardinal.add_one_eq (Cardinal.aleph0_le_mk α)]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  let g : Option (α × ℕ) → Option (α × ℕ) := fun o => o.map (fun p => (p.1, p.2 + 1))
  have gi : Function.Injective g := Option.map_injective fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (by omega)
  have gns : ¬ Function.Surjective g := by
    intro hs
    obtain ⟨o, ho⟩ := hs (some (Classical.arbitrary α, 0))
    cases o <;> simp [g] at ho
  have gfix : ∀ o, g o = o → o = none := by
    intro o h
    cases o with
    | none => rfl
    | some p =>
      simp only [g, Option.map_some, Option.some.injEq] at h
      have := congrArg Prod.snd h; simp at this
  refine ⟨fun x => e (g (e.symm x)), ?_, ?_, ⟨e none, by simp [g], ?_⟩⟩
  · intro a b h
    exact e.symm.injective (gi (e.injective h))
  · intro hs
    apply gns
    intro y
    obtain ⟨x, hx⟩ := hs (e y)
    exact ⟨e.symm x, e.injective (by simpa using hx)⟩
  · intro y hy
    have : g (e.symm y) = e.symm y := e.injective (by simpa using hy)
    rw [← gfix _ this]; simp

/-- `Statement:` a type is infinite iff it carries a `SelfCopyRef` map. -/
theorem infinite_iff_exists_selfCopyRef {α : Type} : Infinite α ↔ ∃ f : α → α, SelfCopyRef f := by
  constructor
  · intro _; exact exists_selfCopyRef_of_infinite
  · rintro ⟨f, hf⟩
    by_contra h
    haveI : Finite α := not_infinite_iff_finite.mp h
    exact no_selfCopyRef_of_finite f hf

/-! ## § II. Where the counting is data: ℕ, a given `α ≃ ℕ`, and the tree boundary -/

/-- On ℕ: fix `0`, send every other `n` to `n + 1`. `1` is never hit. -/
def natSCR (n : ℕ) : ℕ := if n = 0 then 0 else n + 1

/-- `Statement:` `natSCR` is a `SelfCopyRef` map on ℕ. -/
theorem natSCR_selfCopyRef : SelfCopyRef natSCR := by
  refine ⟨?_, ?_, ⟨0, rfl, ?_⟩⟩
  · intro a b h
    unfold natSCR at h
    split_ifs at h <;> omega
  · intro hs
    obtain ⟨n, hn⟩ := hs 1
    unfold natSCR at hn
    split_ifs at hn
    omega
  · intro y hy
    unfold natSCR at hy
    split_ifs at hy with h
    · exact h
    · omega

/-- `Statement:` along a GIVEN equivalence `e : α ≃ ℕ`, the conjugate of `natSCR` is a `SelfCopyRef`
map on `α`. -/
theorem selfCopyRef_of_equiv_nat {α : Type} (e : α ≃ ℕ) :
    SelfCopyRef (fun x => e.symm (natSCR (e x))) := by
  obtain ⟨hi, hns, b, hb, hu⟩ := natSCR_selfCopyRef
  refine ⟨fun a c h => e.injective (hi (e.symm.injective h)), fun hs => hns fun y => ?_,
    ⟨e.symm b, by simp [hb], fun y hy => ?_⟩⟩
  · obtain ⟨x, hx⟩ := hs (e.symm y)
    exact ⟨e x, by simpa using congrArg e hx⟩
  · have : natSCR (e y) = e y := by simpa using congrArg e hy
    rw [← hu _ this]; simp

/-- `Statement:` the boundary self-application `boundaryDouble` (×2 in digits on `End = ℕ → Fin 2`)
is a `SelfCopyRef` map; its unique fixed point is the all-zeros end `botEnd`. -/
theorem boundaryDouble_selfCopyRef : SelfCopyRef boundaryDouble := by
  refine ⟨?_, ?_, ⟨botEnd, boundaryDouble_botEnd, fun y hy => boundaryDouble_unique_fp y hy⟩⟩
  · intro a b h
    funext n
    exact congrFun h (n + 1)
  · intro hs
    obtain ⟨x, hx⟩ := hs (fun _ => 1)
    have := congrFun hx 0
    simp [boundaryDouble] at this

/-! ## § III. The finite half without choice, and orbit dynamics -/

-- The two instances are the explicit enumeration the choice-free proof consumes; the linters'
-- suggested `Finite` + `classical` route is the choice-carrying one this declaration avoids.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- `Statement:` over a `Fintype` with decidable equality, no `SelfCopyRef` map exists — proved by
list pigeonhole on the enumeration (`List.Nodup.subperm`, `List.length_filter_lt_length_iff_exists`)
rather than through `Finite.injective_iff_surjective`. -/
theorem no_selfCopyRef_of_fintype {α : Type*} [Fintype α] [DecidableEq α] (f : α → α) :
    ¬ SelfCopyRef f := by
  rintro ⟨hi, hns, _⟩
  apply hns
  intro y
  obtain ⟨⟨s, hnd⟩, hc⟩ := (inferInstance : Fintype α)
  induction s using Quot.ind with
  | mk l =>
    change l.Nodup at hnd
    change ∀ x, x ∈ l at hc
    rcases Decidable.em (∃ x ∈ l, f x = y) with h | h
    · obtain ⟨x, _, hx⟩ := h
      exact ⟨x, hx⟩
    · exfalso
      have hsub : l.map f ⊆ l.filter (fun x => decide (x ≠ y)) := by
        intro z hz
        obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hz
        exact List.mem_filter.mpr ⟨hc _, decide_eq_true (fun he => h ⟨x, hxl, he⟩)⟩
      have hle := ((hnd.map hi).subperm hsub).length_le
      rw [List.length_map] at hle
      have hlt : (l.filter (fun x => decide (x ≠ y))).length < l.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨y, hc y, by simp⟩
      omega

/-- `Statement:` on a finite type, if `b` is the only periodic point of `f`, every orbit lands on `b`
after finitely many steps. -/
theorem orbit_reaches_unique_periodic_of_finite {α : Type*} [Finite α] (f : α → α) (b : α)
    (hper : ∀ x : α, ∀ p : ℕ, 0 < p → f^[p] x = x → x = b) (x : α) :
    ∃ n : ℕ, f^[n] x = b := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] x)
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨i, hper _ (j - i) (Nat.sub_pos_of_lt h) ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq.symm
  · refine ⟨j, hper _ (i - j) (Nat.sub_pos_of_lt h) ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq

/-- `Statement:` on the 2-adic numbers ℚ₂, the only periodic point of doubling is `0`.
`Reading:` the hypothesis of `orbit_reaches_unique_periodic_of_finite` holds here, and yet a nonzero
orbit never lands on `0` — `padic_orbit_never_reaches_zero` (`ZeroParadox/Order/WellFoundedObstruct.lean`). -/
theorem doubling_only_periodic_point_zero (x : ℚ_[2]) (p : ℕ) (hp : 0 < p)
    (h : (fun q : ℚ_[2] => 2 * q)^[p] x = x) : x = 0 := by
  have hit : ∀ n : ℕ, (fun q : ℚ_[2] => 2 * q)^[n] x = 2 ^ n * x := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ]; ring
  rw [hit] at h
  have h1 : ((2 : ℚ_[2]) ^ p - 1) * x = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exfalso
    have : (2 : ℚ_[2]) ^ p = 1 := sub_eq_zero.mp h2
    have hn := congrArg norm this
    rw [norm_pow, norm_one] at hn
    have h2n : ‖(2 : ℚ_[2])‖ = 1 / 2 := by
      simpa using (Padic.norm_p (p := 2))
    rw [h2n] at hn
    have : (1 / 2 : ℝ) ^ p < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (Nat.pos_iff_ne_zero.mp hp)
    linarith
  · exact h2

/-! ## § IV. Fences

* Proved: the AVAILABILITY of a `SelfCopyRef` map, on infinite carriers only. That the semilattice ⊥ on an
  INFINITE carrier PERFORMS one is a commitment — see `l_inf` (`ZeroParadox/Information/Surprisal.lean`).
  `MachinePhase`, the two-phase rounding that carries `machinePhaseKleene`, admits none
  (`no_selfCopyRef_of_finite`; the `example` in `ZeroParadox/Computability/ComputationCannotBe.lean` § IX).
* `#print axioms` reports a proof's footprint, never a theorem's necessity. -/

end ZeroParadox

/-! ## Axiom Purity Check -/

section PurityCheck
open ZeroParadox

#print axioms SelfCopyRef
#print axioms natSCR
-- Measured: the three below carry `Classical.choice` (Mathlib routes). For the ⟹ half it enters
-- turning bare `Infinite α` into a counting — `Cardinal.aleph0_le_mk`, `Cardinal.mul_aleph0_eq`,
-- `Cardinal.add_one_eq`, `Cardinal.mk_option` (and `Infinite.natEmbedding`) each report it;
-- `Cardinal.eq` does not. A proof's footprint, not a theorem's necessity: UNCLASSIFIED. In set theory
-- without choice the ⟹ half is unprovable: infinite Dedekind-finite sets, with no one-to-one, not-onto
-- self-map, are consistent there (Banakh, arXiv:2006.01613v4, Rem. 43.14, citing Jech 1973 § 4.6).
-- Dependent choice gives every infinite set such a self-map (Prop. 43.12); the unique fixed point is not
-- in that result, and whether dependent choice gives it is not claimed.
#print axioms no_selfCopyRef_of_finite
#print axioms exists_selfCopyRef_of_infinite
#print axioms infinite_iff_exists_selfCopyRef
-- Measured `[propext, Quot.sound]`: the counting is data here (ℕ itself, a given `α ≃ ℕ`, digit
-- positions on `End`).
#print axioms natSCR_selfCopyRef
#print axioms selfCopyRef_of_equiv_nat
#print axioms boundaryDouble_selfCopyRef
-- The finite half re-proved without `Classical.choice` (list pigeonhole over a `Fintype` enumeration):
-- ACCIDENTAL for the `[Fintype] [DecidableEq]` statement, whose Mathlib route reports choice. The
-- `[Finite]` statement `no_selfCopyRef_of_finite` is not re-proved here and stays UNCLASSIFIED.
#print axioms no_selfCopyRef_of_fintype
#print axioms orbit_reaches_unique_periodic_of_finite
#print axioms doubling_only_periodic_point_zero

end PurityCheck
