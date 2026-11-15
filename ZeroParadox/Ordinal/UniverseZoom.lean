-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): one universe of ordinals seen from the next, `Ordinal.univ` as a fixed point of `α ↦ ω^α`, and one construction giving ε₀ at the floor `{0}` and `Ordinal.univ` at the floor of all lifted ordinals. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Order.UpAndOver
import Mathlib.SetTheory.Ordinal.Veblen
import Mathlib.SetTheory.Ordinal.Univ
import Mathlib.Tactic

/-!
# One universe of ordinals seen from the next

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)
Below `Ordinal.univ` a copy of the lower level, and `succ univ` outside it (§ I); lifting fixes ε₀,
and `univ`, above every lift, is fixed by `α ↦ ω^α` and least such (§ II); `roleAbove` gives ε₀
at `{0}` and `univ` at the range of `lift` (§ III).
-/

set_option maxHeartbeats 400000

namespace ZeroParadox

open Ordinal Order

universe u v

/-! ### § I. Below `univ` a copy; one step over it leaves every copy -/

/-- `Statement:` every lift of an ordinal one universe up is strictly below `univ.{u, u+1}`; Mathlib's
`Ordinal.liftPrincipalSeg`, whose top is `Ordinal.univ` (`liftPrincipalSeg_top`). -/
theorem lt_univ_of_lift (o : Ordinal.{u}) : lift.{u + 1} o < univ.{u, u + 1} :=
  liftPrincipalSeg.{u, u + 1}.lt_top o

/-- `Statement:` every ordinal strictly below `univ.{u, u+1}` is the lift of some ordinal of
`Ordinal.{u}`. -/
theorem lift_of_lt_univ {b : Ordinal.{u + 1}} (hb : b < univ.{u, u + 1}) :
    ∃ c : Ordinal.{u}, lift.{u + 1} c = b :=
  liftPrincipalSeg.{u, u + 1}.mem_range_of_rel_top hb

/-- `Statement:` every ordinal strictly below `univ.{u, u+1}` is the lift of exactly one ordinal of
`Ordinal.{u}`, and the lift keeps and reflects `<`. -/
theorem below_univ_is_a_copy :
    (∀ b : Ordinal.{u + 1}, b < univ.{u, u + 1} → ∃! c : Ordinal.{u}, lift.{u + 1} c = b) ∧
    (∀ a c : Ordinal.{u}, lift.{u + 1} a < lift.{u + 1} c ↔ a < c) := by
  refine ⟨fun b hb => ?_, fun a c => lift_lt⟩
  obtain ⟨c, hc⟩ := lift_of_lt_univ hb
  exact ⟨c, hc, fun d hd => lift_inj.1 (hd.trans hc.symm)⟩

/-- `Statement:` `univ ⋖ succ univ`, and neither `univ` nor `succ univ` is the lift of an ordinal of
`Ordinal.{u}`. -/
theorem over_univ_reveals_frame :
    univ.{u, u + 1} ⋖ succ univ.{u, u + 1} ∧
    (∀ c : Ordinal.{u}, lift.{u + 1} c ≠ univ.{u, u + 1}) ∧
    (∀ c : Ordinal.{u}, lift.{u + 1} c ≠ succ univ.{u, u + 1}) := by
  refine ⟨covBy_succ _, fun c h => (lt_univ_of_lift c).ne h, fun c h => ?_⟩
  have := lt_univ_of_lift c
  rw [h] at this
  exact lt_asymm this (Order.lt_succ _)

-- Statement: CONTROL, the same step taken below `univ` stays inside the copy: `succ` of a lift is a lift.
example (c : Ordinal.{u}) : ∃ d : Ordinal.{u}, lift.{u + 1} d = succ (lift.{u + 1} c) :=
  ⟨c + 1, by rw [Order.succ_eq_add_one, Ordinal.lift_add_one]⟩

/-! ### § II. Lifting commutes with `α ↦ ω^α`; `univ`, least above the copy, is a fixed point -/

/-- `Statement:` `lift (ω ^ b) = ω ^ lift b`. An `Ordinal` form was not located in Mathlib as of
2026-11-15, searched: every file under `Mathlib/SetTheory` for `lift.*opow`, `opow.*lift` and
`lift.*\^`; the hits are `Cardinal` lemmas (`Cardinal.lift_power`). -/
theorem lift_omega_opow (b : Ordinal.{u}) : lift.{v} (ω ^ b) = ω ^ (lift.{v} b) := by
  induction b using Ordinal.limitRecOn with
  | zero => simp
  | add_one b ih => rw [opow_add, opow_one, lift_mul, ih, lift_omega0, lift_add_one, opow_add, opow_one]
  | limit b h IH =>
    apply le_antisymm
    · apply le_of_forall_lt
      intro x hx
      obtain ⟨y, hy, rfl⟩ := lt_lift_iff.1 hx
      obtain ⟨c, hc, hyc⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero h).1 hy
      refine (lift_lt.2 hyc).trans_le ?_
      rw [IH c hc]
      exact opow_le_opow_right omega0_pos (lift_le.2 hc.le)
    · refine (opow_le_of_isSuccLimit omega0_ne_zero (isSuccLimit_lift.2 h)).2 ?_
      intro b' hb'
      obtain ⟨c, hc, rfl⟩ := lt_lift_iff.1 hb'
      rw [← IH c hc]
      exact lift_le.2 (opow_le_opow_right omega0_pos hc.le)

/-- `Statement:` lifting commutes with the `n`-th iterate of `α ↦ ω^α` from 0. -/
theorem lift_iterate_opow (n : ℕ) :
    lift.{v} ((fun a : Ordinal.{u} => ω ^ a)^[n] 0) = (fun a : Ordinal.{max u v} => ω ^ a)^[n] 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', lift_omega_opow, ih]

/-- `Statement:` `lift ε₀ = ε₀`: lifting sends ε₀ of `Ordinal.{u}` to ε₀ of `Ordinal.{max u v}`. -/
theorem lift_epsilon_zero : lift.{v} (Ordinal.epsilon.{u} 0) = Ordinal.epsilon.{max u v} 0 := by
  rw [epsilon_zero_eq_nfp, epsilon_zero_eq_nfp]
  apply le_antisymm
  · apply le_of_forall_lt
    intro x hx
    obtain ⟨y, hy, rfl⟩ := lt_lift_iff.1 hx
    obtain ⟨n, hn⟩ := lt_nfp_iff.1 hy
    exact lt_nfp_iff.2 ⟨n, by rw [← lift_iterate_opow.{u, v}]; exact lift_lt.2 hn⟩
  · refine nfp_le_fp (fun a b hab => opow_le_opow_right omega0_pos hab) zero_le ?_
    rw [← lift_omega_opow.{u, v}]
    exact lift_le.2 (le_of_eq (nfp_fp (isNormal_opow one_lt_omega0) 0))

/-- `Statement:` `univ.{u, u+1}` is a successor limit. -/
theorem univ_isSuccLimit : IsSuccLimit univ.{u, u + 1} := by
  refine ⟨not_isMin_iff.2 ⟨_, lt_univ_of_lift 0⟩, isSuccPrelimit_of_succ_lt fun b hb => ?_⟩
  obtain ⟨c, rfl⟩ := lift_of_lt_univ hb
  rw [Order.succ_eq_add_one, ← Ordinal.lift_add_one]
  exact lt_univ_of_lift _

/-- `Statement:` `ω ^ univ = univ`. The standard fact that the initial ordinal of an uncountable
cardinal is an ε-number, at `univ = Cardinal.univ.ord` (Mathlib's `Cardinal.ord_univ`); the nearest
Mathlib neighbour is `Ordinal.isPrincipal_opow_ord` (the initial ordinal of an infinite cardinal is
closed under `^`). An `ω ^ univ = univ` form was not located by `exact?` at the pinned Mathlib as of
2026-11-15. -/
theorem omega_opow_univ : ω ^ univ.{u, u + 1} = univ.{u, u + 1} := by
  apply le_antisymm
  · refine (opow_le_of_isSuccLimit omega0_ne_zero univ_isSuccLimit).2 ?_
    intro b' hb'
    obtain ⟨c, rfl⟩ := lift_of_lt_univ hb'
    rw [← lift_omega_opow]
    exact (lt_univ_of_lift _).le
  · exact (isNormal_opow one_lt_omega0).strictMono.id_le _

/-- `Statement:` `univ.{u, u+1}` is the least ordinal of `Ordinal.{u+1}` that is above every lift and
fixed by `α ↦ ω^α`. The fixed-point clause selects nothing: every ordinal strictly below `univ` is a
lift (`lift_of_lt_univ`), and `univ` is fixed (`omega_opow_univ`). -/
theorem univ_isLeast_above_level :
    IsLeast {x : Ordinal.{u + 1} | (∀ o : Ordinal.{u}, lift.{u + 1} o < x) ∧ ω ^ x = x}
      univ.{u, u + 1} :=
  ⟨⟨lt_univ_of_lift, omega_opow_univ⟩, fun x ⟨hx, _⟩ => not_lt.1 fun h => by
    obtain ⟨c, rfl⟩ := lift_of_lt_univ h
    exact lt_irrefl _ (hx c)⟩

/-- `Statement:` in `Ordinal.{u+1}`, `ε₀ < univ.{u, u+1}`. -/
theorem epsilon_zero_lt_univ : Ordinal.epsilon.{u + 1} 0 < univ.{u, u + 1} := by
  have := lt_univ_of_lift.{u} (Ordinal.epsilon 0)
  rwa [lift_epsilon_zero.{u, u + 1}] at this

/-! ### § III. One construction at two floors -/

/-- `Statement:` `sInf` of the fixed points of `α ↦ ω^α` strictly above every point of `S`: the least
one when one exists (`roleAbove_eq_of_isLeast`); when none exists it is `sInf ∅ = 0`, ⊥ of `Ordinal`
(at `Set.univ`: CONTROL below). At a point floor it is the § I-b role of
`ZeroParadox/Ordinal/Epsilon0CannotBe.lean`, credited there. `Reading:` that 0 is a junk value, never a role. -/
noncomputable def roleAbove (S : Set Ordinal.{u}) : Ordinal.{u} :=
  sInf {x | ω ^ x = x ∧ ∀ s ∈ S, s < x}

-- Statement: CONTROL, at the unbounded `Set.univ` no fixed point lies above every point, and
-- `roleAbove` returns 0, ⊥ of `Ordinal`.
example : roleAbove (Set.univ : Set Ordinal.{u}) = 0 := by
  have h : {x : Ordinal.{u} | ω ^ x = x ∧ ∀ s ∈ (Set.univ : Set Ordinal.{u}), s < x} = ∅ :=
    Set.eq_empty_of_forall_notMem fun x hx => lt_irrefl x (hx.2 x trivial)
  unfold roleAbove; rw [h, Ordinal.sInf_empty]

/-- `Statement:` if `a` is least among the fixed points of `α ↦ ω^α` strictly above every point of
`S`, then `roleAbove S = a`. -/
theorem roleAbove_eq_of_isLeast {S : Set Ordinal.{u}} {a : Ordinal.{u}}
    (h : IsLeast {x : Ordinal.{u} | ω ^ x = x ∧ ∀ s ∈ S, s < x} a) : roleAbove S = a :=
  h.csInf_eq

/-- `Statement:` at a point floor, `roleAbove {f} = ordinalCornerStep f`. -/
theorem roleAbove_point_floor (f : Ordinal.{u}) : roleAbove {f} = ordinalCornerStep f := by
  have hn := isNormal_opow one_lt_omega0
  apply roleAbove_eq_of_isLeast
  have hlt : f < ordinalCornerStep f := lt_ordinalCornerStep f
  refine ⟨⟨nfp_fp hn _, ?_⟩, ?_⟩
  · rintro s rfl; exact hlt
  · rintro x ⟨hx, hfx⟩
    exact nfp_le_fp hn.strictMono.monotone (succ_le_of_lt (hfx f rfl)) (le_of_eq hx)

/-- `Statement:` `roleAbove {0} = ε₀`, at 0, ⊥ of `Ordinal`. -/
theorem roleAbove_bottom_floor : roleAbove ({0} : Set Ordinal.{u}) = Ordinal.epsilon 0 := by
  rw [roleAbove_point_floor]
  show Ordinal.nfp (fun α => Ordinal.omega0 ^ α) (Order.succ 0) = _
  exact nfp_seed_independent_below_epsilon0 _ (succ_le_of_lt (epsilon_pos 0))

/-- `Statement:` `roleAbove (Set.range lift) = univ`, at the floor of all lifts. -/
theorem roleAbove_level_floor : roleAbove (Set.range lift.{u + 1, u}) = univ.{u, u + 1} := by
  apply roleAbove_eq_of_isLeast
  refine ⟨⟨omega_opow_univ, ?_⟩, ?_⟩
  · rintro _ ⟨o, rfl⟩; exact lt_univ_of_lift o
  · rintro x ⟨_, hx⟩
    by_contra h
    obtain ⟨c, rfl⟩ := lift_of_lt_univ (not_le.1 h)
    exact lt_irrefl _ (hx _ ⟨c, rfl⟩)

/-- `Statement:` in `Ordinal.{u+1}`, `roleAbove {0}` is the lift of ε₀ and `roleAbove (Set.range lift)`
is `univ.{u, u+1}`. -/
theorem roleAbove_one_construction :
    roleAbove ({0} : Set Ordinal.{u + 1}) = lift.{u + 1} (Ordinal.epsilon.{u} 0) ∧
    roleAbove (Set.range lift.{u + 1, u}) = univ.{u, u + 1} :=
  ⟨by rw [roleAbove_bottom_floor, lift_epsilon_zero.{u, u + 1}], roleAbove_level_floor⟩

/-- `Statement:` `succ 0 < nfp (ω^·) (succ 0)`; the supremum of `succ (lift o)` over `o` is `univ`;
and `nfp (ω^·) univ = univ`. -/
theorem roleAbove_work_split :
    succ (0 : Ordinal.{u}) < nfp (fun a => ω ^ a) (succ 0) ∧
    (⨆ o : Ordinal.{u}, succ (lift.{u + 1} o)) = univ.{u, u + 1} ∧
    nfp (fun a => ω ^ a) univ.{u, u + 1} = univ.{u, u + 1} := by
  have hn := isNormal_opow one_lt_omega0
  refine ⟨?_, ?_, nfp_eq_self omega_opow_univ⟩
  · refine lt_of_le_of_ne (le_nfp _ _) fun h => ?_
    have hfp := nfp_fp hn (succ (0 : Ordinal.{u}))
    rw [← h, succ_eq_add_one, zero_add, opow_one] at hfp
    exact one_lt_omega0.ne' hfp
  · have hb : BddAbove (Set.range fun o : Ordinal.{u} => succ (lift.{u + 1} o)) :=
      ⟨univ.{u, u + 1}, by rintro _ ⟨o, rfl⟩; exact succ_le_of_lt (lt_univ_of_lift o)⟩
    apply le_antisymm
    · exact ciSup_le' fun o => succ_le_of_lt (lt_univ_of_lift o)
    · apply le_of_forall_lt
      intro x hx
      obtain ⟨c, rfl⟩ := lift_of_lt_univ hx
      exact (lt_succ _).trans_le (le_ciSup hb c)

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms lt_univ_of_lift
#print axioms lift_of_lt_univ
#print axioms below_univ_is_a_copy
#print axioms over_univ_reveals_frame
#print axioms lift_omega_opow
#print axioms lift_iterate_opow
#print axioms lift_epsilon_zero
#print axioms univ_isSuccLimit
#print axioms omega_opow_univ
#print axioms univ_isLeast_above_level
#print axioms epsilon_zero_lt_univ
#print axioms roleAbove
#print axioms roleAbove_eq_of_isLeast
#print axioms roleAbove_point_floor
#print axioms roleAbove_bottom_floor
#print axioms roleAbove_level_floor
#print axioms roleAbove_one_construction
#print axioms roleAbove_work_split
end PurityCheck
