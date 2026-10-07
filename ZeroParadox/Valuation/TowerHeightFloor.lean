-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Valuation.InfinitudeFloor
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Height meets floor: the tower's 2-adic images as an InfinitudeFloor, norm order reversed from stage 1 — ε₀ ≠ ⊥ of `Ordinal` preserved

## Engineer's Take

The height and the floor fight because they point opposite ways. That they fight, with epsilon zero never
being the bottom of the ordinals, is exactly why this needed to be built rather than avoided. Chart behaviour
can have an inversion inside it. Read by the valuation, the tower climbs up to infinity. Read by the norm, it
falls down to zero, and only from stage one on. The map into the 2-adic integers holds the height and the
floor apart while joining them, and that fight is the whole content.

This came from being sure the fight between the height and the floor was the reason to build it, not avoid it.
Sometimes it helps to work through this from the ground up. Much of what is here re-derives results the
framework already has, and that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

The tower's 2-adic images as an `InfinitudeFloor ℤ_[2]` with floor ℤ_[2]'s 0, beside the ordinal height ε₀
and `ε₀ ≠ 0` in `Ordinal`, never identified. Argument and fence: `ZeroParadox/Valuation/TowerHeightFloor.md`.
-/

namespace ZeroParadox

open Ordinal

/-! ### § I. A support lemma: the successors are unbounded in `ℕ∞`. -/

/-- `⨆ n, ↑(n+1) = ⊤` in `ℕ∞` — the climbing complexities are unbounded. -/
private theorem iSup_natSucc_top : ⨆ n : ℕ, ((n + 1 : ℕ) : ℕ∞) = ⊤ := by
  rw [iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  exact ⟨b, by exact_mod_cast Nat.lt_succ_self b⟩

/-! ### § II. The complexity on `ℤ_[2]` and its value on the tower images. -/

open Classical in
/-- The 2-adic complexity: the valuation off 0, `⊤` at the floor, ℤ_[2]'s 0. -/
noncomputable def towerCx (x : ℤ_[2]) : ℕ∞ := if x = 0 then ⊤ else (x.valuation : ℕ∞)

/-- The floor has infinite complexity: `towerCx 0 = ⊤`. -/
theorem towerCx_zero : towerCx (0 : ℤ_[2]) = ⊤ := by
  unfold towerCx; rw [if_pos rfl]

/-- On tower image `n+1`, the complexity is exactly `n+1` (`cnfToZp2_tower_valuation`); the members'
complexities climb. -/
theorem towerCx_member (n : ℕ) :
    towerCx (cnfToZp2 (towerNONote (n + 1))) = ((n + 1 : ℕ) : ℕ∞) := by
  have hne : cnfToZp2 (towerNONote (n + 1)) ≠ 0 := (snap_arc_z2_loop.2.1) (n + 1) (by omega)
  have hval : (cnfToZp2 (towerNONote (n + 1))).valuation = n + 1 := cnfToZp2_tower_valuation (n + 1)
  unfold towerCx
  rw [if_neg hne, hval]

/-! ### § III. The genuine InfinitudeFloor instance on the tower's 2-adic images. -/

/-- **The tower as an InfinitudeFloor.** The tower's 2-adic images form the infinitude of climbing nulls
whose floor is ℤ_[2]'s 0, with infinite complexity. A def (an exhibited witness), not a global instance. -/
@[reducible] noncomputable def towerInfinitudeFloor : InfinitudeFloor ℤ_[2] where
  floor := 0
  cx := towerCx
  member := fun n => cnfToZp2 (towerNONote (n + 1))
  cx_member_strictMono := by
    have h : (fun n => towerCx (cnfToZp2 (towerNONote (n + 1)))) = (fun n => ((n + 1 : ℕ) : ℕ∞)) :=
      funext towerCx_member
    rw [h]
    intro a b hab
    show ((a + 1 : ℕ) : ℕ∞) < ((b + 1 : ℕ) : ℕ∞)
    exact_mod_cast Nat.add_lt_add_right hab 1
  cx_floor_eq_iSup := by
    show towerCx 0 = ⨆ n, towerCx (cnfToZp2 (towerNONote (n + 1)))
    rw [towerCx_zero]
    rw [show (fun n => towerCx (cnfToZp2 (towerNONote (n + 1)))) = (fun n => ((n + 1 : ℕ) : ℕ∞)) from
      funext towerCx_member]
    exact iSup_natSucc_top.symm

/-! ### § IV. The reconciliation — ε₀ ≠ 0 in `Ordinal` proved inside the statement that connects them. -/

/-- **Height meets floor, reconciled.** One shared construction, two carrier-specific closures held apart by
`cnfToZp2` (along the tower: valuation order kept, `tower_orders_agree`; norm order reversed from stage 1,
`ZeroParadox/Ordinal/Epsilon0CannotBe.lean` § V):

1. the InfinitudeFloor's floor, ℤ_[2]'s 0, has **infinite complexity** `cx = ⊤`, by the definition of
   `towerCx` (`towerCx_zero`); the members' climbing complexities have that `⊤` as supremum
   (`cx_floor_eq_iSup`);
2. the **same** tower ascends on the ordinal side to the **height** `ε₀ = ⨆ fundamentalSeq`;
3. and `ε₀ ≠ 0`, 0 the ordinals' floor (`epsilon0_ne_zero`) — the height is **not** the floor.

The fight between "ascends to ε₀" and "descends to ℤ_[2]'s 0" is resolved by the map, never by collapse: the 2-adic
floor 0 is the limit of the tower's `cnfToZp2` images, never a `cnfToZp2` image of ε₀ (ε₀ lies outside
`NONote`; through the canonical threshold map and `snapEmbed` it does land on 0, `snap_state_zp2_is_zero`),
and this theorem *proves* `ε₀ ≠ 0` in `Ordinal` while joining the two closures. -/
theorem tower_height_floor_reconciliation :
    (@InfinitudeFloor.cx ℤ_[2] towerInfinitudeFloor towerInfinitudeFloor.floor = ⊤) ∧
    (epsilonZero = ⨆ n : ℕ, fundamentalSeq n) ∧
    epsilonZero ≠ 0 := by
  refine ⟨?_, epsilonZero_eq_iSup, epsilon0_ne_zero⟩
  exact infinitude_forces_infinite_complexity ℤ_[2] (I := towerInfinitudeFloor)

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms towerCx_zero
#print axioms towerCx_member
#print axioms towerInfinitudeFloor
#print axioms tower_height_floor_reconciliation
end PurityCheck
