import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Valuation.InfinitudeFloor
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Height meets floor: the ordinal tower IS an InfinitudeFloor, order-reversed — ε₀ ≠ ⊥ preserved

## Engineer's Take

The height and the floor fight because they point opposite ways. That they fight, with epsilon zero never
being bottom, is exactly why this needed to be built rather than avoided. The order-reversing map is what
holds them apart while joining them, and that fight is the whole content.

This came from being sure the fight between the height and the floor was the reason to build it, not avoid it.
Sometimes it helps to work through this from the ground up. Much of what is here re-derives results the
framework already has, and that is fine. The movement of the thought process itself was what I needed.

---

## Formal Overview (AI-assisted)

The tower ASCENDS (ordinal side) to its height ε₀; an `InfinitudeFloor` DESCENDS (its members climb in
complexity) to a floor ⊥ of infinite complexity. These orientations *fight* — and that fight is exactly the
content, because the order-reversing bridge `cnfToZp2` (`Ordinal/CnfBridge.lean`) is what reconciles them
**without ever asserting `ε₀ = ⊥`** (a cross-type identity, ill-typed per MC-1 / ZP-P). Building the tie is
required *precisely because* it fights `ε₀ ≠ ⊥`: the map turning ascent-to-ε₀ into descent-to-⊥ is the wall
that is the spine.

`towerInfinitudeFloor : InfinitudeFloor ℤ_[2]` is a **genuine instance** realizing this:
* `floor = 0` (= ⊥ in `ℤ_[2]`);
* `member n = cnfToZp2 (towerNONote (n+1))` — the tower's 2-adic images (the shared construction of
  `mu_construction_correspondence`), each `≠ 0` (`snap_arc_z2_loop`);
* `cx x = ↑x.valuation` off 0, `⊤` at 0 — and `cx (member n) = n+1` (`cnfToZp2_tower_valuation`), so the
  complexities **climb** and drive `cx floor = ⊤` (`infinitude_forces_infinite_complexity`).

The **order-reversal is visible in the numbers**: as `n` rises, the 2-adic *valuation* rises (`= n+1`) while
the *norm* falls to 0 — valuation-up ⟺ norm-down is `cnfToZp2` being antitone. The SAME index sequence
ascends on the ordinal side to ε₀.

`tower_height_floor_reconciliation` bundles the reconciliation and **proves `ε₀ ≠ 0` in the same statement
that connects the two closures**: (1) the InfinitudeFloor floor ⊥ has infinite complexity `cx = ⊤`; (2) the
shared tower ascends to the height `ε₀ = ⨆ fundamentalSeq`; (3) `ε₀ ≠ 0` — the height is NOT the floor. One
construction, two carrier-specific closures (ε₀ ; ⊥), opposite orientations, joined by the order-reversing
map and held apart by it. No cross-type `=`; `ε₀ = 0` stays ill-typed.

**Honest fence.** The floor lives in `ℤ_[2]`, the height in `Ordinal`; they are co-witnessed through the
shared `towerNONote`, never identified. `towerInfinitudeFloor` is a `def` (an exhibited witness), not a
registered global instance on `ℤ_[2]`.
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
/-- The 2-adic complexity: the valuation off 0, `⊤` at the floor 0 (= ⊥). -/
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
whose floor is ⊥ = 0 with infinite complexity. A def (an exhibited witness), not a global instance. -/
@[reducible] noncomputable def towerInfinitudeFloor : InfinitudeFloor ℤ_[2] where
  floor := 0
  cx := towerCx
  member := fun n => cnfToZp2 (towerNONote (n + 1))
  member_ne_floor := fun n => (snap_arc_z2_loop.2.1) (n + 1) (by omega)
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

/-! ### § IV. The reconciliation — ε₀ ≠ ⊥ proved inside the statement that connects them. -/

/-- **Height meets floor, reconciled.** One shared construction, two carrier-specific closures held apart by
the order-reversing `cnfToZp2`:

1. the InfinitudeFloor floor ⊥ = 0 (in `ℤ_[2]`) has **infinite complexity** `cx = ⊤` — driven by the tower
   images climbing (valuation ↑, norm ↓ to the floor);
2. the **same** tower ascends on the ordinal side to the **height** `ε₀ = ⨆ fundamentalSeq`;
3. and `ε₀ ≠ 0` — the height is **not** the floor.

The fight between "ascends to ε₀" and "descends to ⊥" is resolved by the map, never by collapse: `ε₀ = 0`
stays a cross-type boundary, and this theorem *proves* they are distinct while joining them. -/
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
