-- EXPERIMENTAL (branch scaffolding): bottom-as-boundary pivot, worked through from the ground up; mostly re-derivation of existing framework results, kept for transparency. Curated/load-bearing results are indexed in ZeroParadox/BottomCannotBe.lean and classified in ZeroParadox/MANIFEST.md.
import ZeroParadox.Ordinal.CnfBridge
import ZeroParadox.Ordinal.Epsilon0LeastFP
import ZeroParadox.Valuation.InfinitudeFloor
import ZeroParadox.Valuation.PoleCornersBridge
import ZeroParadox.Ordinal.PricedInterface
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Height meets floor: the tower's 2-adic images as an InfinitudeFloor, norm order reversed from stage 1 — ε₀ ≠ ⊥ of `Ordinal` preserved

## Engineer's Take

The height and the floor fight because they point opposite ways. That they fight, with epsilon zero never
being the bottom of the ordinals, is exactly why this needed to be built rather than avoided. Chart behaviour
can have an inversion inside it. Read by the valuation, the tower climbs up to infinity. Read by the norm, it
falls down to zero, and only from stage one on. The map taking the tower's stages into the 2-adic integers
holds the height and the floor apart while joining them, and that fight is the whole content.

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
floor 0 is the limit of the tower's `cnfToZp2` images, never a `cnfToZp2` image of ε₀ (no `NONote`
denotes ε₀, `repr_lt_epsilon0`; through the canonical threshold map and `snapEmbed` it does land on 0, `snap_state_zp2_is_zero`),
and this theorem *proves* `ε₀ ≠ 0` in `Ordinal` while joining the two closures. -/
theorem tower_height_floor_reconciliation :
    (@InfinitudeFloor.cx ℤ_[2] towerInfinitudeFloor towerInfinitudeFloor.floor = ⊤) ∧
    (epsilonZero = ⨆ n : ℕ, fundamentalSeq n) ∧
    epsilonZero ≠ 0 := by
  refine ⟨?_, epsilonZero_eq_iSup, epsilon0_ne_zero⟩
  exact infinitude_forces_infinite_complexity ℤ_[2] (I := towerInfinitudeFloor)

/-! ### § V. The asymptote along the tower, in both charts -/

open Filter Topology

/-- `Statement:` along the tower stages from stage 1, `n ↦ towerNONote (n + 1)`. Ordinal side: the
    denotations climb strictly, each is below ε₀, and ε₀ is their supremum. 2-adic side: their
    `cnfToZp2` images have `towerCx` climbing strictly through finite values, are never ℤ_[2]'s 0,
    tend to ℤ_[2]'s 0, and `towerCx 0 = ⊤` is the supremum of their `towerCx`. And the two orders
    agree: one stage is below another in `Ordinal` iff its image's `towerCx` is below the other's.
    `Reading:` the tower's image IS the doubling orbit: from stage 1, `cnfToZp2` sends the tower to
    `n ↦ 2 ^ (n + 1)` (the `example` below), the doubling orbit of `2` in ℤ_[2]. The map carries the
    asymptote's shape from the ordinal chart to the 2-adic chart; ε₀ itself has no image
    (`eps0_no_preimage`). -/
theorem asymptote_preserved :
    (StrictMono (fun n => NONote.repr (towerNONote (n + 1))) ∧
      (∀ n, NONote.repr (towerNONote (n + 1)) < epsilonZero) ∧
      epsilonZero = ⨆ n, NONote.repr (towerNONote (n + 1))) ∧
    (StrictMono (fun n => towerCx (cnfToZp2 (towerNONote (n + 1)))) ∧
      (∀ n, towerCx (cnfToZp2 (towerNONote (n + 1))) < ⊤) ∧
      (∀ n, cnfToZp2 (towerNONote (n + 1)) ≠ 0) ∧
      Tendsto (fun n => cnfToZp2 (towerNONote (n + 1))) atTop (𝓝 0) ∧
      towerCx 0 = ⊤ ∧ towerCx 0 = ⨆ n, towerCx (cnfToZp2 (towerNONote (n + 1)))) ∧
    (∀ m n, NONote.repr (towerNONote (m + 1)) < NONote.repr (towerNONote (n + 1)) ↔
      towerCx (cnfToZp2 (towerNONote (m + 1))) < towerCx (cnfToZp2 (towerNONote (n + 1)))) := by
  have hrepr : StrictMono (fun n => NONote.repr (towerNONote (n + 1))) := fun a b h => by
    simp only [towerNONote_repr]
    exact fundamentalSeq_strictMono' (Nat.succ_lt_succ h)
  have hcx : StrictMono (fun n => towerCx (cnfToZp2 (towerNONote (n + 1)))) :=
    towerInfinitudeFloor.cx_member_strictMono
  have hb : BddAbove (Set.range fun n : ℕ => fundamentalSeq (n + 1)) :=
    ⟨epsilonZero, by rintro _ ⟨n, rfl⟩; exact (epsilonZero_tower_lt (n + 1)).le⟩
  have hsup : epsilonZero = ⨆ n : ℕ, fundamentalSeq (n + 1) := by
    apply le_antisymm
    · rw [epsilonZero_eq_iSup]
      exact Ordinal.iSup_le fun n =>
        (fundamentalSeq_strictMono' (Nat.lt_succ_self n)).le.trans (le_ciSup hb n)
    · exact Ordinal.iSup_le fun n => (epsilonZero_tower_lt (n + 1)).le
  refine ⟨⟨hrepr, fun n => by rw [towerNONote_repr]; exact epsilonZero_tower_lt (n + 1), ?_⟩,
    ⟨hcx, fun n => member_cx_lt_top (I := towerInfinitudeFloor) n,
     fun n => member_ne_floor (I := towerInfinitudeFloor) n,
     tower_converges_to_zero.comp (tendsto_add_atTop_nat 1), towerCx_zero,
     towerInfinitudeFloor.cx_floor_eq_iSup⟩,
    fun m n => hrepr.lt_iff_lt.trans hcx.lt_iff_lt.symm⟩
  simp only [towerNONote_repr]; exact hsup

-- Statement: from stage 1, the tower's `cnfToZp2` images are `2 ^ (n + 1)` in ℤ_[2].
example (n : ℕ) : cnfToZp2 (towerNONote (n + 1)) = (2 : ℤ_[2]) ^ (n + 1) := by
  rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote]
  show (2 : ℤ_[2]) ^ ((cnfToZp2 (towerNONote n)).valuation + 1) = _
  rw [cnfToZp2_tower_valuation]

/-- `Statement:` no normal-form notation denotes ε₀ (`repr_lt_epsilon0`). -/
theorem eps0_no_preimage : ∀ x : NONote, NONote.repr x ≠ epsilonZero :=
  fun x => (repr_lt_epsilon0 x.1).ne

-- Statement: Mathlib's `not_strictAnti_of_wellFoundedLT`: no sequence `ℕ → Ordinal` is strictly
-- decreasing.
example (f : ℕ → Ordinal) : ¬ StrictAnti f := not_strictAnti_of_wellFoundedLT f

/-- `Statement:` CONTROL: with stage 0 included, the `towerCx` of the tower's images is not strictly
    increasing (stage 0 maps to ℤ_[2]'s 0, of `towerCx` `⊤`). -/
theorem seed_breaks_climb : ¬ StrictMono (fun n => towerCx (cnfToZp2 (towerNONote n))) := by
  intro h
  have h01 := h (Nat.zero_lt_one)
  simp only [towerNONote] at h01
  rw [cnfToZp2_zero, towerCx_zero] at h01
  exact not_top_lt h01

/-- `Statement:` CONTROL: with Mathlib's ℕ-valued `PadicInt.valuation`, ℤ_[2]'s 0 has valuation 0,
    below every image from stage 1; the images' valuations are unbounded; and their supremum in ℕ
    is 0. -/
theorem nat_valuation_control :
    (0 : ℤ_[2]).valuation = 0 ∧
    (∀ n, (0 : ℤ_[2]).valuation < (cnfToZp2 (towerNONote (n + 1))).valuation) ∧
    ¬ BddAbove (Set.range fun n => (cnfToZp2 (towerNONote n)).valuation) ∧
    (⨆ n, (cnfToZp2 (towerNONote n)).valuation) = 0 := by
  have hv : (fun n => (cnfToZp2 (towerNONote n)).valuation) = id := funext cnfToZp2_tower_valuation
  have hnb : ¬ BddAbove (Set.range fun n => (cnfToZp2 (towerNONote n)).valuation) := by
    rw [hv]; rintro ⟨b, hb⟩; exact absurd (hb ⟨b + 1, rfl⟩) (by simp)
  refine ⟨PadicInt.valuation_zero, fun n => ?_, hnb, ?_⟩
  · rw [PadicInt.valuation_zero, cnfToZp2_tower_valuation]; omega
  · rw [iSup, csSup_of_not_bddAbove hnb, csSup_empty]; rfl

/-! ### § VI. The `PinnedLimit` role (`ZeroParadox/Die.lean` § XXIV) at ℤ_[2]'s 0 -/

/-- `Statement:` `q2Val (2 ^ n * x) = q2Val x + n` for `x ≠ 0`. -/
theorem q2Val_two_pow_mul (x : ℤ_[2]) (hx : x ≠ 0) (n : ℕ) :
    q2Val ((2 : ℤ_[2]) ^ n * x) = q2Val x + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, q2Val_scale _ (mul_ne_zero (pow_ne_zero _ two_ne_zero) hx), ih]
    push_cast; rw [add_assoc]

/-- `Statement:` for `x ≠ 0` in ℤ_[2], `n ↦ 2 ^ n * x` is a run of `2 * ·`, and ℤ_[2]'s 0 occupies
    `PinnedLimitUnique (2 * ·)` along it in the preorder lifted along `q2Val`. -/
theorem z2_dbl_pinnedLimitUnique (x : ℤ_[2]) (hx : x ≠ 0) :
    (Motion.ofFun fun z : ℤ_[2] => 2 * z).IsRun (fun n => (2 : ℤ_[2]) ^ n * x) ∧
    @PinnedLimitUnique ℤ_[2] (Preorder.lift q2Val) (fun z => 2 * z)
      (fun n => (2 : ℤ_[2]) ^ n * x) 0 := by
  letI : Preorder ℤ_[2] := Preorder.lift q2Val
  refine ⟨fun n => by show (2 : ℤ_[2]) ^ (n + 1) * x = 2 * ((2 : ℤ_[2]) ^ n * x); ring,
    ⟨⟨⟨?_, ?_⟩, ?_, ⟨mul_zero 2, ?_⟩, ?_⟩, fun z hz => q2Scale_unique_fp z hz⟩⟩
  · rintro _ ⟨n, rfl⟩
    show q2Val _ ≤ q2Val 0
    rw [q2Val_bot]; exact le_top
  · intro b hb
    show q2Val 0 ≤ q2Val b
    have key : q2Val b = ⊤ := by
      by_contra hne
      obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hne
      have h1 : q2Val ((2 : ℤ_[2]) ^ (m + 1) * x) ≤ q2Val b := hb ⟨m + 1, rfl⟩
      rw [q2Val_two_pow_mul x hx, ← hm] at h1
      have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ q2Val x + ((m + 1 : ℕ) : ℕ∞) := le_add_self
      have h3 := h2.trans h1
      have h4 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := h3
      norm_cast at h4; omega
    rw [key]; exact le_top
  · rintro ⟨n, hn⟩
    exact mul_ne_zero (pow_ne_zero n two_ne_zero) hx hn
  · intro z hz
    have hz0 : z = 0 := q2Scale_unique_fp z hz
    subst hz0; exact le_rfl
  · intro m n hmn
    show q2Val _ ≤ q2Val _
    rw [q2Val_two_pow_mul x hx, q2Val_two_pow_mul x hx]
    gcongr

/-- `Statement:` the tower's `cnfToZp2` images from stage 1 are a run of `2 * ·`; ℤ_[2]'s 0 occupies
    `PinnedLimitUnique (2 * ·)` along them in the preorder lifted along `q2Val`; ℤ_[2]'s 0 is greatest
    in that preorder; and ℤ_[2]'s 0 steps to itself only under `2 * ·`. -/
theorem tower_images_pinnedLimit :
    (Motion.ofFun fun z : ℤ_[2] => 2 * z).IsRun (fun n => cnfToZp2 (towerNONote (n + 1))) ∧
    @PinnedLimitUnique ℤ_[2] (Preorder.lift q2Val) (fun z => 2 * z)
      (fun n => cnfToZp2 (towerNONote (n + 1))) 0 ∧
    @IsTop ℤ_[2] (Preorder.lift q2Val).toLE 0 ∧
    (Motion.ofFun fun z : ℤ_[2] => 2 * z).SelfOnlyAt 0 := by
  have e : (fun n => cnfToZp2 (towerNONote (n + 1))) = fun n => (2 : ℤ_[2]) ^ n * 2 := by
    funext n
    rw [towerNONote_succ_eq, cnfToZp2_omegaPowNote]
    show (2 : ℤ_[2]) ^ ((cnfToZp2 (towerNONote n)).valuation + 1) = _
    rw [cnfToZp2_tower_valuation, pow_succ]
  rw [e]
  exact ⟨(z2_dbl_pinnedLimitUnique 2 two_ne_zero).1, (z2_dbl_pinnedLimitUnique 2 two_ne_zero).2,
    z2_two_views.2.1, z2_two_views.2.2.2.2.2.2.2⟩

/-- `Statement:` CONTROL: the same images are a run of `towerImageStep`, and in every preorder on
    ℤ_[2] no point occupies `PinnedLimit towerImageStep` along any run. -/
theorem tower_images_towerImageStep_empty (inst : Preorder ℤ_[2]) :
    (Motion.ofFun towerImageStep).IsRun (fun n => cnfToZp2 (towerNONote (n + 1))) ∧
    ∀ s c, ¬ @PinnedLimit ℤ_[2] inst towerImageStep s c := by
  refine ⟨fun n => ?_, fun s c h => ?_⟩
  · show cnfToZp2 (towerNONote (n + 1 + 1)) = towerImageStep (cnfToZp2 (towerNONote (n + 1)))
    rw [towerNONote_succ_eq (n + 1), cnfToZp2_omegaPowNote]
  · exact (Motion.leavesAt_ofFun_iff towerImageStep c).1 (towerImageStep_leavesAt c) h.2.2.1.1

/-- `Statement:` CONTROL: in the preorder on ℤ_[2] lifted along the norm, no point occupies
    `PinnedLimit (2 * ·)` along any run of `2 * ·`. -/
theorem z2_norm_dbl_empty (s : ℕ → ℤ_[2]) (hs : (Motion.ofFun fun z : ℤ_[2] => 2 * z).IsRun s)
    (c : ℤ_[2]) : ¬ @PinnedLimit ℤ_[2] (Preorder.lift (‖·‖ : ℤ_[2] → ℝ)) (fun z => 2 * z) s c := by
  letI : Preorder ℤ_[2] := Preorder.lift (‖·‖ : ℤ_[2] → ℝ)
  rintro ⟨hlub, hnot, -, hmono⟩
  have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from Nat.cast_ofNat.symm, PadicInt.norm_p]; norm_num
  have hz : ∀ n, s n = 0 := by
    intro n
    have hle : ‖s n‖ ≤ ‖s (n + 1)‖ := hmono (Nat.le_succ n)
    rw [show s (n + 1) = 2 * s n from hs n, norm_mul] at hle
    have : ‖s n‖ = 0 := by
      by_contra hne
      have hp : 0 < ‖s n‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith
    exact norm_eq_zero.1 this
  have hc : ‖c‖ ≤ ‖(0 : ℤ_[2])‖ := hlub.2 (by rintro _ ⟨n, rfl⟩; show ‖s n‖ ≤ ‖(0 : ℤ_[2])‖; rw [hz n])
  rw [norm_zero] at hc
  exact hnot ⟨0, by rw [hz 0]; exact (norm_le_zero_iff.1 hc).symm⟩

end ZeroParadox

section PurityCheck
open ZeroParadox
#print axioms towerCx_zero
#print axioms towerCx_member
#print axioms towerInfinitudeFloor
#print axioms tower_height_floor_reconciliation
#print axioms asymptote_preserved
#print axioms eps0_no_preimage
#print axioms seed_breaks_climb
#print axioms nat_valuation_control
#print axioms q2Val_two_pow_mul
#print axioms z2_dbl_pinnedLimitUnique
#print axioms tower_images_pinnedLimit
#print axioms tower_images_towerImageStep_empty
#print axioms z2_norm_dbl_empty
end PurityCheck
