import ZeroParadox.Vendored.NaturalOps
import Mathlib.SetTheory.Ordinal.Exponential

set_option linter.deprecated false

/-!
# Natural sum on powers of ω — the deferred CNF characterization (ported)

`NaturalOps.lean` (vendored from Mathlib v4.28.0) lists as its open `## Todo` the characterization of
natural addition in terms of the Cantor normal form. That characterization was completed *after* the
file left Mathlib, in the Combinatorial Game Theory repo: `CombinatorialGames/NatOrdinal/Pow.lean`
(Violeta Hernández, Apache-2.0). This file PORTS the part of that proof we need — that powers of ω are
closed under natural sum (`a, b < ω^c → a ♯ b < ω^c`) — adapted to the vendored Mathlib-v4.28 API
(`toNatOrdinal`/`toOrdinal` rather than the CGT repo's `of`/`val`).

This is the one fact the Kirby–Paris ordinal-decrease argument needs beyond the basic `nadd` API: it is
what bounds the hydra's regrowth (a finite natural sum of `ω^β` terms) below the next power `ω^(β+1)`.

Provenance: the proof structure (the `wpow_mul_natCast_add_of_lt_aux` induction, `termination_by
(x,n,y)`) is Violeta Hernández's, from `vihdzp/combinatorial-games`. Port changes are marked `-- [ZP]`.
See `.claude-local/notes/kirby_paris_nadd_absent_2026-06-29.md`.
-/

namespace ZeroParadox.NaturalOpsPow

open Ordinal NaturalOps

-- [ZP] CGT uses `of`/`val` for the two directions of the Ordinal ≃o NatOrdinal; alias to ours so the
-- ported proof text stays close to the source.
local notation "ofN" => Ordinal.toNatOrdinal

/-- [ZP] `val` of a `NatOrdinal` (CGT spelling `x.val`). -/
noncomputable abbrev val (x : NatOrdinal) : Ordinal := NatOrdinal.toOrdinal x

@[simp] theorem val_lt_iff {a b : NatOrdinal} : val a < val b ↔ a < b :=
  NatOrdinal.toOrdinal.lt_iff_lt

@[simp] theorem val_le_iff {a b : NatOrdinal} : val a ≤ val b ↔ a ≤ b :=
  NatOrdinal.toOrdinal.le_iff_le

@[simp] theorem val_ofN (a : Ordinal) : val (ofN a) = a := rfl
@[simp] theorem ofN_val (a : NatOrdinal) : ofN (val a) = a := rfl
@[simp] theorem val_zero : val 0 = 0 := rfl
@[simp] theorem val_natCast (n : ℕ) : val (n : NatOrdinal) = n := NatOrdinal.toOrdinal_natCast n

/-- [ZP] `ω^` on `NatOrdinal`, matching CGT's `Wpow` (`ω^ x = ofN (ω ^ x.val)`). -/
noncomputable def wpow (x : NatOrdinal) : NatOrdinal := ofN (omega0 ^ val x)

@[simp] theorem val_wpow (x : NatOrdinal) : val (wpow x) = omega0 ^ val x := rfl
@[simp] theorem wpow_pos (x : NatOrdinal) : 0 < wpow x := opow_pos _ omega0_pos
theorem wpow_ne_zero (x : NatOrdinal) : wpow x ≠ 0 := (wpow_pos x).ne'

theorem wpow_def (x : NatOrdinal) : wpow x = ofN (omega0 ^ val x) := rfl

theorem val_eq_iff {a b : NatOrdinal} : val a = val b ↔ a = b :=
  NatOrdinal.toOrdinal.injective.eq_iff

@[simp] theorem val_add (a b : NatOrdinal) : val (a + b) = val a ♯ val b := by
  rw [Ordinal.nadd_eq_add]; rfl

@[simp] theorem val_mul (a b : NatOrdinal) : val (a * b) = val a ⨳ val b := by
  rw [Ordinal.nmul_eq_mul]; rfl

-- [ZP] CGT's `oadd_le_add` / `omul_le_mul` (ordinary op ≤ natural op), via our `add_le_nadd` /
-- `mul_le_nmul`.
theorem oadd_le_add (a b : NatOrdinal) : ofN (val a + val b) ≤ a + b := by
  rw [← val_le_iff]; simpa using Ordinal.add_le_nadd (a := val a) (b := val b)

theorem omul_le_mul (a b : NatOrdinal) : ofN (val a * val b) ≤ a * b := by
  rw [← val_le_iff]; simpa using Ordinal.mul_le_nmul (val a) (val b)

theorem lt_mul_add_one {x y z : Ordinal} : x < y * (z + 1) ↔ ∃ w < y, x ≤ y * z + w := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mul_add_one, Ordinal.lt_add_iff hy]

/-- Ported from Violeta Hernández, `CombinatorialGames/NatOrdinal/Pow.lean`
    (`wpow_mul_natCast_add_of_lt_aux`). The first conjunct is closure of `ω^x` under natural sum; the
    second is the CNF identity `ω^x * n + y = ofN(ω^(val x) * n + val y)` for `y < ω^x`. -/
theorem aux (x : NatOrdinal) (n : ℕ) (y : NatOrdinal) (hy : y < wpow x) :
    (∀ z < wpow x, z + y < wpow x) ∧
      wpow x * n + y = ofN (omega0 ^ val x * n + val y) := by
  obtain rfl | hx := eq_or_ne x 0
  · have hy0 : y = 0 := by
      have : y < 1 := by simpa [wpow, NatOrdinal.lt_one_iff_zero] using hy
      simpa [NatOrdinal.lt_one_iff_zero] using this
    subst hy0
    refine ⟨fun z hz => ?_, ?_⟩
    · simpa [wpow, NatOrdinal.lt_one_iff_zero] using hz
    · simp [wpow]
  have H : ∀ z < wpow x, z + y < wpow x := by
    intro z hz
    have hm := max_lt hy hz
    rw [wpow_def, ← val_lt_iff, val_ofN,
      lt_omega0_opow (b := val x) (NatOrdinal.toOrdinal_eq_zero.not.2 hx)] at hm
    obtain ⟨a, ha, m, hn⟩ := hm
    have hyz (k : ℕ) := (aux (ofN a) k 0 (wpow_pos (ofN a))).2
    simp_rw [val_zero, add_zero, ← val_eq_iff, val_ofN] at hyz
    rw [← hyz] at hn
    calc
      z + y ≤ max y z + max y z := add_le_add (le_max_right ..) (le_max_left ..)
      _ < wpow (ofN a) * m + wpow (ofN a) * m := add_lt_add hn hn
      _ < _ := by
        rw [← mul_add, ← Nat.cast_add, ← val_lt_iff, val_wpow]
        rw [hyz]
        exact opow_mul_lt_opow (natCast_lt_omega0 _) ha
  refine ⟨H, le_antisymm ?_ ?_⟩
  · refine NatOrdinal.add_le_iff.2 ⟨?_, ?_⟩ <;> intro z hz
    · match n with
      | 0 => simp only [Nat.cast_zero, mul_zero] at hz; exact absurd hz (NatOrdinal.not_lt_zero z)
      | 1 =>
        simp_rw [Nat.cast_one, mul_one] at *
        apply (H z hz).trans_le
        rw [wpow_def, ← val_le_iff]; simp only [val_ofN]; exact le_self_add ..
      | n + 1 + 1 =>
        rw [Nat.cast_add_one, mul_add_one] at hz
        obtain ⟨a, ha, hz⟩ : ∃ a < wpow x, z ≤ wpow x * ↑(n + 1) + a := by
          obtain (⟨a, ha, hz⟩ | h) := NatOrdinal.lt_add_iff.1 hz
          · have hxn := (aux x (n + 1) 0 (wpow_pos x)).2
            simp_rw [val_zero, add_zero] at hxn
            rw [hxn, ← val_lt_iff, val_ofN, Nat.cast_add_one, lt_mul_add_one] at ha
            obtain ⟨b, hb, hbw⟩ := ha
            have hb' : ofN b < wpow x := by rw [← val_lt_iff, val_ofN, val_wpow]; exact hb
            have hkey : omega0 ^ val x * ↑n + b = val (wpow x * ↑n + ofN b) := by
              rw [(aux x n (ofN b) hb').2]; simp
            rw [hkey, val_le_iff] at hbw
            refine ⟨ofN b, hb', ?_⟩
            calc z ≤ a + wpow x := hz
              _ ≤ (wpow x * ↑n + ofN b) + wpow x := by gcongr
              _ = wpow x * ↑(n + 1) + ofN b := by
                  rw [add_assoc, add_comm (ofN b) (wpow x), ← add_assoc, ← mul_add_one,
                    ← Nat.cast_add_one]
          · exact h
        have ha' := H a ha
        have hav : val (a + y) < omega0 ^ val x := by rw [← val_wpow]; exact val_lt_iff.2 ha'
        calc z + y ≤ (wpow x * ↑(n + 1) + a) + y := by gcongr
          _ = wpow x * ↑(n + 1) + (a + y) := by rw [add_assoc]
          _ < ofN (omega0 ^ val x * ↑(n + 1 + 1) + val y) := by
              rw [(aux x (n + 1) (a + y) ha').2, ← val_lt_iff, val_ofN, val_ofN,
                Nat.cast_add_one (n + 1), mul_add_one, add_assoc]
              exact (add_lt_add_iff_left _).2 (lt_of_lt_of_le hav (le_self_add ..))
    · rw [(aux x n z (hz.trans hy)).2]
      simpa
  · rw [← val_le_iff, val_ofN, val_add, val_mul, val_wpow, val_natCast]
    calc omega0 ^ val x * (n : Ordinal) + val y
        ≤ (omega0 ^ val x ⨳ (n : Ordinal)) + val y := by gcongr; exact Ordinal.mul_le_nmul _ _
      _ ≤ (omega0 ^ val x ⨳ (n : Ordinal)) ♯ val y := Ordinal.add_le_nadd _ _
  termination_by (x, n, y)

/-- **Powers of ω are closed under natural sum** — the vendored file's open CNF `Todo`, ported. -/
theorem nadd_lt_omega0_opow {a b c : Ordinal} (ha : a < omega0 ^ c) (hb : b < omega0 ^ c) :
    a ♯ b < omega0 ^ c := by
  have hy : ofN b < wpow (ofN c) := by rw [wpow_def, val_ofN]; simpa using hb
  have hz : ofN a < wpow (ofN c) := by rw [wpow_def, val_ofN]; simpa using ha
  have key := (aux (ofN c) 0 (ofN b) hy).1 (ofN a) hz
  rw [wpow_def, val_ofN, ← val_lt_iff, val_ofN] at key
  rwa [Ordinal.nadd_eq_add]

end ZeroParadox.NaturalOpsPow
