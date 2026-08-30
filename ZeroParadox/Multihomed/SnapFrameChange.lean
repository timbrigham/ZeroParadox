-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the valuation-frame realization of the POLE EXCHANGE (the snap-as-instance reading is ZP-Q's conjecture, not established here - see the declaration docstring) — P8's tower encoding sends the ω-tower (climbing to ε₀) to the 2-adic floor 0 = ⊥: its stage-encodings converge to 0 in the encoding chart (reading that floor as a NEW bottom ⊥ₙ₊₁ is C-DA2, a commitment no theorem here carries), while the SAME encodings, viewed through the Riemann-sphere frame-change rInv (0↔∞), diverge to the antipode ∞. rInv is the passage between the two charts. (The encodings converge to ⊥; ε₀, the ordinal sup of the stages, is never ⊥ — ε₀ ≠ ⊥.) Conjectural synthesis at the operator/space level; the abstract cross-domain "snap = frame-change" stays open. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Ordinal.P8
import ZeroParadox.Valuation.RiemannSphere
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# The tower limit's two chart-readings: ⊥ and ∞ are two charts, swapped by `rInv`

Experimental probe in the bottom-diagram campaign — not a finalized layer; results are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

The formal overview and every fence live in the ride-along `SnapFrameChange.md`; each result is
stated once more at its own declaration below.
-/

namespace ZeroParadox

open Filter Topology OnePoint

/-! ## § I — The tower under the frame-change tends to `∞` -/

/-- **The tower, viewed through the frame-change, rises to `∞`.** P8's tower encodings converge to the
    2-adic floor `0`; pushed into the Riemann sphere `OnePoint ℚ₂` and viewed through the inversion
    `rInv` (which sends `0 ↦ ∞`), the *same* tower tends to `∞`. The dual chart to
    `cnf_encode_tower_tendsto_zero`. -/
theorem snap_frameflip_tower_tendsto_infty :
    Tendsto (fun k => rInv (OnePoint.some (((cnf_encode (towerOrd k)) : ℤ_[2]) : ℚ_[2])))
      atTop (𝓝 (∞ : Sphere)) := by
  -- P8: the tower encodings converge to the 2-adic floor 0.
  have h0 : Tendsto (fun k => cnf_encode (towerOrd k)) atTop (𝓝 (0 : ℤ_[2])) :=
    cnf_encode_tower_tendsto_zero
  -- Push into ℚ₂ (the coercion ℤ₂ → ℚ₂ is continuous).
  have hq : Tendsto (fun k => (((cnf_encode (towerOrd k)) : ℤ_[2]) : ℚ_[2]))
      atTop (𝓝 (0 : ℚ_[2])) := by
    have hc : Continuous (fun z : ℤ_[2] => (z : ℚ_[2])) := continuous_subtype_val
    simpa using (hc.tendsto (0 : ℤ_[2])).comp h0
  -- Push into the sphere `OnePoint ℚ₂`.
  have hs : Tendsto (fun k => OnePoint.some (((cnf_encode (towerOrd k)) : ℤ_[2]) : ℚ_[2]))
      atTop (𝓝 (OnePoint.some (0 : ℚ_[2]))) :=
    (OnePoint.continuous_coe.tendsto (0 : ℚ_[2])).comp hq
  -- Apply the frame-change `rInv`, continuous, with `rInv 0 = ∞`.
  have hr := (continuous_rInv.tendsto (OnePoint.some (0 : ℚ_[2]))).comp hs
  rwa [rInv_zero] at hr

/-! ## § II — The two charts, bundled -/

/-- **The two chart-readings of the tower's limit (valuation frame).**

    ⚠ **NAME CORRECTION (Tim, 2026-07-30). The handle `snap_is_frameflip` is retained per the CC-2 /
    MC-1 convention — do not rename, the cross-references are live — but it OVERCLAIMS and the statement
    is the authority. THE SNAP DOES NOT APPEAR IN THIS STATEMENT.** There is no `c₀ → c₁`, no `bot ⋖ a`,
    no `⊥ → ε₀` here.

    `Statement:` a three-part conjunction about ONE sequence — the ω-tower's encodings converge to `0` in
    the encoding chart; the SAME encodings diverge to `∞` under `rInv`; and `rInv` exchanges the two poles.
    So: one object, two chart-readings, and a chart map swapping them.

    `Reading:` **the FRAME CHANGE is ⊥ being both `0` and `∞`** — the two readings of the bottom — and
    `rInv` is what exchanges them. The **SNAP is a separate statement**: one covering step off the zero face
    (`bot ⋖ a`, `HasFirstStep`, AX-B1), which is a commitment, not a chart change. Merging the two is what
    the layer's older framing did, and it is what produced the standing puzzle that a frame flip is an
    involution (reversible) while the snap is one-way. That mismatch is what an identification would have to
    resolve; ZP-Q holds it open rather than settling it either way.
    (ε₀ ≠ ⊥: the encodings converge to ⊥, they do not realize ε₀ as ⊥.) -/
theorem snap_is_frameflip :
    Tendsto (fun k => cnf_encode (towerOrd k)) atTop (𝓝 (0 : ℤ_[2]))
      ∧ Tendsto (fun k => rInv (OnePoint.some (((cnf_encode (towerOrd k)) : ℤ_[2]) : ℚ_[2])))
          atTop (𝓝 (∞ : Sphere))
      ∧ (rInv (OnePoint.some (0 : ℚ_[2])) = ∞ ∧ rInv (∞ : Sphere) = OnePoint.some (0 : ℚ_[2])) :=
  ⟨cnf_encode_tower_tendsto_zero, snap_frameflip_tower_tendsto_infty, ⟨rInv_zero, rInv_infty⟩⟩

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms snap_frameflip_tower_tendsto_infty
#print axioms snap_is_frameflip
end PurityCheck
