-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the intertwining of the odometer's Koopman (composition) operator with the Taibleson–Vladimirov operator D^α on ℤ_p — the two operators commute, so D^α is equivariant under the odometer dynamics. The operator-level bridge; the orbit level is separately walled. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicVladimirov
import ZeroParadox.Valuation.PadicKoopman
import ZeroParadox.Valuation.PadicCharacter
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Koopman ⋈ Vladimirov: the odometer intertwines with D^α

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

Connects the two operators built by the earlier probes: the **Koopman (composition) operator** `U_c`
of the odometer `x ↦ c + x` (`PadicKoopman`) and the **Taibleson–Vladimirov operator** `D^α`
(`PadicVladimirov`). The result is the **intertwining / commutation relation**

  `D^α (U_c f) = U_c (D^α f)`,   i.e.   `(D^α (f ∘ (c + ·)))(z) = (D^α f)(c + z)`,

which says `D^α` is *equivariant* under the odometer: translating then applying the operator is the
same as applying then translating. Mechanically it is translation-invariance of `D^α`, and its single
hinge is the odometer's measure-preservation `measurePreserving_odometer` — the exact property the
Koopman operator of `PadicKoopman` is built from. (`D^α` is known to generate a Markov / diffusion
semigroup — Vladimirov–Volovich–Zelenov, Kochubei — but that semigroup is neither built nor used here.)

**Fences.** This is an **operator-level** statement (an intertwining of maps on functions `ℤ_p → ℂ`),
stated at the function/domain level because `D^α` is *unbounded* and is not the bounded `L²` Koopman
operator composed literally. It makes no dynamical-equivalence or physical claim: the **orbit / process
level** is separately walled (the matched-rate / no-orbit-correspondence result). "Equivariant" here
means the two operators commute, not that any process is identified with any other.

## Structure
- § I   The intertwining of `D^α` with the odometer's Koopman operator
- § II  The intertwining `D^α ∘ U_c = U_c ∘ D^α`
- § III Every isometry of `ℤ_p` preserves Haar measure and intertwines with `D^α`
-/

namespace ZeroParadox

open MeasureTheory
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — The intertwining of `D^α` with the odometer's Koopman operator -/

/-- **Intertwining (pointwise).** `D^α` applied to `U_c f = f ∘ (c + ·)`, at `z`, equals `D^α f` at
    `c + z`. The change of variables `y ↦ c + y` is the odometer's measure-preservation
    (`measurePreserving_odometer`); the kernel `|·|^{-(α+1)}` is translation-invariant because
    `(c + z) - (c + y) = z - y`. -/
theorem vladimirov_odometer_intertwine (α : ℝ) (c : ℤ_[p]) (f : ℤ_[p] → ℂ) (z : ℤ_[p]) :
    vladimirov α (fun x => f (c + x)) z = vladimirov α f (c + z) := by
  have hker : ∀ y : ℤ_[p], vladimirovKernel α (c + z) (c + y) = vladimirovKernel α z y := by
    intro y
    have h : (c + z) - (c + y) = z - y := by ring
    simp only [vladimirovKernel, h]
  simp only [vladimirov]
  rw [← MeasurePreserving.integral_comp (measurePreserving_odometer c) (measurableEmbedding_addLeft c)
        (fun w => (f (c + z) - f w) * (vladimirovKernel α (c + z) w : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [hker]

/-! ## § II — The commutation relation `D^α ∘ U_c = U_c ∘ D^α` -/

/-- **Commutation of operators.** As functions on `ℤ_p → ℂ`, `D^α ∘ U_c = U_c ∘ D^α`: the Vladimirov
    generator commutes with the odometer's Koopman operator. `D^α` is equivariant under the odometer. -/
theorem vladimirov_koopman_commute (α : ℝ) (c : ℤ_[p]) (f : ℤ_[p] → ℂ) :
    (fun z => vladimirov α (fun x => f (c + x)) z) = fun z => vladimirov α f (c + z) :=
  funext fun z => vladimirov_odometer_intertwine α c f z


/-! ## § III — Every isometry of `ℤ_p` preserves Haar measure and intertwines with `D^α` -/

/-- **Isometries preserve Haar measure.** Statement: an isometry `T` of `ℤ_p` is measure-preserving
    for `haarZp`. Proof: `T` respects every residue map `toZModPow n` both ways, so its induced map on
    `ZMod (pⁿ)` is injective, hence bijective; the preimage of a level-`n` fiber is a level-`n` fiber
    (`toZModPow_fiber_measure`), and the fibers are a generating π-system. Standard: Jeong,
    arXiv:2112.11012, Prop. 2.5 (for 1-Lipschitz maps: onto ⇔ isometry ⇔ bijective mod pⁿ ⇔
    measure-preserving; proof cited there to Durand–Paccaut, Prop. 4). -/
theorem isometry_measurePreserving {T : ℤ_[p] → ℤ_[p]} (hT : Isometry T) :
    MeasurePreserving T (haarZp (p := p)) (haarZp (p := p)) := by
  -- residues agree at level n iff the distance is at most p^-n
  have hiff : ∀ (n : ℕ) (u v : ℤ_[p]),
      PadicInt.toZModPow n u = PadicInt.toZModPow n v ↔ ‖u - v‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    intro n u v
    have h := Set.ext_iff.mp (toZModPow_fiber_eq (p := p) n (rfl : PadicInt.toZModPow n v = _)) u
    simpa using h
  -- an isometry preserves residues at every level, both ways
  have hkey : ∀ (n : ℕ) (u v : ℤ_[p]),
      PadicInt.toZModPow n (T u) = PadicInt.toZModPow n (T v) ↔
        PadicInt.toZModPow n u = PadicInt.toZModPow n v := by
    intro n u v
    rw [hiff, hiff, ← dist_eq_norm, ← dist_eq_norm, hT.dist_eq]
  -- the induced map on ZMod (p^n) is injective, hence surjective
  have hsurj : ∀ (n : ℕ) (r : ZMod (p ^ n)), ∃ a, PadicInt.toZModPow n (T a) = r := by
    intro n r
    have : NeZero (p ^ n) := ⟨pow_ne_zero n ‹Fact p.Prime›.out.pos.ne'⟩
    let lift : ZMod (p ^ n) → ℤ_[p] := fun s => ((s.val : ℕ) : ℤ_[p])
    have hlift : ∀ s, PadicInt.toZModPow n (lift s) = s := fun s => by
      simp only [lift, map_natCast]; exact ZMod.natCast_rightInverse s
    let Φ : ZMod (p ^ n) → ZMod (p ^ n) := fun s => PadicInt.toZModPow n (T (lift s))
    have hΦ : Function.Injective Φ := fun s t hst => by
      have := (hkey n (lift s) (lift t)).mp hst
      rwa [hlift, hlift] at this
    obtain ⟨s, hs⟩ := (Finite.injective_iff_surjective.mp hΦ) r
    exact ⟨lift s, hs⟩
  let C : Set (Set ℤ_[p]) :=
    {S | ∃ (n : ℕ) (r : ZMod (p ^ n)), S = {x | PadicInt.toZModPow n x = r}}
  -- the fibers form a π-system
  have hpi : IsPiSystem C := by
    rintro S ⟨n, r, rfl⟩ U ⟨m, s, rfl⟩ ⟨z, hzS, hzU⟩
    simp only [Set.mem_ofPred_eq] at hzS hzU
    rcases le_total n m with hnm | hmn
    · refine ⟨m, s, ?_⟩
      ext w
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rw [← hzS, hiff]
      have hw := (hiff m w z).mp (h.trans hzU.symm)
      exact hw.trans (zpow_le_zpow_right₀ (by exact_mod_cast ‹Fact p.Prime›.out.one_lt.le)
        (by simpa using hnm))
    · refine ⟨n, r, ?_⟩
      ext w
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      rw [← hzU, hiff]
      have hw := (hiff n w z).mp (h.trans hzS.symm)
      exact hw.trans (zpow_le_zpow_right₀ (by exact_mod_cast ‹Fact p.Prime›.out.one_lt.le)
        (by simpa using hmn))
  -- the fibers form a topological basis
  have hbasis : TopologicalSpace.IsTopologicalBasis C := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro S ⟨n, r, rfl⟩
      obtain ⟨x0, hx0⟩ := toZModPow_surjective (p := p) n r
      rw [toZModPow_fiber_eq n hx0]
      have : {x : ℤ_[p] | ‖x - x0‖ ≤ (p : ℝ) ^ (-(n : ℤ))} =
          Metric.closedBall x0 ((p : ℝ) ^ (-(n : ℤ))) := by
        ext x; simp [Metric.mem_closedBall, dist_eq_norm]
      rw [this]
      exact IsUltrametricDist.isOpen_closedBall _
        (zpow_pos (by exact_mod_cast ‹Fact p.Prime›.out.pos) _).ne'
    · intro a u hau hu
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu a hau
      have hp1 : (1 : ℝ) < p := by exact_mod_cast ‹Fact p.Prime›.out.one_lt
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp1)
      refine ⟨{x | PadicInt.toZModPow n x = PadicInt.toZModPow n a}, ⟨n, _, rfl⟩, rfl, ?_⟩
      intro x hx
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have := (hiff n x a).mp hx
      calc ‖x - a‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := this
        _ = ((p : ℝ)⁻¹) ^ n := by rw [zpow_neg, zpow_natCast, inv_pow]
        _ < ε := hn
  have hgen : (inferInstance : MeasurableSpace ℤ_[p]) = MeasurableSpace.generateFrom C :=
    BorelSpace.measurable_eq.trans hbasis.borel_eq_generateFrom
  refine ⟨hT.continuous.measurable, ?_⟩
  refine ext_of_generate_finite C hgen hpi ?_ ?_
  · rintro S ⟨n, r, rfl⟩
    rw [Measure.map_apply hT.continuous.measurable (toZModPow_fiber_measurableSet n r)]
    obtain ⟨a, ha⟩ := hsurj n r
    have hpre : T ⁻¹' {x | PadicInt.toZModPow n x = r} =
        {x | PadicInt.toZModPow n x = PadicInt.toZModPow n a} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← ha]
      exact hkey n w a
    rw [hpre, toZModPow_fiber_measure, toZModPow_fiber_measure]
  · rw [Measure.map_apply hT.continuous.measurable MeasurableSet.univ, Set.preimage_univ]

/-- **Isometries intertwine with `D^α` (pointwise).** Statement: for an isometry `T` that preserves
    Haar measure, `D^α (f ∘ T) z = (D^α f) (T z)`. The kernel is unchanged because
    `‖T z − T y‖ = ‖z − y‖`; the change of variables is `hmp`. Albeverio–Kozyrev, arXiv:1105.1506,
    § 3, transformation rule (2) and its Vladimirov case `D^α ∘ Φ = p^(−γα) Φ ∘ D^α`, stated on `ℚ_p`;
    an isometry has `γ = 0`. -/
theorem vladimirov_isometry_intertwine (α : ℝ) {T : ℤ_[p] → ℤ_[p]} (hT : Isometry T)
    (hmp : MeasurePreserving T (haarZp (p := p)) (haarZp (p := p))) (f : ℤ_[p] → ℂ) (z : ℤ_[p]) :
    vladimirov α (f ∘ T) z = vladimirov α f (T z) := by
  have hker : ∀ y : ℤ_[p], vladimirovKernel α (T z) (T y) = vladimirovKernel α z y := by
    intro y
    have h : ‖T z - T y‖ = ‖z - y‖ := by rw [← dist_eq_norm, ← dist_eq_norm, hT.dist_eq]
    simp only [vladimirovKernel, h]
  simp only [vladimirov, Function.comp_apply]
  rw [← hmp.integral_comp hT.isClosedEmbedding.measurableEmbedding
        (fun w => (f (T z) - f w) * (vladimirovKernel α (T z) w : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [hker]

/-- **Isometries intertwine with `D^α`, no measure hypothesis.** Statement: as functions,
    `D^α (f ∘ T) = (D^α f) ∘ T` for every isometry `T` of `ℤ_p`; `hmp` is discharged by
    `isometry_measurePreserving`. -/
theorem vladimirov_isometry_commute (α : ℝ) {T : ℤ_[p] → ℤ_[p]} (hT : Isometry T)
    (f : ℤ_[p] → ℂ) :
    (fun z => vladimirov α (f ∘ T) z) = fun z => vladimirov α f (T z) :=
  funext fun z => vladimirov_isometry_intertwine α hT (isometry_measurePreserving hT) f z

-- Statement: the odometer case `vladimirov_odometer_intertwine` is the instance `T = (c + ·)`.
example (α : ℝ) (c : ℤ_[p]) (f : ℤ_[p] → ℂ) (z : ℤ_[p]) :
    vladimirov α (fun x => f (c + x)) z = vladimirov α f (c + z) :=
  vladimirov_isometry_intertwine α (IsometryEquiv.addLeft c).isometry
    (measurePreserving_odometer c) f z

-- Statement: CONTROL. The non-isometric map `z ↦ p·z` does not preserve Haar measure: it sends all
-- of `ℤ_p` (mass 1) into the residue-0 fiber of `toZModPow 1` (mass `p⁻¹`).
example : ¬ MeasurePreserving (fun z : ℤ_[p] => (p : ℤ_[p]) * z)
    (haarZp (p := p)) (haarZp (p := p)) := by
  intro hmp
  have hpre : (fun z : ℤ_[p] => (p : ℤ_[p]) * z) ⁻¹' {x | PadicInt.toZModPow 1 x = 0} = Set.univ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true, map_mul, map_natCast]
    rw [(ZMod.natCast_eq_zero_iff p (p ^ 1)).mpr (by rw [pow_one]), zero_mul]
  have h := hmp.measure_preimage (toZModPow_fiber_measurableSet (p := p) 1 0).nullMeasurableSet
  rw [hpre, measure_univ, toZModPow_fiber_measure, pow_one] at h
  have hp : (1 : ℝ≥0∞) < p := by exact_mod_cast ‹Fact p.Prime›.out.one_lt
  have : ((p : ℝ≥0∞))⁻¹ < 1 := ENNReal.inv_lt_one.mpr hp
  rw [← h] at this
  exact lt_irrefl _ this

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms vladimirov_odometer_intertwine
#print axioms vladimirov_koopman_commute
#print axioms isometry_measurePreserving
#print axioms vladimirov_isometry_intertwine
#print axioms vladimirov_isometry_commute
end PurityCheck
