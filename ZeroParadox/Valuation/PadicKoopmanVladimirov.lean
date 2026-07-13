-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): the intertwining of the odometer's Koopman (composition) operator with the Taibleson–Vladimirov operator D^α on ℤ_p — the two operators commute, so D^α is equivariant under the odometer dynamics. The operator-level bridge; the orbit level is separately walled. Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicVladimirov
import ZeroParadox.Valuation.PadicKoopman
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
semigroup — Vladimirov–Volovich–Zelenov, Kochubei — but that semigroup is neither built nor used here;
this file is the operator-level commutation only.)

**Fences.** This is an **operator-level** statement (an intertwining of maps on functions `ℤ_p → ℂ`),
stated at the function/domain level because `D^α` is *unbounded* and is not the bounded `L²` Koopman
operator composed literally. It makes no dynamical-equivalence or physical claim: the **orbit / process
level** is separately walled (the matched-rate / no-orbit-correspondence result). "Equivariant" here
means the two operators commute, not that any process is identified with any other.

## Structure
- § I   The kernel is translation-invariant
- § II  The intertwining `D^α ∘ U_c = U_c ∘ D^α`
-/

namespace ZeroParadox

open MeasureTheory

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

end ZeroParadox

/-! ## Axiom Purity Check -/
section PurityCheck
open ZeroParadox
#print axioms vladimirov_odometer_intertwine
#print axioms vladimirov_koopman_commute
end PurityCheck
