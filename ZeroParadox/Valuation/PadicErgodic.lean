-- EXPERIMENTAL (bottom-diagram probe, not a finalized layer): ergodicity of the p-adic odometer (the add-1 / adding-machine map) for the Haar measure — "start almost anywhere, get the same shape." Curated results indexed in ZeroParadox/MANIFEST.md.
import ZeroParadox.Valuation.PadicKoopman
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Action.OfMinimal
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

set_option maxHeartbeats 400000

/-!
# Ergodicity of the p-adic odometer

Experimental probe in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in ZeroParadox/MANIFEST.md.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

`PadicKoopman` already banks that the **odometer** `x ↦ c + x` is measure-preserving for the Haar
probability measure `haarZp` (left-invariance). This file takes the next step: for the add-1 odometer
`x ↦ 1 + x`, the dynamics are **ergodic** — every invariant measurable set is null or conull, so the
system does not decompose and almost every orbit sees the whole space uniformly. This is the formal
content of "start (almost) anywhere, get the same shape": the *weaker invariant* that survives where a
genuine Lawvere fixed point cannot (Cantor blocks a Set-level witness on the valuation face — see
`ZeroParadox/Category/Lawvere.lean`), realized here as an invariant-measure / ergodicity statement
rather than a fixed point.

The proof is a direct application of Mathlib's general result that a group translation is ergodic when
its orbit is dense (`ergodic_add_left_of_denseRange_zsmul`): the sole hypothesis, that the integer
multiples of `1` are dense in `ℤ_p`, is exactly `PadicInt.denseRange_intCast`. The remaining
hypotheses (finite/inner-regular/left-invariant measure, second-countable Borel space) hold for
`haarZp` on the compact group `ℤ_p`. This is standard ergodic theory — the odometer is the textbook
adding machine; **no novelty is claimed** beyond porting it onto the repo's `haarZp`.

`Classical.choice` is inherited from Mathlib's measure/dynamics libraries (a dependency, not a new
commitment). Ergodicity (§ II) is an "almost every" statement; § III adds the **every-point
topological version** — minimality, that every orbit is dense. The remaining gap is the *quantitative*
every-point version, **unique ergodicity** (every orbit equidistributing with the Haar frequencies),
which has no Mathlib API and is not claimed here.

## Structure
- § I   Density of the integer orbit of `1`
- § II  Ergodicity of the add-1 odometer (almost every start)
- § III Minimality: every orbit is dense (every start)
-/

namespace ZeroParadox

open MeasureTheory

variable {p : ℕ} [Fact p.Prime]

/-! ## § I — Density of the integer orbit of `1` -/

/-- The `ℤ`-orbit of `1` under the odometer (the integer multiples of `1`) is dense in `ℤ_p`. This is
    exactly `PadicInt.denseRange_intCast` after `n • (1 : ℤ_p) = (n : ℤ_p)`. -/
theorem denseRange_zsmul_one : DenseRange (fun n : ℤ => n • (1 : ℤ_[p])) := by
  simp only [zsmul_one]
  exact PadicInt.denseRange_intCast

/-! ## § II — Ergodicity of the add-1 odometer -/

/-- **Ergodicity of the p-adic odometer.** The add-1 map `x ↦ 1 + x` on `ℤ_p` is ergodic for the Haar
    probability measure `haarZp`: any invariant measurable set is null or conull. Formal content of
    "start (almost) anywhere, get the same shape" — the invariant that survives where a fixed point is
    Cantor-blocked. -/
theorem ergodic_odometer : Ergodic ((1 : ℤ_[p]) + ·) (haarZp (p := p)) :=
  ergodic_add_left_of_denseRange_zsmul denseRange_zsmul_one (haarZp (p := p))

/-! ## § III — Minimality: every orbit is dense (the every-point statement) -/

/-- **Topological minimality of the odometer.** For *every* starting point `x`, the forward orbit
    `{x, x+1, x+2, …}` is dense in `ℤ_p`: start anywhere and the orbit fills the whole space (its
    closure is all of `ℤ_p` — the same "shape" from any start). This is the every-point upgrade of the
    almost-everywhere statement `ergodic_odometer`. Proof: the natural-number multiples of `1` are
    dense (`PadicInt.denseRange_natCast`) and left-translation by `x` is a homeomorphism, which
    preserves density. NOTE: the *quantitative* every-point version — unique ergodicity, every orbit
    equidistributing with the Haar frequencies — is strictly stronger, has no Mathlib API, and is not
    claimed here. -/
theorem denseRange_odometer_orbit (x : ℤ_[p]) :
    DenseRange (fun n : ℕ => x + (n : ℤ_[p])) := by
  have hg : DenseRange (fun y : ℤ_[p] => x + y) :=
    Function.Surjective.denseRange (fun z => ⟨z - x, by ring⟩)
  simpa [Function.comp] using
    hg.comp PadicInt.denseRange_natCast (continuous_const.add continuous_id)

end ZeroParadox

/-! ## Axiom Purity Check

`ergodic_odometer` depends on `[propext, Classical.choice, Quot.sound]` — `Classical.choice` enters
through the Mathlib Haar / `MeasureTheory` / ergodic libraries (a dependency, not a new commitment).
No `sorryAx` appears. -/
section PurityCheck
open ZeroParadox
#print axioms ergodic_odometer
#print axioms denseRange_odometer_orbit
end PurityCheck
