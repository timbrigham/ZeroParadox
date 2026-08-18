# Evidence for a universal at the existence level, and where it stops

Argument, scope and fences for `ZeroParadox/Valuation/BottomInvariant.lean`. The Lean file holds the
declarations, the Engineer's Take and the per-declaration glosses.

**Experimental probe** in the bottom-diagram mapping campaign — not a finalized layer. Curated results
are indexed in `ZeroParadox/MANIFEST.md`.

## The conjecture being probed

That the *weaker invariant* — an invariant measure, "same shape from anywhere" — rather than a Lawvere
fixed point, is the universal that recurs across the framework's faces. The Lean file abstracts the
least common denominator uniformly provable so far.

`BottomInvariantMeasure X` bundles a self-map `f : X → X` with an invariant Borel probability measure
`μ` (`MeasurePreserving f μ μ`). It is instantiated by **two already-proved dynamics on two different
spaces**:

- `odometerBIM` — the odometer `x ↦ 1 + x` on `ℤ_p` with the Haar measure (the *spread* invariant;
  ergodic and minimal — `ZeroParadox/Valuation/PadicErgodic.lean`).
- `attractorBIM` — the doubling map `x ↦ 2·x` on `Q₂` with the Dirac mass `δ₀` at the floor (the
  *concentrated* invariant; every orbit converges to `0` —
  `ZeroParadox/Valuation/PadicAttractor.lean`).

The point: a "spread" invariant (Haar) and a "concentrated" invariant (δ₀) — opposite in character —
fit **one** structure. That is evidence the invariant-measure shape is genuinely universal across these
two dynamics, where the fixed-*point* shape is not (Cantor blocks a genuine one on the valuation face).

**Caveat on "universal".** The two `Measure`-based instances live on the framework's *valuation* face
(`ℤ_p`, `Q₂`) — within-domain evidence, two opposite p-adic dynamics. The Markov section carries the
same idea to a **genuinely different domain**: the stochastic bottom (`markovBIK`, finite Markov kernels
with a stationary distribution). That gives three faces across two domains. The unification section then
brings them together: `InvariantMarkovKernel`, a single structure over Mathlib's general
`MeasureTheory.Kernel`, of which all three faces are instances (the two deterministic p-adic faces via
`Kernel.deterministic`, the stochastic face as a genuine Markov kernel) — so the universal is *one*
structure, not two parallel ones. The order / category / set-theory faces are not measure-theoretic and
fall outside this abstraction entirely.

## Honest scope — the fence

This is the EXISTENCE level only: each face carries *an* invariant probability measure. The *strong*
uniform statement — that the measure is UNIQUE (unique ergodicity), so *every* orbit sees the same shape
at the right rate — is **not** proved: Mathlib has no unique-ergodicity API.

What is separately proved per face is the topological "same shape from anywhere": the odometer's orbits
are all dense (`denseRange_odometer_orbit`) and the attractor's orbits all converge to the floor
(`doubling_orbit_tendsto_zero`). Uniqueness across all faces, and additional faces (computability,
category), remain OPEN — this is the first two data points, not the universal in full.

`Classical.choice` is inherited from Mathlib's measure libraries (a dependency, not a new commitment).

## The BOTH-AT-ONCE regime: a unit multiplier carries both characters

**Nothing here is new mathematics.** That multiplication by a unit fixes the origin and preserves norms
is elementary; the content is the **identification**, and it closes a gap the overview above leaves open.

The two invariants above — the *spread* one (odometer, Haar) and the *concentrated* one (doubling map,
`δ₀`) — are exhibited **on two different maps**. So the file shows the two characters are compatible
with one *structure*, never that one *dynamic* carries both. This supplies a dynamic that does, and it
is already in the corpus: multiplication by a 2-adic **unit**
(`ZeroParadox/Valuation/ContractionRate.lean`, `unit_orbit_norm_const`, witnessed by
`three_is_unit : ‖(3 : Q₂)‖ = 1`).

**The three regimes, decided by the valuation of the multiplier:**

| multiplier | orbit behaviour | invariant character |
|---|---|---|
| ideal, `‖c‖ < 1` (e.g. `×2` — the framework's own `selfApp` on `ℚ₂`, `q2_unique_fp`) | contracts to `0` | **concentrated only** |
| **unit, `‖u‖ = 1` (e.g. `×3`)** | norm constant on every orbit | **BOTH** |
| odometer `x ↦ 1 + x` | no fixed point, orbits dense | **spread only** |

**Why the unit row carries both.** It **fixes the floor** (`unitMul_fixes_floor`), so `δ₀` is invariant
— the concentrated character, machine-checked. And it **preserves every sphere** (`unitMul_norm_const`),
so it is a norm-preserving additive bijection of `ℤ_p` and therefore preserves the Haar probability
measure — the spread character.

**⚠ HONEST FENCE — the Haar half is NOT formalized.** That an automorphism of a compact group preserves
its Haar probability measure is standard, but the Lean file does not prove it for `unitMul`; only the
`δ₀` half is machine-checked. Do not cite this for the Haar claim.

**The standard result IS available in the pin, so the fence should be closable rather than merely
declared** (prior-art gate, 2026-07-30): `mulEquivHaarChar_eq_one_of_compactSpace`
(`Mathlib/MeasureTheory/Measure/Haar/MulEquivHaarChar.lean`,
`[CompactSpace G] (φ : G ≃ₜ* G) : mulEquivHaarChar φ = 1`), whose additive alias
`addEquivAddHaarChar_eq_one_of_compactSpace` is the one that applies — `ℤ_p` is a compact additive
topological group and `unitMul u` is a topological additive automorphism for `u` a unit. So the gap is a
*build*, not an absence. Stated as adjacency, not as a claim: nothing is proved from it.

**And note what sphere-preservation costs:** the spheres are invariant sets of intermediate measure, so
`unitMul` is **not ergodic** for Haar — it admits *many* invariant measures. That is the failure of
unique ergodicity, which the overview flags as the strong statement it cannot prove. This only *locates*
a dynamic where the failure is visible; it proves neither the failure nor the uniqueness.

Reading: `.claude-local/notes/paradox_as_simultaneous_inversion_2026-07-30.md`.
