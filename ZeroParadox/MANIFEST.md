# ZeroParadox Lean sources - manifest

This folder holds the Lean 4 formalization for the Zero Paradox framework. It contains two kinds of file,
and this manifest says which is which so a reader knows what to read. Files in the **experimental** class
also carry a one-line `-- EXPERIMENTAL (branch scaffolding)` header at the top.

This material grew out of a broader exploratory arc that is kept privately; only the rigorous, review-cleared
Lean is surfaced here. The speculative interpretation behind it is deliberately not part of this repository.

The single best entry point is **`ZPH_BottomCannotBe.lean`**: a machine-checked (`#check`-only) index that
gathers the established results about the framework's bottom element across every layer and organizes them
by a classification schema. Within this repository the shorthand for it is "Bottom-Meta". It declares
nothing of its own and only `#check`s already-proved results, so building it recompiles every result it
cites; it is a curated map of what is established, not a source of new claims.

**On the central claim (read this first).** The organizing thesis is that the bottom element recurs in the
same structural role across several domains. What is **proved** is the *membership* and the *recurrence of
the slot structure*. What is **not** proved, and is stated only as a conjecture/program, is that the various
bottoms are *one object*: they are provably distinct as structures (the "walls" results in the campaign).
The index above is where the precise line between proved and conjectural is kept.

## Core (finalized results - read these)

- **The formal layers** - assembled in `Basic.lean` (`ZPA`…`ZPH`, `ZPI`, `ZPJ*`, `ZPK*`, `ZPL`, `ZPM`,
  `ZPN*`, `ZPP*` core). The established framework.
- **The synthesis index** - `ZPH_BottomCannotBe.lean` (Bottom-Meta). The curated map.
- **Standalone results built this arc** (each cold-audited):
  - `ZPP_RiemannSphere.lean` - inversion on `OnePoint ℚ₂` is a homeomorphism swapping `0` and `∞`.
  - `ZPH_HilbertDiagonal.lean` - the Hilbert bottom is the unique finite-dim fixed point of the
    biproduct-diagonal `X ↦ X ⊞ X`.
  - `ZPH_MarkovSpectralGap.lean` - a mixing Markov chain's relaxation is irreversible (non-injective
    transfer operator; geometric decay of off-stationary modes).
- **Direction A - the archimedean place** - `ZPH_ArchPlace`, `ZPH_PlaceForcing`, `ZPH_PlaceMetric`,
  `ZPH_AdeleGlobal`, `ZPH_PlaceAllPrimes`.
- **The finite Perron–Frobenius / ergodic / spectral set** - `ZPH_PerronFrobenius`, `ZPH_EigenvectorExists`,
  `ZPH_SpectralRadius`, `ZPH_PerronCapstone`, `ZPH_MeanErgodic`, `ZPH_ReversibleSpectrum`.
- **The ordinal-descent theorems** - `ZPP_Goodstein`, `ZPP_KirbyParis`, `ZPP_Kruskal`, `ZPP_WeakGoodstein`
  (Goodstein, Kirby–Paris, and labeled Kruskal, proved unconditionally).

## Experimental (branch scaffolding - the lab notebook)

These carry the `-- EXPERIMENTAL` header. They are the exploratory work from which the core results were
distilled, kept for transparency. The genuine, load-bearing results among them are cited by
`ZPH_BottomCannotBe.lean`; the rest are probes, dead ends, and honest negatives, retained as the record of
how the map was built.

- **The bottom-diagram probe campaign** - the `ZPH_MC1_*` family: `ZPH_MC1_TC04`…`ZPH_MC1_TC50` (pairwise
  go/no-go tests of how the various bottom-constructions relate), the `ZPH_MC1_Tree*` infrastructure, and
  the named probes (`ZPH_MC1_Linearize`, `ZPH_MC1_Fork`, `ZPH_MC1_Obstruction`, etc.). Most entries are
  decorative or inconclusive by their own cold-audit verdicts; the load-bearing ones are indexed in
  Bottom-Meta.
- **Deflated attempts (honest negatives)** - `ZPH_StrippedBottom` (a ⊥-by-inversion attempt, reframed after
  a cold audit caught the overclaim) and `ZPH_TwoFacesBot` (tested whether two faces of ⊥ unify at the
  seam; came back vacuous).
