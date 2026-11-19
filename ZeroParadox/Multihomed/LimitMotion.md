# LimitMotion — the limit retraction as a die motion

Ride-along companion to `ZeroParadox/Multihomed/LimitMotion.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md`.

## Formal Overview (AI-assisted)

For a continuous self-map `g` of a Hausdorff space, `limitRetraction g` sends `x` to the limit of
its orbit where that orbit converges, and is undefined elsewhere. `limitMotion g` is the `Motion`
(`ZeroParadox/Die.lean`) with that partial map as UP and one step `y = g x` as OVER.

- § I. `up_idem` holds because a limit of iterates of a continuous map is a fixed point
  (Mathlib `isFixedPt_of_tendsto_iterate`). `lm_jumpMap_breaks_idem` is the control: for a
  discontinuous map of ℝ the limit of an orbit need not be the limit of its own orbit. The corpus
  `omegaLim` (`ZeroParadox/Valuation/BottomInvariant.lean` § IV) equals Mathlib's `omegaLimit` at a
  singleton start (`lm_omegaLim_eq_omegaLimit`); a value `p` of the limit retraction gives
  `omegaLim g x = {p}` (`lm_omegaLim_of_mem`), and on a compact space the converse holds
  (`lm_mem_iff_omegaLim`).
- § II. `lm_tendsto_iff_arrival_or_closure`: the orbit tends to `p` iff either `x` arrives at `p`
  along OVER and `p` is a landing, or no stage is fixed and the stages have a stage closure with
  value `p`. The two branches exclude each other (`lm_not_arrives_of_closure`). On `OnePoint K`,
  adjoining `∞` adds no OVER step into it (`lm_not_arrives_infty`), so an orbit tending to `∞` is
  always in the closure branch.
- § III. A homeomorphism conjugating two maps is a strict isomorphism of their limit motions
  (`lmIsoOfConj`). On `OnePoint K`, `onePointInv` conjugates scaling by `c` to scaling by `d`,
  `c * d = 1` (`lmHealedIso`); it exchanges the two distinct points `0` and `∞`. Inside `K`, field
  inversion is a strict isomorphism of the bare function motions (`lmBareInvIso`) and no strict map
  of the limit motions (`lm_torn_no_hom`).
- § IV. Instances: doubling on `OnePoint ℚ_[2]` closes at `0` without arriving; halving there and
  doubling on `OnePoint ℝ` tend to `∞` without arriving; `lm_q2_torn`, `lm_real_torn`. The
  oscillating orbit of `1` under scaling by `-1` is the control on both carriers.
- § V. The reverse direction, from existing declarations only. In `Ordinal` the ω-tower seeded at
  0, ⊥ of `Ordinal`, is § II's closure branch with UP value ε₀ (`ordinalTowerMotion_stageClosure`);
  in `ℤ_[2]` the same tower's images only approach ℤ_[2]'s 0 (`snap_arc_z2_loop`).

None of this is the snap: no covering step `bot ⋖ a` appears in any statement here
(`ZeroParadox/Multihomed/SnapFrameChange.lean` § II).

## Prior art and credit

This file is an instance of the limit-retraction programme, with weaker hypotheses and weaker
conclusions.

- M. Abate, "Iteration theory, compactly divergent sequences and commuting holomorphic maps",
  Ann. Sc. Norm. Sup. Pisa Cl. Sci. (4) 18 (1991), no. 2, 167–191. Theorem 0.3, p. 169, credited
  there to Bedford and to Abate: for a taut manifold and a map whose iterates are not compactly
  divergent, a holomorphic retraction onto the limit manifold; p. 169 names it the limit
  retraction, and the iterates converge iff `f` is the identity on that manifold.
- R. Venturini, "On the orbits of not expansive mappings in metric spaces", arXiv:1304.1023.
  Theorem 5.1 (pp. 13–14), item (viii): for `x, y` off the compactly divergent set,
  `lim f^k(x) = y` iff `y = ρ(x)` and `f(y) = y`. pp. 18–19 define the limit retraction and the
  extended limit retraction `ρ̂ : X → X̂` into the Alexandroff compactification; Theorem 5.2
  (p. 19). He assumes `f` non-expansive on a locally compact metric space and does not extend `f`
  to the added point; here `lmScale` is extended and fixes `∞`.
- J. Milnor, Dynamics lecture notes, § 5 "Attraction and Repulsion" (2001), § 5A: the basin of
  attraction, the domain of `limitRetraction g`; p. 5-9, `∞` as an attractor on `ℂ ∪ ∞`.
  Conjugacy invariance of basins is that section's framing; `lmIsoOfConj` proves the die form.
- Compare Séré's retraction onto `Fix(T)` (Theorem 17 of Fournais, Lewin and Triay,
  arXiv:1911.09482, p. 24), in a Banach setting.

The delta, stated plainly: any continuous map of a Hausdorff space, a partial map, no metric; and
only the convergent orbits, with no group of limit maps. Only the die packaging is new: the
arrival-or-closure iff and the healed/torn contrast. The split into "eventually fixed" and "never
fixed" orbits is folklore.

Mathlib, searched 2026-11-19 (LeanExplore, three phrasings; theoremsearch with one formal
phrasing): `isFixedPt_of_tendsto_iterate`, `omegaLimit`, `mem_omegaLimit_singleton_iff_mapClusterPt`,
`tendsto_nhds_of_unique_mapClusterPt`. No limit-retraction or basin declaration was located as of
that date; the null is uninformative.

The § V bound is cited, not claimed: Escardó, preprint of JSL 78(3) (2013), § 11, p. 19, "it is not
possible to embed ε₀ in 2^ℕ using limit structures" (quoted in `ZeroParadox/DieCannotBe.lean`).
