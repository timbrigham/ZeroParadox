# BendDie — the overlap condition, and complex scaling as a limit motion

Ride-along companion to `ZeroParadox/Multihomed/BendDie.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXVI.

## Formal Overview (AI-assisted)

- § I. `th3_AD_no_upLax_of_proj_ne` (`ZeroParadox/Multihomed/TH3Die.lean`) rules out the lax UP square
  for a map with `c₀ ↦ v` and `c₁ ↦ th3E0` when the projection of `v` onto `ℂ ∙ th3E0` is not
  `th3E0`. For a unit vector `u`,
  the projection of `v` onto `ℂ ∙ u` is `u` iff `⟪u, v⟫ = 1` (`bend_proj_eq_self_iff`). So, with
  `c₁ ↦ th3E0` fixed, the obstruction fires iff `⟪th3E0, v⟫ ≠ 1` (`bend_AD_obstructed_iff`). It fires at the anti-parallel
  `-th3E0` (`bend_antiparallel`) and at the phase-shifted `i • th3E0` (`bend_phase`), as at the
  orthogonal `th3E1`, so it does not separate the three (`bend_no_separation`). The control is
  `bend_overlap_one`: for `w ⊥ th3E0` the square exists at `th3E0 + w`.
- § II. Scaling `lmScale c` on `OnePoint ℂ` (`ZeroParadox/Multihomed/LimitMotion.lean`). If
  `0 < ‖c‖ < 1`, orbits from `z ≠ 0` close at `0` without arriving (`bend_closure_zero`); if
  `1 < ‖c‖`, they close at `∞` without arriving (`bend_closure_infty`). The polar form, the angle
  step and the negated angle under inversion are `bend_iterate_polar`, `bend_arg_iterate` and
  `bend_inv_angle`.
- §§ III–IV. If `‖c‖ ≠ 1` and `‖d‖ ≠ 1`, a homeomorphism of `OnePoint ℂ` conjugates `lmScale c` to
  `lmScale d` (`bend_conj_of_norm_ne_one`), so their limit motions are strictly isomorphic, a
  strict isomorphism being `Motion.StrictIso` (ZP shorthand: the die isomorphism; § VI)
  (`bend_iso_of_norm_ne_one`, through `lmIsoOfConj`). On one side of the unit circle the radial
  power `bendRadial` matches the moduli and the twist `bendTwist`, `z ↦ z · exp(iα log ‖z‖)`, matches
  the angles; across it, `onePointInvHomeo` comes first. The twist alone gives `bendIso` and
  `bend_iso_abs`.
- § V. At `‖c‖ = 1`. Complex conjugation, extended to `OnePoint ℂ`, makes `lmScale c` and
  `lmScale (conj c)` strictly isomorphic (`bendConjIso`); `bend_iso_I_negI` is the case `c = i`.
  The negative controls are `bend_rotation_ne_identity` (a scaling `c ≠ 1` against the identity) and
  `bend_halfturn_ne_quarterturn`, whose proof uses that the half turn squares to the identity and
  that the quarter turn does not (`i · i = -1 ≠ 1`). `Reading:` neither negative control makes the
  angle an invariant; § VI measures what the die isomorphism sees for periodic maps.
- § VI. `Motion.StrictIso` (`ZeroParadox/Die.lean`) asks for a bijection carrying steps and
  commuting with UP, and no continuity of the bijection; `limitMotion g` takes a continuous
  self-map `g` of a Hausdorff space. If `g^[n] x = x` with `0 < n`, the limit retraction has a
  value at `x` iff `x` is a fixed point (`bend_mem_limitRetraction_of_periodic`, which assumes no
  continuity of `g`). So for continuous `g`, `h` on Hausdorff spaces with `g^[n] = id` and
  `h^[m] = id` (`0 < n`, `0 < m`), the limit motions are strictly isomorphic iff some bijection
  conjugates `g` to `h` (`bend_strictIso_iff_conj_of_periodic`; the iso is `bendPeriodicIso`).
  Conjugacy by a bijection is conjugacy in the symmetric group, classified by cycle type; Mathlib's
  finite form is `Equiv.Perm.isConj_iff_cycleType_eq`, and the form for an infinite carrier was not
  located in Mathlib as of 2026-11-19 (searched: LeanExplore, theoremsearch with a formal phrasing,
  `exact?`). Without periodicity, for continuous `g`, `h` on Hausdorff spaces, a homeomorphism
  conjugating them gives a strict isomorphism (`lmIsoOfConj`). The test case is
  rotation by `ζ = exp(2πi/5)` against rotation by `ζ²`: `bendFiveIso` is a strict isomorphism,
  through `bendFiveFwd z = ζ^(bendSector z) · z`, and `bend_sector_shift` is the sector-index step it
  uses. `bend_zeta_sq_conditions` proves `‖ζ‖ = ‖ζ²‖ = 1`, `ζ ≠ ζ²` and `ζ ≠ conj (ζ²)`.
  `Reading:` by Rybalkina–Sergeichuk Lemma 2.1 (literature, below; not a corpus theorem) the two
  rotations are then not topologically conjugate, so at `‖c‖ = 1` the die isomorphism identifies
  rotations that topological conjugacy separates.

Axiom footprints: the `PurityCheck` section at the end of `BendDie.lean`.

## Prior art

- Standard framing: the topological classification of Möbius (linear) maps. Rybalkina and
  Sergeichuk, "Topological classification of Möbius transformations", J. Math. Sci. (N.Y.) 193
  (2013) 769–774, arXiv:1308.4224. p. 3 defines a Möbius map as loxodromic "if it is conjugate to
  `z ↦ μz` with `μ ∉ ℝ` and `|μ| ≠ 1`" and elliptic if "`|μ| = 1` and `μ ≠ 1`". These are the
  Archimedean senses on `ℂ ∪ {∞}`; `ZeroParadox/Valuation/RiemannSphere.md` uses "loxodromic" in the
  p-adic (Bruhat–Tits) sense, on another carrier.
  - Lemma 2.1 (p. 6): "Möbius transformations `f(z) = az` and `g(z) = bz` are topologically
    conjugate if and only if `|a|, |b| ≠ 1`, or `a = b`, or `a = b̄`." `bend_conj_of_norm_ne_one`
    is the "if" half of the first case, with an explicit homeomorphism; across the unit circle it
    goes through `z ↦ 1/z`, as their proof does (p. 7). `bendConjIso` is the die form of the third
    case. The "only if" half is not proved here.
  - Corollary 1.1 (p. 4): "(a) Each hyperbolic or loxodromic Möbius transformation is topologically
    conjugate to `z ↦ 2z`. (b) Each elliptic Möbius transformation is topologically conjugate to
    `z ↦ μz` (`|μ| = 1`) which is uniquely determined up to replacement of `μ` by `μ̄`."
- T. Budnytska, "Topological conjugacy classes of affine maps", arXiv:0812.4921v2 (2009), Lemma 4.1
  (p. 15), on ℂ: `az` and `cz` are topologically conjugate iff `0 < |a|, |c| < 1`, or
  `|a|, |c| > 1`, or `a = c`, or `a = conj(c)`. `bend_conj_same_side` is the "if" half of the first
  two cases. Both papers rest on Kuiper and Robbin, Invent. Math. 19 (1973) 83–106; Budnytska's proof
  also uses her Proposition 2.1, "a conclusion of the results of Kuiper and Robbin, Cappell and
  Shaneson". Both are cited here only as cited by them.
- J. Milnor, "Dynamics in one complex variable: introductory lectures", arXiv:math/9201272. § 6,
  Remark 6.3: near a repelling periodic point whose multiplier is not real, the Julia set contains
  a sequence of points converging to it whose Koenigs coordinates "lie along a logarithmic
  spiral", the curve the twist follows. § 12: Poincaré's rotation number "is well defined, and invariant under orientation
  preserving topological conjugacy". Mathlib's form is `CircleDeg1Lift.translationNumber` with
  `CircleDeg1Lift.translationNumber_conj_eq`, for lifts of orientation-preserving circle maps.
  Complex conjugation, the map in `bendConjIso`, reverses orientation, so those statements do not
  cover it.
- The negative controls of § V concern an isomorphism without continuity, so they are not
  consequences of the classification; their proofs use a fixed point and the orders of the half and quarter turns.
- Corpus: `lmScale`, `lmIsoOfConj`, `lm_onePointInv_conj_scale`
  (`ZeroParadox/Multihomed/LimitMotion.lean`), `th3_AD_no_upLax_of_proj_ne`
  (`ZeroParadox/Multihomed/TH3Die.lean`), `Motion.StrictIso` (`ZeroParadox/Die.lean`). Mathlib:
  `Submodule.starProjection_singleton`, `Homeomorph.onePointCongr`, `Complex.conjLIE`,
  `Complex.arg_mul_coe_angle`, `isFixedPt_of_tendsto_iterate`.
- Search, 2026-11-19 (theoremsearch, informal and formal; LeanExplore, six phrasings; GitHub
  `extension:lean`; the open web): no topological-conjugacy classification of linear maps and no
  loxodromic or elliptic classification of Möbius maps was located in Mathlib as of that date; the
  null is uninformative.
