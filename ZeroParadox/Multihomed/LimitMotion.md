# LimitMotion — the limit retraction as a die motion

Ride-along companion to `ZeroParadox/Multihomed/LimitMotion.lean`. Experimental probe in the
bottom-diagram mapping campaign, **not a finalized layer**. Curated results are indexed in
`ZeroParadox/MANIFEST.md` and `ZeroParadox/DieCannotBe.lean` § XXXV.

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
  for the scaling `lmScale c`, adjoining `∞` adds no OVER step into it from a point of `K`
  (`lm_not_arrives_infty`). So for a scaling, an orbit starting in `K` and tending to `∞` is in the
  closure branch. The lemma is about scalings only.
- § III. A homeomorphism conjugating two maps is a strict isomorphism of their limit motions
  (`lmIsoOfConj`). On `OnePoint K`, `onePointInv` conjugates scaling by `c` to scaling by `d`,
  `c * d = 1` (`lmHealedIso`); it exchanges the two distinct points `0` and `∞`. Inside `K`, field
  inversion is a strict isomorphism of the bare function motions when `c * d = 1` (`lmBareInvIso`).
  When `c ^ n` tends to `0` and `1 < ‖d‖`, it is no strict map of the limit motions
  (`lm_torn_no_hom`).
- § IV. Instances, each for a start `x ≠ 0` of the field: doubling on `OnePoint ℚ_[2]` closes at `0`
  without arriving (`lm_q2_doubling_closure_at_zero`); halving there tends to `∞` without arriving
  (`lm_q2_halving_to_infty`); doubling on `OnePoint ℝ` tends to `∞` and closes there without arriving
  (`lm_real_doubling_closure_at_infty`). The torn pairs are `lm_q2_torn` and `lm_real_torn`. The
  oscillating orbit of `1` under scaling by `-1` is the control on both carriers.
- § V. The reverse direction. In `Ordinal`'s order topology (Mathlib), `ordinalTowerMotion` is the
  limit motion of `α ↦ ω^α`, so § II's iff applies to it (the first `example` of § V). The stages of
  the ω-tower seeded at 0, ⊥ of `Ordinal`, have a stage closure with UP value ε₀
  (`ordinalTowerMotion_stageClosure`), § II's closure branch. In `ℤ_[2]` the same tower's images
  start at ℤ_[2]'s 0, differ from it from stage 1 on, and approach that same 0 (`snap_arc_z2_loop`).
- § VI. The dipole. `lmSinkOf M p q`: every point other than `q` has UP-value `p`. `lmDipole M N p q`:
  `p ≠ q`, `p` is a limit sink of `M` off `q`, `q` one of `N` off `p`, and `N`'s OVER is `M`'s
  reversed. On `OnePoint ℚ_[2]`, doubling and halving form one with poles `0` and `∞`
  (`lm_q2_dipole`); halving's half is transported along `lmHealedIso` (`lmSinkOf.map`). On OVER both
  poles step only to themselves (`lm_dbl_step_level`); `Motion.reverse` keeps UP, so it is not the
  partner (`lm_reverse_not_partner`). Controls: doubling on `OnePoint ℝ` is a dipole with the poles
  exchanged (`lm_real_dipole`, `lm_real_dbl_zero_not_sink`), and the identity has no limit sink
  (`lm_id_no_sink`).

No statement here uses a join or the covering relation `⋖`. So none carries T-SNAP's join shape
(`t_snap_given`, `ZeroParadox/Order/Snap.lean`) or a covering step `⊥ ⋖ a` off ⊥ of a
`ZPSemilattice`, in ZP-A's induced order. T-SNAP's statements take that step as the commitment
`hcov` of `t_snap_given_cover`; it is AX-B1's form (`BotHasFirstStep`, hypothesis `hR1` of
`snap_of_firstStep_MLRandom`), and in `MachinePhase` it is proved (`t_snap_derived_cover`). On all
of `Ordinal`, ⊥ ⋖ ε₀ is false (`ZeroParadox/Order/SnapCannotBe.lean` § II).

## Prior art and credit

This file is a variant of the limit-retraction programme, with weaker hypotheses and weaker
conclusions. Its UP leg is the limit retraction (Abate–Bedford) restricted to convergent orbits, the
case Venturini's Theorem 5.1 (viii) describes.

- M. Abate, "Iteration theory, compactly divergent sequences and commuting holomorphic maps",
  Ann. Sc. Norm. Sup. Pisa Cl. Sci. (4) 18 (1991), no. 2, 167–191. Theorem 0.3, p. 169, credited
  there to Bedford and to Abate: for a (connected) taut manifold and a map whose iterates are not
  compactly divergent, a holomorphic retraction onto the limit manifold; p. 169 names it the limit
  retraction, and the iterates converge iff `f` is the identity on that manifold. That retraction is
  defined on orbits that do not converge, too; `limitRetraction` is not.
- R. Venturini, "On the orbits of not expansive mappings in metric spaces", arXiv:1304.1023.
  Theorem 5.1 (pp. 13–14), item (viii): for `x, y` off the compactly divergent set,
  `lim f^k(x) = y` iff `y = ρ(x)` and `f(y) = y`. pp. 18–19 define the limit retraction and the
  extended limit retraction `ρ̂ : X → X̂` into the Alexandroff compactification; Theorem 5.2
  (p. 19). He assumes `f` non-expansive on a locally compact metric space with countable basis, and
  does not extend `f` to the added point; here `lmScale` is extended and fixes `∞`.
- J. Milnor, Dynamics lecture notes, § 5 "Attraction and Repulsion" (2001), § 5A: the basin `B(A)`
  of a closed set `A`. The domain of `limitRetraction g` is the union over points `p` of the basins
  `B({p})`. p. 5-9: `∞` as an attractor on `ℂ ∪ ∞`. Conjugacy invariance of basins is that section's
  framing; `lmIsoOfConj` proves the die form.
- Compare Séré's retraction onto `Fix(T)` (Theorem 17 of Fournais, Lewin and Triay,
  arXiv:1911.09482, p. 24), in a Banach setting.

The delta, stated plainly: any continuous map of a Hausdorff space, a partial map, no metric; and
only the convergent orbits, with no group of limit maps. Only the die packaging is new: the
arrival-or-closure iff and the healed/torn contrast. The split into "eventually fixed" and "never
fixed" orbits is folklore; it was searched 2026-11-19 (theoremsearch, three phrasings, one formal;
LeanExplore, three phrasings; the open web, two queries) and not located as a named theorem.

Mathlib, searched 2026-11-19 (LeanExplore, three phrasings; theoremsearch, one formal phrasing):
`isFixedPt_of_tendsto_iterate`, `omegaLimit`, `mem_omegaLimit_singleton_iff_mapClusterPt`,
`tendsto_nhds_of_unique_mapClusterPt`. No limit-retraction or basin declaration was located as of
that date; the null is uninformative.

A bound on the other side of § V is cited, not claimed, in the Lean file's closing `Reading:`:
Escardó, preprint of JSL 78(3) (2013), § 11, p. 19, "it is not possible to embed ε₀ in 2^ℕ using
limit structures" (also quoted in `ZeroParadox/DieCannotBe.lean`).

`Reading:` § VI's `lmDipole` is north–south dynamics, read on the UP leg of two limit motions.
H. Masai, "A horofunction counterpart to Teichmüller distance", arXiv:2512.23249 (v1), Definition
3.10: for a group acting continuously on a compact set `X`, an element `g` has north–south dynamics
if it has two fixed points `x+ ≠ x−` with `gⁿ(x) → x+` for every `x ≠ x−` and `g⁻ⁿ(x) → x−` for every
`x ≠ x+`. That is the pointwise form; `lmDipole`, with `M` the limit motion of `g` and `N` that of
`g⁻¹`, has its shape. A. Lonjou, P. Przytycki and C. Urech, "Finitely generated subgroups of
algebraic elements of plane Cremona groups are bounded", arXiv:2307.01334 (v2), Definition 4.8, give
the uniform form: a homeomorphism `a` of a Hausdorff space `P` fixing `p` and `q`, such that for any
disjoint open `U ∋ p` and `V ∋ q` there is `n` with `aⁿ(P ∖ V) ⊂ U` and `a⁻ⁿ(P ∖ U) ⊂ V`. No
statement in § VI is the uniform form. Mathlib, searched 2026-11-22: a case-insensitive grep of the
pinned `Mathlib/Dynamics` for `attractor`, `repeller`, `attracting`, `repelling`, `north-south` (any
separator), `basin`, `sink` and `source`, and of all of the pinned `Mathlib` for `north-south`,
`attractor` and `repeller`. No attractor, repeller or north–south notion was located as of
2026-11-22.
