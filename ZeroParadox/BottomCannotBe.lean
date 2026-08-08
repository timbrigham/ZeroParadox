import ZeroParadox.Multihomed.TreeObstructions
import ZeroParadox.Order.MarkovPlacement
import ZeroParadox.Multihomed.RootCutObstruction
import ZeroParadox.Multihomed.WallSpanRobust
import ZeroParadox.Computability.MarkovNuUniversal
import ZeroParadox.Order.WellFoundedObstruct
import ZeroParadox.Valuation.NuRateEdge
import ZeroParadox.Category.SeamNotColimit
import ZeroParadox.Multihomed.FloorFactsCooccur
import ZeroParadox.Multihomed.TwoFacesBot
import ZeroParadox.Category.SeamUniqueness
import ZeroParadox.Category.RootCutDegeneracy
import ZeroParadox.Valuation.ContractionRate
import ZeroParadox.Category.RootCutBinary
import ZeroParadox.Multihomed.SeamConnectorFail
import ZeroParadox.Order.MarkovContractionDual
import ZeroParadox.Order.SeamSchema
import ZeroParadox.Valuation.NuRateMatch
import ZeroParadox.Computability.RootCutTrichotomy
import ZeroParadox.Computability.ChoicePurityInvariant
import ZeroParadox.Computability.NatListRegime
import ZeroParadox.Computability.SelfApp
import ZeroParadox.Multihomed.SelfAppForkPlace
import ZeroParadox.Multihomed.SelfAppSeam
import ZeroParadox.Settheory.Wall
import ZeroParadox.Order.Snap
import ZeroParadox.Multihomed.InfoFunctor
import ZeroParadox.Valuation.PadicAttractor
import ZeroParadox.Information.Surprisal
import ZeroParadox.Information.BottomMeasure
import ZeroParadox.Valuation.TopFunctor
import ZeroParadox.Computability.Kleene
import ZeroParadox.Ordinal.Incompleteness
import ZeroParadox.Ordinal.Gentzen
import ZeroParadox.Valuation.InversionValuation
import ZeroParadox.Valuation.PlaceMetric
import ZeroParadox.Category.Category
import ZeroParadox.Valuation.FloorWitness
import ZeroParadox.Ordinal.ProofFloorCanonical
import ZeroParadox.Valuation.RiemannSphere
import ZeroParadox.Multihomed.HilbertDiagonal
import ZeroParadox.Reals.MarkovSpectralGap
import Mathlib.Order.FixedPoints

/-!
# Index of proved results characterizing ⊥

`#check`-only: no declarations, nothing new proved. Each line names one existing result and says
what it establishes; the imports force every indexed theorem to compile, so no line can point at a
dead name. `Statement:` restates what a declaration proves; `Reading:` is interpretation and is not
a claim about the theorem. Sections run: what ⊥ cannot be, what it must be, how it is approached and
departed. Schema and corpus sweep: `.claude-local/notes/bottom_object_harvest_catalog_2026-06-30.md`.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.
-/

section CannotBeIndex

/-! ### ⊥-interpretations do not unify across the μ/ν root -/

-- Statement: no strictly monotone map ℝ → Ordinal exists.
-- Reading: supporting infrastructure, not a ⊥-exclusion on its own.
#check @ZeroParadox.no_strictMono_real_to_ordinal
-- Statement: `<` on ℝ is not well-founded.
#check @ZeroParadox.real_carrier_not_wellFounded
-- Statement: on the standard simplex, `p ≤ q` forces `p = q` — it is an antichain.
#check @ZeroParadox.simplex_antichain
-- Statement: `{0} ⊆ ℚ₂` as a `TopCat` object admits no initial-object structure.
#check @ZeroParadox.padic_bottom_not_initial
-- Statement: both the Kleisli and Hilbert floors are initial, and `Fin 0 ≃ StateSpace 0` is empty.
#check @ZeroParadox.split_kleisli_vs_hilbert
-- Statement: the Kleisli floor is initial, and `Fin 0 ≃ {0} ⊆ ℚ₂` is empty.
#check @ZeroParadox.split_kleisli_vs_padic
-- Statement: `Cofix → Fix` is empty for the identity polynomial functor.
#check @ZeroParadox.root_cut_no_map_nu_to_mu
-- Statement: that emptiness, plus `Fix → Cofix` being a subsingleton — asymmetric in both directions.
#check @ZeroParadox.root_cut_strict_asymmetric

/-! ### ⊥ cannot be reached by a structure-preserving (descending/ν) comparison -/

-- Statement: if `r` is not well-founded, no `f : S → Ordinal` is strictly increasing along `r`.
#check @ZeroParadox.no_faithful_span_to_ordinal_and_descending
-- Statement: the converse biconditional — such an `f` exists iff `r` is well-founded.
#check @ZeroParadox.faithful_iff_descending

-- Statement: the equivalences `{x // selfApp x = x} ≃ PUnit` form a subsingleton.
-- Reading: POSITIVE and indexed as support, not as an exclusion — it says the two faces coincide as
-- a bare point, which is what the interpretation-layer exclusion rests on.
#check @ZeroParadox.faces_iso_unique

/-! ### the Markov interpretation cannot be a single ordered or unique point -/

-- Statement: some stationary distribution is neither least nor greatest in the simplex.
#check @ZeroParadox.stationary_attractor_no_order_placement
-- Statement: a doubly-stochastic `Fin 4` chain exists whose stationary distribution is not unique.
#check @ZeroParadox.markov_node_no_universal_property
-- Statement: so stationarity under doubly-stochastic chains is not subsingleton-valued in general.
#check @ZeroParadox.doublyStochastic_stationary_not_subsingleton

/-! ### the p-adic floor cannot be reached from within, nor matched to the Markov rate -/

-- Statement: for `x ≠ 0` in ℚ₂, `2ⁿ * x ≠ 0` at every finite `n` — the orbit never lands on 0.
#check @ZeroParadox.padic_orbit_never_reaches_zero
-- Statement: no reindexing `φ : ℕ → ℕ` matches the p-adic rate to the Markov rate at every step.
#check @ZeroParadox.no_rate_conjugacy
-- Statement: indeed no single pair of indices makes the two rates agree.
#check @ZeroParadox.no_rate_orderIso

/-! ### categorical floor and seam exclusions -/

-- Statement: `fD_functor.obj 1` is not a zero object.
#check @ZeroParadox.leaf_not_isZero
-- Statement: `(0 : ℕ)` admits no terminal-object structure.
#check @ZeroParadox.nat_zero_not_terminal
-- Statement: the Kleisli floor `fC_functor.obj 0` is not a zero object.
#check @ZeroParadox.kleisli_bottom_not_zero
-- Statement: `{0} ⊆ ℚ₂` as a `TopCat` object is not a zero object.
#check @ZeroParadox.padic_bottom_not_zero
-- Statement: given no top, `bot ≤ x` for all `x` while `x ≤ bot` fails for some — least, not greatest.
#check @ZeroParadox.zpa_bot_not_greatest

/-! ### μ/ν fork: the least fixed point is empty, or does not match the greatest -/

-- Statement: `Fix ≃ Cofix` is empty for the identity polynomial functor.
#check @ZeroParadox.idPF_no_seam
-- Statement: and for the binary one.
#check @ZeroParadox.binPF_no_seam
-- Statement: the `W`-type of the trichotomy functor is empty.
#check @ZeroParadox.strict_fix_isEmpty
-- Statement: `Fix idPF_Coalgebra.Obj` is empty, proved choice-free (a tighter axiom footprint).
#check @ZeroParadox.fix_isEmpty_constructive
-- Statement: `fixToCofix` is not surjective.
#check @ZeroParadox.fixToCofix_not_surjective

/-! ### orbits that cannot reach ⊥, or cannot be matched -/

-- Statement: for `‖u‖ = 1` and `x ≠ 0`, the orbit `uⁿ * x` does not converge to 0.
#check @ZeroParadox.unit_orbit_not_tendsto_zero
-- Statement: the swap chain's orbit from `e0vec` converges to no limit.
#check @ZeroParadox.swap_orbit_not_convergent
-- Statement: the p-adic orbit stays norm-positive while the Markov orbit stays balanced — no match.
#check @ZeroParadox.padic_markov_no_orbit_correspondence

/-! ### the seam and floor cannot be transported or cross-connected -/

-- Statement: the Hilbert floor is a zero object while the p-adic floor admits no initial structure.
#check @ZeroParadox.seam_role_not_transported
-- Statement: no binary cofan with apex `fD_functor.obj 0` is a colimit.
#check @ZeroParadox.seam_not_mu_colimit_apex
-- Statement: the QPF seam is a canonical bijection, and the recursive `idPF` `Fix` is empty.
-- Reading: this records that no cross-setting map was EXHIBITED. It is not a proof of impossibility
-- (`IsEmpty` of the map type); an open "none given", not a no-go. See register D8.
#check @ZeroParadox.no_cross_setting_map
-- Statement: `(1 : ℕ) ⟶ (0 : ℕ)` is empty.
#check @ZeroParadox.isEmpty_hom_one_to_zero
-- Statement: in a `ZPCategory`, an object not isomorphic to the initial admits no map into it.
#check @ZeroParadox.t3_unreachability
-- Statement: rose trees over a partially-well-ordered relation are partially well ordered.
-- Reading: a SCOPE FENCE, marking where the "canonical floor 0" claim does not apply — Kruskal's
-- theorem gives a well-quasi-order, not a descent to a bottom.
#check @ZeroParadox.kruskal_is_wqo_not_descent

/-! ### POSITIVE — ⊥ as the fixed point where operation and result coincide -/

-- Statement: a FIELD of the `AbstractSelfApp` class asserting a unique fixed point — assumed of the
-- action, not derived.
-- Reading: the framework calls this coincidence of input and output "concurrency".
#check @ZeroParadox.AbstractSelfApp.unique_fp
-- Statement: `bot` is a fixed point of `selfApp`, and is both below and above every fixed point.
#check @ZeroParadox.selfApp_fixed_point_is_seam
-- Statement: every `selfApp` fixed point is both `≥ bot` and `≤ bot` — least and greatest at once.
#check @ZeroParadox.selfApp_bot_is_both_extremal
-- Statement: `¬(p ↔ ¬p)` — logical negation has no fixed point.
-- Reading: the contrast that makes the coincidence above meaningful; this is the fixed-point-free
-- map at the diagonal (Lawvere). ⚠ Do NOT read it as "involutions have no fixed point" — most do,
-- e.g. `x ↦ -x` fixes 0. The claim is about logical `Not` specifically.
#check @ZeroParadox.negation_no_fixedpoint

/-! ### POSITIVE — narrow uniqueness and infinite width, which coincide only at ⊥ -/

-- Statement: in ℚ₂, `q2SelfMem x` forces `x = 0` — one uniquely pinned point. [NARROW]
#check @ZeroParadox.q2_unique_fp
-- Statement: the intersection of the nested balls is exactly `{0}`. [NARROW]
#check @ZeroParadox.fB_bottom_is_limit
-- Statement: the partial sums exceed every bound `M`. [WIDE, infinite measure]
#check @ZeroParadox.t2_diverges
-- Statement: the same divergence in the `BottomMeasure` framing; this is `l_inf`. [WIDE, measure]
#check @ZeroParadox.info_bottom_diverges
-- Statement: for `‖c‖ < 1`, every orbit `cⁿ * x` converges to 0. [WIDE, infinite reach]
#check @ZeroParadox.contraction_orbit_tendsto_zero
-- Reading: narrow and reach hold of the SAME point 0 in ℚ₂ — `q2_unique_fp`'s unique point is
-- `contraction_orbit_tendsto_zero`'s limit. That pairing is the framework's 0=∞ signature. It is a
-- criterion, not a theorem, and the measure aspect lives in a different construction (ZPC), so the
-- three are assembled across carriers rather than proved of one.

-- Statement: `(∀ x, join S x = x) ↔ S = bot` — exactly one element plays the ⊥ role. [NARROW]
#check @ZeroParadox.da2_bottom_characterization
-- Statement: the initial object maps to every object by exactly one morphism. [NARROW]
#check @ZeroParadox.t2_universal_constituent
-- Statement: in any additively-valued ring, `v 0 = ⊤`. [WIDE, measure; subsumes the p-adic case]
#check @ZeroParadox.addVal_bot
-- Statement: the ε₀-tower encodings converge to 0 in ℚ₂. [WIDE, reach]
#check @ZeroParadox.tower_converges_to_zero

/-! ### INVERSION — the symmetry linking the narrow and wide poles -/

-- Statement: `(·⁻¹)` maps `{x ≠ 0 ∣ n ≤ v₂ x}` onto `{x ≠ 0 ∣ v₂ x ≤ -n}`.
-- Reading: the inversion symmetry of the tower. ⚠ It is ℤ-valued and carries NO literal 0=∞
-- content — 0 is the excluded centre, and the source file disclaims that reading.
#check @ZeroParadox.inversion_reverses_filtration
-- Statement: one orbit `2ⁿx` converges to 0 in ℚ₂ AND diverges to ∞ in ℝ.
-- Reading: this is where the literal 0=∞ content lives — one orbit, two place-views.
#check @ZeroParadox.doubling_place_dichotomy
-- Statement: `rInvHomeo` sends `0` to `∞` and `∞` to `0` on `OnePoint ℚ₂`.
#check @ZeroParadox.rInv_swaps
-- Statement: that inversion is a homeomorphism of the sphere.
#check @ZeroParadox.rInvHomeo
-- Statement: Mathlib's `IsInitial.op` — the opposite of an initial object is terminal.
-- Reading: CITED, not ZP-proved; attribution is the point. Passing to `Cᵒᵖ` is the categorical face
-- of inversion, swapping the μ-bottom to a terminal object.
#check @CategoryTheory.Limits.IsInitial.op
-- Statement: Mathlib's `hasZeroObject_op` — a zero object stays a zero object in the opposite.
-- Reading: the seam is self-dual under `op`, the fixed centre of the inversion.
#check @CategoryTheory.Limits.hasZeroObject_op
-- Reading: PRIOR-ART RECORD, do NOT rebuild. The abstract "order-reversal swaps ⊥ and ⊤" is already
-- Mathlib's (`compl_bot`/`compl_top`, `OrderIso.compl`, `setOfMinimalIsoSetOfMaximal`). The three
-- inversions share no single buildable type, so their "unification" is a schema, not a theorem.
-- See `.claude-local/notes/inv_cop_prior_art_2026-06-30.md`.

/-! ### SELF-REFERENCE — the diagonal fixed point -/

-- Statement: under `[KleeneStructure]`, any Quine atom `q` satisfies `q = bot`. The statement has no
-- Kleene clause; the quine-atom property is class-supplied, like `unique_fp`.
-- Reading: the self-EXECUTING reading is the framework's, carried by the class commitment rather
-- than by this theorem. See ZP-K § II and § III.
#check @ZeroParadox.kleene_quine_is_bot
-- Statement: some code `c` is a computational quine.
#check @ZeroParadox.computational_quine_exists
-- Statement: `eval c n = eval c (encode c + n)` — the Gödel number is *a* period of the evaluation.
-- Reading: ⚠ not *the* period. It is not shown least, and a constant code is periodic with every
-- period, so this does not tie index to function. A periodicity fact, not a diagonal identity.
#check @ZeroParadox.quine_period_is_goedel
-- Statement: a Kleene-periodic code exists AND a least ordinal with `ω^α = α` exists.
-- Reading: the two diagonalization fixed points coexist; the conjunction is not an identification.
#check @ZeroParadox.both_fixed_points_exist
-- Statement: a finite-dimensional `X` with `X ≅ X ⊞ X` is the zero object.
-- Reading: the OTHER sub-sense of self — self-similarity under the biproduct diagonal, as opposed to
-- the Kleene sense of a code applied to its own index. The finiteness hypothesis is load-bearing.
#check @ZeroParadox.biprod_diagonal_only_zero
-- Statement: the seam satisfies `seam ≅ seam ⊞ seam` and is a zero object.
#check @ZeroParadox.seam_is_diagonal_fixpoint

/-! ### GENERATION — the floor generates the ceiling -/

-- Statement: `epsilonZero = nfp (ω^·) 0` — ε₀ is the closure of 0 under `ω^·`.
#check @ZeroParadox.epsilonZero_eq_nfp
-- Statement: `ω^b = b → epsilonZero ≤ b` — ε₀ is the least such fixed point.
#check @ZeroParadox.epsilonZero_le_fixedPoint
-- Statement: Mathlib's Kleene fixed-point theorem, `lfp f = ⨆ₙ fⁿ(⊥)`.
-- Reading: CITED prior art for generation, do NOT rebuild. `ε₀ = nfp (ω^·) 0` is the ordinal
-- instance of generating a least fixed point from the floor by iteration.
#check @fixedPoints.lfp_eq_sSup_iterate
-- Reading: generation pairs with the μ side (build up from ⊥) and its dual is reach on the ν side
-- (flow down to ⊥). So generation being absent on the ν-bottoms is the μ/ν fork, not a gap — they
-- carry reach instead. One instance is built choice-free (`node4_generates_nat`); Adámek's general
-- initial-algebra colimit is not cheaply available in Mathlib and remains open.

/-! ### DYNAMICS — how ⊥ is approached and departed -/

-- Statement: `c₀ ≠ c₁` and `join c₀ c₁ = c₁` — the state advance off the floor.
#check @ZeroParadox.t_snap_derived
-- Statement: for `x ≼ y` with `x ≠ y`, no join returns `y` to `x`.
-- Reading: a GENERIC semilattice no-return lemma. It mentions neither ⊥ nor the snap; the snap
-- instantiates it. The arrow-of-time reading is the application, not the statement.
#check @ZeroParadox.t_snap_irreversible
-- Statement: for `0 < n`, `fC_functor.obj n ⟶ fC_functor.obj 0` is empty.
#check @ZeroParadox.fC_no_return
-- Statement: the predecessor orbit from any `n` reaches the floor in finitely many steps. [μ]
#check @ZeroParadox.pred_orbit_reaches_floor
-- Statement: the doubling orbit converges to 0 in the 2-adic metric. [ν]
#check @ZeroParadox.doubling_orbit_tendsto_zero
-- Statement: given `⊥ ⟶ X`, the hom `X ⟶ ⊥` is still empty.
-- Reading: definitionally `t3_unreachability` — the same no-incoming fact under the irreversibility
-- reading rather than the unreachability one. Not new content.
#check @ZeroParadox.t4_chains_forward_only
-- Statement: the relaxation operator of `fullMix` is not injective.
-- Reading: information is lost, so the relaxation cannot be reversed. ⚠ FENCE: mixing-specific, NOT
-- universal — permutation chains have no spectral gap and do not mix (`swap_orbit_not_convergent`).
#check @ZeroParadox.fullMix_not_injective
-- Statement: an eigenmode with `|λ| < 1` has `‖(T f)^[m] v‖ → 0`.
#check @ZeroParadox.tendsto_norm_iterate_zero

end CannotBeIndex
