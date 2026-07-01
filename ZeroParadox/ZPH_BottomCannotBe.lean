import ZeroParadox.ZPH_MC1_TreeObstructions
import ZeroParadox.ZPH_MC1_TC16
import ZeroParadox.ZPH_MC1_TC21
import ZeroParadox.ZPH_MC1_TC22
import ZeroParadox.ZPH_MC1_TC23
import ZeroParadox.ZPH_MC1_TC28
import ZeroParadox.ZPH_MC1_TC33
import ZeroParadox.ZPH_MC1_TC40
import ZeroParadox.ZPH_MC1_TC44
import ZeroParadox.ZPH_TwoFacesBot
import ZeroParadox.ZPH_MC1_TC08
import ZeroParadox.ZPH_MC1_TC26
import ZeroParadox.ZPH_MC1_TC30
import ZeroParadox.ZPH_MC1_TC32
import ZeroParadox.ZPH_MC1_TC34
import ZeroParadox.ZPH_MC1_TC39
import ZeroParadox.ZPH_MC1_TC40
import ZeroParadox.ZPH_MC1_TC42
import ZeroParadox.ZPH_MC1_TC45
import ZeroParadox.ZPH_MC1_TC47
import ZeroParadox.ZPH_MC1_TC48
import ZeroParadox.ZPH_MC1_TC49
import ZeroParadox.ZPJ_SelfApp
import ZeroParadox.ZPH_MC1_TC11
import ZeroParadox.ZPH_MC1_TC15
import ZeroParadox.ZPP_Wall
import ZeroParadox.ZPE
import ZeroParadox.ZPH_InfoFunctor
import ZeroParadox.ZPH_MC1_TC05
import ZeroParadox.ZPC
import ZeroParadox.ZPH_BottomMeasure
import ZeroParadox.ZPH_TopFunctor
import ZeroParadox.ZPK
import ZeroParadox.ZPM
import ZeroParadox.ZPL
import ZeroParadox.ZPP_InversionValuation
import ZeroParadox.ZPH_PlaceMetric
import ZeroParadox.ZPG
import ZeroParadox.ZPB_FloorWitness
import ZeroParadox.ZPH_MC1_TC07
import ZeroParadox.ZPP_RiemannSphere
import ZeroParadox.ZPH_HilbertDiagonal
import ZeroParadox.ZPH_MarkovSpectralGap
import Mathlib.Order.FixedPoints

/-!
# Machine-checked verification index of results characterizing ⊥ (the bottom element)

A `#check`-only index of established results characterizing ⊥, organized by a classification schema. The
negative half — what ⊥ provably *cannot* be — is a characterization by exclusion; within this project the
shorthand for that register is "apophatic" (via-negativa). The positive half records what ⊥ *is* (its
relational/universal roles). No new claims are made here; see the Formal Overview below.

## Engineer's Take

This file is one of a series of iterative attempts on this branch to build a map of how the various
bottoms interconnect, and by extension how bottom moves from being the floor, a thing (a noun), to a
verb (an action). The Lean here is our attempt, one way or the other, to get a clean verification. I
defer to my AI assistant regarding the specifics of how the internals work.

---

## Formal Overview (AI-assisted)

This is the **⊥-characterization object** — ⊥ pinned from several sides, in three parts. (Honest shape: it
is ASYMMETRIC — a rich CANNOT-HAVE side and a more modest MUST-BE side, plus DYNAMICS roles. Every positive
handle is universal/relational; structurelessness forbids intrinsic-structure handles. Said plainly so the
framing doesn't oversell.)
  • **CANNOT-HAVE** (apophatic / negative) — what ⊥ is *not*; the bulk, the register
    `.claude-local/notes/bottom_cannot_be.md`.
  • **MUST-BE** (cataphatic / positive) — what ⊥ *is*, in two poles that coincide only at ⊥:
    **NARROW** (uniqueness — THE single pinned point) and **WIDE** (infinite width, in two aspects —
    infinite *measure*: a value diverges *at* ⊥; infinite *reach*: ⊥ is the universal attractor); they
    meet at the **concurrency**/fixed-point. "Narrow focus + infinite width" — the 0=∞ pole. Each entry is
    Lean-anchored, but ASSEMBLED ACROSS CONSTRUCTIONS (narrow + reach in ℚ₂; measure in the ZPC surprisal
    domain) — not one carrier. The coincidence-is-the-signature is the criterion (definitional), not one
    theorem.
  • **DYNAMICS** (state-change / time) — how ⊥ is approached (orbits/descent reach it) and departed (the
    snap, irreversibly).
A 2026-06-30 corpus sweep (catalogued in `.claude-local/notes/bottom_object_harvest_catalog_2026-06-30.md`)
confirmed these slots absorb ~60 ⊥-theorems across every layer (categorical, computability, ordinal,
p-adic, Markov) — the structure recurs corpus-wide — and surfaced two further positive slots:
  • **SELF-REFERENCE / diagonal** — ⊥ is the self-referential (Quine/Kleene) fixed point, beyond a bare
    fixed point; the diagonal-fixed-point keystone.
  • **GENERATION / Gödel-inversion** — the floor GENERATES the ceiling (ε₀ = closure of 0 under ω^·).
plus **INVERSION** (z↦1/z) linking the narrow and wide poles (the 0=∞ Riemann pole). The index is curated,
not exhaustive — the catalog holds the backlog; gaps are filled incrementally, each with a cold review.
(Filename is historical — it began as the cannot-be index; it is now the full object.) It does NOT define
or prove anything new
— **it is deliberately an index.** Each line `#check`s one already-proven exclusion theorem (a `¬`,
`IsEmpty`, antichain, or no-go). Because the `import`s force the home files to compile, **building this
file recompiles every indexed theorem's proof and confirms its name+type resolve** — so the register
cannot point to a dead or renamed theorem. (`#check` alone resolves name+type; the proof is certified by
the imports, not by `#check`. Same discipline as the positive register `claim_map.md`.)

Honest status: a `#check`-only index creates no declarations and therefore *structurally cannot overclaim*
⊥'s nature — which is exactly the point of the apophatic approach (a negative can't assert ⊥ *is*
anything). The `meta` entries of the register (A1–A4: descriptionlessness etc.) have no Lean witness by
their nature and are not indexed here. New exclusions are proved in their own files and added below.
-/

section CannotBeIndex

/-! ### ⊥-interpretations do not unify across the μ/ν root (cross-domain walls) -/
#check @ZeroParadox.ZPH_MC1_TreeObstructions.no_strictMono_real_to_ordinal
-- (supporting infra, not a ⊥-exclusion on its own — a generic fact about ℝ that powers the line above)
#check @ZeroParadox.ZPH_MC1_TreeObstructions.real_carrier_not_wellFounded
#check @ZeroParadox.ZPH_MC1_TreeObstructions.simplex_antichain
#check @ZeroParadox.ZPH_MC1_TreeObstructions.padic_bottom_not_initial
#check @ZeroParadox.ZPH_MC1_TreeObstructions.split_kleisli_vs_hilbert
#check @ZeroParadox.ZPH_MC1_TreeObstructions.split_kleisli_vs_padic
#check @ZeroParadox.ZPH_MC1_TC21.root_cut_no_map_nu_to_mu
#check @ZeroParadox.ZPH_MC1_TC21.root_cut_strict_asymmetric

/-! ### ⊥ cannot be reached by a structure-preserving (descending/ν) comparison -/
#check @ZeroParadox.ZPH_MC1_TC22.no_faithful_span_to_ordinal_and_descending
#check @ZeroParadox.ZPH_MC1_TC22.faithful_iff_descending

/-! ### the two faces: `faces_iso_unique` is POSITIVE (they coincide as a bare point, uniquely) — it
    supports the *interpretation-layer* exclusion (no STRUCTURE-respecting unification) via the
    structure-respecting caveat, it is NOT itself a no-go. Indexed honestly as support, not an exclusion. -/
#check @ZeroParadox.ZPH_TwoFacesBot.faces_iso_unique

/-! ### the Markov interpretation (#2) cannot be a single ordered/unique point in general -/
#check @ZeroParadox.ZPH_MC1_TC16.stationary_attractor_no_order_placement
#check @ZeroParadox.ZPH_MC1_TC23.markov_node_no_universal_property
#check @ZeroParadox.ZPH_MC1_TC23.doublyStochastic_stationary_not_subsingleton

/-! ### the p-adic floor cannot be reached from within / matched to the Markov rate -/
#check @ZeroParadox.ZPH_MC1_TC28.padic_orbit_never_reaches_zero
#check @ZeroParadox.ZPH_MC1_TC33.no_rate_conjugacy
#check @ZeroParadox.ZPH_MC1_TC33.no_rate_orderIso

/-! ### categorical floor/seam exclusions -/
#check @ZeroParadox.ZPH_MC1_TC40.leaf_not_isZero
#check @ZeroParadox.ZPH_MC1_TC44.tc44_nat_floor_not_isTerminal

/-! ### the bottoms cannot be zero objects / greatest elements (various categories) -/
#check @ZeroParadox.ZPH_MC1_TC08.kleisli_bottom_not_zero
#check @ZeroParadox.ZPH_MC1_TC08.padic_bottom_not_zero
#check @ZeroParadox.ZPH_MC1_TC08.zpa_bot_not_greatest

/-! ### μ/ν fork: the least-fixed-point (Fix) is EMPTY / does not match the greatest (no seam) -/
#check @ZeroParadox.ZPH.TC26.idPF_no_seam
#check @ZeroParadox.ZPH.TC32.binPF_no_seam
#check @ZeroParadox.ZPH_MC1_TC47.strict_fix_isEmpty
#check @ZeroParadox.ZPH.TC48.fix_isEmpty_constructive   -- choice-free (note: tighter purity)
#check @ZeroParadox.ZPH_MC1_TC49.fixToCofix_not_surjective

/-! ### orbits that cannot reach ⊥ / cannot be matched (only contractions reach it) -/
#check @ZeroParadox.ZPH_MC1_TC30.unit_orbit_not_tendsto_zero
#check @ZeroParadox.ZPH_MC1_TC39.swap_orbit_not_convergent
#check @ZeroParadox.ZPH_MC1_TC45.tc43_no_orbit_correspondence

/-! ### seam / floor cannot be transported or cross-connected -/
#check @ZeroParadox.ZPH_MC1_TC34.seam_role_not_transported
#check @ZeroParadox.ZPH_MC1_TC40.seam_not_mu_colimit_apex
-- NB: `no_cross_setting_map` records absence-of-construction (no map EXHIBITED), NOT a proven
-- impossibility (`IsEmpty (map)`). It is an OPEN-style "none given", not a NO-GO. See register D8.
#check @ZeroParadox.ZPH.TC42.no_cross_setting_map
#check @ZeroParadox.ZPH_MC1_TC44.tc44_no_hom_into_nat_floor

/-! ### cross-domain CANNOT-HAVE anchors (the exclusion recurs in other layers — corpus sweep 2026-06-30) -/
#check @ZeroParadox.ZPG.t3_unreachability   -- categorical: IsEmpty (X ⟶ ⊥) — ⊥ cannot be reached from outside.
-- SCOPE FENCE: not every well-quasi-order has an ordinal-valued floor — Kruskal's theorem is a WQO, NOT a
-- descent to a bottom. Marks where the "canonical floor 0" claim does NOT apply. (apophatic, scope-limit.)
#check @ZeroParadox.MC1.TC07.kruskal_is_wqo_not_descent

/-! ## POSITIVE side — concurrency = the fixed point (the not-action point)
    The complement to the exclusions above: ⊥'s one positive handle. "Concurrency" (operation and result
    coincide, no step between) is the fixed point `selfApp x = x`; ⊥ is its UNIQUE such point. Still
    `#check`-only — these are existing theorems, indexed, not re-proved (no re-skin). -/

-- ⊥ is the UNIQUE fixed point of the action — the concurrency point (input = output).
-- (NB: this is a FIELD of the `AbstractSelfApp` class — a structural commitment assumed of the action,
--  not a derived theorem. "Concurrency"/"not-action" is the plain-language gloss for `selfApp x = x`.)
#check @ZeroParadox.ZPJ_SelfApp.AbstractSelfApp.unique_fp
-- that concurrency point is the seam (the μ=ν coincidence).
#check @ZeroParadox.ZPH_MC1_TC11.selfApp_fixed_point_is_seam
-- least = greatest fixed point: the two extremes co-hold at the one point (a concurrency).
#check @ZeroParadox.ZPH_MC1_TC15.selfApp_bot_is_both_extremal

/-! ### the CONTRAST that makes concurrency meaningful: pure logical negation has NO fixed point —
    `¬(p ↔ ¬p)` — it is THE fixed-point-free map at the diagonal (Lawvere), whereas `selfApp`'s fixed
    point exists and is unique (⊥). (NB: do NOT read this as "involutions have no fixed point" — most do,
    e.g. `x ↦ -x` fixes 0; the claim is specifically about logical `Not`, not involutions in general.) -/
#check @ZeroParadox.ZPPWall.negation_no_fixedpoint

/-! ## POSITIVE side, the two poles — NARROW focus + INFINITE width (Tim, 2026-06-30)
    "Narrow focus and infinite width is what makes bottom bottom." Every positive handle on ⊥ is
    universal/relational (structurelessness forbids intrinsic structure), and they sort into TWO families:
      • NARROW (uniqueness / focus): ⊥ is THE single uniquely-pinned point.
      • WIDE (infinite width) — itself two distinct aspects:
          – infinite MEASURE: the value diverges *at* ⊥ (a scalar blows up);
          – infinite REACH: ⊥ is the universal attractor (everything *flows to* it).
    For an ordinary object narrow and wide never coincide (a unique point has finite reach; a divergent
    thing is not one point). ⊥ is the unique place where they are the SAME point — the 0=∞ of the Zero
    Paradox, the Riemann-sphere pole. Each entry is Lean-anchored; the *coincidence-is-the-signature* is
    the criterion (definitional/keystone), NOT a single theorem.
    HONEST DOMAIN NOTE: these are ASSEMBLED ACROSS CONSTRUCTIONS, not one object — narrow + reach live in
    ℚ₂ (the 2-adic floor 0); infinite-measure lives in the ZPC surprisal domain (a different construction).
    The "poles" are a cross-construction characterization, not facts about a single carrier. #check-only. -/

-- NARROW — uniqueness: ⊥ is THE single point (relational pinning, no intrinsic structure). [ℚ₂]
#check @ZeroParadox.ZPJ_SelfApp.q2_unique_fp        -- 0 is the UNIQUE self-membership fixed point in ℚ₂.
#check @ZeroParadox.ZPH_TopFunctor.fB_bottom_is_limit -- ⋂ nested balls = {0}: exactly one point pinned.
-- WIDE / infinite MEASURE: a scalar diverges (unbounded value), NOT "reached from everywhere". [ZPC]
#check @ZeroParadox.ZPC.t2_diverges                 -- surprisal/information exceeds every bound M.
#check @ZeroParadox.BottomMeasure.info_bottom_diverges -- = `ZPC.l_inf` (same fact, the BottomMeasure framing).
-- WIDE / infinite REACH: ⊥ is the universal attractor — every CONTRACTION orbit (‖c‖<1) flows to it. [ℚ₂]
#check @ZeroParadox.ZPH_MC1_TC30.contraction_orbit_tendsto_zero
-- COINCIDENCE (actual-⊥ core, both genuinely 0 ∈ ℚ₂): the SAME point is `q2_unique_fp` (narrow: the
-- unique fixed point) AND `contraction_orbit_tendsto_zero`'s limit (reach: the universal attractor). Not
-- one theorem — a tight Lean-anchored pairing in ONE carrier (ℚ₂), the formal shadow of narrow+reach.
-- (The infinite-MEASURE aspect is the ZPC analogue, not part of this same-carrier pairing.)

/-! ### the poles recur across layers (cross-domain anchors — corpus sweep 2026-06-30) -/
-- NARROW, framework-abstract: the ⊥-role (universal join-identity) is satisfied by EXACTLY one element.
#check @ZeroParadox.ZPE.da2_bottom_characterization   -- (∀ x, join S x = x) ↔ S = bot.
-- NARROW, categorical: ⊥ maps uniquely to every object (initial universal property).
#check @ZeroParadox.ZPG.t2_universal_constituent
-- MEASURE, fully general: in ANY additively-valued ring the floor 0 carries v 0 = ⊤ (subsumes the p-adic).
#check @ZeroParadox.FloorWitness.addVal_bot
-- REACH, ordinal domain: the ε₀-tower encodings converge to the 2-adic floor 0 (a different orbit family).
#check @ZeroParadox.ZPL.tower_converges_to_zero

/-! ### INVERSION — the symmetry suggesting the narrow/wide link (z ↦ 1/z)
    Interpretation (NOT carried by the first theorem): inversion as the formal face of the Riemann-sphere
    origin, 0 (floor) and ∞ antipodal. The LITERAL 0=∞ content lives only in the second theorem; the first
    is a finite-valued filtration reflection whose own source disclaims any 0=∞ reading. -/
-- valuation-filtration REFLECTION around the floor: `{x≠0 ∣ n ≤ v₂} ↦ {x≠0 ∣ v₂ ≤ -n}` under (·⁻¹).
-- NB: this is ℤ-valued — NO literal 0=∞ content (the source file disclaims it); 0 is the excluded center.
-- It is the inversion *symmetry* of the tower, the suggestive shadow of the pole, not the pole itself.
#check @ZeroParadox.InversionValuation.inversion_reverses_filtration
-- THE literal 0=∞: the SAME orbit 2ⁿx reaches 0 at the 2-adic place AND diverges to ∞ at the archimedean
-- place — one orbit, the narrow/reach pole and the divergence pole as two place-views. (This carries it.)
#check @ZeroParadox.ZPH_PlaceMetric.doubling_place_dichotomy
-- THE literal 0↔∞ at the floor, made a HOMEOMORPHISM (the p-adic Riemann sphere): inversion on
-- `OnePoint ℚ₂` swaps the floor `0` and the point at infinity `∞`, repairing the discontinuity Mathlib's
-- `0⁻¹ = 0` leaves at the floor. The strongest p-adic INV witness — 0 and ∞ antipodal, the Riemann origin.
#check @ZeroParadox.RiemannSphere.rInv_swaps
#check @ZeroParadox.RiemannSphere.rInvHomeo
-- CATEGORICAL instances, CITED from Mathlib (NOT ZP-proved — attribution is the point): passing to Cᵒᵖ is
-- the categorical face of inversion. `IsInitial.op` swaps the μ-bottom (initial, e.g. `fC_zero_isInitial`)
-- to a terminal object — the initial↔terminal = 0↔∞ swap. `hasZeroObject_op` keeps the zero-object SEAM a
-- zero object — it is SELF-DUAL under op, the inversion fixed CENTER (the categorical analog of 0's role).
#check @CategoryTheory.Limits.IsInitial.op
#check @CategoryTheory.Limits.hasZeroObject_op
-- PRIOR-ART RECORD (do NOT rebuild): the ABSTRACT "order-reversal swaps ⊥ and ⊤" is ALREADY Mathlib's
-- (`compl_bot`/`compl_top` in Order/Heyting/Basic; `OrderIso.compl : α ≃o αᵒᵈ`; `setOfMinimalIsoSetOfMaximal`).
-- The three inversions share NO single buildable type (order frame fits categorical/lattice trivially;
-- p-adic inversion is valuative/topological), so the cross-type "unification" is a conceptual SCHEMA, NOT a
-- theorem. INV is Mathlib's abstraction INSTANTIATED here. See .claude-local/notes/inv_cop_prior_art_2026-06-30.md.

/-! ## SELF-REFERENCE / the diagonal fixed point (NEW slot — corpus sweep 2026-06-30)
    More than a bare fixed point (CONCURRENCY): ⊥ is the *self-referential* / diagonal fixed point —
    the Quine atom = the Kleene quine, where description and instantiation coincide. The keystone the
    object previously carried with a single concurrency handle. #check-only. -/
-- ⊥ IS the (unique) self-executing Kleene/Quine fixed point. (NB: `kleene_quine_is_bot` is under
--  `[KleeneStructure]` — the quine-atom property is class-supplied, like `unique_fp`; not free-standing.)
#check @ZeroParadox.ZPK.kleene_quine_is_bot       -- any Quine atom q = ⊥.
#check @ZeroParadox.ZPK.computational_quine_exists -- the Kleene self-referential fixed point exists.
-- a genuine PERIODICITY fact (the self-reference made concrete, beyond bare `f x = x`): the fixed point's
-- own Gödel number IS the period of its evaluation, `eval c n = eval c (encode c + n)` — index and
-- function tied. (A true periodicity statement, not a deep "diagonal identity" — kept literal.)
#check @ZeroParadox.ZPK.quine_period_is_goedel
-- cross-domain: the two diagonalization fixed points (Kleene-periodic code; least ε₀ with ω^ε₀=ε₀) coexist.
#check @ZeroParadox.ZPM.both_fixed_points_exist
-- TWO SUB-SENSES of SELF (a refinement, #5-Hilbert probe 2026-06-30). The above are self-APPLICATION
-- (Kleene-quine: a code acts on its own index — a computability phenomenon). The Hilbert bottom carries
-- the OTHER sub-sense, self-SIMILARITY / diagonal-uniqueness: ⊥ is the UNIQUE finite-dim fixed point of
-- the biproduct-diagonal `X ↦ X ⊞ X` (`X ≅ X⊞X → IsZero X`). Genuinely non-degenerate (the hypothesis is
-- load-bearing via finrank) — the honest version TC37's `seam_unit_iff_isZero` faked (its converse discards
-- the hypothesis). NARROW-flavored (uniqueness) wearing a defensible self-similarity label; NOT the
-- Kleene-quine sense (the linear zero object has no self-application). Cold-audited SOLID.
#check @ZeroParadox.HilbertDiagonal.biprod_diagonal_only_zero
#check @ZeroParadox.HilbertDiagonal.seam_is_diagonal_fixpoint

/-! ## GENERATION / the Gödel inversion (NEW slot — corpus sweep 2026-06-30)
    The floor GENERATES the ceiling — the project's name-as-method (self-reference located at the floor,
    the ceiling built from it). Connects ⊥ to ε₀ (the snap target) structurally, not just via the snap. -/
-- the ceiling ε₀ is the closure of the floor 0 under ω^· (ε₀ = nfp (ω^·) 0).
#check @ZeroParadox.ZPL.epsilonZero_eq_nfp
-- and ε₀ is the LEAST fixed point above the floor (ω^b = b → ε₀ ≤ b).
#check @ZeroParadox.ZPL.epsilonZero_le_fixedPoint
-- ABSTRACT engine, CITED from Mathlib (prior-art for GEN — do NOT rebuild): the least fixed point IS
-- generated from the floor ⊥ by iteration — Kleene `lfp f = ⨆ₙ fⁿ(⊥)` (ωScott-continuous f); transfinitely
-- `lfpApprox f ⊥`. ε₀ = nfp(ω^·)0 is the ordinal instance. (`gen_probe_2026-06-30.md`.)
#check @fixedPoints.lfp_eq_sSup_iterate
-- STRUCTURAL FINDING (GEN probe 2026-06-30): GEN ↔ the μ side (generate UP from ⊥ = least fixed point);
-- its DUAL is REACH ↔ the ν side (flow DOWN to ⊥ = attractor/limit). So GEN empty on the ν-bottoms (p-adic
-- inverse limit, Markov attractor) is NOT a gap — it is the μ/ν fork; they carry REACH instead. The
-- categorical μ-GEN (initial algebra = colimit of the initial chain, Adámek) is NOT cheaply in Mathlib —
-- recorded open, not built.

/-! ## DYNAMICS — state-change / time-advancement: how ⊥ is approached and departed
    The complement of concurrency (the still point). Time-advancement (orbits, descent, the snap) meets ⊥
    two ways: it APPROACHES ⊥ (reaches/converges) and DEPARTS irreversibly (the snap). #check-only.
    NB: these are existing theorems indexed here; the "approach/departure" labels are the plain-language
    role, not new content. -/

-- the SNAP: the state change `c₀ ∨ c₁ = c₁` (⊥ → ε₀) — the fundamental state-advance off the floor.
#check @ZeroParadox.ZPE.t_snap_derived
-- IRREVERSIBLE: a GENERIC semilattice no-return lemma (for `x ≼ y, x ≠ y`, no join returns `y` to `x`);
-- it does NOT mention ⊥ or the snap — the snap merely INSTANTIATES it. (Not "arrow of time" itself; that
-- is the application, not the statement.)
#check @ZeroParadox.ZPE.t_snap_irreversible
-- NO RETURN: no morphism back into ⊥ from a nonempty object (one-way departure, ZP-H).
#check @ZeroParadox.ZPH_InfoFunctor.fC_no_return
-- APPROACH (μ, finite time): well-founded descent reaches ⊥ in finitely many steps.
#check @ZeroParadox.ZPH_MC1_TC28.pred_orbit_reaches_floor
-- APPROACH (ν, limit): the doubling orbit converges to ⊥ in the 2-adic metric.
#check @ZeroParadox.ZPH_MC1_TC05.doubling_orbit_tendsto_zero
-- IRREVERSIBLE, categorical: even given ⊥ → X there is no X → ⊥ (chains from ⊥ are forward-only).
-- (NB: `t4_chains_forward_only := t3_unreachability` — the SAME no-incoming fact, here under the
--  irreversibility/dynamics reading rather than the unreachability/cannot-have reading. Not new content.)
#check @ZeroParadox.ZPG.t4_chains_forward_only
-- IRREVERSIBLE, #2 Markov via the SPECTRAL GAP (the arrow of time for the attractor): a mixing chain's
-- relaxation operator is NON-INJECTIVE (`fullMix` sends the nonzero mean-zero mode to 0) — information is
-- lost, the relaxation cannot be reversed; off-stationary modes with |λ|<1 decay (`fullMix_mode_decays`,
-- via the general `tendsto_norm_iterate_zero`). FENCE: NOT universal — permutation/cyclic chains have no
-- gap, are injective, do NOT mix (`ZPH_MC1_TC39.swap_orbit_not_convergent`). Mixing-specific. Cold-audit SOLID.
#check @ZeroParadox.MarkovSpectralGap.fullMix_not_injective
#check @ZeroParadox.MarkovSpectralGap.tendsto_norm_iterate_zero

end CannotBeIndex
